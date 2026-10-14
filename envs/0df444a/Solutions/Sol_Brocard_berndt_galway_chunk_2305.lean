-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:25.357227+00:00
-- url     : https://prove2.me/submissions/85c551af-6098-4b74-a40c-71854340354d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414388489 ≤ n < 414568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414389739 1250 414388489 414388531
    0x9020d0204110c0723040e03041707030c03060504170a0203070201050906040e07050d06090203160c02180a060518090606132715051012030e060403050f0d0201050f 72
    0x15100f00703049001d6074480d12400040b101103551705507009500c3c002c50f8074900c201c40000c101c291440d03003d0294190b00304000c1008009024001000104681c206403031203259a074883c1b21000200d90300c280c41d015280d03001c0100300182c40c100400244420b0020354104034503810001c2d5280983c0c07000905115002811039030a60707903907055600900462210000030b1809200003000b0b500200282c9629904010340801c03110428020b0b24420517440b00d2134060b003c9540030072120095000416604400b40c416046540ca0440019921032000d0b41d9011840c20300e42024090410110007141506a000106201c0240340104000d90000b0b4100d032960690f5034005400c50052258540c80035180f41c0c1c1c240c80c1d0070010381a0031254405e602035600304510701c2007001d4541c181e800c200c034410b082200f0090305000c1e02c00c0303000b13207524414040d190942c030b00c801e1000032807002d82c41a081540c0543c81140801300c1000c0800041100340342e00d1009014504001c0603508480b40302905403041c0384112118007032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414390989 1250 414389739 414389771
    0x140c13030203010e0307030822020d0201030e0d1e02060c09040203310b150906041509021c050601020a240902220e030a081b0714010b090a09020d0204 66
    0x800355800400030005100801e401c9507595000c100c084000c242481c0000304418040703c0e94001000e02c0700994407604100740e003002704103407120300f08a0505644020340100710000b000200036104540e12200e0103031160b40d481040c180c1e2038944410456001e0000c008401d03c0c0f0030291217000c8410f803400340e22074440500e24804030000c41b040c108014a100a0702c4101224080c0d01c200740c1d400344c00e880701d907500c1d01103004d0000044031800e00c0e00000c02502085060410354051f100940c4000003a070002c5c0d440b60072542c280c1e441a56a41f810402a035001d0716030b21118800c294001d4000d00040c0641c45603655480c1d81048010065000c010700c4a4141c407051095401c01d01199078010482c1703142d001102a03811031a041c003002000020320344028405440400811694101019154241140c0d510030740d042072101480d414001034041482048002a408411500c410305024001314007030304104203000001d24010011a003a6040100200150325108200345800d50151030100b510846050080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414392239 1250 414390989 414391027
    0x21030a030624050f18130b010e0409030816020304120c300609080f03040b0f0114010507080d0905030f070b060d020f010503072a210f110a020918060a140c 68
    0x30380c2150280341d031b180891661754000b02e001c0c8800d0700c0303100007840e610703050100304c8441c0d40d0001c010071100d601013403101070a10201c0d8032100c803902c104d80c038040e142c98940c40c4030300e03441508407460360308180180102e0074580f0a084642c0c0304581202d88181042c00e4400d51003040620141c10581d1f00c540d40018080d00c0303000c4913014481aa0026070700d05052400e00c4010768111a1205906040c07000030896500f010a08400820140d480300d0500809450750380ca142d001d40c0709040790315501c0904800060080c0045c010541004008680310781650810380300e1120020501442135440c10500c10060742c17114205101d4403420b03e041a140d036a00d400c155a01c890700b03d00b413101d1a003096508944138081a03103070542c4522608642e035044070306891413000820300c0b0300060040360705000580340580c4030359010003c111903103044400d882031303c0d00800c0c0b24200c207446546000143c40740036407401000b007104641003000c010042102d000040c0100501c058090040e011000c0300092070071070001d21074590 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414393489 1250 414392239 414392287
    0xc0f0901031b031205220b0405010e0d06050103060923070608092a010f03290102070308031006033c060503010f05060a0501050403050c21030a030624050f 68
    0x1407242c00000203015034201c502011844c410300d01506d080c440d903080b05842202c0d0030f00c800508181c1044015588040c448401c2038210800c80c07151070124180d0301a0500031800303400300240c50802030a26058464400c10090110309120071104140e080000d91402103507900e00e0080000e445201600b800c00e90589480260200100b8044642e42c803000d051138490002600c88500319022943e00350180c501002000001d5203003d41d400e1001d8822050819800c0c10510550308403a031241d5032440d0640084d0f5a4689407a5640d000703000c0f00e9014858200ca43da091440100c498a4074241001c3c61403881c500d800421582c50501d1142402c1c0da0003507005000f00800a00020064000010090074101d80982c0318080203c80042c1a50181303041368107481e04107000e8010780c03164005202815068900005907540306442d8050000d80c00d00180102c0712081c0e40100e081403500b544100c80c44000303044100842007030313034400181603005003c542003020110b0704552a0f410003030300c5220283c104480c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414394739 1250 414393489 414393503
    0x30b070e0d030807090815060613180f11091c030311040602030d0605011412092107020f03030a0c0201080c090d0b010e0106051305012d0309050c0f0901031b03 70
    0x701c1c0c0201508042058820412070303070b034590180c0d6500d2000d50b030380900a0b000500c0d16060b00101350181030250041c901c0c00040c1d076000c80c0701a941c0c0c07850700c121803490000d00007042c0d80e41280d024030b41d4280142c04e200107010036a00e0030000d5100000d04410040400a48a14041000c00003094040c1e0401c00c000145180000c0d1110798426020b52030340d21284c420944249000700c0807980758042c207600c224482440b110581011f51180c0c0912451001802c241c15600c5000500468066103038560b4429050300d250031030300c9551907c1440020031b105c0c040b0700d10a40003802410310312a44141e0212819809181001c800e0710b41c41c4501d8414428103d999811014800c0c40c40e05001505180798100c40a4040303800f81070781ea072001180c85000f422540404014580020402d96114962400721410100324080e1055001019010b10084601c0e00601182d1680c840d8414080c09200088a0010a84a0014000d44800091211001400001d140a0f00300300c07041010003852044401a541c8454 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414395989 1250 414394739 414394759
    0x1c020c01090201020c150a2304031103010c2c060c0105090601080f0705090f0606160302010b0a050f0d032d03050f0a1b0516050a151113030b070e 64
    0x209001e401034101c141d0140c4030b9203d603000c043c140202e01c036282031100b40d40d0a041090081080b03a144003201400050400c205000030520254440200003c600c28020303458103500c000c0505080d13031038480d8203400b40b2034540c03816002c09040174418000d2010101c005204c0144a034001035990046241030142c1d5840d03c000c1043c4600b0008441e8140d450003001c6074070200130902c20fa540c80100b409000c0e0008061404200341320104903a150b004000201428100300300c0c40c03114181901c81d1181580107039119406d8004604100451801602082c6e031801104000107000c600141c1c80807030024204020000401d1440c02d00175071442c02d419105910401d1866945001030103854181c51444001101c01d02060004803544591500344880004c0c1914501d42e8040a9a04c3e4120540341800c0403081c42003180002c00500c0b035599085d2181041c42d07800401e4500e10b104452040c680308058220400400a04592400c0d0f01c90403079901007001d5803266105101101d5400c0c640031070b2500170382902 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414397239 1250 414395989 414396007
    0x30907031e06020d2004060c06050601030b0d0501140109200705070e18070b0a080a0c0e12070905010611060a02090a0b0316110613030e06040806010b040801062301051c02 75
    0x600070900c40c840c03900030f540caa480e42402c2c03045d05100c1c070f02c550700218002414a000041e515000250322100504000440c2060740c0046550030107031704001c4426035521b26031b00b95810003100c0001e01605100200b003026080000c1111075001000c419003150301c1002c1060001c20104101d50b0703019040e0000b10800da07042c888000d500c40301d41000704100501800340045504400340040d0b481044465640018580f241c1c50f041c4020701605408808220b01c01781841104e45440700001c45040107440100a4039151000d900d084a0381a0840d01c01c04c40c060010441060b0001007503074200b00100401641e0b440c03030f040050220300e07142e4400c1800b07038004400c1041c040b50001c02580090301548411079202419481640c44240449011281c540107061100100b4031075909090002c01c080c191501c0c058030b07000803600d4081c099006090843e0001000c0c080d6940a00916000340005216800130b2000c81c02055042601c000c080303810004042141200c11100107031018a05804040c115a00c290203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414398489 1250 414397239 414397241
    0x608090708070305031c050613020d240e1006080412020106050d03051c1514040209030a0516150512070302070204050403021b0328020105040f150f05030907031e06020d 74
    0x25903d514042048080312030700411b25405014800d01005103040c00c40340e00c101d41c09009420040700d005288e030b80c0e0000c18210040c640800088040c442d200b0120340b40c50000994070300030b030080044140b0b0f5109001005655040b0302400c0d0020350000900f24040500e0394202d0060940d41d012542c041c2000c400c100500d40c11030003c0081100c42068003c0d00c0000b4091031080c0d4850080004c1294841c041c10410550524a003c106542c000e1000d454030200c040020701d80f5200420549985d0400c40100c191241c01002100080102d6142030000c40b051940c0a00341e4003803092040400d06500703001640380e920960456821a80c01401081a07042508000f5030302c0e108140002c0e51042c0d020b05d801c019182c005001101c01c800303150000e090f6085a190300d101c4000055081f8103110302404082140a40381810f100902910343c201e09e4650b40c06000186964403448040c2d090003800c0052110501e4041003250540e500026110120104100300425060760228058a03503031010031007007001c0c01e031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414399739 1250 414398489 414398497
    0x201180204231003060e0a020307030602031b03040516081209040b0109031202061902041208070201051b011a0a080a03180b04080c10030b100305092802120f07060809070807030503 79
    0x9008100500490081b40d603a4420f0030040195059020307210401c005045500115480041300c518858400c0d0080c60f08030050300142c8044489400c60403800f400c254006107410010041c5400070141e10004071041d60341c5214081150b4040c1d500ca0b10300c0b00c1d069014400140003903501000c110b0311419001002515034009541c40c44200310500020945141c190007901d00741d4210440343c2600c0da09550750420700780d210307240c2241440002e000302000070140d03480c014000e5070410f0020032004a060300d034102c8411403142c01445461000820b21a02c08006880040c2d264182010026041a0010042040b80562009110050008020602181c040740c52030885d40b09849131014881d00e0007064064412828171309811280400900b0840e9200e50041904122113200b0307070341e003800c00e5250781c8004001403010304082600d40506004506011401d448264401e80c00340c2000c5a0a0801603100c4019128800c104860a0041942d20a00344007100c010440c0300e040310540f81d503906e4420340780c3e04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414400989 1250 414399739 414399743
    0x90a0303110405220f230106050708030105090405010b04020a180504020705150c07021003020405010815010207060e060c15090f010e100f0b040c0503090c010201180204231003 77
    0x1040c01d85004100c0422400d8a064460082000303003404500050b94021148424003400d0303903a160242042c1400e250300c2581d512490b030700354543d68070a1125051581c4001070703000394100003007007100c540412102070580c1c1c159001110f1052881d112400d00c01d0140c04c2c032001403680a840001e041104941010401a42c01c100080004005039500b0404c422070049000240a0390000381c8010744011000104070785c05030350308020500f014119000f01e4a90a45c041d04d00d004264002400c0c0031568122441c4c5900c008440941208a0b6950000039194040c9200c0c00003071080c1c565070700b02340c5e503102020340740960700d010b08031808540d5212000e0703072410060361403004900030003228a9004c0c4041c01246a04040c0f000107243d004074105101c4010084503051070300d0655075603d041c141380d42d071340030303000b0a00f00560729140c6908004201508010110781652b06583c50604e41e00314400c20190098040341c1c040381c0c0040c1081800c10f101d0030035212440d00c0d0603055902d0040201002c081144041568 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414402239 1250 414400989 414400991
    0x41505090d06063503030417190801050405010506070c051003093002031819091a10090e01030215040b030a0207030207141f0302091002070812040b0d050603070509090a0303 76
    0x700c1411414044000c4e507a0a07406142c00400000c2d010503044195480c0d5402070310249450721305004075201c25444281d40440008000750010070003032410b401540e002d0310040310350300c4c5800f0041e5925425203041e8491140524a1031f03c40405050103640140c1201d904142503002d50688180740840c002140c0e40c1c1c1704044040030481d0f080d000d10010941c2c0400040040b2000800300280401581032084005060702110800d404902074416000c1e02d02d40c00002e050084540e29190304110f5403e032188800001c02810000400102203d01c0540c1d046071f4040c4c5a9402c402051400e5030514440c80e0850f1302e02140020500c1408200b0f94002c0031607e0181d42541c0906840d030315840180c000d14400141d00200b90700c9070b122034601000416400c2407190034018548103507071022404000680020381c015810844003044401c07000d00c854100aa1703c44181403901d414003040c0702e55801440348424a05580b400040e44646041005e10301400d0000e1880305d007032402103842984c4000138a4220f00203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414403489 1250 414402239 414402299
    0xb031605090a0e100506040b040c020105060f10090905041a010b070b0a090201050403150f06060c0204050c03070912031101060e0103150c02190f08030408070c0803041505090d0606 79
    0x4038400f8800c01910541c00d6028000d402d201c000894003524000d8101b44d48141d581d8462002c039652840380d180d00b01440e80001c01c01703240c0002002101c403000b04e40c440c060404540c0854519501a50b81000e036035402400141d10b80703450074144545450355602c02d100c4080740d00045500750781d0f00c024001483c481c000c014001c0e41d50401c150181c41c18080001e0219605200c2440040d00e0300300b40080c01038183c1c00024000c4000001e0340182c502d41e0b40060085011441c401c07003903060034010179500545095140740f55003032000c4000c2588002e8420300c420b603d4030117561700805115881d000c103440300d500020b02455071540242a0285402e2004031f5040c0503821040a01c41020302807814044903a401506000d00503581d41d104202800000f200d90a81045182000a0030007000e5801540078088050701d03940146820398114205400081c19a801030104008a101028600301c50010b18a0142c1e00c503804c030380c0414000b0100c2040101080c0c244140841c00d1070b00d250110341e6401441000a41c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414404739 1250 414403489 414403501
    0x160b060907020a150c0315092304050726160609140901061107030f05160f030c09110405090702010f061a040317070f0b0402012d080603010b03160509 66
    0x240c3c15294100801070b03e04031508190038045a0b210402c2e40841342000b0410310b084507e0440e2404090300301d0102e4039079806030021502100d00043c60481121041c410050034140c9810f5594070f4240710705000c41400c81c070411503c0c0411004441054000c2048030711f144040103104941000c03c2c0590800501c01030707000220b002000c100608040005098080c069081a0003140d51161925a48880d84a4401c00100107961030782c2d400305150144015041645d04d080c099030002c0090b034040104040018000d00101c0c4500a82d034013118034420001500040254001d01c4602843e848590312030420782c10402566019004200402c07079040d020022603480705200680e4070031120984803180f800b40018000144460706400c44004d200c4c20150070320811780c1c2c5aa00c4100400c50031180c4011250034070045507080b144e001e41000a881c20ba000c820003250b035000c08a1440481300c0c0030010600c000c83c406440c20352045900420103019102600d03250501e0912608092044134041d0140c040010b83d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414405989 1250 414404739 414404743
    0x91b0301080604050c15090127030804031b03150b1f020a0b0a0e07060302070510090c08010c020307080a0503041103102c030403020d03210507030c0e01020c1203160b06090702 77
    0x310310803c00c1e5160070000e0b07c400445410f4248400e0300400380845c400340700c1031b603141140c1710011886440c01c199202d0a524008500b542405d406c540390f440d0110050001444014680340f040f901314000044c8001c0d044001a0340d8011442e079001d000402044036003105130301103000c507140390040750088120749a4003010421112101d64640343c0da04621030900c290361003500101803c80c0610221500c401071106481c045805503141114200407489040281007000c0c01103a9a0b48a503001550905010b51a1500e10703201e00d6501e074080200002c001410000001520b61003c60003030f08441488400d403495900516008480c50440d1038842560540e0a11030f040761162003a80401550601d841c642c20300c1070f4a11400000c40a000e80659a50351640c00d8007107120a0741144030001c00c0f28103003404003408460061041100f08544409031030b0b11660002882c1c40900703c1030b988441d064111099050550140d20966950700601c481e24200380500d03045101d0140d14112000c900e00d44680c60103036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414407239 1250 414405989 414406009
    0x60f0e061c030f050d021e07020307170d050c0f0a060c1704020f010c1a04060b0a0e130b100503030f030105040e0a0b24030d020d02010f1109091b0301080604050c 71
    0x400041c003c02035408090702c2003000e44910440c150016080c0500503100790b49140010a2840740c80101150440a41c50204000e10040c4805d140300c003800c0c9442c3c1482c03510b5210501124003408800103850720700d0481001101d030085c500900791440f80d001450f001c005045030401d008009001c140c0c010407000c072154009405158020a02038a0303803025401900c04982c2038030103841c5501c4810023640c010010b0039019120b0342c811080010300f1004001080103403409504546450380e1403108115403140000100c0440302c1e00315203244120b82d5401c400c6d0301030810030703000a03070140000300e507400041007000051416203000321003c0c000380541e4040c0c40d58410070718601800300b20000d00403c00030884501920b40711f03120f4030450599012503e002c00d281c0032400d500e0300c0c0168800c80030b80442c3c641c2840b5050081d8454002440040c00e2240c03520440d00030003900314030801b00c40740424080585058000d0b040000c01c55947c0e01c969480c141140c0b01c3c44119001d071124000d80d03400c070b0030702d29000d8009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414408489 1250 414407239 414407243
    0xc20071e0608010911120408120711030a20010f140a020c061501020c090711010501150e220908070c0b13030609020a0b03011e050612010e0a060f0e061c 67
    0x42d00c0c481c0e1a1211101c064850081c0110b40d014081242509413918000b0382441907000380c0d0955610200446d14a2802c00018609030402401c540c0c05400340c04080100da0401c040c5280002c40500c40000004448510140c400880c0d131a201c0b54014104543c1c101d01d6495000c0c044500c402d960b0a5a1001644102520441a03800400005400c140024548010b10b00180304417444d841d00c801c08a101254140c40c0e100205030180d042000003e804d001c1c00b800360448042803419900801130240190107026600b5200308521700880f04401c2c0103843c8541078241c44941030000f0074480c14024601d602961050f200e410301940c002c920580c0c07000498020300c0001c1c0c0c4008682c1c0c95501d400c1c0c001c05403002c0490303111100200018148501001860103058150f44814440d2400952050304043e5580014000e22003400690612140700d032a003411107a805203c0c0c801c41c6d4400340040000d046540150005c840304201c00306000703d10748582031103103500307481d46140d00c2c140150300035000c2d10310040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414409739 1250 414408489 414408497
    0x5071d04021e0c070e01170c0301060b1b1f0603120c020d02060307050715052406041712070309150309050a030e1c050d020d09060806040c20071e06 65
    0x148080c0c0c26003800200f121500401c10b0701d00064070341c69680a680c80030383c400d25500c3c1450324004c540700818040415010f1045000300001d91400301d1890a0b4018010103580049243c24400c0440e074081c00171070884411080318410f002c02402c00c40000704428003050320519400004800c903280690060081e0940042070084200c849608001c0b2a03032009000000700401481a20005921810b44100101c160726000c941c0c0e1902240c3c259542e1703c0b010540c10010383d18070407212151210411101079410401d403040480c26050882da181400484c0c3e983e01029001905609160b480000300c0301741e419800e6041c441d02000c2a040302500c201070005401d40d00080d4203c4000b17400303a030780d4601e000400340c01c504400441c03001030038112100c1c000c2a50a50030a545404ac0e0079410b0002c074140314182c0c00c00007401401c0c8080100f10342401440140100d55076581c52107108d0040f038000d03814051810074003644030b5030300803100c0c1c0300d100f948a200b00080c03140d03e180171201504c19051b42500e6103075031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414410989 1250 414409739 414409777
    0x909010f1523090a08030a0c050c010c031b03020f0d0512060409050d12110c06010906050105031006141207050a2d030f061a041502010c09050105031905071d0402 71
    0x44062055100000260b070202420000180d0705e00c083c8060268245140c0700c4045915050415504100786c1c100d00c1e504104015041100003078101d0309000460282d400e120211010500e020b0740741500c1c4040168551141403500b200a90707021009010020094003102620b80b140400d00080e100712060083c110b420400c0980e900c5841449104c40c0e148494102050307107007400100100d103520640c0420348940020380140300d110076502904000f06000c1c45c1c040e1070761405c2c1143c04c503002d074203002d0701c000c1003000c4d04400c0084c003010050340d01c1e108603e40385000c642008100500700ea030040c11980e0201e04a003c00010822248500b00d0f42050840d021240901604104900a02d08113a5240019a448001140000b100708a504207241c000481c25915070401c507074001c80d401240e010b003045a040c6000c1091450740040712008803003003824541e44031b0325407a206e610840d02684900c54400d01c0c0500b000b00305a4000001011540b1541c611007002021506000c2648507039030248130301c0d1403d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414412239 1250 414410989 414411047
    0xc13060905060712170c04090e03090105090d03050c0627060f2a0c01022214010e01120e011a030a11120a15020310120f170909010f15 59
    0x10400007440d259103010381036003980301d0616100810560303a202d0980c501040a1123181d540c0d02c50504164110f03c0214100f0000e000000c1503071103003190040c060008003140404140c003e400303452840d4060801d90700e1500e00f07100043c12885444a9028040c21080340c00d80e00c0f040b000ca0a2401400142100c2040c0e41d51012031030115080c030528441c01c41c3c00c030b1810000304c8100c1005003076540440c00c00940d90769006004111b83d021280d00100034244404001c00841c1c03020f4142c00076041c1d003030804000041403480103032a000c1003456801c02e03980c10500e102c1a03001065016000054064051250003240301041c507940b0300c452240100a4441d10340c10724410314040b0340181c01c0405000031225062881c1e0b844001c40b01c0102c0b0004203103a004400c1c001448415019080540214500c008080d22a9100e6003a03c84801d54064444041080c4407104031458000b11782a00101400020080d40e4a108891000c44c1920404900d00c0407801c10624091113580c455204681000e9102241d292003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414413489 1250 414412239 414412253
    0x110a020d030b031f05010e09030313111c050609101533090501120b031c031508070305060c07020a0314010f0c0201020a03060602030c0a08210c130609050607 69
    0x191003850750501c242d4044540d544e500b44000e000c40365030410049103d516180e91040c200c1c402402d12403158005100300300c140007131041c10804560300700c8e240c407043c803101502154640780d01090790150101d02d40d14002c1403200000700700d4040e1194601b240c02184e5914001b4044450040f552400c0c02642ca03400c00c01420700b1290711051103441c409821044201810f80c0107080700010f480e4000c10b500300020840e03982c00c41285e070041c40400300103002001e81540082e84880c040805250703010341580010143d1032080d40043d09860b040880da4110980394000c1540e0741c00300348001c03a00751040d080007030510303242c401c16540c00c02c0c1d01409803441c190560380c4502d281d2000c8403114200d50760324952880c005c0c030300d0300544202c4001c80d00016a20b8a44a200600b0760781c0390b401200641d40100b0040300d04810014450300301d00e8001e902c7d03d442d43e4003506400300492498008800d8810780c9018041c10480b01d4000b401003e840c1540e1205180d03a801043d42c140c6c43c103100340d640c404c1d0144607140115543d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414414739 1250 414413489 414413501
    0x606011d120c030f0d180e010902131e03060b060c0a080705030c01020a0807020c0a0b0d09020f06040f26060601080703090218100b030c04060e13020d0f110a020d03 72
    0x440c4040d29210a00700c0b01091412564000c404a01e80c401c1d00c82d042c841d0703000781c0700d18020805150441989402d00c08030701c40b11881031181c004056800540182010f101c0c1e11154007402c00454264007880b8200020240f4800501068a0452403c1c0e0a200d0502c1c4c180202e0795510384c500d000d044045a161103481d0241c201c94000d45050200b0000c650664800384000c1561284036150b0901c00d0801c0003009240a0090120f00d015008210003400840389540c165204e4544008010650200c0c1e8808908480d003080d26079074000c400030801098000d090032010041e2258032481500d2445a190f46001c071403820010b01c801c503081600810b03c0355110303c0110394459014113000c03900c9103c56004c6420913070800310104002c082901440020302e01084103d000300115400300341142002c991020b401d1041d4450b190500c0401c40203104152500c0c5103040c20041481c0d401c540711112800090080c00160210402c0c00d442c01040201d0b401200741074905000050340104014117041034160002c240c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414415989 1250 414414739 414414769
    0x2130b0a09120605070e060901080f060f03030403110102010c02120307140f07212d03150b0d230406092301091e030f2d110606011d 58
    0x282590080b454036030b4074110a8031a44120000207191819210080c160503c111440e07215070000c0011002c1070f0b0b40300c3c4a054010782c00c40c002c00d0b5580c4413600051140c0100d1461260180400704000083c8168100c84008808082c0c00034840341e42e2030030301280c6501000305500510301c01070011820300d0748100a2501d0302c0340701d0035205181c500c0384000c6a0071904506002c841c00c042051032810f52440c0e44a11041030f135400d01b03010054100c0d0a0040b0021100741c3d01d00d0800203810038961720b59034801d81045004081460241201c0e5484600c40142035010742e081880f07040c1000000c3d41c152000a10401240300b2071240b4802270744a56452002a208910042d642d0489250380b105d21904640340d0114800c40c081d0000903074101620300100030025481d42182c4141c004c001e5480840d07004281d040005080d840c11080307016030b40b07040c601459044c11003a5158105d4030b001034506a08a54201170000f0700310202d034025619100112070444220039020888a0140c0c102412410540d9228403101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414417239 1250 414415989 414415997
    0x90f0a02130f02070f0b07030b011805062817071e0323011d0c0f0405060a02070312050301080618100c0c080f19030509060f040201020c030601090c110102130b0a 71
    0x440d903030721031750715102c0c01000594101841c6d806001401c0d415206201c01400c00f824400340e1340402000c8001e0140c0349128aa000740000034198100488524038032094900c59005401c1d2411203d90050a0016420f40c090a41c45940081601d003070080341840341c0400054581104061080303400c5001c0d041c04510a400d02c044d04946d00200c1145210690113459004d2090362100500b901031540a036000e8440c000d0681e0070440407011105c01c0c4215010350320140d80296403400c0301c074002c0b89881b50030351010b00304034585a8400c00e0709a000c802103040b5080f207022100c6ca6252175008802030400c0c80020344241e4070115000410f800260040c0140005600744407618440b1519107900c00c2c1c0c407804248204090014140c1c0d500c9846445520380b8600d5031408100300d20345006aa50758170b80103408a42d001660000040841e80b08000484010202409032091940c0d01d2094002030501c0f11034079404030f80d8104004108030814400c0d118201548a0340d030545518000751041c140d0f101852420400c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414418489 1250 414417239 414417247
    0xc0f0409050f100b03010c0c050a060902010513060906030c030506012a2a06020307050c090c16060b030c010f02032a06010305071d0402130f0b03010e0105090f0a02130f02 75
    0x34510a0141000c860843c20001c10b600380304504260031a40341c0d071515000d102c111414400810400241c0310310f1503074084000102400c1d24001070321b031805141501c5400301d00c0704002040d481e6000300310f0000c6071f025450070310450300724a90940c241e407011140b690001c3d042c086044171142d1424500d948042d2040780c080c2c0c000d0650f840e802041502180b52140b1079640d4020010800c011181540c001c0c00c5620240d424003aaa548503910307032445052a5105c2d44940c004590080c10003400c0351001c00c0840d501900c0030500d85052ba02416000c070007584a40148a020300980d4082c03038071340c24000302079030107540b604461900d500000381100e1080e00c1c00032022412030b00400410015507018501401c02840460f1130084108407000b003036000403915215500a01c00181c946043c1e40301c017080c00103000b180000c9202d50030002441030383d1445030301d50b08054004e441c80c1c0040d8840c82c0034088110583c1c02c81c3e50400e50040d510b01c14080029040031101030740440487c416880b20340481c14080d03001d464 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414419739 1250 414418489 414418513
    0x307060519020d0e0f12041e0b040e0a060906050303121005090405061603061a070501090602031e09060c0f161b060f020606030712030c02091f080c0f040905 69
    0x700c0c0c0140c1c54045015613101e200284020003000002c1070a100e0380d000340300300080d14a0020607402103114900e1000d107440c103604030b5500b00a40c9003020300720440b412511340c0e960342c800d018580c1d0190346d1011218603164003c961110603000d610b0540e000900114540032900da068509070b100149030368600900d01c90081120b40d211400301d40100d0041c4001e118a0401000d0007508030b07030008144003450728000b003c01114482d5801e41c809a6040d00d0b500da11070001c0cbc103001d0701401c501c0200603ca54400020841a00c3c1030b807002d00c1a8030305240040c00700f5911016003982d2140190f40c00440c881c001d000344480c41d0340400050030a401010f003030380ba0340c00c0d056030760f804c2d031003211040150484258a014405c1e0f81e84180c1c0408184154402003900d8100741c404203498075400d001d04c60b07541c2c01170364100040c18014071100e1492580541989120300d001c1852640000c3e903c045080c44403050301c07002820000003d17507102c02003801044c0c2c44004103442e04110080810300340445403070241240e8102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414420989 1250 414419739 414419741
    0x20a030204230306220f120810030c030320150901060501050310030b0612010905150609130818090a02040501031b14090d05010903020115081f020d1803030221090307060519 76
    0x1c40079101e803a007e00101c3c504c0c039024201d502e0041807801c4001c40c00320100003040b4000f10100860303801d801c01d0501601441d40643d800d194016002110b8070410b821a06041d00380144a845548540000c00c07116454100440b00d0784400d81d1403003c080c2d13402600344045035901b2100340c1c000000904a00c010f03c9110490b9094840130f030004e0b01c00c0e4004c6800ba0b41c4003841d00d50140e5008808452101c0c191403c00d07200fa02038405113601400200c0f0214404144a4016801d0004c0f460300801802d0b007440c018207944042e60240c011140007a043c212820a2951101540c101449042d150791074030a5242c1c3c3c11110580200c0800f9502074942540302011034000c0c4a04c40000340250300106814a05921000480100e1380c0010302d142c3c05070040e00039810107400084100b41c03803250096640c01e0340488000144c1140d01c500c803804000c4c1a1000e00b007540640c02007002d0321041c0e110300004460f02c0e50102880344200c2d02182d558100b04007601c00610715501440c1d01c4089107041c8206540c504032404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414422239 1250 414420989 414421013
    0x304030c0806150904020120010f110d06090203090d0507032f01050106080610030f06030b010e1503010504030519030f02300402010203042601020a03020423030622 72
    0x68031981002c428060b201444803d0042e45207010760f0350381580d0500d0340c0002d11400c0f8220362140d00982c01408404620030030742168006036214141400380012001388a48517034400d01c1d01416540c0780940026880d403403030095031711031751242000d8414090880015a03490340150380840801007814840c40140480c00100c00038129004020208020b00b0807446084540680080d0f042c40094401c00130039907520784411140c0c00141c500403419005140d000c102030081a0002002154210000303e00500a0f6000038803074461a804030709902001c030306160880d9025580680010800c0009051140c1010400755680d40c5070b02e000646001048500f900300d800c80c00a2142c1d18500130b0480d2000b01c43c0480882e407050446a55404606155001035540e200b0b900c221940b11401d14011110f068510464042d0030040900039940d41211190040c0298014060400c2c003280c0700c001003096800c107032924018000c002d8000d041c90707100c000c000303050044a00704141001c00c1c00f08c00e100000e00032010032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414423489 1250 414422239 414422249
    0xa17070b040909060b0a0b18060c1209091e010302010804050c030109110307080304050a1202130513021503040c170f1f0b0909060f07050702061305090c070b0115020304030c 76
    0xe442c0303c3c1407070403800350b68104140398451041d4010070300400c2445c20450700103003238005507041100030000110300c0c0c034042d54805c6803860240c0c501100d040c803549401048240c0045a81e03141c2076031a10507003d410100300c5140c0806101040042c80103501440703010390400c0c005c03c202d4100204d001c001074251144c1040c1144c02820840d20644a800c040107848045c101c01006541402c2c1081c0100b000c214940c400d42c81c4901c10003282c030040d91500036603440d807190500c60a105e28900f42403e0507248103080802c80c0151440000e1b030044c805500c090341d0240358003c0354074000314902000c2045c420144101003840d4081d01c01101c580c01810010750500c0300001102a007007101454900d001c4800140b9141d020390300850401000c0d042c04500541c2c014008003038645203441390701084400b4010682c000f50058000503110141030000100c0d04100c41088403403a0480e07551036602c40c268000e040c002004980744400510140ca03109803855a041850720480341020f50700e403203501e9850344580c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414424739 1250 414423489 414423491
    0x90703022b1d0c0409020103181a01050402090f21070e0910020421050309090c0304020306060f0a140315070807021b06030426030705120a06050a17070b0409 69
    0x1900300c41d5000e030180c084500c455900080c98041c049645400c1142489440780351703964000021680240c0c44410840400c4411a0303942c117041c03038a40d00c4001e1805980911464801c00092146000d0080750785884000c1c100382c00c10b4030301c0018005200c01003690f4000cbc001d00c100d150480c81c0c1c410485036004141e0b20300211114188000354900300344a645140702003600412091050000e01c0142000c0d001c170305102d45214040d50306000f0304600880046690000b1920284082070701b100010754000c40c0214203940311a155a03081003a07044a10600d66000603c1c03241c104003100f040c2038918108500501980c0740305071802134208440108442070004103040c041032181c0580d04210110b42d0709103480107200020341c8040010b8050000800052014210780180c03460200d000042404c2d0001e003c2800c1d07260f09040304054110780003100d1088401d52014002038003081c4c0760040b0b1084070000340c40040a00c0c102050808044040c0d20000c160303104048000800c040c11800600041510002c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414425989 1250 414424739 414424807
    0x5060a090e0313080105090604120509040609090501141009110909070201321b191e0504240c0507030f1203150e09120304060c032909070302 62
    0x1c001210300c82d80d00704c015103a140000304140198006109600282c020045d844140b00204084406108110f0b5298106040240004d9507000c0360704000e002500c00d10003030100642140009044031000c64508140c24050b100c10403644401c2e501074180c0c1071400c141c00c1c1c81c2c0704808002c0703201907105444540c0140c0d59224083ca0b001d014100c544a080010204e40751070032101440381000c4440a007401d0719880240f81d101c0ea0b0030013000100d88403180d0084490000049a007c00341010b015141c005107403d0308040040003c9108404903420f42e26984002d001c0c55040b28003850603419501d0b2200240400382e42e040010640c00c22029000354444c1d0b10b1402251070902d081a600414235000400f4503050040745001c25203000d110009468511002c10030350307682c0e1122145030415205542010354400402c0c0010b11441d9000815800c0302511305010040140c4111091352a6241d6160303291480501c010700319180141c260341e040045860301505200005441d1100200350048000354101d940c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414427239 1250 414425989 414426007
    0x91311070b060a0e0c032205011505010e011704060b0a090606032703111609140112080d110f0406030203070e01020f0d11031218011a1305060a090e03 66
    0x401c0507600402c107442c150096454041d0b41c040900001e00710141c0c03c4000300c00104100c140b00300d40c83c20a0220380c8981c4202c4c0e07060400c540209042d45010290000042020a0030350082086e05026501a581d840001114442890f000e40014000f00c4445032654894490783c0c2d140742c8010302600000c01c002800b20300e40840a400c4070320031400c50184e040e03031403000300c04541201d1141c0035294050501c056903160040806007001610b4401910060f520000454103c00b682c0c800050000480010b018a988503c4103594156252400409000c0100249003da031035036040500c100c01e00c00c40481c2003c000c180d8020068010f0703001b99001035400b008110000b9401111441400800c1c00038150944a2612035604c070004882e40700c0c00d00c40c030313498040d41c181810030440c0d8002440109907402420082030468659900d084c0b43c035400e40c00c14804803140041c41c28a801e41c620010310248411101d0a8480083e000040480b0b901c5681a0800100302d10280124000b0011481c00b40d5030324a404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414428489 1250 414427239 414427253
    0x7030f0201060f1202090405010e1903020c0604290c0d030506011d090c07030509040212091002280e09010306050601110303130303020f070f0809010f0f1409131107 72
    0x80c0c1e2107540841c0c0300f41c108000c2d0308048801c48481c603805948407981a900c5d428031902410701e140e0010360504c19181c1d02c561621080b040441c416120b41d00f0348000d2114642000380500a81c05090301d00035040c904ae80d840c90300d15100c40b20900300e042d051400d00e88031007c500e0401d0780000800010903164410440c1c5582e0040c0440c0070100f945e5001040600c1036400b14200d007100424418004200082607014540a07405a8954070002001076640703404188a44145400030317117205156200302d0480070b100c84035a0013a42c1c6c0903440041c13040000301d00c1c5900c40413401c0f0311003031a03000d21084040005040d00d500e40c166000c0c50007003e0109590400c000010426105001c900c00180c100b8000e0000f1110f159520b400d00da81c06142c00368a401c403900520100b403280b2103004011307589140c1283c081182440203000c902e5000d8a034200707502d414003c1074540c181703244944000122031401011660340d441001d400d084501078048000b981c0500c98030800c6400100000d12142d0001c40c944040102d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414429739 1250 414428489 414428501
    0x601030804090e06130303050a090609050c0f0102120a0f110321010b0a0203090409020609060c0601060314090640050c24091c030c02030f010e19060605040207030f0201 74
    0x495000704078a1411840c205c400d900180c60040c1016103400c0401c0584416400196440e50030582c2000710051030314203070b81d603000340b244501c1c01100071840750240c41d1300124a00c111112804402840c0689201c4126003c0840c01508410b01c4a0000705c4007514070200040c0043c2d010014917100c0d5110070b828608074111050784841c0c0c40180400c00710606a5020007607407042030050314040383d00c481500c002103250107035030405a00b00b1001708025076078903800100c190413200301d074404120a009140390a4600b074001c4a113040550b1000d400b0503249040c441c6105d1400045044110418418107000f000c141c030160849803100822240041c2408028001d0f000080400c440201104014070500301001c407007140454462800440d080c105501c61342201c1c8201d240000741c4c00203181b400d14000d02130031010042a40a4030035050b4040340c1800501c81c02119228010080002c031444400d40540b4105000c400c881e0252100d0001440703803203500152900700e02c01d4591084403d038280009007141c1c1c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414430989 1250 414429739 414429761
    0x1b1612140c03070303050c0d09050a030e01030501050a03032007080c130207050c060c0102091017150604121412030403021005010b03220b010b03011a030f0601110708060103080409 79
    0x103010082100c06078000002c0b40e20596140c01c004c00e060b642c072040306003030b40110703060808800e00786407515081020214221440c41c0c030070740350440c2c41d680400045044407c01d0040b90b030840c078801010700120b8050010b020312101c040d01190886625031260600f0320415030301040302980701c5003075825a840d0154030701ca101400c01d0003c40c14440ca0b9200e2075600e0003850900c0b400b4003c00114000003000c2134044a080300d4019080001c144030f000c00041000886110b0b807005010114041009101440002c40440c0700013001a0700b01820f1188a412000401404030741401010308071900c00e070b90030301c00d100800d42115031698503854242000381c14024503010a120851820005000d000324100950f500074180749807500030b0040041c0341e150f11810b00745000c0c0c00208101c1c000100341c09500c00840c140e9549581410204034412940e0340c090106840c40b84541111130001025544600b221100186496045654480e5038031089810242d0a810503030304c0000004007030040007050300600e11081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414432239 1250 414430989 414431027
    0x22e0207060c0807121205010f140f01022d06040c05030f030c06010b0306010c060509060105010914060306150403020d060b03011b1209080405120a17070305031b1612 73
    0x740407940c070110980f003610303c0106405610651520b172644a1840022605a48481000307503507180c41e0b8120f00380f80075101c1c0101c1c00420140c1100241000201c4411402068000304076a601440ca0600070010760710300300c01803180e00700013144034801c1040210b000324015481811045c3c2014113040c10310802d03200810141e03200304111401e8034000030314981194000c0a245e616500c8540040380c400b0320152018140d141000140003880b10301180b002c0c103c45090701d03130780106951240401c609049284032554884410300014002e41042500d17020841c0000c00c42d540341c10b40381c1d40028005400c20b01e045d110a59140c100e01210b003024840c15507000e0710520484801010700c200240300c07000911a4402c900e80760005070003000010000d40d0094000201000c440307840036a40309070380d1042c09906641c010381100781c076191840f5000803600d41c9034241d80c80c40d14640d500704d13041401c25005280200100340030070210034500f582c0241030f0b1189129401001000800c1c490007003014005016031040031f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414433489 1250 414432239 414432257
    0x9050a11070819021212090c0108070f050d0f1107141612020301200706050f01050607240c11010c090e06040b0d3503070207030609022e020706 63
    0x20070901c1d800da85503018003604090103c2c0803140128201034840b128261050381c0401d010203582042c5070316522074040f11f0100c80c010400c440044034600310640300306001c605d0f0f10f2040b6070050311442c0103000000e1910404612200703c000910111586003100700008000403c8080030131000d0f11103c40c0254a500042c280501c440d04007803590505071040c4450206024485011034400f034000c000041d02509150410f00c920b03900400095000e01c100704d07140da280000049200011250b0349040e280f01400b42410503250b99102d000c08030390151800300003401a40e044102080d1402881040303c287c1da200728000003195001401e55030205410300078425001400d00c044e119a031030403540400101c5000c5110b4990320080b40e0100385070b400c09403490698400f03800c420b002d01a181d00284800c100602500e68005080040d507001c00d40d403050050308011410004074580c2e40001e00810700003004002c0d184085200003401266103844017005819201d1250583d40e010f0103004000c0130941448020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414434739 1250 414433489 414433493
    0x20d020610061b060b120c1c1a1e090313120b04060506040b060d021312030f032d0c0306060903030804021306050303030c0c07060f05120c09040609050a1107 69
    0x10403c02501c8100d521041000c079030602146070049111024050801d40d408000c1c10041c5803981d042496860142848408d907100f07460f050301015011b45e030002c98054070f003410328804078180710b80174040020300b40f120041c010f01104918061030140480800540c3d03600e1424000f90701c20303203d550180c04070b035001c801a00b000c14003002c416580142c1c0b0000018896490308000f42c0280401103400e9006840800c91451241c900c0e070090510410040316502c2e0281e9410030850b032081c1c8488002d0008070f0900c4840603042c0242c210b20401c0e0850300481020f040d11401400c04030f85100310541c0003544030022a16100e0b00340c03003124054012403030941c00d9103085440207450351401520081c020b82c0d011042000700c00c0075501c40c4000c0d2030001c00752030766410040500015074002d201c01107020702800d8000a0900e0007a1210490702d4081c2c0c60310750400d80044c0a044c4400802000c034114840200200c4a8503511441144c0141041180c0003403242010046102100c49626400720014001c001c0c40340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414435989 1250 414434739 414434747
    0x3030207051f0c0314160b06120312040309030b130c060305010605160c0503060c0d0c05040e06041d100c030b040b0f1201090804090e100504150b03030415020d02061006 74
    0x30100014105816020f4030fa14044900f6002c060320303404801d1002c101100e84801c1c0001808460307025a1845c02c0c580c688004200301510381020706000d50384204002c250707170349040800d164854041c1c00d000c0199690703600c9440f6030000407158140900d149040300300400c42d0404070314016007200e140401041d0305081c4058400d01c2800034401c0084d000070050008c00800005020140801609480c0c0300d0400340118107460b0440c10044004d42c3c10420060302e40c6200b4410782d41120b03104a41440c40b510f645041c00003c100302e484900090900c00d10302e01c0c652a04001440380003a11180004240c4641c000090880e17100c0d40d00a442503091240840c031954819481a401e07080468400c2580c00064440d03a0042c448650010444000030400082100e669480148400402d0003903407812102031024101311603040360001c0030031070424142031020301d480e8002c0810030009411031749895200d40d03800c0c002500c011458001644a4466414101e9060240700c0d001994240e10940c80c5040000c060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414437239 1250 414435989 414436039
    0x61b0806011d0d1208090d1d0d0f0204050c030601021902030604020108180106140405061801090b0103020408120c01060e0f0f060d0f0c080d0e1f02031b01060303020705 74
    0x450242d4802c14210041d568628510103016401110450102c40c04440980440d0044071515010b0060241030005940a04804091101c402c840c503010541807208020407981602401e6840011a45040d80103869502c240c3e400341e041c03825030310345031316000000a180ca0115080b03910b6040307801c0442401a1800a0059046542400d02424955500096001c00d41d40c6030702034100703982020070029501400a911103101c0000307036000d00003599141c0034400503100860001c000440418010400036250341c1c00f01c0e82140e0149030161600382d80d040301514040c0013043d2088140130008030085030640c02d100d040d00504044603510700c145040c84007030442160007496002011018000200076a41c5c411040928a500105c510044252400d14646c07068460185407510300c90141c200308214040c10300c904c802070f002061040d00c6045081d0340c00e1650001026030381544814001034101c400907628125111003017100000301e40d8a94203000345803002c40e51200d4000d101d1400c2e02c0c681c154180c0004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414438489 1250 414437239 414437267
    0x5010512060a0e0c1f12270602091306090b0a0b070305030604140405010e060603011b0e0310021209121603030e0a060c0e0102010e0102091c140109061b080601 70
    0x740c40c51410196404c4c407a4031410745901c100200d00d5409403ca1030340551601038810b076503541e44203000948290803900c03400800c0a06130070440d17480c1d0742c0303c09081041ca1954403500025041080f0300d40801c0c2e1604800001d203034560b40b140c0c0b0500804081e8131070800b0a040c100d0b4614001450010001998070070000050708000e800000144c268985c0e401048040509003c2d148480c0b4150510324020480340f9a02c601c14041d8a020070043d00d414002c0381051810010440c1210b58000302c00d03034021201150030340e0507000b00c4032102c041c01e41d54805410700081460444501c1d00e0090222400d202d40c5403925200c251003404030000e0080e681c04c0b1404020380c90704001030942d20515181d460040c01000040503a03081c2030f0300d076807120b50040e44040307108801e070004d01c5400e0301804e640b070030f0380201c5070100c2e04a6945064040380301c0c4080b15200c0142d00070329010600c21914034146080d948801c505403489030b02e8500343e403842c00c1e80404480080c402071810b100c2d1414601c00003840008280300e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414439739 1250 414438489 414438491
    0x4050f01060c0609020a150f0e0a0b0c0106170d0923060903010e0d1107050f060a0e011206030b060108010b070b010501140f0301120b01080304150815121005010512060a 74
    0x2541c0c01c001140e401041d4082d00184010401b6980d24554500000c2d4400a1000166210100ca0126020700664850000c0007000d010a050030145003210310380002404164564861000145a0f40306405c0803845a540c44050b140100450314045d002200540c05000003d100a42d240d04600303541900c0f400b50f550407249103503123030681c2000a01414110041a5403409004140030301c041d044040300204060003000c0d81d1506660740200400761030800c0415401c40400c009400c0407034811504685034050505001c8060711010000804807010303508200da00705102d205001c825a045a02903004060000103d444e1010554801d50700030410720446040c800740790301183c040c4400b40152107640c0c0d440d940d9240c49603507e48841c80c0800c030b40581035500349058800402c8811010007110140d038100861f90034920100c000803114010010002c20b0322650310010124070740d40e0703c010048090740ba90000c8c0280c4100d11800400c40340e040e4840ca10500c48003a038840c00c441c0114805d03910140e0030744 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414440989 1250 414439739 414439757
    0x5090c0c1e0c01050d06030b0a090209010506041202040b0d050f060108010b0402090609041a04240608090d11160905070f111002070f02030102040b0a080c3c0a0504060e04050f0106 79
    0x105c05024009a400082c41e40032035100300800c44405600480c4868022030f0404130a07680c8506002540c80ba40c000c52100d0490003d0081c09420305804c0400480406490100000c01544516080c03c404c910710f1201508550010410000b0034050b1102c0c1d450304640840ca05840f990015405200341130300309010f56124111084095041115004c034000050810b110100d4138401c9a00300784141460201540b5584001160140c403c5001e24810203e450040442c014085025125012031600c4100540300b5400445000e9004180203001400d0b420400b0642e42000030000d4280681c00b058942002540c1c1513040840200060070003c03c2d4a200340140d07205071038280200c01c040d100310041d40560000070b00007042c1e079840d00107001000b49980c4580f600d0711000380c1c0c00e8a41c071885950103a00514006041068011a103076888580a0342c820440c0c1c50410900070b4410317810107a040d5022402c0410300300103968101d69a08048082210100103500d0181c0d50440383c2c0006001e0382c07040203c086 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414442239 1250 414440989 414441007
    0x1d060f180418060917040f0815011a0304240c020c0d03050a0e03070302040e031309060b090622060207150903080a20070803070c05190509070905090c0c1e0c0105 71
    0x2090840b01545d80c030000d9640d031515030800000b0302c1c6a40c4101c041c903228240d640d0768135a1003c102e4606071340103a180b0100005032400140c80f0394002a10956003150b681048412481c44801818180c0420740c402003200c0c2c6500c40060b0a040795200e4090041c14083d49000009600004484000c016800c21030782624281011902e00311107a00000e401c0f030320301240c403000003000001400d40c4009100c01c1784112604c1d80920001c2c1e48161094501078074013407200f8120391502c00f020b8541c00d5401c60201c900c0c04c01c0c070006610480d00603444140940c2120209000404105282201000213070034038003000c80ca550748a1030640f10300b00b190410007920850f058072411440c10842c500f040070a013240d0b1200d8480d800540c03264010784013114a840904030015950400040c00e0001e40c040706140b9400519020500206040c0207082c5002c00800740400f094961b616943c1302d0140961850340d80d03e913115a01854039044810790103901c5034002456107069002d0000da41c2009080a1030165240c981c0a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414443489 1250 414442239 414442253
    0x20616090b070506090c010203250305090913050111120f07051204050105101d0403180801090602070611162405010e06040614010f1d060f1804180609 66
    0x9400116001c00d002440c1d000f0b100002031550b000e00c21100a4070034031a10500160399910402c1079a10040c40c1022650b80040040d03880d419845009040c000e04c2d2241c50000180c1c0904100c4001c1082000301c41d41109201003441503894440303028191501d8128880707854100d800d00200f000742c4007141c40000882d0705218905503202c0d1075542d0313003d08a0f401c0500c1c00358042c260854030250b010400d50300020380c0341141744a40b07560401c0e04010124a8880d034078115001d002042c140c4003107018024001858000074410f10040c1801a400103841e03019519042083c0c17001c0b12488014440248213594a08030201d00b160380c402d6002206402d440ea01c00a00700190315052600c9160500d491f0000562240c019290343c0b003840c04036800c01101352241c0144880a420010543c0042c141c51000001540107400b824035203050301c2c00c41c41d041c900103800141240d01000410a6a00c03012540400c5119840a10000e400d8200c80610191041101c060032030078400d000981304c1a100d440369018000f007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414444739 1250 414443489 414443507
    0x609050d0602040314070905091501030b0714190e0904020a180e0106090504030e01020109030206010b0a05090303040609050a080309012c030a050c010f0203090a03020103020f0c03160c09020703020616 88
    0x4002c0d14019140074407000d054450406d44076011040d07052500045910402042d80d90b40002c0010b0b543e515a420f54a4880c04001c00418141c03c2c04550740f0012900e800510182c2041d01c4002841c050412500034003c0042d5800c101c0940640c503241c0c140001695540404010380d405004150301044012642c4400352440c00002e003219440c0071404500d8401a40186108034004d8072942d0b110000080124202c1708a1100600140c00100051001c05050001041c504401d440d1007030410740c2c000002820340c0d000c0c0d4058808038906910400042c1444d900c1c000051600d00f01540c00c12220b1000a0000d01c0c000d032440c082c00c2d1011900726600c12041d0101c004180001d8112500d8640301d10702a90b90303134000200c5901003054540700b01c0c0032610000171034100843c0500700d500100e10b598015800b80d0000541c0d031a00c0402400b805c180c03104100050090301030405401c0d06102803074100210319030115000900800e004000d2280842e800059080e00081c0b14403200e24500300c0d49204a5110030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414445989 1250 414444739 414444743
    0x806060f0f03190b06011704030807110f01020d0b0a060f021b01200a02040b0d02010207050913080a02010c09120203031812010c0206060a080c03060c0c01110c0f160609050d06020403 80
    0x12020341d19409106010000900c03500013031f200c0c0441038994807a24030b62020300f124028005070a07040040c02c40c5202d440e00700b20580c445c008540881011001c000e0aa82089841c26056076407108203949610340100d1400082c04d107818070781020120b0440c002c0d11101e1701070300e644801c0320000c0c079840164803c40c0d52209441000c11303518912414007041d40c1c0c80b01c245035000e074482e03400c0220482c0c062030440301c00341502f03030305800411a051929040c4000d03018020064190402c0507200d0401042c9184001c2464bc2815800010b5500c8001030107040c1e402681c00c40305511141700c40120044e00c0000880d802c145080c41007801400b441c10008181c02030b00146503005500b04524280b849400141c60742c00b0303081c1141e825407010f40f5080c0c2a5952160401c6aa901d980400081000e9400c014010104071241400200d1030080300c900000d0203512000c0c0c010340300da100b1034800314031070340a0120803040588024a807041d18580000200003060b18010f50b4070800c4103003500e0041061030b40c100c0d4021a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414447239 1250 414445989 414446023
    0x20901050f0102120c0a02041b09090209061602040905030703080115080f0a0b1f0e09180303070804060213031a1f150201020405030703030507021201020306180403020c0a0801060f0806060f0f03 85
    0x30209c1100701c0039022000703149030209000f410003050b0110035000342d400c44040585040e007404400c0c0c0c4c1c071940c1d004e030001041c2c0c1c01c990b403070300401c006c00c0b81400200b46960280d01c1d00718542d403408402c014003101034002201040751220501c09044800d1a2858100c0c000070f501099081000740001c1405641580c400d0300d04035103491451019030030030304d6540b404908444403c8113580c0e041c07450440201d400210840380d0010800642035034014500d15800c54020f000040c00c0030484607c0c0307000b00302140c00a844c2c02c001005d80b0000030000400007948000d02900842804450814801a40c0128020070f0300445112100d21a054030035410340703000f04002821200c80f15a40c1c200a00035600001040c0d000340521a5080d158280500890b40181000350040d1084810041ea41e4000f03580680214114014a0140d1110b50b85041421000e480c9000000034403d1a0a211020020310340d440320100e0f811103400c203c2259160620011000c3d0305640d00b0300e40e00410710006c2d0420b40748220b1a2411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414448489 1250 414447239 414447251
    0x3090409030908010f15030b0c07080307091517070f17272e060b0a110f150a1d0d170a020702420304020901050f0102120c0a0204 57
    0x1c9a4440c000d1022a000b03107000b04144269a0014401d407221001c1c034102105051200300002881100c51365400f1a4514169040441a80d9500343d15801a50f0200004004420030b0043c41c13003040d5451035020043c200848000117000c9501d00022005224030300f03000000342142000c0c0d000300d4000180c1e110f4421803c0561401184042c41200140b40444c100d140c2d42c44216080c5100280900502001c03407401d80c40c02030b07040c00a08680394118001c820554552100082c0c006c0c891000c0c0c40fa01c0100d0301d50f00300381010303000310300d1612100d2140228258001c8180884d403080a81c280b5802031502a00072601480d191007401781c4103052241c80da0903210300401c614415601100c500a550f1001400c10300503240d200c503040170381c0540c5001070340c4203208000815085100c1058003400b03490700c01c25403802181e50108042c00b205c466034501f080c0680041007200f1803400c0d840702ca000d0001280c00c2d47c0c845400c000000e580b19645001c0145c040c0c40014040769000c1c080018030311656004000f4480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414449739 1250 414448489 414448493
    0xb032820030a030c140607020709050a02070212060f091b0105030c0412080703020d14030601030c110d031d010501060f05130b0a0c050105060a180b060d0204080a12020c0306010e04020303090409 85
    0x200300c003c41380581d48a1194404c64880312004620607000f41c001d50300406003a82001e00c420b0003000003404111100354204084030068071143c881c84003110450780945641d203004c0c2c04003516040024035a02150300281444048060200b204164409c400e02e040d54803581c44640d07148803031040d6000600c0c0c81c007481c1c0c1d014042207484401046040c1c0b280e0b0030b0b100c08181c260b0007641c016524600d6408010310500008003154480d9004c0c00301d100e80b514200c1d0b04070300000e5001c2d00300400003071007400007501d4008d103491050040207031555441c03820700200159890600d000f0a00c500340da010000304100001c00842580c3d1415200740540428a00550340784d028040240601164040807500c9500300307030000c0d40d10700c1c0074006402203d10b0180010752903010180300000404002c00e14a0340118144030840c5031460030b03c00740000e02a00c90043c5080714250500307950032170001000d542154024003043c1190745002c00d10a045948410200d0301544a070320019042d402080701c00c5401514100c1c00700c0c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414450989 1250 414449739 414449747
    0x503150103120804170705010f1104140a0806011412030a020319031407030c02160b0909062b0204090816030306080a03021b040b0a0303030b032820030a03 68
    0x4101c0340b00745190314039540c0800b802c1c1d80307210b4111009084500d8250426104282c114000c03e0154810400040d8042210504800711544000450751286020409200040d145032560480c2e40049800444103460b0020440d518030050003410412407074800c50841031348400406007020243e02042e81d84684032150b0081d40d039008611807104803100602c01c0b108540c020b202d848940d030720030203050b5255696068281c003e800c501600d0411845900c0b04035100440700c6001e400138024100541d0b130340300444402c00194650140641d44220308450040d011903612007490040d07902c0141d942c05d249101030000030f00a22080f440501000d0380000c040e00d00d002d00310300e0307030030300500c00d440411425443d03d0b03420383c0d2000008402005a03000304400002c0c4034072071128441c01500108086a02c46180002c1048100b403a0f004802098035115003100c1840c1c2444516200810f400030509080300780740328030068140d41c183c040c000d141c444411340c99104122070304001c032000107401c41c3d400410a16000f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414452239 1250 414450989 414450991
    0xa0f06021201150807030504020604090c0503040203070f1211041509050a05010b0309030f030a0b0a0806040302010614060d2c03091203120f07020a0204050f0a18031e09050315 77
    0x40d00c51441d5002254a104442c550f10100346141d40e020f01a070345618080d801068046e2051783e200000384800122044140103d0b02c030496035a0322540c40c0d05251050514040c0c05400c80311190700209030030b04c40c403954514400081508681a00c07129103100303022400a100022030180058405640440d4103039454010034060704041e44108a02d27a6078010360f04d0b550000380c44402c0181c000704285800b82c00034001558102005401c0010703600c1c802030000b40810f0441e0b00a951940140040000303054080c85500000e00b0032032000080031040301d0008442e07100c0c512289030303507039915541d008008141038210b4a40000140074022a00030b0340720000e41e2038100303035016480740c80c08507640300d45a60044169160b02000b020001b42988440004280030703140103024508606c103203011a030251740c1c0ca00400b4041d51400407200c8050401c03903500800d40e00e1004002c2814618010800d000980c0940b00035981014843c2c40346014120302ea040307910b002d6643c802c0741c1c144107150750100d103051840849 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414453489 1250 414452239 414452257
    0x3051b060a0b03160503030904020c0102090307031202150f0103080f13090b280b09131b1e0f05092806022107060506040b041d0610030b060f030a0f0602 67
    0x2240680000c003103404e9103d2990141c290980c006200f036550300d08258018203043c0341d46400140c01c0000d00b41c0030078a05171240d802074950b90f0b420100030034040c4c2c0520141c46404441029140076107000e900d003030a5124103210003010040c00051407640384101106036503201c0f0f51083d64859141d9181081005452440d035101c0c1718010402c05807075849020003618200d10a1034070100102e0b45003020015250300802c100d243c10a00341d441610040c5142d10540a8144038020200085204c07100003d003007100c400219032103440454450001c1c160003010300c00c1c0b00c0500b450099500c1c01403201140086000000032034440501e0141035600340312a140c0722040d01e1142e805c90b8200176200130041441c25804040c40d035407400400040c80801c0c00f603001550300120251000c00c021815001180840d00c43d074a610034902444e03516031040e200c0600125404c121510b541240308e0b130654a4006500502902c4030384190355402e02d44a9a84040c000f5404083d008051048800d15504000c0e0280d8004094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414454739 1250 414453489 414453493
    0x21e0f03070516021e10090806151206040602071209050319140706080f0601031506030c030b090901050601080603010e0c09090c0613080706020106060c080d0603050f0a020906100c03051b060a0b03 86
    0x500d0f82c7c13050b0407030000c44466400500042d110303016068a44100320341c8082d000b1201008811001d5000c02140d030007030f4801d9100603030b80c80380c3e070405041d0b110640c0707141410801a008100001d90f80000e005480301030781a00b0b41c0d4465203a1510440c0d040c02c0510100c0c03240102c000005140c2d0b006078042e48543c000903440398282e0ba40da0011812a40c082c034140301c0c0c0018411043c0001c900c240e005e645142c0f120305002924440c204d00151800804641d64080d0f03a450720104041568002007164026000b40c000b8441e2603d5241d11980b603414516515000340c02c02d070001115602c2c100402c21010401821090b81d503501c1700d12140c0e00303504601420320180304800c00000e034588144114402c86100741e5680c98000c1250381c0d0041c50380c0c40582a00e401c262983d0010011070001d02002e071100071420002e0416113000e1050010307020000300b906114080c0041881c050b203800001180700c2c1c0743c0c54500a0780d0b94503065100c65112801100482c45449400200010041254422044c026003207007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414455989 1250 414454739 414454759
    0x503090a23071208042c040804050f030c0f040c051204110a0b040b03010e07120e100c09080d0809150a14010b0304170a0306030501020d021e0f03070516021e 69
    0x703e250003481070100c000c241d140d0800c020800c0901c0c0d4030000700200c009210590301c02c0004914981d0181c820780e13064402031030001d0704100526040340c64141294094000d86042a4404006405d40b80201b1015000300d40b160003412800340315208407401c41c0001903001c4624205410311196108004040380d014414000000c1100c05003003095604a52220380381c1441c3d6800c020346d5408400001e4400710070b00070707403246240c1c801140d070088104200304400185207e800b44140001a07a00400d400c1d0140507110300700380100d4001050014448445040c240d00c9a11f803c01c03138601d05101805481c16032401d9600b44225440c450300001205000120348000590320b6401407480e0344002d60b80188039440d410100c200b50150800a408a4191418002080c03540d0783c6409080e07034401000c2c5126654009900e003070000501d04070701460f5540b1180300b410100b050200c146640f001400700c0c014480c02240c041746003019900111144ea40c00b4141c041c0280c244071040c1c0244801c0b255951080710a04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414457239 1250 414455989 414455999
    0x50411090903070303180b0f1009021c230a0e0c06030f0f060319142401180f0c030203190c0e15040e010b04081b0901060503090a2307 59
    0x60101d018110101c0610324210056409030b005207010751003406004110600180450040d485003032143d411140c0082051400025813062124180c00840a2500c11b00601c40161a43c1e0f01554248440c100001030003062143c505031a070018003a01074030301da02d00040140408840d00700c0039440301204220703181c040d407101c10072426000407903500f101e424812001070390340e2074410b1096130440e0f03001c2d06035847c680800e40e6220500110030b0043d55840f00c0e0803000643c400040200301000342c03003100300042c44402c0400100310050103104520503113910300a1901c4031603030b95002140d0f031213003041d041041c0c042d50100500a0340044440f18a950000301c1c45c906814101c1c0144111444207645403814403000c9030402240c41144582003501d41000d10020030780078001d14886010b0240d040179152203511303004ad910319040e260b51098121002c032950010b06500ca613000c55056071030303504209840e070b40d03003414483c44c20481c500040c1c940100200b15902d190b610312803544d01c0c0d00700c1d04151520a034841c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414458489 1250 414457239 414457249
    0x3010602030a090f1805070c0203030309030705120403050a12050d020409050105010e1e040e0c0613080d020d170405030c01090804050a090b060403080901090305010e0d030f050f01150c0510050411 86
    0x548151019400350380c0c22034016203000e0340015403119081c01c00d48d4440600d900868a0b41d0001c8501c1c000c15800051144240032081200403c10054108414903203070550343c400e80ca800c06428028500c0c030031000e082000502034001d9641c081c609010440d2115038860481000e004280b04080c0806d480c00e828a03a5402e10190000480c5400390300d4a40c1e1040740d400b408002c05c200e103285092030140d0744001059a0716400105216490b40032100d203000e02300038116007080101c1c25030009650000340c2560410b0b4101450703108000d180302c1182c0e6142da81d4100181103205280c0001019403a01c1082420016900050301c00e661f401d83c1c0385107807a03849042090480d03035004801031b804401804100005a00000201500d0300180b400a8015580b07030f9038682900e41c0030600d140c07160040099010300542c544104818503228001c180042c2c01e006005c80d442c614180148000c091a4540c2840350500030840d01a404d0780c0f140441d2003000d40031440100800007914200d0b11212041d268400c10301c2c1c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414459739 1250 414458489 414458519
    0x50a05070c0308060a030803040f120f081501090b0c070e0601020d1202090406080703030309060b010503060d1211030a05030912040e0c1303140a0c1a0405090a1103010602030a09 78
    0x79200e140102076503032002d4880200c0201070300d52204411002000050b071580295018601c1021107081030080c80c070307090440e81c100508039020032102d0303000050384ca544610043c2d04803003280b05019034054a100100c5650071903800040c02010f0008000c05449000640303c0c0845004a412107000c2d1225001242c4402c0081869400911200a02c945444043e80103000c00000244005800781d601c421207400c14605500035030100e40c0c0e40d001c0c1010b110709801a20020502441d2007491440c249002403000090004060104010302a4045220b40a800040400048103040326100c02021078000d0aa51080321107088038000c0d818102507001103e404d507820388811004000095560211041841c0c110401e0f02090400141001010404246a460083c000c0101034038440360726041c000060302269100c0c0d100c0752181c9600264942c2802d00369002d44104030f4181040b5221342402e40080e050804001d603c2c104004000600b0030380001c002c02c1c88103010340701c03142a590b60b20000510114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 414460989 1250 414459739 414459751
    0x206090616031d10081005031905070e0c0d020714010219140307020c060a0909090812090c0319060b04050708010503101509021b0a06230405100207050f0d080109050a05 74
    0x20203c0681302c8590b00400b1040e500c40100c00c000b50750980da5000292038001c03525048124440e0030f003010010700c40e0602010300a043e1501c0c07000d01030f00b40709094100e0340c40344c0c607080341000394041454010004d00c01010b0007040d0f8014000d544030a00110300114014541d003000e0042140b4030031035107107084944181c0e0312070401a005490100851001d2000c15805901044108680003101248211482c495504003a0282030b100c0d03142c9400803801d0b2029040a07101e0505544031080380017160754005142107060f01040495043c0fa0018900007014201450b00e030741e48a42000c0410881580c000d01190481d0f0084080303455000402032440c08540d074000c20300700758124911050005490070740050034001d4500a1240403280868509414030b440380c00112121a21181c945030b08001031002c0f4001c00c0c030392468070981c0c1c2c140380d40ca65a81e02d070000001515241c002c204101404428422040071309110829920001414a0010b2130004240581c03542c4a1804011a0400c8058490717988550 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 414462239 1250 414460989 414460999
    0x6080a0c1412060a060501112b0923010f050301210c0b0c0105010f080304230a0302101101050a090b13081c0f0605030a080301120206090616031d 64
    0x203801c08104000d205001540d40350080c0304100461802403040003141c1c49288080c00005980c2e080500040c401c0040207541031080c1d1140e0116030b01c02d4004401c4071a9010900010383c994484103500381c1c0c440d01107501508009880d0303a068252610414141400400240c1c0e80850000a851054405000a000710482c2c040448190007096040e141065603550007880d01349103265070780410040d10780c805c140342c80e910394594004010328140c0b80d0105025109180195007007904018102c096640c1510070550f0341d01d803000e60700d032441d1075205280c000b45801900801c0f001c02903400192401c0e00c0e03e010058250302c0c000000d0b0024031540f150240c81c9a02041950054850a15a41442e04204015100b42c0400c00400340038283c80e01b0341f1b0000c1007007042c0100c0c1c08414540c580040790303000c1d40518029084200c4800029600000b12815128140307801c1071010700070700220f1540d00400700070320b400103000a050401034848040c001d50307440c429914215000c8481481c005018145a4041d400c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 414463489 1250 414462239 414462263
    0x5031e03030a0531050609031801030906060f3c05060a1205100303230915070b15030c0103062301020a02031527030412030e0d11030106080a 62
    0x8120183c220301d82099a1182e90b401d040c40c0002d004480780301c00b044400207012100d080c070040140c280061607124003401301a5007070502c0420b43d0445100d40d400b1041c10581d45059070000c101d4154410005003c1400350003c040d6254500304620001401010415500306c2810101340d048282c40c00095800c0d010505140ca4602002d001e590f801400c0040b081c025605480050a00c0c14032940303100c0d050f809100b442581c0365050280010528040a6100000840d00350b440d2540707031011180581d42c156001e401e4605840c118a00c03a00400d00001c110320303000c100b8049000d20020300503403505012000d48051560040064048482c9403040c90803044000101451003040e201c80a099940180140c500c250341a5002074100300420888600b51000c100a00c540d00b0400140000c42c00100f02344c3d903011001400b991035032801381e0301c03950440da08080404001c1500ca41c0c0020110640a0012002407000c1d1400e80054410220654000e610f48480018503040000307490340e509410030301040076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 414464739 1250 414463489 414463501
    0xb040305030f09130e030d0c03060e0c030c040314061e040b040b060402040806010b1908040c090914010e011d2107021203120a0b09041505060f04060f05031e0303 71
    0x31034011601607a8040d00400351500b20390102c0c0510b518608805c005541d4944d040c0b45240e00300d65401c9074840c201898408140043c10b00489429005003015030095201e5545407254080c038881d075000101507155040c64111034090000c1d116003d14118a01c1000c41e900c001c580205061040b00c003d080c2a20007404200801c4544203016040a0041d002500d400d0712034030300c10300d0103d00307900c002c2000200092404501401e940064054161450a02002e0625803a1240d808485000d0040955510302c0d40a0802c2400950815823011120003408150300c200c2115000301410341038141003003541d00c105031030601c000c234610b10b9549480040008090058200340c42c1d41d0405941260044509400c121403c5420000750030b81501c100042002440c3c80003d030025240480340050103800c00c0420b00002401010035002c0e515040781c00000e07240e84030310002c0d03206510001802d400916005000c40e80034407101d6000251030b0306400b19945449100484034400d403890351002c2c0150024004208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 414465989 1250 414464739 414464767
    0x50307060c1a1b040608040c0b04030f1e170c0d03051618031a1501050a140d060b0313060515030c0d060906150312030507020c0d170c03040602070b04030503 69
    0x900b009080362100b2846035800300604655101c1d0b001100443d00b0301c6c040004000b5540c2942c0081c100002c0c01900f07080c03035030f03a883c1281c08824070b00414580680c40140c40782110030750751441c0e003508550440561050150581c4050b031041e0201980342c0207500c88014414001e0241d140075040720000386500200c9200d088074640f4040300b410324901c008074000408150309240604051070400348420407410500802580301610701143d6061100070300588201d02d0301305040b040c00c051a4408160b8030001034240100800c1140c00010030f140003c4144520a440c041501070f6a5109044c2000035440d034140e114a0001c001d0744166050344019509015400c051005000345441420b0208640d519035940406070b4104003000303110481d01c40410428048107c0303942d0a2469182000c1001e0f04190b02c0c025140c111b00c0c4489405020580c09040c20010303991041d072014100110255120220b01c81c42e10b45960003449280300521039024082400d040100c110740031207900900551038402a6503841e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 414467239 1250 414465989 414465991
    0x3100605101101060807090b01021006030b1305160605190c08070222020d1a0d0c03020f01020a051504140609070e07050c150402032802040e010222050307060c1a 71
    0x540c5548484001905d800708203ca0005040000808680040c050000900d8810590009480380b0b04000d001c2000c030302c2c041c90280e00200441c800d1088600c1c40e090040c90b0500700a95000320380300c041030000700c090340007010b0070600318150480701038140d000b4400c8801352401070001d402c00008101200041c980510b801e0562441d280d98404941607010881b402c90700b19660080f059916060044105a1140039603103055a00b02c402281c245580d84a6444240d40c50000038041c4601c540d510b0100e0b8000c111b00244541d02408807640440c02c0e1942043c80c910981c0c0403903926011203101040702c6c501060301440344110313200511180c0d01e89601100e13809c0300580780300e0030b00c1010003200a103c102401071111129a00111203890b0901e0302c14145452614002c04d04400541d4507100b450911900342e5495068044030007213001320f909d9402c0d50091040c0c4a07240051500031003904401c1e86604c071400202c400c21810346451a40c0c9010645207000c4103500140740e10051070701e089004a10503025 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 414468489 1250 414467239 414467267
    0x503130609051509060c031303030b0f19050a05010302030c0a030903091d1503012708040504181a06060a0f0e12031308030c0d080408071a01050310060510 68
    0x208500886854941c03c02e060042216510300042c03040007a110b10401109400a51a5441e01c2c694500200c40f80c580c5107900800030b08054403000c042d0060307943c1c41c0807405000b20003407460071000582c04030300d5041642403050602480e060b21b000500c0758040d10a9070321030800030702d1952501d800800200c00800c480301d81101449410f210100d04540568005d503a0075900640c4030699041c100c004a601e988c0b425141c41c032aa041003580c0881c044c86e15040307035400b08a0b842ca0722880f03405213007090050107141c000381d400038904ad06032441c10041c4100c40c0c02050003503544002913142c541114140c8a03044800d076800040c10040284031600c0f903080284c50101c0c61810043ca040303c60001641d414052440d160250310210b030610001d003020700200c008212150086280c0b4032411401520f41500310042e4007401340e10310002d028040c001c4111791b0301c198401040140c140003c82040c01240c8280105030203807081c40d412180c41d040d00c1c40b1300b0050b100000c1101000d03110481c005c4400b00328041c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 414469739 1250 414468489 414468491
    0x30405010204081203061c020102070512010b06072d0309120303140f1008060415020307090b0f07030306050103051b0901020114040f030f09030c060f17190f09020105031306 76
    0x400359001d00c04c007030031115545100d5980742000760030450304090302d4042c401410f42c4444031000507a00021401d08841c42940c132401d031f031000c0320032031801001141c88440d00058002002000c01c801518020b2807891020045070407000c1f1103500e004000d443c0f800c0180851080041400280810200b903c4414400c1c0750100341304034620040c1c1011641541d52181d0b182c04407091000c0c5a41402c401405400d1150081002d403400d030f1524414008450b5210034456800004120b40c1d610400010002e40990105c880e030703c5d0405001106180d02c850b4064000915103400410303d5072090180e03500072141c10b441d86030706900245038a2503580c04035100303c0c1550340e140c01d40e51801e002041428850b0f40212006800504035044c041e0178141c09010f4407007007140c04c07502440000e103010000c0007035441e40e18180e02c40c0d035080c81d4162003038211030a00a14010202c020452561904150419041c8090800348000b00140090383c2c1587c0c035000000380424402c1c00000c644911801d01c1e01c500d0750103050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 414470989 1250 414469739 414469747
    0x5130311040f090c031509020612180d0f140304030e091f080714010206060303122d070e01051303110a0b191b020d080319050a09060f05070c02060304050102 69
    0xc841c1045900080f0201c48110742d4140030070030f008992621202191117204180a00c0c0e42580c00980315104d00c44111090b01011400b003101c4500000320b900a590380a001c540303041c061448007600100442c0c503e82c001910342d248000100c1c2d6040c0030f0368010307541525602100c010940410250b810020603401a5501c0c440350b80341140c0c002ca820600404444000d0082c0034208203c50600d6207500c1d10450641d4801800d1002d25100001103034400502ca41c80c000f0280c4904603070680729400f600d00d11440b070000150400c0d414121842460007940c40340c403054800300c170f44401990725011300b41c0310752400701038190300300003082003042d1185034600001c001c81c44c070741d80f2040800d6164211503448849603031040d940701d1007240c0044901ea201c0e541c4100301011000b00c2d600082e006411880001d0411801102203140300050030307000e42803400d11050902680c503040c181a402005100c07030540b045c80c107148002002171710600c02c1d00c2c010080c1c3d60340c000e05540b46409002c01da6001404c11500e66600708 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 414472239 1250 414470989 414471011
    0x25150c1403010902070b062b03020304240305060901030b0114040608010e0c0306010b13090207110a030308070f080f0106260103060506040b10120b01030f05150a060513031104 77
    0x340210b01030060f1080060b2540e1039404e0107888a200280040d000f9540c07401d00701c3c0d840952070040d51400c02074400c190341400c084d00d001c0f81103025030361100c03102c550b480c1d0440007442170503400e4140a018550701000540d44010030040075060a2201034102c07080d0000601401214807004880c1c1c00c0c019001107560759541c0c844908680c061440c02c502c0e500000e08440040c43c1c184210740c01408107840c51810410200c200a80d80388181c8103010074941e002415074208040703203410442c0312400034903c1e0451981c070304000c3c103401c0c2c04507112800118188041c5240c00d0240358014020348407090345500903800c059040c0c5078644224850407400e45020a81c500c1b40064202c0700340a540304440c082aa410310310107001c1590f41120381e2900c10100e103551440a0b43d8020411400781200d160040340c1d4002940042c0c00801e421203c078856141440c0400c003040103072070801c500c40542982c80140700e0f0b0b681c1c00101d5490180c0000400b40603c84002000412104288182214401400000c168a41c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 414473489 1250 414472239 414472277
    0x4020924121608060405160b09010302070606121407080d0c0f03020a0803040303020903120901020316020111011815060e130c090c02100b010f2102090301020403050325150c 76
    0x90f41c80400c4a40c0300900b000b04000f018040314150900711140106036a043c01030540d0300d070007200e007207904150b1701207030442c10301500d0340001c00140812030404013065068244403001440191682450b441001c00c0041e407150006109581284907681e03982eaa110259603889110401030304c107034110700c03802d0840e101140702c8100540c0101c1c403a440c016940c161544c10706080450b01c0940d601030590601000c04140d0b00401101c0c8500501e402c100140030700303440180d60382c08800281c02c0a80d0b18082821440b510b10078031040d10207010340c0c1c2500c8418000040c203070903161503001e820110611130b400f0410000045011940e410b00c5510071a5109803181c2c13400b012900748140d4400140d0103400c000744003a6540c0b240d148030704420720b8001941d0301442c802804200a81303d00d450443d10119007203129062540c10b03181c200c1c030000d0082d59030f81e941c1d080c071300d5032600304e103080001c40c03012aa116007011080c07000c4101415801541810b80780984040c0c00018a980800b10007401254582d08a00501c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 414474739 1250 414473489 414473533
    0x20903100c02160b03040b0f06040f0204080a1b0506070f050c0d0303061806080d1b050f061e070f0305062e09091808130308030f0402092412 62
    0x981e40c0140101018110b0450f02828268420180060f0030801c1c4001319440081e9198009400d00c0411465160390010900a04044032446846440072401061a520206900408502075220301e4940058a440307070a012410341f158540c01002081034a000074003121410f841940520269100660340e40d010070300f2076507601001c81c0006c3e9110001d203c02400032007140f00b032500246042003101d0906038503964030a000034ec0d2205100d00758801c05420682425861f840562000c1914a43d0301c80b841196501d681c1a00d8000b0f01c5290601c08100c861000e09c8410710074101c0340e0352410030602100c1e0540c0100790107420a90400800700440900c1c91110302d01c0b4070745145510154600d00040c04000b81603555a410a87c0380600304002c40154505d039071510032100b0703041070105039520215080c0c2000d46242d944000c01c001004420000c15800e01070079248a00d009540d062059a41c0e500d080e0360046011180b48594003914050030800c0c105090000ba02003141c008a8030b0301184040d140d00c405031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 414475989 1250 414474739 414474761
    0x101701020304140a0507061404170105070f020a0804050907030905030a08011a0405031b2206090605180a0e030c0f0609010c03050c030a05091204120209010605180402090310 76
    0x34000042c8410003c0b4600040000b0720590080e110050540d900c003a1903c0e950301c2080b04000c400c040e1540c1c506d448404803801850b40e20700004d5000d1131040210b0207084111002e0000c101c2000e00244814004114a45030b1548a810380340f80074181820400c0000340500801e04140da50340604002407010801840204501d848a040395850070f510f08a40c05c801c0b80580d030041e2400c4c4004c0102c0e450001d0003501c202032090b0026002e2240760301041c80b410700117003405000240c212825444402c59400601562041442841032a4541c01800389943d40d040c903c124410281d00041c10009099201c040d484000c80b080d20310308600348651030310f4a0340341c2c4420b0000d078000d5028807032000d03002d105805400a1909083c0450b141050310702a044c00000c100c180c0c00d6031a0800036050000610801d0010a100e100560301d403610b5001400b0510b040284c100e0103010344174004031310171b405103007034548004403011000b607070380044d40500020703402c0460010b80501c030740070603002c0780c03121409010f001c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 414477239 1250 414475989 414475991
    0x12050d060b1210050d020f040b0a0f2d05060306030a02060a020c210d050c0109050a08091003140619030231020702010e0103020307110a08040801060f1508101701 71
    0x1015900b01c0d856010003a05034410540216000c1001e80c88000b107406046170111920000300c00d111001c10050100c0804069014201c0900410406c1d111003080007038500c82c0400b02c01d91075218a200028000d40942c2110001079000e080042e450b0041c0216400b51018080d500c0e682e006a001c100680c100b040c4440140e0420186007202e824000c0420944440c14031003034580881c0018010f495602445000c81003020020f900550b4040035000401d0050b80901180c0205116003000440c50f085424030512410400c0c0190344414840d006940c1c1144d9201911360040d1a500304100d03100c0c031002d117140c000c00c00351350000007d0303603d5500403000800c0f0104407442e00c84040c440014481c0d56201c1449120f4414400000940d0307200000708682c500178240140d0b280c9807003034181c4144220003d5004584901e060724810041d281000d44212002c0314001e12155448180c10024070b600c500610840480d410b681c0100e182c41440480c0d0404018003440c0c0142c1c0d01c800300c900c0b84403084080c600443e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 414478489 1250 414477239 414477247
    0x2040b030f0a0804060e010216060c0c0b07060203060f03150606030a150f050f1804060b04090f03120606020a0503090915030604030203040305120307050714030405040f0b03010c020a03020a12050d060b 88
    0x2040d00900a1b0740ca1380e500b4401703006507041002810071500072502407901000702d500071104c20800e900c03c00d42c015011441e805900c804251410700c0180d4002c4071202c2c05000083c11031221070500259440c108080c912146010307942e070340c0911900d034000428249136140c4400702d04844443d8020305030301401480095185c1c4e40e040c502440b0190140042d22800b44003510461a81ca10b2401d94003038000354483c4001c03525900c4a000900a403142c00380142440d4800d18004c410103800441408030340510880c1441880c1c1d903404143c1c0c4a51081e030001e413035134004010990140c901020301503401000344213044003140313504011a140c0300741110120056880010f040c418004104107207001c8010200400d851450051402000750195840091041e045075100c942909030078000d4a004e08005032007049082005000b0801401e00d0100c064043c3d4a8045130a050a1012844001d5140c258005010503980c1c0d0b5920003d0b08003807000541006403e01461050b001140a010000d0840034052629 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 414479739 1250 414478489 414478499
    0x51e12040f0e130b0703020f070204050a050a0e0c01050409020903030408061f0828051c0e0a092003070219030c03020c0102070f2907060e060f060105030402040b030f0a0804 76
    0x10781e0b9000d86401030364451060794000150105480540c0014540741c00740e21540340c90602034942c007456400a520900b800c04010036200310360310081c407505540805201800400142c25203e07030000d400706001031020402030112000320380050090340701c0a800c9a10f06a56248590308103801a01c015046000300020300d444c0c408110f807290701801d8618083c1c050b80d17010400c1e912031152100900f030110042102300006111003480002018425100c440c2041209010b0051000d0140c000039071040c4000f0401003054080d83c451030b080ca468501841c0001040c42d42800d000d80c01c000c0400d021440754a04040c0c40c05090900781480a10945405400004a02c1c02074104001d19000764110752041c50104a104414015401120302161410900c400b124400100c042071042c00180750341c1002500303004201140d800714413006114410760340503440701121003030784402c140d61082c0000c02c180042009803901c0d6014050010f0b00404513000a0729010256003400043da01c00e481c207003000300b42040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 414480989 1250 414479739 414479759
    0x5011407150203010f1502162105010e0610090501050603070c23101406010210051807031109010f12020f1f0804031d06270d05060114060403051e12040f 67
    0x61b8852400502454007643c2c10030407211600d417207000c04d56030b144400b40f0000584041c8030102690040002d111511100c446503a940e8001c0c1d94003041206100710020300703100203201341c1c0e05a4200a100b18610307112584112140082228203070307401960b0040c40c000e41810200e4070101c0c4c2c416000501070750302c4090702080849003030403001c0912156100410843e61381c049004403084114003400a80758540c6501c0c62103190000704480421321400c403002c0240210015561443c0340f089401035096078840d01080c049a4451094410110030700c04103c00520300080c170344224800107020487e000480030501400000400c81c80008900c044090100381030303011042d602c000081c415590040310421011030201c0c4207010412020421481e145d080030401c0d45680c210144c40244440c21071b24030381c140300b41c13904406e01c41d5555229800c60665001c1c01c0c100b00b42c504498210000d0009515460180e45c0481c0d0014103003a49030040040302d04400d501c8001800151005c0040d0880c520f05244a9407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 414482239 1250 414480989 414481019
    0x3041b0e04152f070c0602070803070f05010f020d0e2b050d0b360403050403061a0a12060b090f012102030105071706010905011407150203010f 63
    0x56405416030040002062001022000185500b400001c40c5100c0c20264010500c2003034441c2000c2c00e90800711010000014060583d4600520881030000e41d0342c003060b40c4d911440d100380051030f0000c0c06a0350120301440c040c0e010180c090b80010802c11000a118401c0b64001d4480340802c41c0c3ea008112304440e0100209007a2001030814101e6108103940c480c0d0841c014003400404001000415000c2c6046940009130b0544c006020050300c024144042013003c100f030322842c8005040460300c15441801c1c4079803a400b030340c0c15448552800342107894400240482007001d509007805903080203413503103c0c07101040003009c0c00585d40e00c4a0800d80b40050075a00b9516546220340e16040502584284030800241103c0300c641c2661001e20078281c851003c240e008102a5140d441c001c100b100c44d5411501070030320031540c504440913558a450040d00e144203540280350003d10213074a101800700f100340081001d140140300c0e00e8143d148044001c4286d9000342c005081d0280b03031400405c07107844824244 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 414483489 1250 414482239 414482249
    0x27031719140f010b0c010b0411070b150603060d05010e0604120905061201260f01050103030e060316110102041205011a0108090a02010f0507050307060b10050a080c030703020f03041b 80
    0x10a4103104246098215044c00b6000d00f6190010344442c14110942c00403a4010000c0c3c410b0140300d8124000d07110316041110152203280219001400c844003100c851600110000c01d0135046896400c2441403140606204a40c11366940444500352101080300b18403692051000309090250184000c0072071040307074000c0e40610300900c110081000340c40801030546880402446018070509440c814100040501c00d00380e010748140c42080c0300e819009241a0b03402901c0f444600711101d006d011301c03031004a90007490340f440300d949003035071034400c0c012158000c8800001505203901e0b800445030030094203408641030ba5450703400241c0501005004502440e09080242051030103403003c03611020841c1d0020b0401c070380c000d50007401d24051015110810f800c001140e4840c1d1041c038040008103401ca40c40c80c401d049071580010304500c41c90131142401c2c01543da10020b6101c142e00403005800140802040c19024000000340825000c043d6101d0b81c042e03000c44c3d030000d00c241000300e0720b0000c6d5001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 414484739 1250 414483489 414483521
    0x109080a0c0302271902040b070305030a050c0c1e1204170706030c1209030c08040e1e091b3f0a08090d020f03030c1b0427031719 57
    0x11909046601c0600030b40c0402d0003030051070445c8081c124000244502c1d040841ca100300490800c0074107901c400954421640248100699120503100000a00516030106010341c07045c00c0392680b8000220380f807039140c10001c04442c8010701031505030340c03260403940100c011021800040007404004009410040000e41020000b22a541d003004240103800c00060350041e455480c0c44007018481d0555801850b0020242c0752501d886440c8250841d8080d11841c201c00310030040003414011000d195401200391400420b40c00c10307203002c00c0c0c09a0010440b03c0384c4c40101c0d40e120700f00c1c9601d01d2000c24580700011a14613a081000a48002040c804a8101c012584440b0710f110004400d1401c40e940002c003210103c01920f0648006894441d0034441640c01d40804121696902c0d8001506611806031603e108010803044003030100300c0e482c10003160101c028400d82d41d010f00350503074030710140c60340240b4100022405500c545010724000b51030304a084144220680566411442200a00060008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 414485989 1250 414484739 414484789
    0xd030b24030711070b0d06050907080f01120f0803040b010806070e0121020c0a03110c0607110108090f010203093301050103110c15010303201002090109080a0c0302 72
    0x19410348180001401e610500082100702c0804040401450000307040110129640e12421301005025007900c0c4a09405540c00e440031815039401400f2482c4074010040101000d03a00c1c0845e00303180c0480c511415101c0407420000a408100203600540c03180f070058030003002c40c0d494541407501c6c0c400d006100c81c1c20040100d44602950fa444002d84d06008103060120f00415400b607220b1000344a5164031401130312940c1c0c2801d041640110851029220000c1039408003000002071200b2449100e500411b20b01d00b00700780d030300298003400046070811080310856144104001d5110b00320f0f4015580103038181c0c001c080c03148080c2c0c1c05100081d1110294410165a07405945006a4503101030181e00d06058454480c84984000704045d0362240d15080115828600d048074001000b06080c04280c0000380300c2640d503210b40e01140101e2000002074401408001284544034009401046140381081845040007032400c40410104402600400e50040c0c1185076104114002102101104805220750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 414487239 1250 414485989 414486049
    0x80c1809270f030f280309060e0307020112151d04020a140607030e06090604090227030a0f0201030212010902120f0108070e041a07080702010e060114040209030106080d030b 76
    0x80700361480078444c0d05503940c0341d200c1211542600f994103038800300504032001308400e03003e034180c018050b054003408080043d5000d060115840e4494418060302041d0425000d4050b942e83e5402464161422051645407580750550402c1400b180c11120070721400301402e0100751724001482c480180000003145031081050001704d101c1e402006005010302ca41a402c0080070f40b075450458182d86070080c4119521070b15841664000c0d0000003422813481c001c903402c89101e580030340c07012483c400700800034011404c0ca507035000314040f202d081c00c034100354090115607000070358510494003809001202680b5aa800c00f01502c400304020f1801842861841c0100a1007070041040c5e4242d0311100bc4410450382d50b42403021640e80044240e00803180084200000168003610150081c42140c0c000d00001d0500c00703000c0e030384030004e000386d0070030f0221641c1c9001a460641e0040c15021005030001c910142d540e100c01d424231740070095080100ea02c40703101c0b881e517142004a2840340100020100b40090201d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 414488489 1250 414487239 414487243
    0xb010801050f060d11042313030206010e0a0f0908030a15150e060c030a020d17010807050607051c2a050d03020a090306060f09110307080c1809270f 65
    0x5010180115500790b60f0805006144e21040c17440c0d1000f030000c1c0507919201045001007402d091580a010804c0b034041805862456400340c08160190300500070399090800e407540456002c3e28180c05190f890780103a41240581c024103140d43e014005d81601c82c50000109000e481d414440c0c40c480724443c120600c541e200b0007282c440d4440c105c2c5000c4428801002c04100071f8441d001e40004544008615814241d600180c2d034100310066644d8124410842410003984110a000390307401c540107a04d0601450034280080c104050003401180c1024501200d41d802d01a00d42030200c0c001034040c00210902c0f01c51203001800c1d02c1000c5040c0203501e00d41d0300d91b17035154660851020209a00060003a001502c2503403888061604100104031007903032000c080d488941984688440642008a0240c0412442040d03e00c5035103152600d20315a07460308a401c442d0781c04400745c141300ca040c4100044d0191600034206215034200c2c0c400c821400c0004070580c589400c1414101c40a03400782c0c9a4841200300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 414489739 1250 414488489 414488491
    0x2030309040c09210b0916030809030106050904060b101b1205071a010e130c03081e03190c0801050d030809120a020a060e031608070215070303090b1537060504030b010801050f 77
    0x1c209d548850498000030302611203640402c0d48400c51700c081c84107211a9620580c2a200c040700c1d405e182044c0043c00382c401c89c103a49420030f141882c0101200206010440c000091a183e1400b64503000daa075903440310040f011b14020301c046890340c005100d00c6075001c00c0710b504041d1658821907070503102c0c1d5403100302e160503003c014060640880d500116500b40340d01c850700304001c0b2405c03580300d160003494142c001c4c2c2d941c9460781000b42440030800709140100b0302c540c141d59000d400200c0400304d9071801c0c0c0309031402a00d40e03001441120f83c2084c040000b000640341a1035142c1c094080e50360b99041000541e40141c4114180303070400c2000c03421000b81c641031100455404040e0f5030702d41d00c0600000d01c24a4005500c00302e0798000003100c0c810141d159202d600e0f854444c5a80089c0354503003030054020116070440c116080000f444100c841000e811843d1000200c50104a0092580c1001002c1d440380c801e502c014041000498180301f0801074051a40c054402c1000170010b07858050803e0701c1c0710700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 414490989 1250 414489739 414489743
    0x60118050a031103120c0a0c0614040b071b2306040b040501120e010204060504090f050906131b0807030320100e0a05010606120605040902030309040c09210b091603 72
    0x3c031980506000340c5040c400d0f40032400440c3e400c20303110310f00c9002d825111a00359030101d503400600c000100e405406403060180e41c0300002e0382203060a04102d41035190361303c8030b04241c8608032100a480c0440000c811124064402008001c04d4501c02072039141402c4429800c05105042c1030005000303c024507000d032001c5800034640b440e40025113507071200003031110103d0005079500020300440c1d03d681041c024030450751118030820040013600c415500701c035000d94004060b5004040401c0a8000b20441d601c1094040d02456800d40c204081062032503895512480043d0000c103420024550000821516070070040301040182da803598401d40c850840707003080c4c501e15648501034256040c0801420155075400700c001c001031754032810301418441c08004021100c0c3e08182010030241081e001d203e0466502800950901d10582c0400014101d01d6103500700300030f0707244800104184400c1010a00d4048124404030300401418440d1600c0d47c01800c94130b069010407050108081c9081e1004100c035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 414492239 1250 414490989 414491003
    0x1020408101a041d01090b010f0b163f020f0a0c03020d062c01060503030f0426070608070207060f050307030905030d0204030c090b1005030c0927060118050a03 70
    0x10b80407808000c070f89880901321607290720f000d03001c0c1d0170040300d444a11b0585003508280b21446617070b5184c103c554480c086035903074507000d64290400040c0410b200548446015900c9105803000c0c40041000c011044400300d0080403034128411090741c0511409442c41c019001520014203680c40340120566284002030044200140240c02e00c0405d501001c020308413040100d0102c280f10820300407010000d552a800b0b541b825100003150310740041200c0e0301040b0010303890b091501d004c404907400b030080c90151034200002140c0601c0841c00f4020300703000c2c003102d8032560007606201c0c10091038804260000007d011040c207924070455005000d490f440851340c500403454140c2c40c17401d1411030048a043c403807120700120b004010007515006410580d215101c04011010b040b00401100c48d07542150140071a5080002c241c1001d40c042c014200d94201034940c02c003081b401606083c9042c203c5080700c8a4030324000522604d9a8844542c4440800344034800d80030504002c0000e6800c821807200419039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 414493489 1250 414492239 414492251
    0x5040515150603071d0105180909010f020a020706031518020304050a1b0302031b0901180b0910090f060302010f0c0507120c060f08040c0308032701020408101a04 71
    0x195141c0044070561880203003009441e030a003400c0180030460320f1074103483c1644c0901407004565100d0025121005d0b10103003030703506d5804c0140034025015400b8106420340c2d52600c546516034401c6000401d451305090b8000c0030032501d0603000500300c40721450b11049074500b059042003428403d01d405100307007240440c0180e40e52598a8058071b80071b95558000c100d81c0a511082c18440c80329070309a012039009034295209134400401d1008030710f204035040d5500c41c40c0700e00180309480c24000a41c0d0003100341080047c0f188058800188100405c84000480c1ea514143c10f00254455000346600c60300b840328240134660031a03001814110700d8064040c01c0120074101d20381882020054040203024641c402c1ca07007403035581464022110070b0302030038010130100002c226025102d003050510440e0440d81c8904080d0035648d03006a07031b0303001070030700ea22001d51802d18a10a6444801d007410300c172038600005946a24040b1030070f08044010b41d601c84075500d00f10508032054042040654854012100003a10b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 414494739 1250 414493489 414493501
    0x70e0402090904030e031002073503010b07061103040b0606032701050a150f09020a09080f0c030106050423060127031e200a08030d02031905040515 65
    0x280590381c001a80044140c062009040d0000842d09140303200390161000c4040741d01c44103045c0c0c8200076005000244402024410880f511080c00005410484411120b032005003808003641081c0c102001c000c0d40000d11000700080e500c50040c0746120900344504525007a02c42d5807100348000d0500b40191800000107602c071150b820300d140104c480c8202420080e51a002060080c04102c5040705543e01d040780a1002ca41403006110841d150f2101c0200124205090320019410040e03140f0180302509601180c1d03060b060101c243c2c000c00c9040245070702900c40c4101400d40d4640c1e0b01181c0190715080c82101820030a52003000c1801481d0005515030f120100120340031180400c0d110350b405242100c00d040450760400d01e0044078003030f5400040c9030107a40c0030a00e02054803800202020740041541041c01e810a4280c154400d0041c035030342c4615601e0300410f0071688500d050b1107042d0b0340002044140040b60030b80150203c54100c04000b140340540d900d81d0b442001c04180b04808904c04001a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 414495989 1250 414494739 414494741
    0xe0129090a080c040501050f0d200a0e0412180b07020f042307030c0e010305060d08040902070320031b03160b07020c04090210030b010c06021803120f03070e04 70
    0x2a000c0c058a0301d2403259558886940301e05010120074440c508000001071586400c80303164200a1006100890080c01a07458540313031282444074520303018a08961329200d13912000410000c1500075860b0b203080c40c1ca0f180010303291181c0b110910520403082c0311f900c034203204440c400d81524400e0f10700687e03a002600008010904e40280780d584203045c04988004403580e441d080c0c500740061011078046844d00c43c01602500c0004000740b0008007480881c071081c8d0f1282d0820383d04007402030a200401000d644503039516901030b0304001125600050340004155214000300400700c025038400c0c1c0c61500d20341e60303039469101d20700c1044e4100341400b040c03004440c428000c55500392120b0f0b0070b030412011586055a04200c0c1264040c01602400102c0b50060900c0c0c06003520302680106200400d00700c011068008021001c1c2150400c205d402c1a08001a107030b10040990389000400308440f0144403080624019841c41e28048405090044205041095091760381003155070030925200000b980105e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 414497239 1250 414495989 414495997
    0x22b150506100f023d0213060503040f230105070f11190204050423011407030203060d081e0c0a0605061009030b0a0b061201050f06070f02090603010b060a030606090e0129 75
    0xf18170519000d1a44646009a5004008010285040030041039894000765480e000441d0090100d81e40d0000070800181e0a00142d040908070f90140b00c071070455014403508460040368003401144001c14507200305900100f407642044112001480302180d00c4412001104030f44800078080d40d01c030f030041404c0003920599004518920411001518090040701d0702030005540c520b02110340000c08150550702c01c4c000c40c0c0c8160006000010f00e00c1c00f07541c50540c2a4800368000c0d183e60044641c0b1903c6110120090550606220041403000d201c2d00300182228000b5103c0d81c801d001c40302000010341d070407100910880b600210311040740c1e41c40f6900d00c00035010986c40c00c2c1e403140700010304076000700d00c89031014180e030320a403030150801d94284240003a034895181c01410903008644100014034000066603401603010380042500b03001e05010600980081e4001000b0030344a40c0d0a01060754003018040c002d00e58007418801c154034029502507465004112200003203800004650030644413000c403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 414498489 1250 414497239 414497323
    0x10201091a04150e030304140c0307030c05030d0201090f0b06030a14100e0106081207060207081204050c030111090d0c030b0c0c07090603022b150506100f02 69
    0x85021100c54115000c4040d0100d41c121903d18415a942810425a22802032002529001180f45450719104c11000342a04020302c1d10302c0c420004814995181441000c009621810b41e800c141c80c1058100342c02c1140e42e034a91070440e03240110310707000302e0201810144180d4000d4038010998980e00046410500740d0480a001b181c400c0360700e000700100002d81d800c51200d41100400400c00348140d014241c40e25841101c02641c44040a114840b0301c050003001542e101d100010b00d0900d4694581515411040d90884004e581d0307030400003805410302000c10300c00c90440003003040d10302800100e140c6005922f08103014400d00c10120017000703601c0e0300c24005503410000c1000c040c80c0009511545600a00308194140580540090080910300800e070613698020301d1003441c040059620511465640f0b005202007403504000004550135240c40600100c0300500400c2c0d43c030b0b04006100410588610034020070003540341d117500003640495000c07013615003490700c0f101240004a0018880b040c640300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 414499739 1250 414498489 414498503
    0x40612061203050c011b090504020a12050705120a0b09010b251101142706070f0302060726060105030606092808071514040e0915060f01020a020d0201020109 69
    0x1c0806041d0428041c02807941907900900c00104240e0740c032509002e9103040c803070104808007428041d0346003e0f0044c18003c0090b241031601c00a21207403080c00d40304207a80390008104005110101c261401c1405684031072802c005100440007400894194034051044154514000c1007403203000795650b0b41d08500850140c1140900130040c140360b8888010226504d01060200405c1004409218159031080450100c0c110680c2e014214540c010619600b1145d8408000c002240000306504090724841c0e0080e8014000380c9000711019001051140071341703180380e072101168000d10002c1c107480f81d441030082c6480d035280c1d22083d0201c2d074180607440181d45d00500b0f40107440030100142c00807954054401220404440d501c20300300e81c03125468003d028030380c50341d080140302850145481109c10850103000615065403441d486901ba071007507c1143d015004101c40804c80c40c0302a5106400c54000c44c1e002c4000c4a101002030b540d600401d00c028059901010f4900c15a03000398403000390f10382c02c075036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 414500989 1250 414499739 414499769
    0x130207060b0f0307081e01060e07030c020706030513030c060612050309030d080f010e0601020c220606020d0f030506060705031c0c02010c0c23012405090c04061206 72
    0x160803005080e401c1009406003100300080c40c080c0c507000403518101c5032218041d0112015401b0811145003130540e11030301d50f41d00e80b00c000410008600190703100f607201c0e40e8002404030201d20003d0030030b141c03031b448282014101400c1c02401c80c2d207001c011203e9503140c04d081403010341c507113085805000990700a0f41c507403929105130b000717020b000700080404003011015502c20010003581901c0600094a0580c0c1c0101803030014000c05c524000b2a9800050500450f286a4407050014000c1505500104000741240384c9030b25410800307000d031002410150000e0701d4031003100c00300140011080c03042c05007019100e201044a035110001162641c98020007607070760328810310302068a001800994106c0e1036182009098665106100720b1119031461b07035466600442944500304000340e0081c0c0b821000da845502280c00310740034807480b505c151a59a40c081414210040b103000302c1c88a50205025254803020408044d002004440a40c0e01c43e00302070803211070780080c450041809820001401300b20f41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 414502239 1250 414500989 414500993
    0x106080610030302060a1a090901060305011107110d02031b15071101020709060f0608180604031d060c030f130803030709032102060109020a050c0610030b0c040b03070509130207 78
    0x60040c0e003580c3c026001c882c001d07201e00d43c4442c1110391040251102c00c101041082c3c5901e007070030020741c00295043c00428200d4680e1580c60031140c0806584060700000203006003040005044031010880c00c580e51040c401440d004240c65503501024095141000c0101c4400e0ba9030b000e00f0b14068103502481c107515107005c1e18003401d000304500159809481104400668499a80a90801d5924a0490242c100e117800b006a4406801819640c0d801c620040000750580003040340383d104501980e2010001c2161120441c81c0b001e14104050059404001d554802c40d0300100f01c600071406111a60742d0f5a00030140030005411680260302203000020a2140041e88030700c102d829280500d1040d0079098901c90001c940414901600016800c07500c010001401d00c3c2d03010f081c88092030f04026113040c02101c42c650404000300c45814144851501c14014011005602c1d80e100088807030a070714190500041c600c05c0d0000902d9002004800a08581562140c210240b90300207030740c4041d07445001d14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 414503489 1250 414502239 414502261
    0xc08030601032703090e013f0b0f06030d021506010c0c0303030b01030b06090d0f08041a03010e090610172109031c05090909031612030501120305030105090901060806 73
    0x4000c0c1580025104000418021300e11001c3c1412034003d1143c1101c0c00c445040040b1035424103030079582e00b0303c1c1c41100e002083d0210b03c5c1d10009061252700c2d2403d09143c600c1c2e03225526140a814140070794042d12112440980010f00ca286000450754452040c0c0d8404004907210b42c0d4203440104610118a0300100701601500b0100ca1540d00342ca0038040d00c2a1074081c801c4600650781403d621008001d002408100d0314840c1102c0c0078042d2043d0b1345010f843d9600c41c403040c0348024030014035203000001000100711229007582c005500d1805000700c0d00344801040a411264012020304c0d40840402c160000400c014041000702046205d403102c1503440310f48405030700301c126824024007035211081c400180741c2c0c40d40160034940e40c444504100720320080c003040c400d0040c11501a40b00400030030001c1d00c01d541200c030f2914450090030600c02c4030041c0c0202928810b0303010240395070011242b800000e800c20184c0741525021780f01581c0503680d142c0e480d4003420b8590301c01c00c014001c0f0300c14001a0440d0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 414504739 1250 414503489 414503561
    0x9040507020c310e0a170a0e060f0f09030a1407050a05060304020a03170d060f150327020f090f060112060b030109090f0b070513080c0a03141203010608040b09010207030c0803060103 80
    0x2441d03c952342c0c0c0301551070500c4484c1c8564944a00c00c00d004120f400c40c0360000c0c034060440c80300040c0440c0d0001005a4580c0341e419203840041d90142d000c0d4500700101e01d844120000586020b440d0300b41142025800f241c0c8207445800024041004e5103143e0610741113038015074083c1c0446000c1440f50740e54030801c41c4a0510f0a0090450100052260403402402400740138000805800f10143e0066a5200303a0741c20800804200d070b20030300c512900c5900e640c485280b64000e8020240801060030404000b42940c4110142c030000e8a051000802c100700b040000e5904681300032401281c00103940c94010900800303c0b000422443c030180522000350741c40070142c4024180143c0628802d41c48400741556100c0c0c0303000d09a80041806030510002e4102c400407006402400211030502c5041b102014954200f60007060000f00f000e4100801e11182c02080c03030b08007401c60000c500d803490075103000301107514810015000c86800404615a64400c0d0301c80b5503001e03005120380c421014400b00c03a04c090b1071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 414505989 1250 414504739 414504757
    0x5010e0d06060905060a15080f06031905070509070c0f020105090f060c0c030d05090a0b0c0102130602010e1203010b07110a080109050102120714071709040507020c310e0a17 76
    0x102e540100c0e10b5403900d2447c04080c409078441c8000c90791410310034486124002c214540500640c203142c040c2011490211080f54403490240200718282011700881c000000c0c400d004001148510f140132541703080c00211f0043e020b1070482d0345c3d1490140480d0354031014540c9076070400400143c1110401c004100a00b0401085090303400c0c0c02036042c0c0450f20b0340036a0a540f58051660b55040140344200001800d04c04400b000141c1040f40b40c151000e140080c50307002e0317030260b511a038210b0b44072002401a80312904030b45010506550604598030b847d405100350041400d03e020603110303525960f86039500c0080101000a0010024503e85035000c0c0d04500030341c0340f00b100e0110103e0581409040700c0141e00ca52164000c2c1030900c0e54403002c0401c61441080d814401040045100903121405080d12900150300204090301c100c000b404440302c1403004d002d51811100d194030216640340500c0602604c012100442e04058141005043c019181002020105100510345d038040500c0b003c0c0c40502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 414507239 1250 414505989 414505999
    0xd0b04060b1e0c0f01090317010806040804290a0504060806031b221503140c0f04090302030f0d06180203310c091a0402040f05010e0d0606090506 64
    0x1552041c00c85031500994006065603840a06001c84040010014042c108180412503000e020302c20441c40c2181c00c0302c081500040c00e1381306280891400031210500600c8402d004017140e1030319031100c1c1ca003405540120b04e129664000c041091003030b075644205800040076040c0d943c4000400001d859075001d44500000b054403940003d4140c80d000c41c510722200000340205000603132400c20812000d4450201e80396107003074400036420061181c40b6602107064024440301c003250840c20030900349414510361408560100403110016201c00d541e1500114042c1c6020484078220700d001e03400c40c000c1101326441c100000c600c0003a68501508140d084441920901ca0b120000d8450030040c0e2004940441403441c994292805ca44444407110034411492104841985281c0d50341c01c030b800140f030780701c078080d43c4d1a070308407010700400011060403d00d01201d00314602454003131002202c054600c82c15062005150f8040300646502c40d0120050340c0c0715004218194840b00040c00a00e01a10100d01074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 414508489 1250 414507239 414507251
    0x7020c10110d0513050f0906090408190f030b10021b0a1d1006050304051207080405040219020f0705090414032b050c0304081204060209060a030e0d02070b040b031b0d0b04 75
    0x3509040501b10000d41015040b40c2c440d80c1d801050040000000e8011100301c2000c110a0a041020030800c0c0c03101500f541c7c0c0c400010284010040645012480461080c0c1c19122200402d5400003449246512a40c0340201e660350014006900c1203002c3e40126041130111005050030b99a042805200d90b1014500340032060719a041140c2d2400120780081050b8800685148070704003c002800e4074900c6254880d241980300e2000c13400b66041000203007081c50850351420080e075018011741214150038401041041d1812001410b07552000c0d1003e4132401c400c0d000403035a41d2003442102e00c0402e0395410480c400c08400720b0001c40c00c614607207100410b4a0040880c01011908013180e0149400034800e50604821800168042c017016008640180c8d0800c220b010540303401014002d1420192070014aa0480c1504503041900241c07003241103401240041c001d40b03e484081e107090b68800110503840f82e84070680c1c08009022401c8070084000f01007003403132000c0141d800c0100300080590301130200d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 414509739 1250 414508489 414508499
    0x30d03050c03060922210f09060e030c0406060e040b270c07050a21031a2e09081209010206041e0507180c02010e0c19030f050d0f0807020c10110d0513 66
    0x10408404540c2c8000550030300040181c12b02c500c525401446005040e11000c020401c0007034101c410f998084400b1a600050341d03141131620b0300c41e14801c68400c9d07032186040040d580084820b00000055480102c00b80804500a51503c0040d101071980c05000c036040ca801e035040c08ca407541040b040c2c0e03503000f001c041d000c2d84110348a80140811b040100541d20f003020490b004004840740074001c19401c060030706844850300c0d204d5500340c043e5a0000d454201d645400d182034241804904c440d034450009003000391a20503640000c0c403661281d000394070080281820360b50414020020580600b8a03c5031a401142c0380c01d1450a041088051020400c009881e03424168282c901010181001d81c2040c10103910908201c031001b079003115821700541103240c0742d07a01c0030102c0344400c00c00d0314103034444011401c40a40001c0c0490903c03405085c020f24507d895031000755a400c030050060302807080101200c10745406024034028000000d41503e8502141640090081c3c0214146018108580400042c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 414510989 1250 414509739 414509747
    0x60501090222051e031501060e1e030703020613081f0b041a01030509030c010f1a010801140d06020f0706090506060607150213030203030a02010b030d03050c0306092221 74
    0x1044a03c041c01c07150604685a0060000020a144840d05070142ca411052101e02c40904180602880c0d00c940c803110000c282400310143d11120004009903850850043c90b60f0001107403002c0380d60448106581d064907410680011440b5070120401e403003101c9002100740b0f50b0b01d40c01141610396590030019128818104015580c095043e191003028424010016502c01d4018550100131603044a00e0152400582803c69074048400748a05a942c01c2041820941e10117130034440000340f0300003040e94107007010b5142060035a106d907442144100d50603410442560199442811205c2c1c60301d8481c9000d080c480058459840119014000e443c0094403c0c5007140507245000e400840101400c8040079002c8002c0d800051101c80020a0b0403001006950030401801003014035400403d620810100345481e20200803d03600500d8140801c001880c80910b0a40e0b030721080481e04580c40d5200d02c1030b210900848801c0304203880035400d118100380a109050a1654084061640c04103128110112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 414512239 1250 414510989 414511057
    0x70303120f02030601121a030a030503160e01020607030c02070f03030c140105090307110f060c0a03030501060e0f10140f1b0d020c090c0c061e070c24090605010902 72
    0xd0118000c60111035501e042a03000d09031911009502001c012011f10010b40f0f403180c03c800840004400000300001450700d6a03141103602103900300f40d030101820000203912200300615550405a95404204a042c0308100140040c80c80d2210a882c440c2c5038100103000501407030041d02c01d80c1c000c082c0000914070500c0faa034403c004c1c84000d58100740456803440f10f1103903c0c0c0a080d6000c2d17000d404541c82642e8600041c1a0039207a07100030310f01c0583c540b03409000d54070f05910143c184280701c0c580d0000754690040c0d503501c41000310b410309008624510252102c042d0a0080341140f54085210a841017154001703002500060508502102008007465640c103070b840c410304010b03048903aa42c1c140d82008041540c101048004507414510128911864204106d030021044c44003000140b081c060780500860300a0b201d031034007100403519600d907600961800314007003644003007245901e25450401d40c01420400c0d1711420600095070b4030082a07000c0d401a541030611948040c0141d00b0390b0685207990 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 414513489 1250 414512239 414512251
    0x90603110d1101030b0a15020d11010b01051b15100602013210080a0506070905030c0109060e01030605190306060b0c070e07141216030212010b0a030e070303120f0203 73
    0xc1402da08107030046024040100142da000f445110b4045035506400f00740829038000307a4000c182c0380c004690010f04611203054444001d92400380400d000740d074068102c1d8144500625a0042c100d07065010503e0840c5031040006001d0000081c0b090f0400c0b02c41000741181d0941c0d000303211144240608009080d840c0c40716003284810030100b041540c049455242d44074641d0307004e0b011400d60752000e85007040031150007280d0542001080000c6690490140c902901c004d0700140400c54081c00042c0c4000b040b4040c08040c4580780f411400c86a20036007004000d094003800c44607503c403144100d100b9a040c2d03400112103907030170244080740c1c82c440941510343c00b14021008015140c68107900c1003061002922110400c03090700035145a0340c0301c01d001450b03d500240c01290080c0340011f00c42080c0311803149541c041500408c40e07444520040038107541910800f44034240d6a420182d82580107000c500124115070003040c0d03000042c0364002d151042c03841e05141c014040b001a40780034600b02d01c030840d44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 414514739 1250 414513489 414513503
    0xc03071802040315091203020405090a0905120d0614030c1302210117010e010209030c0111030405031516020d1706010e1c1a131506090204090603110d 66
    0x4018100c200c1030801a45500090014030301900d945440807801d0140404507880c0f6140d10a6804214603410039819204807440d0460400341040001140401e010307000480c12a11032642c5400e0003070502410030065002a180d960340c0c3c0c02c540024001c0c00d0030f80f03d01c0c1e036203070010040610300307082c0892000c407446801010f1800200f00d40c0000030080d0090b200e481529219103001880d00c62098800c80e003c0c000c050300c40040c0280e95103c19081d201400c42404890b401403040980c60340b000140060b10100908160401d01c11b03003440a1f1840c011540110342c14492241c013003010302c9400c1c507054082c50440e46101d11100c024802a641e5800051115000035540440b010706800c1265100390090414581403200d0140100060102d0a40442c2e509006410708422410400c06001001c103000b0014501800741c90314144401183d000d0f0b160107429110804e4035030102413407682c803510141c00400400c544403501d0300320f070500038003850100311030510500a1a4510340740101142015540c0252 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 414515989 1250 414514739 414514753
    0xf061e11011407030b03071a0f1e0a1724061b1b10020609030301230d12030f110d021e0c0601060801081b1002100f1a0604030317070908060708040b07020c03 69
    0x94a10940c44950701d0540f8078212b45022101c0500c440c000d01c08280c0036614180328a0325146000f848180181560701c40710707041c294941e1144aa901c1488044001301c4066486210420040400b1300c10400070003041d01848a840e0f201c4c4040c084240c00c0580c00742d0381d42c04012090399013031343d481c4826900c48401d54810300c0100302c4503503003004000494114500519481c0c40c00004200c20790701e1150112944000400d52000f401d0b4507110704009410642c0d810702c00302401c1d01580035940300320700071030000a40000e241e00c1580011041c041d6540c4020114581e9040341c0d40c506501d03140280500da0010708503500001d05100d000500f21002c260540041460b911510108580380c00c60040c503800b0f5000d4580c40d5000005d4500c02d4024807554490080395038002d9050614900303020f45000c3e44541c0b401e210520200c0e60007100c811086070403241081e1103403204001650418807a9104059601c140d208119030964800d40d458000d520075840da040380e44903201c1c16610f907522550300c04c0d0903500a40c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 414517239 1250 414515989 414516007
    0x30b19090e121e0702040e0d0f02160308041403030405090411010e010e310c0302030610030c0c03030b0a170c090a230c0714070f061e11011407030b03071a 68
    0x100084c10018401040000c58550b202505410851040b40010100e00e07042c58115803550140701414a03400c5e1030346124001400c540d10300500380035500031011140e280040c6044680c03810421100036103001421007070381d1302d080d02d800356502c821000200d0010b420310b0300201c5694014501c0301ca00102c0103050058501e10b007403240b0016046c00350003442c42040d00c0740d1445801210b105000f0b40c8160341d074005d60340341313401000d00051005000c0c61808151a1480b417000d01035004170300c00d4041c0d40c580740201303086071698000b400703480140d00220040f8a1040d00e0041d80a00094400718103113090703440f80002c1d41e0390051780003103d4403810300302288007000140006010504400550095001c03c1650420b000ca844a03081690301080d001d01c1640a02000d0018803a40f010002c0140050b01d424030b00c0102129064075041d80413801001444200341103030444410a40280c44e0880240d600b1a0061030020402800b602c01c1d192040c0c040c0c01840703004100b801d45000411101795034601c0d06c2d46002840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 414518489 1250 414517239 414517297
    0x201090f0b09010f0f02040608060913140f0313061709060115020a1a040212010507020309060c011e021308060411090405030d050702030d1109030706030b19090e12 72
    0x20b10300d180341c0d50396518000c0c029800f480342604404c0c26400c0161214103104000d84000c0e07014203e64450786800041020100b80c000e0300c2203009501464408028144070042490010070400010090101003401c01a405040a141e81281d91513030358119003e41020090300c1c0038400fa689140650800c2c001440401d112560541001c0c07003a00c111ba500780c8283d241c2c40b500b40141030a030308001604009000c2540b4080c0481c19a48d200d00e4001c104600306414069034034850b0800315400340030041240304000200b94000d80c01c4142004a45042801200841000394070911041d8056082000c000c241c1040c00510b2600c035130fa0024034081042c1a81c01000340702c0b100108100c3d0644001c001300382083e5031070b00416000d03a40940045441e03501481500050302c005600100100c8400d0081c04959a00014501c040f20118100002c1d0101e10801060240701d49074941030307440d46100c000180108103944120107440c05401507134030011405440701142d100d06041414024400700e4031750765145407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 414519739 1250 414518489 414518491
    0x321090d03020a090909050d0306061418121c020105090102090114090a03020d050a03021207020f1003150b090a060314041506090e010209120601290c19030207060201090f0b 76
    0x10f0781c28101030450751004c107041518281203044445402c92400044a66010b0158901900b00c900b8120580f1550050b0700400c0c0c001c0c40800e1503112988101007005071079030020809012040d4054501030f9245030040311000007212000d000641c03810b000600c081c0018402c4d40c0e4a44016500d44217071568245803c004c40e08041c0406a0090245000000603911590004017180c0700e480030f402c0582d0076080107401c0c94240725003001141e000f00f115a00694894211702404c1d0b404803044801c9480d901d200b100205010f04d4012911200302c1f0002c6102d44e05007015001500d000c440d1071101c03030380310b40044007640d100d00b54403020303400c0045c08100011005a1405a15400b020b80041c55982d1284a00c0c00e0f280000c540030407a95000400c9051428000e003a5100482048001c04042d4900700c00d2aa91405200d411201c00c2c10f54240048102d140340b08840710700075000c0c00c4450f020300700b034807251000f000684103d0140c8629500058464010302034410000d4000d8240c0c04807900c140c8a058001d04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 414520989 1250 414519739 414519757
    0x30b09030c0304030c03061a063a06050f1509150d090b04060b0301060305060105040b190b09270106030c1206030c1d06100507030c080307020321090d0302 68
    0x305005501c06074070200064801140030740303c4152000c0c610305180702160381405490455040e084c0250b0900c0d142e04007100c19024034400598601c0b08400f002000942c108201b001044407240c000500d6000c058004400355407088030826000005d00040000b0b1000e9102c10324403071102440141c0d16441c00001c21520311140010303a903d0402c07120080012680d0803942260382d03852507002c2c402880150f05c5400c0e003035002500204000c0781076403506070707482405114080c41035403100c00385152926071520f0541090b045a55141040c2d8550b0b032403c4082d000401744a000700842c40b9801003c1c0c98151031041314501e10001ca103166404c21000718081c0c08288112018040c4000d10701546420300d1140c503005600480c601c004240c10207031b461304254034000b0b500000508903030500404d0341d00c1c1d00300e4000303044e49070900703030360702c445600d810b4420340e9960002074207222000c0204024107030044010300825100001c1c804a01340300780c4266070107038020b80d45a1495840784543d10413450003503005014040b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 414522239 1250 414520989 414520993
    0x105090a122414010504090c03060515061c05090a0b0402300109060b03281103060420010f051207140403061b0801270609020a02010c02120c07030b09 66
    0x40107003891001a995400d8000c2d88642d0340d84030860040360310841d9805040c04482c2840580d885841c1c501041c1e02d20300014101c1c0340d8910128503080c82098015500b0000a4889600c40085408603c0c9600c0303400b194035a0242880c3c0011102503011038001400c6500c980781141310385542d02801020030142041e01c0143c5c900c00c10030480b150116400c00e5000207401c001080428091a1520603241c10403a039174000e6105041d0b004010740040080100c20303544071070040380e410460a00c401510b03622800303940c040c0180c006020a0003950310810f0000030010110500c2071600000441d055402001c1902c00102c040c090072000f110b100d60b0054020304203103841e400c0701c080c1c154040303041d0b4480c0d0710844020740c0e41c0c003003001d0340c1000d5032460200d0484d5003003540b599898844641085004120540070340500d440040406203145c2d0301050140c158554115258000144060300816071105d040c4054451034100075030700a006812100b82c1c448900240c5605851a505c03207440020140c0200014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 414523489 1250 414522239 414522263
    0x50609040b190513150501140f0f0a1d161e020c041b02060108010501060813150507030209120c10110f160e01080d020307020904060207060e06060f0105090a12 70
    0x510b106004030340c0110709a0790115004412440c101c40c100080203050f00c5094140310041040075080014400782007400d540c22012002d001c0c0000f0200c1320080c003000c1d0b0000000c60085030b4014959003202c403070f0b414010340c1200c0da2940503a01c807100300b48400004c0011b000e2010b44e018902560001104d80322940102c600308132180001400769607401d070340410049002c060401400e81c5c100309050041a1880c02004507505013000109642d1008080c1d1a1101c0c21050000030403800e031032414001c2641107010440b40c10070340340042c040e42c0300541031881080545d201284204003c12843d500402c01450303059021904c4105492080c48411900001d010750030500604c038400f4018240001501e914440100b030070076905515052040e040504213074031101108044a400000300c522603601100d40220540c0c582c50188007900c11810014115400d000070b080354a5030000d2081d0180314111001e240c8040d4001c011142c034041c81c2e04460b409415850200609100c07107400801140c0219210038407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 414524739 1250 414523489 414523531
    0x120601020d0306081218090f0610050301050307030f020d0c060f030b06090d0615050d0503090a06020d020c010518040c2001200c07150809060c040501021b0105160309080709050609040b 81
    0x100309008c80d00c2c030b21828090000c20000340707814065052000200d0a1071400d6504180100341d884001e400014a407072111282c80c019543c441941400c4581d124030a602507680f1450002d00300d681b2050310a010a00300007134896240b03841c1e0155441d0350006130105c02654000c0c0c4410003d803901c0c07541a0b1551812510129240d16441c00c1501c2d1a8011402035986206800506c4074a0482d03030320040c115044003500d40071a650200b0485603000091a0254035107139130030383c00034028801541340b582c40341c030380a88105001c0d0401c61101101c1c0441d681c0c0b035800605090200d0a079100354010044940d203140c68810b250350b02a018141d405030001c22039650711f4503035030311061511494010700c2c00308510004008d01d5400800c9403030b9105080b0300c1d005091500e0040041c0d550040c000b04120030044201030380d06103034410829130720f030000c0303000502456448030b00b03016001035014002c80710580100c000228642d0103500030f00c1d00408000d0071381d0400d0b503a241c850000d00a00a0a6411414034040c1c180d21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 414525989 1250 414524739 414524749
    0xc0409020f060c03040e01050f03060403050703090f060804030201050f090d1103090621070504050d03030b0f0a091d0601050604060f0302070f0b0133030e03040506120601020d0306081218 82
    0x4200702248004c1d6500c0341803442640c15000c0c140c0c031540c821980c00645030b802d07842c08100c0c1a0030681c0341c1440c13501e42106207402d031400175a58101c45042c0d130f1200301c00518541e21540c40380c02a4043c0c0c00030840e586030085500d02c145821501c03562564803443d6400009486040e14428035641c0900703032130400500000003801c2d03030b0014000328520220851410040d0a0040384c0d2074000d072080c01c0840c501440c0c03001003041d00d40741e140043e060640c2c407054440c107916503041b0210164030080404403c603480b080b00d040100034810030000110003401070036113110800154141a02d100400a1703061524144044904c04c4503500d0399020550288904400203800c861481c030158800c0808224541c100200218040c207142a03c6003122180c20400034100c07100c0e03200c100c0720065460045010004d0036080c0703245210301d501c40c41e08254000368095180e0070a152050003100240d09075140500104070440a480da540941d400640120460721b20b5a940040281320345d07555804036191454803000011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 414527239 1250 414525989 414525997
    0x302074b0b0a050103032c060c0a020904080d0b01030501181d060109020a0f0513140a051512091f0b010c06090302070315141915120210080103050c0409020f06 70
    0x41d2005440f83c00520401d90000c0c40840501c03c1c1180148074201111b83d1511419040e01c2441d002d2500001c1d0f030407040500740400030091390090b00c07030349960400d443c20391842e03441510a0240b051520720422034940c82400362034100c0d44043c141011480c0010040c0b0001c2580c0c03000d10005d000c0c107000c0c028100800f030102500a245142c2c00603210861810045e0940c100da540349410014100210b0360b00c0600b401690040c2c480241d84010f070b4103840c502060740c4a444da00015803141051048070380c441d2180f401490208560700c0808900d0321176041c42ca598580690070b4507420490701c08112103840c610740c02000d071070b5014034005040840b162541800c86122400940068000700403e006100064070b56604440c2c50000420070150301c04d8142c028501701a06400c104000d425a0b06101c105a070803994003040c41c5007000809036950807942e800c2481200303081f0700503100c68101e2407915015450b554100c0c2d4010000e441200041c40c20400200041c8000300d03406084a201e0358425121007001e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 414528489 1250 414527239 414527251
    0x20a0b030a0612080903010507030501290f12060f060a0f0f0212070308070206011509030b042a06030501050415090b1207180f090515100e070302074b0b 67
    0x50340e581700088241400c0d80c40090060302410b041c80c004000110451a030780d00020007040e800004c82c03660002c07101d540e01c00c40000f4000c081d4085450b0781000340d00c2012500420041381c11224071044003062140340c0c0900340740c02c0c0119010540f0b2803015401800081c0070702da010301c161011000c1424004035590004801580080d2958080085450301000107502504901e01810000107400e280100519208d000041210004801050401ca05c030007640542442401c4800503241040305420115421480b41200007420035000007081c4c1081d10034010f0801c0801c0c40c50840f2414600600094000b84900315080380c10580000c2d1035510a001203000b8080c1c0d19001c1244081401044003a11410100c07450060b14111104d0700190001541030000440120108895a9003207591041d6540b540d0000459040342800c202100d41d0590040015502c540f0a468010305103840070b0020740d90300c1518289030700709050010480030a0303602e805407420384503250b005a1140b5903035510310030a080d122 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 414529739 1250 414528489 414528503
    0x110906070f080f0702010e0d3207120c092f0702181b09030607030b0102030706090308010608010e24030c060c0f150c0f0904110a02070608010909020a0b030a0612 71
    0x12500466074421180701107c442110062010385071900c5400d0700c044804014145258005140d010142c500e403403044078144210143c0b840d40da500e00d180b10108540e803c084405a4807060f000c505541c00d0720031995150341848240c1110801c1d075801c2c245e000410b40780c009258505110580c0142e03112048000011110044100c01d0b042843d000b92130390608403210f40940100340801002030300c0025580f540454a807902048103d00480141c4c103500c10150050326250400c030000040c180c00116450403510a691070a103503a03a640c80310551060150740070844100405004641c0c0e19500502602c80d0400074240d0f00742d04008000190507900c07180d12014160000c0070031540088060080001c840e0b68400300900354070b04896503440d1880340d80d9a0101400c0049a17240164583e80d2001030600c201e282840e5584160910182d510106803190000007601c000011860141a004100c0c1d0154045c10300701541d4200b5001007803079000109000e4640f540c5550015000f25030070028080c0e9030003219 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 414530989 1250 414529739 414529747
    0xd02041802030f1209060307090e010f150c030c060e0c120115050f010801030308190e0114070905030d05030a151217030114190803041401030b04110906070f080f 71
    0x4185803c0010f200b115074540d41118680a4044e8000e80495000d640d08a07001a5070ba5a292810b41e12030380d95420002928060400101d000e12407107024134243d5000040d15403117072401080444945101e03100040c000356110185500080b43d542196142c407407040150b030041007502d4049081034120f2a155107480e034407002e0203042c0041c107d11040c0904001e94030751404603403110028143e00410303c002000c000c0c03184002250856807074030848403a941c610303042c44482c16a580c0203000e0103144812043c201c02c0300c00070400c41c078040d10902007240d40c05000b41c003030240320b02c1d4242c4841d04020004c0c807410792140e285000c10011800504042c20300218948100107560800200034820211005000c034010070052017001030010401c0d03180c1808032401140c0002c0c0d0400c1e150340d440d1130b40c800e448a00c00401e01240040141a42400000c0280d9007000246588030402c0166003040d0310909000c0c004002c01d5145003030003001001c1490080c18803101000203a940c41c3d01680c45000c0d10a100c1c2401320b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 414532239 1250 414530989 414530993
    0x180f0309080d090f0b09010c020603100905040b07080f160e0f1302031e010305060103080c030c0d0e15030c0d02070819020a020a0b070c050f0f190806071812020d020418 74
    0x440c0c2c0024188000c005806c1c1001c110002e408a40d0200010b0301c1014040000360101c0c80017481000504988002440303035046c54a40040610819030f101c5010a10f00d40000c0c3d040840705000e03134401c8010307192801c1ca0b6224004141d441c031300e010b071140d5001000c1900c28143c940394110080c0c40e1003114003005a4a1174840c0c00d004450015800425035641071100400c04100300103440c41c1540d80007050b0a40e902d8100d0405071551054070818449405880c11051149400541000d002d510a441c51003404070071081401072071004403003440c1c41040070b100c010440e4020b5030141c910540b02d010418030304007900d00c2d8104800303255003002c00103902c0a202c010441c01c0c002c08401c018550708054070f08107160b5513102c2d280401d07540a114041c050308a0001d24964454450f08401400504890021842030080c103007040d26500401189119420105603410b10414039a19612100e001e5205410b0a20003084d9a03c00714080a030b80c08041541181c0141c0e5032071042d6141324080290f8810f4501d924 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 414533489 1250 414532239 414532259
    0x506032a190b0c011d0c0616021906020c04020f18030705060d020310060906081609270b01080702060106110a17090a05150f03041a0403170604180f0309080d09 70
    0x2583c170075030912a005114114009240c01080d401250342c903441e032540c210800ca007000c0100c0d020b94480a40038038500401e42c1d6507091401d4907410707801d0380d4101060f03105100c02d921409002030046003042083d031201c13402003062228180d0f801006ea401d030070394400c0020016041008144111031740042440300840e204e460784001402c8504003581242c0c6003000140c1100d0008103820440703c0c0d640013005681d4130540001c0c000e0080380c0140808440a14040b01080c016881900840c03494168070074269809103034107074403903081503005200d143c1c00c4c0703d42107c00410540d0103c80314840c04e0300000c002031041b10442c051002e9451041d4582c40b4074400c00103d0445984443d0050015002e001c0b084540202207a4ac000200b44c2441c0d5261111f18100c41c0312844880c3c043c40000140c003c1c0710415610020540b0031407089410f19400e80ca590003044100c840312500e01d01c10b0a01d40306c881c000140d1500610480e14080c0c03d00d1035815540304ca8903420030105a580c0e000141701c0260a2114641c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 414534739 1250 414533489 414533501
    0x150e041406100e041e0c1d0606040305030714010e033c0301060f110d0201200c0a0f03030906051f06111207021903030806040506032a190b0c01 63
    0x244819001c0c080c40c08410343c80324100a08060480d0603400106080d007015203085000c0e460740301c480781074610340c0c40307030110703070b04900c4001c0d400e0744144040c0442d0ba245031140588064075004805503107803501d20b17030301c3e50400c00d41e1f9520340100f552100000550b43d001030000d0710103810505824080915180d907042d050411500c210340f036040114100d80300e20310032101035905440382414003120030316030300f00240c0c1e0a80005400c1180d5101d00c02e6903d07000ea0341074000f4400300c03000541c23001c00c00d40145144045400380b803244e60001d40c0584007420201d0003242c41044903c0c0031b07050010704029aa200c201c140c0c2c808031044002800041c0b1043d03404107407801400002e0003a898004140c503800d100380307521400c04e92515040f1700000f044080c00d6690f812004d2050b07855442c4501c1100d5528030b03000e40704a0b401c96200384140c3c500000902a0704000c01e1000b21891a251070080c0d40b101227506124501c900541d10f90008400105150300510507960000500b80a003040b80d25032101d03440860950304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 414535989 1250 414534739 414534751
    0x1090c080708270c0a1d010b1206010302070201030e150f06010f0e0f041104060c031d100311131e080c090f07031e0e0f0303010b0409150e041406 64
    0x1012204111510100742110344610a00ca0389035142c1c6245802c0b602c1c0741c40304021134540d0220031340c080001c10194055188280e2407110941c2d01150380d07a00c0c410100b030b01803410700c54004202000060b14940c426802049401d02c14100010000c102500c0301c1d00c0c007011140c003000303d403002505000d80c0030340d60303865594004000d18240050188019006040400040f40c480c041d50303500191324125070302d503000041000b205041c40c607142c60b9505001040385481d6402500800c052110706603022104014120200c44042c0001da0359815601040f0010050800b03030406074007007800f4089003040740142c081d00034192000444210614200c1c00d4100c0f0700150700442403988a44039134038454880c0010603900c0400e2000d04062641c0d400801d80c0070b020b000d42c145100946001c421446080c850303001203800d000780c9040740c1003080d40f0308402c2d580c1c2c0b0007070141e20310b071120510080110b00881c0d08452004d03011070380c41c1807910780d840d030100d84128000d0b40d044910000c0c2c08816102c0c01810000b0703070743c048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 414537239 1250 414535989 414535997
    0x120601020109210210110d0f0b04090b01031a0408030601050d0f02030106120e010b0312030703061d01090c0f0504120c03060203130506070e060d050a180c1401020105090705040506150301090c0807 86
    0x4022003246d0071381031041c40641c031146900c030070300084405419849081c0c9204041c0082c4094141c1c0c0c540030582c88002d0104840d554000b0070041402c46281e12090b1082c0d03401a4070034a03640359200103580c242c021907403001500b91110805243d007203c1d400618001c000381d4850a040110980c071150a860020303041440c075030714001b9900015600005d902a0310b400600d845039481c0c949440c11009441c481c0c22102804210465a01c018083c80c80c1203812102075101c2003284100404c01103c1e10341041541b1030014000b0300c000d00601c1c0321800101511803084865105150341c959840050f07070001c54020441c01008801c00041c0b200c284442075024144d80341881c905030f90074000440b00c1c01000d1030184100e03a100005601800140d0220703044003a10a440d80109829103000c1841d000f813401808100c1c20011020043d55005000b400e00030403480e8080d046060506041c44000c010050650b80d108921801000020080790021806881c60501c0811b6030540351101400c80740014108038104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 414538489 1250 414537239 414537251
    0x2040f0504020c0303060d03110703030203030f06030d091703071a090c060c070b0f120a0c020d09030807060e0c0a030f02040506090c070b0c1c0e0706050708120601020109210210 78
    0x5500401100d1b448202100c0d00e00302d050341030178110f94502d107481c2a994a44949400801810b8002025510036100805025610355500082c10348402400e156040890517402051241b40c645500340304003103042400b16400d003080790302c81d03a859608900a0490307070803a200a0005200f414840f4425100045d10003d140c81e000c00d607244d984440522581c1c0080c00d0200d0b140310415103100451b86003400031100d106003401d112500305d000b4014501180c0251040a40e801411030007005600100d90300042214107103083ca485080c00307005140000c64181c0148224181a0303910b2035240c40c0514056132442e0500d44040c0b062208445010b0701c080d129802080802214845140440d5906030340800346003090384130030840d00c46a028106220885400c41003821020f620554046041259090221042c141d601d08056075948a03000c030250030350707004001d07061200c02050300c0728ad0051030602c00022500320a032108600d01c03a0b43c0440008a16250445036000346e8100000c200b000c0d0800c004101c0c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414539739 1250 414538489 414538507
    0xc0d08060a0803121602120d1505030607121104050306010e010e150f04020903010b150706060909170a1707120b032806020f070f051902010905013002040f050402 71
    0x3c0c0003004121740c50ba110b0103481024030b0391090012510840e00084110f8807850980304c50300c05018044105180c0e038641342030018280c5000901d03179021300c460341c031000c45902c0c406100c04050800359864840c0a01d04000c0001c0a4404026441c002c028a0004c0451941091541d0341c0700b100c0600003116203e00c8001d80c0b1301da0750f00c00309205c0e030b1642c0458005035107408020209014001d019541a40f15038001d001c0c5080805010007441501e01c55001080742d02c0d1180303a11411168800009880880c017000c0c03074a45c2240000061158100d68200701c400b51000a81098842c101100c1a00010380c01941e44111749105d801280085401100541000c1c21950310318114450620350040709a900e000340f03032090001607411035182d0030304000903a5803003103542085a101041580d0817502c1d4890b0501c52a0b80d8030f6260144110154142c2d110040603107410011240041d0641c5011200004100410b0301d02c90340242e400c4590701181800341e1510702d004010000302c0310035440140140c0c01000312040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414540989 1250 414539739 414539767
    0xc1603020f010e030a0c0e070e0301060f0e061f121a0f01050d0e1c090803030c030402130f0f050703050c040324110d050406150e040311030c0d08060a0803 68
    0x1050752020710341a200503c52800191400080c03942c00384c400100004003284840ca400c01c1d05204201c1515843c8510700d881c1d05042c200ea0540c8030f40c440c4600c140d041404142020714015130420070082c03c10004610300303689080307442400f0b41850003144900002c41d0300c04c540c2e80039404100321001d004107003030545c241c040782107400c403540031a04100d000a507904114110f64022007084900c0f1040b200d00e40902c626281600c14500320032008580100302c00116400000300710303072007200c651a901e42191a66400d101c4d100340d40100180a15464840c05101c000b0ba9200e0b64000019040d000f05c1da5040c4040003a040341c04c003170940380c3d52640410040c008180c4142c18002d5500c80c919807495698101150b1a00602c2c000c7c544d5200e02c2000581d0076010030145c0c00035401a4003940c0100815004a40701e80703101d440e18801e810500803224000703408a03000f050303940d00021003081900d00d4011056001802d2061204984002c0303030000c03044c00b6650402503086005842280021854182d80c0c5200503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414542239 1250 414540989 414541009
    0x311121c1112100815060306010e160e013c021c0e0a05090702060f01090204060e190e0a060f081219090305030d06081027020105070f06020c160302 65
    0x746501c602c0400c860780c100c1280c11008064010548a082201118084c0941416500c0324401d00c1443c1c004174171960000b600314010841a015003003071000342c20b42aa4440314800b0308905010159850a0300d40e05980b803116803044901440b00d99040d00b6224890038013000007100d6085510020048811002c3c0c5200c03a1100c0ca454106510100325480c000340a2450300d07003282da040305401042c007090b070b60000744241c01803c034041801c1d0207a889600c0c04080b80100c3c844c60000901d80b0301101030600345a00468502502c2c824229450b035140d1000011011b01a225001015580d0f0f20400c502040e50681e10040d0030079070040c260f8480419130104581c02070300860f8010800c48038402c03800c24012201d10740107603489021785c0d84030105801004014881072140c82c1e003d010f06524031140090f42d20503180c6005003c40d2410b81840d0540c0303100001c407d103d4049040c404200302c2c2c54081a0011034800900e031060310056500c02140880505100b00c2c80820002e084207400c05200581da2117800c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414543489 1250 414542239 414542257
    0x110a02011d12030d14070c020d060218031204092d050c1606050615071a0a0209060f091503040f20040903020a210206130311121c11 58
    0x1161407100000002801c41c00103082c005480e101c00610003104022036001400301c05144a00f003580c650300c044003643c40341d6103520f0003540407040009060000b10550702030615982d180b805032072403a01140200b443c0412000280790341d40c001040c02c2001003174901800c0030100c806c03d00e42050103040d900244005101c0f40b1034000b8691200006108c0040103400e81c0c4140e000f046405164583e2814040c0013000d09550701e9008119100141c1c46048420302107a881551090840e0142440c2650744400c41e40c014145228550b002c1204803100ea80700805810200c0540c048503603680400d40402000c3c01204454030143c01090042101050070b9801c00ea00c419000199403000a4513103120385500904268107560261500c1001802d256000441584180c86032070b5006090b00f160120307030700854800034844016804440040c050684c06484803c51307510904042c03a034000403150716420510403071802e0b400c4040110f044080482d13400481030800c00c000000f0840f103c0c000071081a944152244d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414544739 1250 414543489 414543527
    0xf0e06040e0c030313090c050705190204061a0c0d0207210609020d1b060503060a060c080f0301230a0501120c090306050a02120603010c020c010c0c09020301090c110a0201 75
    0x520580301000c0c03082c04081d0100405482e03842e20015031444080c500c90140019281c60008500f08007030240040b541150b410134010032600880024202082801e50422a001511550700041064080004c01a04201c00e1441501c07002c184170258504040000140c085510140d01040311850780300d00c0c0204680c0c900071220641e015401c000001d002d240100035001282100c08009015a004034850010008141c4440241e9142c00844013800113a81c00ca500c80088c450030004035001e1020011031511889095080c0030000b0001c01643d0000d038041881c46d5184802110a0502d81d141482441e0045a61210341420000001e0500c02e0340340c00e4001c3d407961000c280001e0f5008080e803200540d80040705002d075141180101019400c5101c6440c42c542c202408161645410f000f40f1102100340d50090580740c009800455400b024a20107459a250b4008049070180311400118048c059802010070040d5212100030480b4901070604505a00b090601c000140c0c1c0c40400f800b242140320300c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414545989 1250 414544739 414544751
    0x151003080a020c03070f0618180b0a031707260f1602030a030e0f04020306060f030c07060903021506040c080f0901060e1e010f08030d05131202160f0e0604 68
    0x19040e40f62a00c030203811a450b01c1405800140b002441e03001d8002e44125aa55401d80303120100343d0f02c4052094011403601c207829542d00d03908441d00394001c070b14a103402014060080e0b40e075103410401010440300854404400112001401200407124503400368090760b1155603140082c18070490300403d6101e201300752000480c844105141508250031a030010b0545a2030349203440c0280c4000301c1d01072918000c480190118066140901c01d60340300d0240600024034003105110072a09a85c0020120106100248a402c001c0307200f5105001640d0302c2a00101400c1d034000b818581200e000820b224822030805920210700c1c3d92000c0c1068020901d000e0703407100f9860f0304081c0b5014000d20b404c0300007031041c501e00704910416617403080b0b03110701d0300c1925201203030342c035601429010f040342d003d0070b034a9610820a2104079032483d40611307808100d1000c03030464100c256a0325403080c424084080e0060b8000030420b80c5511492408800070044d01b44140045854144d21448085000700460b1140359910 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414547239 1250 414545989 414546007
    0x182001091d04140106030203190317130506010b0f120402010504050d051c051207120605060d0c0f0f021e0f0118030306151709010b03060106020309010215100308 71
    0x28480c1805001c007081c075580e07080d5124807076108901c011202522211502c0e455544045010f11644081d00d0f000790103024190038010441e081300700c03da00111304001d061070380140545034040d00c0c28016035a60000301c40c0d100140c00d00c6890182c040c6c103c41c2e0b0300782040080c1422a9019404c0b43e000f22421010903500f0707910b60006031b0381030090313521583d0890441c01a60041084c042a801d4141d19800e10301c00c9400b2800e40200c41d24041d00500504200707942011039480d0b0f014052020f182c1e00010404a0102d0712240444c1c03454110707900140b00c584d11001e01c10071460f00020244814842031411407650208244000c0d612a44d0342c1c0c1c4c00e10301c0c1c20980d174840c4103c6014032005004e40800d60090111780e0607841c50b4034100c1220752040d00082d20b0844e01040b04003004000140d880389503a11106528030042050304e0700c08c00904240600d66880c02d5041850b14248040c50003004541c01a540740d940e52400607090100740e07020030000080410800c0510036030291018107070780d0002180e9445130707020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414548489 1250 414547239 414547247
    0x9040c170c0910060512090102040302040c0e01021b1516050102041410170c030601180305070501120b030706140c0f06071101020a080a0c03150315182001 68
    0x960410038520034500c900100c1680001100c003090142550104020795440f01801c001ca1002e008a900052040103585103a980785036120b90441c491030001072900d95658005811034003111060408034040f1641c5103125a0184060b01503180c0704039102010100300340006074165101c590784d030404a03001c40c0b0f494640315040808180d140d4000c000319038030360b152a809808400b80256251081c451010984072040c8142400d104100840e000b82034951030759146609150801800c2d5410080202418200c0394298594400214062806040b03101c0c02d0200051034000c204050303401541c104140c590b526180003a200040307030b000b4034040174040e100c0241d00445104a9041c103800c0e10508600d8171010301c01164080c0284141d0701d80128481209007010301b40c0c050004140e02281c0004001903040d58140c10030800d181c046d00d00090b000141c4140e805000300160800c3d103410262407201030081696100d1380d02448080c003618400074000f5038803002c01090314240d000c000c030060400d6109503401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414549739 1250 414548489 414548513
    0x15020f0409060b0304020a0518041716111311070602030c07050304030c060201051305061807380c10020913060603020a09090b030d050310080610061e0503060904 71
    0x281c0401403106036910040800385400980b41680b00b00c040c0700b0009008c0c50000c2c210704100040080024656803662551040800c03003103600b81480307404100b020290031115010b983d1440c401ca1110b60031104040620400c407054008141d2110f20b0107102d0b11540128000342c03043d040d4402005130362507403011054070803401102c400905502c070106005c8100000421014256042c507402002169584100c03045c07040e9041c034010b40340c1d81056000c5400c20a00710381402d890300b42c101c22146c5a90f40d5070701380300120410b15804103d80745030b89682041035a803140e4001d80340c0507050701c9600b0b1016400049459a0222070038944440d80050b4001c65a00c81d89030000a4140700a0200320407075507860301502a41c02000d003540002c0f92401d011401c01d20500c41c1090301c10340913001707055051803170304161115032001c0c211002e4070307851103400a802c0c541041414031801c44400b1883e900c0e490844041d140c80c41d00044031418410340c45d84c0b0b50141c0c0e440b80c1640d074041d05c111403416050f20396040001d80814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414550989 1250 414549739 414549749
    0x31b022e11070b0703020403230115091401090905060711120d020a08061206070e01020f0d0903020112020a0203030a09060b0d03030510050102190210020f0303010f0f0602060415020f04 81
    0x704200c6001c0d006070080700904581c901601440c05141c1d903000046080303204500000340700340000010420703880d8100030104131041c441c600004024402840300f0040084560103075070f005482c0e018109502485100b018010298071074140315500c519680c035619210010a400c00b044410340e0a80505c0c001000604a12901c40118a550f6207840c03070200c0103540000700c4640407803440d034082441410480c03902e46034080400060b00880d01d03108030850f540e0250780ad0b010304512070350082185188003882034213021981a00c0d50140c00b031843c0300241c00640c58088200980344144070f210003007a004400c40358440d452450000e1030003441d1500000403c03401d00c41c00d400480c145441410180c05910403030158071412807a1510a6075139004903641c80c54081c0c1c0040c0a103000f00309200608004501c0440d0340094015203d80348000c88a507480d64200364800c2042002502c41084070b817454800302009004184064107052500780c072100d240400400c01090740d5640003c090a50009200075180a04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414552239 1250 414550989 414550991
    0x4060507050f070b01170d0e151c050906071b08030712050702010f150b070206090307170a02010e0904020105090d030909020406050c070f0501092903040b07031b022e 73
    0xf20500700480741d21001d00405400e402246580020340f003001a001c81d0b20703903455461440915120f4103010400c0701055008042c1c1806006100c41c070000b1030040a902800001c0005103071400b072442c0c0d480c0c40b80180180301484002c03d0590b80003925070300c00000c07503500104060759a803135081003210b84a142d503c00b000075600d4041440307a4a0b5043d0030041060035812000d000004040c66024540e008034458000032400400400005050085c050201c5200080c141c2d0f0000341c1d104000e405041d14910140e960784c1100e030b0010304641e04070705c0c4445450300a4400c41c6282c42e0582c000b82140c801d041601d4030651903021404201441020440050086c0c08019525991b99200151650304290000509406850400f180c1000c0640c1c2c0181101c0d0140c0d02e000c64141307050f2103c0d0520104040f250013031103013095501c0f000c00c0791400444c0613501c02c4200030510318000700020210f0f28109070210312811059100d80700640c0c00210b9150b00b1114000d590b41070206035080021105419054901c5a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414553489 1250 414552239 414552247
    0x1c05120c1b131d06060a06170604240303031401150509030c030f0f1b060412050304030606060806030d0206010b0f0a0e030a0614070504050a030f02190b0a11120304060507050f 77
    0x101001d2108407801402c0078110f80003905c5800401a00d01d000740039400c00a0b1001408161075208131407620b03009035029000246640d101000040c050f541c40c1040c46070500c046404004148e81403245091007402d80144079a594141a146916400c40c503810f4001c2001c00720b41d12003159030074800a140c0540050131519621281c0160944810002e101d4580c0d90241200015983e0840d505201c40c0480040400d4501410021100701070000c4040aa44520041c400400019441c0c450980500120780f202849450000d041510308858a400c01c0115005400100702030409a010740e04098255007440ea100c8d601c048089410000d030400d51070740351082c41e10120034025280d1000394500c0400c000605140d43d036030b10580d440d1059100d0f142d00078680328801c0000c5190b10b9080c0c40600d1000f000300f0750116116084208005041d009601460380025000c00b465070445400b070b42480d00d190140240d604900041c50203800002d1015043e00d0320780b40000c1a45108030111910044190300b12511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414554739 1250 414553489 414553511
    0xf030f0b03061614030105030d110708030c0c040b0d030804020111160e22110d03050c03030a0b0405070c021c050a0b100503011d031c0b1c05120c1b13 66
    0x21141c0e400c3c0c004003007060440080201114401100d05a07034001d4001c0061281244007141c80000303955490070a8003809a010491032014401062003846071401445941c2404003000221405810070a100d44902c00c41c21002039003010660f68402d0702420111a0081c91103046800c242c4040a801580d048460001c6142d40100c840603004103401b41c8100704541079180a5147c541d00b00a000d40106c1001720091214a0b2400c60040031038070901c6d241342081a4840c01910315081a0f41121000d0744030061850181418401c051f8001c5603031030545094003003500400c1c0700496903a101a40079880d694000705101c810007203480010b512103d0608180340c840680070000019024482c070a509003117082d00b01100006000d15007007501809140790003480ca4115142003d46420003000544600501c0c603c1d07656103c1e0703040d2802c0b8400060f1a00321581c5007031070800a01032050142d20300e090050001c0c0d030000050905014620100b0003844003e144002440c410b0b900504a88c62400c14a0b401c803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414555989 1250 414554739 414554761
    0x41d09070f0b0414030106060c0b130f1101080f100501030f0204050603100305060a0c05030a020714060c1b0102070f02010f0e0607060c0e030c030c0d111305070f020c010f030f0b0306 80
    0x701d948191111341840d4443c82058203950342e0344160030010f001920a8030104100c075240c1c60708658104602c1002c000e0303035624011042c0c00d02009a8140d000c1c090746100b1940c1040c00c107544044040c420a1482c60303d16101a0001c906004030b07410599151100704890b05035038119000342c44010103064991a0003007074001c4841c0c1134002140c0501640002c038440d90040d015001c01d8642c5c6468160440d0740f104040c0001f50000c2c0b01c00d03514a4180c6a52440394101403207001d000c0d010401a0541e151444040c12000e001080424a4682c0c4100b0620340821111318a84c04099424071300090306c0f8004100482e040040d101002d80e004000050b01c5003009402d60009400011688a8440030140311041540b961144ca40080d0580c2114145070401e251900380d800002e8414007040e42d11010301800f00b00d44442c5d950403440c030540d80e0020b2049140c2c00c80c03c10440345000303100508098106000003000040032524a50a0545450580540f000c0d50f4209083c1004040d088a503985003001c1100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414557239 1250 414555989 414555997
    0x1a0c160905040201140703140702030a1226060a120302030f0307050901030c021501051c050609010e2e050703020706240f081209011b200105041d09070f0b 68
    0xd0201300c00700d075174a110108200544811940503194078000111031286030307841d68441d01c01240d05014103401d000004d1030010740828401c4d15a074501568070014070306048000d0002510032000b85444040114683e40c1d50001415030340400880d51000310302c2c0c0750917441c42c0206c00e00c8041c500d10100800c0480340e4014090f01901c8000d98041c0015500014141e80300c410040282000100c407100612150420b405100f9070001c070840b11034101d1801e902c46606010050321031a059945461464110320410040c01c07468061900d0302a501044c41d105100e070010986240403540c54640d4000b8041d28003990680340c4190f000300050094501282c4002d2404d40c400704100c0c0c5004082202082c1e031406120003005030b0f004038006010b0041d81c0580c5006640203609428100500075401c180621600f0907400800c6114a0364507000c1c1c000c810340c40c40c0d8900c2c1d40c040c403810410180300420600800030001604049a100003180076215000d43e40d041034603507080044000d412400c0000c2c4295200c0c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414558489 1250 414557239 414557243
    0x1302040204050d0809011806050901030905101503060b040605030d18050603040f0b070305060a030807170c03030403020105060f0f040b01141b190c0b03071101061403010b0102071a0c16090504 84
    0x5400c2203034044107006038803046019140c0010310500c0480095400b03603200e100cdc01030040c806ca03400d185299201d0016220300b030300345425584460004004000050140c40701c04c4504560074060241840d0200b036403010780059140030070000300c0306520400110a101c0c0c01070301021784059943e03d03240c140740d00401e80c07444003120881802c10000318550721074410240030b890002d143c04402880d5481d032030703540d412044058a11002d44001c0c4600c07030440d140141b17076030044180510b40b03e1406040203402c44074014070b864043e00c142d024195407035a40c00100e0103620411140051503004c000e004845d5911108001c400b00d940006903900c0d0721000c880c4400c50312250390110b038000d0605085150f0899591480100704010040003031101695607000340d603002d0382c6860004068117a28204c0b50a480850380300d2054001c00545044440c242030190f141c40400a00040c0702c814540041e400d40943c40003114184040017041c0c011042100340b15012030840c5004414160580700c0320b16100511007a602 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414559739 1250 414558489 414558497
    0x40b0402190303050f182107081902130e0f03090a06090b030411060c10051005010e09010501140702181608011508040c030203010f0914010b091302040204050d080901 73
    0x328103402180180401600d6142e544c15003407400b40d9040c1079158010500303501d504112800112002d8903a58070030f191080c03004065440c860090303410142051915007213043d8540204d0030040001044200e2807401c141d060f1240e00350a200d1500749002410034840c0c292950140080e00240403000101500406408070b44450400d5999407080d68488214800e88280c0324060000401054140e402000500703005441c0758901919090241d0620726204900c0791003d83d20001d01001116030b16910780030300001e0800c1c4403a100002d001460012052140303034100980b0a050401455401d400d5520140c1c0c090201600d24080a4403040a40b500720780d2004080c0c403400840e200c1d5440f4801c1181241e02450032038001c0607002900704c030780b40e0006009492003a0600000801038030709100c1d25a400c1c1c802c6500091222181c6404040044140000d42140c3e06040e80b0190603a1003142003500300749041c2c05102443c6540c40420f0103802990301151340100c540602d40103001c1c40c1001006c0d260400d81e9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414560989 1250 414559739 414559759
    0x240105031f0203130210020a120e0d060c0e040f09060c0311070f080f0406051201052403060f0301110d0b0a030f020d0318090209010905060307022a09040b0402 70
    0x18140e403181441d1820030700d00c0151841d0708030081164020354000401300003c10344240700f078010411621400c400307207006034404a0781605000b000c0090000f58029440d21030203488820001072000000d801d0047d240c560350f141c0c01d070ba506000310a50100c43c00c000d40140903007003c415400700148a0885d041c3e5030f907070411804650441c0300344a4501c80280c01c0c0c80590a100c1c2c2070710340c2c2d401302c041080100d500d020104840d0280d107424801030700c001d02c40745d5101c540c0c40d49500402645600107034080d5006030058911044254001010507001e01607490b0070700e0312507441c1000107680d441088845a09035103400d1140c507040301c0b684002d1505450f070752014414402181d0071710075514100d21000d41b003855058201c0e0b00615166800f0703e0700d0360292524600032201d02e200354070800c030294441300e40184d00207650b1401d9600a090310006002c200e54030383c00c40c40d00c600041c0d00d440301c82051004410f4030400d18000581c41418034112860054062030f81c80c13401d8501454401c900f51010381c81000880c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414562239 1250 414560989 414560999
    0x6071805030106030c150302070f14011503080f16120207051e09070815091017120405060901090315200304150506031e10110309030405010c0606082401 67
    0x100071001140e174402e0004900d84c1c80c0c0a10a005030840e1208041019020012217002c60050052400407601070294940c02420b080061821100c208810a03d0075003501d1080020a00b034800399003414082c555110303a20040d1042501c0c4001d1455801003010300c170303a50341008003a1b0002d01241a95011389004030b094880c2c4045c1c1e03004120445074558084960000a0240741c80b4409064018180c0d848120703004034200e0004090200440d04089045410301081003880f02070300380059119240009030010070520860310b01607124501a00340641300005100e00765034450013001000b55001180f400241c0c10075071000d00907000503920107082494039400c2080f4004244101c81c080c035840000600034400f100b02500c054071004242c103602d8011050404100070703089088801982540003d860b99042e58540041112106180c1e15540d800c14070400030742d1000002101c050318024208502d1520b500d00e0500080e003070396004490b50740503c0b401a15128944480c0c6c101222941c04a180d0b182c1e254 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414563489 1250 414562239 414562241
    0x602030a060e1005010e0f1c1509150e0a080c010c0306091a010e040e0f15130b010605070804090c0503040c0e091b030c031c020d031a10030b03060718050301 69
    0x2941c200d80b04400a40d0f0800c080d602810300c5d607500410140000511640f6640010044050803038a2809845110f00c00002c029502d01c001185001480c4104600d00603921074504907030004a0640c00c441e9200314403010400c2c104204014540c1c44900c0c142d8403903516024030302800c690010b14011a0808030086181d4040d40100d44940015198104d85840b4003801100d2400449101640091759200349145030b050070300480719001000c200038081c4000d21700f1641c03200c000040280c02c0c01c1501e204000d001840c45101c0c641100d007a4503140762180d80b2424001c42c40e01c07440c0c3c40318009a14002c90365001540010203144158041d44062080e6503582c00366010200040703400100d15005070321002034140e40c4c0c0c158920761401c05000c68104a111002291405103141c08071803c0ca002c020103003120301e504208040c10304013a03241c1171001c0c84030b2802c8014141e88a411162180c0721900f240a1a0b61003a1f10101c0c0460f0001c086503c2801c00310400340800d400b110450182d030a500001003464101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414564739 1250 414563489 414563491
    0x90c060314011203050904060515090f0f1c1419052a06070519061d0304050d060519060b040609060915050714010501140f0d0f0809030705030a0602030a060e 69
    0x40740c1d14410b03c40907956022169a441609082d90060b81c0780004900c0d43c48882d100070b48242c141c06860340c3c40d500c0704200020000046611740c440d95440c1041541c079240c4c2413007000410540444500d107442c55107020500141c0c107480c06002440303580c0380e800c4508031000d5426070f00c40c000d0059940a040c90541002000320b84540b81c20348a0703da007103044990403d03600600016014105542014101680d040900880402b080d240e45884443c102c204412000c5142000a100b5000354030b0146410041402000100c0016180b25510300000711102240701110403080b810b10000c2019544074182e035201c54004d80200d00006002d42030100c0d640c2c0c080c000030410768107088131128101d924600d0440302a84600d00c110b40c6581d02d2248607003924000d02860340038058500860ad24003054000f4003545542c0e8580140c03140c81c0c59449a008940300003400007009811041d0aa500c039003031000300e481c202083d48002d8040c8100342840e011b119203a4069802078100600c2030103c140d41d11503a030000c0078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414565989 1250 414564739 414564749
    0x903030f0705090a0e070e03010608030a082a070305070f03110f072904150804120f120f0204080f0109150509060705070309050a0602010903020105010618120c09090c06031401 77
    0x1000c1420301c620b05c41001055401211894242c0810b10008013017030940e042944107480c0f0b60700c04203010082075004540943d1000c214148003141c070851140d182041c1c05800c00a10b18020006001c03028075108000315803e20390080c7c0d1050040025140042c500701c40942d001d03a0a01a203c1e04000301500410100201c030a1905a05070000c1d0002c07030b40380d40c560032003140f41d281c01b13040100282414505001c1088032016494100040c40d150a00180340252200c2810070041c400c40d00303400240d0043c421989200c401341d00045c001c50150b003940003e2140350001e6141e80324141810303000c440150000c4168510561508801d50b008084400c1561810f558902c1035800c5000003441040c403407405030207898080d1030107494055407000482c400300c0c240d811042c0145d4452000b0130900d90240162030041c0848d280408500d40a21024100c0801e140150402d08002a081c00d0034843c1c0d0900120181000c3d060402821342d40d464401a8000544102c9002c242485281e624080202040c1c40c103c40b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414567239 1250 414565989 414565999
    0x1401050f010e0f040e150105040c120507090306111809010302100804050a020a0b030906090f0309041503060f0b1009050d060b1c0303020d0b090115030c170903030f070509 75
    0x1001810042d9800c031030700650035030044031185880c030031903599002d40034100d90704001800c0307824840c1d208a11001c1050704642c0c0560b051240081035641d001e03134584201c951540740042c09880381030303048070200c1c000da0010748000e00f480d0304500c4800c2410010807620702811100c12000318004140250860f003480043d61042c484500585018055042240e11500c16426100ca50b044c0f0b50015500003202e412210491074040104018023508101c0c0a40050400d4000c1210f078140c4038080390b032889140c50580c0100d0f194607110030354084d51540c01d005035030b101c9001d1081c802815603010083c1000c0d016613114032011243c0802e810700504044c02078030005040c03030170b030944c054603480042c00a40c200980c00c9848410b411018210321900d101047c0e220360340140e03690703440d880c0349020382d1000c04040b881441e07010010001d40300c0c040e8281c142e600359800c010500b51040541514481002010300043c2c0034000c081003000e45001c4003c40c82401c52074800401c544400a04840c0c0b40900080075400c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414568345 1106 414567239 414567259
    0x50601110f060f0c090904110a0b0d0c171e250c0b0603010b03031204050c060406030c090b09131d03132102030607080606090d0803040303140105 64
    0x22044d501c2031181401c080c40b00040c106a005040101100464100e0000740d8a80c07105100041940015560f00c4140c0401d2840240501c541610002203461099013030f008034003883e85009a0804911744131700c0036007450703401740807002404558200b0380e8084203d0582c1460303100358078a2078007035480351070340c900c5440d01c0c0d0711402000d0311080c0f00f0390404841c440540c03000401d0340c0d0850210410486652034a040c154141006210f42036040381e8005004101c854064108440200403503541745075050b035821491201d03004840520760311003429640c0f0815040366030400c855030340c0105180c0c040560b000309402c0c9140e2042c00142220400013034100140f11120690b107401410006204d0040001da0740065110704009064101b40701c2c011000c248203454200540310700c54030182c1069400040c60829142907002240c1c02c0700080d0030b0050014154405490250413181c0141c503c81007 = true := by decide +kernel

theorem cover : BRFrame.Cov 414388489 414568345 := by
  have h0 := BRFrame.cov_init 414388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414388489 ≤ n) (h2 : n < 414568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
