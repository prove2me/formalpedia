-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1819
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:47:38.644777+00:00
-- url     : https://prove2.me/submissions/8d375df9-304f-4493-806b-5d02b3153659

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326978417 ≤ n < 327158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326979667 1250 326978417 326978441
    0x60d05100501090606110c0d02010e0a18060b0c151b0406020601051f0f030f060e0405030315090601021504020a030b0f0a0c0207050a1806052101050105030c0f01111f 73
    0x240c40c0f00020ba0714006c80c0c2c0500e4490740d00340502080e001c20f20030b1214569420f07100302e0401504002406555503641441c002070040007806810a20b0315002d10011150542c0240c48048414059501901800160700c111100c00d1700714441340352514007030f80c581c940daa03c00703044c04076002003004641141d0000e14141202c03004c0724006611000c003406c010020364518140b00c00075400c60a00403815010303400c001e02101c4c0303403a070000d011a6100d03404240d1440607281100e0300d400010900c65140700503040850380440444000d10103052180000c1d40d50324620401784040301c10301740041c2c1507607030b103040003001150082d451103140e1402e460701909801c4110f45031440130b464032071142c0c0c1c0e00b03100051200a40703d0140a0070f84203030418543c1000405034004040c5050b445e000003007601d44464048105003000c00c070b004040741d541c01d10f115003526030580009001e9400b107505200c242c4d6075240300c102500001e0034000ba08a101e80740d00703414800c1704420058901941c0c840008044855031200305a504 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326980917 1250 326979667 326979671
    0xc03010c050c0c0f0a030b070513060f0305071d28060c03020d0207031101030f020d0e0105060f1503040b060d06050c04050117060a0605220b0d051006021203060d0510050109 76
    0x124034410484001041d0144c0e80c3c105c90354940902c00100491407550300417040741000ca0800402c204480088109604030780d0001d1f08082d003089e691030700350265980080140c1080840340b2310b11a0103d40364568603c2240c42040340344580742e101c103d000150107940a061500144498486001400151042204600502c500003800e107480d440400d481e401d680d8005920065944480f0045015022a00207030396010741c20010044003680038841d042c80d20300349000202e01d5280000400400104403e203031805040c01c03e040300f100204102c103e0343c2c455805000c99420351110713408100e03d5074186400408040c40c040074003406415003400362044410903039818044102900040c3c50440080c1e8219402c07624030f00007405014040c40c0a004840360100092000c0c0100c2001c041c07000701d040d4040c1d0500000059404a00040344c01003540c0109281189403480b450000025620340e081a2030f00c0c1058008000320307200356140d01c03001c8105600f01c0100c440650781d231a0524020402071242e07511042c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326982167 1250 326980917 326980933
    0x51626160f0f050307031104092301062618030703020703021905031c02010e0d0e030106060c021e032122060f0804051002071208010608040f080702030c03010c050c 72
    0xa100b050a007601c240c1964402d41180c40e60f00040e13000e00250110001c50f00c800b48004a41520306100700f9817100d9080c458540310300400c007840700e107200040c4c201d6010071813243c4e018030801800402c407058402003944410825500da1001c011140b00b00810101c01d4040090701106042e80051202c06036802240c074040d242e40b0301242c4010144080c802c164040c1c20100d4051852401204410590005170001080943c03500c2c030801d0a1a203064124004242040001403007814244240b901a11083c1801d82c44090140c001800e0700301c0310300c42c0c40110804c200405205407020f00c0844840220402e40500404050a0840e8907800a104020018080c41309485162000d104c00c41c040b0b51181d00e880324034410b00401102c0080c0000c1040d60f01e8407074000c548500d514688014481e0380d00404444e8952440131078020074801069105038100880d074418040801c07108900c00c0f500c82d074001c024984d201d070203101003800c0949071131480c1d0381540703000c40205d004c6411500600352041c128007135030030007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326983417 1250 326982167 326982197
    0x50402071a07091505070f0804090617010501030c290d0c0305090c0108011a0903060108070f06030506090a0e0f3c030307051b190308060405162616 65
    0x900f80920a1144004603d9164140030380120002c2c04401c0c05444000240325903500d4850950b400303544400b004580d41c11041000302d1201e0340700000c4a0380c1e80028815545551502c0007c101c80b0300440d03084040140c2d404d00080f2024a8a100c0c50310f41d107500c1500e030000b4103100341c01855046a90f5020a04220001d2101c0e907000c06e0700c59125405841d80845139081240d12801001015117440d41c80c0410403000c5102d603010854039000340030900050249904040030004410130300e174000024581801d05008456aa801d5000d901491650340000c80401c0050001e00e080c1804200f1495402442588204c0b5540408068070503611441c031000b911800040000754a800e201d92030106404c01d00114007824842c3c001070140150303e2014070100803520405500b0301c415045058202103841d0703041400c02d80c210070070030346c08a400c49081095182280d4440d1001d0181810348041012003040c04440000000f2103200c806034819556541e4584131001004900e4100d01c00d40c017180460003140360f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326984667 1250 326983417 326983427
    0x312010315270314090d0606090b030712080a052502010207050613030219051002010b01080a2319090f0b0105030a080d02032a03060a06020601050a031704050402071a07 74
    0x40300100702c11001c540360b12030320b0440390240e040f00b440030001d40030480d040c15076507940c01100240c2d0055200084882c03501d0900003c49400141c03041c001d4000c400300300410038050410740349141d00a030803140d4404c026802150a0720411081c12181c070f078400181c49a00d401d004c001c54825200703808640381e15031500c0400c1614042d100c0395851031400d1003070a10040c10400c41120791000c1b0844000032445d00d40e00000c0003102c210700c0d41d8006039505c00400c1d40e07540e8001c03003068208924081c100a804801300b13030411103051892a5294581581021452040c449200f40c00c01c0d41514000304102c0c40f0354540107410501e03081c000d0324400d80c00340c00416245400304c0c8a85240394000c000618024210b42c01070f010750402004011884d00e40225071014524000d803061054003079240265407482c16804102043e0001c1d000803045500c20f03001440261a1503005009982d00403180c200d6030905202490168800c0d5005641c0003400030540c41c04104248504210f291000c1c03c4010702c2d9651410700b00c2f8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326985917 1250 326984667 326984711
    0x9090f190203010b030d0f081e01030609031e02030a0210060b0406120608011a0310060e131e030f021207050a030c02010e04150503010632030312010315 67
    0x441500a0040304a580c0401a804500144050300215807031100f90006404d0002c0b0001d10303404204400081c1b401241d00290ba60b80c401e000d095900d000002125032100e400e141400020640c65480080e101854022048400c2c000c111503613022030b4898a04000f5100e80020501001500c0350718003c600c00c00c05401005c0c2030726400742105041c1898240c00701c44034400700c4066440c003541c5410200b40b016007030040e4000c82d0301d0040c011500304c01c0d03101454908100c00380c011902920708841442404126078146410641c41220340c41c4000b0142891010341c06941401f00140c0c0b005403902c1c0070550070005200f0044000c1d02a591440150100c0541c2481040d60060164100c0050180000c1c01f0f4200a041c450043c0340030355000c100e41000c43c0c121041c41c03850784004200f0342d070308201c1d910f000d008541c0030308000c4450b50383e4000452600410701001441c0030007400300800e101b1455840420940d1001d4180805203102540c0d04c0c10050b403120700e4036440c000f80a040030104040000d055280d96 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326987167 1250 326985917 326985943
    0x7051605180405060408070309090501060810090c02250f0e09070e0103080301060f03180f1103070b04300602030405010c140a0315080304080c030c0d02060d090f0204050a0b0909 78
    0x8190f41c3e4035135840c00d46e41c0c0d000203011000d01c8100800400e2444c440c0c49154080d001c03c0d19030308510f04110004603c60800c5a218401003810302c000c0c01d0100d0350106a5005001b60202409811540301010b000306c6401600489543c0c54061000140060b107026280e010384550070070b03a0700c500d4584c014441401801d020103420233408200410503144203451044d0103071001e00d00002d00181c00100c0d4141c1060100090724520b040c1c405a0090205c9000c03015280300c030890081000d0303403921510b01d0040c05140f1421502030854070011000d401120213403443c072000d516651401c1a540c0c60600000c1d00f050310181c0d0158030701311b004c5a243d1f005900000c5c14004103809c4500f440c3c0d040e0401c6002e410105428511290742c1d010010701d500080000d8000760045501801a050081e01030501e041030300c1e590f15108507803032a103500150f04c2e08000c4403282d22b1900b178046008409414a581101d1303000d10000d42151510003006203010195001d2840910100e030b83da4980d4480c20fa1065903240403065070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326988417 1250 326987167 326987173
    0xc1502070e061807080a1b020d0c0f050a0f0c0506040b031501200321070509120a0c0902120603010b030712050c040507030203060306010614190507051605180405 71
    0x30301c0400c2034840d690b5882080100400e9000004214542c6604001d81d00d80b03000c1514102400f2a5012600440c00c842c24a403d440b41103c009410007540c4552120b5084144441a24070790300f03000c2031070042c0035600d4104003150741800da185414006000c208900f611296010a4007050900d0450221000c54100041c0700d0b06540b140c20301101c40100c1c4001950502459651000104018195605281c09074501858030341c034607070052001002c203040444041071100010001400c1c0c0244c02d5441000b816180e07104420485a03030240b41000400024025450007030000a0b40301c02c940092a091205550302012900c808007031500b0f8500c0300d0605a41500031550502109040e070002e0510113015004942408060744041003c60b641945c9140019030000200082c83c20100640e50042c4110301e03100742000010580940c03580a038008100c0c40160b0944103a40c901e03c40c2090703400298015080d1100c0b64013101604084160910840e400b80d1006044190082240d00c1100e1103140c2000c09 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326989667 1250 326988417 326988419
    0x10080105090d0305090102070b191d0304120c181506031406040e12070f0201260c16060f060305010b01032c0111030711120f090d030504120f0c150207 66
    0x10f40103010000e0006040b5982444a54007280301c9a0383c0602901031016910076003201c9014440036141403503c64030072094042440300c03a010001044800305c030403041c00c90001c140c0303e180c03460544c40c86510901005007213900e428a840c00c654840c004040c0000002c07051541c1c0e84034103030190b502c200344103e09a4139010000320542000d0300208030343d035032080580b86410001005140e46030000c0380c007a13800b90f00203591441156040300708552280a00042107c40094003010201c4005004103030b400c0b0801d011901c04120410280521601903201800b440600307540c903002002024544020344903903081042103401540248100d031f40031512070140151941002140d008109802c819110b280d6507a14414901d0a071004040c60281580e075641003401040e0f021407034604486081c0760f6030810010018100313103a034104222050b80c1000d0314454206402da0509441c1400342d58890551356030440030700380c20415200d8041420303611801c01c0751241a26004900110a0400200e401680c08280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326990917 1250 326989667 326989693
    0x19110406320a0906090207020a0801140a0207110d080705060c0a1710090e0f010c02031204110a050907050903071202010203040e101503020702040c0206092e060e1008010509 76
    0x2070103605554000c0c20440005070707200b0160781111a241c2c411002c02d60301240c0102103140207469034009000440080c4a05010081462114500030341081d00d190f0f030004920301044481c0b8885468148001c00d28030150009092a2140d6031212808850b2406118005400c00c00a0320030350300c024405d9508d450400c1c0400c0d8808299100291011200410302c12001880d02000e001e035100d60041d40e0044d001000110005a0940e000d0319003080664105101c40030310f0f404015880d60303200b074002280b40000e54008011500e000b0303180d0045074020a40c4010800c0f02600100200101c00c0242d040744c69040c0c1e0b07041110401c110b070141c02801070700704110800115a11280d03594012556602003040340d661031561400022850b00c4920100e60081a8101540fa041c402c5601800d418000b50ae45440e00a0244e0b4131000220220503076030310140e900c240454924444110102d4410744100f101c0342e101c42400305006000c032842442d40351400f00101d046041809032500681d0400d00920000c11045 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326992167 1250 326990917 326990999
    0x606010c0510020706020c12032404140c03010609120c14060d090501050601320a030209040207061401081f020304140a0b040318050a0b090319110406 66
    0x140290307010b10980d002218484050300c024510984942001a036581810703c00e82e080ca2445100d00441306000d208110111a0b154807000c5900302000e09000300f80c2400c40060010008038400318582c088540230800c2c10413400c80114140c0da415200d00300515640c1450310201007070144000c00d4003400400c20805c0420b04600c0d1403507584010035003410880101c03440811681598000d50b1a61b455005002c020350b00001000c0952001c071001550748030122a007404442060102c40744c000f80006864080e991084e0b056480c0312030014000d42d034424403070401202070200c404c00c0005003500c001c000a1105c1000810420703200d076803e00a030301c107445200a070300250001803042d40e0024044c001545003a5091005d054901e1080f0102c06d10360a150a000344810100a48000a05180c91003400142e03548140c510403039944070811582c5418a101080c1005600042c1d20904c0c1e900030381e048104090348036840c2400c0d1051300c003000455030341c0e80303c04800c02c070548220b03410031062940c000760880a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326993417 1250 326992167 326992187
    0x60702210a022e0f021906020409020c0105010518040c031b0504020d050a0f110409051b0a091a0405180601030e06130606080304082d19111002060601 66
    0x40d0080d2092901c8540225000d043c0d842800c00c0038660810840110500c1100c030b00030440c160f85001261110900380203551040011140444000080311901c03c10042e50121006450790640641d104c00e001131407240605028020b1520440040d08040e60407800000c89034400c9810260405d406840d584580c0004001101c911401810b04440466240c0741c500051003c8106000006480c0c606450030808807051041c0000b0003074103185155401d901800c0039982507a54201c40090f180d100c2e0b41c07042201c0745080d0030402e403100d001324110420301e810141000854480340b00480051800c0e10b292081c0b0f128034019194030012145500e528150030105c0b06a2220060400241d40507482c04103528000042b28944090000100303100e08000080c0141030003003250000850405080001c0d0720740301c208036440c00042001041d1142c0e00446840000c80401c001c203400d0300d03c0380072460a211a0911092401c0e14038091440f510042400c148501c420700c1001d0fa4060101510f40c078004541800380 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326994667 1250 326993417 326993479
    0x50c19030903140a0f08040302030c0f030607050a051603050c0712080301090c030915150902040311010302210703150806070206040209130203120d050903040b0405040f091a06030705060702 83
    0x608050000001d845d90200040c29015180850b00c0b14070b5031040600c0d120040c2e0030240103440c1d01c0344d81c20081e10001240340d0046414180140c0319408030074219654000d41540a0003a180360540d00f090542000c018079011403100262014a030b21f0300c09210025010340c00c0102000c6003000100142142540034079401d88151501040d08000c0f6190074101700400c3d000f00d01d01641d10200b9000b80d901c40459100200811241541414907503100d414481a00741110b906140d0001840903145c950300da013140010842811142440c00c103c50024000c003503d002d62408280c04140c041000307500000e00502c200050344c024510340e40d4039070a200c1c51583c040c0184000b00c03200000f100c01690300b0302c0305000400ba00310202e5110303008001d400080d908058240c5100e0303001040244040d40c4202d040350107503901644c003c14204080c0d0078070030007004503100103070400350f0006001070340f00c18541801d40251005c8080f281b41c142c40c1c0b82001404d10803640000c1d44403000281c0a07001050301d181c50105090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326995917 1250 326994667 326994673
    0xf090109030b1f0501171302010c02060703080604050a020702100f090b040b070204051005031509150901021809070c03141b0a050d030c0f03090c15050c1903090314 72
    0x25503a502c0030300d8104262094942e00140191091900400080c0c58004140c02d01e8420605002c0902e00032104502802070980b04030414822019079000c3c26200e003010b54054207180d038600003410002c2400c002500c107103204904001c04110302206e81d00984611755001480304000a8030301e60b00b5106401000d2110042c0728a120f00098120000c00c09080242083c2c80700c1c83d030b21529071042108032a8024840260204400c1080c00340da240003600d00c031003011024a6800c42d8079482440f0746000059203d80700c0150724041004101d500640260544552601c01d5002000c205c2c0c04008004204603645000102d02c1502d080110340305080c906482801a41d001e4904a100c1c44030b4a540c001c0c4c07007516851684110b005404210041080c01075440c180d1408008540e15008002c00241e01c1c541c04030209512503240100307212402c10110018041b0003c07007034040c0300c04c00d4003501a41120420b00391500075094004401040b03921444092980b694403800014250b50b965241800b02c0481481648 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326997167 1250 326995917 326995919
    0x12606040b10020106090605092505070b150f0a080c011d03030301030b01061202090306060d1b06020d02010c090b1b0307050102030703050a0b1804030e03150c0415090b0f090109 78
    0x1881d00010b04280c04210b40c000b0034a1424009103009440380e80c1c6c0f145001e94410400c10590040d503403c20f0821019151844a6034016103008492a008010002c0c051194240c1405100011034004842d0080f050720440b078581c401404102d02ca00c0d491041d02083e0f00041c440144070740c850148002c400341b824602d012401e1010001c04c0c955003007600301300c03125104000144022a080440b20820b100c040d10294544500c0c000425120b03171001e0001030045000d101ca680400150050220b0070300c0c0401024440c0e668bd0b0fa4009541d0240f2840c4407000d5407900c500c01ea24103202d29078103815140c500c1c2c801464014081061900400101a6440280010700c5150300084c2c0a000850040c12107503008146420461401012200142440c51044058200185482503004aa6a40141c16040942c14400b00c900809c1c10000d51040c14540c03080003a00308541640494007520070f40b024490144d681c01c040303e1041c2c0b100070f90340c003494426920a002c002c62100026000740310110381850071481003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326998417 1250 326997167 326997169
    0x31150305070b0a030b03030f04050f130e0c09130c0302090c040e0c0403031e0e090402040f02040305060a1521030207050901030302011b05090a03110a031211010605012606040b 77
    0x1c1c15006000c1e000400070f400503c02d5818090000320039000c4001c0c510b45022402c00f40c00714807461050b075000c0c1c40318500061451351007548445151400800034031506d0ba01c001d04c952030704040c1c44501c0c8105040d0020032a4a01e01d070740c1d403414843c0d102c62542405400c0d6020889041c0005010100c003450811011605206030650180501c0c1080360343da440e44d04510b0040c10402e02c4000d055107288020700020440351380030b5010b81a000c3d065075840004c2d1941c2c004900a8681003110343c004d13070f000203400020040001403c82c0303c0d100b058010040c04c2c51400303980da0002010321070100d0300d04100312903610312100002c04603025072107401100c2e44655548082486100264019000360b59548521a10201c82c800704401c4001140350076440c1003080d000140d912062400060407810514041c0c504540311144483d0246030082c40d0b61a8580359210000c2c4403029400c1701900d01d500b4036800040b9035004c1c0b024004680085005070070100d420b81c0301c42c030b8405402045a41d00c00d4485c0082486 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326999667 1250 326998417 326998423
    0x90b0f040c1701090510090b010e0a1d01151e11060f07030e060108030a0e060c0709060302030f1c0e0d020a08070801060803091c0309030c0902040531150305 69
    0x31038505500e0720210002c0380840000300c094140e2040c0d220074206020003c40c114031000e20800c0e9010214001415003e820040346c40004003100b5a4101d0400200810fa02011084406208a0491041c00d50b6030700d4483c44180541c0c410850008508550003404212460320f520344e43c607040520340700c42c00120240308140b802d241070701e070101c0310303680c0c03606001003180c2c18021481038142000c0100315170752400034665035922402a14108001b55044208030581c0c51808a49485a00c030040300e5855440d041d581d0028a450304c8102d1003131141030964003070040c020805c0380400b1054803558000c14480881075805e1a841d01d14240d00092074070300400141d9130700c3c0c4c0c010003402042e0010400c10303050801603821078040e500403001d00d900c2402203103056690500c0080200317100748902d080c500418a415601c3c034110740c1008202c002c0552010843c1d200c15405001200d504030745504040b1800c1e050380c80000b22401c00390307440b0014080310440031207d540280504024040d400807902d27a9070789a25007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327000917 1250 326999667 326999681
    0x60b04062001060b031509240a0e010806090d0801031205030a06080a12020618060a0905010b0307030602071104020f0d0c090b0c1614061c020403120f0f080105030304090b0f04 77
    0x13130142c010082c40420b9040e46d0b42d810b500001518030001c0c505206801c1c19080a403a03519007141c80301c4890540703003070310340031b40c1c65008205032110ba8200b943c5401d0159140d40c003c403940301251084d022242001e40c80b600c40301d812a170700414010002038844500701c03440c0d400109404c1019884101c0015804c204110a018150050418a1900302440b400904051020b400251400315088041c00750180105565422440395440000e0503101c0d89401400b4009035002654940560000081402407a80007006840e00c585041007010080004010813402201c2c0c90b4008084103024882085502e503018000311041804c14142c03c0d5982c1040c14041e51204400f1030700f43d0000524001824030403450030018014a80c0401609119103022400b180a42c2d446294008a9003060542c0300a15030b04031030142d80c0007001a42d64404030040a4440c01c000100361000416007124960458032071800a4143e810090240d4542803a00700720b400900800b1080d10b5020004003100c0915541c1e62007940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327002167 1250 327000917 327000929
    0xb0702030307120f12020c10270c1811030105120109060c0306050906030a022b0804032009010302060d0b0303040e1e070e010f08090a060501030606050310060b0406200106 75
    0x462101c0e00b142c40200900c04060800f920340e1b00500001220400c081141110b0000c1c2650000d1440c44106440901088030392032807c0b950100c85c0c0910a010401c05040155018481e296044286e010f00000c1200d54407044160501b40c103000521883c40c100090040d00141040040b44c0c124454a9080464070190380301e00c04650fa4a80412140c00d051b5403965101e00110040d00b9240d4090f008240d561111400800613180c88954095a00350301951207504140c001c2c55031b03074540b81c0340d180c6907601c0440185280514450351a0318640c0d0303e0300d140040c0c1078070707400b03003080381040d468a0481024042c0442e15903454003041c440462400c143d6415144141810b100405117840d0702d4100d80b204c18405009401080320100b220784581c0d0f000001c0709110482c0f45480c0d0701a030b56401000d42803158110008103040d042c28000410302502ea085001902c3d401c800b540c902c01031031041182265010301c205050242705110410110780038061584102030641000c086291080c03020b00c0c00c40350103402c11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327003417 1250 327002167 327002177
    0xf0712050f010801150803040311060d020703020d03060510021f110304050d030b0d1a04080c10060501030c111507030e100f1d0606040b040e0a03080f100e010b070203030712 76
    0x400043c6000d00820360030b55031440076501c0c030798104070700c01e5224880c60002500244042c00402c0f02ea4581004030351030411160780031501c2e05800d15000b526040030381903c40c00a414510041010301d48020200c00c8071000d5001403c0481503c035040000300c214035a181c0a82d6600d20f0340d5000b0480c440c0055100d03c2c07044007d002c40011a002c0a001c651304004403c0c01058005580c01c0020720382c9420030504c0a400d041c0d50299961454031004500c81c24410710301c9070081460024910400360400d0051f03035406d880c10310110a500390200c601042d41c1d9031040030355001c2e5201d09100d03145c081186030800128503010030f044406040151424030b8442c46030350b0031542c072501c000e5482454071400c0c00310219818480550110b80300340540d21940649400e1040d90341d4540001c09a840d41d1180c0004080d21060f9000005075003800b519010040f108a0b40c1c108040c0300280c000244406680156070300078140102c9a401c2620301901500006422078040c0707c100a024081000c4454a8007858031903a0f072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327004667 1250 327003417 327003419
    0x6020a240e0708060c040602030a1809021209120c03090d1a01080307030e301e03040603110f03071404081b0132090103020409020c0601080609150f0712050f01 70
    0x450f5203400c000500c40003d0070000d00090045076808012103071201450718040c2c8513464440a01d43d01d4280707075403244103141d1000850030404401c41c040e0741c0c89281c0142c2074070050b01c03070448003e0603403107040300400c402e800421400c481032915500702901a40200080d507503c0c001e60028640000c1c0c20380150f0000e51021a040782010b60000e0481084041682c51a214a04c0020140540e002d0910080d0680340c01700400400f0b503408000c94450f0701c030084c40e050707148103030392113515220f500034001c81f8000384c02d043c0409490400c0c10201c070001d6a005003ca465076940100c00c03a40201140011405200c0c10000003030303444800c1150390710a20028840010300700325040003410a5280c10743c0b85103654000844044646414064000000c40181a10382d9804241d40102e009218541054000c01c0c0b001c81c004a02c1580020414161600d42040302c400d9155000380d141e03a15104020240600703800b40000744005842c08200c1d410924030700300144040808808181680c808555001c148006400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327005917 1250 327004667 327004679
    0x130f06020c0c13060501050904050c09030109030e010f0212090904030c050604120f021507051e0d050f060a031113110a020c0102071d0105190302030f0a110a06020a240e07 75
    0x45103200004075150100113151525001805d10b00907088214420341ea1000000d0401c070101003110840300740107000300990752003442c0c040c2280c0c00309148180000e0142c0300040c13403d070002a2101c112030482800504004030070b02000103c1c00000c1c400c400f00569100480d00059081214600a5114a10024030361801c490010084034903803000c041103600441650303131503907400710b1142d4100c403061403c0c3c2e03911541c441503450310850040c0150151500004d4540c0c0c00c4000c0e0348101e003c0c841d0036103661840c0e15013004004580056000c09404101090051021450500d03640445440a28000300d6540c00d22902100e00d908904a04005038114002d107841c0d03503a0500c6200301904402d42104c1001f10000021003558605024080c003400c5c01a40100351040c41c10301c080c1c01187d0040840d0310b001400c40500313860300b02d1400d0485802540d184118032a29140296600351160350340108207808146e107070705141d03420708810f00b8000c0300c0f00300001d000f2400c5070043c442c3e00b07070854004111700e0f45458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327007167 1250 327005917 327005929
    0x30a050103150908031f15030603050613020a0b0711040e15010e190e0a02031c021b060901081005090c1803010b010c0803091507030c0f02060f130f06020c0c 69
    0x3a42d001c6000d15165842000030034030025a50070480c09016814070440010b05101c16138141d40040c088151030400d11450030b54140c120406a07032142058a50755103401d56071981208d26948002d43c060990030040c0443c441c070f00042c0c807075580030f070010540340c402c0d10380807078101e840191916080f0303000300700340b4005003054a100d203004052520750030145150581c003141150750005820b80750f240c0c80c1c00c800c2072000c000700504801c3c141c005095451480c0700302c550380c0e003000c04140c0384005401034004620031643c0500c0b1441c002c0b10058025441c03c1002001107407803417402840c221824094400108880d02c070117039518450810702100c00d41d2255660342a244d40118041e8070b0384640c3c1000d06011346c6913032100d410b140e4180d11290035030320307501c0d1041200c1c1001d00a03041d42c0c8a140380c1104020364140c0c95000044595015240c065481e2443d217801c981311141128002d500e48400d03c0403804460302c041180d0801030082d640da0344444016070360b80c01641d202030b00c3e450f490fa10280e410271840c5844 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327008417 1250 327007167 327007193
    0x1208040806060a05010905120f010f0c1416080a110a0b09070b0418020901050c060f15030d170702010605031614030a0b04060c0507050a0b010906080c0102190c0b030a050103 76
    0xb100c15104513072800000801e00c00c014001d190103018480726964503c234042207105e07170000222000740a030f044140e400c0f800916610070b016000808849500e0044130f0344100b12007240c00c42160380c0742220a42c6c0c40740d0b1516840440d4140070800f0381000c101c3d040c0d1041c4000d2074900c2c45103081d6217070b5040c085240d03450443c0740d8114805500c42004104030b10700303041e16840f04031585041c1c05601d9540802c01643e030741c0103001062400303002d940b00300080390b00c072803074020302c02c003a20302ca50343c410100394082c503686c0e805e108000030200d211000c0300304618041d01c0700740d54000c00c9403002080035901c03180400c2c1000d0060785281400e800c0b00905100707114001d40040302c02a07098009200c2418281c650f081c40400151014210a694204410840c1e11a074103c0b41c84940000445404552034900011004e00904c905050b0500d40314001c141d0740c2001c58019070800c0e05170300078101c0c100e2405c10100755550794882245d229021a40000d050b1101c82e010b03510a0b0003601000665602d035041413140312070f035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327009667 1250 327008417 327008419
    0xc070f0f300e0f031e2b12110d05090f0114060307080109080a050906040504060605070201122f070b01061e02030403080a050d0905191e03140705010204120804080606 73
    0xf0510000043d180021103184c01504092412100201c180c10301e03042038558148140301100c180e0b68a0101000d06402c4500c0807460743d508640c08211040e03800440b0b140061040800030100400401d401c400e0700165040607201d415a194640d54082c1c071421515001381d41000c001d9114104555454140716200003071100000900c88102c2e9580c031484a481000d070040d09109000c0f45600b0980c0360300301a140941030141003044816101d600180040d04025801c900140c0d010442020409160103100354902280141007101d074496125400c004c4034510200315075510034003d1704041030044411a008009030344520404240007004a241c82c50f0503402881554000c210030400a103800040303401040b80c2c2c0c60b10780d46803041c0201c1800541401203000d4140e10994080741c01e0b40e0800100045a10312601192003440d40c1802805201c403245200600440c0c0320342c40201c0110740b5540106400c602c104001890b243e183d0700480c2403034140700d205503040b080205007840b08840c01c0060a422140c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327010917 1250 327009667 327009679
    0x90a020103050108030f0f0d20030108190b06012001180c0b07051b030f0604050d111501060302030702031603180b0c06061c0b130501050c070f0f300e 66
    0x3034003d06d900140c4105100200706880c0060240000c2c031440d444200c20441c0e80307021451040200802940d280c2083c080d100036401544100c0308542801002c580c1d80e554414080503856441c40b00640d0542c0024400c0c4410501c451022040c0800030300c6140004084188004510501c500306003141c031141c0c4e004041ea82204010500c00300d5000110b104001c0d0420114811055900e4042802c041d030303441000c461441400140410488080f0724102e81458950394010301200311007840d076444804504200c180c510341e40040c03182e03038400d80096038007110500490385445042c0d034203e0210f01c132041080c1c001445540c0300442c00e40351820240e0042c2451403442e4240701c0240021911000042d0030b0f544281c01590340c6000f03843d180c641d2240d400c1d820642c00541450002e2140035001001d00b0122001e5280000013202408420b05032030304142c1210740040c074044580d8640c0040d03a403c1c07000307403542c0901c00d000755015003810f014041e40030810004078a00c050081c80107041c00039190b038142d11441c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327012167 1250 327010917 327010927
    0xf060207031e080411010e091005090a0216120c080703091a0a170703060b0c0105060a0603020c12130906060c11040e030a0c140d05070c050402071709030f0303090a02010305010803 79
    0x6034842155a00250020700f11848920685c006941c15042d0120030b541001c240740070001c142e281c0f1b41c01e50007110000d6035140c08650381d48035048100d100e500041280404843c10400c00b107043c06d0514009001c150810f046284440c0d00d810030540c2189000f1800911000014030046031807155600d8210f80f58245207091440000d00030f8241042c0380c1401d00f03601c0c401d00c005802c10b8030076080600144161412250745100000e045406003100304e030114010349000100203040c078420710031034031940e100c000603040080c0d41184012441d07114650b01141d00d00b4440303011500e0700c4103101d00303802481c10381c856100030380103498422201000c4a5a9501c02ca19203d040040305a0200031a242c00c000c42c0b4102d5020409843c10241085180300c050b80248206068240c0781f640180003015098000c2d041910f081d80e81e102004142d1042001c0140100c003025101e514101c15003025044c448402000d842e624641100d28524541080b208000c10b5403000002d07405650305842264017404120010758502 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327013417 1250 327012167 327012227
    0x3050304030f350306210f15011a0a0c20121612030201090501110309062505090105210a0c09140d0507030b0f01090501081b0111010204030f06020703 66
    0x404883c1180c0b58440301c000000821030380e107110a1502c9100c2c00c00c41c9070809400301002d5a41c841d00b81d91400c01a00ca140132119036104445981b074100c1d0058482d03c0141025920080300b9030700101044418041301c01c440400180110711401c550186801541d04801a010704004142d20804210b59158115032901a003c200999848064400c40d142078030316480286002c80c01040e80b0000a0415440e101c15490140d4800c03009500502e02c0310101c621a86030003240b0b4141315061100002c0340881c884d069140070f0301890207485c03e01c005050590400c6114440110032000800001d60720b0b040b08002c10003004004c1c41980c40800703107403a10341c1c1e0003414003640450100804110352b11400001269031708000040001c00046c643c4083d0b100c4803814000645046800300b8042c81003128144000402d20034000035a0802d5000d0402c004c10f030000b1900019540055558128102c0303540800001c40450031341840b04200d00d00c01c3c1e0740180c1c0c9080ca801c0041c904207500460040584404081c4669 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327014667 1250 327013417 327013493
    0x8071109160806010f05120a0603061b0e15070b16030f180209310c050f0d0303110904020c03070b07032d022b0b091303030f0603050304030f 62
    0x406035085c201201941104242600c0310701070703403da5a00002c485402c01803005442e40020040b24480d010034000205121015458040d58135031140000e41008030180043c50a0248a480010085d01d0107107002c1d1540c41d100500d440071035940c2c0c0d00e201b500c0c8007092580c1c0d140c4240108480494400c00018180416018045c1d00803100a4844d40c8110003040c800c6040c800341e9419114080c0c0120a07000c2050600c08024003036203c01c0d130790384003c07401c001800d00f0f107401008001c40c4014820702d004000c554080d8000c003440e1022802a500a0201c1c91103626244010301642070705000642c0c540340203207040d65840074002c104004050801c00e83d24845184400d00f1180040c00241c500500000300300c5100090048640c1400800c100e0241c0041a00074801500360f0307460700745810720080048800b4000d0404080d0f91002c4c144000003400000b29109901541c1211501e04000c100c00d0340d40e0300c849181d50031540040d6084401c144e107a0080010fa0100e401401c42c0e08413246094a550790325000c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327015917 1250 327014667 327014671
    0x9020402030a142503021b010e16050405010501081f080d121109010c26040303031d0a0203280b0403031508060c040b0a03020918010503010e0a0c05010f050403080711091608 76
    0x1003071640200b081d02110140c00e15407c150141403008103c13201034505038aaa545000c840c001a84600e01004510b07401e00d4044c0c0e6060ba48181c41d8001d65444002c01c4400d6036080d040e145e80710b0159000040f40b603100520007030004d00b04945c0c40e42082c9401038410030865a500e00342c43c003a403508110f0f90b28140d820800d103524039600709080c8c1d80055136003030741001e0040c511481280310150001d404001c1542541c070050200380c030311200d05201099804495a0361030700c0c0a019515501042200d44842c1d0403964014201964828401081c503883d5140b0f8040041502c04401003915040d54070b45032a24640d002d4020300101000341001e0030f140301019180e20541c0250311400300b001603402c1810340640c0443c1c9000b44050b005900710040c03030780c3d40c0a0a035000c0c00f5817072095003080d1028684050001d032000f0044e401c14030910380e41e8078080040d606e03030300c000710300b0800d1250078030001000c607081d1000380c4409030050200500c101e010100b0000c2e10f600c0285541091843c1015030f0840c0359000f07034129 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327017167 1250 327015917 327015991
    0x2030a0209070c0b0f0a0605091005091005040204121101020a11040c1707020106030b06030703030905042a050408060c0406020331032a080307031209020402030a14 72
    0x405403282d50044400da03003482c001901200b4840240300310b4522460540b0300c41c0c0721001042058a440340100043e5401c242e030341038500000407100f44081e24103180c41075000b203d01c110905c1c03101d5031040440c0c1a41c1242c0d22080c0c000120003c0e510174043d000380428060542440604490585a561007442c0300e555082c02c0d0240d6510350101d0056405141d041106c0300c500021081d070380c40d0102c4002d000e442c0320b010845800b04800b01041460a00040e030030f00b82da038180c6848050074104010304c0018400c01c0301c00011030080102455195030400000340d000c40d040c0e84e030a943c1c0e0341010032070352600f030001c1c0200d144040100401c01100341d021003502c0f8514085086241e0b0110343d8908481c0e4240300440001d0042d00e0b9aa00204000301360f5030b6012005101681c2009074111045400e40c544190b10410182c0d400400c82d520019126201c400c0c184000c015001450941c50f8012034120b810440e03180c50410742e146102040e0348805120300ba070200d501140c51a031481221030a2207595a2a1108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327018417 1250 327017167 327017179
    0x12607061b02040603050a0309091a060903010b06040e041101020c01050a0c02030f070b1b0102090609010f030906050a0b090f06060d0c050c060901060609060302040b1c0b1e0310050402030a02 84
    0x80e907280080070101e00a01034004105002140c0c803818a40c0e2158002e4604070701080002e10001010040c41c019408401c1d41034034032030104c1001c0c000b4084281c0c0801c210540c90356072100c00101030341d50f40c0003070005030407001f072a2500b91601e40350540440814840d040d040d940402070b0103200e40e038070008444225501d40b420030b050a01e07510200e80f400c903028807032480398001d8080100c5c0050080e800f4099925041c00140c1c2c1c080c0000007058200c0c8107045415401c80010485503605502582c041020036081e8900068002856103d600407940e0981d10001c21646508072400c503407800e2004c90b5000420b071403041c031880c01c0110004030380c0e22a60720321412164032660358046242c040c40030b50710702100c4481610700d00d24000003164020a1507000361404540c3c1c4100100351140f00344259800e070394003010204c0c5816400900c162032104a4641500c1c12511060310750102e41350200ca1051b460841282c0c441c0300c0003500c0805092408071007040079020705e441c0820000d41d03400622070f05590b80603a01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327019667 1250 327018417 327018437
    0x1030609020f1f180302090f0c0408030d060609050315150102070506030a021e03040308010323010e060703060611062e03050606030d17060906061b01020301260706 72
    0x10030360000a8180300780d8002c0421403500c2d6103d1141102d00c001000c15a50f0801c03201c4401c168901070b5034103001c041e4100307460000280d0b510042c499400d0300041184400c50405694200003859980400b8081d40301a4442a007082441c1c0c108481c0400360800300d02900d2140b55405080340c403413000030242e105606501c102003c040c0d000380802c030041d1a0150401c1d6a900e41401110080e6020240c07005011800c0c88014003a038000e0000d81e40541d50580c1d6003101a40703913032100034070a8040040650b40c0003900d030344114846030920540c80d00108000141901c0d18000b40c01900f11a81588000d0601626400084c01705a01240841d40001d1000c0054940c00281581d2610f40c01040c400c00c1d04411801d00c080140000010042c2c4114030480449883c08104641100e06041100369081c003000a28042815803802c0d501c10b0b40c1c00000904440e09204105106a140100d20b143d80515a5130001c01400003500c034100f5213642c44209121643c200c00070104d280d903941c0300c0384100001c018650f50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327020917 1250 327019667 327019669
    0xc1d010608011212030b060a03090209180a06050a060b04090507020c010f0203120c09040908030109050105190e06030a06050705130503120313150903080603010507180b0a1e091d01030b0103060902 86
    0x1008000b40ba1b0b01038081d6454000c985009002414003150507442807603d00d001484144c026801c00b16109041000f404000e0b0082d51801c000c2d08001c1c04180b0b9603602c6000201d12611408080c00090000080c0807886051214002c1e041c80c044c8114141081101c0e501c2401d41900001164600321154040c01802e47d6042c0d8500c0e498050101050707805410001d80c0c6c024800350030051030683c0c1410108008a9a0b54010084070b054403403042441c4140c011030410be20120111582d620600207001d54124066507914801241e400300d500e100030a9011949240c640591175415003d0301080e4010119084684140c861034000103200f190140805945d0030104201c1000d0400000702c0300c5424400404507143c050000041201e10500039032a2900103440c1c1441503041125110a0610684460307041109140c0c083e8048620201801701a0b458142c5101a0216a85940300f00d0750b20704250504184141103224220144c504c05002c00134018408110322280f4181100d901a00025210304544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327022167 1250 327020917 327020921
    0x604060509161808030a112811150d150320030f010e0109150203160f0c05070e1f08030a1d041a1c05030702090403030204030c1d01060801121203 64
    0x1c1c810180882c521600083c92410002c0541560180360b1a946a00104034010313550340c000300109412040f000b116023400c0d01750305c80c01c10001c2c2d5010f806100c0c42e804581c0d01141102d801144024200305000568114849051203445030384d940000700d0021951440c0c031484e17030600c050803031300d4410301a1a410364402d5504021650f10070b41800004d12180e01c4844016001300f0040c8020307a85c0c0500c1ca0351012000c0e1652080701d01c5204410302d184c01510441c1d10444184070503400e04410300001e152070300045041040805c00a1041d1802240546807040319000300907605120040d5140e41070406020000c3d0100a440607180f030341ca02840c0c42e202100c07150094130541490980c1080c5824526060b1286660040750039010540303e0284180c1c081e201d000b0b00320f0b00000040c0c015001400b0b95001460180103d5800c913009181c05402e280d100d44551100d125154040000a1002e056020032602400b50fa203006240130300340544a503160803913003601c180c0c11841c018003440e180c62040011500039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327023417 1250 327022167 327022187
    0x306060c140c0a06050703080c03070507060506030705040e010506042d0c1707020c03061602070e100e0c03040614040209060108061302040906170a02030c0909190303020d05060406050916 82
    0x81c008401d80b56138100161044c0d00c841c00076000141468001858018a401228002c40543d59294580000e5450b500c0c01800082c04040c0d141c06045030018507540c4500848422035414000001c0a080c1442007004072000c60b043c60346025461007080840654004203900c8443c051940030518038040881181c1440c1d10502c11000d8401800074820015400100c0000d469000d4044880c60b8030746203192040c000108441c2c2005178055201031009556000303006e9005400e00c1e41d070a02041e2180120800107104071207802c20a0004400c0000303200c03841c0101003880f241c1e00617a84007810b0540125070841401042c00d03050104900204420f42c82d1009003000001c1c4601e000c54071282c940c41180701a040e94415603000b0740b5040e9040500440215a2017a26580240107115140000c42888140320300100a40914040c0450b0100140c0e20900981e030b5a40c4290f5005070303103040344802c550482e1030141001f80510302d41607084c000ca840300d040c0e194000841080807980c2c4281440112620660 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327024667 1250 327023417 327023419
    0x40b240a0e06070c032603150a1203030c0f080402060d0b0d021e03071a09091008030706050f0c120c03062b0b0c03101202040b1009080606010306060c140c 68
    0x15450f0a10026041002c20b4900c40c00fa9842a000e0000c081c00b04484074032102c410048003040031500b402816003801d0080038000d40300e528229560b41c03030a143c0c030701e2502d002c1d0086038a4014003120180d015400802071700301420806c200f82015008102240922000c041520f652552030f000c00c2d43e6464a4544402d030300030f03c0da9074040000c844100701c018800a4490291142441c04611606807448202c1c800041076204e0b81003020746001c21031110b50280ca00950019980c2001c0f4005e14144000c01020780180c40105407030610454800d000c400040008a10324004e01407100d05000482099400190a001075034482e00d4060004019403854000d9004007411400c68402c02580c882c2c01218080c0542000b64545d40ca54140302184c0c4000c031101040404030340c100340007983d10101c4aa42c40c5002a05c001910824170740403501ca4405d0030504000704081c20400c0200010800c5525030180c030078602404990701e00840030b4181000140002c02d06509020404600c2d8030410550b800c080c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327025917 1250 327024667 327024679
    0x10c0c090509010c02010f0903080a050711060a05010513020a050d27030c060506040501051c030210060b0304060e1c03021c0518010c031802090907090c020c040b240a0e 74
    0x10084042c0303008100c0c548400c4007650030443c225407041c03120301c500c1c0c01450309526072a003240c0c0d420300044028034008001409024121889030b5402e04100405841826601000211035060008004040701c880310078106107401040480c8460760f00000703a4503282211103003c40c11040c1c1c20031501034800701031509000c40940d018010181540305444c2d43c141801040204142e03141c41060200f610390901800b9001005d1081100e030485408440f2140d850103071041e1600c1d02200150308080d070340681d1005510183c08000c0c801400766610546604100c00c0c0c2c01488001030b144071462050800020400c02e166010969400f0441184480410b400910408100c1840c180c881d0150003104072500c06115032070110b0f034900040c00307845280d264800c104030400340103209070b0030000f2502c0001c0a03902a8094007030700144682c1140a107481c601010f8001c0e081040c0300d18140004c5031702c80302c501e82c40703402640140190406c21415841544811040d4140c3d11051707250140e402c19659040b140d0495 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327027167 1250 327025917 327025921
    0x20705061c05060604080c210109060506210d05180604060206010609090204030809040c0c1704060216050603060f0a1d100b03070f0503070e0d05240103050705010c0c0905 75
    0x41c0d04540c0345690401c8800e4108040c0d1a28028419140198092410346a016040c40780c21b5103051806d42c40c202c2d5549044c6e4600c020b40b462814207484000c08100c1f6600d813103030180700d42803421615080601c0244035859030181180c035051a0758030359070103204040c0040011980c0c500341e4071049514800d1405841320b6900c540e0303000000c1d594442446554006076440c0c0d4081010152402200c048a42124016003003600c100100801441e20600150500444901d41c100003445104008410440040b4258541c0e2900703134041d041000d9150340000441c150301c03061003a0760b0f41005407030300314209440c165402600c3c84040340880145030070804000d03410386803107080d8a01c110007842c071030403200401c007848035500c0e000b040d03640c003094070084007103512841c110b031006103d6000f55030700c045149002880c100d504404140162071090081e00c1d00d812448a1000102008030300d58205400442c0c544a59855900d4017601c0d040c130b5010300740c100620012100705100d4034018502c042c040c1124104564 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327028417 1250 327027167 327027187
    0x7030f0c0f0b0412021c021e03010b030d080c0901030e031207030b1e01030902031218040612150903050d1b080619120512031f0b0304150c02070506 65
    0x20003510510885400c01040801e240c2c84200076201103804003030340010f410301c450b800c200c80e0001150700c0e41180d04100161001594a41c501a004106c640036002c0d002c0d0701d850141401d44d01c5500c8418045d6000d00c0801f015203601c1981d0340e030301c00782f980300c1981c4402466004030041c04039503080c0c094501c800f1400d4101c4290740c0b44e0003400340901d41c0302000800c1e00c60003804a181c01c003d04224800703601d0400202c66501075007103824064801019201c5200d116080004543c025002950303144542c06110070250505101324005002d54181d17418110183e0356070840b0301d8007a04154803899803140a1481094016003d42d80e480341e07460014401e1800e0b0780e42d0299600c52240d0000001042ea00100d5201d003002c00c4072901002009941065081c180303401e040145c215840200c40b14854081a555481ca0440c050750158602c401002a03e41c000040381c144254140c11241c5004804c000b0b1000041c60800e41d40d110365810030340821103410501c0284d007044860b501c8960030400028a007411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327029667 1250 327028417 327028433
    0x302090a0b0d0c0e0f04030f12060312020c12010e071203091a220501023301030b01030203150705090d1a010b1b0c031b06070c0f090e030313021207030f 67
    0x2540c20707501d12812195074800110000030005c0c4c1b4081d000c80d0149000d0f03e841445000701d10209413400310082601d035943d9560001041000300c807407005800140703121440c0c3c94985202c28070b943c454002840080e00b4040202c0d21007045129400301c611030030580c102094010b90015004019180d2038980300c980707a50300044254040c114a90418021403180c0c071101445100341c5050700c106078020898030100000d0429989000942860340042803940f1120f4112031100c103601951203958a10899451413052601d0f0081e210105100407207907070300b000001c50740003090f102102012074441441441a0400551010303142d102a100c1d0411500080394429201c801025440352002800b1003202200c2c0d08161901008807000d07170b2642002e10f420105040c0001481a54480101044e01d04a540c0d500e0203045140ca9001d6104a821300c0820801140c1910400303400400c11000b0707616601c0e00300e09034880881c02001c0280710720010480262102800c0001c40d0281d41c0c007005110700c0301100e00700061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327030917 1250 327029667 327029669
    0x50d0e130203010f061b0c031205310b0406020a0b2809020906030f03030a1a12010b01030506041814030c0318190e040312020708040314060106180302090a0b0d0c 71
    0x2002c6006c0500c0c945072080e4074a407520380c1c560000c1c074074041c045c11a50703007400000070340c4158410003106110216001e2640ca21038076820f0081010407000c03c3d44810201c480040e070364402d0b50011003c0c0020407030310b500410180d105c1c940c0107a0f44103055840b1640c580303010140c0b04854403043c0c4d0007803007106100b034503501c000d41140c0200c0c0c0500382e0340d41e0f0904056481e0780d5000301171115001070011454590741741c3c10080305a400c141e54001c0094145000c5240c061080c1d1030ba4019079101d0031407030800e5805100e003540000c400d50b01440400d200f004041144004804014091820084405039410052003583c403040c0c503860503070340e640d1001d050b1810b0280c600840f681c45000c80c2103901c0c111030907a4464004490509030244c903203a480e518240d039042c1019030000b0703101c1e8003000070300d001034991002040a5071181010907603040c03581076414a0b040381600442e06010100c4a540140d401c5264840d0803a07134103d5620a207584d81c0c012100c06443d00002e0f007a04000860858000c0103640c0340140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327032167 1250 327030917 327030929
    0x16060b030102090d0201110c040903051c1a0f01020a0803010605071505060306040b090a050304030b07020c010f1407020607020409080405011106060a060311090901260703050d0e130203010f 83
    0x1025454a41082600301e1041001d4242d0100c0361091130b4006500900007070b00d04800c40700980d100da444040c0454143c8200030821130000d54002141b0841c00030710200c8503001c0603804010818403010490100301e22400b610205d1065440140d0a203e6a20800028141541c06503a25071256901c48025040e60042501101c551403094034420003c1c115214071071146500034010003c0d6290380c0c64480d001c003c0a008103806010700e415120105c2c0c0200014001503201d01c07c1c1c510285804ad200030b040c4102010144d042040504130700510a9016080c801c11488940e40165030380424800a0894072405c940290001c3c1400c40b8402442148000381048034002c0c0c0b40c0e0906020213040d02900c0c0c40c0308542c000d5000c1c201000601510780700390b1080381914a2f0400703180c50880d4160000310070b601c09a20200095034811000305e2030064480561582640d0300c0001d0003414111b80e0340d180c40c0c06180169904100002c90410300300d946144c100407920400da4811075503961101406026804140508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327033417 1250 327032167 327032171
    0x9010606051801030908040914071106040b16030f06120204060f0b120703060503010e010e0c0d02130203130c230604050603040b071115040b07021f02070206040b1606 73
    0x16418000c20403120b109601c058200324400c2c0d2103005400402c442d490039142c01c0c1041c04007182e100c02d203200b400c030303000c003d1134811440d0f10340807c1c01440325051917003000031a0808010300002820806013260000c00b0031804a2070301e081c0280c100c00426110002880807424503600194501c68088400c0085000303031070601100c6d846054040500f00c2520411000c200c1c104618600744611065143e0006110b14021491031740e6940000c0c00c2d07498216000b40580d651f0090310714061010032401c0217180b0240c47c1740720012f890340c0004805082241d03914400f00c1d00003000486080428008000302c03a40b01e5410740ea402e444801e0b03100c1c0b500c041e003064089050607980c19095454208255012604001c2110f840c694070ba90361a40500b070003405070320a0149854071445088428454510341c0000c281ca0030a00d85050306020400f02d202a160005540204035850404845000d10000c40c5284071809641c0344502d1001c204a80300fa80c0c000282c81001045070380c0c0703003070400440c05180f41c010002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327034667 1250 327033417 327033419
    0x9030c0b09011e0e041406190501050a03020d0e1c02060112151a09091b10020c0d0f0f140d0306050f041d030403030f11070608010b030a0221090106 65
    0xa1008540301d1198442d02003000c202c03141d03002c0c0c640201c80b5400729102d03140c2030a0201007040414162a0501ca02d407480c038410000704102c6082244204c100040b030b1041400001d881e002c0003800900c58507010b001003580010360884a01c8039a048802541c4404044450b117108800111100300384801080d00140a0f0100014202d540900000d8042d5044103502c40d8024080415200415a42d800341160f044920700c500c0403a91505205880b850303840011740041244a0103400c8041c00d0081e400e0700c01c40e190006200380d10782c005030905001a003590b0300040601d4906103a80c000c1d03000ca9000b089141d041000e80100203660520000181000c01200c01024002c007050b0103848080c0107241d000b81121a950050b840d140c2c104c6c1c194a80002e05040214502241980c196071194000b5804282540c070411003032540400b854460802c01c4014040441c2840b0780207008001c10f12812501d02004000308200ca0000e60485a01904c0750342c40c4030300070016a41d001000a0100d5140c2c0d0194a8808 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327035917 1250 327034667 327034679
    0x50105101703030c07061d0f0c062104020102030705011b030c0503060d110f04090f050c12070303033605060c07080d0c2601030c05041e1109030d09030c 67
    0x10042141d0001d1001460642e907806000e481c0b6034000e04000d4031441c0d1603102c500c9511a8003204180c0c0103a0440c09000c6045240280790720348407a442c02240100b9080004080c6000f10305041a400e460403501c01c055a01c0d5030004070305d98000c550340940745510707001480c14040050424602c0786a001e4606102000c081c0c0c1d400d039001c0c002106c55a40001d01104a000062a030441c0d082c424207006010b6150140f0303c2020a084415000c0e0850b621040114074a0038031404000004101d02d04650756145803c05800807620b4003101e200c010309041c1c5505090740741e03454810b11001c460b0a160041c880d1140d00c040415440300302d05209540714021007012490008080040b200d00039048102640f600000c03c0c55440180560095003080060158409881034288003803060501c040b601540039550543c207003140704908a90001d0320551074000d0030700d4003401910201810400d1000b00244203481d600e0345038180d1142002d03440d458041ca4810040203504403c4100560340101e031080541c81c1c840d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327037167 1250 327035917 327035939
    0xd05070b1312030905160605070b13050703080304080d021c0606050307050702210d020f1606120f090b0106051b0d090509040305040b03010605070311070b1c140405010510 75
    0x1020150801d8841c1d00c00b000030300e003e41c004a07542c5215000b124640c1c4440004440d4544141c0c100b01d00203840080e03a00d080c4504100e581e90080c6c04800c480124007003650705c65598a10911004011000100004051180c040c095403004030b01309406569030341c01e44c0106601c81c1e03844200814803918000010031101e00c5002501c0c812591520303910310348a0b5a40030005a18101000c1c00e030351103007d080100c40c014040c08080c0101d90542c00410b0060030900f905410072040d030b02621103c004001c0c0800609070b00c0320401c00426440600001c0b81d03605028400040d007506d42010f452070110300000030785541c0c08401001c0403a080a01007003140c448201032030b1640002030940707000800402080c08203241c004d000d103030450b109050071031616580d504d40c113110703401c240d01100102da00405d400e414103810541142000c0c5030207001c1e002c1c80e070500044ca0000d010b44130116a007602d065180480040c240e500501810b0184030700100d00e0719040c0380803070103040101c8900344080781c86180002d1f0944c0d01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327038417 1250 327037167 327037201
    0xf051009060204031209291c050610020c1e0d17040602070f0b030628080d0801080102191d040905030a140a0f030906062402241909050d05070b 63
    0x280c0d04547c076600b080d05144450100c00410a01ca4117010008190b0072550860000c181d00b1203944003058038580341c81048400c0750303240d1641d015900502807540c03069132a04e104580e0590000051074070304000d0b80110300c5882c91315100800c4a6410710290000c001e0700710140040395059403c0340c0c4020349540000400c60214443c03110030030020710125205161185950301642412018242c0d409213074075120b11707540c240b07170311883c0b281c0c0140105480d240d52241c0990701410031100290b140170710902c00159402c00300080c410804c803080c208031034061410341012046031002001400340d000389051042d202e41c0030345174010201c0e224244c07442c01a400324058401c070001e19112a01010440d15081d8003a1403070100c1151580c1d038400f408a0301f81040e401c814148500300180000c402032035000680b6052182c3e2084d09642d0b05181100c10214000540b40d0344500c000c0405021420011124000780c00b40107401085030103140c0780b02c00e01540c05030280081d01d004040503125078445641c861904920 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327039667 1250 327038417 327038429
    0x60103150608120c0a02060403080307090e04050a03030e0309040f051006030e0604060b0a0b1207080a0b030703140106080d0507060c0302090d06051e01171510030f051009060204031209 81
    0x40d643c0c91441c440b0800948003059000c401d81c0c07158542940001c01c03d5000390000c03070350b640000c07042c441100d6000710428040c15a01c100b0760b000b42489d03110a0343d501141200201016110141c814150806100340c801e5201c01410900a0b0722540b0784280103003c00f2100e0104401078500c001030707a14824011003005980d480c003e46502d0715240c41d90320151000c0d00c80280c1001104030005440b000da0700050100b40100d4950958908141c580105032103000b03404440800d05024514100382d5012551004580d48141040362814514030003501402b034070740c0180190301406100741c0646820600034140740e07220f450b0070412701101c0c02c400c0d8100c0c040c140185420090660204000901c0d0742c1c0080d40042c0240110780307a82d542c2e506140240701c0c00342c0080c1d592066140c1300c0e056564040101c03041c0d2040410b8000700394505041e034034010023014032010381215017104503141444400c1c05200203840e210360060103840b84c0740c1031903c0079501c544802c480c0c40c5034845074483c14502c80d40c2005e0a640c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327040917 1250 327039667 327039673
    0x30a0801151404030812100f05040e010e1e0631031107060302130f050312031015180b090a091e0203180d050a08070f0c050f060103150608 61
    0x400c1020310310040c6401d10003601407001054603804440c41400c080d0005611070954165607501103507490881c040060049031000207408014491030540548030000c0e158140c80c00550000f00c07107121800341895012103e207902411802405003030b9401c450b00e10040c80031084840985400c00000c0781422130020707030816010b582500b0303008480c0040762111101e019103468025900404080790511907a90b01610100c0d174006065044007031b82459020040c40740701100c440442c50103001c651a4290b81c01c600041000020000352005200b881a402038540c1c0e00858000c0f0703200d664080c046c80000e029044e91070060b103000003250042e22048946052003e800c600240740f520341d40700c003e4210080c4a800709480f2200e12031101c0403502c040d512508a142000300c01d851280da030941068201840d050402a0030880500030541090f042d41c3c20400500c0d004840c8625680125141207100200a1250092002d110040040015558141ca00641601a44840c1940d4240c2110194803490100d60 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327042167 1250 327040917 327040919
    0x806090601150c110105070204020d0e060109020f0d0b0411070503040e060d110f03010e010c02030418020a270f0803030402090105090919050f07080714030601380a02010c030e030a0801 81
    0x6440d5101e1121084c0060400f03508221003540002c0513a00507d041c2c00141c0d696041208003038204015450050104c048114135090308403103500458031642e501c0741c41c03445d00d0301c0d80c56285c0e40b580e51207425024840540c0684419142c5400b070317220b84c414402d104500b602400412041d14010040301440c42e40403415107003064880c401e01810811201c1d000c0e6155598121880c0900820b014006070171035154091940d0302d0410480b1000390307422540d8108a188103000885520b9080110410818954050440000c82150007810b0300d585c1504401d440d11004500007a07524000000b03540103500c220381904490382c80d181402601c2d403045403220b0781d50b071203c420441c01e100303120038510005000d04103480c01c1d4021070f00c0142c0380c000c1030382c0302103a95800170008100d6980140c0060011020840103000e00e54980000b43c420102143c2d024102e40b0200030502c846110100c07034003d1042a008001a1076114000020b402000821b80a50200342808408500040c0100403030b401101b00c0e4403110896 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327043417 1250 327042167 327042173
    0x6020706080f190f1506140307020d08180a11240d09060e071e140603061005070609080c010c0503010b0a05091504031b082a0a050a0806090601150c 65
    0x11001001c2941031071540c4010007909040c440c02041c0b481c1761840d0800010525100009281c0035402e10710350305051040c001d008a0941c041200210300c4954030701460b042c0c407941d01c0d84d00550090044081c4c58407a07008018204044241e002881c980200c0e54207000d00d403142010302d00040c0700299a8492041040689000c0c60303640c1c05454402d016030780c0083c411508150152811a10f03410030a021920002901060351181c1a40e5000d4507015a25450600940e00031071070500010b410b942c86a03201031508200c480c41001662420b80d044002809a0341c00c6051030001070b1302190a0714595400c02a0405103e405002100d048500f080401890a034034107104842036040050742e260702c071340f148020b01d071019500d902030806940982c64a40d00100e03000d004586d00242507008040a4005282c0051402d000c041000e403c880040c1900061100404c00984d403082a42c000c01c0d4860001c3c0408100345000160491142c0d03a150300700c60719a6210200d115081c24100f54403030000f44205020000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327044667 1250 327043417 327043441
    0xc012c19080f25020f0a0f050906010c0b07030c0e100203070215161b0f05060a0309051f021c020301030b0112020a0918060b060c3007030906020706080f 67
    0x40c07044440d0300d42002e6001d4110201c1075a840d0b03820948280711100f1500b58a000e40114900c060304980d4600401d00d41000c103030400549101e102c2c85003112000246441c0d007c0c070000076116521080c210854548038101070001c2520070100390014040d812800c4850a0101c00103201c4141130b0001c60034801036900708416100204880d0035800ca0600040c0044107000c21603442041c89200c2280c0b000c0f00c1180d0402d07201040d980100f61148040000f007182c0d0700d420045031250404d030316021412001c0b0f07081035844c060070300c0c04801036441c0503039030004c035a14241e010b0003024201c95a07072010302c3d8101c0c40c40c3c0144c0c0400e00014005405200042001404a550349101d00c0c0c8054951003000c2e0390341120408568041140d0b290880644051608000d0325219514288104452282c2003031003140ca002d42c0e40081c0400f05c1d0591480d0f5405811484004010021091040c1c0e04c40c1da40f581d903481c00030400c1c8828458100980f19055021819602401d00180f203a0300c04401050980c0c0c0715900d03050303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327045917 1250 327044667 327044677
    0x30d0506060403050703030c110312030105010c0f02090c0706140c09060c0c1302090f0108040512070f080d0903230703051602040e0601142e02030c012c1908 69
    0xc0c1c401000c00000001503800d108500c002d50080c3c5500710f000046003410075003211440e000354408d800800440d403c9040c041d00381d9040d10741c280b07010801d061907458020441c10710200003a44c04440310080107019a84280102401442443c0921498052181420680ca0151071043c0c0c030320018840c0d005542041c102070f0100401e10000c0321901494440810210603c140c022803070143c0006240340c482c10f00783c4203120644803c0c684404107107810b4413029103c0c10b55014001401c0c000103200e000b4000c90112200459401040c20b640c3c42d4041c05107240241000340040380440d00c949031094510403581380e9000b0041c141c1561514122503581c0032640d503880b102c40030042d006203d0406001d030300c9034070407600303c6080007004000c5941410f120850500700d5242c19440b9044090042c003c1c5016a40802c4042802034800c0c8280d1840601c10f0b4114000c080600ca410341ca004170346103604c0c0c1040301d107400083c112248401240f020006660b20b6500c6419901d00714494800e85d08005811200140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327047167 1250 327045917 327045919
    0x10b18090108191703010801092013020d110f09122b030609180b1003080706090606080f01050a0605060a0518040209122a100804050a06050a090c0512030d0506 70
    0x4503a210004c1d82d58034250003e80103840c07aa0340d030b0010101001a529591010602080c7d01e10030f00394030502c0028003409640030554911900481c00318100070f5036802c075515994515051a444031710082c28641ca80e000082c0140c0f003012000d211a1010002080c110b080e082c030b040390341c10030841e02c0301107241c2000c4500700d001c20142e541100049540d03051181885040da4410b1032a140c4410f401e0964060101525250264056080800004440004440c1c421341c1c001004243d044003410070310300801d0700b644145900c2c01040341c3d814000d04c065001c18481e0f0800002002210303154030611400307020b0201080086041048101f00e102684004103e0700480100301600e801403010218900d2010784c480b5070442da11100d00306100c811a4102c45469a245049401c072642d00742001030150a230443c1001d0900640d5400f2038103110050000f40304a035041041440682005107600e0001e0030354407025101c0004620f030204082c6003074268254940e04100046050160241ca090018880030b4001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327048417 1250 327047167 327047183
    0x4090e0a02090408030f0c16060f0b0607080408011a010e040209040e10090c05040504020307030b090a060204140906090606180a0f030602030702061003020d030e010314010b1809010819 81
    0x50010ba46546005110700c1c4a000d6190300d900700000e03080400b40d00a1300c0c1e10000c11080c80880d482c00e11504d60030b000c154000c00301148100d20494280d0081220740e1959405c0000090140144917841004104507050341c0e000f00128080010052501003030b50203181d002860380f08a206440c50240c0190640d00c400400014000030007901c2c10f40350081d134406594a981e101e0701e9080611039501d0000d4010542550140214901039001075104c42007808001e00c49860500451494281003080307291080c2d12000c1155141e4842e11071101c00d00c0c00c281e10314803130951400001c1d80c030305000e400c16000f0140600035500300b0081c0401e145414000b070128941041850300e000500f460900440002903000300030050340e03410305500090401c031b4004e0005c1124001c0c00c00400068031246000088240c0501d8440440495280100c01030051b5105040c00030712013500200c0e00043c0400188071b590403443d00b0403a205a02e1041c0229071000344124903141d04607440944401d0011064208281c0c881c3c441 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327049667 1250 327048417 327048433
    0x90102090a0602100608060f040305130e01030c030209090c0901032414010617010602210418050a05062e110a1103060a1119020c0406090506040b0a030804090e 70
    0x11a00034661a03002d440107a00004084403d11301e244112005401000080c0050b0302d0410b41181003c0c5015000038100071000401025070240302e00034502622131f1884509880d651390400e030750340f020140410303031085900c000403070480300c2c0c00103050011045c0a040e9031074580c60364503811250040f603551303080304400c0301010b010714520b00d100c0c2240340015880728650307e505083c2d000300040c14201800102c10400801440704540000311080d0f007030000c80044076080c21007a107007241d5008690080c18288070070101e00e1f0002010717401040c0f03d00341c1d81204004a40e1103100304000c0f0000c1840032001000400100b41c01410051001e1040025a0400314007144415020078a0701180b01e03400e50b805a040640030021746010701010750402d000e004240700c09668425540d1042c0b14000000000c01c2e0305c3c0c5c0b81e044c01c01d07000f4072204545c008001c1c020055956115815805854200c0d0514070807441d0641180403403801e0742000c03060700d4003d0b040320708117810b280c10500281008180c0b000a8414250 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327050917 1250 327049667 327049669
    0x50f0702300f070b0901050c12130f14100606090605030907030b01030f0b0a1a040b0a0e09011e151a190c0b1014010c0611030a02091c0b070809010209 66
    0x80244080d602d090400c980d25940343c200200c100784082c141403442c2e410403041c400035844481c2950b5040d1240285d52140da200c40408240340c0c0b190034401400d01c501000b11409100644a001c000c80c11a8000e0301c030062102c09881c412a078950103035030b0101d0711f0340c40148901c62007540516403001004084403203441c1c8075155026001c40984c4110b03a200740c08840d1004002c94610280d402403a601c00034800301c1c1500c0306103a000d40e08000300f640983c0d41ca150440080e911054920004d20f41485420018244507030518068004541c0480382e805007c03a06c100640014810107511080c3c10540e02c1503076081c02903002400e0400341009078501005d01c4001009a00c099058903000c040d529412807072402440d00f4003800000038015041e510030114204840718400d48a41f0b88403809181c03211400507180307001e100800051040700010200030007007056083d60395000700b90f0500200d0301500003141c446400000303010741900080c2507a4002c0c010608290240d9419500000000700160411803044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327052167 1250 327050917 327051013
    0x2011e141602120106060c0f031e020105011401050415140f0406210b18090f010e15011e0b0d0204081f060506070503070f03050702031609050f0702 65
    0x2100401c0944161000011860414140c03c01c20500e10000e00000e444c0400c0a0001860745001810381154140c64000305842000400415011f06a20ba821442c5801d0024004d102c01d0080d80030850a9040d16449580202e040d6021035000c035034010f584600c007030300440703203002e26030420402000244401c154991440018202030a0103035a1107a0110100710110407000d003607100c030440300f0710340450b400260b2240c00d006608101c50b82e14000d800d0311030759842803404030b025116000e02d500c0c001044213111400308045081900302d03020440c550b600c46d01e440848040150065104411420302081501d0803d8041c0000215004005003020307521904141000e80f000c9001080801c0b2082d4110082c40e144124000703010700b0f84203c1d040510075903c45660740b08880c0c0250204001400d0784003010320a400701e5110702d6015040ea00316160208100d901e8204d64010340d0000d0b8200000501141003105049228079a664003d04c0844106010551040c4400010289400c001d07405506903907592 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327053417 1250 327052167 327052177
    0x905071203030f2a0804030210060f03020427030e030307020904054c0b1903060c020115060806130507120b030a02010c0b09010f05190b030a02011e14 66
    0x3a49010403c03152440460003169030440510001300350000c5800703201402c000f0296131103403041c10702c0407042e102c0f4201a4613203600000700307804940c1000310111784803d00070b44c1e050072244243c505025103d00d00390070508001d040b440034050007103110042c00c0402e100703124522010b40c014096a1820030b0980203c2e6041c0c104507015074a903404100804084118010300b035020801315100d030009040000d00040200b5080003002c4140810a0f000038849189a0302c1f9040d01400141190b0119a030302c900c0584803103642c4419518503240c11030f074600180c010701034040342040c4130410800c40c606210342a94220310281c24150081c4035240ca41c80c02d02c0f030500c29240502d9483c1c54030030b4000044002841030b12414850309000390408510300c40142d80004501c40d805520030100c04691780e803200998010401a40c00b004514180014000090302600984050a408003418481001d1748428569600c040d89802400100d810b01c1012441014828001c9214001e00c0e0440c20ba0666204580c025042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327054667 1250 327053417 327053423
    0x30a05030702060708060102060118060810090c06030b1804080c012c01060e0c0a050f0a05030106140702090601030b030a0501060f050a081b0103180b0f0412050403021309050712 78
    0x1041c00030300d03501004041d138040d001c2d14240049141c2000000c0d142c0f4010b200c3c0e0180d90144002001002c415600520007a080c070004443d084045003506401400e9034000030784e545604140003054040c4a4010b02c06004006481c0c01106c80c91800e40100707080005000361140c810a1001031440c0d07034207005070081501181e030210840441d00c0b85e0201d070000040142d01441e85000020440403207003010b5030b0b5001e8007600c0c41c2a06c038250490255440d220b1a088034110560000303944174199040005181a26041c0d039640d102082140401c020b01e205580d0301951000000000034501e40c8650804201d414000d0300751000e0b4003041c0d48403406d681e1030307400c5000880440642880141440c0044e400104040740c014002e0b060019117003031020401c003007643d04040d00ca0403600140d801404400341125800046003104d4540301103806004141a1030480b02d00042a0b0711480d840c5c0f080d0b00f547d040c0d98000b4031a80c40401c8101c2260010031a40008aa05000d0344100003038010310b010100c0301c0140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327055917 1250 327054667 327054677
    0x41d070603060b0a091703071208090606040903120903050d090506061e01090b09060f1b1b01021518010212100f030c03081c06061d0609090f0c0705030a 67
    0x30030000041c1c1614200e800c0005501e005000100005078408020411101e031038a00c400c4089a8015050861080043c0a010740c1c0e550400c40341c440780d016000e54418851007050b9086c644904040100341c410040c6c1c09800101610b028100c81300196001c08a207910074200395280030311600c50325080d0b914042041c1c0b444e801c0602004a01d0501c03803c0d8480404031458506030550324840042e00c000580e009001c4441c0020800c0c2e50980c64020440704492120803000382c0325001c00408140c0d40b411600300002500903501202d06402d070400b800d5001c0d8030140c016010603512146010300c0310b0ba00034030b201c0d64040030743c400c1410381d0020b10007424500c41b010300e020500d1500001c0c0b24580c40703d035440b00001c42c1e41e02004001140c00441020f056a912140c07156a9a03040109180c000301e03100c8051051500e81100007075020341007032112040c0c0c84e980f441c032501020b51104000b4503005074017104e904821904005110f0010004520342c1c1309100203103a506220060700d466207160030403200b0b040850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327057167 1250 327055917 327055919
    0x20d150801020426150405190606080f0a0b1603140903041d07050703030c1e110d030e0d0e1212070c15210605030a08130503060123041d07 61
    0xe03440c1c444000131100000b11048040c42d01031452917507110300491021aa0050300046400c021041c17040319120021048055a5000305003409001441c0c40d101c0d0b440703144160701402c000d0b6040031645102050300103203054a240d4400003440d00e05100b100d03500b070805581c0c12503400c007034012a04d15405050404021611981060346e1101001500746c825058003100104005109078403504a0b07282c580c0c507181c04a90901c01001c10b0365041100311240c04240d00c100c946c5080c00e58800c0b03500c1003c132000e904652100024601c10b0301214505102400f2a41004609a219a005880c5007901c40300c058071410b02003001c6a041401c003108605d0740c48854100061240034007840d00301138800340c40c2c3e4029400307a0500c03091014182c1086520035038401900710707521914100131503000000030000641a641800b80380e03d0030202903404207000940121344c0740c01c040380c03605000071514140c0d00480c110010300600d215001800c0303c0200a001d60094031580da101e5141d01404a40205004010060650b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327058417 1250 327057167 327057179
    0x9031b01050a180c060e0609090411010f0e15071b060c0c050405010b072a0b09130905060a050c0f041503060501020309060702040218060705210f0d020d1508010204 72
    0x160b942180c40300340b0700007440c0c3c00c98041100c0c2c1c1c0c180411500d03217041803031488041c1401300341ea42c000c0c4c0843c1ca92282e00c0d0b804100500040d421482035100c070076a214029929114002e40d042107448145035040320500c040628002c1400004180f0303a4002c070401e070aa15a012041a94006583c01c01c000090050050780f040000200e20352000e040d0449041c0316071340c10701030401150b014002000e004103100740c641c04c0031042c00000070351401035201c6030651016140d60103050701c1d80c020030040f401000903004000c001c0c2114400c080480f42d01c40d02812040d00c40c510103202828016201d50a202010000441c4950901780140000c14954006505038130446c0d034041c0c00c84000c2d6000e141590410050310300345a031400100c0e40c2a03130341100d00507100c0d441f012a03050314000c00c0d010940c00c44c070b00156410030710030005034807413034002d0000f48803500c2e00f46c2071a681024094000d0048001740c0c244102803420070260050301ca6611090390014144540c1480c00440f02c80030340c0700d103c10340d50003d0103110f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327059667 1250 327058417 327058421
    0x30e0f03280f080c0318010e03040e0c03010f050904031806080403080a050c030a020c03070501050a09200114070203190c0602010609020f0a0e150c0c09090604020d030809031b01050a 80
    0x1e81c045420300c01204010b40c80702404454000342084400701001000400291136581011403251140000700b2000300894003295a0ba40580600c1c23442c140c60383c0c00101040211400c81e0f040e03c1e424110106010b2501050042c2d81101801c00c505001f04d00419200200c0045018002001c8075914200701e0300f4a418042d00f0b1600c09040500b219050508200316540c2d40800c90384c02c14002e500050b9074005580c1c0c45030440c0500300c8000c3c0194201402d000d842003140d08038000042c0500c0400348840b103001c071659025181410004c1c041010b00c04500b0b11400d645d00940465400170381941c0803010008018100c202181d40c1c1103074100c00a40013488410342c244a110003804600408529040c6ca1801c521103038007540c000b9504005503e40c00900b0380caca500c0c02550720f4091004c1450303283c11800860303d455001d400380807406955000006001d00200041881c0200d80141104d601c1e0310f400d8504a13030022009003070403604e10041044100c040c0305812800e048108040000820782054801d42d01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327060917 1250 327059667 327059737
    0x7081c020d1d0105090a03200115031e0f03140c0a030f0e0d0f02040c030204050909030c01150e0f041e0b06120303060102030f03220f02030106050916030e0f03 70
    0x50b040e03160404201c1e00c101d0000d190506690103040c110340d210070360180e00b10417a501c4c2229039500e508100f51010040480100c0d001030701d11580080d001034240800c8601c1c40c0f08580030103400721241142c580040380c05444448070f000e2004400c0751424511354041c1d45010100749007240042c0e205244407600c140e0200d035414110204559601e041c2c00d01c4c0c0c80f0f05031420002900039100710b9071081003144d100d010340d045400400303015024040c1458034910b41ba40b682c00c00c90261015500b4181c012140480c600f2083c403d40d00540f0b100c80c010345030900c0c4c0429a100041c0304982150742440c1036201080d20001c4402010302c00d010384104d40c60082e06000100481c21400c0394990700600a1048aa170044140e039094201d0401c115202c1e0f517440f580c0149560440380803014418850910414403030740c00b012062850003a070090015aa58800380031241c50102c40651060100c00c03070161410b4400e8201c0895034030380800b100c0d524076203004441d003154080e6440d00d0444c1003030103903002082d000512000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327062167 1250 327060917 327060971
    0x150f120b1005010c0305090303040f0e1006090509131401110c0f0a02030c0112090f0803150904020f04020a03090b0f160e0a0e07110607050a030e1207081c020d 70
    0x30801c289030900103005890040c6008003404404298116580c80800a450090a4544041901e16a141200303074400b14241c50300c40341000c03441c0011803081e0050451310211803014005548680d0303489081142848814401c480c4296052900745022038240a241415080c0d8040b090340d507541792280c036160551003200034883d1f800c41000800035a8003c10500d007203942c2801d004024140c0304002c4402070460800003092141d954203c04188901e050145114000140d02d1035840c00741001044980d0707004070380c0294081c1070442c46004908041d0003801c60304601e8100462840b03a659030b001c1d80721100319070340905001c000d0208482c40c40381516030880f0620790b007440e101c40c1040030080b401c0b01216001d8400c0b80c01b8980f0228a48a1185131208900003084040d111141032400d802030140c1e00400520300003e0806441c119110700c007040d07044004412403c0d4515015a40e5181034198000101007014000403103c0000000703060700040600c52049039001507016a01092100302844900b040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327063417 1250 327062167 327062191
    0x18120703140307030e010c0e0a091a150d020d0914160603020f0c01020d0b010216030f0f15090b0a050105180f070e0316030b0c031512011e1508010e030d150f120b 71
    0x452400744c601843c0e1a03c3e188140d5100f0304122907080403004601c40d1a0380e22371964400515840b0320440c1c0d50009410601c112404540c0128541409a50b840ca021216031001c42044c81001094020f42c0241190140c0000460618810030b01b068226000050081c01d81740c1c4807030a1001d990784c14800c2e514500c6283c00141c0e445030651303c07001e0401000101c003d001c0e80004d4055820301072600c4002c48803000586060044c4a100e18192401d54401d60b19614414107000000c11145065a51052100c0c41480322540ca40d454005011106801030244010300c12000e0808582d903e090100c00d01c08a42400d00120092440c64900d03940b1200405809049505005010126201345440703010104111611421030312001c19090050000c414800307403c10390071555103200099504506c007920802ca26030613001c4d5464055500742c0300105070595858101b04048240056140d1006412a0480d140d000c12152035004424401c07126801c40c0e0f160041551300c0c1010000211042030b4800d12688074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327064667 1250 327063417 327063431
    0x90901061a09010203070b1e0906010b22030209090a0c0b040308070f0213020c0a11060903030909090703080d06140411030c0a1718120703140307030e010c0e0a09 71
    0x8034000840250860400708000042c6481c120380c03003001a1112150450651144c50804684044100300044206400300d005000040c0c0c90703050104040d170484081001e1146080c0c400d2012130300401c03995219600c032402a0f407011000d46c80310f00c070b9039100e5405074004012041c1242025003c0700107550015072001c10401c800d0000848030f00a4171500c070740c0198a2540401ca41c40020515a0700f006d650318454804102030350501000591100c04602920021007040401d8003800802d201e00207107203402d64000c201121242c00c1c51268946d10030310143c02d80e9030240d120350324403103079078460864060051345a48043c4142040b58007400e51450b0201e5040016001c0000341040d68000100083c01381e00000c24000349990241c040d81001000c01803140c502882c150310080080580d040101d0510301c68105003d4040091900319020146c041e01c070481580e400540e00701403039000500800404d6200c81d80b880e04441c0074001c04180c094141c0394a1000da02c2d910612084008a9200010171820605 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327065917 1250 327064667 327064679
    0xc06020c0102060a0608120c15090304061107050d0f0335010512120a03020408120409110421060e010c0f0806040903080a0c0302071a060f040603050d270303020a0209090106 76
    0x1400c420941081203009850323840101c001824504030440c1c0d40486030b508001c10515440100050054511503210f002e02e0440c800c0c090303651000f0600034940c101300041094000314030079100711a0914840d15190203001c039800700c00c5c10383d280420307903140d000c60340595817084141410b4109405064280c4009000e8070003501c10390303659400184441346198000424904680c0320380c04542c040c10f00d000c01c4a400494030758000015900034422141d16a2401e5418028181aa02100d0407038188400583c00d000c94a040707207900303c05241c07003160201d076108090b2020010a000d02c0c0c4d0703c10140d40752510480d000c050702a14a100081c11b05100c2c5150120407800a1f070010346580c0c02c51003565001a0400001d48240d000784038019020307094990994051210543c804040381c1302d0402540c080b9050242141444140c40450000500e02e8000c10340000700241f260303101d4038044203211081da07080e450b201c50700000d01c4207580040d00103800800344201035061908015411140c400c000304071083c5820 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327067167 1250 327065917 327065923
    0x3080a05070302031603051503240f06100f0e0d06050603070b031303080c09030109120210020f190306180f051e060904030203040f06080403032306010311070c06020c0102060a0608 79
    0x140d00f081455900d0000c940a001422441d8003841c07000380c222000110264ac1018900316255041000d08504400154416050b049a240120b2024081d504803a038040b006484c030007000c240302010060035000e280c800303075944641e050150b8050b510000300c0782000414981010b08981114140d21020018000106a1040d0b0044150340603e008a40d64445410100e000d11a00d03210300d6040d820990b60310140050503a58440d420310030f07000c640082c404410440281d010701841050308080034030064000300c1010840400307046c0d6514000a072281c80c0d05c0030b0300403031000c40100d02c5001c0d500d82610300394103042d118280e00503038100500b1140444170742d810040c01c90004e200c0ea0140b2601c10200d0100b50007081a20060504190066620740e10340390300501000040b9010340c0042d041100d0800b40340b582c010b2004001000f102120207039580d00005401501b15140781c0103448804000c0c01021901c00f04c2140090481070713001d00071518007000024034211005d04400d405616044080285507000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327068417 1250 327067167 327067201
    0x2a060309060f050f011a040e0c0a081008060a0b0f03070b03070e0909030910120e0a150218040b01050c010e03030f220204091515090510230604080a03080a0507030203 73
    0x1b6100340c01d2805001c1e01c081030a005a03881011040301c600280b2402d0030711036000e082d03114900c0d0741d580c0d00c070b9540c0c900074240c0e4903a900ca440515002900818540300a6401818403200042c1180144d6000345010901c3c0800f41d901c4050f103441d011090040d40e65200b09402d078032100440d00050300d410280740e440e07217a01c81d04603501d105844003c0c2541030705000b0890745003005010001001152440d10f0842d807902c4c41c80c0002c6401c644103c2e401501c09015200380c5820500300c0780c0003044031100a00b071000a08280c2c64a5051203c1405040f070b066500b40a020821602c84004d56241c1c28402c00b440220200a820030072421148402c441501464036440c2c250a41c040340c0c04a0803020a00b8401000b417158007121340d1090400c0d0040c0045103c010307000e411507000c3c20080100d40e44d113001900703c20203580503401c1e0401589055000c0c0f51140319090464040c0145030b1803401d40d03030301c0d120343c90071030410800c80104120030100444c40320140304840d0704c0501c0d42019840d502d043c501400d106080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327069667 1250 327068417 327068429
    0x20612060f09090a030912030f03051b04030c0e13050a080a050904050114130605030c0906190807090f05070804020603091c0215180a2a060309060f050f01 68
    0x91400058415550410507492152000e0b04280150070f0410055032a410078810980c08100e081a0020300c1c11807003201c40c10002d406980d001203231607911400304e0190801074203120000303003490484188180382e0b0006000844c4203481010310b10b440c00035000100c0b480103080003540039200c610f100201304081098055190300605082d07a581c0e04000594041c0605169107400902d00b400102c0c4000760520100c0a406003240e104500a01d038403101e10660f901030003519010b82110030100e880e806d21454954000b04000d10302050f82c000c03030148584030b48282e4843c10141e4010101080251041e100d00c0c0c8092079000b1050002d0314000e00d01a101c0800034100902564000001981ca81420700141900300c40d0001c0e2850324000440c80256a0a1030311100c0c286c1f0510040882d0a052031200e403460350100350400b41252518540310342c1c1d81d400818000780c0280c410810075040120710b0400300c0700540010345000486450b00c4c18108110340705500c0c030f0301016107490140526408504211411506 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327070917 1250 327069667 327069697
    0x3060b100f050d111206130902150f120708010501080108030c0304050d06181101111c0f02100603050604031202032502011104030c051801030b0a1a030604030201090314070206 77
    0x12041c00e2001091089121080e00710003150305e2400202c031040d5a070292a046410780c0880261a0f50708044860b8550025408400c0415501d144039408000d0b00b031101c03d0003115410030a4800c1c006a02c01411150759000590701c4006100c2d03580c000c140140508505c01c000e60034a51a5440603a4038483e90240b11f100700c1440a0440c20880107400c450035000720030010b441030000070301c0c000b10251781011300c0b10301142d01e032442000327203000c0020b503c83c0482408215650420682c0001d503800c00d01c0102400841c0100000080840c0046c001c12009501c200000c20140c6480c0c140102502040e44569213524010418094001c00081030300201654010f01000b00c0d411003003003030307004240c00baa0481160101280000610030308041d81001c540342a038503801410310101d24242840d0782400010300501d02e1b6400b09a803034140d94040030040c4034544051042c590342c8400a490804110f801700d0060391a00f01400425902418000117420307030042141c1410070781d82c00104540108140041c0c0c5203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327072167 1250 327070917 327070927
    0x1902090c090d0c2c190e060f071d090610030608010e100b01020105040c180603020a0b1308010507021911040908120105010c020a0e060d140703060b100f05 68
    0x8192008a41c5500c100601451500381185001d10756810315115500c42c0c2d45800c0c40c011101520525100302c0006401e81007001a1365000807000d07004140d10300c02c6221607842c240082e4440f0100302c032a00800d8000d000d00d0702d52802820081822001800f0202c404030900642e00c41625542c06803a041601101c5880d015002d525044000b010283e00528944d0300f0809090300410012503110608175081c0018045902014010b900760390341520700410204d0404d108111500d01d000c1207181490a0741c1010940694035000900000210f1b00321000700e20000407040704880741d5919100080c18010001e000c5441c2580020303440780c0c1030882042a00d034298401c00c0c10014000415040e807c00140200800000b41c2450109070304007204140180d442c40d000460258001c140800081c0d900820b96a982401c1401c411114030019204d19042030f04401d41500003411185554006419a0010b0011b24a1410484155000440f1460040000700205420030b44c1c8a90310b02d03c120710900b41281c0d14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327073417 1250 327072167 327072181
    0x12171b04030206310e0f0405060106080a02040f090209010e04060602031804021306020312070908071202060702030a08030636092515031a010e18010801020a080702190209 75
    0x180b102040b010480d0340640e21400707541104d13980002030380e5840c10184600d54401c00485007070013094401600c47da1144004100d05440341c05000e9100c2680c0001500386680e540d00000840340907001644a40e401060600640d6882140c50141c1035007190240b1010f403a200f00a9100c0c814580c184000d20312038800e040035912160100d0348840c03400400100b82d90740d120b03002034603a04854550b060700e4111501103140644540000d4003070b6500c00000d0401a86071451107901e0360b500c01d07400c070380050040c80708002598003441000c10190248820b5540c0b45080780400170400c10080445124103424902c603204184040d07101030310040f180800c81d505884880c0014605140701e9082d0310503a60380e8907041c581440422045049540b040070003201080340c200b0a40540d03001000c10007918851641512107580310b04030491018a01500c5442d60740088800000500780c26004000b45a4000444481c066032202880b0341c040300e98805845007402c10322079002d8241583e400070784a40100c40205090b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327074667 1250 327073417 327073447
    0x506061918080a0503070201020d020d17040303091b0302011e080a050c09030a14061308120c310b03060a030f08190c0605010b03010f2112171b04030206 67
    0x30700b91850407904200f41d10b2034030942c1c0390310000080380140500010740300c201c0c2c00003464a110500c1626003000400400341c01594a40004000303034200340e1180c951001050740107406648400044400540080c11400050406005000b000400c1d41c412138018640580c0003255642100440c44042180c1e110464810202e0213040502541409150043c1041210b508440108146608140c444980d107484c43e900103031890030720103000650300b04049c02c1d0416294030b0190313006200319241c50400c0c0300c07880d00f0080c5c054a00320031152080c2ca1080c5640c02000005050024080304002525502c0c051021584082c0035120090400f944200c2000c208a2000d0640360000d0300c1c4c00d0300e50201000b50000030450300d00d80d0010f4402300e00d0000046488600002107c0c1030313860364207030310347c19515001c810141407116240c3e40c20400c1d101d103950000501130340078010700c80810b035a8241c07441c1c03500321500c002d00b02c0151111103130611214000c503900c1c103030406403005c40760101c0d1001c0d00c076040700001c080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327075917 1250 327074667 327074669
    0x1203270106150203030718050f0d0204090c060c02040f0e0304051306030203121209010509190c080a0b01180b0a1716081b03010506060301050d0305040909080a030506061918 76
    0x102950030b100030009420b0340000910300c603980c690b480762901441c50000c80800090703030059981100380102e9469090a0280400350703078900c041c000240c0301e603480d2650080300015402c03480009244000c02002e40c942806642031700900c0342c0080210744a559000380e0340e131085129090050031002000303c02103141d0350242006540140548116000d841c0030007055038001c860b0702330781d05900c0c0e001c2040800d05118161288049000414280c0c19a10048042c0704103400d044411049070580030a0010303007481600b14252148080300600d505184060109a001030b0700020070b00d1404120f0b10321942d4248002d001c841305014041020400c00c00880d083c103040360346212803417008260008031141c00040d021801490520404800e020310320070076090b07a400761030042d8031407414001070040d4680b124009256600c03d00b0310600d059541c0325040150b4814a00a0f0390428000c50001c42d240e40502038a41d0141c0112019803400d07805400030005030301900e030044200b03d008c04060138900455101c20b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327077167 1250 327075917 327075929
    0x3101803110f070b130e1b16020a090b120f0316110613050a09061404023009160302061902101415010e060a0509041506020607021203270106 62
    0x6100d560300c0741c5040c5400c0c3c0c030102c01040a040401700001c1c0740810307220168041c2c103065541d035151048035200da03002038200454440c190120b40c10701c200182d64200c0c1c030000402559201041c103458000802c080c155208010081c240c20898008400d80c8000c400c40c1c2c4403a504040f00300e00341082e4101003000d6451031884580100c0005000180301c0700c0c408200c41103510403180700301802d86915400041d41d40511501148a2041c03814442d60f160540152941d00032204004c605062940380d039203200b00c0c5150708011040d40c00014402400e0007403001928142c496156032011602e07540c00325200703200b40d145070700548803060366010300144240810302c4980403440041c42a00c9040c224000b00c40c40c00d0300c0b40101a00741010395182c550040200c1ca0046200070115804c1801c21281a50b4a611a03d06140e0080e52901d0250092240300b40480c05080745900821007032605000103840e20039820604440e0038814020070030080080c0340b240d140d00c880642d441d00180c0180e5070107400340606030410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327078417 1250 327077167 327077173
    0x121e0c0a0c0519080c1006080c041806060314070504020418020315030f070e01080604020a03030c050102040f12141c1d040e0102031f06020604060504140d03060503101803110f 77
    0xc0303420300100c2d04c05454083c055006807014003014001001c200e44030f41c45004060b4000307283d00c030031605e13295100c980141958070840c10303110328580d1580101c40c2280c00803503502c21900c1c078946440304d042000101900043e1011803409040c00030494005039030039181d03840c850300080001c61103183d107005003604480213002c50303120f00032459866448007454080e8480c4902c940000054807000006e000303011380d0700541000000380c2140c6080340c0c0d191400c4810346481d9003c1200003038126a10b51880c00904100710102c0340031702f080c0f030514900d03940650203501c26445105000902e200140d405801421981007104004409003d480d400d0004030040d84c1e409807070043c19410444042d00254410016031401810120b0442c0a2244410715401f81d0700051380031000080008031a80c0c03000360402c1c081c580b158a20440c114940d45040c1800040400081d01e0f13036001c2115045c100400c034050b11524400380541c0f20703c1442480c0f00301c0c2842000e4204840d814894580340d605001204401440d1420713 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327079667 1250 327078417 327078463
    0x109030f051e0607031a0d082a0102180306040c050415030f0602090123031b0702041a010e04060806060409030516060915050c0901030b0105040902121e0c0a0c05 71
    0x10207407204011213029011a0400b0311600a50a44522202c0c03240380040103c0070014440c0c1340c04005800240c0704200d00c0002e041c60883d804840c0c1603416800840d0780001d0303900d01c845605c45001d80031140b407240c001e074011002d1000044040f44007505442d403c0d60f0002d84c00c3c07414070f0500c440c0d60040c0e1014001070922000d0f02c09000c0580c0003070034241d100380c0352858000c007034051200003070300340b5002602584010704c040f4a070104090006c894100460b61407038200459600040c007103544144141000c4034420703c0d40291560402c420f455203030412602086102e14004144c1e450b40401407500d0321941e41c0383c803010b013054085e01c280ca952010010f8002000e004520b040c4000304407040c1c05861000e05156000c0c00401c4500408d44140d5581240d141000310050044d0042c0803122412414403209000100f03003042c103031010304411140151003100d075080c0183c0341c6031080c1d0740c2c010492110410108016807114004200c501010551400070544115400d10358202411003d10781c843c1c004040e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327080917 1250 327079667 327079723
    0xe1e06040311040b060f0711040605060c030705010f050702030d02030c040f0e071106161809150911090a0605030c070807030c0524010b09030a0501050703021903020403020109030f05 80
    0x100c010315004143c03020401802400d0800100b07000f4602c901a5084040120b01d0014600c00c1c4038200001002d04007041c50b51f00e5500091140c2c0158100848507407002c19841705000090140303c40c1d0014142e0100200d042c5402c000351644070b41d0b000c25030247e800001081070f055412040341d00070b004e500c6002e1001510780b81039004a010039078803040000d80d50b0b41c030790074092400b003622400340c41c0600045010890282c800d031251406e8082c600508c5d42a5940002d070f9002d940903035011540d4030310b407821619042003c1c4404449a076500b02c0c11154041c00f98100c151200c01e00401690b019080c56070316580ea0302c0c08008584104503000b0002e140c042154410140c002d102401054030a00903140103e41a2021079029212440b00c0251440c650740100300200000c80181000e08003d03060b19101102916024203480003900c0283c0042c2e800551824940210401c0c4007039820280380c1946458a0758000900e21840e0b400068881d18071058043c080100c01c010503420002c4584c581d0000300c0e0001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327082167 1250 327080917 327080933
    0xc02010816021c050712050306060301050d110d060b0111060f0106031d0d120501060302090a03030e120303040f02090f04150c0c0b040b0f06040605030312180f0a0201031505010e1e060403 82
    0x20800300e400f079a80c0e884006c5028000d04c20f4174072440001d0700090450307107020100802007031003920503502e8043d10180c01406464020100b550a8000d000109080701e054000400c1040681b4015825401050600803146040f0311070350b04440301c502e80403030307001c0c4290804001407540140079180d91050302c4c1c0400311140c10824424094200305403c0040303070791340e49080e000e91145158060348400b55842c14000a80100e60403850150007400144500c13840b50140b61441e8420b0f1070641d110a142e561940c118507103085900e0303100361011890020b50074181d8541d081c1c0600c1c0c41ca11071426880300100304481d4030074085880b0881c1c102d1200c0c01c25080900789030a040100340e0381c125940c451000011514103150040004503a0041c0003180b40800d0f00c0100e15080e4400341ca0f200d040690300001c0902aa4200650508842e100001d080b00701d040703100240c102c82d43c281100b403415444c0a420000e40c0e8000310810382c500c0c016142036800035001d040c0c0c0c1101c201c0c1c07038084652001020a011080c08821 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327083417 1250 327082167 327082177
    0xb09011127040c020a33020924180f04022a0c010507060b0604090c050a030b010305280e0f070503160e0423030304060f0c0c02010816021c05 62
    0x4003540d481030000c000240015190070549000c0942e000301c0d010303800201c40b21030346c1002d0043c9100f03440b4080300d02a824012081c240c00480c504c41e80102d48603500c3d2070502d100c202c00103202c2d10041754400d80611144214090b4480c038a003001902c0d0581045505e64000840340c56100510131541e54400c040221a0349003042c40c0413104000c0b1002c2d10ac0f0b00680000c151010280584035582802442e84d951070141c01035403c0c980e00901c06201c0001c01002a00504994401e50703220180ca07003c940000130100e812160b041c80c1014241014821450400c20a041008468811542d01c031555581000d010784940c4058031690710504040c078500b18804908c290549000b00d00780c03000355003002130b403040e00741076401503418407061040890000b4212405484107001d200c075101c0d0040c0d114007041800c5410840d000d03a5000e1f00e458104d68038218a205d440e86003c0b00f400c0840450300c80380c00081031744000a0440100c035111041c82000c85000f08160104681122034511003446440001011904a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327084667 1250 327083417 327083467
    0x60315032409060631060807050102060c090d080c0c03160f050108151002070f030f1a090d110c1905040c05040b031b07061401050306090106050105070b090111 70
    0x1c030002003410301d00c000c907030a4004e1070b000b000c08260b03a183c003442c0c10284456915040001d10441580002c55a06004220051400501078440180f5010019040c55070041504850710720400240c0951358890444200b020342129030070340ca60102c05070107440c001d0641c44803a8148150203108824966114103502076270181d640c480c40140d030312401526140425159441802c010800002503800c190390a400400c40300e05c100c42c082c0f40d446a00340f2100c51307150001d0701c3e5010b2025200050240240c000040701049840c4011a803a01c4603106413a5001c444c00401004240314070801c0101c420000b1541640c0020683e550005519800400900c0d40d4402d6500880c1408101d009050041e402c1d10308865102d98a1451503031850803000007500c1456401c402c404042c032070b01c00450118407441001c40c0100c9841850365040504052034003500501b0981c150f8141141404642d0b844000d440320075610611304400c540303c01050314050503030f00d0001018003401007150403e01c61800c551120b0920 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327085917 1250 327084667 327084733
    0x15170607110c01080612030405061306020706090311010f050c030f04090e0109051c0512010b0d06052b02030a0206031e160e090702160605040602070806040c030206031503 75
    0x10819541c161030790441c01d402808107400c0c00005409090440c4103c1034088104140ca03d80b40e2901c000600d10303000b14007500c0d0798008054003401122f070104060009013000d03040070030fa0240744d070f900d21842c0214106428104400e480305881041d00540a403110340410300c054070b46541c0e5144822000790010711681e1801824000d225143c8881807040c403910641002c00340142d100700d000d4090403000708081032001c020702084092209141e00340494064400280b0441d5542c0b800400f100907540701d078201c20310034001c04402c20780c0c0528051510107400d071042d4085071049030f10b00010707003005c40000010350000000401c00040840c5a41031b15402107103440c01d2403050b101d0307222045845554005c208041a42e02e61100b08900e4107805150f841140c910483c0c2d0300c00c0d4001c076241d10142d03082d44040c0101c2d80109050055030340500c0620007408207140102480d01d040d4960200840071840082d009080010200e488e01c56010441040100040c08a6100155483e07032040c0748100381d106000501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327087167 1250 327085917 327085937
    0x3160c0905090307260a09290d0b01170a05010501110a020307030209150a03050d0f0201020f18150f090a05030c03060604020a11070308070b0106080c0d15170607 71
    0x60303900e224a50081c40d038800210f040c10031650741c60541c015030688490324201c011070520750044240005090180440c2c3c3c031280e81030300e8000c56204c04c0381d0310300b1000707900000350b040700706203542d400241c503041e00c5844030200b20603002c0e10060f15030b94048110a01c05511100410551384003907040141250000e907280e0000144140d841911028542002903241c0c11120017040546000300409412000e8500311a210060280018034447e01d280e10860700c58202c406908a9543c00c00072098203640e45000075403401c0000c500310000d901c240e4081926924400750a600181c41341640509082c82d00d8980c95031320300072a0042c0d2803a81101590702e20a851900c8046050700b00840da2440c13008024006100f651150310820029420881ea1041001301150099001ea0001c0012000650041e80e0080da901200c1c1043d41e0000c4050308000b09011a40701848070030100b40044410b6115a00c8000a004601c20708003622441642e2061140809500310303292203000102d4828040c00072515640880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327088417 1250 327087167 327087179
    0xc070b0a0c08090a050706050a05040b0c0d0f02030c07030f030201020c0706030f06091b0e24070203011d0304060315090518060702070506090d050307020402120708060d02090a0c09030503160c 84
    0x40c4d080740708000c146400c2400c040203100e0141c0068404514207051050a15840310000141c0c0d80202c04000741c180c0c00100c00710712441d0842c1d03d01c0a120803c0c0b014501e4884141051944c509151000421780115004000309040c802e6064910103400e91064514031a49c0c0c2000038082e004500f807100c11189441000541d1520503c40d03012110030010114900c8400701e0b1061300c04564025003a604520411601040002440e01041c12640c20712982ca03282d0b41180141030031200707011600380100403035606040a1034000425181101c1c00c0d441c000c074020070080081c0300301c0c01c1180e20400b2068100024071142410f1038000c10640c08001b412610941d41d41e400407a6640550720915400c04010040b070f80c21414030740c6180f01864000c0003100e1034190690f0210302280c1c0800c44048824070410203001c40c5030b03407045a01d900450122100150310503d81c0000d0141d02c0041d000c003507110703503a0501e84603041c05540080003c41c0c0040c01d0f41c0d00e8003400c11284198042c078000484803441c24200c04110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327089667 1250 327088417 327088423
    0xa0212100e060a030b060103090f05030309030d0b030f070b0a0c12050d1a0603060f040e060c04030506132004090b01030510060f080d180e101401030b1003050c070b0a0c0809 76
    0x444ea04041c6111440d00d40800540041190842c10307550361910801c1d050210b40100025401900018001c0d030703a508118100504903103414000c0e52094010509101c20940d0021350741c0181c4112807202d036607030160420b080e01e0b1040e501d800204824101c0300c04480c1035802501504548401d2442404036036000c4259114440301d9114403030780501c081c40030034070351f0410703004800008401800000303144503070303031002071a00404135054404030741c0000c1c05004014003409629048100100703001900002695408444607410703c40c03405490f5071040101095889070050003001e034105c00102c205503100d05010b07403102800050701807601d04241d00081d09520340b00a000440c0d4201c0c0140c1040031072000100e40d0b91110090111080e503030400007086e40f4030b90845140c010703210805004400c6e4034100c589541c680c100303d08607040c945056403020190b2208134040c0c0b1031044500d00001c0f5070340d40b0202080c480c0180c81c8040e2002c120b16082006001c1ca541c0100030042013516286030300d660b48130546076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327090917 1250 327089667 327089669
    0x70806060a09031712090105010305150f070309020a12030809161202060c0f07090c180e060d03030612031d0f01050715020412030302130902030c040e0a0212100e060a 73
    0x700040e034280c070070004074600a038416290900010001e15020308511820310503141a01c0010240e55140010420418100060401c10080011085080c074000a82005c4084024218801d0580b24595041195035110344d81d8040e040c41e803446810354000f8103008254040440c0c0c40c1d40c252140d492820b21040501c0c01040449114500010780c1c81c60700e90074401c01e904001d00b56081803103000c0700d81d0440302082c08220301410030701000081180c41104000c081440610045020031911001401140400b011003076022000751400c0d400031103545011801041e01e81e00140e038203035141039220105980071000795055031091143c4111085a9001c12113520000002103001c95802c000000005103560000d9400c0012140c0c0142032035a1640c01e16040700e454081240029400034544862041116000b800342038142011800c0d460706820010700c502c914010590255103a00004100e61810340480355107100d9244038076098141620350320400c00940c010035003c03421240000e110380c241030b03d04c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327092167 1250 327090917 327090937
    0x1f0c140d050f06150d0e010207050105010e0403020706050301050a050d020109050405130512040e042a1203030513020105041703130b0a0801061b060b01050c0114090c0103020415140d050c0307080606 87
    0x103803522110401c4400105410703c4a070034195001d0003107032702161013882454020a883d01e10f841039460903160003401c00c0f00503001042070100900040c00340d500d4070401081590820b403a08442e06205000595080c20341c0c7d400298428141820014141d260500ba00200351145d4201d070028455003a03100014012030003000301101e00c0200180102d00d485038403641c0590741038803100c1e055101e10301c42c5110306855005030242040010f000d1041581c107116840e44501045002c050303000e400d40c0000c3c01032141340b01d90000d141c0c20010781191090b060040354244103108108000071f607501d201016554100e1a500004a40128000602c81d401044030160b1b250420110311542d180c03541c0e85030000e042280c170315410071006100686144100348603030418010300d03045100d01454004c510610340041441e4050400d801884200004c0414031020f80300307002542442c5884651601d007a01c500d0142c01e00784c040d0740d410442408408007aa100a50142000c2e41c1d8004982c2c0d42c0b401400128803d8070310700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327093417 1250 327092167 327092209
    0x6160318020616140322171c090b0c0c0f0d0305091302070b0a06261c02011e0207060f0504150f0e100b10021f0c140d050f06 55
    0x540e8a440d958022280b00300c0c03144881c1c426141318440303000e26540040150741500c6040c03070f00840740103000742c8024006102d1090401660480040000d1312503c0085c211814900c070021081111801205940c0140000c4034075503032100c1103c4501540d40454440c01d0303000b10001c24880f0090304141000c401c003280c050b00c0b0b5030700e0104440180001003000c202c10a5500d42e09100000c0010807000710303280500090440803c0680c10000c050b60071500030407085050350351440d03021011481c045640d180041009001e0188903010b01001da014040e0586100d40700b03e002a501540c0c102d190f809482c1300303809900200f00701008004190308981064501521800305900700c1c10003c100d9811075200310f00b5010340800c4c0c00c0d98030401c051070240c00c040000e2160742c40c1c0d802c2c0595800c01c44084c0e4000d404620060400e003c0031080350a5080f042c600d10b496180d2600540001ca03030081020941e40c944c00d101041e600c000008801000700000e8440083c08038120021610b580350501032820480d10711190 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327094667 1250 327093417 327093427
    0x903050405100e22140103060902130b030a0318030b0c0a020c03010915090c0302040608030903010f020304080712022103070f020a0b27060403030e0f03040f031112061603180206 78
    0x200407a184d03809110000318070340780c2411104c00e20078a01c0c810b000b1841904042482d030581d01c1000003c03c080902030141368900042c410b0035503000140d0ba007d25130035007011740e5108a80305441d40950341c19000640703030700704440070f001400d5041c000030044c003482d1380d003038a01e800002c4040509030350b00c1520240c120899944042049102caa21031030f850340c4141c5103941070f107036281d001c1400e80f031155000c4d01c43e541001c03030b07161041e0800303005140e000d038800c0000f14070311310381a501c08540317001e0030300b0141125504448034506503000304410308000b072154242482040c480d01129009605c12034060380000c2c8441c0c50a0001800041c5c0404800d0f449900045140d41d030140041e2030703042c05548030b0303055a1054081c10541c1c0c0144402d07405640240c0d80030510540e600845803404810001c400500d40c0108410050740c1450303084039060707a81c80103081d0b414031222030004500000030000095103000307003030038441c146094a05030b15110700c140e11b0038003588041601e1545004200721005e90401e000b00300b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327095917 1250 327094667 327094699
    0xd08070c03051b060702011b05091c031413050103060e0709090218120105070917120f070206030a150510090b03040f0807080406140309030a18090903050405100e 71
    0x2900845603209143c1803007010907940c4501d040019902d00001d44d541e201154030104d2111440007011504d414000e15202c250004507000880310507030643d4411400008400305449040046142c003030080c07460b80c40300b03221543c003030300711441e80300b550b01007468042c00113504946010140d10071841c9480380d0404032300d0155100060742c082d89100041c00840c0e03120903107580da504101c0e6900034401000264529204001420102c0302d90090007102c080000c1035141004000b440743c421a00c016002a16100e0311070390f5100c2c900410100a51100e404000c02200c907030702c0c1e841054601e0007516003401c8141c5c1c6100f80000d21039a84d91020000301c1018040c8495103107440156006803013444462541049501c0b2101c2d035402c00c40d01281d40c10400902000741c990702103603400b207491020130030a03e942000b8040590300c0c4219150401440000d0303940c08030b02414244d0f9a401000d81c03010a125400d158079006107181c1c041c1c0240f070300c0b44c041105100c50f1540705460202040ba4050541e0038640c80c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327097167 1250 327095917 327095927
    0x40209040b070e030f010515030106240212040e090106091a121203010b03160905010c02040f06090219020f0a11010c0c151e02060c04050f0f04020f07050d08070c03 72
    0x1e00200900c200e440c01042a500c1c10444260100308100001440d82020100a6123410400c2c0d903143c8aa81894010701500403040c00101010481c29008120352000c00c00c00da0511000c88030100002c40c0102c0d00081030329404540d144a40320880080003969100c005074812204604017440c201c400060f01105903040850b03002e515810300100b00c818801140d83c109160364400d810090403203030040240204a9040c0d910a0340c41656424240c00c0b40b0b0411000030080d00220801a104a4450340350f039041b42655813003c1d0150000304829035135a0440a00050412200c1708003034018803c0e50300210000702c021801c400003d070b0040c0c0f4501105490300c0111070848020360244c4030b51501000005034030b0a5142203054400030358440e800040700181c681a0b1315901840e100096402c14010000c0301e4a28004440c240c4208485c0307643c039400c5450214040d079454095a941003840040c21903205503400c1d01800b0b985100d281115032001032600e007100c0380c0345e05544080c08540e4140c58000042d00078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327098417 1250 327097167 327097171
    0x204030f1e032a06051e1312050d2a0e060403021503180712111210110c030301300b0703051806190606020f0a1b0b040306021908040209040b 62
    0x2c20780403208124151165000c9600a076407a114224545181c0851b0805044865130720282c42d2110084c0b0042d580c0320074160203219a80340042140c005041075502c081d9500002452441080b40c1507004d460118442c03181c00d4404200300450001021288240ba0880c01c07102520341c0a03000403d07c018003021034506401c0600000c0c0c900004100c0c1070440c2c0000c0081c0c0b0001d013026002c0404010300307070801840054259055a008030000d0401343c941e2440020004d0580d020100000b171600c0180d84040c01d18081d099080070740f40400000041c45d03a882d403445260010765a12005d03c09051009000c0320040c603054010800090300c0c00103404a030280d80038650000791405200c085030081e4660301e081100c1181c0c42c0c0c210b0090751000403aa54250310442010f4040c0e07000610700e105002207c181c0d80c041c140002030403811600070b03440d00d000a1090000080c81929541501d070364070317450404080d411104042e00745648091126003401c0c40340e00d215016607000b410201d42d540380c503200c0210031640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327099667 1250 327098417 327098477
    0xa02040b151801080c030906160504080a0309080d0e01020d030c05070605010e180f15180601180e0c10050702150d0902090105040b01080f0a060503010204030f1e03 72
    0x1220001d040c29111440100003804030000071031a8000c2c008000f410800000d0500051003400b4020041c002c1e070700003003003a0031101009081c401d166810004885610480e04451458042d01c1d08201c109900000e079203003642c4000381a18652000504200c2d104915100c03010300507884494040041030081e404480d0001807442c00d00d1600e0f1441c2c8030fa4054440a03440b001a40401100300803020745039208070211a10480041c045211000003030b80e644100e8000c4401141030030001080a8004910041040c0f90010054404969440102e01c088405003c85900510f04040b00080c102c0000304500301108001003100c020202d540c0390840f419008544101e82048070141d4031080c40d0660401b80c120010020b401040950052040c440e01081c1a0700c41d90003641810140c1043e40c0c0c111820540c0100e44400d0427150b5505c0511141c09080b40e07034000c1e0b4040d48001030110512111102444040380100031100d08141c9020047c1e90f4264100005000030306411910b160b100958110b0b146d11000b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 327100917 1250 327099667 327099679
    0xb070306050d0819181a0d050403080103020a08030f0406110a0606180b0a030506061903060e2b0903060b030a0b0109050411010207060f0c020d0503030a060801060b0c0a02040b 77
    0x1d1900c001c210b411400b0001950300e0702010940003840d8220001040380700d0b140f403a00c6013908a90800c800308201c0d05000b28000d0345208200010180721801c00e0314141e40d10b43c1d00230711140c1030a0030301a114542c01c0c0410307401452041400310704440c00208481109824458040c82d003850890120344206101c03840e21840c3c0119101c0ca0007140c0c1070702951000c1c05101951071910350001c41142e0440b107060364928010f60380e00d801000458800f00380a6404a0299000007101150f940d4860481da03507a040244030504d400d6250074007800000c0d080b00d14806a46502400c0c180640d030050b00341c0700c26034040000585d03e0009100141d02608041030550010741110b1300c5840a5841107030000090b0000c030ba00c16660810082030001c0c200981c0e0b40c0c10340a0014151050401000929401080c09860305010b0750303480c1e038404c64a0701c098940c446a00b010a49850382080354205006c1e11507481500c6866090000102c0c038030f40f140003120400c3c45044010512040283d017440301401800c440968400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 327102167 1250 327100917 327100919
    0xd09090b0f0d1a06030d09030602031003050708031c05090c280801090c060504060c060b0d0f0302010920010504091a120f070b0f0d0518010c090906080a0308040b070306 74
    0x2407580320b0210211445604209003643d49102c62440c0740b50000e0a00e44661b100010300c0c0e00301c0e9080019181560741060015039a6511309103102d46040c2a43d0000303216205030b000003d40201d000c4040d0041901c0c1c0309200e03050803c0858114195002680c02560320341004003040c02e036140c41c800d0940010b88a040c80d000407400a4140000040c1c20352000781d540c0d454440b980e04110340381c841d02c07001e08641d040c45400d040c10010018166080000020415a51110200380d55070341c00e10045201603001c0100c030030400b500d240081c00f0b4014030b07000f00c60312000d00f9030344c0e1046810b5085494541d081031303641600f040d180c001445c000e8505444040c20809104600641548400351000b03481401100140040745520700c555152510980c48101c040c441408202d07200180c5a044452078442c8800209980d195480900408100c1303024900e41d6620341801e01e5146600003243c0b10071207030120320030403038030303a0314070032035846584c5860028009481d00c0c000400245a040d5100d4010326503240010341382d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 327103417 1250 327102167 327102169
    0x1202090f070e1207050307051f080406020910030c0e030607080a020f07020913170901020705060705010216230a0f02060a091a1b03130302100201140a0b0906030d09090b0f 75
    0x4600300041202d082e070811441401700d420208802001020f060b61540440c80d82041041d00a140c2c15540c2c00c104032074107001c2014449e280e0183e401d0080020200c8a04031100d46024004201d525002c0003c00c00201e00d1514a02e0081111840b406080d21410300c140c0e01c014481e070081d489000142034181e4281318810158461400242c070552049800f11095901800c280000c010384006008800e10100038036039071a40e01050b42e000b01e54051702c41c1c03a210000c5181c007902a014001e00140100034001e00c1c2400d00c00e191a8158501603c00c0420006610304000300f0b4130f0308032072100541641507038a052401424010b000b01203950b90741c580b102c001078450007400480d541c100310100e2005030106040001200c4440d1900310001011300440c94a85540880b0342000c0b110302c0040e1160795042040b50015000303400c54900365280e201c844820349032544201b03005019031030a1501956003e40003400c82e040004554032884090703100c007040c00b46000507000c058050110501c1e005440d640007120b403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 327104667 1250 327103417 327103429
    0x80c0706020708030a050906010305070e070908010c0e010e04090b190e030a020109120c02130f11040f090609020a140c01060315050f16230408070e0f011202090f070e 73
    0x424898074543d0703aa414400f1450007698005440d0081d10b0b00104d004000141d000551482115114841c04080c0d540d00207055075001c495500c015901e5003080c804005a690055200031081d50980722040451601e03000c1c40101e030503074080101a4100c0c0030210360503181e02c662a0300c403850303841004100c00300850802400c41c3c0210518002607912040c1c00001c00000038508010840285080302c411511a0002000d02403d0350300c0000c0c0da0f580d80c1c2c1440f14182190402c3c2c240d9250503440075607903a960821210030514a00c2440e5606260210100b10008540202d4042c1440303560f9550003140c0b1000081e81581c400040c061143d076880c4c8000000840b144480100f070042601b001a4a2030014200e9021000c0100905c0303442c81c0312165041c40540000d02d04441a882040580480d50b44a00c0d5412601c501c0d0860410380c462128002040b00c002e5280c140b04888a05929080740d80c2c90500010030b035500b600c001e5204102100180408003040c403419031082d43da25001280e1022840402c034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 327105917 1250 327104667 327104677
    0x60d0903050a0801150503073603020a330c0c060509090603010b1c110a0321020304080304050f030313080303150111060609070c0804060206010e130c06080c070602 72
    0x408590040b81c00a002a003002d2024010006090178010140004030000d285100007400c40d42807000c403a4a42444407080300b02d440340000f01d540c0b080642000b00007003400504552104900c02e2162440201c0d0b524104100c3e00c09000101040d80e805a10b0786c034a6004008802030780c80204840d44c0803900c0800d00b0f5102d04401030107036840f4241da5954100038401002c100030b20090103603040c40b418080c1d5440d03c404540e201c80b144170304206800201d140200700107094612407070f80040096004410721408864017114012905500704820800e0f4509070307204d000324071642c0155001840b0401090500fa0030607c034900e4010240c9143c01c01403507040d020070440f50010321441d0302c00f1041201400e141c254002c0100401d08254511a200302605da0340c54400130701643c0546200740c0401e0480740600c402c2450290f1115030640c03a55140c440c02540c403078007480340c40c0b020408c034004140e07507499040c07443c020190003a00e034000c510b0900c241603d8248002d820305240c2007080003d64041186803016007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 327107167 1250 327105917 327105923
    0xf1101020f030114010c0515060303070203010e011a0a03050303010302041a1009050406080309060708070c0b07110a0e0609070f051c09020306060f1804030315090b10020d0e040209060d09 82
    0x1900d0f54181243e201e8078500034140e03107050184101c10200030840008074013044583c0e140d02040c1c15954540424154014640e0003509903013040c04027404920190080b40e180c00300f04140100c0442e8a00410484216503c000f801c190400c00050014ec24650040c4442041201c6104100038105010400c0c90740760b03580345400103410300b00c1030001e0300e4075014460080c43c0c10402541042e1000c2c00003603a9129082000b0000a0005000740404c004121090014041c0c011025100d2660f810003010842c1c0c03a8441c2c6124210202010401286846100c0d0286401600080240c3c2e18000d043e83c00c400c038400400b007844401e0000d5162600100103905880025400128281c101d03441858504000a040d1038424035030a10f000d4595250789030015451856000c1d1001140c41d50f00781580188035100d00485201c2c0041004503840075581c1090078441e03030035900d110100031041c404903103c040b0703081d80d50300250480c0b030103035010720745034000c1d01040302c1c01410b1625120f107600a0001326083c2003411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 327108417 1250 327107167 327107197
    0x150a1a031806190203060315072303060303040605070609020402040b030a0c0206011203230301060201021e180d030c061503020f1509010f171e0106050702010c0b07030b040e070918050604030f110102 87
    0x2c02ea84d084040c0c212b07103201660401350a6007802c2001079240d00035401070b60700b00311020402c0e038240441500980341550b0090310441d071302c540f100c212040c59030046544480035401c1c41030414201d4400207200d03048540b0407102a2892146036000c840d441e00507005098001040301b48082d4140081009500030185900010790314000c2000c050100314100c03010000581c01400700280c00190015003045031381d4101e4002d0290551882c082c0c13000d0881c6503014007250700d400b000400000c2c41d4000d120030b0742e0007100c29507168082a8108a80b910220314900b0788944c0600078a0709a5006c1c0d01d200d24103284508010342c0502691030302101e00c42d030403950610409014400ca5404901e945559809007515280c0240751031190740010305400007201c0000c1c4120400d2000a59543c46a80310347c41008004100b4012030942c03519403035a4078541c2c020803481c10b190000c10f0760b0030319020b0a01f000c203079405809080300342d8454900b541c0c07482214903004c0500c04500a11303c0412000c0c0b0051403460303014119 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 327109667 1250 327108417 327108437
    0x9100c0f0323040f03110304060e0913030c14120d090308100b03010b1b010e010509010c0c23190506070e0103020c06150a1a03180619020306031507 65
    0xe06841d4110b650240c850346000b81c08040100301c0030455805074002c001030284801a280c11251145841c0b0ba0015901001c9404651a60300c643c042d1013114040b074030102151620580214000c0d9000340040200c0c0301100150002003907280d030034854025800c01d864400070b0011201400360301c14102c83c207209a41d8902c1d40c04064001c0030454021505418402d081070170400180c00511040c000d10304028408200600e02413103030348080064038a414028400e0f09070600f44103000c1c03c0c007510b0094055081980b030501c6e092203101120817071342d04082024500505622214030030345461404070007502030358800c2c4280341c150305031103004144140700420700c91030444402881e110f404248541050b0040001e05041580059010340082400d0407a8165074440c07000035a88101d1580403440c2d4520013521208215030000c0075500c10040d98080100c5d0504140d0026240c003801c8030030740078480e10544c5154076502503074043c43d030268001d0111940c54004000003040403030200c42d1032002a40d0004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 327110917 1250 327109667 327109697
    0x51e0d0608010501080d030e01060f080d03050708061c110909030d0509060f1807090609020d0b03010605010f2723040516180f06080420010c02040509100c 68
    0x1103500020266070700200281d504050145440e0341d0186040303020940c444005404c080000e40c04240101441c1d8518150070f0b5035141e109403109443c03201140480d1034400020400c0703005800c814801c602c014100e1241e17584100d00c449000c0c401c100240ca9000121000b4203d980b41c4102041c01041200011510396140842e0141a0350004140c0025a0800014001464010104680c0008004030051451070458a000b440c100103588220069800c3c4440042c0180c0d803a40208401818144180080c01c0d13100d080c5401d0301c400c0d00c5075a000800d6064401a030700c0c802c01042d2a031010381c07100396182c006280e10100141c440c3d500301d25036242810780301e402204074200c0c2050500800303440901c035500c0c11503588036660004e80850014030244651603038101d100340d090700d40689100001021407030344594008112403403c4904880600110000403c480086920000a250140d440760f158580540c01e00c0090710028102e9100c602c80e00300c8414155070b8600458220764190f80c1d85540c0d00446803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 327112167 1250 327110917 327110921
    0x1808190b130305030606032508060a051804032a0606151107030809130204030f03090503060f0c07020a080f0d0e04060f0504150305060708040501051006021c051e0d 72
    0x90404036445051000040001c3d80082c2503e0b1300a10440e8882d403250743d56459085406008144a01c190422000822809070804e800c2402030340255100340c0c103a5264000d0000b03c0898104031106c5210704800200024400c0b6558040307101101c08901030300c03002c40b1090342100700f8000704981c0c494568030300303102c0304e444540508080743d0310b4640200b0721458902d42e191984c05901014007042400241e0142948400e54a546001084e6400319952940c0342440c0c0b00d90042e070a01100001e85d246000255440c0000700729018900041400065072074030000c3e00d00725400900120f8000851000c00581c140c3e0521090007184400c1c0083c1174000003440c0014402c281081ca003500c1a4500001445842a070340848801d80e1001e4030009640310781d0011070905600340342d1004080d8480c80d000c00001c41d1340000980d000d00d00c01c900a002540b601c0000070380301c0700b03a03006240c01a4007041e812906130710140440c0c0d41c20500341c1003082ca0a888143d01074a0f030020700804241d1202c1c0000e0400304030100b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 327113417 1250 327112167 327112171
    0x20a082a070905010911040b0a1101021e0405030d0c0213090f060c0e01030b030111090906060f07050f0f0307202206080f0a11060f09090f1602070b03071808190b 71
    0x956411f8609420024142424011003000d0801c01c02c0404084101071401d60444a0a036406d42040c004034001c41290900c41d1700c1805070340e019004001d0b00503d01809140540510380c0e00a10089104400708500350081c4601241904d8821403441e0320804202c191040b881c0c0b4030016a1120024624040094261407003c46c0e0a0b000340c0c58240c4d5404004d0310380b01901c020603c2200c80e00c99a40321600015958000e5200c01d4055010000c2c4d960704000c400280c850744034008500f41c07604207050b49031450322405081800b81c45400031041403107410512100e8003142400c000c00a010f26007000d02a030080074140c0810295041d6542014860520100401039814110070024056041660f89103c0c0e4001e0300d00c0c4003400f0b030101103005c404010340d50080d80c0441201a00044552030301c0780042208507420b030360424003841108060041c4500c04940c03601600c40c081809841e54881900c112030411943d4818020306145100c0030800035828441c4140720103982c507280e00810401d00f80f0050078000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 327114667 1250 327113417 327113441
    0xf0c080115032009041d030a050d0e1903200a081b060a1a0607080406030e0703060c02010203061c0b01060e060d050c0c0d020d081306180f050c01020a082a0709050109 73
    0x210300203002034040d001042311140c111302d2030306035112404840381e40d01518601a42d64014058002e084070002442c3e520f1408960280ea40d2100007010800c5003100c0041425060340c1c036030002c18480e030202d02003100038094116510401803200c0030100401e401c2c001c080c0c450382c071190f403034240c42c0038803c2e102000c40e0300d204c1c0105da030203207021169034405015114a1240320185912000c110000d410309208440007190408400d0004858060f0001c0c000c0d80200c5200d48035189209000c2d0074110901000303407586600800f20f410590900350191182840c0b4944590312040030440110840303604d004060013043c0c010420780d00c84920070a0a0706000b103200c3c03440308541c86411010b680742d0344501140d400045490300380c0340c08403060400a001d800d40c200c4088036506c0d4031001c0000c21100305070300740da2640180c064400d4890851f00483e1a039001c0140034002140c01d0000001d90910040212070856007558a804001032885007141081d2842e8403034450a0703a00c000404c0399040134010140302e07084c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 327115917 1250 327114667 327114701
    0x2010e010c050301050910031401050106080a09080a081009090c031a0f040f020102010906020c0309030d020610050906040b0301050f0f090607140714030d020d0f0c08011503200904 79
    0x10207030000800c14007051091a01c544c07510004140c1c448298100c840c00346800c03000c0c41800844003e020b50180c40d00384a484002002200000c2e0386031000d121380e400040d44289090300d070041c5414212154070020b000e40350409100140020400c449100d42203144d4491112005901d00d0341c02c168000800c0204641150783c040b10400201c1d62000c01155849540103548400011503400101c1c01007450402c0202098800503900240d00c1c40040a000420f40c201c0c100c40340102c0c0810202d0f00ea0001361000182025218014002454443c80c500d51000001c1d00000c0c85002d50000242540c001740d078210702c02c8540b41c1c28404488130405405a0020a210007031100f81881c9600800c0300004000ca040d4414001c500c400401105400d00d0402c2d0122034101d81c0c40f00c07404185040250300075001c5407030161034440803081d0020b02e030041121070360b107540707500c25540c1c030300314200c000c0c000303200e868804140d41c42994038540800300016000f0003450086085d11400d6050a01086611903000500c03c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 327117167 1250 327115917 327115931
    0x706030f0b04200a030b0303030109051f15050c011107030c17040e07050307020c09010b2d070206090604030507030303051602032701091710050c03091203040f0f0c030302010e01 78
    0x1054440502940c1000030601c1d6034242d0181300301d0080200c01d2506905010000c00001d50702070b140c019500503070b000c2c9a0020340505034840194442128403a680e0050600054810446d004401508203502c00a00104820500580300c540c590b016100440110315410780c00000c0c043c1c1c1d601000c0c18800d243e50418501424a0100d5040510040100301040f00000019503030358401d1041c902d070300801510a82e10707542c42e100d2855454001c07100c00c00380403c1c0e00502c03444200080303000583c0d0130a10108186001c0140c1c080c000c05900224890750850b40400c000400548100f0040f0002e60283e60005150300304003603170340d00d01d0103003010342400c541c0107110b017045404041c10401c41d404c100040d4a030341b9004800061351201101d61240c0c102c0310030340c10781a04c3c2410105040d0840132000004004130399a0403800040c0380404d0300d130030510380c0c00744180c103080205030001541c116005581030b04048241c5e41d00c200b6103000122045036007885a050402c10141c090041ca202020040000d01c190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 327118417 1250 327117167 327117191
    0x10f090c020a0b060d080409090f03030c0e180604060e2409010b0a2111030f010e13060e1903030b01110325140a03091e1203110f0706030f0b04 63
    0x250a020301507510400c2c5c14140001003005a2007113500400b00c900302806949030301d05240c00030000300c00c009d0780841d0501c41083c0b21144142078903590144001c001a092801100c401202658000e207056006a5120004145656981b501600c107a814000c2902c00303000390b01c244111100e0300381d007441c001c1840b0001840030301052000c1e0b510980d41440d14202c8480e048240d082e02c02d1800303100d20720031494004c6001c501c11000300154489d00c1e0041643c1542d981e95900305054520440e02107800c0c4048501940010303500d81c00c906809060304003103030b4040d400ca00404e00e1040d40e840c1c0450100ea50344e00000d4a658011360060304c00010440958185000041d82508210314080400c12555038030171302508201d504c082d134040e1210078000301ea840c01c00b64500034068900e540601c0c114660311a000c0440903d01120f00001c0e118100e60300840c81006950030340b00c01020342a400c0e01401807540400d4030304010440c0400a04440e038011541c101050210001c0b101c0c1440b034076004500702241c554070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 327119667 1250 327118417 327118433
    0x607120908040e040204090816140d02031209100c08090d08060307050103020714030d05040533042321091005130911030f07020604020a031b0b03010f090c020a 70
    0x321111000048141c0c4e903240300060003001e1f40c12000305050310105520f03560010700c06600c4480c511414061014425007040030380e407124920000b02c01681b007041181900d1510180c6150042d41c4c040840c1c0044c52020424816100600801c41c0000d8400041000f1564100480b840d50125810115001d041010100b92078aa0a00030705043c141c001405c9020070405c4000c0050354210b00e0107582d00c40d00c04052410241c401a1800d030b80f031744940b4201c0005003070404030700c0300e080090102416010404540004460400503c15240c1007040408004242c0c01e84001505100044004d403813403944d041c295241018a81e00c034034042c03400030700640b03003940c40d00c0503641c041880307604281c0c2c1c40740364409440e105601d05810880c0c100b403c0010850f200100100514050310b0581c9100481f551445000c1781d4443c402c03500a5030003d40a1010000708860402ca4141d0000d0124030501c01a1102e20381c2400341e000303a0100c2d030010181031042180c001c5512584040d10000c1c03020b040d20441030348950304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 327120917 1250 327119667 327119669
    0x910031b0503100315060312140715060306021c050907030302120d060f0609030629040e0c031e0f030307090303050c031e190306080a0809030a060905060712090804 72
    0x105010000010600d401081002c450040d51300c8101341c00d6117400241007401810b107510046030050015400403141900a001d8040481618290341d0b081500649078104000b0203c2c4100c101140c1d101408000700d003080c0010642409503442c94003900c094034070030408584000b448000c20b604115401e20001c0e501042d00700c90f245070451403d0310380c40e0503d00da1000f00f1003540000b161102440c3c0000c4c0050b00085000704503805000b04121280c016150201c00c00045040703c100000e02c4860303002d16180c16401040886d14190440b00b0f80c403c814003091406840c038542c1d204075041002c40f055204000c0042c00e4014543c58040c500714200010040c080a046000050a0007000702e4800340404003003040d51003461a984070103200440c4c035000302a035a48407908503041c0300c640490204d9806d0003030080400b240c4182001f0035900c005906e43c0340407504591002681400307007501c01d0f0003081d900d01074500d0036070051015100b54105584080d240c80315202045030b00b5410300c60200d01003180304041e20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 327122167 1250 327120917 327120971
    0xb0c09150f13050625060f0c0f02011506050901050a09030206030c040e0603030a0c0209090f16031101141b030909010b031006170708040f140304080d090b0702060a170705091003 78
    0x7400030303845c0d15210000d86a000e030701d00202403030310340240c0c1221f9009414040c0c440c05034008006215004180d07540914a9004060101b6000c000ea00c5040d4801c6005204000701d81c5002d88045840358001051540180c6940b81c0201d03010400b400034046103113480c0d4001c48210011403424032411806414101c103c840030b807003960400000390008005201d00d0f0214030011054841400c0740c808004240c5165000980c2d4080b040082031a0650140100f6042c0d0f089a24403141480c840040c0410399500c40011242c06000901ca00c0d6919240e0526550280c071001c00b4054691601448030300042046070b000804000c00381c4e41d01c000610b810703800280c02040e980380480103940d4034106410300c030350342d07207401400f0440140840c00c2502c00400507200340d03681c0740300355000300340c2602042f50300d543c0d9070060110200040182d200103241850051580048a04051140580d009a00c0401c4001180c6510200c0c40025410350a490b26400c044090582410f02704889025048080303c01c02d0306070106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 327123417 1250 327122167 327122227
    0x907032307030b0a0f0b0a0e0c120a0218010f0c081e0c01090c08120315040b0a08060a0b0111100902211f0501030b0c09150f130506 58
    0x495005400d10018104102102121030840d620300e02058414011103050b42541d10701000d074120700006008540420b04000c00300d000ea14285006445245000b40908100f8030341005407400420380764045034850f0320b900d1030050300c2d4000203400704050b000500c03815040005030229030072882d82150200000541084443e0703150010b8680d20012801c41c900301c2d90701c5034000714021040007015081511800c0c0b1400041c1161585c40e0782840d5120780179503003003c01070400c1c40020300301d9000c440b0000078524001c0c40400c6100f8a80041000d0802d00e41110090b90007030020054000414000c541101c00207203400f00f0700d4140d454510341c81d100e20704408080c680c0c5030003030310065550b4a0710002114007520100c3c501050800c00c0300c0d50702c104101d4030007280e04610011080b001030324402c060403070ba0050743c15441c41c0c1d100a40007401c2e40c4103800d0558084a1300072940070088128000d0051601da0381140340d6a000f0040005100f0702082d40b09502c652410044010500b01d0910003105042d504182c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 327124667 1250 327123417 327123443
    0x20a170a03050d060e0c0d0b090105060a0e04090b0103051b03030702060702040207060b062a0a0201051608120106030e1e07151704050303040201120515150d060609061403090703 78
    0x10b0005400c0b43c0e4072803900c10714a85d0074418940003140040144060f14035040142a41200c28404409004d1041e90340c054800d00161071124099040c0001040d00100001145a00b40e80c2d0305480c07201c02c3e04191641d03804900100e601568054039500300c120118001e500301040b07603001072140c0c8200c1800034000c40c2c011403044200800703900845514034004007099140c110203036451540d52030340d2030109203003c681071078408e00080204808060a0b01a9034603450100000701c1c01040c0b00c5034a200326004041008031b1624801e40314030483c041c008030703034002c242880d00c810010b01d002600e00c000100c080c0340c1503040e1142c410000e05981100c200f16944400b00034444019940d12009561100700d68101c6000c100030000084000d503c00c42c030076240d881400d02c1c030107030a8040702c1c41100c442100c000441c14400703030740c42c101440303409410420000c5443d1114204032032060b90040e81c00600807a220103030502ca2070b90007070b80c403841d0141000300060441c03402c59a02ca64441d45440043c2c0f0303000f08045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327125917 1250 327124667 327124687
    0x118030c030e0a0602011a0436050f01091a0609070807021e1018150207080903030d09140f030313060b1008040308012309060402090d0c03020a170a0305 67
    0x103400c00b200301d03000f008890104c0c0d9810000c0c1c045d2641c20100004504200040342083c80c0c1407141c22034801d9540200a40c141e45818041081200e41c0d00c141c046440c81c403c07074000960104155132903154500008101c618661030b0441c030700440c2107401c200007900e00c4100869034884441750303030303100f2014540bc0901c0d80fa419420703400c20030b0400941668220001c041e0007460400101d0341100301c0c40c20000c000e0700101d00381c02885d401d603c500003050750034901c6020300345d04940d0b0058102240500d40c101d140181035400685154044000c01c107503280c4442001c0244070000115058101d020320140500081070302650ba02c0b07120007080300d064141842c0b100c00901503d0350003850801400b42030b0322130600e0044809003c90030120303022030020b1018800800d04903c0141d500740c8101c0d1003d1245040d40101f420011500340052045412079424000062141e903881e080b450040c0c024406400310a00b1401480b144400a4105940c1000559150030700002d0000f18602e80c107030946001c60722400004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 327127167 1250 327125917 327125927
    0x20406180501031401060f0b032d06030606061606091b0602030301150c12030b130518060f0106020a081309050c0c1902030c121005070f09080118030c03 67
    0x80c2040c9029a003881412800e21466480745040c0c2e805403580c1d00c054000b41c41e896090f9812801786860040d141c800c10800384d030455001c0d44c1c010607113020042012001e00050300b100041c01a45510307034841c0905024203400c0c144074a40c1c0000050f64114070340f48403451092411000c1400c000c020340c2e9070b07242d14018441c1030602d210820400c01d18100302682d44000c001e40e650000c1c01119198500d0811201500703009115048000c4d41c482204185907009890540c020070003a4404c0707400036480010f60170411414810307140310308000800691500c14401c600b0f8500b44c4000c15030003010310004014044240c0000341610000e6000480aa50f1880030300003090b065140e902801ca904e0809083c06440c451603009072082101d0340080312100b40d2501c4907400c5005074104081d4268206015842a50070103000750768030180c0d441d048a0503035100303010f00c1d82251401c407518800200b2130305c01407000b036501001450042201c4070081c801c00ca01020385405c0c1d8459a80000c05005451010404240c002c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 327128417 1250 327127167 327127169
    0x421020312070f0f05070c0611010b130f06050a080601090b03030f070506060f0405071403220b0106170702073c03020307060215010b0d0b030304090209090c030103030e0d020406 78
    0x181c52244a0800100c0a40804003074007101c000300b10454000c500d00c1d44a1006c1c0c440a68011020004603840c11105407400c80421204880303075502d4180c1c03001e0503158041c503d010420300b040002091a4810700c000304a48250700040d1040c03540f290304200c010f400240060664030a50000035443c511000000e10394800c40c5241c3d07541e01000300d00700c42440b10104140b031241c2c2054905000c01b9000b0000c0100b1104100c40c1100450700c40300c4429100b0311148081c590004001d01110a61101111000441d20340303140e00b22440d040c400700521409034880200f40710080c041100411a0400050103900c841d083d0180c44c018100c0c0e10000c1c10720342c0060034200202002d8640b40a50203050400c00202d40c6810701060380a48191240051403d100080c0d65003044000400c2001c540d0a20448450560000d90b44a07001600c4a218501e690780900c0204028113a1140060f60744a044080c040245d00c0188a081c5074141803004002180c0c2202c1c00c01d1691034120341012088503540300040040c201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 327129667 1250 327128417 327128437
    0x1202161a0f06012f15010308090319051b150424020c010c08071b0306050610050316050c070f1e0821030a0f060902180301050421020f060a0207150504210203 69
    0x1a80300004103104041e80108018801901035030401d4242d201140d5142940f5100200cc1c4d511000d8007030141c940d1f44030b51940c0c204000300f012065040d650a40b8101d50883d40011019802ea40c89910b11040c1c440c44940b508020b81c005003900009800001e000032510b44c201812a44d0300241b100100181c1e20384900d10002c0c0c8003030003412192a81401e8000b444104c036030901a46042c0074041c083ea0041c2c00343c2c2d100d003841d40d4940681100401040305c1640010f101640ca034403c44001054448619019030301900c41064101c6410520b0007400c400000742c0e51110110740c01046000c45200d508469140051220100c00340e80c9450b005107a00003040c01410380c0300d0071454480c01260804c02c680040028090444d6a181d4010000040508032030040c1e80040c188983c1d8540c4454040c0c0149a032084101a40141c1c1e28000400607890705005007112200c0d039080d40081c001c0c007048508141c41c042c210f0800c2081040745495a00d05042000b448924529007500c0000924458030030011900c48442d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 327130917 1250 327129667 327129703
    0x307020a06080106020c090103080f0a020f190302060f09100b19080c0111011514061201080604060c051806391504031202161a0f06012f 60
    0x35907400000c180090138010710005006100845d100303481c103c1b0f80d440c1669003000010380b501d034031420181c0c0c0a500c441010015409140e5000070b13075510500c01849003111403100080a1469441e001f400c0540c010102640d00d1024028030410550000d054240d0408c1d2402c00036086554100159801c000a10b0f113522606040202103015000802d40401c0030310300b038a401001308102c14140c0c0c01c0e80d101c4080700c4940e0075030140030884402c1042900302460f0f000346c06d1628060040d0501003680c031090b000f00c2c80650045080c07104109042c42121645265858143c1c2068130851584e180c070f03c00d2891141c1319050200340f52521559070041400740c415400c49002411a240b1086d000d20401307611085028003031080f559110b0041007003041d00c155416a030315071590b05107041c2c042c029000031504801d80c0c51010202c200107014507509464805500d02c50f11103514100041800540c00181031504210020b61850030f4400102c4812a400c40c1103070790f43c05201c8410105901e1f1070181d5011010b0070b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 327132167 1250 327130917 327130919
    0xb1503103c0e0601020a08180d12050406020d1b1b092f03010e012c040308060405160e15091f030605030a030905041a091005120a0210110307020a 64
    0x8000d041140807034542040b008656035880e801682c9505440310003510144081001d44540300d4042d50403400810007c0c84002e0301552515909081880072090502007030000500f8040140c040107040c44916803440c1001c00c41080e002903051600030880014a2489103480c2809403244903a4070760088d00d50b90760100240349420380200c1d880e800b003d246003d45104011006200101c100849058403249038130b61160383d01e01404d1251200c0701a0f022030a80501000300c2940c03200f444500e9020b5402950351120701c1c1802d10400045a802502c00c038030707140103540d03006511307504007034100180802120303025000380400d00c001c2228458801c07c1913001017810f0b1190f14083d0f03c817050b580c00b100981c0e030130410760b510f132000e06659a207115800b401007080b0350002c01c201d240a41100c41640c0304600c00401045440d800301d2601c1405641007071000c100c00341e0602c56420104044041c0c864030100030619000d0a801003500c4600d844800406c0000a07403110101880420071525216030140c4140310f16 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 327133417 1250 327132167 327132269
    0x9010309061410180204030c0e0405010204050d030806010305090115050618040e06040c0801050906150d06050c0c210906160804031a0705190305070306030212010b150310 75
    0x103403218000c0413100d00104900400d50b6645209407070680303900c0b0200350003103030034020302400f0380400401c00c0340e0541d0200b20109541e2a131400a007940c07842a190441c15007007650024098a1006240000301d03890804841810101d206030340b422903a0650340030356034100c0e801c8903888a82440d03214982003420702880c6618181d0001d0081c2c401d5010380c401c000d60a84480d442402e0301c40582d01d990150b0310100224110022103003040301910b80052182d00c030000c140d0f0b01c40058800c1161a94006040032840c1e9035029418007501043c001050101c1091000310402e00c1076901460354841d01441c0301181c00401001303820f00c103c14080c0c00c4828607480c0d6a8901e050b101c038450401e900d555214502c008141d00724014401c0d03500700e01600d107010048072500e4200310024000140300303a08050b02c504000000d80c036400f258400d5541d054001160344001d00c0b007400780c0408041ea00000c081d000700f08102c2c0c0c002c2241d0211007a82e5081c07181014035060300c60083c9860714201040c1080707030304840c001030315 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 327134667 1250 327133417 327133441
    0x1302040815060f011106010509061f020f01110a0503150409050307050d0201180803180709061409070c1716080c01020c0f0c030706030f060801090c08060615090103090614 75
    0x458101103d00c0000d030029240119a00840e0004501351030b40420018007007031501c10030640e400305014006840e182c14500262400a6840c43c0c41005a04007010314600c0764000c0c0a40608030300c20000041c84e200c0369500c010101e1000400601e10410a0803400d440303991190040f0480503000011261501124208a620703080c0312410b20002d98609000260309018000901c03c001d9004165103086a44203000d00308241400b05c80c8200d54001e607071021a001c20765128900240c40ca21080d2021203c2803424041e0850010300030b4028040303ca5114000070740c80c6403510b001061071743c3c0441d03100c1144254501010076038a20007051b0394000308048490043c15405072610121f00021110940c0c6160b080c240c4039640582d800390141c0040d40301b8081c6038001c0d0440c410302c80c902000000c41030350300c902103801c4400c4142d00710388c0302000150400c06000104125600710500303c8044503070400c0003210701014851100110306060b01c404401003440103d50000d000442440316000759031904000c0140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 327135917 1250 327134667 327134671
    0xf0207060908131a0f070f05061e0a05060307031401020d0908270f040c020c1009150509030a030309020d021e031002031909020a0305101e1a1302040815 67
    0x41940e0320340010f005400241001c01820151131428501a0400e0f030310342c1294440300c0b00381d03400003400c0805c00006004000742c0d881501040314441841069038805000340d4005403403c10b8190411007031081d1640c010980c802201d43c0a5480b44601c90f50200a6019004504103000d03054502004e20040c409800c00401d0703e47c00c0000461640c0c0d081d28943d0300c07080003210b031150f04022441200500c0e1308050707000700103014041c0120b131068400701e0001740505c000a05110300285955600f044907440d000003003000f03070040c6e0411078200800140441d40d40c00d00070310301408064440c0040001d6440301c1c00c05100c2541c010746290080040c1032492101e901300d445543c2c0c001d1240f080e020381d031446a4400e4038040c010610522160326070350082100506a0110281e902441d100750000010f00d04119001238010000c01c081420450907251811035480c41d002d0580a07030900f072010a243d1000d004412004904680390042070184010000081c02207400c407200b10720480c0d003250000c2804c0154a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 327137167 1250 327135917 327135937
    0x70c080415090518061e090108031201060c0803040f03200d02060714030402061308030d090b180a0b150607050f010f060e070c080d0c0f0f090b09040f0207060908 71
    0x100c04155501d00713115003402c14401000020100ca0b000c60703020310700b03e403400c00c4078282081c070104182c031000002103d40310f003a0700c4900c09130700c001052a40c88601040d03042c010303c2d027802c200e0365844080d204c40009100050004080e6440c001e44401010b004610885020865044c200310051110300859958524449040b01600c502c0000410700f40c400c141c1d0760a54030b000002e030b6081d178590b070342400b030b99030800c0a01030b00d084110940840c445000700003414080d03520080200d1644071604115500c24030107441380e020f00c9480c654003c440500040c001d40c14031b0f440782601107181c1e2600313175201e0840c0c80341504a40c060340001d4000705000000448001c0400d0000003001501410006101254018400d5009016030000011800c0b0700441c001c20318140202d0341146400d280b4030505084480d2541c10401050b24440d8101c060f690040e206195203110f8200602c82d2400c1c82c0981003d4051043e180d8440c4d40c8801d031540c203140a039015a881c082d030169040c4401120b07440c02c0c9903a504282200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 327138417 1250 327137167 327137177
    0x50f0702160503070303050d1808040e06030309090f040f0b0901020c010b1f140403060204030b0106081b030a15050a080d140702010503010e0a1e020d110909060108070c080415 77
    0x86034500c1c0310812140304072400180103016080c40c42d074058500d500f044041d224a559241c0200880c0e454641005001c54461110290742d50706014071185440c4014264134002d61041c4062a000c0e06c0b14546250802c104940315030702d5945d90304d070010786040014001400c40a900f001d001024005401414070080480003d11140260390103008141082040007242900821003d4005501074803200802c2a0300409580c5025203a845000590b0320030791007214410b00400040105550094205400000341c00d49020f248642550f00c0700302d03000280200d0901c0e683c5039005000d400340d000359200141070181c14803c2c982d6403580d65a44500041103000003060040c0d1403000792000c03c2080f540320176816160141140d0800400108419000b0841b80c10681c4e60600002c03800c9a120000c15110304071240541d440744a0720540c030a43d103000c1e0030290040300c01d10101131180d8949007410fa120400786013640c03e95031208001c40b425085008050510f560004002c204001090400c11000000d5158 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 327139667 1250 327138417 327138433
    0xe0c0d051c1d0d0305121e0702032b0e10020301081501061d0d060216020a0603020405060d0221100f050603010b03070c06020903101a030a05030403060f0f050f0702 72
    0x105850200c082032820074201450204400d1500d4002c0c3c1c2e03c0d000c240246403072420020f440c91103c0741184103407000341c0890607507020103100f60300d9542c1003648640c50340302540c106040c0c00811210680300700b811000c4201610894504042c2c5c6520025100120000701d82d10301420075000c1000f540203004a08081c02000c1070b1280340540c4036101c80c12924151741c2c644506d11000d04254440c5000004543d00405a01c8140007062040c0060202003206e580003140f951707014030400c003044849900c00340a243c0144010006a541c050940b0600e256007403000da0b403010903c2840f2004c00440050000c0300e020002445210300001e8006000c0c0c07109a01d07400402c07038491007007143d180000d201c0c505110340200000350f0140d20490340d00c8800e17132240704d000d800c20440000107030500c00616580780c115503996002030110b808820802581d2041900504030140c1e46840311a2640305030301002d002e0715240c0d8480c11002c3c2d0325500140365002214420003203402c00c4919004101c000f42e170b440c401449a400c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 327140917 1250 327139667 327139723
    0x60b13020301082b0e0a0b0705030a110f0d180b07050f0c01080606040501030c020a241109030703121202040303080405241f0801050c0304150b030d030e0c0d05 70
    0x75030005078040601d0f40ca40740baa130460100d409000500c0c40541102100c0c200191007440d02c400780901c280f084014640350b14050a00900d800c10000d15907095501500d18481e885e0b038003003100401c40d005c1745856205480c007401c032060100300c664402c41c1d0300bc400291880521034003140131807000011800751100030405c00011650078a0a0752001da020343c0801c0f00700700640c06680940801091070056403903004440d2580340c02110141c41041c901c40412001040b607041500c03542c220f00d20000106800d140c20f807000303c0d9582e000360000818100f084440b0350b940c0d41c0500380e444a01a03032100b0944d940c0c3d17101e1400620911040d0b0381180c162241c41c140b60741040304c0382440c00c001c21a00c41010685d5544075284030042c285004401c0c02d40300503e01c0411201400c1c02224840d0180ca6a070f81c3e03481c00e051034107921082c800b10400304614540300c038103015649c010800b5030002c8414503022628400d240d8249050400102001e80c3c409108040e01d020402c01003045292480e10000340680652548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 327142167 1250 327140917 327140953
    0x30308070201021e090d0501050703050a061a190207090e010b010e220f0b0a030f03080f010e1911071a011a03011a160804052d0d060b1302030108 64
    0x1031007421914007904041d8003000000040d1203013007801403100d11506c0b010b0703c50a00712042600c200b000a6194810020700d4a041d025090040020600c003142c00345511520081502410407070b2100c60214078500c00000d48200104400b5004241082000d0ba61448801d13000340601036149000c10003c100000e460f142c4070311403040400d404051154440c2d90001d0000052191080e0018403e03650b0005514a4030707201840f002035031007110611005112400d01074840c00c0c00400450741480d6400052040a040c3d05903590490401004050b8505c020314103600544403260901807201d4005c112082030007030a462200404204046800c2c4590b200d44000c2c1c50310104480d00340380098200010002c1d84510910120700c0364204402a00b0304a056041d030445241f0548250388018011a0034403a034601130000c820394404800701e9103440100780d052000c000c500c44030f02c2449194010b0250080c0482070b0003190324400c0040000e0041044460700c40000e4100303020381c8105100e80c0c490030f080c9418107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 327143417 1250 327142167 327142177
    0x1416030b30010f02040315110901021905070e0f0f01060302090a0b070c05090702060a0f27050f010e0109050c0d0c0b030c04050a14030f01060b1b07180603030807020102 74
    0xc0700241d2125080800714825001c41495034641543d07070f41c41004129616840540040c6105070000b072100d560081540055511010725460805000c2144d407100340e80019103030042e030009050048a054403401c00e103007400c009070f020036001402d040030007840480040303a85100d0107403610b81a1069880700d8084089001303038840680c005000c00e6091002006c13000180c0031803445420b085401c0c5840d18007003444028241c440c1005139010340e0500c00307400000c0c01000d0500045c42c00c100704402103a00d000641803014904c07100f072204103c40720003d010081c0401c80070311020a000703014032480700c84142c0c02054601c0054a07140a0f003001c50702035140021400360015000000345d00914100740e00b044290b400a4844a001c071070800000405484981c0710000804104100c814007804850526003000075031000d041c3d45925004041c424803030034406544905001d44c0c46000282c0a01c040c042c034042054000c26082c107181c0000d40c402c846942c111106591099442140744e0301c608100360300b82d000d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 327144667 1250 327143417 327143449
    0x90d020a030918060308040b0304051b1008070302070b01062a0c0b09060403060f020d050f19180b100812030c16020112020a0e0f0a06050904050403031416030b 70
    0x61181d08005030b403a0f516191031010100040003031180d950b0750b107036400b950183e4401080350700040200700c280a0b081c40005103141200e0300c0c00071201c1c10840002d02c098070300c1c5e55880a01450202183c940382c840d5060300c0d086c1e03038019034010055031180400b030041c4043c00100070400e0703005e800354038158801946000ca80b6a0080c8402449803c0c244684c100d40c11039080d60b070700007200344000004940716000301c00407084642401070755501f6203483c100a8540040000d068060503105201456020300784c40084042da00c44005410406480107001480c000718015088130050800d110350901c42d40070403822240510101c42c44083d02c0038000f1441d00003121140d01452003802030066910040c0b0038503101900c145132828142d03030b04001c010b040b6004041044001015001c2410240c00c02100d0078038840030850300d41100d03d2510310000d18a1140039001030044e41c40b00e0104007090f0194002d4151605030004640741803615404c586010394521140a000030300b844406881c0d030070599032038030700c0c400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 327145917 1250 327144667 327144677
    0x60e0108040605130b0a05101a030402090a0e120415020607170408120f0601030c0809190f050706020a0b0f0c0702040c111b0a050312033c090d020a03 66
    0x207181d4a8880042c039005000303500c4140c5418020001400359031900344107103040c0b1000a018201100111601c40c0315400c040403101c3c03c00008418012550241d907840340d41150780400d540c0e91900e00c40090220051300003802d100301402e00d004902c82d0310107071060b00c0750110072500c900c100c0c040c1280ea0303130401d88041c0c1c0070400303200701804030342c0d4880c0b0500d1b0320034014242c192524099440c1c51440e0a0121402950766100409001c01582d00d40500d0022418520749a10f9a00b4032980740c03602c90b801100c05890840c90903900e2001c0104003a038101074a50007105540b03102d9503072a000780d140c2d90f2821049408005000000f44494440c4442a004101840c43c0506101003a82400010314002e40600300740055400c01d000042010440b0301c0e4001506c0302c0301c1316444a13002c140319200000e80c110302d2180d08580c609045503c0420702b901e50158050400e9820140102618280102d12000380e070354041c20a18514594100500d0031030281c0311100807107007000c07201035049031900b41c4903134001c001138 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 327147167 1250 327145917 327145921
    0x307180e100b0f0d0807020613150f02030406050a090f0e10080106030b1602161e060302120a020f31080c0f040b0102010b1f1808280b0916060e0108 65
    0x8141110411402e905c00c410407850400d15400082c0c440d0490803504448030700700d840034488401c003028006198006410300714005200c480001e0f407280034901402c0c00704070303000c1a00403296110b1858407008100c59048901d420352181c00d000c00031801120071000943c5103020020b00a28144500001c40c0e0300002d440010352036900790403038420505e0751200d04505c54042c0f285210b0391102e214030000c194518880c480c0440c1000e1074680140264042400d140c4144207000a066400d5242a8010030080c0f0059403070317980f26072010450042200590003007002219001c031005415000c500d141c46c810000042113070340d9140407960340031f001c42e03440c0e000700604000303076460306194000b04c404100500002c590030703080401080416035001103200348810002c1d48811450303040a03030f00f001c2c5945c000c007000c4041d080c1004640c2c1c5a030120808030305082e2149808100c91114054180b4150703000506c2c00c1c0b40e017000e40b5919074400e0140095038419154140000b009809210b20501c482c05c180c5a2140e1a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 327148417 1250 327147167 327147169
    0xf03050d030b0d060f09051207020d0807050109080309070f17031b010e15150103060518040c0e070314010608131104060806071206060801030314090307180e100b0f 72
    0x5010100b85071070f0400100e010000c0080c02e640226100021081000103e0480c0740c00c02500d42036083d075007902069030420900d009625a0744805c00413580024070550758170218508540103001650f80909451400300500001420208072541114540e07001c4401181d00c9040c441003585d036801d80e40301d80d0b81c0308228482229001c80400c070003c15440b8000620100e907188400e08013a0700b10004003401554404103c1034030030086456490300400e180400c051800e043c00700c0c0c0300d10012241441e60341c0c981400501048409060100039207941408000380742042d40014001d0509020380e8804641604c2c0080340052162860380d21030f13411413140005080003034540f00301c50380c2c5c070407407454216494200100b8114030802c560f03401180c00765a5545070441100300b1400700c034100d070002c82c20011280d004101013644030280d902104044241c26076585420b80000e86400301c10b83c068200090484021810045940c1c422200f010102d81612040c07030703030901000126441900c1131a40005150030a100b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 327149667 1250 327148417 327148421
    0x120405010309060e011b120b09190e0a0b010509150a15090b0a0512010e0c0901050a02011401060801080708070302100302070215040323010c0c02090709052106010f03050d03 76
    0xe65004200001d0b444c102c5074901406e48065142412042c2c84003450241e1b4183e1240e6840b0411104034420086803201d08000383d00d1020207008503031400314040c80d4014800295001343e20f030410070000c5a080286520b4aa04940004d01c00d00e0310030314448002036040c000350880415003850003860520081d003441000207a140e00202d608040000b401c1c1e010540c0d140c000c00521a460460701d80588810305240242402c0c23805801604070603281c4014031441c585d0710400e84515144c00d0911300d80303821b5050390480c01000d01c010121884800800001a0700d40c01c400d001381a9080702007501c0b8070603120131800da07131280039100c000e400c004403038803c0030403901c42e03800741582d14401003248500c18009440e41300a03802541040e901142e42440317001c8503000420761000c00500c20b0303000b404101d000d2400642000701039407000e07029002d40000652080d1140b1411000f4000017421803582121180001480903400c00c2d1a0f1180e1082c2d400210316440780b42e03541c000322a84400200b400c0c0d0503c01d41100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 327150917 1250 327149667 327149681
    0x2015011a090a06050c070902030a020c0708031c0b0f0303030a1b020a05120d200d0f060e060d0606120c030b2a0a031b020a030905040b0604061d0904120207081204050103 74
    0x160b54041d860300400c7c400c0013800114050b00c0911005a22070070303901c0c41c0500f018110750160409070310400c80f00c110341d03c208034503a0322600860400600e03404030f4030100d81c0f410402c4500307580c1070000208004008900780e0108007005000058400d01007283c100aa03611140114060a154001c000408070444010b00816551030a4103022410b6442c58010f40503074496054801c04400c0041a054998071841c802c154642c0c8030500140601da10b045a4007040d220302410540c040c0c6012119841030268a4100b50010300302c40301c0318012200700c0c0c2010101001c0500048030b900f40140302241001d80402107140d040d6000046d40c0c0400c0e0441c2e032200d0901d80c0000e01180900d5143c0220180060340740c4002240261582c0250814581d20700d4010301d0b00c0c0391600108d102d035242001441f0191180415139003501c15a017082551f8845c00e500c450700200110840315400784c9200104070400180b091541045050341d0201d03100a078507130100d59100d5140b112101c65904090100f04034662181e04208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 327152167 1250 327150917 327150937
    0xa210603020301110406081b0301120c0510033206091005130f1b05090f010909051e07080910090f0203100509070b090901062015011a090a0605 63
    0x101a596580031a00707460601214a40b142c0000c03d003040020b130090720b20b56002d0f0f008280c5040004004400604070b00060041c0c580f070042c2180680c0400c0400c02541c3d018060081407808030303a4440c2c1001b0084c01d145004602e8000784096044050714103a00340108400100003901410380e181c1050094445008004904ac60070000e0005526100c0d000b804c14456400000446c40d1540090800191000c2e80f404032040c0f4020001802140e0f07014040e14094241110006c50041010b03004032403100c12508520102ca24003024458045803030f02030f080c01c0c0c50102070701d0200c0b035442c880285d6a07240216825000354100b6541640c0701c6420742e1080740080e1094410000050082e00801e18001c402c6005202060b664403d0102d0444108551401018041c040b00e10b4480140040b8012840c1803082d102400701c0001242c0003109030702da0f140820404070381243c0a0300801500640341c0f5030300380304240708010744c0300100d45c0c949003c0742122186403002c1c01c0d040d40c0078a402c004554980c0800d400c0c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 327153417 1250 327152167 327152171
    0xe04021314031011030711150106050d0204171e060c0301120f080307020a02031b01020a120507080703080a0c0305041a06010509040c020a050f060103030207140f10020604060e030a21 80
    0x940c0c07940b107407441421401c94507200d04640300d25000402811041f4a1058402184d2201c031091032076034801549141568039030f14005454020920160b400384c0901c0d0072001110201c41803004142d5000220ba0304c2174181d0313800714a10106103219143c0c440c0d9081e1a850405070040005021580000f2550940c0782d1051030325121414458031040d21365081034030424016040421740609503c0e04111b6040005000040c0d8041031703c038800041d42d07a49106900500003503001c0d01c80f46100d800350041e900410f4002000656030b09461a00420090b002c0b11f54022245c0307010326034903509100780710742841150b00c0100031405912001805641490003800c1c6030402c081082010300d603407514001c500100055400030a580001c40c038080381020b40e600c440c998150300600041010039400600181114001c00046102140b1140800c1c40e08150711140b94000a100e401c0440140d40000c2e0584204e0241904200050540e403219440748540107035100051900c20100d42c42e0a001c0700c00c81a000700071000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 327154667 1250 327153417 327153433
    0x60f0212040902091201020a0f0e0d0206031303120b0d020d02040f020f0702150a0203040e090a02041d010f060b18010903020d0b0105100f0206012d150e0402131403 72
    0x251454a0380942c00c10300e419500469408914104002030940408001009501700f44600000a1070f0503440c0c41e030101040342d02c214000ca0b588400300d00c02256500502000e560340340030f500e51031202c0d80841d42140002d2b040c0c0820170100d001031181d42d200b190000d140804c10b5141e130302003166108c0082c02c1a41d0180d47c521868092003080d1008105038181000000c4c0c48040c40c1c0100f10402032425407040e0480802c0040d420440e80c00b008403002d54071003410400e90b07900d4004c4818503103002908001c0d0050310306402c00002011255998404015090003800800c0610091a003629103078400c40c214950288464002d409100180d0840b400e81032500c000b000341c0c0c03034000030404000008259091558040140898100303844a510100c550342449008822607100c025907502e014441c03614500000702c404c0307800c0d0350110340d000440702d40f43c0c81190301d031a25030f2100d201212303104480d00082140c1b202c007401e15003482c0c0242d540810b1507001510b0780340d19043c00703900480d5194070659494060018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 327155917 1250 327154667 327154693
    0x503090f0109030e130b0904020409030219060203040c15080c03071b0b1e0c070b0a0209060c0d020c12060a0507090f030804030309090905030d09021c05060f180601060f02 75
    0x41618900c60180e41c4102e440181602032040f40707209810020f052509000d81c2c1506c0d91501080c41e900140c0c1a60000f41ca07011906040f800c01c4035a454015800e401e1041e49c4040c055290059401140107001d80000c65030785034821803002e881c90038120041041c0c1000a40d600544102455100e15607080c0158186140f03121018601d041c1c3c0012204542b040303050007815172001c20328000700c0c0b2a01000303450324100014030891a0041410040034161640001681425140c05a986082c4003074000341d114011561215100d110f0080790f00010f200322005d84407189000303c00c0d07a04002c011fa014102540300c00b050030700980401007401041c13180840700003514081c0503a000000754011010300ea2071b00d007035140040074130b0713866844008464280690000807610100803241c4901c3c0d066000a06a803d078408641e2034200948100d1610034601e00b841d0034000c022900c54801c2c803422603100f0030341da54490354406c000e40c081400c00c1c06900a200500190b030003000600e80540c400c2c01182c2e44415801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 327157167 1250 327155917 327155921
    0x109150303020d0f1e0801080105010501020a05070e07020a020627031f0b030c0a230a061403070c1209180e07210c1203030e062a041502010c0206010f080d0503090f01 73
    0x358040000480000041180d4480ae100c0d807400340c4000d00c0036040710401c58542c595200d92900580000e980c0c8180480c107034074020070a420925a001d03100c03e440f42c0580c054070851039034004410303051061a42c045e4500b0303d000300d6048480740c14030f04490740d1080030781040300c01801103d40c01a014420b6080d5091566200c10810b401070461801000c0004900400d1a01051040144500410703511f00280410740d0080308180d40c1c04da00e00752686c0c83e541c4003e8100d40810402070003030306a0346050000e100143d4040d069000fa07170310501c40042e00c085401005400c0b68800c04104005400200050102280700c0351a12032640d8001070b6800542c145481c0c00320501910350100c01d03a070104001100070990107001d802111103070a0050146440c007a0b0703d08104a0b8841810840180713403480245003401d442058a0161140c030b08804840c007074000c0040d00810700141c4940142c03098038000103038254030803080c0c1c0541c0c0401002d03000711004c0190940300e0382c00103000f001c103d0040c9440282485424 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 327158273 1106 327157167 327157217
    0x60907061e050307020c040f270b0115120f051006031a04021b0604112404050d0c05100906030f1418120f030109150303020d0f 56
    0x40c14202c6c05d25a040c030700301ea486403400b10140c01c5c12045910552604205140c040a00116980c040c0e018414181e8014000c100b54401440150038283e00c8450300c2aa45c181001d10440c200038100584482c3d20744034107680d07911310030071000342078282c06880180741c0c80c141008840c81d42003107000e02c541c0313101d50304e80a543c0000302c2080c11302030004915512001c2c00305441650902e03282c0401d014032242c40040c07260030340d50060f81c0105054400c0c2c00c007181c001c000c02440c0c2450f0009016200800203030540d500d64095074005080c0d02c072081070381c1401490369150342e1058104000981110554564101200d20304010f1540100004016613000340703180203100340248a484c41c49203031100c104d48a8010504c04109803400c2c4580d1009981651003903d418014801c4e5051041203542e0f80b4400580140c1c02058682042da018a0b40c00c50f11687c1072500281001c02ca030405000006030b = true := by decide +kernel

theorem cover : BRFrame.Cov 326978417 327158273 := by
  have h0 := BRFrame.cov_init 326978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326978417 ≤ n) (h2 : n < 327158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
