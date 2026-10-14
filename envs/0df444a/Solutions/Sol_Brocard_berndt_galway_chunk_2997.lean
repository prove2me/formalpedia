-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2997
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:21:40.773407+00:00
-- url     : https://prove2.me/submissions/0df8392b-6d9c-4e13-9782-5608642f3700

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 538848920 ≤ n < 539028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 538850170 1250 538848920 538848923
    0x6090409201002070b07060f09150e0313030213150e010915030b040308090a080412052104150c060f0218101b0c0504050a02040609091b030209120a 65
    0x155070181180078140140c65841d1440b9102d04003203120000e6011034108111103050365001d40300d550310329091340075001c0107421100d024a45517086041c13008450340c8040712440d200003084600781d040501c83e120f22940c0444840b01d12006810401414503143e03001004209c82000100510452504048007565038480d070004090078006000b880c00c14030031015841400c0f103416044910319516142d84072401480541400213080000d0440c903818062200d40d6030b4043c06490383c2e5903c0f03110124200c005a04141d41600c54102c0201040804e04800f42c0c02e000c580c03002e24202881e240001c40c00e035400c3c882c0c2c442045000d2940000150050050503400c00b070450b00507072034003100e24030800c502442c165601e1007100400e10114665402809030381c03000400c40c0024500030b0460605250b0309a40d640074a80151034113081011549555016005070707401030740e510765a5070340c0380042c00517982c41e100900c8240c1380162a0b4492240030341d0050000060142403441b80c1d003060540613091110b052030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 538851420 1250 538850170 538850183
    0x1e05280c06020f120403030f030b041d0d0e0a03020d061d060c04030b070807210e0a0b070e090c030f0a091b0509010b040f0b0a05090604060915111b06090409 69
    0xc04003141c004c0c8500c61a02500c490020b003407616503140203120010122002082c1a0341d400904120b484d80c0d0071400c0c00c80600000d0340360403030040d070f04540d881e07010f0312200000503100351216110385803103c00141100d40040c003868242d111926640c6c010460b0001d414002108004103038182441408107078854503401343c8554075145982410ba10100d030040052040104510400448580088034044200b142c40c0e005040d143d407420304000181120248203040d0312800c4030300390401058440d414420003203135031500307801442c080a0184000302541e03220104030080c000504203030034140a5030342c090110b03207003c2603d410b0760305c4050b1441082400403e6100303540c40d0600550600c40131103801080445a551703d0107240985061a588460140c2c4d00700d42d0303000900c40c0450f807141c01968401c1c4002080559201c5e911200030703004120600c10380140c20841800140140d000d0342ca500852010240036043c01d01050240c4003010719600c080313744c02142404052100d4442e44100300c5600d02c940c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 538852670 1250 538851420 538851433
    0x42009060c0a020d0503030108011a011d0406090f06080d03050403120b010903020d05030c06010b09010509040f06090203010e0702010e030307080103230111090301061202010c0807171201031e05280c0602 89
    0x100c0c9c035007910122015000451f8041400b032440e079a00c0036800003105406500103020f10000e00001d805480c89a0050700460b08018010b2801c4401d42d010000312040a001c44080c5640e0000a80655800f200c000d400304200c038a03519040403464001d070915a41c149401c1c500d031510f9034001004115119029a8150310200b40d8045110040107030b9070240c00b8050740542047c2107540004c00511508102e5409252640d040c1e140380c8425400c10005440d0340c000941d165a116235810030960b01c222200c2d40158245404a111505c0c0801200d0051000b83e42d0700c1d40aa0030350b12000b0220800240d44192040c503140c0c103401ca14800c1c0708042c0d6900d03035441c5080d51983d80c20300f00b60030750300160800c60308101554040d00040c0e810641c00590a540040510340305d18003410000c0c04441003c000c08c00003180010b4202e9910344102d4028140c03485031801c0c2d0f00e0505032140050b800d540c01e001c020004ea1100c0b090358500c07114400341d1404182810200d07800c02032541e40314489405154005005640b00c01e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 538853920 1250 538852670 538852679
    0x130c03060f050601030b031e010605030706170f07050d1a04050a06080c19171c0203041a03130201050d1806050906060d03020303070807050c0a03080402042009060c0a020d05030301 79
    0x34080c058010710240780c140100759403500001c0d25025110910082c6803010131584140440132b40180c001000300506565103c0c2e03035080c1c05049964121036041c224406040000c2844001010712401b4201a65405051100c2c505218004002c0c01140c030000c0400601f240301b280c2e81e140142c5100d28445000031407002c0c58191414540800080001d109903418040e5689640b001618001141d8089841c0c41da47e01d6910324103030030483d1146c0341c50343c1000c03810361a011841c0c0001c000c1c821107020384a61041c0003440320118103240000c1e0f80c940071030b46d2082190005907108030060f040711500d0031000180140c04c0042e1001046010744111009a180e608200007204280600d690041060300c0b61603010616680082d240e1000401b620706009450b40803641d414414000c1c0e401001070303c002c48150030501c0c10082d154840c00c440481c4201c1c240582c42443c1f100034203c4030b0952805062072420401464200030b510f401810308141e1910030b06907220050b0f0b561142e00c03409540504081c42d640d5050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 538855170 1250 538853920 538853951
    0x807020d0f0c05030c120303220b2805090a12180806010509070e0102192121020f070201082a030103060e0a020f120a080a020d03060911030708130c0306 67
    0x840c0e104610501c84404014041b00d404030840364050a0000c0b1052000d050b4100440a07601c4024050014903100080000240b040120040b06151354940c4842c0310b0b103000b010101390b41d800c40d806103850b006007580000040170030000c110561010705082c02c0019007d2407201001100390700c10a003079030002c0010071040c00c10100c1d45410100e94600014000e08050011f50b0301c441c40f003c1401c006041d41c00d0309041c003a8807051004602c0e80c0c01c42212684107a104014568243e06a40c81c80182810b15400034218039131003101c40c0c2c581034100690400206400544003c40c00400703451101d88541014003d01c0078400ba1070105201c10480c40b0340b29410f508002d012200301c4e80070300c2080e5001c4036410740582e40300e0350480300c2048201c603165243c94040700dc0078203080600b40024501280400c42c032004c07a80224100c05c041c1559641008003d503203141c10001d030360960300304091034081040401c01f0680319480c40c81d40910b9030504c0c04084079641d5180c915104c4564025200b6950b00d000c0036030001c54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 538856420 1250 538855170 538855183
    0x209010314060a0b0c0c1806120c0901061101060f06020601230303040506031e01060201050105030d0305100e07050f0f120c1e030703060503070b03070807050f070807020d0f0c0503 79
    0x16641294468540080031541140080c010b6120344e01c00410060782180040000390b0040d400a004240400143e5010890f0550243c550511604404031045501f0b000010078800040d0010000700440e444c4c044280c46585200e01100da843d526500e003c2540d03034070b04218070b0045c400c0d035000b06810361500380010f051030003000100c020750f8920000c81d00c25603070000070381c0c098030b03001c580d030550301c0c0c81c0e14011a442045400d07483c103042c54428000100e1907010750001d4101c8d2307001c3e81560403a1852103021422603000301c0d01c00a0740070701020188003030031208601c107900c221941002c0d03150401e1844042c4540d0808005030903400e1b1f00050f40c11001070b138625195084036003540702e81d040c14000c2943c0c0001844035949003c49100100000c1c8a59100750003580003400c0c09400d56441365150200da80d116070007190407401080203080403070429072150040f695443c0b11781d80028140402d560303441c140396001207402e07039008581c001301401240170701d030719050007038403a402000780c00c2d2a0209050030b003023 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 538857670 1250 538856420 538856441
    0x7060809030a020a06020a0504120606030b01081609050702070f140f0105040501050a080403120c030e010b100804030f120e0619020307051204020d0606080313050307030f06020714060a02090103 85
    0x10810b2021056040e0000b46002c032071a800030025032501e840341002c0f280c03401142e010003c0d400114102005010895000c4410303680103030142280d9a8a80342c5240da604444042d003204020300c924108a00c026a81c00143c100040b4170603151001c0c0e4801424562040c1504680c80c2804c81c00300c0c1d00780e2480c165000350f20004007824842d0500b031a00f070001c2d15074090380502c1801d0001d910001410507108041c0c03040e400440280030070044021100c024010030315101801001d6180240c0038890386007649814110174015512401555a641da080b606a1030916040e800d00207009001546662540507851140d40d50000804062078515036140c40d040e1100310482400740f0400c24016081e6101044450000c206c1919101d603442c1c61011440c081040600580200e01d021408501d0410200003401400403500750074941a13100c00c2010744548445c0700040501040010b08030005200c2d4020b0b140843c09540d680d007818088841d103a051420895444000ea0b0340014000000c0d80c046c441c90907030300d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 538858920 1250 538857670 538857673
    0x3080c15060f010c23100b1804020604050d0302031201030308060310050c0a030b03101a12010e030702010c030e090f1006020102030f07230d0203011a07020d031d0d0507060809 77
    0xda400c82c0000c0c2400c000e030100074101a0f07412810246080185458084450500c4101c9502042e01c0000400400ca1441503c2c8070b01c000e0918110046500c07060715004580007089945020729003020007020a02c03c010407810740c0024841d22013030b00d1031050388500a500a0700c80d8075040c98240d0070182040080d081c031b0184a80740001b8094295280340a40796642541d0030009101d90028000070b00d002d80180c0c00580309418806401e401101100c0040c80540040c1da0303030403801c1c1c90ba0300f95509035403070214212501e0b40107100d1240950701c00d920b0225040e001c0d00700403d1045100010403074421080700c00001e15250754090050010071074030608000c14403032000318110b0400700506828660090080800c2142d0340c0d5803655803110700307181c9803d6003070220f1580d03594803003800107100031390424805e0911405159440e800d28411402c221000154000c000d20010001c80d60701f96285002c3d486007061035058a00b001c9200d841d8621075010803400340c401072211a1400710014a580402421400d80c2d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 538860170 1250 538858920 538858939
    0xf0c031109060d032c090a0b030f0a1707020a0314010b0114070b0118061d06030c0406060f080405162d0b0703032318060705211003080c1506 62
    0x8240c0c045203804032a564091300c002400102c0c1c00400c100c18400000d86da001d02a1003c1c0240e0110740d5001140103481a0b0030b98415915503a149601c0d9201018090281d0700302c107540c01c80b1300300200d004290350b9200611000d0126102d44400d034159400c400789a80301e039529641c100c415a00301c6213941094541d466224500b13a030b241d030707000c007420810310401807032005c034440398030b0807610300c0c0c12813805050080c14004400c0042c100c054220f140548070391303009006003444040315003000c0c00b443c4155a00c548582d552000d045108644030600100241c403603000306120410603400b000e9440000784902c034081d2419090b00c0895000312140408818040b450000b010071540c2c050b142a168000c1d01420002150030b640d15500303011480b0b01c200180c203c4500000c000100d4040440c04108591403401c03154250349010b0165040d02c141405110541c00044500b80c40a0204899951054980b2400c41c9407a90302e0b9140e440c9034215203481d0340244c00c0200040044400c058040b40e005000712004141d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 538861420 1250 538860170 538860173
    0x60d1b081b07061107080a0f0f020d090b03040533132105070b0f010305160506040512071214122104020103090b0109061e0b160f0c031109060d 63
    0xa080c89214001803c1d00e440340c1c6500c21812100080c2c41020750004203040d070714198000000c014024210120010038158084200d06900c00035003c14400000c0d201e00f084c80341407004c1c61100b83c0004104440b9407240c1c5c105924011400380c04902c04c0d4002c16007106511408030f1581c40380300b00040550004400824800300807900c2c1c62010300b28000c40304500400d002c00c0c0c17401116148a001c00c00381030f001d1880240294001f119440c01d0480c1d018500f50f0300750f0f60380c0505400f00c402043c031900d90b1001d0140018070a44c50150f003100a00070350201207a410a03950b0445140035411035406840255001a441031002800e002101c0d0f12080100c50504d4114156840500c0c203021600848506034044002021039010b54014000c0a8000b5a1104150f0b500e41c50400600541d000e03500190105624481803407001414003419600032801540c203061a0340c0750ba42e01a4a180015074410755084101408504480c0c400c0c1c029500a4041801042248083c810000c0c070142c5080d0284104111090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 538862670 1250 538861420 538861471
    0x70b0103060513140102131415031b03090309040c0c02090f27030304031e08130611030f150a0b0306060c031303061b0e0d12120c09031101051215060d1b08 68
    0x134100000c9c80301040d1240c6500c184500e00301c1e101a90b00c48100400424403021240010140207194400c03202400781c42c100c0003003203803070310b0700d000000390020448400b268507807040500040d0320034001c0881207941218191030301b03240600e101c04040f080e00000203000c00d144e4401418221000d40341c60440d120a4a01d40c01080000010310b12034000c159101c40108024003074100340710305180d01c03103980c1d161700f0000d420004081c400d481c082540d159145d0b0501c698101104100111001c502140e821980c030302c401d1250640c001c0035044443e00040100c0c10755580d52601c02c10265000d000c0008800c505103058054402c80b080d94541401300d0b9400011441d512074041d42280c907480414408001c000c20300c107842d1030300c00300101070205060910442280c1d90201d00703101201e00558604020b14000c03001907401d80b20f4440310707502c44000b0000203003079118807100c1070781c1845028140c40c2c9803040c14091a022503444184001c0800d8588125280f49680000c19940080707940e030b1680c0d06d10300c0004854 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 538863920 1250 538862670 538862689
    0x50901120305031f05040207050105270304060e0f0d210302120105010e03101806180317090f0d1d0306060604060c050c0405040c030507060302070b01030605131401021314 75
    0x140c60a10248946009015013080c080c0e0003014042c209548074851840e14601134031003100d200c01d803076280500c21126240c042a000c040700c03440c14007031464a41003039401c984030101800316980000c10134032118504c1d101c2214820905004007000c0044602001c0c0c83d161890b07090072002c04050040c01024000b06010707c190b41150001d003031039102916a40c010a00701320030170280c420340c41e01e00100503014620342d0410700440c40c03085504100c10300c007407151b41e0b0a6440c80c2c44d0103800070310610154242c080750380d070410380c00028a60481b00c203416500941480d00c51591401c1d000501c0720540c2d00030648810040ca0301c0d2003c110f0203403100303161041c080b8401b80503c0c4030316020020a062500188035007404803140200011f002440140703024284000404564070040350740703218846000903607921901c25541c070681e12409640c2c6603480c603140c00d405004007401c14503000903428003170070000300a0502003880711048400961100300401445005002c2d503442a0709020541701180420358924100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 538865170 1250 538863920 538863931
    0xb0c04080f0c100e04140a06090617060604020c07090603110907030c12050a11131a0703230d140a0c0f050f030711030f03010305190f0201030b0616030905090112030503 74
    0x504c2c2c2180072000001d01a2090041600c80c07100035405000541d8442e03003000081c3d1395061000c0c0191076030fa19030902c480c0c0c0040080c0e2a16005817000c1112450190002e09030f0389220800c0724a001d8564600c0e80072200c00794812182c2d007081c05100f030300c0d508010320203e43c400440e0070b00700129000c030140078043c040c603407803420440743c1d8030400602c0d000b036107511500c0d0640702e000a82c3c3d100c1002c0c0404402c5501140207514408812607239010000d0007020403150241c0d8980e59540300510b6158910000c00c1d000707100b405c0340d0319040c8220040780e02c0300d00c00d6500c00d50511100b0303a40790800c18403040445000404120800150440e00d04140d5002000c80c4c44400303041607401d0b0f881c0d803854022100c241f20303040c0d2402c00f4040090038501c0c1e079608401650582c0c0c0503505a03005490442d401da644800300c40c20007044951f0041d010805503000358400c0c082780030085c4c40e551400282032096030b201001180100c0100308105002d0006083c2a00024003420f400d0160602881d0706440140c1540002440d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 538866420 1250 538865170 538865177
    0x3030307120e1b1905100c060603020d1a07080705180f0603070c110415170a0803160e1017040f0c03080307032d020a0306030b0c04080f0c10 62
    0x1d268441460303981c0100c0c2114640d4081d41ea03402c11000741c070f00d07103c10b010210074441c1c2d50a40704550804528000c090071100010f1003414002c00c207880c140c030100e01110040d070b8815510000000036031101e404128555104444a07d0481c001407009110a0009003400007042058130030410fa845e0003000712940312a440381510100c0308140c0c0014402620200360030340020020082c09211900714501d806074034400d10000000b501e15005003c04c981850001d041c1b0309200c4101000340c042c1d02c2d40414002142c01080e59543c40c0c2c26101d0a04a5109aa03079400024106218500030f50f40154445038078001211210b00e0440c144800404c03250300c00d015843c0260b03540000c202080aa4903640102561101145240f2aa6400d01c0364054000301c68070004a42402c0d8070070381c8500110750b084580303d030f007400111100d1540a1950002d4001807224424595210360100229111080342d9128102058045036200d05266415040400c90f840851a0f40e002d1651030791195200c688002c014030f80ca24 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 538867670 1250 538866420 538866437
    0x5010c110d12020d0207050f070801140703091e030e0f0406030c0e060123030402011b0f0605060a12081801090b03062e02010506010e0a0602030f0a030b06040801230603030307 77
    0x60b6420080c841d025401801c0c80c40003400c2c600b0003002152000650110000b40c40b8403982e5071103014243c9e00e01c0d04101d035480a0803000502e02600036807040700d4682c003c13009030180600802c004c01c0840b480c4001540411240c0030700d10b400e0310303040340040d01d5502c0540b01402032030f10310340d150340c0700c0c05d02401803201125030040064500e03442900806230100d9a840071070203405419610920342d41c801d54050380000c0c20b559440f0003201d500560160056030007903003203104510b0740c2c4500c1c0052501508880d40325100740303000944000032001044085010344480c42d603d11101340d14504a00c2e08866080c107014003610200101105581600c1d808402613400d45204280000d0604103032121074100c0114422680e00207500316815400540300b07000a89600e50407104d582c0070040d900c00c0034070642006a1041081541402c2c07150060100c24005041c0032408108540001d00280c104c2e81180a5981d59030506901e0030780459650189500c1e50301c0e448a850030310b40046512840010406014401c401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 538868920 1250 538867670 538867697
    0x3080901030908030c070b0a020405090a090203010b0310060801050703061505030402030102120a0e0d0e0a210210120501090c09030f021305010b070506181c03020c0106060c05010c110d 81
    0x82d000341e82c29950000c0000e55900e010555460030382c000f038409441d8000c00b500040c1c10104c0074070071101940c2c4002d103020220f0361052102d1014204860040386c15540303c150004003030f03c0800c20b0350360b40c030b101c0300c0c0100e2038500f000401c9084640003000c1d00109810314408100c00306810803050090b101924060742d40f83e1b941d0002ca030180c0b20300b24501441060040810031981c0266004004201040096802d2101e956034112503002000005a03408100e8000c02c0001b03180508020b00110410500b50b9014171494001402842041e054480030132422a070400001c0542e104050240c08409000c1000c0c2144990013006031a20b804000c5c02403407068000410740d82c0700e500358441c07104048803d10581d80c441030002a960001c2804031410310440001c540d085482029000d01850740c02d000700610400e42e1094140000010f0641c010300d5420070100c8103d034030a0003a00003401594850302c2c5580c0301490300d10308558001942c4020400190a0100c170007070042600c0e03032041c00c107280c013090040c04c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 538870170 1250 538868920 538868927
    0x507140703030f300b040f0903140a0c0524070801060c03200706030e011d030904020a2a1110120e03360915010305040f0b04110a060f02060103080901 66
    0xd006a08030b1300250007014801018858201d1400000281c800384031017000d80ea003c070709a8800290040201c1c0c0008500304c8694000b0001e000078409500c2c1c11640d14003203031515810b01c2038041c0d8829a108061402c844d80903103008001d40c00501a281140b015032500710002c10131035500400408020b9001c105000100e008128041600703546010784443c540e13240c0019009000340c8000001d80c0d42030070000c0e90030743c1142491246106021010f980742030310350b4040000030f61144500c101400319101005005410300c0e181180509034885281e11055458202090101c3c206100e151156070364440205105500010407a24107000e44400308082c02e40091a50642c081c40d4500c490806040001000c64180110b0750740143c8510118000c1720100a030034003144603411140d00b003143c910329050412039442503000e070341c0c031074000d20328a000b014659803800c42124099038151010018520307188100d14201c4061030003005142002741c56480c0d0000d01944900c0e0502c4003424210f40816600c4c1507900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 538871420 1250 538870170 538870217
    0x70c08060a05040506011203120f090b09030c15060d0b060a080a0302011b0216030f030509041812020601050a05091b0309160b18060904060e01060507140703030f 71
    0x2501019140d00e46000105200203082c11502520248914800000e1408040c0148803409400da038402401c0340c06209840003a0640d07102144000b070740ca0182002090600360170070300170000b000107540d41c1d41001006902e40399020f0180c0c0b10382c40b00d5805106407941d03410002400e480c0e01056822003565807100051040f0000c0d40050454012000640304065065010b000c807042c00c0e080410510304944070499070341f04141030f182000b10400e00d05002180d03482e404003410505c030b8585075140070762041c0401d0580d4841c40052001d46038441c14501003100000c8568410441031008242d950b140600042c1031030040e21440340590b841c60045820b8091060600303140b0f600d101e800b03a0b920b0415100140d81d40504413040800007200820100c0c4007a43c1000300e0f6400d900ea82c1c01c4000380e8070100700b0480140d02401c103282e03002c0d598000000c3c52802501c08280240504e0700e80716250005404c142d45030f103c10200030002c036009481c003030000076000780c0c1000044540c2d2909c48000038144503410344045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 538872670 1250 538871420 538871429
    0xc08010b180102101b080112230328030b04053106050403091a0c060c090102010e060702070515030921040807030f030f030c02060c13050a0b07050d050414010302070c 73
    0x18141501d050100d017400c9514120000c0e640eaa0b175031035a0340c0701d40c0042568000d40004103451660001518990300d01c0c4031594102c40c000d41aa4a804132012400c3d26415081d443c50404002c0e03013000707030b03d071a4051007550061042a02c05000900e0700213034031980d802d414508402c19158440c04441200e19150075503070401d512085c108980d06190401404a48483c4034017107005000b4a5921644030b10b61003511070202c0140020f000e0340d2030b0b0100e600f0007500b00c86000e5046646e40c20f0004040740e42006990b00901c5650007030300f040e5041c001480000b00951601e540050000c0003840071000c1c0001da454000f0300f010300203000e28082c01c652042144034550000c4820720030040c01000380110782004503030b041e119881d9401104009182030301500c120041c0c44000d600b1800004526503030150080246082c044620000542ca400001748014107a03013110300800307008030340101001010041c45041c1d42040c00c02c1c03400c207031401c51310b40102c0004641c031038101030700400c1c5038040003c900061005003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 538873920 1250 538872670 538872703
    0xc03022701030c140d050a0605131a150117060d060902090106050c1605011704020102120a0e030f010509060112020d0614040219060909021b19060c08010b180102 71
    0x256501c2c145140c28070418014402c44144641e640002d40c503100f00010003040d4006c0c0642900252522014000c1070014116980c0d880d1071030201000400c00c4155a007480b01d03c003060b41d49802c0c0788100381100001c3c00c051078184003029000b200917800508010b948040e08030707580b0442001c1880c10901415840c6002034204000300f00201d081a04003016110b00060403088036100020010014a40d40c01d6100702804660304194007480401c541e80313683d03405030040c01142c612145d801030584155201420a400240c95081c1282140c90305000645101000c40020f000c1402e01d0b000450b115501071007211789401480b45c00320b007103460700180c000c0d8031a00711b20f00f0007403000e07422003c0e00c1554041314120700c1041300000500440701203084030310980d03000360f481264460401038490002c0d8041000c030b0788402401a10007101540c1004042c000c08408114050b400803245459015a0b5000380c5001c1845820fa0041c4101d1407050142c40c00107a4513901d200146e02e002c80141e080004042612014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 538875170 1250 538873920 538873999
    0x1c020c0a020d0308010608060a030f0308041a1807080f06070f030b100801050909011103061903211701120809010e041406131b0525030c0b07020102070c0302 69
    0x50540213840107040720b004d501c400ca003958a190403c0f4072940b40c5d0000900c4146200c12003008644200d42d136503880761085240200000700419917490910003103c00e411005940c5500d42554074061180030010300f10000101040c5d00250f080c59260a0010401400c0144048610300e41c2446600040312a94000d44078500201c02c07040010f0052000340104c1d0b00031003020b030200740000d00c14800c4442450a0452090440d03c0d40010880100c40d00c010082c000e904105000c4041080c84141d0a20b101c0c04070204655500f2194000d000b001d42140e500c1100c00425004000300307250b84410703a4030140d0103003815580d400114016141503142400d100c1e0841c2c0380c140d02c0100c0400c020300f003900540c0304032030344191a421b49140105a42d112000c009811000822075005d88d07016030050182205d0001c0f40c40c00c88688aa0900d150320300c40b06003079001911900084080c0504d101100d0340200c210f2000b5860f2100365100c61020035041d02c00280206c00342041c01d4603000c258200c0318041041074500300380707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 538876420 1250 538875170 538875173
    0x120f0301060e030a02010f1b08130501080c0406020d0c170c010504050106050f03030423060c0604060c0305041101081005060c0102040504050a020913020d090b09010e070602031c020c0a020d 83
    0x4064109014910205034000c08030661407500180c140083e5074144e484008852026600b00d4071580c4e241403440882034290010800505804e0141a24090200d82048503d290400041640f00c0140c07000b81658020802407118a40c013151107401e88410f81068682e4420528050005402e496086c1060303603804110781d2300401c07040d04140e00881c01000203211154484e010442e18041c10429a94194010031007000b090990040f0416080d0105d003100055400d1a000302d401c90340807041005294000d02c04002c04c0100c184580203c002042c601003145180c03aa4039502007440c00305525041c440c5c003900190085400d1704480014000180c072031926410080c180310702079003050199a00c510304100010342001403d1090302c20040c1c00070a012555490490814000c0d801441091401901c418995000c1035400711450f015503890300c00060040c0885e4501400c000154000c2d1007190010480404c082e16503500a505c01080702500603a038011480490340b40c84c2c07500100a400000c00f841c0c480 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 538877670 1250 538876420 538876447
    0xf07050604050c0a0b090103051902040e0f01080d0909020d0b0a12020a090c200a050d090509150108271203040b0109020307050d0b010507060608070602070b181212 72
    0x5005911601c21641c40e01d03c00707020010403074014015444440c1d0709101c0b0501640c4a0b41080d500304d0001401d01003040b10882800c0b00741c1e071068100c01444010041480211103040c2e11305801490144081c1c5084461460014a80b0342c482c03050132405600400d05d07544850a0750320661520200a2440a00b15590a8510050f4003100b9003030340700b4090001300241c1007489020b00300403034601d43d4400c500d1042c82d100d9460103845952500e1818800e0021000015404200408520040f6180c550150b0f03c0c04080200d030398001813416520005500079240140d8201d004282c021701a585031034030b56400c6500a0446040c080d0244409114141c01c480b081c03883c410082d40a1801140c81044586e241d90055081c0d03c42030300c2c4600010030401c4100c8034403100303a000e5100381c40149001403910303425803a01070583d40340c3d41128100b50072036442005070580400800c1c0041078004007903400d10f41d21980304480c1e903000504a07400380300c8a04202950303100c140300d0201003e000b405515202c40e480101c42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 538878920 1250 538877670 538877683
    0x903070f061716140f0d020d0b10140f12040809040c11060105010c1401020c0106090b0f01120903091d010801060b0304050a1101120e030c0111040f0b030c0f0705 71
    0x190200301c04a4910020794418900c0c41d2180c4501d043c114090741035820100c8408502c41041c284404040c0880280908920010048440d1004001d6160340d4021081800c403000654460b01c0743d0388510101c00140c1d049800307402c82c140000d14003911041130b10705503145031040e1100910b00701c0401017004200080300c0b0180943c6013041d00c00700004030491405403060300b403507080c11846a0056004109641c4602140d8640c507208851140030325039103d20503426a00403280c002802e0351520b00c14820844544a14010042c0803035028444011020018051604410171030200580303c00d2088285400303402650020240d194940c2078174082845600100c40742800356003101e5080c820b0004440880b00241da00484d00710000c0c08150465540f6032000d801004180ca0521400600000005c4500c0c0701c1c0c0c00303a10f0540e4002c1d5035114074151402c4c0c211007482074038031208002400180034201100c0f10000c191908107840d45d5036901d0b03640d042502d81c0691001004c83c001c0c0080c18008010000c50315 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 538880170 1250 538878920 538878929
    0x606021c090b0d021b12030c07051501120201030f05060d02211f1503120c0302010b190608011a1b0a1e03020c0405041e02010504090e010b010f0201020a08010b030a020903070f 77
    0x1742450001d5809402d41c0b90f103d00030303401181d1201072010503401005d03d0010186144503400300c03088668059010903800340240d00c4951241c090358100760645d42c00d80102e498094a1900402040c50301000080070001c240c0c40c042e018a0140412030906098042c141c0c602c00e2007103007102c1090004100440c5030a0340c42c8200c0345c0b030034100300c040d115102841e5040000d40780e001114600040b0405804c0701c2c0b115104405804664035446481100d460b980c54078a550b080300d1062030842418024040c00115040c3d0213079001c00740c042c0f88004859688016220542800b41501a29000c495451751a101e01e9050240800c030410104071440f140c41b59140001920036000d0b584072009070340c100021070b002110090080c48042c002504180ea000740c2452000707105042c8107081c55124102c000c01c51300202c1610781c29a40d252295105580c0000600703800d1a01440298542181284010000641032040c1c114071a004404968202034a03015190102c9001c0c044406e4207a68041440c0190341500c82e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 538881420 1250 538880170 538880197
    0xc0406020f070501020604060504080d0e010b1e090a021b0d0c0b06041e0f09050303151503010609090f06050612011806050d080c0c181006030606021c090b0d02 70
    0x10160000d9002c5204021644160003a001070ba542d91201009013400600480303c0400400000700d41100900c540d8002400c1e050000a0b070001d01c40500124151511030400c4003e070521011060355544030003240d20a00c82c000c0540c441d0151007010218040d8455220345a0140302c0300ca204840c0e1003a100c825460040300240d429807034600510049075400070341c07618424419124600c080c2c2040c1c004100e0100840000146c035a01d54540500316041580c600e140c07100e4440310155a03181c0b4082e80c20185c1c900d41540d62642d4500400502452180c0c032608108039128200b640c150f0110b98081001048042c1810b03135204060000c5603003d4500340502413940d011185007121110080c41201d003500e070f02812001b072814041d2508801d50700100701000080c0b050002500d11915510b000c102160150b807003041050511120100000340107400010805141c50810001141d0005801400248065190801007000801126446599001812800d00001d40c250012645500400c40020b9855 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 538882670 1250 538881420 538881433
    0x3050a05072019150509120d0c020c311a010c1704030c03110607110915060a17090a080a1d1003050106030e06010f15050c060c040602 59
    0x2585a000c960303058528900151103103101c003501c008a8000c98000c000210101d500c00f03800c11007020320f45400c2142c01c83d052031152106041035500307800307201e412581e00005080c030300c0100312580e1107501406e4001c14000f030b2500b55584000c0d00131f108180050801500700005801502012035007404030f880c0032406c20348141c906000d54902881080e494000c108407001c403909200e0700440d0340ca18403410a032903401c03007420721540c0c041c0f0500c0104021031003201003c540622b5414207190f2124248107003401604100f2010002800306200481140e0007101d00580c9a1214220100c00020148200c0d810100000d00d50300e81135003140d105841c030101000880c00030303502d42d0800e0786c8400b200c000081c00c02205100c0b4203031413401081a180301561240d40c81c502e080040e40000d200031a440d44640c0442c0d501c000500ac442c1d418082e37100b090145000034585540341c06a0103c01606611580c4800812241138070080e500ca10300311603070412501d00302d45050400f0041038420380e00c284609800740c802c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 538883920 1250 538882670 538882681
    0x6090603010e12070312020a18140105040b0a03390507080f0a230d05130222020705101d06010609090b0a0b1809061c021e03060103120305 61
    0x5000742401d02415074081c0a6102c4030f0040d100700e035000010100c0521044a06140b084000c6101902d20312a55681d40348402e50b04008170811002242c001c1c41115040491860003640c22508460440f40c01d00c070301c00d82d20031901204600501003d10b09200c1001080c410000c68180b86588200c145084018010481840d0106440074070500100030101801400192084050500580441c4c2200d08150000907028584400010300640d806800706402123460301c8070b468284140c650044005514103103c1d100c540001d00d0080540e0004418a51000204110f1507a5501660203241d440821a50f00c0c07255a0f50010181101c80b10301d10415698911440c50380100041580c100c131090385030030364410704202607440070304109240943c200d10039460000c0c011100400070699001141c50b0303102705c9503000080240030075014216520824081400030401d5144400180000b41d045542140076501c45003485030a40081503c1d60341070003200000010301c112060085201400c0703a41c100404d5030741 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 538885170 1250 538883920 538883923
    0x3051917040608042d03030204032112090c0906240c0f1101020a1505060f2202070c0f0308071109010e070806010c0602030115020f060402092703030a020306090603 72
    0x760301c02d620014410801003804603003d0f416201440410703e01040040480742c848200b60361791024202c0c002580040c08206200300c8800b1000030340340c141c0d89051450780c1900c1c01000241001c041c1d92405035100c000c24200001041c07034a0090010b03582c2409019920a281844003007142d01880e101e42c05000501e035440e1080105000181d4005000c40c042569625445c01008805824605500c5503100c2100400c0400b03003c0d502d4100340701c0004c95580340a4041c4034500301c40f480d03824040d0800d1640d48095102101e00000d25400b40b5200607115011401c0040c024483c035840350718503804041c00070090110320710042c103415000d02e20b4698040240000d00c20380c0402440340640408003070020071000780c800c0384400d400160500d488803a0f9019501d40004a074400e9100910400c00c5204001881d0f406008080c60845040301400341e51070a5000714181c00001043e2401407440c0b1045074032030003600ca000901480c4003600701d0b0340360718100e001c15000b5841564001d101d10072800015500b03140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 538886420 1250 538885170 538885177
    0x302150105060301030b1003061109010215060310150f06080105092a03040312060618050604032001110f0d030e0d0207050108060303120f0a1506050306130603051917 73
    0x400ba02c5030345181e1940d295130200d04c1c1c001e00f1051020507039903800800b044640c040c4140c1c05110801e02da94503030f140c4002a00c0c042c6008080f4001807102020803250703540205070000d1400e0310b0400441d49102c5418000e09d070300302c60f4220b034a5180c4403110111b00940c1c40a41d0398141c40064070307198481e4407000c3c141e10350414000e80f6001c0701d21b01c12160810a040902c061a001442410300c800404942c802c0300040e41c103030b40c10110000c0c00b1184440d08500007000443c00501007517503c10b10b01411912540107002000700c03103a581c15140c9aa003203842e4481c400b072a5500a1a109485013080594180f685030300c198074842001a083c00c03500384000c2c0300801d401041680980003071082c00d02c1e010055415100041016034140400c1c0318000481100d41801403040c007100740345084501d02800345c10300b1a4030303a44c00c0b0001d200c1d100c24180070a0fa002401c40b504908203c0c0c1d910703001506560200050055904000d040d80108800c1100c50800c40045070b621030301c16900c0d032610242c440f209800750f02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 538887670 1250 538886420 538886429
    0xc0b010f08122713020d0c0f032306010e130219030615031e0e03070b0a0603020108071103040f090b1816030e0a0506240409021305181903021501 64
    0x21a18441480d062085003000060010b4489001c444c46425100106e8021440850351152100044455503520540921094041c0c2c1000c001c1414030001514000c80d000e01c81664040e1050041240f581c01918528403d5000074020b004100c0d00e030050201035001101c000c3c00481900e0080d110040c00f90040d5000c4d980d079010f010201c55000c00040b000380400a101e162401c07a0581c002c8000503032400382c100184010002990768181d68a06100c0041d402002401c00900c2c10b90f05100507a030040f285a000354080ca0004945a000256542988101d034404031603840006400a0040b03413903040006e03102800c903503682c91500d06042d4801c20541c125407a50796145401405c3d0f0105000364080c0c04498081d2003110030703180780780e500c0b14506401641c602d01c0078201c060268070051040c00c110569100e090700d05026081095021881404400d40342c0165191103100068070100e03070507002a040a071280031074040c0154100c440da012060500c0a40041c041c61804071800101a42e03918103d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 538888920 1250 538887670 538887697
    0x30405030424120b01180b0406090f03050616020c03070306060e060a03030801050d0606030f03080612010204060914031501030b1e0603060a020901110601030803010e061815010c0b010f0812 83
    0x1e401443c2c0d0304005200c150051410702c40d50a019a0000c81442c110324060310010083c070b0f59139420711402a01c1d1030540d41c00b0710f80c03190100b0024400110041009038100c0e41d60940c01d00002c5200301c05a05140d90481155010310039090008140503080d0054012156880110599a00c41106221100b1207501015006c02c2c4854010095400c10074541d14509000e000002540ca8032aa10604a04080c070415800154a84180001c9180c205205102d01802200031840c0515018004d05103407424424401902c220108481d55501e040c000184203004012450b80036603182c0c07601d0111408192030701081c1c0702100c86854030040c5140385240c040c4000900500c001d6a8506029000c1c0d405000c1c018100801050601da0300b800c108884c1e406188250000ca0302e941c1440300c201038a0400a144c20710410a4081e407150501da29010140c05c00040640202420010380050342e400c002000d0003007010041c8070000814000c01c0d07003200c0030340e001d003070035952411440d148408143c0902120f09007013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 538890170 1250 538888920 538888937
    0x1707030801050414180a0b15091e2206020705100f0b210102070c12120503070c0308180a081902060603030f1305040603060b011106190504110402030405030424 70
    0xc0003c40004145074240136412034107421b1203541c81c0740000c202510400030160724140000700c3c070324000c0039440d8080444c400c00d8141c890b913031800810012029010303101007561070038581c00c15000c103096552240d8102c14250350719100341c54040c2d030702e828506400b42110b180042240100d4802d01640500b020000d04503d1031064401d4450411080c0d8041100299400c01102c4001040801d083c00101455120a0305e81811800c0c03000b4100c0c840e58120040100400c1000300d034035002420003070707056058a48580c550361a4a0311241071210628042d9807441600072a41c1000814402010012051078920b4001c120340c840a82c0d90380010303100141e2581081c0003104d60101c0314006810420704100e068218241d498010a0807141785420503076000380c0b1103884015558101030744043c1c501603400208043d1400d01d020b220000301900c0150b0b405522a4003140600000005400300008000e008540d28101440d1007941c030341c4148a410004480741c3ca2001d45883d102d06407a0b0101c205450310030f103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 538891420 1250 538890170 538890181
    0x1407170d38032b0206010902030709060e01030f06121104090f0206030c041509081c020601210209130b0c0c0d0804140a0507061101050c041202030a1707030801050414 73
    0x60741c03440c08458041c820600e00c04549a02c0754940a80421042c6100103e01e50b00c40000b41440030507048800020700408c03c1c40310450707119101c003045801c28a8201a07226460004030098020303680c60040c154100b002c00320700d01c07240640e11250244201c0507050070940300d0041c0425a081408d0191035a0010071101c009170804100541d40910440041460141c50742880e0403004a40400e640010301d00030b01c14401d4071410008240075626041381d0a1b000d5040030f800942d5400d05000c2c807035180b1f22080c83c800c1086c1c2901a542032a80c1d0041c40d103561850070459182140079003d6041e5801d180043c0400d283c50f04807411100c0c0408004041c10041400b418196182c200291007152210400b254000c40c0c500c0900400241c18482c002a244552034030134000d0203652203e07200c00d000d91400c004d00c0300300e80c0c22004650031100e10300d00078a043c1c110750000a06101c02c000000e0402c1c402c9804074840351030120000c007186d5201c0d49441c0403d03620756061000321840c003000401156006400300d50b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 538892670 1250 538891420 538891511
    0x5030a0f0f08070c14030c1e040603060227060309101104030f060920061c1503060e01060b0703170c0c0a0804030b010e04080a1407170d 60
    0x421450180001e880d4603060365960349100d82c84200240c40d0300580c2c4000380300000c070b46900449000c0b000ca00600b040c109240008003400c40003010410b2622204d40450f4003504c458024100568005108544404408840024110803080824010300c582100c1c040545422420b8034010000d0000900105448205110091014403008002d081d41840000006101d0800b00005588600c9001c5080c51140c80d19030b404c282d000070001160fa07012613480280740ca4400039940171050f103189120403003442c040340200510421546650301c904003170700071050000540000102204c00002040810f40e145406039007030043c0100180041c0790641c07040741c01c000741103050b9080003401d041d4600d44071101505c0c51030030001d002c4c103c0300003501003010001d0046c44400c0274018510500100068038060341c5000d02d61207031070544014002c0b10004a001098801c050300c0c00107620925040e001d160100d4480e030b03d43c2104040c1038070305090030b010440341c946011110f4a410481b00140c86901d00100400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 538893920 1250 538892670 538892693
    0x303011701020405040e100e0c010512191517070e010308070213050a0e070e010e04030503040303060305030d0914010b10030c12050a020316081e190e030a02010605030705030a 77
    0x60300d8640d001d22000c40c441d5168400c064002200c040149601141c061301c00701a01c40d0920600419045503100c60300c01d9070800300b180c1c91184141064851651442041e01d03148920700030140d10f0520305661281000210411601034ad4041c5003118580d203449042e031592400140100f50751803071854010000070780500058513105100601c5040039001c0414084211a012203842c07000c01c0c0c5400b10342800310018800c040c081c0c40b00150780b0a0940c10440003070304501c1c1c0a400241080000400101458480c0d4811005194004140c070b81c0d4503031940092010300100c0f101a64001841c1d21000c0c540581480740078007055001d010300b80c0e401c0b440001079009214022242c418052414120100c86c103003846018070902c8400001600c1e4100ac45640380d1403011800032805000350709003400040510b4084405058683c0600c0804596800b00200700c0d400d1a6500741e054541001c0600031a50b0010002c0c080981d080c0d03008120311981d0303804040da01c40c00da11031250150000c903251004140c2c000c010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 538895170 1250 538893920 538893959
    0xc0a051011060901151406121801060915171e0c04180308011e0509040f120f0e0607020a151806020604030305060d0b1302041d010b0a05040509030301 66
    0x1007440122400205042030300840b07060140d070b50759100c004071449450000314083c084525600c0c0b600041e040c042110341c8211440700000b12494800614000c1c10030211808140035100280209075072524044054800030402111000a556004c24080452080000c090040000520002844420210800c08401031080183c054600f041c0030750703151030044101d0300c40c00c1c503402610242c060800803c1c1d2031040e007160405041c002c603024810f003903034181481503c404845035a05611203141c81c00720340c460904002c0c202044a8540c402c450741000103e44c01d0151502c070030f03a00c180e0b00c5041204a02c03400744000d51241da40c58052201e4a4815000c4000328100e0800e89010303413150201202454580c0e00050059100328108030416506005080d0803040a4800048200c01581c440841190040c4014017581003920041d00759901c2e50400e01390f6414418280c41c40b4141c0c62450360181c925803001d01d000e514240310008181c18144551846121208099070440c0d00f00030100d242e04502030f01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 538896420 1250 538895170 538895177
    0x2090319080919030b1608041106070f0605060301051006120207110a1203031103070905010c1a090706030e0a080306010810051e01120c021c170c0306120c0a0510 71
    0xb0341c10b078076210302450200e0b141da90300014000390718626001e0480070000b40400c9405060030040c0c2c0441c0c0e0030070840c0b034101d903021521003481da01d0030000c43d000303010b5641c0c041c004445100030501401500e40c00240200310070340c02440349554070014509104c4071441060300242c244207a561170b02d03041e58050410103100e0b016010b10001e0311400140220b5050b00689415482e103040c0c0c5080640620600601021412096056144c6980003504140e0749108103030600c400e07031120707604000343c00181052456140f80101c0f038600306460142c0d5591898040d140100e485d007078003107010040024070501e905030300c40320341441c5507a0a80111199070010b00411807040c8030f0800840d0f1951f800c2400c06c4514110060300030451142e400041007503000d501c0c0040d45a00d40f50813a00281d03400300b81d051a10690300c814544000c03041500720b4451003000c001ca980d00044201380103000c404a001903025180403544800070780c940d00d1806485050140c102544007400840801031410000b40040346c3d41e80030304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 538897670 1250 538896420 538896427
    0x3212f01051509070c1e03110d111522020a0b0307080a270b06030c040e010c181215020f030f040308090d05090f030102040b0d05010e01090209031908 66
    0x5091425107209a8402e40c036a8a00c0710040c400f400c200b0300b4280d0000741840e1280b0700034007039190202c00d001c5182a458a510a240329102414024280c100340a907060084505450549000404203420115400c07070b60b00818410201c04a150441d8501420720b00c1014110b040000d0a11812079460000803a0400d1031114001060017540015610036005500e903c25103107002d03503440046030340c1403110494000c0c04078014041918200740741c1e40f200c1d500118101845e101e00c80064030306400c101c08039921904143d01d00c1c000800641080a08404503120450301c1c0c58501d50440e41031000c0c2c000d5803d41c0e00d41c0724942d00840c0c0016050441d202184200614101d803c04100302c5680c000c035060411030320050244810103620103009a405079402028000d0f007203020304014030703034450949039510682c035085190445030382c2903040b9001071040d004565601d81c4030f40f80000c01303003109203d04070740104020000940b01005000f150190007005010302800c40300040241046281c3d08030503607540000f031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 538898920 1250 538897670 538897757
    0x506091912060b1f020318211c05072105090918100216140c0405240a03020108060d170d09060b03240703020f030c040321 54
    0x1c800402400c1c01000081800c801d14028011510b0458014490030b07801d1120410610382c1c0801940c1744104d00c1000d0098001080f40024012040d19410551f81c10b580340b000b02051800250400c104549514500d4030110b50349002e0314203004100c1e01400300b0307080e058a4074100e1140d9100c00203d070a079081040c281140300e400700d21050b808507803550210040072050b59000d4010041015a0300440780294904441440608003c826040c002482d4003001c1e040c0000103801881035114040000d0410803a0749006000c60640400d01c403203441880503026080d001e81d00b020205642a640c060316488010707125081801100030b00414150341549016007001d1a00b080a0000c1ca9014000b5402041011440c02c24200300e0300092075052080c1d03c4403000324002d4030101108211310322a50f07070950301d694807000103078082e2268284121041e8000801c0115699a90000c0c1040d00c0c01403121b08000304a4984903001c0c807140303000250100c1c5421309038000c40307844c0308500c00920074202c2d803840311200d80d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 538900170 1250 538898920 538898939
    0x20f0102030406020706050604110f09011202130608090a05060c09120703060f060b180103180624060215270a0f0311070b0a08130f1202100605060919 66
    0x5482c111800340e00040d00006124840c050240c08c104101c90400401540c0c460040342032003034240e0b1603a20304011a01c012968003500758042d0710410840255581d60200031851220040350090b5008103040b14040380381c00c8000900240b403640e20200401c0305440b850000ca82e42e41259403800ea10180301c04940500e90010b014030f50045204030404580840350050701c80541d03003917420034104001d0034000750b00d0307010481c4030250f24280203007000940c6d0402e0100318507000c200e403c005407101d400c1c9034040c103c618040350019a80913910a10682254444200b05c1e00c0340081003164000079130000100e941e0303106450319590042034110300700d402010400c610f242001516003042c0c1d26880410914801d2540200d00002188200005040101c2c102512448175014440c0048100710002c000180c1089246c903240441c04e0301714034030384224599071600c2009100e040741c50170014020543d2500c01002c2e280280002d90307000414050070001c9002c180312500000800002c0c030b1950f01040040e50005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 538901420 1250 538900170 538900177
    0xd02030708121819030206010b0c1b0f060f180649051b0702010c0308040201091205060402030d0e03190807170a0e1f0305090703050d030b0108060d0203030415020f0102 74
    0xf503552403884c0c0d10f082810064140281603100103034086c82081084c07c41400814191000081c14102c04071850004000c1801820300c160b201e0707004400011014190285800500740c0801504480c1d00d10340d010100f441003d01440040c081e50380c04043c84100e405074a40c0c0c0c401c0d14401c5c0c20b4088516040c2880038982440e00222007203000b0b03035540003840303a84940c02e004501251040803c09152084035400200240e61100015040105001c007240440e0f22511207a070003031010703402e20118103070a4100306840c0c080075a401c92281c421490700041c0503000385540c9610120060103819500c0031100341c920000c0c009401110100002c101c514009000030b00345920900b0b00d514010707207a03420210050b082808401d5150320a00240b40001658481000f50001030499480c000c101d0f5201c40d2080b52505249403c0106940280440d100ca002d926502c010b03007040e02680c582d42c013903c404050050000d103030a80a50180c10420090040400b0545003d80c068400e1044401c0152600310641c03ca81 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 538902670 1250 538901420 538901443
    0x30f390f030a12091a0f190207080a080a0e0d020f0d080d0c170a0e0c0103090807020409050d23031f030b1306050108010e071404020d050a050105030d020307081218 72
    0x1000b1010600c4031501c0710041880360300c100d0310014a0406070304140c011ba40201d98084590398a03142080d03071918070901610000b0943d00301200c034014114541a446500400086d04c0015040141102207150815203103034540d4028043c030648040b03400900003000d443d01c1d81604c1d40306040003400d0440920b40f02d01c480701190759486503108485450b185076030343d8000d0f143e81d1010307080031041c044903103003c00c414080722024240050110102d15008585000f01400a54000c1c43c2c1481201030010120f40c9040e07801844ea200240110b2161044603505510060b2484505041c4001648908a0b0010f61500031014001c0803c1ca40e81c1e82c0c03260380c540004c0700d0003c4401c16900c20340e0208155070007035901501ca0070700240004c04c8ea41d01c1a5507151111702c50069094020365400f072032034456604031001c54070400c005000c2da00e09095100c029050a1146501901c0b80d11410360880d4808015038030815400356500d454107000120100414002800000c80b64602c01c0d84000d0400003009a4244107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 538903920 1250 538902670 538902677
    0x90118112107080601051203121305010207030801080709090f0204090311030301120b060f030c01080403111b0f030303010b07150b060c010b130614120c030f390f030a12 74
    0x1905048200d810700344d06078821402284208503100212a01200b03942c141480800c00b58035550315a522100740115100001d412944009011810b155005403181d042c0c45c0c0c03650842c0c00b0035591b84840c000300c4408035006080303c1c20a480850062505d1b8001b154001e000746014290200f400c1001400c5504c00c2e88034072080c90680e00a03400b0408140c0c250396008800315808041c1c40078601c00300351500c4400400702c1c100f28200380001c0406000b825410414187d0208407440c0c007440048081c2d41921341e8808500c512a44411419a41703400805c49040e0b9543c01d202c541403011545d034900821900e040c5071021640c403803000301001d844d003030081e00e41d6001c214004030f0400e03000e009006c418904289443c1c0b49605004080c0034018180038401c2d0600020f854403802903186401c1d803400c1900808689a060140594000c0741d800c0001d40c032007001100500607100c0b0009180e14184070140140180800750384132a011049240480e41582c0d07108005e000c2d10712001c1550f652595022025a140010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 538905170 1250 538903920 538903933
    0x3031e040b0c061b03010509070302030a0f0c0e13020705031c02040305160302010e0411090d020d06060605030f07030209090601300f0e01050c1605190303140901181121 74
    0x4403070700c04401c1d6048030136411103078615410300780801d1804100403c0d0300107240c0c0010114455126030f07400105d4501c01501c042003035071030f042c00c010702c0090201403461240b051400c2a2101007190302c2100c16256015000314a4400d000c6042d07244844000240e81509a080c400080414002e00c4551824450146a19071325801d601c000352050428040ca140201d2608178000400b5604000f1990308200c2100d508503840820320000d001407103c014010040e07414280001101904080554000e031708840e000d10003595507440c100c00b01d000f80040c140d44502404045003455000340350100b00605107004103003501d10210705135050310307843c0d540280ba45a40c1e0702540d640c100c0039120b59280017003107a0007800207040c002295442d81c01007006546001c2864025541000000c100d02812213078902e403100551a41350034050002c1241000c5030f500e4000e024001445000f0610400c0341c00c110403800b2556803035540d00d40004002043c0c0160340c215101740145401c212034048226070615581004115 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 538906420 1250 538905170 538905181
    0x415030c0605030703051f09021c020d020306100f270e0f01030c05030f0a11060c0717070e0403050a0f0318060e0d0c0c030f0611030a090b010e0603031e040b0c06 71
    0x8030756000300350400c4074441f440c9140041c2c0440c10003000f2174414000150320380805801b044081d80340710301045945440080c402601020070780203903215443c11205a0307407002c0c0380e00c025a251041c0100780c01c0020008038130000007076280b9144044d0751118505a0641d1600c520003a00080015200e0022070701c288030040041203404038294010740803d902030a40a4484142199112041d00c0010f080e071040240400360303619081e096540200d00c0c0b40881c0c1210382d4a10564426518a20007600f00303025072200415854651641c0f01d0155038990340d05468000e184030100e4250040d00403030010180c8030000150000c000b00c0e2803c4010b405140001410f01c030b4900704624203281c80016105110b0b11000b0800401d001551010440383c000d100d00001d03840714a45030740244a00c90750102d8800011040c0315944d20140d11010300c65100712004075541c1d81b40e046c440140403048a1a5500d030b40100b08802e204200418a0410b1803050400142820345a000218041d00300101c55501503121008005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 538907670 1250 538906420 538906427
    0x60310051302040204060c0b2503050c09182409070309020d02150a02070e01050109050607080405031b090702062205010b12032107050706090203160305061918020415030c06050307 79
    0x41d000403104a100000741494000da0742101564140c070414159202e00003142e4404010480300d062000621a0070660410004608104c0b000c0d0fd441c8503100140007480420fa07400c5500340c1500304000c008117010307564904218003410359018200c0c0c00c003c8090095005840380c510405590245056542c0c640c185d440c2d00074580303d103a5000c3c00000f12440010080d9036006906407041d00c4040e510103541c0d4000741000391750342c4199801103801d4450384200b080170b001800d80001e5501421500d1010076160a2002c036a00c0c10250344118022980070611241c0c0192540c0c000d02d030601ca503002085151200780025000360300044168001e4000144a002d8003800d031340e40c52030700b1210800325201c1c2d04150b0700040140c0602e25004000503901c0b000901556410402c0884282164071400e440315220725201d82c0f2604261545a503045030442142c40c0640346028142035680c6210341e01e844050240c003000003814200b100b022103007071080e0001c00810030b460b0780314015100b42e0315529500c3c2080312004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 538908920 1250 538907670 538907693
    0x70e07230901030c09030209041e05060c03060a06030b0a050418050307080d05160c03030c030e060406060314030909040f020f210c06090907030b0102100c080a0f05060310051302040204060c 83
    0x100c00b04064945d041c40140d4820b03820356041a00501c8522a4400302489a20042200400500a03100c0c07070040140807010704000390303c0780c4c6082d40c600d0101c0d0341d141c0055040c1e501d01d05884d9840180900c00380304c90300b480c3d480215030b07582440c24514105000e4480c1c03401d552064200303440c8540009048030700ca20b002d0050f03070b8000c0351001d0420700008406d1001051805c0c0760100400301502c07412080e030030380d00c81c0c5c0050108010002c180c42050509243c1200289154441181c200614405141e200c035070100a031180391102500b400801d80e10b965880300203150410040381e002040d41c58445042e19203000e201c4681010300c10172950b410090003902d20702600080028420078041103a40703c1d0343c5a552549800c010305040110f1401c1c81e8400507420700e42e01a00d80c41e11b0300e1400c42d81411850340031006130700607071010004000c403201c00d240c80410303601d00310b841a80540c400303500a02042004c0c0d112960000c074100607407100103d1a4001410707640290301040025803544200300c00c2c07040d407907401d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 538910170 1250 538908920 538908941
    0x30a0b010525111c17091e0102010f020a0f0521042d02010c0605100305030c070e0a061d0a060902040e0a0c08070e0f030a0c0e07120608070e0723090103 67
    0x1c915850240e9107030411007120100b001448146081e458810084d2240c0981e0030f4a14001d111138100c240302c10840d441071947d20010380c0150b003022500c7c0040c5100e8030850760809010b40c0c80c01c2003c040581d013518030343c1c032491248a21001d101c032142103142030008402d004500c20602d61107813545901070306800b0041d03005841ea021010001f000010307a002104150041e90004005c6100c5c0d4801c5814070115503640e20103016030100203117900030030401042010540700101c101040345c0d29264005c2040314410b0040303030050307a840d80c2c0c0f601002c0e40b414803090b40040d034003102050710703a2104000c0040e80c1190b0301040107407a4010900c032841d042805801014140c0f403520100500e069a0000c2c907404255091034043c0600169030041c64400b8480d490700c1a42110918201c40ea44581c0710b43c640000311000000070750381c201c203510105a10b010342c1c41190f54840c01005014109440d00c1ca4102d000b812900c1400b4511820030b2181c030003c08901450182518420380f21a8580005400e44103240790 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 538911420 1250 538910170 538910179
    0x9100c020414040b332d120129030a0203010908190311030c070c15200a0f0803190216020a1505041a090d05060a06050109030c0b16050a0b0426030a0b01052511 70
    0x10b071070903289c07070002c0c4050364020702c8a0505801030f5403201017820204a104043d41550078101f0010620480500500b12000811400a440c422100c022000c40f203607180c02c83c4041e8402c1002c1b450354031320331014107034650050703003c01c0003a503039081040b03180c0d104501040003103071101c49003140c0d80040c1c1c1c0007025200c4025020307100b11402603842c801491403d1400a00a4402102103105103411034000f4034400910401156201b8681414203041000f28204038072031a480c101c082641807041c0000c80710250291281420701307050041b0344141d002c00501002001c072051060901d2543c8442d40c136840c40e0301131006007416043c1000700d4810f6903140e0304800d05110412104000194400c5103400489400391103094031400046a00544a03110319806089882008520000e0028466080d4000c0d4420075090030007141c40c01800b0764907450f0300c050601c040300a200180010541f03800030f030b030030840c149059460304490103032000107211082c5002c0c081c04003200d250000c008004a4403c1066000c40d07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 538912670 1250 538911420 538911431
    0xc03011103132301060303030222230117010902180306010b0a0c05071a0c070e070c11010e030102030a021213020609100c020414040b332d1201 63
    0x40780c02a00a5240303000509a00349507800e104a182007202d2480394943c088000e01500d641c07414010080d400c50203000c1142644071200480c215a00b01000d4101ca1500d02000f05010280218990492000300c005040c85907480101003100c40d445825030107030287c1800140c695081d040c220030440400d0750030786e000b68002c90041c0005242d40040e141007403458601a650301607189070142c14401d0725400a6210150030000c3d0141d4134500002d440305c403c2c0d071811520f04594071405c8074007900c0161a400081516001c03410f0200741e045c03d0036900b0700c5040c14031034240142c00004c24220713802210b600b003909a001c03c000450321800d80000d88c0000442345001c0d8012a1038000404038031441d10140e10a1540d0784080040502030060408902d4000380200700054006a260042c818101d030225100c20b00e100000c0c1e80c03140424902d10160014050030141418028400d010240c500001c07558006622464180c2c051028401d1600d0007040c00c95800322001800b0038485212112202822241d0410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 538913920 1250 538912670 538912681
    0x60f040c051207090c020106030506090102160803072c1005040b030f060a1707060924030f27120f050904051509070e0916090e071806020c03011103 65
    0xc21400c01076490845001141e03800c0100c035140b8008060b4040c8903114109808150983c0d010f6100740200c3c0e009a041e0b0340b0750b5a41032040c0d401c0f4403415881c91040082e513594000820004009154003942a0400c02081c0000c00d030760a410540c0c9800c011009000160389904a080c03c4100002c840c80030300b040f03420581812540030982c0001000b09043c0c50000e40040e00c96501c0c0d260203402446003508403085907010142254440c0440e01941000c0b07800703c031001916240c0342c04061410075804600c004840c52928044003d8002c5007004d050007034603802c84401c1140102854150b40d40c40c401800034403003040c80c140000c01226030308441448a00818100d0b56600300c8101c0345000400c403000686542c2e5100d00040030416003440c2600602a582080001600080d034015529801c45125070b20ba40c403060f0605420341c1d001a1140040e04041c010003c2d200a800e0440d00a4100e0405003030721032114005100145140c1e00407030040c1d04c0300781e181250741000c1c89020f1202c10821034031071951400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 538915170 1250 538913920 538913933
    0x306180f0c09061207180501060e0603190e030f0d0603050607081014010c080316030f020a09050105160203060c040303030c1e05030a150b0a02070e01080c0603090a02060d020705060f04 81
    0x4200c44c2c05002180810202e42500388410030142c040002c200e41492500010fa01c0205424003034000401c3d070100070443d10b8644030341568811444010859002400450000e02400001c20300420b244000c1c040d4075802400180034100c21001104001000341c43c0d0705009d464800040c1c802420300c00e5040904c40314000c9003591400f690542840070300b000103000f0049a8602ca0a500900040c1e00030061120090107a03140100c04003440ea02405052802d800b404101e00c1100304060201c0d400100800855001d9405040112850315004007120015004070342400c4c01200d1880c142600060b081c01015054459200010a80e14103600400070307113182880b05e500d0102c07240050060106c00502030007050f401c00c0c2c2c042c2c204400075000c1d1640c0c6001c4c51046410244941c000342c000d0080c085010700c03110400504803412180101203d121402c18041e4035403020b0046410740c01150b14013009a180e0900400303565150f504c0060360342c40c0d1402e115007012400b40c90000d03040103400601c40807030340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 538916420 1250 538915170 538915189
    0x1050a09031b0f05030f0306011805092809060507090b13050d08090d0b0129040504020a09080307111e0f04270c031b180b010306050306180f0c 63
    0x51200c0400308600c1c55082a083c09000003800030503511000074442012030500700030f140104420389541c2103441c1c41110800c152281401220f410120341c000048032071507801526031204510f48000d4100b131003009080002e44103078690a1314800d885e03034217000381903900c400668004c04003810080d050006400b0400c0d0301d02c00d503208052050780c0c96240d030000c0c4042c41c0b04989130700c54010401500c5901910701055502000d1180040d04980409543c0c29000205a14410081075901c00c41c0742138241010400290011003080081105000000c00c440e2010030040012a00400d2205100d5009600300300154004000300ea5400782c0e03450041d0000e84502343c6149004200322004100008420b980031020700381810503880008045182c10180002c0e4149102038038040e10f08a182940524071441001e04680700790300d40360500740c036410b40795140e076888841200c0c014900031850030303038850020349003403405d541c01e102e1006568942d110800040101481d0362140342d000d4482c2c464244006100710f034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 538917670 1250 538916420 538916447
    0x60f01140d0c27021605010b0301090201080a09050f030408030408071208070b040809100519090e13020423091c052217060702070509060f240a0203090301050a0903 72
    0x2110310b4545500e41000b1209004181e080d41011034aa485c511551000039102040903140381d441c11070a401d0714101809829901038040e160403002c0c0c0c503000341c883d00806182e6416149401f03009502800d140003480100000c100140045446070b00b00800c180c02d190242d441685110300280012001541d080c041d00c840c01c1e0804000d440c599180c1c1040003191141d030601c0e079030204105141602c4650404003411038038003656220007540515131816035208200d4001c00c600542681c0008070482c2d0110540c0a4a034400350010500074446075102c600c400e5840c030303800d8007008040f04001004804014081c007940a8010380ca08202070220060071520810307100e55a20304504002254004540c0301d02001410004802400018220314135621900103a030781100501603c0320009540ca41a05601d02500d0000c1c00d01007443c0024041090280090b00e008a200e03080c2c100010100311010054408107802e42c020719a1610000c0c1050b00f1518020481c0c16001e141545001c08070368400440381c00d03030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 538918920 1250 538917670 538917689
    0x1e04080903010b06040602010c0201060509010b0712030b37030c0b070615082d030a0e04140f01050a2709150507030b040c0302072f03060f01140d0c 65
    0xa03824100400d000d0315002d103aa64001c07a00250020382d0b141c0c158407015035015540c3c02001101d85404c1082050383c02803050205c0c2c030b1010b11404020540049214000114600300002c001d542203001c5945040c0c040210915a1149030110410700c407070f40450801c018000103101c0e941411039480d0b00b15070419008500070000045000310400c020b81d40019101c2412104a4601998501d20070b41d448001e08100c48820100048060341c100ca0b041c162240007080c10040d5040148024007110100080d40f0b40b44d83c015181c04621180c8009410034501803c03248114000c03941c1001305104940c4181c0d03000303150310b5418000e013403d10780d504010103070b410000e810040707110900d6041c041c1c803e6500c142e41007641407411040c0103030140c15074000040484241d5040c002c00c44110020b500724050071a01800c0f440c00c000c061103004151100407905d00000c82512082c0e85912004a841c1c010202c40d40d521400c0b4900040c0008101c02c425409105002c548440a0304003c0e80c481c5c1e4409510300c694040f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 538920170 1250 538918920 538918927
    0xf11010309050a030e01170117011512060209060904020c07050405090c030a0b040f0c0b070606060503060d06050c1314030c030c0a0b0304060f09120f020705061b120705060403081e0408 81
    0xd030310030b503c00c01c03240c08106103403042075844590000c0b0303606909c80105219072901d0707800e8003040e0202e400c0500329524440c0f20401d524442e01c44901070344c031542e1510b030701c54010044181156150705c0507003d0305001a008080003410b14040c030040700c901501450040c0c0c00360845000b03c0d41e0000e03402d446640e02555400c0c42e91520701e030183c25088501001082c150008030003145020b0b002c4090f080c00d9024090601120703585440a07a800c0c44161401ca40055014014074089480b54000d242c119a1001c5a40d10305103103c801c101d140005038001d1540181c6081d00682c003032a0810030003142c1c200490142c9031941d40e0200088110280b072082490207100840058148510359101c90300642c0d80320002d01000b05c192408084140c41c1000004c04202c0940382c940c021440003aa050594001921403450a50440d2103441d40c003d0401407043c4d1449414054944203603407001030702c290381c4500000c180e00e01b800d150252074400018020b120005500441e20a01608950304641160300840101e58 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 538921420 1250 538920170 538920197
    0xe0309120f0d110606010c110111121c0e03191b06150e07080f1807090c0507050f0111030402040207060b1f09170a02011412040f11010309050a03 64
    0x81c075808480389202406207442045840b9000b281c070f035009010500540c0d9080e600c0700b00544e0142c803030880186c0242098680d4180a5000c2d41c40e0340030030b60008080320009d4000010340f18140d4409840c20002080142200c1c12400ea540100e810964462000d035080c412420310088a9a408007481d6003000350500526030150701020300e007010140c011600f80a080f5140320b4991955120707109a0700c00510020003e4800c5124441072805901c1964030202c0303c0c1c8030031051081d80c002e805c0c40e0f82400c3c041c460000030b002603e032142c400840c883c1c1c0c031100e840e4007036401c1003410300c905403610a10990502008425080791030089942c091340c1200d0041e222489420300c0c400401c801000b0716002510700888140c0104a6104440741071003a84d1018002e40d110352541071115400034a0000703c1d4000c250302c03401507014815505800115203041820003c040120407110042560203403404003460032200c042c420300c2e6101200000003803d040c45032004582d5419030790400248080d0070884144510352 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 538922670 1250 538921420 538921423
    0x2040513180b0907061e020c151308010903230a030f060503030d05100602010b0f1509060f12060402030c031902041701050f0601020c220605060715050a0e030912 71
    0x12070058000c626500d803840c04410080d914050707800354401081c0306190642d9004c0d035651140a4034007056001e04103620280d018070a01003000640010315a01c01d02c02c0d1562401d00040b128000e04810001180364126410007414a0b0320701020211442c00f02006100f0700c8180d00d040324604002480e000410403442c120000c002d02d81900310903414040050101c80e0480c043c3c1080380507810f422741c0d960340305603603241c141d00300d4040029180e0000110604c4140c9481d203106101101340c410400720340f90040440000303080b03501120745401440b8000c140111200d1380100802ea2045003038404500d18140520380e55100e000050041207201c100c0e14806107039010b180c0503140203261410401c03141d9030004a01c1c0f03004e810f08840c0040341100c1b190000c0c040350301c0001c0c2c02000310320103800d20310040d441c01211400d5900700103c0d50140d580715000091075480c2d480080000c01e02030903551a15280c401c00c5082503800160208980c2801e0481c05489000e01000f01c4007080d00841f129001604400f120a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 538923920 1250 538922670 538922711
    0xc040e180102121e010503010b030d0e1906080405070f05010c15060b03151201090b072a1401290f010c0b010305010603050d03111e12070e030106060302040513 70
    0x10004140014004c8000d2001c80300a084001919484a140e032601c0c241400c0300e042c83c040340e0341584420035110b031450098055454285000e410550464010040310540344480ea00020004107410101700034820280501030103011405c1600801901d0400028801c8405032070107494504001c1e13074a4804925948071500824a0000503912885c240a070b0380940a10015440e01803120300048500c0f180e0103210b000141540007421507199143c2038403c407008861004400c00c81c031068081010180104526510160710400c10b003e07802c80036109031405d40c0d00c2c0c40c200110314411808800b062411443d018030b1041802d54580c0c180354421401250011400d150241441070018008418032006410040941c1d01500490701c024076014021011130706548840341e000d207024000d18201000703000c042494082d9929040b030034148060f81c001c07440c2c1000c1d99010040b4104034414280f605080c000c5000518903400c3c03c40c14a0700d0301c000310b46800c1103c0a175600c6195501400210807912242c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 538925170 1250 538923920 538923937
    0x15010903080a02160e060a05010206010815100b0c01020304030f0c050c1219081201050603040f17190e0a060c1a06031606030203040b0a230405100c030b090c040e180102 74
    0x1421009035499200385c940031000d80d40c96004414441d03010595500004420307040f20180700040c140d0101c940320310910b400015051014046980c20300040c400d41d00c02c05082c40c415413200040c1d5901b024a005044042c0b11503049040c4a0003642d030034041900420900f0301004161007410a40d071070251401c1c1441ca82c1800c0c2e40d03502c6040c05440c000d00c070304000981035440d18244d01a00726601d0303a0030080c0c1070000325002403881c0700d000504000125941004025040044131603403d143c41180e6030b030225001181c0c10310000340c590202d09520b2504005540040401e418844c00b0060140c4801070b6222500e9910881414800c0c00300f05030340c0b0100b10782e8178000100c0f081d038051a41c403540d006010303500980c1c05440c9041c4c0d0401060100540b4420881119085000414030f03c0075600c08001d0a48014820f442d0390160a1070303410200498050221404950707030b8002445800c06040001d4580060729020001c80d0501c000d20500e104041d026400c2020300300140b800250410302e0034068415140c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 538926420 1250 538925170 538925203
    0x50603061602030415050306090a02030105060304030f17012403360804080304030b07091409040f02060c0a0203070b032a070f030f08070e0a1e030b0f010e15010903080a02 75
    0x19004440e1b074828043c50180c001114104030715260001c00c40d0984c0420b0080d04d500982c2003010a00090007080d50340f49940203410440d03040b0b0214130785084581400d900003021034143d8102880c488402c02c1540803070f464582010003028400014111244003418a112600102d0000442f400c804901d40c0000c50f5600000702c0c0d0b5241d45408800d61070380c10510080754460403110101e440039015103180019100c09803446010b1940140030002105000381080c2d03207403a8590501000740e00ea41e0000d01c01e600300038000f060034140078030600d0f01c1e00c196640020f8034040240180503588104452960040c0c0d011030110b180c001c820301c0c401c030f42c134410301d107004007004ca1b01150322080503080b00300c843c1c0c0e550580d21805900da4410780103450070440d41c01482d5102100601c28080d011a0f241700c04010281c0b02c0400c4165038607940d690282c11003d80d074040d85240c04800400c5026902101c06505c04000d5426281840741000081c0605480e40002019014081400e480c654800c1000c040d0003c102d20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 538927670 1250 538926420 538926449
    0x207060213090b0118060f0f050d0f2f090405060a1805101413020309010618021e1213060e060406090210020a05030315010516031805040506030616020304 68
    0x100090010143c100c056400f00341d84000f034200d102c1d074401da08002c6404603150791620001494085550407803158080301408000e03c02201c100310940f00d04019403410450000c0c0c1080d0244036040010021003200390fa10320a40003100f1515524026611340160030381c0c020800b40c8910b8006a0b0030340d035503041400e0350400c07407100f50b45401140c1c12250086040f045c0044800d51102d0056001c00600c00415030460b050640c1c1c2d00c00710007a03030b00550744441a00000a19103865814041c04480b01c0030442030015004508030541204a00c812201c03408a00c0505245c440500112010300500401c2503c2103008400b6034001d00005400075104d03000d0410a450151a00b450705200804d094201030740903885a82898000d280001101109640c11800850540e610440600d2001e2484000e0f581000702c144225031a699031480706006d0507102362100918070311506640251a403950b80018441c50500c010700c01ca90f200401d025400010030300c000c0070150420f040a074954821076011901d02c48004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 538928920 1250 538927670 538927679
    0x14041b0e09012103231209010605010207121203150e152d03120403140f070609060807111009111207050d26030115020f100207060213 59
    0x550340d0810004680959560341c0342c03200351022802c2d2540c5851010b9240c07000c200404d01076194074440640114602540c0d00070041c182d00320760052001c00080502200901042940030b01504015100a100038080e230f03840c12254803c03059084101801c150000c01c9299025482601b1200404d000390390110b0400f9610502c410400300c08640e81c00c2d2a100030704007601c01e0f00e0700382990040b080d00340101c446504010005611810541e4034410761501c00c0c5c0c41906012800034019100840c055405030790001d015004007800d00420440b20700c0640c10041c401c1c007600b60010010019200c003450005032a958840342079030b000c0549401c1d00f41c04e10545142020344185500104501c503c5010b4400307910701910306018052400c41d420380c036507401045060045092210011a40c5801440c1100580d8281c0e64a109140403c0208414070352000005110031540101c0d06140340f401440280700c455282d040c060380314a00080044001c607000030341c200612075582c041c3c6841e4000300741d1b52815595907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 538930170 1250 538928920 538928927
    0x30a0e1207060c0c24020d2c030f0f090402071407090609020c0a2a1508060105071a06060c100501032303040603024b0901050414041b 59
    0x480320440e00307642456190f0340b10f2442181a41500355208064050700c0301d43d1111021035070f03802e038030000c00b030f503401e0100174079504480c0a60100304201c0c819503210015440e000002c09100c16850040c00c0d4020410404076031044800c580e0301d0a51104800e80341d42214000502920038580c0c0a000b8281c00b009c103c58035000031900508843c40c2e08800c021f0107503500c020b0340c20380c060509411041e400c0328202c000807450004002e102000d502e158004028000d504281040000750480e203428103094051410303454019810316005070090038410b0800e00a55100c0c0880a582c0d8800400139078880081100358950070140c1d221070304201c050ba071160000d13450200041c03409100c01d0329859030b161030754598003100500b041c0441c0039510145240c64142a030540c040d5021988419034900c40c1c203a644c448440849082c0b1099800a01300070f040c0300703540010359141031105200044518100007001c2c44c0e030b800100b16801c6482c9242c10210168203040064000e20082000e108402402c02205040c141e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 538931420 1250 538930170 538930177
    0xf0a120b091e3708070b060103020702090a0c200102120109061802031b04030302030705151006080915010612140c04050616050304060302130909080f030a0e12 70
    0xc10740215034503850b5141000b02104804040040560030042c400a1100300068504182510308030800540004020094405400340d54058902c40300c0030500301c0800c038507420001c4c1c000c21309107000d40c20300740140c000403881e030b2024203080300d02a40e80602d10842030148800742d41080071003d00b1459a4803012009021b0b600a000e4000c04071240c070000300d402c1482d482001c0035500d41c0c04401d03155410001c403410080d44050300ba003920b02d4608401000901062005001540c417940c041c58071006245022482c020001420140c10f448030403c12600030700340c01c01d0804070b1f101e83c600b01c41c681e00c82c2151281880c561007540d0f018000e0840021421030b400c055070140200d15118100134460242d200184010010389174401c0c8107001700400c0150b4580b40000d003d008095841c02403401c41c1c2d41d42d490307141d035019520142c04039030041181d00c0103a03440700300300b0002c0420030014030001003035a985541034030402030b030a2140035002c80846d411850700d9200d0800341c2040d400f2101242e0120310031200750341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 538932670 1250 538931420 538931431
    0xf0619170c0a0e10091e0f0f060f111207020d0819090602030c100b13060303020705120c0904020d140109050a06050915070f0507020a090e06070503040308060f0a120b 73
    0x11510102034400d03050900c400101c890b920303604c00170b03420f04209080010007100710440b0340c54115100045010b080620311480100b82d4081300a80d41450640090150407140d2400014481c800305c4014030114041010508081c2880d0035030b544400500c006541580c50002c040c0c80542c022035050106400d0180700701c2c2c45403554607084411980c07283d08a0341d80c800c8103c08403a54100301c5844608004503003003040e020500910420043c41e200b50404110b034490741c000d0380107a014000c20049401d0100c0202111154200540103009142c000f2078080314014100a001d103911462820900441252500ca01c840b500001e00c803403205420102e90700c0179048020760f61145018003181d51f001c8000f03030a4110506501c400001617840e28002e40712101c010803a0028000c2c10881e20005a64001070700016001f031250000740103207548003051034030000030085000e1040402c24071010039080900e071640b0090840724140c841a4040c00714202c4003080d0b200103044d502155559041201d54034203140f107507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 538933920 1250 538932670 538932677
    0x1030f02120f070519080a03021c0c082a0d09050906010905300f100b0604030c03171209101a130906110a02030c0c0f0619170c0a 57
    0x41c604a00e9140c0750791605812500592040d074041200b0309108804150010301414030181c41d6683c1d4402900b0020005005c400507006080741d0842a00020f00c50000f054051910a80f0044960390741c20080c4a40c1c81f200120140c4943d50070040303010381c00104c812001d5a17003928100130303421038050062146030085031700c0340049500240a0394481e0080c3c4045483c005d040c4603a8404485030300c090b2840b007c038400394140030360710a014644400c001654200301035400400110110107000c0f821200b8000c0541c3c45450100010004141c80e18500415203030031032022507003907081c410040d0700b6104809074622050511070400451030f03c04105c80c444035500c01010310400402510141c071001c404801c040d4000c02c00c900004235803410b40d1284010701d1240307100003000a0700c3c441440b1681c0110b0321440041e072000030b00307040c08402403010304010302c01660003c828040040002d0054003803506d1a0786e0a000d2450b58100143c451141182010300642c4480c1d8282001d68010075694031824564012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 538935170 1250 538933920 538933939
    0xc1103041d1801230a1b0e0d020a06020d1710170c1e040e0f031b0a0506090313170a02060a020120190503040b040f020a0e0f070f02010b010e100309060501030f02 71
    0x64107143e020b64510100c5686c4504103508000000b07544002031401034035005105042c07600010b03110152840d000d0100364005101e50804040e00420a00d42d0068034035881a084050102c101c20b504003d205441e081c92149003003d00040e511407501c1c6c62114903540c003954810800b4010089000010800d55094806004003c51820007030ba68a4803442c016880750300402c040c5c03c49284400608a15544080907180d001403e40c0302d0924000303058404031550340000407808407003108149180010038495820084581c02c42503c1510b0f000382100180c000c810002d5082d065030310079805a08180d0001c0c219503e0300d005080b48a0458001d4101da0402e03400a55220001a00440942c2d03c41e40e030040d40c0351410b5803035070f44081c8001b2024a00702d807c00300c411004960349000300304091149400d01103012f110b01d40240001d0080c103a0b0b1185105691500c1020781d0aa641300c00040c2e884c20060713a00214a0f400b02d40100c00400c1c40c42d030b001c0d140c1e0340f400b0004010004607800c0c0d000300c01d0007195207604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 538936420 1250 538935170 538935181
    0xf030613020c0d030c030212040c060e09130f0309081006050a1703091e03030f03070905040c0c060c090f06170705030106120c1b05010c1103041d180123 67
    0x8a10030b024194a03164088010714140d10300c02d0300501c0c40e1072030a24026082900403501c2e002401426902143d540044000078400036501c03003880e00e11403004480601c82810500315080e0322001d0951302502c20717418003218800381030081092200a184060484840c8006248908001c240390301803648199401e00000560483d00c203450b401440000001c1d5103014070240800584000310545e04a000c0c136403440a0b180c5a80a00141219905000845a40e450401c0300144160003d4100c144124503060600c10250780c00419004c03400e0b03010400007110900080c00351006045c5030b00900e20014594800301f0620303801b40f09200d90305000020210a41c45800090b10180024050b0100141c2d80150a5030101040d41041c0d0802c6051b041c032040c900000700c9139603001c4200c408103403260703910703101c448985980c0024516449030b100301c061411b190400c80700441c1c0034500d5692000045180d80811240108401c1d905500d902800c001c00c60200c040c0d842510283c12100c0e040214042900041d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 538937670 1250 538936420 538936459
    0x60b030d030606051827040308090102160809131508160501080601180b0703110d02010b0f040e0705031c08070503100303030c05120c1b03160f03140f0306 68
    0xd0907901d068803030606102e0049650b0581840c1500d2881d4000b1000d05040441c5010a00c000303090751600300454800e00e010309009c0c107403180c01341041002d40c1c8104a5240720990818080005903809a00766588020040004141c010b0303006854034078900e0a11100203140900f10740d041241c9012054514078502c0711821135541c040e070f1240601040288000601ca0b41c400d44d21904820b020016401c060b80e110800101d080d04503c101b2004a4520301c80025062810400d500241000e84020b000c1c6030744410100381100403820724103024130f0715010700800e621420f118000180c000079040392013070090704400983c0c641020a031900815140b01c0425803a5220750103c030710820016002d100040d18640e011001000701100620400006000182100144ac000c031801280346c20800c9440ba03500709a940498140c13421054411b138000c102105003a24000c544a50283e00480b1240840c12a07080950364488490003000c41c9a40005190700c0c000700b00c00255025900c1902c07007000804c203014064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 538938920 1250 538937670 538937681
    0x6110a0e042c07180911041b0e06120408031608070e010507081918050307050a051203070b09030a0e011b0b090106090c030605030c0603010b0a0c1e060b030d03 70
    0xd0490034226421407030b0260007001c8100c0794031050000c4a5101d91345800e401d04850110038072405090700c504240007804051110509000b83c110347c02c0241707146403c00d104044c07074104608800d010341c8112828907a0384580a58460140c42200444149014179054000e58800c0710715200010030304100b02c00c140d2188010300e101d007006446030222a030302400103489a804c046001c03541483c0412010034910707102841b007200c05416440e14042140030503407603035841c500c0f07800c00740c080d034881c0504100b144d0f2111840c408a8600f0380710003d0800f05c1141907400c6106030a009490780503060148142950004003c2008800c0d86e071300e22100c845000011186089141c026049202c1c0074403055000c9800b203506c0d141c200f076400000245031551a010f5a0594103124644008207581c0d0408110b10304041c0400101241b04480b614a0341d810302000e4200d6008050041c4104a0200c005800700160405030040902c3c082a92040411b01c514101019001c03403c0d8081c004d01600000d02441406030050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 538940170 1250 538938920 538938941
    0xa050d050109150e06060d0c05030402041d0a11030c091008010e0d05070312090c06030e1b0a0314010207170405010e0118060c0804050406090212090c010f1b06110a0e04 74
    0x1220ba403441c010380d604204c1001707062164000c400f00003080075603d4620400001c5034060300d841c4c6d100c2c5040d004100440381d2110200c1b81e000111110701d1000708002c250880c03080c0d40901c0c01d000c00c8545401192403c1841d810b43d542200b1008140510244452810400c55450340001e2200311110b61a83d9182e00000301c5083c04503905008500001c0d004070b0320240c40d00311324200050459184d84586000c0c241039844900825550070154000c1441032090003000b851301040243c4007007810000c00c401868612018011220300d10300416640800c3d012603445640042c1d0310403902144404c01a48d682c003034400c440c0410000485810b85500071080a007400c0002840c10031494030b0904281e82c24000810201d490b56802c020100f4503a50b24418079020700100c0c0801078448021201401c0c0842018003064034a0703001c80c04100103030307900c403d050b03400943c180343c000741c1c6002422004049100648000307040030f0929007030900c085180c1000c0c0940e00026543d00e4405150041400304440042e4603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 538941420 1250 538940170 538940201
    0x2006240a03060e0f060f07030e0c0a0302090702150108031c0b0d0605151c0302010c09030c09020d0912020c1912061a180f160e0d05070b0a050d050109 66
    0x1400c2000c02c5003a401614206840825158140a10224641059000c8942003072408140c4140035442e80d141c8a8003d1021041c001400f0140200f000203443c0700c81884020b201d031403518000ba18445c404c1c44005109404d40030145125611601c8040d240d4105032001d10644c0301411040110702814080c800c0204405018041e18082039120340c0003604000f410722110340d001e104810103940f141c48804030500c1c44104031140110301854000c3c2591074001020040150880301070000c22040b80202003207841f1180c006136200d50034045100984070911010b0030702910b00100510064010402d0010301d5001c88000c0e03590804a400555008400c3c042c0b40c000d4041c281d6100005901544070001103040c03500d200075001000c40004803c10030b2400d65001809a580c18400d4403120744400070b40014040c206054011102c1100070080074000401a1080c1c05942540c000d0000030701007040a002e04455299813040740c4040075003150b1000980f101400d03e013000000b02100c0504c91503c130200440c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 538942670 1250 538941420 538941439
    0xe0114100f08040f14030d0f0e01020f0a03090302011b030906050903030c0d050c040911040303110a0305030a1505121f0606020d180e01030b0105120f0c10200624 71
    0x403100301941000300021604400908031101d66900200091f08094104400114a80d4102c8200386c0c1681e40c1919034582a03801070143e84c00d182c04ca0b2064072844211450002804c0856040c224003414543c070445c84c00c14076000c1c0309a00180e05410186c84175010758001d00868440000450356440201c0e841c00204030140500e40078241181c022a81204000134040d003066101c680b903e0448094100d2000b070751400041c100200350300321100c1403a008a580103803a8005058a01034664480280306119456898140e9506041c0c084401406000302904188200103100582c40d80ca01100b0540440550401020703410b82045021340810317604580e0141c141421401d200f038640c2600d04845040760441c8540100d88004800030701402907000b1510040340c0e516040c2884502000e400005210750042c082507100c1247c0010030320f1f164407040d00d0003005a1452103003100c0c020240501c81d017010030b07001384030691070a000620070b008240c2079952401c620300501e0606010303031405291580055259 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 538943920 1250 538942670 538942673
    0x30112030e0a0311130b060f13090b360a240506070b09120c01060303271403010e0f0607081e0106030209130207031d0a060207030b0408040e0114100f0804 68
    0x40949000003060174000306030070390540009022500445440002c1c00800303c2c81600066941035480001d04424030200000201000400d246444080d04c0b480115076007010b010161511504074039000040008009150402e110040c025040c01c8072801440924010414070000342144c41d43e0071070710010b141c0c1e490310744640d8405d496900001c280c903d040c02101d4940d84109002030041900400c00c80c000030307000f82145005850940d140105081e560000c4110603100054215550140c8000000300c20245150000082c05401036000849650180f810718a80c02c100000d10030f400740c7c9060702d40b12500e90f41c0e18002c000008007114004038040ba00c200401071306010b42d00401ca2400c01415640d10303400c64010b80000d9030b00180c01280011024501a180d15190310304240060304101c1d0041811403800000035901c100d5400060041c0861b000420304000c00002250000d25503103c08420540c1d44901c5400783d045505251070080c000ba85507450014420000400543c90a4581620300d480c2c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 538945170 1250 538943920 538943929
    0x1091d040302010b09090a1208070f0309110d300813020117010e06031218061614100e0304050a150221090a0801020405010507030c1106030112030e0a0311 68
    0x80c209809555851103100600d48408a0741c9104581c080000c001d0358026280142500e031800e5603001c01c1125010511540940c002d120350702c014143d103070104681555007468008a44a00d01c1c40340d211103540b0803801009219824070540c02d840303001089598040c20f1566421a449240040000314007400091341d148488000302c182d50300624242e10115140c401100001c0c400f03030041304c4025100c0041100d2841d04011441d4a0b002d0400c41c103040c40c0d42c1181c4824009103514046110728800320f80c07580040c124598601c051900f21003040181520a00e110707486680520b0007400c0030f030818844654651001080b134044460141091035100d1419a4a154038000c8078803580843c0948454801145001c1d5052000c29070240c021b40c0c0d40d0060f82040005a000c030350b002c040d5a0340140f10401140e07030031805071107006400d801d040f4031884c0e4903c6d05000f07040c0964aa6a4003334070100c004500303060004241540d042c8681c4440c4e051580d170300108180d10782c0a202c02810102c0086c003107005400c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 538946420 1250 538945170 538945229
    0x30103110d03020708190b10081b03030f0a0e0315061003020705030712031a0d08040e100305060405010f0b0405130201030b0f0d0b0402040c110307022106040b150109 73
    0x1c3d20595803e01d482c2c0101609003242d0800d0a80b51040e654021014860000c7c4225001501c50440c1400207141030441c030b4a46030813583e4590940080c000d1303d040c2d6201401103c2d1400d5862035800d1340c40c0c0070140301030200050501214003d02c21502c400301412030030341103d4002c0400402d40b000b24010804100c000c5d43c03050394119402e000900c5500b0010b6031550b01403407080d00684012074001001620f181c40c0c4c0202c0000d1a104100e0390000320b01285135007040f601a50000002181c1c55615405103220041d00c0e984020054030501c42000240308065115608525416409010b100079050800c016a0b02c241c030b41c2c1008000840c5548010341c004d0344549060500500a82c0d94140d1520018015001a920030355580081c0003c000441ca081e108009038002682400f0070103450302514aa540d000b6080001e010b1185c04e82540c80e5041c2c0301c0c0d040051031a00904482607494035181a0034070480c2928801740b050380c255071f910f01d60740c045c02450041c0c44071819403c400100340303c1170703421048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 538947670 1250 538946420 538946423
    0x7170d02040306050a1d1b040c0c05150a0b010e01021c09090c05091201090f03080408040312030b01110606011d0a12030f02060603120301052206062003030103110d 72
    0x15401c01c00040051084e0080501c41c0c4201000020460034280b8102208032802d0000d01c203a0b0008411f26002089074132a0b00c41031841540e0024000c075180701c080d50100610600601144580c02c03400308a0120380b07050340d1081a0b0b07010140072040e41c441c019180e0301c5842e010140543c00140c01c440c050703187c0c4040783d90309991510b05074080c0b0355508090805c0700c2c810584107001560000da0f2091505040c401410140784220080049903010740702c11405074042c440090030880c04401050510958070146c402a40d04154809020350010802600800304100c0c2039010960002c42e8951017036000c10407074441d202c1a100c04014804c1c662400c1c1d000c0d40c5000b0040d5010590701e070046055845a000c1e80c40c0b103842074499100030310116002901e0864010044c0e8825444000c41c0720004040b00181da046400540c0c18040c00d101c00c4001c1c0701c00d00072a1080d0a0f006142010000e5410390210240e44400c078000030300c01800484510040d140d200900025000c03100c805d00ca080740d0b0138035941c0d403902503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 538948920 1250 538947670 538947697
    0x54b070201110a0e0315040c05120111031510030501030c1502340e0103120f120c0818010209030601120206040812030a0e1507050a1b050d02010b03030717 68
    0x301c2803000b1000007600300826100003e1444c10008080d81010032108140d03040301c481a08007490301c0e54030100c00441381d0181c0c50041c7c030480401c800b101004d40101c0b001c001c00c440781d9a100e18008a4505082c203920585600c507007000d00d80f8a10301e6010348940d078181c1f90001201d410580c1401a80c00c48104140708400840c4a40f058a111000c2c90300c0456a003010740507000d000c413030400c8801400c54601904541e04d07440d00c200041001440114884284102e81d041911101010800c11b86443c80f02d181d1190800c1e0611410f43c02031548540703551310503c0c081c0d28002040296803a010b00300d01403c101c45130503600c45d034010310195400da00c0d0b4000b0300b840282180d00d000d4443c070480c2e0800340300c100729110052000c1705220800c8610701600e0385503034140c4010155150948140d03038246001404c000b003840b90006074514044e114403001500d0103c00041840d81c00260f26041d541d496412a2080055280003084d910034580401150f10550700507102c0803030300c4a180000640c03079101e01c1192400303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 538950170 1250 538948920 538948931
    0x2030c010e01020c04110a030b150703080406060b0a03090212150f040f050f0304030204061406070201030f06080d020c0f0108100e100906080d030e0607052b054b070201 74
    0x241d45c0c4a000301515203402903511a2201002c0d1805001c1d611150702041c45001003030702d4101f510b00240d0580e207605400d4075014940f604c0e80d0030004020a016005211b4010740003450741000d035010740106955510913144c440b007401040c910030303481d00c90b030241148a803590712021412500c0100c1d18290002d02803055440202c0140d030315585041c110f107054610700d402c0071074100150f2803e4424940181b54103010580030800310800100244a00c10000303043c9641d950f076a500e5803c080e031007030010703180102c01c031928201441000b82da40c4030341c031111920458070f95217100d03595446480740c240698090740c008204541400e044005814000307188803c1400754400c0010f42e20058000e0800803e0804040c1004078541c03a0b0040664050820304040703503201000381311040c1e40c80310450352716414a407a404544950400002c10003829100c5501d40c0d9410082403103100d0700d005480c1c011003010250b1001540e141c0e0f030303829014141c1340030f118101009804000c00904000f440000d40c0708505200004a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 538951420 1250 538950170 538950193
    0x605030c120906040c0503150f0a140c12060f0109030212210304050616020c191208040810090203030307032307090f05031f20041415030402030c010e0102 68
    0x41d2481112440410b9111400340814440014080c602622064000d0400c4143e80945034400071005803445036241c2000c00010405d030010f6000001070b1682c1d0008000303070700b499824001650021040380c0300403c0702c4000318501d86002c0e10b16541c41103041e165800c0003451502008108003d000381d00710389006061405003080158048284ca28203896199030f01c0741030900740a80303044002044841c041441800f2172007420740000340400650700881d00c2e83c0240c0ba200301c6d503c0e01c00c40b9960000100d4001a07801e20100505d0002400549602404a480c0061340003086001c1d00c415003000780d0581c00420200d9100344c4203802c035005072032407445008911603000080c0c900c0400c080364080f0000d03006843c2401024404001c1c40c006041c128014244020502c18003c02140501c031500c0c82c2d240e5911112401c4410441c1000c40d81c0c1400c03040b2030f129580c900c8040e816031000c8207604d110384c00f400001c042254111064078044c64000d8028103058505400651b11240b00498660651040250108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 538952670 1250 538951420 538951447
    0xc0218040b07080601020a02030a08031f0902040632070602040e0703090c05100503010b0c15010306020a1e0c121407050f0705010c030c1b051f091e0605030c 69
    0x103014030700c20440003800d4505804010314560000d00110304540000101c080582e03000203081043d03982140c90f0564a868101100e0f1580d5903210854aa400340c81000062040151f0f0140088400325100c8110241184081c0b401400c0006895448a11741205007610046203802410900d4400c02d030052034a5101c40a44800c2d03601142c0c48070000b070300c0e00d20900c10420031055580041800381e60319410045800ca01800d2400140a03141c520744020a15000c444010800171840b01c0171005081d8032940c40c1d082810180d40320301801f101088415540101b5401c0c440d58580b04441d4035030b500030210307a5030b82e20b00d03601600840d0702c80b08101500c0d5604280343d4001001f040c0f903e01c5840103100e10550640e4543c20b20b4100d50183d414030400c140200082500f00d00c1207001190700000c2200500b0035805403c0342e00c00d02e0740040f9001800c0d142022940300312a00c5102d0700203070f55114010b41642d074070030a8903d403448482c44680d10300b284504200b12401403000e1500700804050250802d1191503005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 538953920 1250 538952670 538952719
    0x6010e0a020313140607140c0d0c0507030215031f051011120319140f1618060306081605060901050c1f05070f1107060c050a021305190b100c02 63
    0x2c544e580c1040c014000c4c1c458002c644004203c81811500e818032031034543c981d4441c4c0c40002c2582c10b0042d0b40900307400b0080180180009540e008003921483c2c900950020320582040390f150b030070f440b560494114048051043c080856070001c00240e9441e1040104480c18025420007281505c103070152404140380e0080514458401c0da018441c40e90440705840c402c0c0c8a207000094202000c2e84107008034508440400e0b54081595614040500184030080b0f65031901c2908099980f074048901290f41ea034903030002c0c021603a001c0c048030743c00c0004200b8240520190311a13035511079820049000c1a50007800502138a02907901600c0d030840441054485aa03403603803011660640e21402c1004035900a07020400642d101d00d031606840071080081d03a0345802c0d500429082c070100d02049003c100c0200400807920741d01801c140324045403a00c440740034040580781c134040b40d031890714507030f0803050070344140f02110200504e062104d0b04454000d0b68101c3c00b402042e81c00c86c1c100110301039001c0300031501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 538955170 1250 538953920 538953953
    0xc070b0a110d020102211504020705031603080f0f07021f0b03030c070e071803060b0f19150c030225120c0f0603050112120e0406121406010e0a020313 66
    0x246e56054030924080b4070074569140b035035030740081030207201d40e600f0845194420550190b60059803114182440b51440c01182d00c10031509026010307034010140d0041e41c15001e2030403070174070040320307102d040c3ca650038003070200c44c1200180d00107602d001c6480d001d141d2404250a051310b00060719149100468115403115820034110307440488100102e4040300501035200b465450a0071000803001901d9180004a2001401c850f8881c0c0100b005070fa6581d896030348501d00180030802d800c1d6600240c4035030f400341d841480744151440040d20000c1d402a101241181d034140d001c0c120003203104c1c81d021284000d070081d01c980000003c03804590241079001c85900940140d813401d00c6207240523080e4542aa26401c800209810200100b20714941701c2e45805101e5031101e8000401d680d100340464149003582c2c0103d80c880c1c00c001d8002a0842c81444d125000b40c003800000b8400c0c18030288080e51000c083c4a6244c5038405100041d10708080d0b40d004d1604114202c11950045503980c4a9845540310f1000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 538956420 1250 538955170 538955173
    0x610051210120309050909011b0c050c04020a030902130c020a140a05060f0f1012241505090a0b010e0d150507030e160807060c03030b0612040b09030c070b0a110d02 72
    0x8080c015446e001204551120058009200705c25072490054880008644071205102d034505140e02001020b1140d00d041c81006401107403100310003030006001c2c110f10b550580c0200115441d50100764418050f4400362001c0c0c5d00180305603007541d59a20640300034040e010206006007090000003c0003404194051803041c003500e0340c04e00b41801e4002c65400f01410801004074038000030001103580b2884011141d4002c034120100200c80e00300d2000c1e6103e281c034072180d0546402001550707035078403000030401c0d1041907031a10050313910b0490480854040104c8507000c20215154029180380160f0341500061107080403a000302c0300182074100b40e9405407590408030341c070b83c003101d00701790000c00010407040c003100301c1c60040c24500004d96880d407030140911401c10028060304814107000340c0000c0c1d400078024010b1a6203c141000034400e000f000c2c2d804407104141c50002c1040c0740340000c10385240e10340f103002401c0e08629195402219511620201003400301d50140d4181c00d80f400d018a6101010540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 538957670 1250 538956420 538956437
    0x1b13170102071202071d2203030606030f020324011202120a240b09060f0c070f0b0c07050607020f0904030e0114120609090307050d050703030506100512101203 70
    0x685180d98450f400c4002c021544004010064504a4405008612030f04101d0110035104e1042c801d04002e1407414030780f109008a40e03080c04044d450350025044880300d50701000301c041d21102c00b105038401a0751102503c212018010b20071404202c16450034041418526000243c0b403191000b42c0c2c21080c030100460a8030710400c580e149080c01401080345003201c1c1d5600705128507100d5056140c55000e408903516000c5004021520740404960079401c030a20395035122145804040d50344c9890703018036402a20502e0001030140610410703907144841104c043c00c803040c2020207028a1741c0000800786d038800311849555503e600e50140c0e19018500980e10a205212404000340191001c2120910014000c0010309840106d081c0d030107401a03403c03282c0b19015120303003a00d1491070064840107031160040d02c82800c00e140c0c0240003014094070945046c8504e07581c3d102000011025070ba80b0501249042100d61809a400100b1640c4040485900510303240c955001800380300508000300d01158103030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 538958920 1250 538957670 538957673
    0xc0108010302120a0c1d0a020406050d0f0605060f071407050612070c0605040809120c06120903040f0f090b03070e15010c0c0902180f01020a0b07020304031a0106030e061b1317010207 80
    0x14600d070340c1f0103480c400540c900b47c41c104e4010700d580308031030000d5840d9a849541000b08411500000b0040000138412034580c08503003010021940442001c43c2d0030a002d0140002d440310205007402141c070b00403c0c25050024000084486030320003000380081144a540d6000092414130072980100d0243c7c0c485916503a600050000304040441d01030a03561000c2844103282c2c0c0e51301c0845040c81c822000c2c0400e6031b181c103480c05203140501c0d0801000004200030105500600b102400708450145205101c0108504d00740360b1603064901942040c0455480040d0408401e5400f9a49005040c50180d050681c2078a0300d40300d40041d900058400e580000c0c100d16400c80048580e031030010120b41c0940b41e00304000c0080d540340e048442c000c100b4249100002c80c0d05009100381c9004641000f0f45107000c400c55065100001c0f001d004d120040380c03070441150050311000414034815801016403a40201c6603281c2c84005410248054a03808500366000c2641d00c0313408a81e9605a00d01c400150300e44103d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 538960170 1250 538958920 538958969
    0x319030f09150e042316020709092904080a1d150406141207081305030409050f01060c050c0f0307030c291809190c02060906090c0108010302120a0c 65
    0x180940300c00d80b01803141d1704811010485061300260100030003d01c43c0702808080e07080120907403241d480d413403400da403c0c02401401e40005008413012407106000c11507041d15400a44420398003c1c040390411702a02c1251401782e99440d90f0b00002e075050000c0c0606140c00540c15040e2006001001031011170304100c03a54201d00307110702c4000d11000240c18100d180d0344102c04000000c00340810801c002c00842c4000c1142603100b0b2089400409a99545840703500d654050082540e224001110103c00010380c1c511903400c050309198088090f1800107000402c2001d44403542d07007869410f0180c41c00010002c3c140f4001d00d401002100d4403103040500e081070144400905801105800600b00131003000601d0342103031f00c000024101c07003d0929071290b071511b44e0001e817400c2500c5c10b15445d103020209001d40000308640310340c607082d08075260340d0307184040b5a490b68803803602103011564250040c4014a45a110f00003007a11120886540c41c0154607003404e0b03c407440d4044a4164861403403031804603507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 538961420 1250 538960170 538960181
    0x9040f0e0f0a11040b0d11010e061308060105010e060d090c05030a0605010503010b01031404081606050705120a060621150b0a0e0108060d060902030c03070617060319030f09150e04 79
    0x82200c08120142170031000c5490324000c0786000340040503018100c0d20700ea00a007440441d411020f40382c2d0751500348503a40032041400d035008507038092240c48000102503120744140c644400001e00300c1810000045a00405000940341c101c0323449880050100301500c0801c080c0c07410b1402803102140b40c0d45400300b810b0071031b00c290581c5030405007050302c8100c005489008158015511440a6640b00c004460401012070301c414001e022900380381c207200d5a00d501c800644126680002e510f0070b81e440d241010000c480c1c403480782c600801c500f160603041100c4004403083c0111030807000410302407050130740805d144003503405c0141c0e41c0d000480c400070242d034429007219224130203003001221070400200041d03407042c031460f00030300480c0c580740100115102807240c10f610b04000b8084540240d122b41004d000303100d65103a20300c2d0b00c5114200081c440d00c0d00103550424400c90110b000b00164058070200c0e000c0c001c80c180b50b824801c81c1e9500062041460380c50403080c515950740da20032600c025040000b03480c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 538962670 1250 538961420 538961453
    0x3020316091a0d0b07140a0c1122020708121003050d1701090f02070b072601150806210601090e03030709061d03030f030a1b0509040f0e0f0a 62
    0x7801c4040e0419107481c2d083c40d140342c094001840b40c4180d034650804944410903150f4081307041401144d03005046800070204512248681104c80d4079800f600c0c140807844110506c03810f8036881012040010000540c01030801501406d0300c10f1520180e000d904d104110180c4070300b000c0c00240401001803280c24006005604134a00d0880b4512841d01c5006815207018002d9200039503a6184102203040d17654100d40322164051184079003440c00403405041100c041e101546240c1c1c8a02903401482d81000c0e21605940210400c0e05244407038660403100781c08020600c94110304404001c01580030740d40148140118000014222903041c107000c00280c0d412004415041d52060092061890308410f021090340c1c000c0c90400354001c80c0111242c80403d4650344107401d400005150f543d081c1d81c0380c1c015446080c11a0091000141000c0d140e00708540d8095070307200180c030621040400345021f0700405940c204040d40803941107500c4c000300b8107014110701e24080e02c0d441290340d5000c00917048171604149 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 538963920 1250 538962670 538962701
    0x5130b040c0303030b1507062a030c0e0d0804090506190b090103110403110d06151e05060705030f0d0603140604020f0a0609090e0f0604031106060d02130b0301060302031609 76
    0x6c4180310404034001c81c1e07030003400781d919520302d0b041044050800700500300c400c2d0501c8480b1401c5074005401402c09031520300c00640701c5102c000c0d01e401d1040a10380201d0380030000d98a000c1c50064000700070800a8410380c0c2c0001100f02120a08850705410009000611440340c4c0d601c510100142c1280d405000055030560306000070404102d0340840d01c02100d4040c0d0700003c0c9d0000350304c0c2c00780c0181447e46181407451820140400c04019905902c11803101034548081115114001c02001e8061308400405c25441040f0042c0da200341c51014209545441a011444a80729518410903441c0324003110703141e5111004010a510344080d010f25210301c03d6400408442c14a980105801114011604002d03110343d8281103900040200c0f02c80110b4070800d44900f8180781c9070003400d030380c1200c034500300c140b2901c0040745075894025200702000b0360041c0b813200541e000c0e040880103004084040c580c0b6540c1c940000002d600c05209141c45540300304513510206050070f8580080710784100794041c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 538965170 1250 538963920 538963939
    0x30102191701052b02130b1908120c010b031209040f0e060a090807050604030906080912030a0c050c01060b09150c0a0602300106110a0203070905130b040c0303030b 72
    0x451311548102c0c034060451440140303582e0441c0d003921510200c80ca01c020b40141c07410900d601c003010260f101c103489100450708001660040708204141c14900d01948006401c00e00c012005591008001c2808910400010513040403013800a0708015a24589110028001550f2041032a0512600e88590300b40d290401201c1e40101d8050f07540c00d030081551083c240e41d580580184107400094a107130980c0801104c100e49468076006002002c5032151101081180c004035921007400b20710060723041e85003200e940c11a51070120501c05003802001c07807000c5c4001002601d0ba030841c2030007064050001402c226549010311014080d40000c0082601d014070402d000044000b440800d4036800c0a4204c0f2015031141c0d104180020f80e8003070091b0403841d14800c800b0203045903054014180c101d9038a61100c520300b030b250304103403620703901407010007581600320700386c240880c0038164031060308040468006059004a80e0701e03420a03510558060301d400c1104d03001003040503030600801e1000380c410782d00c00d2203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 538966420 1250 538965170 538965179
    0x2040906090c0807050a0e03060405012304050607051612030b010f090e04060b0f181009050403081b09060a020a06060603200f120a05071d03030409020f09030102191701 74
    0x10984041c00c42030410170005900c5024512400c46503900e00c10080c1518002d0601e032518a001b0150703800c40d0440140c10742001c008002e01400254400c82c1c01002903c2c0380e5960000894899000c060214100e448190122003c5105401150700820365500e00049613841000094400201001c10008005025105000c190b4010390815042503001c840480e400b85040006009500440d08464014400001500c82c0780a0f803650039000c0c42c4801c64020700f40741c580c180d513004d071481110050081404e2001044901200c0807a515400d0340c0d80d0b00c1035090126240018a80703a101407e6070005a0001d0003040c00c3c00f07001d1091000030000c905003003081d01d203038105044002c009110591944ca90104144405525840c11100d0040d80031181e02d80628248440c400180810340300980080e2a074003401441501248000451081c01001581480c0c50403590030081e60000082618645041c4405049030300c1c240050948807404500041c002c0c240f11078010289508126440200480300c0010007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 538967670 1250 538966420 538966427
    0x80f0d0b1527150c1e060615030403110106140301110a08161b0803090c01020601211a07030203180d0e2b240b0619020a1502040906090c 60
    0x7070020496090314002c5425010001d00e042e00c5045210090040c00103145045440100da02d6040080c2d0840c0c2508000d1058011a0307a41412200c40707410024441c000a107002400c0007446e4811300c20710389440d043d00d0114085d42500c60a42c0606080286010400c0c420300c1c0038026458551403a100322070504003071480080070300c01c005e400418100030b608080120b65105002d1600c2c40c5541c100315481c500a130340303400840741d8421074040015000d9107030818404e602c082611030484680c90300c00010040040220510101114805c40d12041d0950100020b98001d05201c0c0c8a601d40fa01c2c0140c0300c1c038115080015103044980e44c02081c0c0c210070442209075400440c04001428107841c1d1a4181c401c90846065040d1128500b0303d400010001d10340c00c1203100507280b90100d1220301c5a4801e0036505107414203640d80c0c9051a1ba200b003060000f508070020089010a80c12010306c100c0b00350400d207071248240740c6a0040d03d0039a050f00050103000145503401342500070031003800c042204114102005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 538968920 1250 538967670 538967707
    0x140a0b01260705060a09080102030f071b0b010e0c0408060f060306060a21111306050301060602010b0a14040b1e0916080a0e030c030d0915060312030207080f0d0b15 72
    0x3d0b104000120702a550a8071a08180d8040c0884d82c2c0210350f2420080c14500d0307030507411940c840000d442c1e89884601c0c40380e81041b401d0f54179070005641001da401c042406400610041c10046502001d1000040703065007048201d000e03004500c100d400604046c0185820010b000f80442e018510200d02085110503100200c50100d5141c90002006800385c600b8417000307078082c40e195900c0b8405c42401004040a6440b080844000310002c11140d5a075980aa081c0e89008041640c002e2000b43c040018894503018207403649401080040c24405c1a070000b204490741d000320007100410a00c0610f46030801030758041d0802401310454840c107140140c003c0145034014400d84200e6140c401c1c0c13015070481041910301c0c08083c403040d00c0d200d25608001400500020500341c407030100341d105080300d041003446480300317482e0000d1841640c43c0c0740c040190701039445880304440305601004039288810508020b0a504060028003081e01c850b40c1e4200110300845240c124500741d0108412602000500c661 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 538970170 1250 538968920 538968929
    0x111160212062502010605100503060a170a030c021c3e0120030c030d0b040b010203190909060311040c020d2304050d0819020304050306060904140a0b012607 69
    0x11600c2c02024141c1c124050125a4040da0b0000d00001d18021009e4000015620071601562019001c5660705c0450a0104030f601c0414203517000106410b004c6485270800001ca039001600245180c20410009d82c540000c1200c140e0350000c450f07042c1d0108951a6000d52080951804d40d0751a02400300342e4145200324681c16641400201040c09080c0760710780e041d102d5010010000d484d200c080e108205a101d40c0700c030b541401d06c64540f04c0390061300e2410b4402c00301c0704038041c0d00450902c4200035a8803c06820340404509026158800254401e49405090f0203140f01c0d0007607607142a0042e0070300c8103444403415160103540010030480d40c050303032000348050800008014443c5021640c45484054451501f19a420010b4000300c9400d01186c840100912f03415170f014054610700c120422600e03030140d405501c0d819007002c1c01248a5180481c5a1a00a0f01402207803262004250b801454281c0a0700d044498408440040109902c000202041c8800c01300c9036198400c4070524150719808207014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 538971420 1250 538970170 538970221
    0x50c0904050c04091b0f0311010c080c070803130504021206060306060706090b1b0a050706020f1c060501080703060506070624030606030c0b0a20011116021206 70
    0xe0601c0002c100030002c004010700200000d408600700030326680d0350030840d1104122070503030001d280e003590b84008080741c0e0002c88426160b1801e00044804444412050b0340c003a40601244604850510400d00181800002169140340003c0c411100200301c0e8030040c459071041c40021940030040f15000c6d8010012540650f8035525075000500c01c9c019814060115890207007040b0400100c201d01c81d0149290405491680241c000c0d20312042c03007004004400070740305120440000f82c41d60090424503a80c018018104500354a46030300003e1703440d0b1400501038541c94200043d50300b10904071340040c0c8a107000c3c0311250904011629600c9a0140182620f5a4080303c000003098150000300c0812800000d8030079680e01d081c580e005d4100d9000c256440d86170300900003040c1c081d48048904030134bea6210310555240b0341e4000f900241d11030780c862555540700c1480034041004140100702c034032606490f010800c4041c3c0180040700e41903150b072901d298082c03420710800103214000c41959804008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 538972670 1250 538971420 538971439
    0x70203040e1b090f040f230f09030f07021f0302030709080c010c0b06030a0b04081207020c0d23030307030f060b0a05042607060903121805010c020d08030a0504050f0109050c 76
    0x80101d4000d06d089160b013409103151100b01c00860802d00510040c040c041c60301030085445112580e04080010b0300d100c8902d5101300014805c011500015180050000381500b0f40001412109a504141060f00e20700095001041103101c82c0c12404c0c000c0a0503c5000401e94024a000084c0c980c000600c405002103420300005083d030b03a020414414141c0e070003200e04405060515154000b600704540481a079030200d00002d2200d84001518000e007040203010200702e98081e224605d100100c002101032620141c00300d0200e503482007004500502c096a4002100002c2042d424100c4030b00b50420100e071502041400611548032080c0c5055680d22501400c50b848002c00603201c203866140311040901809000040b000d4100740c40004a9000b40350005501c100e0500880f0342e005065000e00c0c0b01410700750140a01c4d4420108070092a102a054050022507600c03403155640044911641c1c0c186c40e03500700010814240036003201312603000e0091000284959496842d00302c101e080c1402189940d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 538973920 1250 538972670 538972699
    0x10510080c04022206090509160c150e0a0c0807211b0f030302070e07170403050a031103040b040c0501020a0c050603100b12011e050a0909030314070203040e1b09 71
    0x2413442d840c218910010b6819680e41201400c900300512810b445001c0400000725031070340320090118a0318440e600e03103018954035a47c010fa40d11410000f01d050303560b2298801084c4008201100c1454022400c61089c0d901d0410000c0c6003c01c1500800042c0da14103255018200380b080c0000300c8280e010129090031041c40c0d1401109102a03808401001480500001455004101c2c3d03002d03a110344a44005507583c101c0140c504407486070b4801c54094042e00064082413049000d0f0110072a1850003140c80000007003492003640041d034059910381e0f07902c4284000c0000301001100240720030300142c0350400040d1501c100303003509071050034001d01c00000001d182000031103c2c034014046080c43c80e6164091001d81c8070f050750b001d02440040465035104401c0c0383c40d084000d0002c84900810724654241000000c602a104a4000320181512504c90080140260b00114480d158035402982c44520300b481d901018500501890448800440402100e0207400100e843c09601940c06c120b00c192070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 538975170 1250 538973920 538973947
    0x10507052503030b030d0f09060509100e0102100f062303060a05060f04020d020a0212093304060507060f05270f0d0207050310060e1b09060f0c010510080c0402 70
    0x5003041e02d64540079016544030007c0d041614104508050355a50031881d46804090380e07140f003110f02c2c25070702040c0d502c2c4e2070184a200d4004106281010700c140c510440d412007181d019148240c080321a0700792100401d100404a240051411b1414a107101070201c21080100c0d403600c2c00585460001a21040003c401c1c0d1190711240c000c0c00c0002c0c008550345c090849485000b9004101c40d44c0050003101c0051002e00c0b150010788007140c4000348aa01050041c00340c501d0241c0d1501002d088521071082d20340a000780c414043c00050195031a840c0d654580c61920104441e11072004890941ca405c05100c042c2842c0c4c001c8010355808203ca00f805541114002d038034100b5014a0203040e48613044004202541c0494000c044900035411039202e0b0f180310069001b5a40940641c418060303000c0c0c006503150f6201e8241041054848010628089401020032401d6100d440c520910400c009070501d0b01d41824442c0d560310a03071800c1086e03402c0d0b0600702e142e911540d2442039680315540204032030080a50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 538976420 1250 538975170 538975181
    0xd1113030501240b1303051501060f0c12121107060603020901090e0618160f1d0c0a140c0303090601030b06040b0f100908160e0702060709090c0504080a0c030501050705250303 77
    0x412504030380e00a680d0b00340040c8d904000740100c000013100d045001c218076005030300601c525603100310200384a425074842250344003040fa0680141549a80c6420b40140350800181002c1d40507550100d405421401030041c5000c060340060203652409100712591000800c072203401090740d401801c0b1202040d140140351903208821040a1802850001011403040070240c08440c84130704d01a01400740401600000103084600c0384a000081100001440c4200010103424813101c0390103041c80b550042c0c1c1c500c3c4d50012560740703c1079808000140103004c1c8029500f81d00c20301c110303802e10054918a000c201180d031090309242c0a8052002150041030003889104050a40300f011504118100c00d40194141154032480002042c00404106d0151001c10118031070328854a45606aa1604402c4d03401000c080310f07200104003041c800801c0b1690b05120742c1c200140070721080b621a03802c5007032041c21601c0140076442841001c01240000b9012070501c0b0060003086034000010300050f0505801904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 538977670 1250 538976420 538976423
    0x180a031511072013021308010c0201020903070312050c03071a0622092402030f1005180601020a062a020d0f05070c05090c070507060e06030109020d1113030501240b1303 74
    0x2800454110003000706c038040342046500310002809520f0120109908034421880041d40507000316109001285149924441540040c98101d142090340380340c142c11500305071000c855100803544281d001d54a0510000e42049080745c2d03074600c1410040714128105560202d5540668031858020148a400094100c510000b03a204010003442d05140400a5004036880d0354003101c1c4d800443d0280501003448005d469010f80860040440c080304001060300c0100280c0c11171046505041c00150039018001191094102c8004402c414101c0c00b04110481019102154807002070003441c583d1111009401c18813908010365500d072503003000c9504030f006401407a00000341074140001a00d0308402841018003803002d03a0b40854a9101c101d414240b00084658448010b20040c031400c842c85d401800b90140700f80c00000c40c002c0caa002603416410081001e2043e618078001001402428043d84680d00f0741c0152582e440310040c0a654121000d902a02130401c801103180100d03615511030140146 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 538978920 1250 538977670 538977709
    0xc0d030e1908010b031002070206040308160609030e12010912121d06060a0b0a080103170909070203041d48070c06020d020d05180a0315110720 63
    0x56860714003142c00303080b412031194080d101d030511b00340541c0034910136501003581c002e2485d0b00c2c085c510745400240340c10400160b00d003d40c0e012118400103040d8030417038019034400e45500e00250752360790421090580740183d0412590400703020f500055001008602d080c000b5041c03855560411850800041c481c0e40041e00c0c1440a054540c000800001000c0b44103000c11210040001e0700c0d0b42645101e03014490410011a0130f400040c07000403020f00c0f0803020f800c3c0428910781028280e10024010300d0b81607911002581001405226000004001441081034004182c006040c24030151940e40c1d41060040d9a1604a19403003661004079000c0302444444030b100403100c10540e4561a9031580590310803250691100d2000840a0012849800391401030300030380350701840e024095403030364402014505207405107084050150b0b174455181003d54003849440c858030441283e000200c514042d241406000248041c200017040081149070044c116003085865055140c00306e100b4209807070807003140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 538980170 1250 538978920 538978969
    0x1020a090521011509060f03030906031a06031509060303071e03020106081005010609060309030527101e090510030c020705040f090b010501051c05090f060c130501020c0d030e 77
    0x10000901350f0b41500e040700c20412036180d50707202010446201d40f20082c0455030180040103030b680a40e00050140000b40410324640c0c0c000784c0003848a034000c032104001d01601165100031424501d8009030f100380180c00651800216880390760307454554a550148510b5a100100b0402d80f003900b02d907000b001500d0480359010b003c0083ca00c081c24090092800065a4220010381c60703220303002d80d8190302c2c3c01d6200c192420600b02c0c82c40c00081410321241041340f031092100300b40e588071100100c004000948e200652802c64408445801121040c0d0034100508480c00b40541e964000000340d400c84c550030006910034092070b040e801c20f921b03984020b60043c6801d8910f910354045403c0206080e00c503d501c06603030b82c2c0351001034441d80180d48104062881c80c2c03550b841d107640a5408245c10074200c00840390362541c0419964a820021a54000c0082000c10fa00031179618141d180310207088240050030044000310041211480c0300c14020b0200001081001c240d5283c01502848101c82d80b03001016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 538981420 1250 538980170 538980191
    0xe0105010e19180b0115080c120a0b040b0a0609030309120503030c0a11070308030426030105130f02071a100803070b04020d0c0b041e0b070b0709180c0e010201020a09052101 76
    0x603d0700106e200401207880d07000001d0054140004456211040d50071214080c1c5a00850030010428402d90903001b81d601d03007414240d0b540c0c0c00000001841a946e607403a01038114030340240b040d0102e61007075a50550414182c8001140032007940d80c455100e0150580b100c01c0c030001101c1c40440030410b11114082c008011091040c84001144a07e0051358107004c7c0d0315014415680f00090140c3c00c0c40d5482c3d003400184800d03c2d001c080400303021040c4d033780803911030703009010700c001c036032140400b20741b803614046070060001c001d9807040e0352010306120b4110310540ba180e04580c881c0b00d1900b008005000d6100005c046658205107540100d803c041c100400030b44541d009015a842401404c0c28039595442002c056424504490161075580040c45e0500c00035548181301241c0241c141004e0052404011507240b4001150101040420f5004519030861000c0500444c500c0391040c0e046900400c2108032844e00b00c1820411a8000d98201c10b450840724406084011201c10902c401d50030582e034810b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 538982670 1250 538981420 538981439
    0x60619030b0a020447120a09020f0d1e210806041a0307121416031e0b130809040c0203040509100608070806030c060408010e0105010e19180b01 63
    0x542c0c0c1110041c04019280328118120191444000c211070320740342c01c5d10200340d0101810410f50f603080346031003800c161001e600940040f00444604036990369425001d429441c151035011200039050783c0c1403514a081d902c5243c0a00d0901000c0424040300e02203100400050450702d0700c040d40c2102c2862103442074001c5c002c0c08514103543c4030388a00d04145210315031a00210b44290360f203c0c000c008014440c0b600e01102c040c0c084c40c0d081541c5241c20600c40d01050302040c404003190001d0145e22043d054210b19203000401e8005030480005540e18807004001002c801003550846031008c2030801c007007511b1030520400e204019015030803a04207845032841d44d400201800035a803048404104a54424580e03070000c1010307110b40340010340414081103900b80901c0119130001e0001d001c0c1d421103070841c404140e0360b620031b500c020348030782d9500c980d40300c103036806c0c40340710b02406072028945050300300342648140c441d1f40e8420403500940d60b54047d9040715447d40544910903802940305076190b0b565055403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 538983920 1250 538982670 538982677
    0x20c01080606040f12110907080103030f05030c030a090f08040b04081e0c061308031c05060109030804180b040e030705060108061e090c0301090606050a17060619030b0a02 75
    0x50100309124007180e5075240107001d0b41c055030303440321280c18054a010300d03500c0d0070021a074094030141525001002562602001320f03100742d10308e485400c41c0d54510f25004058a00024210b801c1040c284140500d0381c2c60700d0704598200c0c1042001040c0f0300800d09010014901c41000141064000500010104040740242c0101c803403407425110212501000704047d0b07894040506140e40040b010180c89103000e00151804510800407948056200e020750351441d8489502c13101c868540c01d000510210300da000d034580c010301c00e181501e00d040c59556116054000c41c001c41c40c4800e13040442d201c140c0070560103504002d200a100340b003626a18101c071902ca84c0400019105402010000f1035480800140d83d07000383e10243c0920000d10050140740ca03000c40103448003015020746e540c110900d0b5400d01954140078010003001619030b181c8402c010540342031b684441010710300025152507650010800769030100f015130b00d101a00f040c1180c0b07003840009640006003003108100c1448242112075014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 538985170 1250 538983920 538983943
    0x270e0106091b050408030a050304080c0105070e1e0102061927050601063e030307080105010216030f080a091701020316030b0904020f0301020c0d0e1906090e041a0702 73
    0x42c002c42c03101000c4111010320850080720400d52003003021444007441071005540c0a40a00c20140c2001c018000300c5081d60b100707961090014241d8560b200c00c1e07182c120b0a10220011311080c10a03040e02d0580040d450b20341c02070804030201c040420108070408686c0104040043e00d0301c0034418080643c0e40032211030540c030303415a001d1081c4000070408a000b16403141f2114180d402340d000a4500b00500301034554614810a0403402803450120f0340c080402c091030240e050758566201542c14200020b00d17040306c40c2000b001140031920100040340b4030107000340b00dd03500850700301c0d618400c1c910241c1d034443d01c03036000c24845800c0000d02c8601e11010350155001e40e1021000000003030808a04400340e41144815541c000c0781d58000c00c005192402007142491009000541003e40d4400300d00e0130155406400400300303101040307460345480c1030001c480200e012581d540c1d412a09000e80100101600d00030030701011f403050003040502c0039800c5411011000044040324610b0207080083d212142500c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 538986420 1250 538985170 538985201
    0x30b010603020412081e0d020d0f1e0f060e01080604030201050f07050901050306040603061b020f0a080703111c09051c02031218030a2a270e010609 65
    0x864081d11034001c480c1114441401040b211009480700b0f0403a5000322045038680001210300710030078081c81d0140420000e00c02005031039180300d05661054030030950500f84094600302c0b0002c1c0c50714244650000d0a05074040c00149880c0004e0080c000f00496040f40070209000070000038000000288540301e20700c00c0e03000340700c0344d01c41000c10203c0000c25502400400c01c24081c2c60615407050010796403082e00100045101d40d6a42c481c2002c5039403c100c0f4a4240750004801903a850701000081d090690010050030031680da0307140c1c000540a00c58009080001c0c0d44141480c0038010050040e1140070b4940d92034a0100d81440500880c031248113907030040c41a42054404d00888280304d449468006e4060229010305002880c4550b01c10401d040040c415103841c0205500c0400c503500c0c3c40c1c0c0c481e41600c001c041c0441c105101d0380c060180075820382a01140700380200300803402640351038182c5950708807070040d12440c01005001818034400b1290300e0700400103040361450300300c1c9411042d800c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 538987670 1250 538986420 538986443
    0x70f030c02030702130f050a0b191d0c0408011514010c050d12020403060e0f1911040f1d060105090a11031b04081f15050f210f030403 59
    0x4505809a62401104802503041440010003508115002400d4034080d0040020602014090101211016285001c000b582d42815403000c2c1416200895807030300c60403040d8041441d003c40808143e4180c807102d050449150003240c41c88a0030300641d40031b0500c00e4000e00c40e000f4028215114088548030b4441a0b480180902804c0d501400c1c2c2c01e07000c00d801c54042c103000500d0321001e4030018000c035601d071a0281d080100002190041c401c25140041d013601500d0a907500461480c5482080d24140000708991600000001d400d810312100381c00b801d03075020074401f56075100b88000b010800140140d03e555050034641c4880049091416141d00704c4261886481b01242d03841210b14503100020f54540c100081403884050441d00340340e10407140191442d003600c90b8011402c0c4080900202e5604001d10b29181c44481107005e0280382102e40c9009502161410000a22201040301d2301401200c01451600c070381caa414584610300a0741c401200c46076541110232a95075840780c230003a1500c2800c00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 538988920 1250 538987670 538987697
    0x7020907030f0b040b0607141e010e070510270f0b070b090f0304030209100512030d0b010215010302010e0a1509140301180b190c030608150106091a0913020307 70
    0x51145c2c0030840b0000d80f0701820040b4603a0f03440c00341029808a5510341c0304405800340c6c0055030f01d101440000c610340011030148a41d00203e0300d00041500204c0c42503841c00740c0380074140c0c1e01c64102400c01c4940000726407440c0c0e0820411840130708542201e494481c1008010401840680040405a219400c074142a82c2c601031520740f02c01000c0703c482ca20307030010442000545002c1000c140c01600e000020b92005540e2000500f8410399000c022203541c20101c2c0d040500241d900ca0609048001e002405803489800768211a021050000078103001903500c402d07246840340c20b2400c0c0681486101d02510010280b8060040003d510a085441102140300c490504041c0240400f04810b016000f00c040550f41d107048000c2801490000c0e0f22503c40c50080c100b00b40ca000f0070003000c02c5a100004c140781000348950621090104443c40e5451510040081c10303802502030084441d0440064411030302c035401e03443c4521030f0800c1c440d40300112312004122000280e00a5000e920540c42d22030400082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 538990170 1250 538988920 538988929
    0x9080d020a08090f01020114090a1e0b180307060c051c020f0a050c12040303030902090105010c030906050c0f0304090c03270f1a07020601150504120f050307020907030f0b 75
    0x445000510b203400500005025042202180f40950014000840ca4032014034090802000c11a45c4c1d00c86a4000002c55051012141303104001018980c000d418110058940f080d41c0305020301742c00701d00b80642c6028140c030b40d018025200e44540c0203105201507104100000d2081d0440882241e0104800c41c4507200c00895108840540201141c442d0508a20750000d444a4104101c0300c5001e0103240382010402820b900100080c40c46502c0c0040c4c5001203005128911105805c00c5040c091781c0107e4801283d0000321040c1140d045250550b40d07050715200c91800c0501c10102d50246110105020070740c0500e80c0c0265000302d096640411580560070108004814808075908207541034121401c0402c04400012801e03902a04450420007c06d11002c9801c003400c44174500181c200100521136002d000d00e8084c81000240740c55800c0c5801c0101c0000301c0d8a02d200010b06d001080c5aa05080020520564040c82c0d0020540761031460882d2028002d40701e020030101c0210b103403040400c1345180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 538991420 1250 538990170 538990183
    0xb030a0e19051002070204140f090105070c0b1302030c0d140606030a0209130f020a030506161d01050313060216060e150a05040609020603091e0105040302250b030709080d02 76
    0x10850b0003040345214141c010300003580107042c02da0308980c403118420030544034a14820300404210044548905d40415030508449001d0500c00421403004601c070301240070006410b400108600038002000c446200103072610007a40303941a00449114801c5c0107009107030080c00030b001c52074003c1d0346465030f42c03504250722201c008200a42c000c220780c1c04942e03880600386100c0c1d0050310500e2610501d0303815400180c8000010b41c800c86043d0701034410415100d094069490400c03045040c2500c8a810f0321020040310043c07550b500b030401c00d0100016006007204041001c0898004000315a2090450f001d0810042d144105882841c1801c406409c1d501c0009086d104018021340e00550b5910b42d040f043c4058170001e00151030803131312100a0000750781e03044021802001800000c00c4084560310310800001c04603c140d0b5000c1c1d250a0400001c00d03000300b81d200682040e14000601c2d2070441c05500740b10441500b0036150201c0c08004c0000854210003600243d8061000701c035200140c00d4030407a039540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 538992670 1250 538991420 538991423
    0x501060b0c1c140f090f0904020f060708070204090b0915011503021b06070302030718050603040609020310060b09040f020a0e060915030f0f0601020f0c010507020a0b030a0e19 77
    0x41c01070080080001050100521078012882e0000840800028002c410381005090044c2400000380701050f0b868800c00c1900d00f548192401c111910301500064440c07184401e40385c0c0150f200244020070407017a00300f21030030603600420802c0900010b09201c03a110b28200c500840f14802d00d001401018410030009040f50102c00c01420b15011403441180a50000036032150802c0517092943c002440074024288910510b950058591601702c20003001c200c200101ca0a80388200c210038005500c42004503548650130440215640c0918404203240c40d21407100602d10303c1c504007001c219940204018030310038404413018008800181c018108901c110f0640401240c05070500c040c13a400c0101c0605160b41c00245012050403000c000d003100d56004951030303071001030781c101044100b0713040104860f08540300303100920b0b00300070b444d01c41c9540f01c10b641c0c40903041c040085041c804550b12101c503107000c0c0c04122083ca46030300380422203001400100c0f480925034041c0c02c0000801c5c0b00e190742100c2102d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 538993920 1250 538992670 538992673
    0xe03040608090a050c0103090320010f050a18020d140a03120b27060a0f14150906040909051906150608100e15090403050c01290f01090801050901090501060b0c 70
    0x20a40010341c004c208c02c0c6002ca040c00a49013030345401c4283c5174065142c3c04140d50011a001411b014440101d13040100b00c00503607072408010484101e002d404908a007941518102044d4009062400b00d11180b4103c60409100d01c0070005c080580c40110b00c80ca001c108003040c440ca0741520108807507400f104007071040551000f001c0fa646000c5020556030495406420750041d152101b1056851100701d4018000c0c0c03054040e00401e16081c0342026090781c1222445240c2489103000004401c1d02c554070440a4090300c401d031850504c80107005a601841c030f02030101080c0002884c1c070710054074120583c1c0c5610500342c140010024081e250203849620004003050160b030030003a2042c4181800307050503901008041d40318600d41c81d8000c0581c003650094486503101c450600f112425a0a83d85000780a44c0c540515006258141040c0400064044907101c1000c1f840340012280e898481e84032035a190300b0b11052000628042d40f1140045002d440240b00081d11281c00d0103a0744aa42d107194421f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 538995170 1250 538993920 538993933
    0x6030b0a0b011106130507050402070305040e0a23010501111b01110a0c0303230c03040911120c130501020c0609040203100803030f0a05091b0910090e03040608090a05 73
    0x4052003a4820212032070141045a0b41c00c0d07610a00d6490b00c41c0448803480046803146200090001c20032040c8000d190481d42546801c0d41903500071700b217005a12034648400701c41404500005041d820007600c2d0f11461005002c03000700010b0b41d01662000b03100311404a042150040705035031012400c007510b804041c21801034010540f00445000d083c1181a403440d0141d82c60300c000140e403840003a0003e40c080e555a00d000000d052030100c4c124200306003821240c504003f2600c60b20004000c0e1000c841e86050009400d10707080074050317444e1080d01e1518804070b10300300400600a6000c80600b0115419890001e011900c9000580c0d031812058a0140c0c08141445852014079258004561251807100c0c055491941c5901681c503603081507504c44030030300350401040141c031003920400f61b012400c1001000d400d00114206034202540d44100c40c01a14604000b6074400c50070038070a0020046040c0c2000728009071001c1c55101d402900036140050b4061002c503560130300000e54800410b0f0000080c1c680c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 538996420 1250 538995170 538995181
    0xb03010209031b01030f0e0705150a020607080c0f0d09060b0d03090b09030304150305060112090b040f05030c0d090e0f0403090e13060518010c1110052e03030f0306030b 74
    0x30304082c1c60030f494100342c0c5030841c40400c890306001c1c074021000c2060013005414100000c1003540328202d05046008241845818030b010360001e4856040080c80c10819150f1316443c01e001101d2159240c0d03202e082c00c002440d4002a181ca030300410700140204010004080744200b0060081000c2d00e004d000510036003070520032120100002c0c01d41a0303005048074506955900c40301c2e0034081300030340701010941d15001c10000e5604102c04604483e82e07008200110031440c3c2c2d50202921020b0f10280100681061000810600b0070072191603803d007504440303910204c0311000700380c410f043c0143c1495882c00d0000c502072442641305a8041c40c0e15407500802c40e400c02102c00300c002d030014080030303140807450100c034042204c52017030a00910b030b804001c1c040f0304829140d160a4480201200b000c11100417010941208045040d110249031160045070301d8840a0404481c840303a5614a851402c02c03070081113120503104100e90840e803003602e45412803840240c0550480300203200c003510002140e400249c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 538997670 1250 538996420 538996453
    0x603070e011803020a0b0403110406060504150905040501080f1203090d1d040c120c090b0a110a0b01060302070521070b0601032405150f07110a0305030315040b0301020903 75
    0x2e079851008160840890f43ca80008180c40107562001245940c005001c0c828410980c0b40d841c100b5034107440a1021510317022008119208038440c01881d9000d0a2001d0a02c5202d0b0a49000070f1100810900455866622182d01c0b00c6400c880c000e080d00c11320010b14291350780740042d00c1c0310302c030341d00050300005101d814292044424a10310413a4003c14240c80e0219a4661261042903170769580c1c0c83c00c04d40d100c04d01c0c9a04403507040104200b4801d103a581004601c02c2c2c07a040b40c1e00001286011200c4042c01d80100d440c1c065a13450041c101c00d00c0500100e10240e0550240040c240504211518000c4000d02d020240f400d48007080159402000000080761641c1c9485411000624000a00c85821f000c40d00c101e1180850442110b5400c0004001c50700c1c005c148c114491101c80034080c0b401c420382c440d03440184140c800007400100003040c1500b655658504007001103410209903596403400b40c1d80940030000d84a94584104c0c64200b01c0c0209060520954100c06d030064010843c0030003400511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 538998920 1250 538997670 538997687
    0x9100912180905070906091e03140a050105040602090307150507020409030528030c17040f050f0a120f090b0d0506040f0204060503091b03062a070b0906060603070e01 73
    0x2003500c0103012000881c80054443c2a106004c07a54886080c00d0410740010840d8500d07a00403101c5106119940040c1c0741c8802069044990040517a00300b00c5003481040c1c10800c000901511a510304810402072007619002410808000c90075220032644030961083c1c090884440100059020b0090b000141016804424094024100542405140000406c2e4501e5006d0340c3c0c5c00d244947d00d204100943c040c0100139007101c00d410880310708651011140002140104083c1007441845e200130240581440031170034000c40c010a48a440c4d0349418146e854800c00044080020780c0d500342d0014461042c2008000c2e98480450307a40380c8003801030100003421010b4001e56006a60346440f41e2140c1040c80100020822500d800b5100d152000820b410480c2914140044181d600d510041e10f0782c1c0030860a500140840f001c41511030919501070241c0341c920b060b08882c220002e0607106005003050b00c4d903c1210080201c2d103032680d40c0000e00c80c21b40070540f4280e0121b84401d140300c44070360180102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539000170 1250 538998920 538998947
    0xf0e06011406090a0b070b0a0203071b08090907090f120f02041d0708070305120304030905091f030b042918190606170106080304050609180405030309100912 69
    0x100342c242031203c00064081000c81e8002803100000081400400001161850b03000e584103404500354507002e034000d010080c5c2c0d00131a04103041d031a401d0b402001040d0050b103440d40c0020300300c844a8604118050610b46890061014419480200280061145050001079944010501980c1d035441e82444042c0018061041069902c00a0348e03408250070044600207054480080040c82c1c41c60801e2070030803020644180e0203076010410080482e070011959001c5810990b01c0b03a6280d628450074000080a601001000303080c0c0030400811711400916480c00b40b40141581c00d40c0001c0b054407603c00482c2c05401100b0900d0000015020014814900c0da05084c0602654078a10b0044441d002c2d00c0c41421045132041c0c0c0d50a03003449040a0802c82103130b04d490200c000c00c0114108591aa40c074010f0340700e801d20a00300051942c40c6134940084086000020f401c48140e941454a041522134100b156440014031075004d4003c0704078441c4c050307854a140c204000c9a255888844102c5000082010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539001420 1250 539000170 539000179
    0x10207051c02103c0b030c0303030f0405070f23010203030423010e0f0f070501051222290a180b04050f0703050c101412091e010b040f0e060114 63
    0x8104000e201000544000c0c144c00031280c2d50001141c5036004104c0f2448011503000340e0140e00f10f000c02c2c0c2c03800001c6917000804a050804140d0361480c09a01d000d0740c1e0382028124049061000a09507955690340c90584d4041c00ca910019500b10300482e540d0000304c0c0e003e820081100d2034900e0310280c107104401203880b9100041050b0140e4914585010601104449654402c9402c0030a085d0184006000303080c003460030394a04450840440301a903006804040101d40b00d9003407075809079900d034140c942c045c0d000d4580c0150407413410148001d0005145071190301d641c3d03280002d5100312035104e0030004019408040d44440c80c07940300e0f1041594020421520b900c0351050303102c5260820849103000f503200c0c1c002091158802e105124441030002541230920140d9001210787c8000c40066842d007041a0741401c5d25903030340c400f5192800e011245403100d1009410502e03500304006400018640c4030654041c40090610500e0404903080110503e0b26a048000103101840000540510108000700b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539002670 1250 539001420 539001461
    0xe160804140c04020a090509060103091a060301200a091406041802040b1b1002030441010e0106080a120804030c0b0c07020102010e2b050c0f010207051c0210 69
    0x50203d07080f42c1c0b2101d40380011800403402040301d441c4c60342e4078a40c024000e1034140300c40e607250b6584030b0310040024190b558150008000440741d0720254090180055000f520300c0500724014054003040d40511036680009003041c034082a00b080d04039541c40292400360426240c10710f04100081c0c0342c00007034808480c20390200000076203042560054003401d415407101000d8000a040004d182007450a04401814014010440862120941c641c0300050615000035841502007060f2200c00d400c00d000e000c17288a8500300c10803103c05600c01c3e60300c5080d110080100c1c503210b5034103035519a4903040c001d1290210341d66828031180709104076508180b10341006507a5224079a0380ea04501c6088402031206640440d46c0b405540e8240560703408104c480c0007802d01511380d0005001d41c88250340015022002c00200b0483c198424001c80b40540003c20070360f42d42c0714846003014040d5005000c1500c2c18868101c1c2c40404a119495100941c0601d8005040c070404c0380345024013400ca140020300c00d01c401d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539003920 1250 539002670 539002693
    0xa0c0326131e03091d064e01110309070b09012a0201031404020f010311070b010f0302030606150909070306120506060a15090b250c0e16080414 63
    0x4048260308644030f070b00c031904c203a410440144044400340c0c1020f8201180c24082c000644c407030f40302c07485442c2140a01304005805103c410405020a80c200750010f17014180b038048040300084188440f000700c14024800d80e00740503000c040a000640d00c00400741c0124004024031130b03c0d0f170002c06002c01b0606144140c20200ca1880d41070304801000003c1d0010004000001c540e494407035420410100c00401903503007891340200d0003500d02e000045061695901c541000c210440c3d080e2520a5400301e881c98456071030300f504664400051208034042c0c440c480104645241481e40d96012060815130103007055112070800000c3c8001622a10505a841c1c0c0003042e0201607075101010320f4006c0004000d18240310040c01a1500282d00500094900140a515199000e940d01c000c03140c5c003441070350f2607591048440302c000d0400500008076001469000080024408011040300d00c000034007180c0d580e0b01c101011480d00300c00b585900003412200003c001803038944405640c1c0100800b1104030040b01d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539005170 1250 539003920 539003963
    0x411180a1d1608010c0c0809100216420807090902030406021c0b0a0504020d020c0316031404062718020c121201050d0f05030a0c032613 60
    0x150142c00c40041d103644014424402e09000c0c0500c556280c0c50304100112003a100c00e2080d00a41454511a0750700c0c03402521000c0c0b081000d0691100010385941919565540c691914404003a05044070152140c801c0d00401ca000e20801c0011060350030035a242152480c01c0740c280000a0542c010f21041071000314290300d8910281d486507100b040c0060742d90f00e484200c02c00505818a036215064148139040099490318007114003202e070281c90160300c8044003100180039024112a98420348000300310851900a001c0c15050054041e49134001100ca030100d406100b4451801113102194031140140d0940780200e00e24001c1c64100301e2042d1030291101c038003200039280c581c49064030396004290f04804030780074454a0500744000303200b035117400841c01d5040740740c2e070b81480750f00e1117910b04501c01020b100c0404402103601c0c1d07011054035980c1c444100068100d0301907101c240d00107080030f011014400c1c0c02504904400304044070400300c6a80e01e507410b14000c40103000441e180c2c4040000b0300b1450300b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539006420 1250 539005170 539005183
    0xa110304020d052a0909060910020f1e0301031205040f0b03071e0e120604120302070201120e0303100b0a09030210020c120c0910060e010f03230411180a1d 68
    0x61130a101c40c000c8000c80c007080b0003448090041d00c601c1e0030040500461440020700310b030a0a000313080150b01e964a400c00d24825015200500c1801007440d14200c240c1c501e8080298142ca1151013440045100a5000c8450b0302481c02004640d511100e02031043e0070301c0308082d60307010005240440503060480701c080c0f102030341c0c4900c04010500c02c42070a0380710f14000d4a0503600e0301107a001030000c0d140540325080448130a05249091541c00148203096901c2181c0d900120300c0340c0382003449003440103041d0903a80e610464000c80c0c550400c810102e1a00302c64000c403003030341c15151390b40707602107043d5003c005200050154400c258812103005940d152107205905a1801c044006440500b051038184105403034000c2c01c10f02c9040d4100410300055401c04450b403000802032a2400d01c00c408400181c0081ca010614260b009220806410002c0f54003c5410b103c0e40c462100002490381c030b007040c481c3e507a190b454085400041e5000003034402034554461420100c0d110407140c080c0d01100011414500d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539007670 1250 539006420 539006473
    0xb040807090b221506020c010909050c0f03150a0b0a020a0b06011206030b010e100609140303040e0f0402040606020313090207210c030e03060402010509060c0c15120a110304020d05 79
    0x25190b40d044c0400328000d00c00840144500d00150050700091800240030a00ea4000c0801312562035010880c034041030001d5400d62070400c0303281644c1741080c6001903083d414519526206403801000070070090207010555200241c550020300e14465030366140069401d0007400c03d410001c5004800324110141c0c0142001140100603020f969410403007050352007607005140920840903054104a07080e840300a0008031500c00100211200c80140000d041d07218562084442580c49028071000303c05060760940903034422a82042002d40d01d1100307030f8a81c040c00c809820f80d4180010104401d50850300203118140c42100711030344900350300d070f000030720540c050091000084000f81d11008040d007244c0c404107460f07030031002040e00b85000c3d800249980b00c1c025096001d104007250360b4911000030000c9040d04000200480c98260034070303601c40a16044030b6400070040c0044408180c0c580c140b4072480102c04015000306e861a92103401f4440d101c200c0b110119454400c60300c1e42914041140040010354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539008920 1250 539007670 539007739
    0x90b0f031f090b040b061303120c050a140c09011410031107032105040b15030f070e0a060f15110a0602030c030f010e06030d1b05030f030406060b040807090b 69
    0x41d244800d00040b103000c00041d0707014200c10803402c850321f8124031014003182e5014680d40c01d003a00e01c3c0005c44600c5d04217840100315101e098103100401055401600c00500d4400072250b05401450410000510a02c14010003010600180b050783c2000c1e184400d58000b035041c0814403d44026038950307543e010420960011b08000d220301031028442c90b4024080c8800041800203080c540ca0301200c0d0350000e070101c01000000120740740161400d104059081c64010306a9000c035988800008594004658014441b40792020206106003d0f1080d10709468030205a8140d101c5101020369803400c1100302c40000c2d1107910300c2c14001440754001140b149241007011a180d0602c070200c200c10b418181c00411104041001304600da071400180c001032880d02e85040d04c020198200c1c4002d6031307000c0c0100a4818000050f40044d9400420000c60013644a1402084203c4d0f6844181c212801180034040064020400811000040703800c506d1400d400108a283d010212945d058041c0420703400b080a030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539010170 1250 539008920 539008931
    0x51606020105070234030203010c020a030206061c02060c0304031704181a4606030b01300c23041214010608060c19090b0f031f09 57
    0x28240e0a00445421140e680000c281e104154102c40ca442d9402d4000198611000e140c2c4aa40041c40c18002000759009070081145009042c0b009440f804d01c40d00a8015203d0940880d4142c01d00f8000202c051aa41000d98012a0036608100280c2d01500509015120901021000c1600495048001200510100c0c0d1311032801004c01c280403480d0800400452800301000000c00d992040e411018104541c02481144010a0001305481c601c135400e0b0450b0900724041d80500e442a5102d641d1075184132a018065500d060450907580c40e501e120780003841c50355001d000404045051003031104000140013141c1c07091103400c0c080329404010f1070001030045140741d40c0c0c01e01ca0041c4503440c1c500195014a0241049a560300c500d6071110001d1548000d00d010300c990307010039401000a410401d0681c0d45906080c00004d0640c5c0025415100c1095a41503001c900340c000c006200c215200d0403c4d030741c10f01c87d003224a1200b541000740704058402c40d000100c4c10400043c0742c039102404141400040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539011420 1250 539010170 539010179
    0x533190f0807020a08040603020a09031e030306080304060f080406090218040204051b041403030903100605030d02010b0d0803060f0306090d0908060103020a03061e020309031b03070f120c0516 84
    0x8615005402c00055400c12001c0001040c445012201a15480c1c01c0150f0303075074011601182c1a0045a00140241d21610710005100102a041842d1a400317a40d092100e5a10307000350035141d03c00c501c60b0101264900b20140031560151070055485030041d800012401c030aa00895904000d00d40021105541c0c1c2041004602c0c0074403a0540000900050715625090038071142070340d00c228010302c41c0f4080000715000c0307640e80070408c6a10390800523040d02d0b030310070f461384c101406411140503041c828040c005440560510510900440c444010583d20440c0030940720006203a00103040d003500f01404502d1b12103e501c0410070075008007109030080a80e0b6680c054001d20482584c0c0261105402c10383c010005a981c0f00e41c5103054a0b0000e8000800c0020141d1040300c0c198141030b002901030000c030400c084018044003403d01c4d03120700c1d441401c102141d0310721251a4071401500400d000b50f443d0030000031505070003000c803e04120341010409265152200b5281000b034845400070003441c1c1c0c00502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539012670 1250 539011420 539011427
    0x1911030c100c0305060d08030a15080a140303040c18020d020a1e111005090f12040302130b060315010e1c2904150b041e060533190f 58
    0x481c0b000b072442c00700598140800007518000c04920064503c1002102096046010341c0c0030790302601c02c074100003000381c1e90b4004440c0c403140c01c680300f0b5072841140ca107080d074101c01c04030459208507840040201400c1c2485041c41c1e104000700f4000f02d849900b40b02299642c841c52005109032403450707d071200c0e2828289804d4016007114035040080104540306599100d20004c1c0007d02400c0c8039a010481d9550118000d10706035902980c1d08241c4036000000308481491002441640e00a4540d0240ea0341000307100001d964041c643e40d6007040c0c040000425110000300301c1100c0d980c05240c0303e891002c0e020300144d501004030b1031805646a20001c900100021000401041d41c9409641000004c5100654490400092001d080d00000f0380c3c0403006266560301045800ca8014400c20a54803506108441080ca508200114914206d008078040c80c0c00302040c07101d81a0360128040c513107640c1080008400403502c2c010607451081c01012410440304200c811800742c166a100f4103600d40b0203005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539013920 1250 539012670 539012681
    0x1206040209150105120a0b040903110111121501020709060f0519121b0506030f15031209040b01020304030c032f060301031101020c030601090e01110903031911030c10 73
    0x68404604011004020781d8015080c1c8100742511120700003e551ba41e5484006802c0382c02c0090b900a1500c4010400c050f000b450784d02c980b06595008104604801c02c071450148104603591080c10003c600041c2c4821101c100d812202d0010300c181e48000380e840c000d07c0c003500c406403c400601403aa80c0140200e044c415500b803801b150395403181c00e0300f44c0b4241d81c5500c0c9030041c40000e0a14844501d070f48130b95403100300140004280150050b0750741d1a1071040c001c08000140c0e014510500350b0070030a001c0d8900001c1140104103080101c40c54011072508100090040700081c42c10740c042848000b02061f0500d6200e002140580002488104141580d103400804e171020300800340382410000200c1d0321030764281e0f03040d01c4c2e1000020850494640044c1e1501403039000c10384e458458440003007031140540d0410150300c2c290700000d02c060903003910042c50b207010703859000b505a8000d000440002d2500110421403162600384a0000c1050007291800d507400186181e00c0f90340040d402c920700c01103902c00d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539015170 1250 539013920 539013931
    0x30f0601090c18031511070b15010e0306060907030203090111030a02340602070602071202010b0301061a07110f030a0b01050907052503020309060c07032a0e0a0b1206040209 76
    0x1100c501c00d05660b0b41c00c1c20465918400170f8070b2581c41c08807448100b40072045500c800d80000f0380c0c428501d000303001003c2c0314506128042c000744602a0351040343c10001a0395004682c010007600190340c40c1c0b80214020340004280c0800b564135030f50b180d03188000080c0150b0107408001c4015030b41384024510b00103d00c2c81e1000b2402000034480100450a111001a4030150307480303280984e407540c090030700e0300207401011400b400035500000304002840d0150311041c42d40da800d4000f4044181c2e24a14281c40c400344c1040d81d500a1010172540700001c0d561880c21000c000014a01440c44001d0b00200e40303044159001210100c600d030005018a03d00608140d41c02181340c5042c40c03030010b81d00c0c2903c0c079204800c003070541c041145544c0c40c82058024800d640d00070705c0186c0001d0b01c0c0c000c083c01e4544d941c8802e203c1503c041c0b10b503500e83c82c035551443d8141c0c680e040d0800b0b803810540d441c007005075041400c02408141611740d5035444c001a0342d0744560445541641c400242003e061034010445040c00c003404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539016420 1250 539015170 539015207
    0xf050a0e0603030f070501020403060f230717040f0506010314150121020f120307020a0b120610090f3312110c03030408070b0709060c11030f0601090c 66
    0x801c0784035076001080322071203280042495250180c07460100c0c003a000359040101980e060141104012185074442d01407017500c8203c105030703089001c5600500b25000e031030480000d0a801000001065004403454101d44108214117400302c0d980c40b11400c202085e0021100e81081417081c2c9031965041220106921100c9045495545400c0c220303000f02d900304400140f0010740c8082c071400d40d556040d541d101d50030080c100891058614030110b072603074848002244a2900c0c188007145000d010b01c01c0d03d030845a5907204056507180c18040018031071103452000301300505400003080450040c2440e0005000401b00c4034207a40592040710203280d00c251034120a02c14007280e141d45264090811903818221840016081c041c032030148a0a00c120802c83c89140f000105000400a00c003009051031070040c04044c00701d460383c240840d103501961149070006245401c0d25004541500d0003a07c20700c00040403111200d0125004604108003640b02d00c6c01c451341d5001076410103822011a401c03ca41200c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539017670 1250 539016420 539016449
    0x222150216080718140702100f06030c09110d020d090210020a030f0f0e0d080c0613080d050a0209040c0207080708030406080c0a2d1205070f0e0310060f050a 69
    0x9580390b5200910721070010101000d0011401300041075018041d070900308102c3c050280b51180010755a52081c160284540c0c0c030b0b0425814075180d45203e00c105403603020340d8205426160462850190101600d0700100c20810488501440c40920091500685500000c174100c01b440c01005252404404400c0a64228001880000b50301c445001404c01c01d60030310540180ea40002111141c912050894121860107035a00c24402220007624000c0380010884a141e550f9503000c04803040e1050300100700039810320940d81003c403241c00c07141e0700036080310005003030404071070020f81034607002040d01025800000003480034440a01c6050003801007180150300d0300c1d10300280200f26100081811010700d5010400d00d07042c501c105500c0c910101b05103a100030318404662450280485480325201143c17000042c4214640c050090030302c5590b071506c2d4420102c2c0015415101c1034050070059605001d184219030101c0b003a0301c9440003400e04002403091944c10b020502c03264107140d401c100201107008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539018920 1250 539017670 539017679
    0x41502091c050c060a03060305060a110d27060903090905100e0402060d0504051501300c030b1317030f01051908060f1608040203100222150216 63
    0x603107940908600400807003145940c0ca08000b4204003030500016840000026030030340150b4550002030940f801481542d46640740e82001c1d41c202d03148024804070b003c1c4148100c038110413180d07014031100e401c910fa259005d080b03000e000c00b5007000b58250880d803031540e460300441816400000d00002d0807800c0002c00181c10700d0b03042000c1d0a4a544606000b480c1600300060071900d0345816030341d0350f134030302c0505015a04092400315242d640b030845040303180b8610300000a156131060040e01c49001c0c82c4200f500c0c203034a02d0b407130440c40702e81c040c40a59840d05050070010000f4140c01c100d510400180707911540f40040d514001401c98120100302540c02c2041c014071800038000c4808504441d822112907403103941074100c00002c4407403940494590b010704010044004d01c1c0c001840d00c640c1035200403c030b665108010944c3c58000139100690180c0c8200061000202142e00800840c041803221800c42100442000c6820010790170080000744500b9a081c0d5082d010000440d00101200040c0740503420b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539020170 1250 539018920 539018929
    0xf0e1f1e0504090b010302091312030209010c020d050f010f090b0c070201110102120612010e100b12010906020d060812030c0a050424020d02031e07050304050d060504150209 76
    0xa01900e522010510500c4a04000c55028a401800041c2c410f01c10b40040b42841d01a0401c240b0090f409808540300041c10351103081090f416165210000055003040800114000c1d04400c8000c5e061250380040040580d4802050b52060740c4075400422181c24211600ea003903820402c5907410607800c0007000400540007400f103681c03200c185241c05855030440c0c00126441d6aa031502c80019510000b580c1d00044100001c09105d020181c6444c050750030322400103402c8400c000b040c44225080340050038000c003802e811414100c00f004004039050302b00c0142d03040c2160380302e907002c9809070b41c0040d0b5006c601c083c40c041e01000300b060201900c00c1100106c46656584402001051800000104240d0203030062084e600a04212103e841050500d815043c8650749000702000c058860703902c21144180c4004122000c2c0445030400070301111903503075541c5460b00300b9482120140402e11000c1040c1e281c00f942407207210301035140402d0604103414151081c0001c210220340c41170041104145a465 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539021420 1250 539020170 539020231
    0x1020102070507050f27040b0f04030e09192f07030504030308060d0606080c010e030d02070302012d0503010911070c0b1c05011502010f061a0f0f040f0e 67
    0x1900c000000e2040500041d2150f80c1408006e0341c00e0000c80844510741d0607103070b03669200300d2192109000707a07241c80e8a041d04192045400600190200402c0351140c01c240a005403c408526601d041007000207000d9016100740d28103406031481110740144500160132000003b05c4881c5c0c920300d1805000703490003001881640405400d200103a00410110784507000d0340600300b03800510800c420f03611411540d84403c0d409420a0000c0c0c0d03c0700e0b100200780b902003030001e0b0740d01d03182c1c0082401d2461940199071402052210f1428811115450f9035060b00c03511120031348045035528079075030f5810081e00c44202c40c50414909407220060102c100082c84080494098902e480a21502c51030707643d01d8080300c10a11040bc1240605020001595800c0c55038400c90b00812a0004c0c042d40c201a40a0380842c0d00a11810b490702c03003441482c0910301c6030200100310004040441624101e102030146079140d01503401111420b10028040044600b000445500006214140d09040c100a00e900d0b1180381c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539022670 1250 539021420 539021429
    0xa0e041d150601301e05060a080303011a09060a020a1406010b09010804050124050a08030c0c04020c0312100315050906043305010e160212030a0b2d01020102070507 72
    0x700140200d25415000b9003a0b00994035500c2880300305c0b00c28103075025002d2411045501c1c02c0c24280451020b10703118940105a0b80d0b4440110b0840c0c3c6031043d0020141c450812041c41c030b10041141d010b1a40b519001081c0300071640d0001c25900c425071600090070781c6040401032640d0003190040c090f504901c07044070304d212000d1800300256200ca04000d40189500aa00158006105d0220f00c0e41c108088040f01240c07402c0720306191131075480c6401526407048031a440e0b0544c00c800b480c1d605524080d03000e407040042e40000c69080614450941414034015164400b400d0248030b130400410a0460f11030b501c00c2c0e84080f0500c039a0401e00b221035911341d00684020803609800300da102e04034407007151003645401c01b800d00b00e690034500c031881d07030003090300303008200800c0145400640104190248040c0c1203101d64010000d1070400c140d260003c4d0006000e10030095180c05014180796994101d00e201060011211107281103048d0601174201c6400380224150390050041300c0c0460301c0800c0c5c050484 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539023920 1250 539022670 539022707
    0x2030c3a0b0109150e010221161109071d040b0d03080604020c1e0106060509010203030c130f0314010605010e01021908040801061e290a0e041d150601 66
    0x91150300c0165058261600f040070340ba044122424000e540c408003491717990b0001e0b02a04c01c50034190341022074120258102c100500c10411480450108000c0000340380d600030708542e040702000304001500c0c007000b9640e0300c00094502d907402e82c102590303000f0003ca4600807101002050b04080c042280003060440c094240504000014095100ea4044484000d038071001d076040e140000201c400c01c4441d0080c2c3c0d5219601c0d10201003003942c000d0013100d00d000c3c8140c0055065030b650b00c100245503408042e0407139404403d802c0001c1c0506503058200042c0d44a14807510f010345041c0813003401c44a40342d212504005502544041a036001f0528020880c250b50000302c140c0401e08003a0341c41d2007907500c509482e41ca030010018031041010340c02021b40311032002080ca0315985219100003a110f07069442d6020b98000240411001e50ac001040e1098090401403d071303005c0c2c880000c0c1140d0391000802d80d09107040c182c0700300c00001031120000c00400075081621508020000a003079080510203000c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539025170 1250 539023920 539023931
    0x302010c050124032105090d060b1009062d030c03181a010e1005060705100c05030108070905150d02031920010201050412031e02030c3a 60
    0x1d00c0400c0d0425110001c10b901c00684450400c00c8800c0f0140a500c02aa0030030801c5c01501d91403002c1039226144e040450f40c45a0038030486030b04104a5000c0e5000c00c964965903014000a15100c5082c2d5035500312040c2c42d000416458800c001e031031504070051a072141c41290300c00e00810181e501078441060074901c2c0000e401141044142c0080c902c400700d105801300703903403440340c100700342d03408012421104880c1c0030388240d036103681c04507e290082d20280c00340300c0c00c030005101500b05440901308250150b001c540c8004d5181c80c2010031181f01c4120351000400000041c040e035501049036000500030200100840d1508108010014040100c298421402d03050401c040d035808005d201c42200b00102405407c90311407400c03a00595865101c02800c40014000184560040c40780d00d10840e084042c5040c01c215268040f00100f642214071090980e080e800d440c071403082e501c0614883d1495025003503440b2941140801100100030040c104800ca01100c0d01740701100011042191104070303008140b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539026420 1250 539025170 539025173
    0x10b0a0e07141201060e1206040803040314122d01030f050c0a08030309011503020d0f03030f2409060b18060f0706020904140601020a1103030c03120f0601180302010c 73
    0x2840c000119a04811039800b090785a0b407843c50308903843c101c540580391650051114000c0c401d44140307011403151780303422090000703010401c800e0045600c10301c245070008107000d040c04490200d800c0811041c490013101e000300603181c6c188440c1c0d070811007882034403800b1454981d015024144d81c140401001701d0500718101c42040000c00c05401c3d1040b0060000080f251035a0301183e4a0b08100c0700d0501b03541c01e04c050014400307020403806040e2600900080e10702c400c1500d0f456100c10501e0800c400b01943e071041354101310211310544450706082c10500c40e88900c0109802c4031050f4980110f001c1a01d4a08100b001c0d50790f940440c1c07031111071180d080d4a0425403000041301c9005500240d100c54400050350810002994002e241c8804203c404100c01c0b003820003c1c1041d070404032803060159004280b65400b20390900302001a00708001d088038038102c40003550505640000300d01d0039580302c0d401c044c41078180d010304686511040a00c1d140e07803500c3c1c404116200b0300d020751101070306002c1003440800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539027670 1250 539026420 539026427
    0xf09210f0d0603030c060609180b060d060c020a2001020a030c1a0a02041e1503020d2a080a05100e220506070207120b041e050109050d030b03010b0a0e07 67
    0x1c9034030aa0310810001c0990701e06025000b101c2c00301d030440703000e0f10704240456024014803404003080c0f40c001510903041003039510000264070141c902c80e440304096007824002447c501031038008501c0340e8050300d0b000d000703481c00c204284031001c20b818090304102c21508003a640014207a400c680c0601c0c14441488131410850329616500c14102c8810100340108034003881c464004000b101e01c02403600c580d00070b02e9840c04210321004d0040c040714294103012115507034031a4014110400ca0504e0003d000649011040421100c003403c0241e0070402d00e040c3d0148541241d8442d60203001b900040c002441c0100318800030551902500c83d091614202040782808003810011400c13215a502c00502102c0d8240f8a5544004940780e0005109498010500700c464a160f065051352081c1d02c0035164640750307900080c411007011100055071481c0c403540c0104009001da07022150141c13014080c2c0d803d050344018103036510112441c1c0241c2c100392469080789c0750040080104d0310305910845103916502c8086 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539028776 1106 539027670 539027677
    0x1320030606040509010f09060c0e0d0302030a0302071e050c03061006090b03060d21170f04111513080c01081009050601051c050f09210f 60
    0x15407604040e0000c50300400c0c0b00001040c40111103550390121514910155000f0b0740f689003c0701500c0d0042000c030f2206c2e9082d6410408420a0344002c0c0d5a4422040704204060b0300084101c00e1040400d4081c050414402050002c00042d0078240c0d590920351100c0c501c02e00452001c5038801140000c08406c80d1102d44803a00c07507a15041d6919840e0b040241603a80044003041204002a211408001000350a0141055044040b44002c00140c0c1059801c250401d4035801d0000031840320000a521a0b4080040145103801d2b0002c5980d10211010009072150003080040b0041000038402c8140c0d06840c0031922111501c80c01101c80203000d985807001c81c00045000e100e2030019401156210006040c681c0c5800e00389031107000511010b042c4640c107981d0710710500140c05900c80c2da040d000044040280051000c60300d07244102d01f50204c3c804c0703681c10002040d4015841c0c40c0140c = true := by decide +kernel

theorem cover : BRFrame.Cov 538848920 539028776 := by
  have h0 := BRFrame.cov_init 538848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 538848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 538848920 ≤ n) (h2 : n < 539028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
