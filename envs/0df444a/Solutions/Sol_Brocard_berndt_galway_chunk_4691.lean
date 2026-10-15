-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4691
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:25:39.532817+00:00
-- url     : https://prove2.me/submissions/a470dc0e-9e87-41e3-a00c-d509ed8fea7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 843525179 ≤ n < 843705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 843526429 1250 843525179 843525181
    0x2060115080406180b0604060902030613050c07050d0903150e07170a023f0312220507090605030706021c02150a090c1d13050f0d051e13030803 63
    0x905080134000d140080b07500764000440c0320b418490308102d00b9018140035641080f5864545500740141d04c03045840940016001000848116080d4045580038501c050114100030150b5500c83c140300f008070007840026014601401400031010840c0c0d082c0310b0601c402c0006000400400340c51712150710a0f004010444c41154095901c180b0228045036030003400031080d07000c0c024000c40081011050000c126000c000c0c3c10044641d64054121154160310096081c03034186407600b00b122074000c1c01351185185940e648a0700d400c00d401034208083c8240d002e0440a030604040d00c04035071040d80001c0c801c4d80902000c1120b1600070079003881c4c2c580140c0241c1040b85448070306903d4412051207203500038865004001d0407010355849940d549218000007142c0c0b03995000c20021006440e600721088448207c0480c07030a002c01114111307010b00c01c0b030585a46035200d0380c10a080c041e4a20030100454400500c240d85034421504000c0030405002c0410b040051055403e5201c90680c00003d180140c000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 843527679 1250 843526429 843526433
    0x30c06020c0d090f0603020309071a0904111b0601060905040504110604060c0312090b010b0a091701060503070807030c061407021009032009150f040203010f080d020601150804 77
    0x280444004281c4a401c0714003102d50140c00902c0c1c2d503090300c110355000720b2880f070100b5030b284a8022603016180c1d54005007805824424001903d00e1408074220514004000c000d505464034080d203449190b500b15450f4846030500c05154030a43c2c40341d0701c08902c0d00001d00510100c0e41007070602c002c2c2e44065030b001645903110b16248251407510300c0003540c0b1400c081000140a50321001c10440750348070366500208041d4070041001519042c140c01403c42e01c411005002d900351001c040d00144102c1d02d40904403130341d68040c800c0510680180780c0c0075030351550700c103109078202000190000c1407150000c101507851911101d510380780e0744c0070b440704000c00c3c01c041c0082d04140301c040d16070362034008208841010b0542c2005d000c4031280d202c00c5903c0b03c500200306000d180910500040c059010b80204101c1e981c20f101d400404010280c5254400da904040a50300c0c1c4480c03001d10f010303140a500b445402ea003411000c621f0281440c0251045500090040c09003090000841c070190183e0706103035240e91117074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 843528929 1250 843527679 843527681
    0x30b01050c011107020307090510030807030e1009090e060f130c32010e030a0201031e0908070b1f030b041505101a07030215180609060f0f0f04030c06 66
    0x1c0210505698246540c603003820300940020100d8034030880440782080c2d5101e08281c15108100c44100b079030000e05800b08003040040000b0301d0381e02c0c468a4074071116000d210008402ca8500f2002e20000344002d1020b008609881c07058040101c01c5a000789031034504084087e075002c00050803005500040c2c800c24040241f58404000a07010084070a003011440c80488a0207083e00b541040d030148890a016a00c3d50041400112036140500079040030f00700c07070300150060440300400c003580f0008030040007180c91031031059203100c80c4500d40107603942485082902d21070b0005426800c0f90301c01c2030003060502e0b0814450104136540035904104036510f0341041d100084409041400ca03078100010411800c0c207540200c1c0954200c009103e003058059460306a681c0640d490007400b40e0b00280507400d4403c0750300c0c6038661140c11500c2410514460017816402c1140c10385444403194803070014025002d0320310017103a9006c86201380252003480c01c6010030300f4289020300090700b130118140c28913040c0649 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 843530179 1250 843528929 843528937
    0xb0c070b1803030d050f0709150c030216061707081e04020d0b0f040515010605040e0919030503090106060c0f0809041401080a030809120415440106080106030b0105 72
    0x4010150f070b440f2078400b8110f0f000351004803030030840301481c0c4001034030b50f9005d401a101a00c2480c00006000008803500743c51400950000360158400c0481030010b81c038194000c0300c080d20b007540d5201c803104042e50380a090800e0241044c000d022000b000c1085200c0025006060765402c01e0002080d42c031140040341d4100d9400a000d8240303c0d19204205003222131701881e50107180f04001722800f0061001101165040a00560300055010001001050003400c011504403400d5420346200d031140c98091a254145218110042500842004003100d400c0c800d6078001d049074103142c2140741480e903174002a0203e06000411040c408a450f8446403666030200c244050040040f2019584440c88a941c440300000c0450006008400244426074003144d03d082100100c4079260409050848100c7d6121a1482d03200402032001c00c03034590711400305401c0c036507038422840390a4101c41c180d003a080c4419170654409883c00940004120150344402c042e4112451460006504c120304401201c0d01d1007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 843531429 1250 843530179 843530227
    0xa0b0430061505031c120944070302030f0a0e0a03051c141e130b0405040b01020a030f030b220c020d020f061506070503031f0b0c070b 59
    0x403400400b07003141c0104025000030b460040f800c4403d401003482c83c00c11041c0d400d0800c40c0c00103042080a03d007801941e003000c00200e10a40d00a650340d00c0c2208000d03000181e2840b00117558025420510161041c5600b02c1034580300481c0e403518100742c54602940e20b1241e82141a030004000424682052041d048088800802400480d00e02d40e641071046e80c1c2c03d10000240120650084c060b1070345401514442d400040c84c5c0340650034a403102e9403d100601000b80d03001c03071030203041100c1032298089800c900060b0500001082d01c1c0c038200802d1108842d140071003035042d9803100c1e0004011036009505000508054a00852056420750102d05c03d181c98440916440309450440b80f03509800e07400c046201011035013200c580b000170031800c0340d0744c05407021881c1480d0040b5001c18101010141c1520a9410240010703242c0781882c0c1e149481d5074021124a98898050560f494045a480003004003c00d00d809100c0e0034400b000b046907494011512600d903451800007400c6001401d001c400006d006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 843532679 1250 843531429 843531431
    0x3041a0903030c0d020c0a0e0114031f05010e070c020d060c0e040e070e0a0b090705030603010212090a0302120a05041823040b0604050709030206090109050a140a0b043006 75
    0x140e90110000d549048110304d000140c0696000240c090804504070011942c52900000203a40303040a0608000120f500c0d840d0140650802d440f02c681c55803411501c10145031034005019898000d82050648000d88200c04114040798054056500e98075510301703141d00700d00001400305480200361125005c410015070030600f07001000156080100e01d00003229140c030580903040da14403031103400720351940f9030450380002c000000c6010648110702075a0700200180006280007902402850107c1c0c003140d101a081e401a01c41400309681880202c0184400011560070301010000150140c0224024007030003182004800c01c1c1c080395a08420505a0500c030742d40007503400c4056152801c1e000710f8003034030400e8078000811001d0905102e164420505540c4d014440c074119801c0060640c4a41d500d5410400901e4001c12169a0000304000401610354850102c0c0c525009100070601a40c0c4180d082101c1407108010a040c41000b1400d050700c0b00402101c1c0c1130860403031400d020341250025011f5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 843533929 1250 843532679 843532687
    0xb0f07140d0209181305150705120a15090209101d010c02031f0507020d0c080f0a03090b070e041a1c05030712020c0406051e01080c07050a060f0e06010803041a090303 73
    0xd0350030040e110704d86e01035400e0f11800c1418510300e402126007521000006442084100080b41000304026003000e20400085200d5812028090030b282040d0001047c6640c00a80ba6815150843c000b00107040541089000501f16002170401110420403c1e814012000d020301c0844d41c06022050500c1411010040c80110020030000206030458408001d440303141c04842d05980a9910101d03026804600c10b8541038400c2d02d40c22050b00844803d109041d00d582c5024009200300c50014400c1c8042d40c0c2c0c003c000481002003105407100c01440011300240d00300040d07066156581c150381c4000d103503c6111024039003032030600d10f58420000080c0c0909000c2412200341d0f40c0c00301e003039030000504640074851a51a40204a0750f000c4c1044041d050440290300c0c1005540524803d60f840041350001c581000f5007501c030b141c100400d40c4e400301c4500390f89070001f0072030110714403e00408840020080c083e541c10150010380d01d22480c0a010201400c05044c8814869008d00f140c1c114074018050701d8807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 843535179 1250 843533929 843533941
    0x20f0d0218010206011212050702131e0204120b09031902060f010e01060e011d04150e090613030e0a120302062a0a1112070b0f07140d020918 62
    0x940186219407009a07915426064942c800a90036061300c1090640d207181706510354a032406074191481440c2070203010701000c00548e89054500c20445040741010a07648010790b4504084412400f0018a0364070500c81070000040540c240300115501c0340c8d404101d80c0b20140120b01d0340c011181a00142c04d50b03c40e0204000307a010405502800e6000001d82842e41c031007451a000440074080d480014124103950580d96102c0c0d504556a1141c210884520840110200382541d0118104031602324143c003007000910603c1c000541d003d0380301030107014207080807001038041c1c41b540c04000e17040000c5419544016542d40c4140380003089868a0210007071040d15010351140c1c41151691056902640c580030f400240300c103130401c41e0700460341051418101502c01d45039541521491050b83c400d203220340001c0c0040200800005000704200a203038504909038400191004200d54100a68a42039003039001045040d100c100b08404009030300e413040000400e81d011081c0b1112003004104000b4004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 843536429 1250 843535179 843535181
    0x21080405300303070c02040c0903060510230d120504050301051305100e120714060c070c091b030e010b0a03030806010e030a02090402010305090312040c051008070e13020f0d 76
    0x140c9010040109804090402071103612400b08640c6000403500308000800146400e03440440005810704204a02c0c0d504d0741c41d440100e070320480712010079640c9180d0a100381d806500e6445002c13140004107503441c881c080042603000c3e00c0f07880018440c54900f86881c21245c020310039100a440d02400800c40e034645194a46401d800d1000251400d008840f40a516003409020740b150343d0034440700070071105800e240410040e6001c403000b07980704c01c003040341c0224200051042c18050b8203030b0f48036a40c0b00e80311424507502201e900c0c1d0100c682039242481303161b03840b0749d0942c12042c40d1074103040008510003d54152809854500411039000040e120040300301034010084901402080c2da039100c03c0f990348828503545411824000c0d40c050300d03c038001401588640c2005030700c80240350035203040c161071603102c41e001c01d0155012600075070101810700c2a410000b4460120f20000c0c40d0905160826500142a41c228041c2641c0500308a4401c0b0135205601e404944c0c0900306042b60555074042c0108880c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 843537679 1250 843536429 843536479
    0x2090109081c1205060a0b161a040b0f16050304141606110705030a0b06041b020c0103050703060623040f060503010906080304081e120304080c010b03060121080405 72
    0x8010403c181c00c1001415818441c1d01d03c2030714050a454104c50a0400f985291703088020042d100803c01000b0000180d942c071040c86080607034111040440c00d181c0317460219182c0003000c2c8942c8815803401c2140c1c031803444a0744d5040024034103289070384c0d80307660600e4040c0810700d07201003040748180311139070b060b202040d000e2004440b500d9aa050381115441005a01c40c40c1510034a503156211503400400b2802d1240404c0d04044020000076440d458005c5034240c030030035103104902580104400f4040c1e542c041c05219480f441e1071400b0072001e0b04121025102e111400d0780d882190030403003401c09001064008a40c0030304030b030754141c040250340d8000090103507009006000005007007020002c0e008400009440c2900ea005c00903016080401e4140340009200069404035403285507603610aa2090000450160f0f02801d041640c41c8030140d02c1ea425205040c0041d8041c0d8840001005101c0c56001d002074005d8204442d04131a101501b4141c52030700468000030340c045400983c0c2240031002020341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 843538929 1250 843537679 843537733
    0x1203050d0e0714010509130507080106031506080c0307021f0902120a080909041e08071e05030f0c0705100c031d0d080313060f05180f100209010908 65
    0x34004100200c403038588032541071107042c3c00d10790800300904807580140003820900c58007900c0c4488211900014800f694002c1e125400820744020060000d551325020302005107e607280450f201b54503000004021481c0181003c0e0103070000320126079031074405d1020b44010400e100180640952502ea4034004020380c0c80c0491080c03e1381c0c2100285041e01040a40b00940c2103542903050070380a109000011200070700031940c1e40002c0d07881400c05411003000c20400d9000305455502c8840c94901000029500c2400c606001c0b0003000c4180000e4001080303600c0c0c01150312000791600d240c400448d203001d400f80c01140d4081c803480d000c4c4045580c0300380032100c0d01d4040c2d52001040c124030083c2c000b00c2480e54000030307004454503403220081b0304840b00850f0082114038a0410348075003910303251304890102c0c100c580c2c115110030a11102c4444c0c0301c422164411400c000d41051008802c45131307a101e80c40b20b2040d03409500401c44a04580c065915980200308480540e5400c11111111070f10a000507101c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843540179 1250 843538929 843538931
    0x10e0603071205060f06011205010902030103170c064006050c030f0403030c0c02030a1407080102040b090f0d05060103050a050105010902030705120c220f270c02071203050d 76
    0x100054000382c224050725456004000341c0fa40741c444210815024900904140c140310070743c01034403607500f00c40c03203114004c00402c5030050f00c070f50551420b00701c1181c8943c1240350014042c040d50007041c07008100303690800940380101c84694000207021607010900031008800b009202d1105403140e81d1958119040c91044a00700801c1d540c40d80c40c014280000e41c1c01e030405800e0600082e001a01a47c440c0c078519030a401d200380003060302d5000074039044d10080229000c0084080410740e10304108a8440580000c900035402c01c2e0400850391841c0c0503c4142d40e200d43c04188801c0d103941c5032815840a10740d006403c0d90501c0d07031039041c030ba035403881d6201044a00c0d41c03800c0000110382c01d003071003070b603026401998810745400ca683c2121840030601500f1040841f0081041412080b81c260180b40240c1000d801d42c035801e403429081e4144040ea80c0d1010f04a0500c1c03001e80541544121040d0159104100001608440001d41240340115603081718041d101c001c41000c3c10302d50000040c242c00d401c0544 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843541429 1250 843540179 843540193
    0x14010e031504153b0a0b07020304031709010e1e060f040306021b240103020603070e0306101e0303080c07031101020f0d0e0c031f0e030d0902030d0c08250b010e0603 72
    0x70100e120701940000e8010705401c05c19081000405031211190440720390310499080c1501c9403101d011751030300f90007107212000c40050a6200e030b580100820400c20003c9400f40a500c2d0405071500e507441445505900c1a50005110950205101c2c1550095078006004548480c104521017403200181203ca42d0640308010340ca0b00003982e00a0505800e4603072440700d5200340d10f180e00340302c0145c01c0a00088281311200080481c40c3c1c400b001b00910803d00f0500c5007890606d8a1019110755003509080d403a583c0c1982404d00c04660801000d94006a807201e0f082d907a0003031810105d60000d0007100146c0c0c907500000c0c1c1d98a11030700c0c54000c2c21842000c0d100c10062484c58a002c283e86400300041a50140c010b40c00b40d20003c2440350a1140d42c0404040201e28550200325150450f800062075010b01c0d5030360213240007981010810a00d1104007424a604010b4864440c1c00281c0a0448444034a6000c0201010b00030050704180d0302c0350780d104100805951b1a401444419881210483d000707110f582 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843542679 1250 843541429 843541511
    0x330306030b0a051b0c101b030e0303100b0705070902160c0503030901020a030806010c021c0b0c072607080c060109180b0f0702070e010902030114010e03150415 70
    0x4460b60740185007040c1c0e00004910504c0e400e19480e013180d91043c149004408080004100300e0103189040844c20311b101c540b0307a8081c1e1001d400c4a10084102d1160741c024130070006801d01d850300202c11f507448101210b07150300041c07070703c64901612a00300114039400414142c807640030414020720401e1051196441c070940fa002815981e0081c1e03050140141c0c00400d2120119015134091a0850810724094882c50b54a8001c05ca45000c0001124051381285078400e00344825140180d1f0041d4076200200d142210030384031145c19400d0300c128011000c44d0310105034600010842120b40041d40124041e84031000740102a4441800348103985070386040c80e280c0a0140d0310604d0702440203a0040030000d103a1944074041d00c1d80742c001001c0300305610589101180c0707010250700c05030003403030a10700141c0d0329030502042c60440700e03989401038140030500001e181c00e582c0c04904c0c1c803161119003058001580c0c07181806c0d040c420300d00501d40c41d52841d1640e800402d801d034801c1a00070224601944040410384 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843543929 1250 843542679 843542681
    0x41a031005010c0305090d080c120c010f052707180c08070e060f0c01200a17010f060f02011d011a1906080c07121d09090601330306030b0a 61
    0x843c005000034010040301c0f40c6071904980480b01c06019a0b0501c0c01d02e01d4100d0001d182c03c1c1d1000d500c661940021400c104489824001e00859052106090110741007480d0b1841020038009071405d401d8220b980d80d0624030302d041200c0030080440c1440100da0046200b4020000d00240c0280c0f030000e0105400a89858081c12000f1014500640b50742d20b4180b13044040c200ca074004150800c90b0b035480d0182026a000046401000500903c684540d24608550040c0c80da10029000e01000005180100324121491000004440150814181400c502401240104030010340160244045a080720320702005601070f4180e54042001100344201c15400c01010449014040a4411101711b0900843d445840e200741c02621811a90307042040c15550641c00c0d0502c02d140c07500040e8000780aa400030300c80e0340d10807605001079550319050300384031075400c0e2110414001c15055001d1400420951140200c440d8180080321081c00292409200024068842407000751900812100440c101d2400303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843545179 1250 843543929 843543947
    0x9040c03140a0213050d030306080f1f0203250f0e1c030f1709060f0a0509060103021011300c06010302100c020907110f0114060603040602041a03100501 67
    0x201201d8801603030341d02002c10003035800003000031000c1140000c0058140c403040d40001001d482501c01089080c100400146400c01c080342c001411f52110150342841100d03417214400c1682d03180e002607a02d68641d244010610003000c3c0e00000d442200348400300c0658082000440d94040e40e9901e400224034104000c0c1c1d200301c4034440925402c0c1d1441c1540003030b000345070048a035045410181d81291540801110881c01250000c0e4540c10210400c4681070030090071607401030758540f00b081a41403a0741500d1b514541400020700480038120f0207481e00780a61a03c0d00140340c05011525001e010343d9841308024408244000303081810b180a00416440344140d610030580038005000381da10716002c11401c0e1100340187e10500101c0d506031405a103903040c000740f04400a4541c2d50404482c9000d052a1400344104420030f645070002d91071310005010090350304410110390454480d25203003040c000910555000421240c41410000ea0010902d00035603c150100b00740c1400d07180c0d03103600544100710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843546429 1250 843545179 843545201
    0xc25060903091a120a0b0901091512031211040801150e0903070210081b07051c0801080d0c080c151005030106150305070c050f0a0209060604060c0803091009030509040c03 75
    0x10003804146034500c4080d4905a1101c00040b0204100342d650000c6035481c5e07c00e0300010152034880c0c24001c0c44486102000000b445c01094032084100302e510003c06104d001e6001e182180c0c0c07035240d0201500c9200007650080d01c00031008004086008a06420040e00c42c826038480505280016850300c0000c400d07a1381c0c0a8024003200303c1440328810448a43d00003c081c84182941410084071500c08903014019441c4503130000d00248032000c0408900051490812003080151001448200404118196004510f09000c240d0a4161400e03a10340d02814009100504c0340207202400490b0b8080140c0c024056441e206817119140d405040c00e0b540d0500910000e039060700b100078040e62080c0e000340c0d41314802e860b090245440300da071072030b040c01840010543c144d40980c000000707501e000003119401c0b0000300d914602c0c0c68035149000d00190300002c80036250340400720008000f01800d000ac8072449280513404c004280480c6006841900300c4419280198503095140324034a02034803413400300d06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843547679 1250 843546429 843546479
    0xf05010b090105071209031704060e031b040906060b0c1c02010504022110050a0605100201020c0706200f0a031407111507051b0301140408030c2506090309 68
    0x4c03058448184105000184108000c85000008045240e40404c03004180301c514945684501d050300c018409002503030641c0c403d42004420000340805c03602922800c1d04184c0340480d80010b2410290000d003a03035440340914090014980c5c178102800300e0222081001c1030250090b915285408900300c0344101c80c001d400c02030724501d50110f6650700c085082c1c0c035200c69003140c2002c1c00c10309207041072320000e07a01c4010083d29406c2c1030050345040148610f01c000b4920085040403140100c1607500c0c01c82d0b2080b1010710504900c140d844070180024000e05803445011a40b81d46000c88600f580d43d94103010580c00500c15440e036000c1c81c41e03020308864a09800c40f00d01c5045251200422002004000d1080b12412081052000048061000481c40c2a03410381600500052605240c2550307030b603c1c0790028401510007000b000884443c1940c0c0c0052585080c13a07250b10300c40c401c08048071080700400700c01d82074406540e410001e0383d810041c0702e01e04ca42e6507016441d0340c80c80356046642612342014450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843548929 1250 843547679 843547687
    0x1020d0606020a26071506080c0d03170c07020d08030402090a02090d11061c05040c0501020616080a02090d050604021801080d030b132406050405060a0e0a05040507030f05010b090105 80
    0x4001c0c180d90070301c03c080c00309200724581480c540d15014401b425144c00380c611030701c0361001c10030401c0a1040e080d03484810303113910072507041554000701641d201c400900b080300c000c600400c0043e10100c050307560381d9601a104503450b10329400c00c141d0b42e4004031001c0f8401c00616001a00210550007902c5080001038040c0c1548207280d5104c0866410a610260704a1300c248600c441c0d04289603205002c40071001c00000c1e89040500348a029001150081410365219806000f000644480b00440c1c0c900c0c14a0140181e4581034881c6005e4890b60059030b134095103545441d4288070700032401d907004074400c5802e05100902c903d00035050403001d109440c2c40b601703c00c190401040c042d811081504a008010f41848405171550408840400d142c210300d90440c000c0840707000b02c003680c550340a02518100603052500e0300d400101c61348151450201001550400b01d8215107500a0100c060040100103210b103103815038000b030017420400c100904403814900009115000ba204a036401941a520f85d454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843550179 1250 843548929 843548963
    0xe1903030b01020a080d09020405150a060c030207030b160e01020a0201050d0b01090b0d0504030f050306150c01140f150a12060506030f060405060a0e1902040c0905030f01020d0606020a 81
    0x3000101c903100e0642c052020110000b0321010000d0649449a20f00051301c140c0600501049510050014032400c0c0503801c075002583c2d4690414048034143e1601c49440d0415140c12070401c029944010280f98004046c09103a41486c03001d1140681e940c1e484880a021940c012030b518585900d000c0e012400410030858002c0303d03500004031442060400010310341d51900c00c81060b03404181d411440c5c40e03031001403000705a4081d80d0200500ca091500500b035090400c0006c3e2510010b0815450109000800c401e4411086d0072006ca03007100c0c1c1107003699030718141400300d0349840300300c805090852590500714010b141c044507280c1a01e094085080c805107140e030701d840043c42c0103801da41d8503114201c2241d840070000c0000c0d5208a00c03500c003030711441c00c1110405050310f00c0413861b041c85400075504090364095500e20078900e41d8040314040303410841058103a8149038903400541d090f0088207002002d20105400a046e01803070202c040240c595255000c90710303000d00c1d18004004540f441c0340d07002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843551429 1250 843550179 843550181
    0x318091e0414120403050114130b161101090606050f121905010b0604030c14060403020f0114091206010513110a110705041d070b16020d330e190303 65
    0x8001d000c00c0304490f210601d00c034022100c2c0e0415031044502d603468400c000c0f08a00c4034482c407070b0044408051141c400000b03075030b10079000d40c1c000e0100c3e0504150340400c2e114070384203aa1405416603010002c200d10356150500f17001511480c0282c5000f45040c400140d664100703803d540c3c2d5415001e1018047c04468006009100c10041c0e0090703c6564071840c800000e555024000c01c01103104105001c0140d2500c104103040190702080c4038419601070004001507129500703d030b280800c0c01d00e010000e005054001c180940546071505800103440c42c81c401c0e00f41000100e0307605a41c0d0403142050f40445500c44101a51a80142c41c013040b0018000030450318001c0c900c80104600da0000c2c1c0b009681c035140490211401c04c001e41d03248540c0d4416040201070244140710103410382c60550340c0b42c0900c107401c554541d0703e00e00d0024000d05034001032806010148001c000541c00389082402217010401c610011500726202c10480c80b45040c1e504022203000180e00d584040307104011580e05c80c901c0d2400c1d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843552679 1250 843551429 843551453
    0x90c180405070302062a070f030f230c13020c12030406020f030709180c0f12020708030c0702130c120f020c0a051c03020f0415050c0318091e04 63
    0x31003a11490070b020005a682c2000740c0401031450071704c0e0103807038420b20b035108444880203026811074014075814004861b18a4480b001d40341c009200da02c10320942d14140f511114a0f4a00000b0024078204108c078903540821190071030b881c2100c901c0013000803000079a04901c100d640d642c1c6c003540800c4a0300c0840047d5005964042e008078001410b203a44044560490740c001c84031840000c460010511102c03a41c0c08095140c240c0c01c49040012440000010304034250b81050a41403180700241e00c0c9038480150101d4110b80d5100808640328149224068425001010201e00c5800e07000b02442a60b500c92185c80040421696902a070700cd42c418004000d20011000003e450707020090450201c400700980d0207d644200000c00351900c2a0210341c0ca4624404585000c250041102e00c01e091240760584046d90440c0e510400c400654031000d465900c240f002c04100b90102043e0400382414034402440715a50540d1007160301c2d501d134081c2c405610b918042c40822040c0b604049004105e03840b0001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843553929 1250 843552679 843552683
    0x60f050906090913140706110a0b0601110a0203030f04030c1d010e04140f0d08071404050f06070512190305061c031103040e100e010305120c0102130b12090c1804 71
    0x80e0341138038003a111070b0b0f019031001e482403150380e018038070421065500c5442a81ca07c0545d170050070403450169076610301c03111f000e40010304004a4200f19442c2c00c50500c540343c84168010100c136500c800502c0e40e080300782c216202c02d69108a8101d0000307181c041c060700c4628181e00043c1078041981c01c1c0b0700f444605120191059601c1d044090034000003102c200100462700c0d2030440109101001c0b00d400a041c0c40300248407004100c065122118040c130210290740564000301c0346214418800e0380130404034014444003800922810000c420310704d0010f4000c00c100d203440c14010306602d00d048819230648006642540c2c0201e41022641300e2003080e2040d000003144607241040454212101c0c0e80d1454206d0703001440b0310340c0000f0610070301030b4241281d440109841d0101c0340341585540c403880d1700d9030152003515800050004402d000c290007941100c078040120188082c0194560710300641c55000186c240c4428484540850461503000915058110005005070081c90b200080c041d1603100140007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843555179 1250 843553929 843553951
    0x30f0b040f0c03110427030c051203010b0712030908160606150e040f0b06030c07061808041e23010c08031302090c03060a1a070204060609060f0509060909 68
    0x84040000c09604200d001540110b14051544212208000417107603501814891165222001181c1d81d810302e9006d00c1003509800c10800c9803c0c1420700b02d0401e22018041951f000c0c0020010450345180d1010b000440c2c020010307a00303000c490740e005070216000c0b102e0103002c8103410701ca040700e4605080c4589144500c130350f401007034280e920501780b243e902c87ca031000c0f004501c3c40c0f041c180031801c1c184114a08035040b0132081c048161050003089407840040c100b0781c400f4000103802d20510101d5001074016000892404403480e80c07074180079007250401c0c003401c4150a4603460b10481c3c803501046003015156100001a0755034210301c0e20804d03480307074603407813a041c081191080404101000e0155118543d1084071311071a054520420500714401041032130300260a0043c4020f5854080260701600c040054104001c070003442217182d076014030f9400a5001d800e0074408a03405038440b4864045680d551141145542140e40907180c1d401152620b0380c0240b03040c002c110462402012440d04440c000d25 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843556429 1250 843555179 843555203
    0x603050f075001030b0d02060a030b060c1504030f1e050c0703020a23060a12052809060c050a1710030c0905041104110a03050414010c110c010306030f0b04 68
    0x2554100103050b030380641038240a05825115540c05004001d49482e0444189550300d40c60790008640d0f00071214520101a60b540c0f0700c0c80940c07240760032518404618411101e4460001840034000c5100700c9040b000101001080c180b050301880c201902580c2d84043d440040d140c0c0301d0300703c07004c2d0424004601036100c0d411000000d6101d007181c81e405801e5040d403c4249002c8002d1080c04000c80d244a5030090104000304907019030300200c1c503002e810314808007003105d1b11030b0784c81d45110044005840d229100d4881d134000b840e40850b8420400b4134070a40c030510991001e650150780d075004010305a00441c0c3c2c0d807070a41d141e8064002c10554401007048400340c040d80c59441d24142d11015800c07002a03e030740c0b0400d11042c88448041c4a4202000301c4041c04100d041c1100700c085401485400f80a064803a0089400c003c00c02c0c0d400d01203600a035000700009440403000801442e488da1200f02c3c036003c0e0515a031303001d51080c00380c2000e490700840300715500403039550380a0762007400910075615403070561 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843557679 1250 843556429 843556529
    0x180b09090613080f0c0709060b04050105041205070302100f300509030c030307020f0111130308130513060603060e060108190603021003050411091611150702010603050f07 75
    0x80a004000b1208004105590130041d1f098104c07485a0880c003901c0806000420031a030b03000301240d0944013402a00c032240350007840d0541c58400380350002980b080450000d41e01460340070803003d00808032035031586040c1014095070700c8424401c2101c00c0410304910400901c206403a040290090b80c08400c0b2031400b00d641160604540098402c00c0040c0c000242c0741c81000424083d403800c260180c161b0302e1400c04820b80b0840c000342c0b5880002c01130340300401c41d1540a402c40321140b004003005044911a03c01c1c3c15001e0b002080036001d0400413915052020980d0660210590b1240d40103071100b014507101c0c031440d080404e0843e00c0b88402c25449140c040016214040000d18a1056403408601800d1601d0302c10035a420301c02c285801100004200183d044d030807844186610f0b4a8100006e01e031340140c400300d0402142c1c61082007880155024084180e5055000404a07809070b810b80d05d1050040c1e01243e01d891091055540c10140030107078990b17019541c040a40101c040743c201e090680001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843558929 1250 843557679 843557707
    0x120e0309062a06060a0609180b12070605040f0609030b0402010813140318040c09031707080f030402150f1e0c0604030e1c0203030706020f090a180b0909061308 70
    0xb080c030954160003800911181d418582c001c00040d0607142004d2000c2414190170340f407402140d9410626494941c0440d038116100c04007260154030f4004240d41c0b44030b80750f1502a0040e44940f1565052040840001030418031415041080e0707684030840d00d0709174460303030011500e4100181c0302c80544036101d104080020b484c1d80f000c1d151f0580c0e020141d030f1240e00301c194070f10a586a01103090700541c100100c11001503070060030322013900e82c03220303149042c1e00c103900c1444000e003d00f25008001d01d50004e0a50522003010024510403803003129504138640702c0c000404541d0181c100310005400e420b1203180511003503401552003903500c6500d1903040c1015512000c1c54004107680540115842e0491660103051201485419800c992158100c0300e074603070b0110350b41c0d21460340040c0c810381e40820144d1a982c1140f048034000b040040030001d05a41b54600862040d007801c540200c0c19241480d070178401e062002c043d038031540001000e00815a10311591440c91010b0b0401252072030010010f4440301000b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843560179 1250 843558929 843558997
    0x801022704020703020a0204022808070810060f030e10020705100b0303070b0a0905190809150f040e1815090d09050901090b130612023d030f020f0901120e030906 71
    0x12fa80c841940c0e081034030000e8103800016003035a030502e0054500f0300c04580c00290382514102140360000b5080c1865200500701800c01848070921800060038400f07000c4005050901c1c007071610020440050100d0405075684a42d1400608031410600020840c03410355100c9808580960b0a0724001c6185001403e40c0040f652001ca403001004900412103007481c4098040160b0200491071811211140e8501c05024902c206148102107500148080707414840100b000348016040322000b415141c212a24504c0442c5c04810078425076045284030340c03141110750101c88002c0c02d41003c0d642400110005459540005038000b0385a06c00c0c0c109000c2d035407207142c004204c1c4c44070303d1800c8000e80c03041103000d1800c0181d0814900720805000c00300d2107507004490407100024045200c81d0081c0c0c0c0250086c10300464098200791000c02c45c0301000c065280145100c00c402d80c0c82960071079a002148084810140c0c0c1142c05034003d00c0400c12a0038240c0080010f0f650907a83ea429609900a9541503009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843561429 1250 843560179 843560257
    0x180d0f0206070b0118060b16061b021c03060506090f04021b1006091a0d0c0b220504020a270e040c0608090f1f060801022704020703020a020402 63
    0xf4020041201d00ca610601d00ca00300e0083d40107000c05442c1004103034440c0190000c0d640406080841c5404010480d0701c01304020410140d040182d000d8094080d4941548181c0c0303c1a02d80070b01502c030703d880c0c441d00c507100603614014080340c1014070000c02d1144c41c080001070b050300150b0070090401041c0d141440300102c1e02001004000e4400300b01c1a003002c0d901c0c02e6001c0c03070700c4508189454031084440d21074460250b0301916038a02090381070a0004003288550300550a641d400543c040e0000743c0002c0c00310031500c24070150b007200b03552281404101d105d00c034407000025aa1341076500440d462030781300c2e51060b4075400f0400359442c3c03105142e8442e908103440880c1c0c680381088040180701c4e08900c819a00c880e0510190001c040c18050454580c0125070328044281010805802401071551058003e4001140219252003600c0090340920300c420340c00b40301c04c0d2a03001401d03109261a0003240d881c2a0700d40e0103040004180e40c203010294000301404080a1151441040140da041e10349a903551 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843562679 1250 843561429 843561443
    0x61603021b07030c0609050d140111160501050c0a0f0e01121e0c0504050303040312020a08030a050601080c030702100b0402042d052e020c1f021002180d0f020607 71
    0x3031451502c0066100c913580150b091250400080162380d4509070300006442e08130f001100342080b46103900b401070068031140740b01305c900401c0201c0082003100006100d03c0c8640020007894aa24080da400ca00603140b80754000b03502078040140301485250700c3d07018624103040900802c0303e0998100309850740054074404035a0781091480c2c1c40442801509400c1d103017410890310785420400840d80300d114034040900310000460080807210301c2080350009640c0c0101405031603040c81c0c020400a04400e0719002e000625100100380d80c4101001105d004042030b130000c0030160200c501150290010b9a952540305500f0f0100046004800d2140400300d00d880440d09801c40c02040c00501c030140c240c00050188550b00461000000c0040c11582c920740031180c21140c1c04c44110341245080e020f00c8002e500101e082c03001e01c1003000b003014a0f0492501d50703021781c0d0f2030801c00040102280600c0c10210001412911031076050305040441c0401140100116903e00340d0703170b401041444c0e00c1490201c40c02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843563929 1250 843562679 843562693
    0x1a1c06050610050f0f04050a14120607080a09030e060f130902070c09110c16150503040f121e0f1b02030d1409090f0604050612061603021b 61
    0x48944110340c0e01480c100c07000d06104420b94802049401103650407142d20400107158000410300f1402e80303000b4400104126560b0303031204c01d0744001103180d08c64035010344880b61602c1a14a00400c000d88503620a0359400780c1c5030358044004c0044c160100c8141e0501c2042e0f600c10007942c440d40014101e4070083c045442d40d1310003480980010350040d40c03120200920500c84400022604d15001c02280c0c0300d40c4003c20f5000f2003034000a1144200d101c0400244a000c1e0100b40c404403860144d011280701301d4000580303815042c1e05660600c41110020191018001d042000840c2000b481c6a940030398644001d40f441038144604180b58181c2418010038401c1d00d840a80760341c40003101c0e200c1e00e69021001500c6146601084c0d0707881e5031090420501200c0480015008070103c2900c020120051849210341080100019450403d8407054000e80c01c00c4001202818410880070101c52484003c00c1a0382c4c601c058085d2200c515a40003040680800c00360980c008032016a900b0180d100d070141401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843565179 1250 843563929 843563933
    0xa0522080901090b03040807201206101413020717130806010b0f1e0903100203010302040609050408030c0c031209030909010915030305070f080a0903151e1a1c 70
    0x80c24900d610130100340c0010410400010065020741c3c0d41c3c107600003c2d0130484102808108062600c000d0a03907040a4040042d0320600360001b02c0d5070249822424201b942a00c4200c0300c5040784070700b132009401041100c5440302240385c039802801083e0146c00000b41004244030062100c0d40400300165041600c2401800b00306002d000032801403600742d25881c50400240120001c4c0e00841140501076219010003140001c0c5d01c100325140c840c001001c2d1200350030440701110094200780010b0340201c2c50701e000032407004120310405004030340013680070b42950b0300c0c10384491865009a07802440340c08180032802c0b082a4440c1c1540c01050204091911200204140481940c050340300380c20403400c001d00912a4207401c81d0314416280c261034182d43d40d0b5000d040c0640d600a02c030708020000407000800c1405190b200501c841624820300500019441c0c081c8a00195910100c850101180c8808250004c03070076a0311078200c1c11003c2e01c40383e0080c0e003e44002040c0c1c3d00b00c01442d0f200d00e10454042e6003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843566429 1250 843565179 843565187
    0x4091103010f120b040b06031002030a2a05040302150702030102043209070509041d0d020f06060a120f02030609010b010e0a0e0604020a170c04090c0f080a0522080901 73
    0xf030040c4400c0c034804100d86489003000780e28003070f10240c40140c500000c940c0d181c0b030601407060403c01d0084155543d052411510f8000c090000040440410000a500042152130400302d6004850780e5041d04207800c43d020030210304016045a0b408810800200005881c20b00107840100f840c2440240080034250201090b07407001603003d9911503a01a00c045650b41b0788400c1c40c1c00c105585029500c420b54000410010112503502c1ea81c01107400c21010000b120001d034502503503807241d081d00c1e021119803c2d5a07a0b100c0f415038a580d4050140481804a10040030f0707940041d6015400106504500790007090500b0030940720400140d4555070781e010556007002803404098425692581039a240c4a0f20051400d00603010a101c3d40d00040d1030306000c0c1c466508031441a0130f545214001d0308003041c40c0301855001307109400ca0181031800f0070071210b00a04140041c4d84054442019075175401d4a001c0040c04024201485010442c8050200d451040c03010000742c2d100c3c0c2e003129901e40040700090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843567679 1250 843566429 843566459
    0x1b030f0d030b01120b1e180f090706020f0c01080a110a02010c08010b09031f02120108070302150405130903091d2a250b07030516020d0f0507080409110301 68
    0x18100c5060000c44040c86c3ca426441c184819000500d0b111036010900c00030300c03500a514501c2c030250a4a00c2071005100000701c0560041c018001200e650681d01c41c0103076200c0c01c103281038101582101070458959402070100c0c1da44203026080028080c40040911134494001102c5800140c1d03403901314052050300044440d014089038005281040c240100099940c0002c01454800f01401c14180f94200c84a80581c0e052110a00b4503402c0d66071541280e0b992400c0fa803100ba84910542c0c41d00c40017007030680045806541d40607107560381580c180301104000e014007000440410101c0700e00000c44a4552060403205011410080402d0410420005008060040111080c49a807001c10380c0c0c014048129114909808441045200145482d9000540154010306070809c0d0500f0026403a60552140784124284281c04000c0308802c0400c0ba030754144403c04801050a02c0007000c2128010b030003802c400c034403820100f803500340c84000320400e480c1d910b28460302c0000040014000c0484000c010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843568929 1250 843567679 843567707
    0x2090114060d0f390c0f020a0e040501050604090215090a180207061b020c120f03121603090201270504020a05190c0b06040203040201050c061006030b01111b030f0d030b01 75
    0x301644c240300e001103c00c030b12100c0022109100565a1000811803d8407a806500d40c00401c1100d405665000345c82440750b003120122802d510307120008455150903c103e4041c1d94001c0c4c8a0010865004025045940b19103141e90f402032260500181203140680c510b080c86000400142e280c0c42c640c07618806407802e09003400b504411030b00c007214102c0d074005082030758504100d035454900308041c030740d480c100b4070015941403150100080014904148158150095210110b10445074405000c102c04981e44040002d0000c1c24004100010007044642c400c4189588031304400d040c1e0b507520014003240d00401d00180458404030b0f04008401030446a01041006410700d078035a007000340c2c0c646141d1a4000e0080f40f280f58048042425079201b2426500c44018aa0841300c5504003002c84d0003540000e1f108580000382070224004407075210b003003501c0046000304010600c0503612a012140349101c02c00080d003600c01c400d02e214424204202c95900c0b40c59a450010301c402100000408800c203500039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843570179 1250 843568929 843568991
    0xe130242040b2b05010905010501120218090a2a02070e010f03080706111b0106060e0609060306040e060408130609030809010804020a09141e0402090114060d0f 70
    0x104101c1800c0c000112690103000034219a40f04480f0b10b0700780d9040080044036000700b840e010000c18020003aa00c428140e94007600c40c803c21301c103050070b0342040c0d20500a611016500072142c0300201c1c1017407a1070b20b4204482000101d44030410340c691f92219a107030302c0c1c2040d181442c407030289031654040c030159015280d00002101c1c40e606200301103c044189110003010558000350081c184821744d4080105e400b80c014035aaa1368803500d480a15901e070544d41c8213265440c1c00c600082c07540c01100768607070400001e0f000b00e0920505104001c1250001415650480c2d1a21230f60203410301c082c024244500c0c400c4041c1a00c1d5075408000185800c020b801480a0010548043c0086480380c4190b81c0c0d003800c2460403d800d07507500c1c8046150400a9809036448d5400c00c446c007103021580341c269921490900e2001080106841c051048522003610040c0d00b10710140014005130100c0c1082c00901d9502600d0300e4036100004c4003420480f0040c501c0f030200c080d0388802080340c0003902c000d0003c0107008010303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843571429 1250 843570179 843570187
    0x20307090e09011b02010b18060a05090604112101091503020909070e1303170f012102091305010b2d012102030405160e130242 56
    0x4068400c25050040c0c0194812040001e510418250040100003100c07007040907006040701e0313000e0b0107000c800307036064460002000280c1d134104101342564400e10000b00700810b4a8501b8003031003580e01024201a8101d611a40014034506050b8024000c2e0b90749550354500c4803420305403050b2000c0e01a00102d0b40a800c05c1000356902480c500b8100640f81c0484143d9101c0e200d03d0021840c040156000c0711031080c6003400c0160300c2c90300e000d0400d00701e0b02981b01d1008200b90f0440f03052642608903003810035424418014083c100c2c205180c03100140c1076003440005041c80b60009401c07104100d505822524038002d100007003210a02545003109000d894010380c00d250520000c022408501141080c024100000b048a80c480c00041001a030310100c0e4280e540c40c40040031000e07500880d01960f072403280340043c0c1c070000e02e0810f410f0100c800200c040c2c10380391943c280c2840c1c140b0722500e0917a032240119403d9000e6541607280201d031410141c4441c800145a40340344222901074106520031300d04244 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843572679 1250 843571429 843571441
    0x3050307140702031209010c05070b0309070f05060a0309050709020f041517150103110f1218101e0f0f0501060f0909050601200d08060a03081c111305130203 69
    0x16007801590002c05c0142c0d140c01d40b42004030b0342c00310240c034042c1444c800d0300300024030728418800643c000d43c400c00545003015140c842e4641c48503054410280c0000040003000707200d51282c2d0041000e903100d10151200240d03901203010998203d490850303001080010104001007d4104506441040d4204a03250707400c0c0e180c1c0b1425940f00106a8012041c840d030701164268420f0303111010078a0b100c4400d546544181845210300d03000082c480980e80321a4010403075880d003403c0081c24002c000310003019401800c141e40c4000d040b6003a0000b407100c2c41140c41115002081c002ca012540e4040d00c0026034408201a200070342e50107900200a00c006001305441d0381d07601c0418241a00d541410104160b292400100c1e5409503040900d0700e4030303064040d100d0481e81c0c041002c602d140b43c0c80d502c1000c1070715044c0401c110300000c4d1100801407801000310f441c00c0030f0200146003900c03c00000c002840002100c01c072010b5405030110700000410074009008070b180543c0c1046c40e070f0740917180440c02c41c80d100f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843573929 1250 843572679 843572683
    0x1008090c09060303090307120516030203030d0f020d0603061e06051e03070e040b040308010f0e0103030e040917090405011217070503131508090a050618010b04090305030714070203 79
    0x900c080d60301500c42040000d00030b45081085603000c4601074216441c0b15518401e040700e48507040022280b40c09200c0c800e81c02012610407220070740360010040c51505110b008480000c2c100300d04600080c40c0c0a00041044071214440d01300114020b03080420b03460320f0910b916001c2500e2903c40c0300700c14507040e4144640d03100ca42c0143c541d502d40203110b00400490740006441d054071307940410380c06c55010f0108000c0018551886d07014a00c0381d00c584155036286c0c000c03114940c6440c041d00401c00010f000400109105a140801e8820046d100007040c094a4440100b180540082803000c03c00020744441c003404c00d4400c0c10700401c0702d403008841101d400d503500c60310340c00c050b04101c0d03004501203820000c0c0300d0b0500c00c0f00c214051701c0d003100302c486568107410030b100e16803001728002040e4210001000503501082a155940d80701001d09040d070b80d03004e10f003000292400e24000966507900c0c9070301281c0d11548101c070100c50194644075120b1911420007451080c0c3c5541100307099509000708001601c0c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843575179 1250 843573929 843573943
    0x9040f060c02060f18100c03091704050603070c060b19080c030303040f0305030c0d02031e060409120f0e04090c1e0303140702180403032403020d080306030109120806100809 76
    0x1706490b0503c0c07845e0b50f009180c66180d422001e60b0500e0415031102c200d415070301c911403041c03007483c0c041e003041440484600b080c0524803915401c01410000104040d01c2402c4400810703206500000d80d0844201c0032402d4581070b04004d0384090403115090000042c100815802000220000d519501e00380d6519443c035408690700909000010010580714050041038803081e10000c40115241e142078140302c00d03000380203902030480160b01c1d80403404608090042d045440d400c000442004504220201c860001080c140c00402403450f00c00d04041e50780d07001d21001d040c02070036101015030401c10058000060066143ea00004440042000030782100b00e840640344a42c00d030795129801400420461940311540c0710291045004100c20950107034060f40d40030141c0700c80c01e8810500e45400c81d103040d542e4000070350f00c100080041d50010791010021170b07104034050300209140c0815641d0500224041e4502400b1803296070400c80b0500308011580c10200980c60911460b080c900d46903629029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843576429 1250 843575179 843575191
    0x16080c010e0d050c060315010f03140412050d140405070f0302090a20070b04060605060c0312130f0b16020105010e130c05150403030e031204051e09040f060c02060f 72
    0x6000d0780707051010500000100070400f920186e075a00e004210030440803000c01e034450114010b841c1c000c5491303100784151200208052400c0001d91981c7d10780700c03903010240c10403408010f0200311034041e84541c2d002c1d444080403064004002414180340150902c040c0b50080c242607105c440040015a03100751450b50004200300c0700090b8107410b00000c034500c00a506070700f0390300a400208002000050f0201300c1c803850140c602040100d40301c50400c0300c0362241006c0142641c2c014000910301c0d10041c254560003694480031140b00d81030ba035884030702c0c81440303141c01c2c0c40a82c0c102c020800d2450081101c0401b00700e89200030000d45d03041581c09402400701502c002d603c1024185410200a002d9040f0340181400070305400380b10700006680203050780b02d80800c80c0041c4c03031551800403d040000c5d0304d04114a00c284d00c0c0c0e0601d42000280070729805201c08003850740a4443d0b0002c95511407456182c002c0707000319000c1034000010300b403400644501e040028115403100c41023011910078110301d01e411003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843577679 1250 843576429 843576439
    0x201b0d0807050d0b0a030b01060f1805040b0307090f0203041a10060309300e060405030604060b011b2001020c010c08090303070602181f05032a0c16080c010e 69
    0x83c00b400215030041c90245003040d001010500080140003d1850280c126120796444080420301c0c02c004540d1800700c8805070a40c611032540501c17152034550040c808500c4050101c4100e145c0c4d840b17994041e038090010800784a41d000051205104a4001d00780c0b807244031004c40341c502c2c100003d081501100070f2140000301640c9110200030020488804851105d83c03030b800503418010140e1554503440000e00040c08541c41d0422080703141000d03c290750840e0f030700401418566441c5d4443d200030b800042ca140c0c0c10030194030140354032901e21145540959014120480000b0b642d21003074410170301021840c0741594410404040d00342e034060b404000d003540c00803266894412000100c0d280d4024030744000c01807030000c00c3c460300e03140e81c034513061203907001c01c880410f21203605d1074040c5d1440c000300d0140c100040c001c0000400014132000b50440c0e032150812001d940000e01a90340760107070000f1800c00d07016007012039207014454242886801500c5030303d02502c01c2140d0a0000b034400040c03012030902070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843578929 1250 843577679 843577687
    0x30606210c1106070e0f0f0a260f0312011a070312110a020f070605030f010608100f030305090a142103161a0f062101201b0d080705 58
    0x207911440d807031110a2648802c5074010306048101500c002503000c9018000d0707550131701030112803500b8000b13124040c0c400b800b180d280500f0302c4041e00c0c580609075180304d680b03040c208407020090710801180100161040c05580c4808262400c050b91200681c0810f0b0054961104200d140b541d080031600b02540c1b41c20102842e40002400101800d400b543d848010754010860010701500892048076025490301580c0b20700d911100152942d003c143c07104c640700f101040061040754000e00d00580c101c00f68260340b5042030780d1101000d024560540040340000c4c0081405891810139406da900a010710b22000c8444483c0440401c40e60a040007048068481d90031100d420f0400510898242060021041d1040800c0d4201010841d603103011090b0203407c19000108180071038540300d801980018581c040494151030720312414481401080b006550710a0103801a80348007020300e9a130b4409007042c42d11070060070007403422128820580c0c0c006811141e4000c68480d40301d09100d500c21102d00f00603440f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843580179 1250 843578929 843578951
    0x1b1f0f050709290d150e0c0a111002040b0903010c03270804030605270c0a060c1a01060206181207030804051204030f11180115050f03130303060621 65
    0x946220700780520b4110b00f0000d00e4252990542d0020703c24140c04088030f44140b82d40c5c4000d40f281420840d10181e014405002e5070f40b480d485042c0400c2c0c11114642120302106590101200320390103a030243c0305661000800c4071090800380514060141c650904108422240c5071200002c240c100b21828030071b22030740d0f60074200550001910701442c1c01400400880c5810600300c10040c1500014100340f01e16203c464481440c00184044c40c0300340500502c108901d807000030b4501d04c05402080740c808900c00b1420701178141d40315005008203402d0f40105441c0c1001450000c02d01d068000c20405070300b018552031039004440c070450380240d80c10b01d40f684190341c03141032a50511240540d0400311520016000050210702c40300c052a890155140050702070314a81007010803060744140c88201c48001004001c1c0f0714030141740500b441c01a007800b502d0540461002941940211840c03401d603404000b081040c15890b10505004d40b805082c84041c0504500003444000d000031009032040380c803402c90b148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843581429 1250 843580179 843580229
    0xa030b060d080d09020a050d0c0e04150903020d0905061305120a1a0f10030302100b0a051503181f0e2a03150601050d021b1f0f050709 59
    0x2944a410241e280e858180031090740307000e0130241c403080c0d01c540f40b184c0005c103092810300020304042c0d50004101c40046c3c6041c800060170305008206903003402851400d0b2000540900440b054a8800c6d406071000c00880103014142000d02e0b000140222020300c080011040d1481119054400807191403621012031442c40b031402200420007071501071902c1d00d80c041281130b0401940114005507002049644400412210001780c0c030016006a10000507010400842d50161000d07400280c00904070704c0c1c5480210740d14000b40703000000030a000104003d800341440040d4210030110001a0444050744514044c03003815000c54028041d40c0e6150b1004401d10070864552034030301c594102c406003000030030640300c210071000e1040e00a0181540b0300d0034413001e9405052044205860781414200d26000580081d0007240c46002e400b20705860701040308604001091007058541c0d030310b256094007050b0b0001541d002980c0d00702c1c80b41c18601030045041e0841e00c524183c9560380c10440c207c01e00342034940 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843582679 1250 843581429 843581449
    0x20f100b0303040f1706010603090f0b1e0702240411091008070603020d141911070b01170f0a03050301030f06140106050c28170d0c0804140c0a030b06 66
    0x11840408090002000d031500129000410111740603191648c0c0d8070102602a96080352000300070aa00010388400034000c010026002440104410900d41d14142e40c5040c10400782c0d51301015a01c400510b892280d6419203603410000710310030480c0030307040ca60348450360b003400c00c854148074003aa0000582103140180c024401401800101d0300102d40d29038010f802984000c4030002c50505181b040d00e058241d026140b801000300701284502c0141070060003005005004090b00040d00400680d00803500c2c1e648000d0192640c0c560300480302407088401f0b417401c200c2003c00381d81038010030006c60100307401c801607a04507904110032102030150342c030f000703002448403222040000c0c10040c00460111360000c040d00402d07500200721032200d22800000311801500502003d200d02c0303001d14480014001c56407030500c03080c508030b45c035060164100c0441c0030360707240d0723004400040c610800304030a000220000c040214000400f400650742240d012651180031030001820000d03807040840c11070b4841107044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843583929 1250 843582679 843582689
    0xb0402060706050f01050f1f030e190605100f060c030c020f0319020325090b060903071e05010809100911150d0b0907050a030c030908160b07020f100b030304 69
    0x4212900e802c08100404c2e040a0040500400b0010400221802d10200d422900908441d402c84601c103207803003c03409000310f6240502d05000d103544620490441d410250100c40c0316200210795860038810b00e8075542c010340c0c40035000381004c03201000301c1a041079000c00b80715003500c0c2000840c4140d00100b8005050040000d40500c00c2111034030b10720a41031049010b00d4400c50588900c00100c10304008920b489040540703070318a0000e01003010080c2503100200800003c0c010364203205c400c02c0000e0034407045a21030810104100e4007001c0f0045110301400c0500b0090034039001a091841c0c0c0b07980c0c1c07441900611884a540c07910050700380225601030084020008141c1e140004c140d6204004075008203e00161603170504004030a18940381c0340032880303103003641d40da64108a20600224094000c65400c80149507071100c407000170441c56001012046a5118072144208503413508038030b80040100190110f40141000c110fa0040118034040c0c003a204500100792143c1480c0001e080d4482c940c41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843585179 1250 843583929 843583931
    0xf0213060c1109070e060913020a05340201050d0b040c05070606051005031f0801060f0e06030607210b130606020609120a050d180809030d09120b0402060706 69
    0x2001980500028401c6215007030031803420705401c05201071a202600d2a201148020b14810300c1424880d010f0200c20340001c000a04110340208000202c0e4000d40c01030b00014000036080d80381e00720030f46000d222081001c005000c80703144015034030541505540d00030b0400500082200501d2600e8001040400c80100104072811071410003818584c080d040c2124a18148940060545005080070032140229205d42e8510b546085480c201504070507500420b03442c88000c0030440e0a000d11070800035105030303401c0000f154103220201d65986801803140303109074411020418403503440a02c07403410780240d981c0f6071080300440242101a002845d103090708030042d1000c10365070417195007101048501c55000d596260b00c600b03994136191103a4185c2c900705000c0801031014118414002002181420000081d11034038240c1107004c0d40b14882c800b69600c404c00304031015640b0781806480640d07212410b24040841c035100c0a001c46050788100605a00d4442c0300050654403008119000c0d0356004034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843586429 1250 843585179 843585217
    0x601022e06050406030503180604080d200309030c01030c02010b06070b06090609040f0209040c150f020106140102120d061e1505091804170a030204050f1f030f02 71
    0x4140004000c9208000c20054184400029142880e1080e64103903a00328026502d0038440004010301014580780f0700750020000c100004000c00c040c4101d81c088400d607900d0b0816904d540205001c0d0300061034909070160410024603100d0383d40000e020044050a080124200400d403506034018481803d0058101d80c001070514204406085151320400c0100c4400e102616040113000420340210790040020410303111040141c901076401c1c903800703403041c066a24038507154180380c0400d8034411060008035140303100581019030280a00d5019041e210800c0e81610150f1000030b41e659400084103504050008558400000e81d40103103000d030100441c00018224040b4140141003614490034103489400a54405594071070400ca8003410f00003401141900004040c1d4079001e403005c3c008881da000c1c054480f4907041d090383d01405601c00a9100161078610700720a100101c500980000d2241d8204104030030a522a042c0c0500e551645103400180a0285a0000001e110304510380814104540e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843587679 1250 843586429 843586483
    0x604170a15050708010306020708070213140f070f050c030904060602030d0e0c1809010f0507020a03030e030406080c0a03060b040b0913090506060411090613060f0804031205060102 79
    0x4403080064881c02019220071420005141140d205442e140e0000c0c011000400220382541c01030007809000381010307803400c2007603070003e9070640c00c03030424640b050349030300c08544009080700026070301000d2031000007400d1402150003042175241075104801d100c40441c2d00b90303581e20f0030410786101c074034058001c1040030703120100a503413500010f006000c03403401d00b021308496103000700e072004240307002501d108420046100600b0800d8402014072810f1345da500b8440240040340d0003282e000310010340103460701108604001303064800d111604032050f80108000c01c103003035011036000d51056a0000309515038a0b580000c80c00780003031360b02c0600d001a0200340410803121200080c03880b500c00b00d0342384010400c481071480a40e0174036030300a0700e282c0008002803c2e5061541014002e10800041e0a281605180004c1d0194212500ca00ca0348a4034007014804c254101002c4e10a111450130b001c20b2620b001c0e42c00615100207204002c4080c3d4480300462100d0340208030310700c0b9906100d030070140005044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843588929 1250 843587679 843587683
    0x1503180304030c26011a01030b011125050307050907050313120314091b04020a0e040f0c0f0203120105100c060905250e011a04030b1005011d01080f06060417 69
    0x1240114513a0078240c4409810890512442c03050040c0210054001056840154018460101c0807030601c217a10b4845100c0382c4003440851039096a0011741c0201c0c081c00300701113000c1d03601500518081c2e07200c18020300032941c03800074440d401956440d2059480c0ea60716015526290029401030082c0707108840c0103903281c0c060f0000c10800d5400300a211513961800c000c1641c03004004c148050403800280d1111003800c158005200003043c0382071076507000e04800c011401700d13151062003586060b40d950b01c01801302d920200c0864012620310045050070361a82c90308003501818400c840c880c0c4201304650316807074080d40130706194a4010000700701180c1c03141040e584440c023850355507e00c0c0b003203601d02c5265540346030413a00c250f80d60600a005243e080c042910244034400100141e804402d010000004103000c803103510800c65005203203103041c54500050607c0c26049080e484420441e8508015030f40e101130825440302c01d41c0710f0500192a5100454928480c5810010100000000c500729807840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843590179 1250 843588929 843588959
    0x30b01120b070309020607140f030c1507090b0d0b0301090614181212090102040b0705070602010b011b080703030b10030618051b070303140f06040b1503180304030c 72
    0x3060005001c2d03555030022803c8601903040258002e0044c0582004940d4410491001907100700444581888200304986160044449950a80d00c0102150031140108000541200103814961461800e00418001c50301841d4038040b580390b9102024080b0759401d4100e45611600f00d8010454228100c40d801000a000c8400320f04440000c484500131000004503000700c1d03660b41088a0600d1800828600280300160048806640038400402d00c4840107004020a61003000184001490600041d007921a41c003030980c14801c890030094101560b004d086125241e0103142182d8507080d61038241c00604004000c0c50700408580528240c9039015070111381950103602245a44034500301c000002e8400480301d0b050601628a1000b11940b400006460318034424140807908142c1001e001c0ca03280742c1141c119215460120601050707082c64400c101141ba405d0b250240c0d48082c24044801620001d0000802e074080c0070549408100240103a4000d15401085e160030540c0d942d0100e5a0450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843591429 1250 843590179 843590183
    0x1c03111201180939060206062709150a0509071815030606050406050607050a030807021e10180203071523030403022a0f04060e130c120503030c13030b0112 68
    0x21081c46101c0078103000c804c0321401c0300c103d0f50080481c0c4e61503070280040c8010007030302911402c035600304008144440c1101e4503c2903284500901c41207143c0c84008116a40241124103100e242c1403d014244402141100954030070061010000d814011481c00500d4034524600a4030980f50300442001078540143c0704132031003244e0521000c2d44400c20448248100c0c58000c1c51903100321440701c0080e024881d030a900104600580360000f184050403158405050010b5071030740c11109410416105d9485102e282900300b450540f280304941c0e005c01e0751108607015580b0460719074460305000034071504a403008561181c070007500d050710107451402142c00076607046000d4001c51000c80b03e581e0400040d1a404110801e01a0300488541e040c030203034034a201402c03034015858031800704c0c4019940c2d40c01ea00070021003002c40b200340c080e414403503800e034010b401049a100011010301c0218000100341d9810a103000f030601d035500a0900f40300d603010031542c03008001c001c00034000240c12070b01e27841880d4054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843592679 1250 843591429 843591503
    0xd031205060102120313020f0316030309170307061508030d0e0c0111070e0703022104050f03130501081504060305030a091a040909141c031112011809 66
    0x91105030040e41c58030341030810404c2c4039005000050782107505400e50b5040500141180c10558950000b2904040c10b1044003404058005400c01c02c050303000d1400402421000000003a04051019080d01c0388500c45000c1e02c400d40b60342480e5200e10714145c459005005002c03c8a03039a03010081c110006d0010300d002910303103014040b00c1d220154055400d0051070101d11000d09281d50511100c40c99104014202d4000c0607800d1140324400b10a8204000702e10741c04208000342d901d458030b4118a07041c0c03045022220b5030018480c195020810520050a0361003d0828074020364445c00b01e44112501549200d60042c2412000814080040001c003910016507075040030641d200e24808200d400d0780c440a0004000030001004609040d510010801e44500902c15210341d848a442d45451008900c0180300d8602d007200c0c6607015050b205190741c0040304082503081c0041c411b40d0b00d9071840d05105d09460400304281d81030341d485055101c00d0056501039020b60307070b20b8840000400070b0001c42032209010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843593929 1250 843592679 843592681
    0x30d1e0504020a1205010b0402033120060d0f0b1002010608030a0e040b09070302030a0b040e0d0c03050d0c020303041106030912130b0403060209030124060c08090d031205 75
    0x14240c020284140d8014003114032152410510711120200303000203542c20355a47c05d4112007a6101e0000314080e10304440c12a151040b00a52032604180b440c004110380300c903a9031424009261200120500e044c416160f500440d841c0d00070517541e1180425100b4051315000040455600591210120314010b403450320307181d0341c41c0d00c090342250554021402103500502014454a00c00c0711403a0a4a401134004144000c100e03021840940c0144c5150000c00e80200402815044604c2400044801280c044c4200c0340200101034481c4480c583e80800c100748502803505146c0035000f19040705816490411100b80b42010023512a041590215020590003c003901140381c80020749004406400240c00300034181a0440f03516403122050000d10b40034a1000500c0e80c0d080b00107000158050103000da503495028040608454900c041c1c0880d11140403001541c3c06c0c0c40e22844800d45c1c0c4d41d4105030103462258241030303200d400380d441c00580c0500c14001007820540d11000c40141004664018861 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843595179 1250 843593929 843593981
    0xf05060603040803153105070c080d180c0906080d030603081b01110408010906051b1b03070c06020c04110a0f0c1412030f060409020d080a0908030d 65
    0x10344410782d406070681c0b9090011607003130f56507006540604480149031000b18003c1306014401079000e5184039854004100d02141564001d000e510350203a02c51802000e02d400070380d20304903203010b96092803001c40d98456401203180d040030200d8485542102c520b002441d911440800540b405014000702c500580404800c003600078010745061305c0d40064141d08120701c000c00d4039088814504071805541d250300750111061000e8000704040c1001078004542c041315410a00c1c02e0301c0003c0c0540f142d46040903071179030f0140f10500030f5440175030440c01040c0180300c0c90000300303155016418024008100910780003440e143c00182d4000230050913034080c8104030383c040c3e02548074040c109501e000f0906401740a01d4092041d800405d83d2840342da160300801e48900d1180c0d140c40080d044200702c06500000340100709800600003644003204540c01c0c0026a86d035804075000c0c1076242e2004000010100302c08101714010111300000d4506003040f40d8032800402d180700080c00d0350380350049078180c40407081c081e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843596429 1250 843595179 843595189
    0x3152d04020306010f1d090717131e060f020d0204060f0e3f010213080307020f0906061606050709050a030c06140d0603060b0f040c080a0203090703050f010f0506 71
    0x100c03070344050719007417810007182e03a0a8402c858040150f040c2003054042071101540d0301e0340d405000c2c1d901070390380050100020b004810324140103440d0006e0318104408130400500814800c0c14100346480141d000145070385019000383c0306d0038400c4202c02c6c0c00411803000604450307002d0421244241d4521558032030405003591440406d020140e0000d05510008018400060243c40c110440041c011806203440101108100305088000d2043c2d400092202804066200003000f82501902640c9011400c0e400510710400312031005000395a4000001d10395601c0d0030941c0c11442d880c03001d4100d501c0062420100606049504c01d01103005c040f004a01810050f0300d80c01034036400a0285441404c200003665010f0300d103800041d018800700130400c82c0c1c00b12402410010361140d0008551100320b501000040d034a580300c0103002e03502d018200380c00f05610600054000703256110050341c0b40c480d40710003802e115a58101808a205032000c0da0304644056205002022034060b0400007a01c0316001c020b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843597679 1250 843596429 843596431
    0xa0b0f0f060a030b06281401020601060e0d0f0b070909050c090102060612011d101407021e10060b0d0b0603010e07030510031a2a04090203152d040203 66
    0x150020b04203482807001402002d0f0b42900710070300500845007a690501c0c50401105408000980e545a0f464100302c00401c00084e2a046e20090003c0d000d01e60420314003c000e024010840c0d48154103440f40e440074020403140d400704503608070091542600e44848080c002e21020f00c24100c03014600380008400b03000e0321060fa005600164080c0809480c0c0d5010070540d4a90240c0c072054555031814424040c103884440c0b0030116a641e00605400c54000c050031381110402d40d1075920310211141084a09507020403174008502104046c0c070362008501d80d03540d1034054030b09030010751146051408a164690318015040030140c1d640300780035900c0d8003400d10030b01c2d02080c4603442d9204146000b290b40e0f90701035000305501280786401d100d10565070352a80c00214401004035031180a45200348580300491855141c042c00340e09094402d40201f0118001881c861442441c59099020010403401a100c0c2d5502c018a400105100300c4510207400901100080702d10304042c031200c8861200c15402c01d1700940f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843598929 1250 843597679 843597691
    0x1060216030b1005180403080601030203060a03022404090207050c151b0109150b1206090607050c0114090f060f01050a051203210a1805070b0901110a0b0f0f 69
    0x1119001c1c60350ba612201454040e00000709600300b42004100c58131544010007210030003081c0003000341814140542907450290115042600410070000942c40e07403408a82140d60666542c80e841d2400b00040524090b0804601c1c80703980b0001d40080c14903881d402404035580260240c6203803103820010444200c042e0320681c0f088103002d1258201ca00500ca000b2412520301d80700204103841c00c0e40e94039550b0243c4800a51450303540f00c540c0b400e541072040110084040a02c0106141d0030010040c0d070f9142001000c0101b000310029503030348001d5003900001528414000040b42da402c01010007901c45500e01c0c01c0800e203205400000700c0e03020190b6086d03070403140701800020b00d05e03003094280816210944c2225549100412842012100c81458600c0b1f004450450800741e0034450340640079a100030400d04c10392100c0710450303000b0450119070b10040310401d150555580306004d006a5008032900c1092040b80108a00c01c4144110b54040310f00c00c280d840f140be056a81e03040b420f00c510b51029181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843600179 1250 843598929 843598963
    0x8010f0803120f07050c030409060f09021e0f0403140705151e0d0902210d0518060705071d070e010c110d05010b06070507030b060301050c07030c021f0e09010602 71
    0x402e40801c10040740c00d03085540717464518604103a401e5424955070083c1d000141d40d60b1390700c50400c51001d28061080103000581802e51a0600c0c2d10b0b6010080003011a0095150400081110303800e09444201c500031580170000700038403022045003607161840751140900406016480622602c040030884e182994400a00b512800b004641c12103160851588420704a6136290b100025036100b40b5550804162001e90008041d0f80c81402824001003418003001d00c0707400d1107100c10000c50080301080007041a03d0342500d910741e900740a45041429481003014200c03182c0c00910340300c01315100c24414002d544411b401000c00740011228001d11050181a4041800c882c241c03500d880d0728074140450051002007140c0d0a04030005800380d02c15181100c2d41d84c0104410410020407460ba1648003a00720002c2040e86803940a0000d64828108024200050042010110341e14407600c498400114000030210166003807001e05418040002188221900750001448030700c0003400b003001d0740039148 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843601429 1250 843600179 843600181
    0x120f06010303050c07170105040303060b131202040603060501120606150503060907022b02010b030706080c16060216030305062d0d02121f09080301180b1008010f080312 74
    0xc1c02c032080d40108034006520301540c05c0c0000ca0300c25101088035080c520340f000196900f807603d030160440c0c22036403091440140c00d11a40f0b191200355a914400c588690107605c10903603d62001800412180c0c000900b042e141c0400416000b001c8101d9080f2035101e813608020068503140c00c03402e641d548810000010b07004100041690805041e010b4010600b40102d54420100c20710f0389510320a00d400444c150182820b0700207170943e09000d42000b00c0f40c164060242d03941029001000d003400140650084003001400b84a00d00c042440701c0321550300b06104644035800d40c2d040c411541095801a4006030402002c41c00d00c0c6004805030140c00141100039500e1001401040900901c02d5140d41e4064002e50800c005038403042824407411444201900170800c0084003107080b8499400c085060720b2510601034000351541040302e0555940c86c010300402e070840007054000e4401c043c10385801c010107240b5141d2582d001110030f8140c480801482e16107640303c1d0034450341c81c043c4c0a0b201c84010303da08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843602679 1250 843601429 843601433
    0x301050d080a0507021f120e060a020c03190e0f031506013002070c230103050a11070b06030618060109090206090303030c0d050105060f0702040f020c1b120f060103 72
    0x18010008420700e03041080c281855074002840d5261a106a1148203000010381b9241aa20003145600d0b141a1402044003c407403a41c4241d60380c000602c05603d0690018004c0c40d040d204005036064400e01c1440070306910380c0007400629441250640a00485032441515010300c1d002c1810600704202404540391566200e0044030704442144512540300c1c000300128180c03000300710702c01c10095600317a000360303075040c0380c0c07a1188034002154800c03902c9424420b20320158004500300354410f900246408103042d10f600103440c0061020b2034020440320030002e004802c1249003003071548075190031816603400fa074405180d40780c0341e000c6448101040d04400c00511061300c1c0c580c044410030340040d00c082d0030012202c020034903503402641c81d54240d03100411403003007100b075500038103025200980f6281e0424000d100c5004981c040c0c144000d10681d290070050040030120b0f81a80c6500901c2d008031a840c403051038180307030121740d0311a644e401481c1680e0f08007503500b000141d2a00b040c1e502002007000360310719 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843603929 1250 843602679 843602693
    0xb03031602060c0f25030503031902121f140a09110408030703170601140711040f0204121502090d03110c04020403120f0c0b010501050d0e12040e0c0301050d 69
    0x24842280c1c0414140f02042000c0c1c81003111640c0440404001c05c81000c41007040501c010762500c4c644907103524041c050000802c0401900c0e0020340c2c8200c104107601200500e20040d02502c0306e40c3d81415030a9042101400512b061665aa0b6000e024039400070f48a40e0303013919010580c12880d0b004540101e04004040080d0301003610320424031162410a0744896840b8215031110200754001040900007211030300b000701c406e5421000909280c40e0506181c01c40d0005801a1100900007642d8006008640c0d1100c0c2c210b00140301c01e12000b10b41c0d941c0c5074448001c0030001e2b03110645620001080c10b04008280b442125803080c8024031488103680b40b41d40440f0300b00041d00380c10803940281c11181603e0f403114000751014621600000842c0e000081d0020800c9a031100e00c0c0d41009805d00140000c030b84406403690541d54203203401c03030740d4003006020f003006010091001c9125210392825040403034880c4c000b503c1a00c80d81001d00c0f40a4941a15400c2c041c0000e02070141c1c85001120101c001800b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843605179 1250 843603929 843603967
    0x705070206070602280e010e061b0703050d121806050601180306020702040b040c09150903050312010504060b1801050a0e060309070512030a0c02130204030c0906030c090b0303 77
    0x80203201515110043e81c8640c10b0340c001c0380d54a000420007943d40c2074104003070340c05024a4410b03490642d0821005400003007054080748015030161000144c000015003102a06445546030303102150a055501c1ca000d0b5030300d100f03c01040c800100040741c0d04071194141c0c005d100c142c0102c001802a0304050761030f48401400007400007810301c914081a5182200703055120001140960300c0181c942003d80144800e4031181c80c4a54800c1d8035040c85403850a802501c02c0c0260b03240e00c03c0501034158082c4042d240d040140e0070103010b9100100380494a940240c2c041da05941081d141803140755a034842045041c000c0c616403038ac00c0e1804642d040c25551044c1c020742000002c602d807035400c00b51030704081541a0320039504075121342c00180d030a0005050501d1804003803201c80004500c4c1503c10303500144403500900d0001c0c820541200c910a4601d840c1c1c040e6000b441e000b0340443c070920761390b87c0c481000b4160b502c41241c0810b81c081000070340001c1d500c1281d0003a00d014024510741039041c81c00c2c22010745 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843606429 1250 843605179 843605183
    0x5060709180c1704030e090a0204061709030405120309120712030315091e0c1d01140f0a1106060a0303050405060d060e0c0a090503070b0f0c0f24100e070507 69
    0x240f100103c1840030741900c00d0a00540c000c0d281c090350005890f00340b0603209002049103465500410007000060382c0503008518a01000c240c1009988804031203d085202c0d42c0d1109920660a4040e002041004402080130460072502c1c4029a6010300384180c40b0441c510a100090b40f055800002190013500b22900f503056150319180f01d130f6261040b442c00c56012044442500c160110014480480e903c101c00d031105842c1040f0301c0083c001c800a850404040141310f04001950305401c2d030341900c030410390314404081030006ea243c001c00c3c01700030840d0308801030707000c0544101d80100c1c2c207506044d909642542e0305540c50702c1c505401c01c0c0c00e000c03046c0d100d846240fa0b840d03601d0340e000507040200003210b80a4030f81100a140c4c2c41d40006030040c00c0d9616500900c0c030a401c80358041040603150401c0b261103240c040c008030f848951041d6120300b0702070b13103154210640c011014030507405080030040fa85a0240001141c03000c0d1140001600d05000e00e02500d009080500f02203100390740588040d024680c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843607679 1250 843606429 843606437
    0x31f15061e021f020a021510060c060609020d02090114070c030b180a05100609060e150d12120e010905070608090a173f040c081905060709180c 63
    0xc0c10b028404034150042a40f0341d140703c1d0301160f80019258117004009441c2101c1c4c0d1520401c0c00d01c0180002d070001648640410b100307002600104100490300a04000e22040804540354444080301c0d40c065130029200740e002445a01e00586000d1102c5c0540301e98940280c201c5010904543d540758007050003801c1861070a154030700c825000002000b89101081c07140740a452100701804000b000e96802d90814100d1500700322040c000b2110021800750300c981c50b042d00c1400ca12900000c140a1a0050300113410030103050a40c00c0c0f51a0040b950800440000f0000c0003002225904075080340c4240600820035002030404002e41440340c900d450b0040404c0c41511040000b955641c00b103843c81e82094803a440300070075403a41120382d01000c0c90641c80c1107142070202c07040020b201c4190b02060b4101c040400b808802160910254217000c3d0040d02002e0300b1540c0d140400c04c2c940b49249a00d060880703481c86410002400e4611032080c40e01184d2004042c40000030300408404090302600484000308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843608929 1250 843607679 843607693
    0xc03070903050f10060609030201230c03133b190c0c14030307020715090e0106021614101b02090112060515060306040911031f15061e02 60
    0x20500074015032400c2a01500109040850780c0313038203000e0301c01c00d502c03c1040c40700d0500c0030000b50360090001c0c02081b01000170125106010300d03821401d4098503220851074400804c502420703543c40790f048800d56603d07500320300700d0003251202190011065609544c802c001c402800d0f008001d13140da034135048605400500d500841c9800035408648034105c50b40d00080c56a06c960f8140503400074110b00d01c4524801070f52841c0351002000e59954607a02c240b1000345803040c816040c0b28070403000000a40b500200404503541c1d1031000950b101ca800c502540440d004210008250407031200d006540d150241c4907007003107140590192103408003841c01c24420456415500b0050361000707010741c06444000d0011914601d641000e5045440040c200c040380a03460b0886a801e0355030304282c9a20590071140850000c101e80781120311854103000042c0c1600c1440e80340061207010100e0a1082e2656820800091030aa001880d0083e890701c40c52001c10400006181d1010400622400001441c011a11a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843610179 1250 843608929 843608933
    0x9140a0b040b031e1009141e0717011503050603071a070204060503030a170705040806010506031f060807020f0115030f020a0e0c0904060501170a020a1701080a0b010608010e0c03070903 81
    0x4072001121804401040d011060010381e0180c03007900001c7d03003064085025071515403481410359403041181c99840458100042081d44070301c510096940301d07110100d000356551016010520852003108010908120000b500307401c000030080c04850749001c144201003807181050100c0c2c2e003c480306036089902c8020100c1c180d00c0820041004903296030f00c030303031410790f61406910030031070042c0481d41001002c1104003e00300b00040c415064401c121601541c94807901002610147d10f102d4a40c612071052030006101030300101103512600e040e0702a51901049a00f2250132614581c48080850a40e0402400803e09003010085128800b41404003800d1720b5142d4004007117003c445144685c0e4000604503568281401081c1c0140402e081c00c003885003044a000075000c0c0d0042000910036030103c0c510007400c0c8100c008481c03203d03400e01e5013101c80d41c503850000d4980e98600d10640d0650340c1440009107003441040c00c94101c4c1d000d0f9590b8038568546e0030100c0c4481c3d00190050007084003142000c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843611429 1250 843610179 843610231
    0x80304030f020117100911120a092102100c030212090307110402040503101a21060903042105031c0b090108010e0d0509150a09140a0b040b03 62
    0x51401015450841801c501c001810480d144800300c0f00100e2071810312285400d00240c003000d50307410107800f2039040700c68003803107100d03006024498820300d41d82c2050000782d41c0b0561000300a00d004052800320012015413544802004988560040e03024541c050303090f4403241d22070200807076075180261420350110002e8044010680d00350b80e0075000092007404011280c400c450841006a03000c0d0308062404e4006500c0d001c08003000518261600d044404140c00014580400040104500d6060180040b00c158402162120b21068410311000c2203100000005441c01c5824603140001d01c00c00c00d01c00c01040104407042210f01c0d100a101c1c030764400e03440706400e29031540e501d400026145440e0080103001c0300107078041d4005034982094407103030744004180140340001c0750070195528006100402d00d08402400840c811210204065215640c0000c102044032040c0c480101d000e01c1c0b1004000f40c0c0c0042e0710410200344400c100400c0481f40000180d80e11504000c4220301380208101044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843612679 1250 843611429 843611437
    0x2150415050a08010f03030c3002070317090312210a2909060f0f0603180706030e070302130b03391c0c120b060f01080f04120203040803 60
    0x2030003068011982c801815440349540d8010446800900d070b031945580c40287c10134810f00c0000e01040e400508640d040c0c092201201c407040d90409182d00414801d900c001e40380c00c1d09000480b40000310440309209401d8810039150422402000781041c0005060642000c1d80000d89580440803090060b043d001b015150603407080300c4948001c41e0b15141403844198400c0c11804d90449886100820141c549804179801e80c00801981d8100c008200400003420100b450154260700030000420031803521440d41480714948010011245040d031500416000c0d6130340c44034480e04a0780403440030130251404401e40b400020841c00009000c4002501103800d1605044494809a500d420441c111100e2510b140d08104c0054210000000081e80010607416090492040038203141c041002403140a0b10390f20010141001031441181081ca0000301441003100c43c10f225040d000070000e490b500450450340301e443d091460800e0743c0c0d11a9284002402c40b4581e2208500c003d00021441d81d8040000b8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843613929 1250 843612679 843612719
    0x30709020901110d08190c090902090301020906040902041e03030c02221a120d0c0f020f060d0b0f0117062e0c0506090309181306060b1c0b0d021504 65
    0x1640e0906c0c1508030480940c40c0b0107007541c8a44e192a100c2410701351700c804c0000c2034071100280541e48140c0d840c0000c2c007a0180500c01da0740028002400074003410154010422a81c1000e00113900c5149000790010780c40341880007401207108140c0d00c40052078904125601c2c1e1410703000e2852189400c40440c01140e081243c1e0451800700050b8102140c54403034440800c8903510001411894048000201010380c0003a009105c2c1c0c411140380c0f01107644042c00c10340302031009000300391904500480740c001760000c199103a000d462440b85070922544521410902c08803100d070440437a031900001d02032102113040140d0510301a180010f45145654244000c03d0491070740c032080c5040741818000c1c1014000740c04031020754410461003540d600d55510b40c1c070130b46e0051112561aa580c800e0344200c550f10032540200324514140c000320300c0a50543c0600740305904140f149950307000010505040720051240c5903803081101c2407140052074101450700302c4c105089850b0f810030740c0d107041504d4640c0b142d1b049 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843615179 1250 843613929 843613937
    0x2106030c06230a170603430b042d0603090501050a0612030c050f0102030a0e060717060d03020c0d08120702030406050315120703141209030709020901110d 68
    0x55102d05481c982c003002c00342850300c80304070702c0c00d0b4902d0700c090155180c29168526054600300003c41c10380d800e11414000700c00070030800303005d140301012203c041000e030100d94070003480c8407965200824550101d101910202203020703213014205245260140c0302132201c0d41e0a07075680f0881c40303201d00102944100504540d10041041c42c910b00d001e90940700c0c014402e0841e546041820400c010105181c6c811481e01410040c4030290181411400c00160342c0001445600000500c0744420031503011504007544202541c660340c540e24021124108190b40400002c00004003186081c5130030f451050183d0701c00d0044a00202111012132081c006004c420340384841c000c100110402c10030f007400c540c005c600b071001d035290a0800d038000d441408081e0480304074070b101010036030355600d41c0d0030410401a0000101d5034050340d40e24040c15102402c02c2e482000b806882b07040c15a1142e0002900c20060340180540b03034480c10901240c0003508442300d840d04002894019201451040c00308100d1890b03141c0d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843616429 1250 843615179 843615197
    0x51c0f110307080906090117130c0608163b15070f081e12010f0911190905130504050d0c0b0a110c100501081b012106030c06 55
    0x90018101000e400309940c00410031030000a10070b40465807910001c4410a454104840040300e5944071000c201035980704190078040300e0400050061142d512840040004c140c5030a0200c41d03043c02603c1c1380e00c40000c00400a1211402141c0c2c0c1400c501d050601000c00007004180c03c4500350070b241d6208200700d18042185030714103000c848000d144c408105941d150200b10760b00d903103540f000f08070302070f000c0035010400b11a020490000c15a10002110400da22912200c414a00e862003c1c440d0b60a070140f0030703200081182090094240002803140a2400c14a40cbc6140100c0d078214a0700460400599180200e025660340084410014110400150700d160a1506501c0c0032810070426090000d18a1400c00040384081e00680c04142c044002c94a40b0740803000040e14041c06200c0380e010701078146104080040390340518122000b2a0880301031004030340703403180c8009034090428000740f040f40040d003000c5003e40b0340501070303155030a0010380503540c0d07111074488184c0c5070001400204450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843617679 1250 843616429 843616457
    0xf09010222080f0309090403030905031905090f0102010509030405090a0b030604050f01060b07020d0609050a171210260a0501150e10230303160308010509090102120a09051c 76
    0x500c0300000540300114035005c0703030340005112544001c0000f010103480c0d82240003088014001d0303441c122000f8007246102c1c8114078000d0318682001a0040c050051054a4405584140940b500820f00d00c000313146014240300a21206120091243e4586910b50304401c2c010380b4104031350381c40b40c3e00502c058030320129207030000342c00c1d0340307042d4401d4035000d5040c8400400340c0e440d200c0768041c103a841b510000340b4944900d8440d040c1000050003402040019082c4261010303c000180f041d2100444200420f5464420b01014040c003800b903045034100c203101c0d42ca610862100c0c41c10040308484100d900001b09a0355550940d58122284803800b07040920800200b0401e08a030b64101302c500103c4014a400d00b1030b22070b1b1440844510f1880344a400e5410000b03a05c00344210782c02d100c402d602c0310b42c99074190308014024000a1245501502007040003907105803040c802d840805040302740e00300301380c0ca03015100005030200b14002c1d81c50340600c0da07104451500400310800d01c2000c54407907420f00440c2d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843618929 1250 843617679 843617683
    0xd020a0c06020d02030307050a030e1506150f070b0709170d110109150f140907060921170417010510050d0507030b070306030c081b0f03060f0901022208 67
    0x99071281081d944200700700b00010741c010003a81e9100d6150b18200d40c03180310384a800c0340074054260300551280070395901c0a18110b0f40ca03a170350303100c2c13541554041000c1c41c890761817156504c40d0006103180c0000a00c142c0000071511150660010b54034940150426210307101c4940d5500c0c1c0ea04403850a5000045091040c1c0d04002440034039151036000b04130318101c41c3c940410580d100307000b500c071250343d03895007000a80c069808486031410035041314490b03180c0154000c1c0e848080d4021240828020800000d080800c029043c8155117800182c3c07660240554403544910110350a02d411000140030101c2e2419030103c05d0b2004450007030010075a402c0413210010303800f00f10742005005a501507041c02c080f030000922281200ea00c045007640710ba84501c81200240002d40004080c04980f2000088004002505a4000c040d6241403140300c02031100f04070380072490095050301a080b030b0000480c07901d001c404c401ea102c0c4030000098500f64144d800c070b4120441c084041945003240f420b040c0300d05002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843620179 1250 843618929 843618953
    0x30c131d24010c020d1e050a02040e0712080d060306140711070602031206030c0a061d01080f06100e060301080f070902040308030c0313020a0603240b042102030d020a 73
    0x1c0106a20000c1000c030000038461030840c02c01a0080308486456000c0020000500c3c4120800c0b0f2070704040b00c0b10758581140c81b440e5240d001d034032a0303040460441229030003103100c0d0100c646e01060480c5000c3c540d0f840f4011508441e50342d000503a0b48080000201c0e9042c060f202c910743d4030364401c0c3c045d17207000d440c0900107114060309a481075114a100f80710550b000421206000c40c491408081c9503500c2d800a40f41444040714250888030038480000d0617074200000b101ca00d26801001340040e03094000443d0404030844483c010844840041038417814060140e00103009645840e02400e0341c99004030745e80b54000e902483e900e40c0030306801081c88106210039006072804074020341c580fa142d9140c0322854000071702000343c005000800301c0e040c5026002c0300c44102d42d016040c030410f00d40e1104050020107514482c40303e2165680341008281d0902400d01d41034030144c07440581000e0030501c603a4546e0203000500f19030300d00301c0c80e000d0000d030758200011540301d07155074001c15519031140307009079071592 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843621429 1250 843620179 843620221
    0x140105010501021f0e0d0c051018030806180c190e0d0222090602030609061206160e090c0a0201141e040c090c080702160308030c131d 59
    0x4505001804143e80c04502160008440c0d40925904000c00e81048001d00e0000c04c100164491110030f12201074001c1600e90a09019009032201048401c95407029684851443d1405141c0706c1c4046000078002e03801a0341181001c0c003604035040c0c1d01440f840d0010819102030b898508003240210245900c0d10720100344034001e00c0e00910145040c0c01050708609030110003031243d010600180d2200441483d8445a4007584030140001030803418004000c2d802a54018090f850402c001070190130041701c607c0b043c1411070010172075680c59100003240d05101e1401641000704420300d214280d561aa6114041d0456403140c65813070401050103401c44035107000507050315034000100f0240c80c2d1541201c40d1030780120102c01c2041d40d590303e03203c0003e03c180d80008181920b0101030443c00e9900c40b600380d22410250302100c00560781c0404940e41c035421444010412003007003000540c11040000500781070b2046c5491481100c5e116241111030b59028115460000201d804009000c4505150300e60400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843622679 1250 843621429 843621431
    0x61103071806050f0f0315061b15042f0d05060108061e0f0a0b0901080105040c0807151d0907120f060e1501020c21011a030a030c05030f04121401 64
    0x1010765803050043d40954141117110380004030000305c06040c91b07400403020764002814155520f0007840020303940c648044d481043c034800c124101c07a0109140507003d014541101e00c609900c0c03202c0300840c90b030100100500c0d007481d50707441e8a6105500e0700c2c0700000c200e9100344090f0849604210b03c0914100c001840601846c40c1030381d89030340d841c03000c1c9031160b0041e4250559401980d10350880a0103003050040c00e0760072004142c0001041d942c190703c0350380558800d00c140c0321420307600c840c01580c8811a00943c1c01850895401c2403619014181d515100b5602599040d10005600c00191051408564503000700e215480d20010506443c8184040b0005080f0200500c40c144bd610307040c1d50f8802803203030340b00c9540750304c02d112543e00800402104010050456505ca0700102001e90000b10200c41100c1941c00c045000d030400d94001d5113455030200180040c80d0201042c1c40c212445040d00c40250343c18041001460b040040d02001403000d00f0303202803540c00e4460725107410496080f100b00350468507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843623929 1250 843622679 843622687
    0xe010903090303083301020123060103150504050403031d0a080409050c070605043e0f0a0f0816061d0f0316140901230d06110307180605 60
    0x9800001c0e960580f80c041c5402c0030f4030360f1101e070007035040f51480045044690b0440c0741e00480d40e100c1e0500c42615007081c0e00034801d441c148041e400790805452030f03654444203060009140c40d4404e500c810207041c607400e900800329a642c400b00d0115641900c003a4006522140d281004640410343c0294003075005005090511240c8c468140a011740c3c01020382142c0c607113002c2039588803941c0c19100c1480d000b07102084a4101417400f02c44840e9640c41c08811088170b00e00c0f001c08410030100000d503000c4c50800c0030030500807040401c9071280c11011541da10052041d4003182098a100c00c40d4090980d001c0182620500c000c0c1e600002035166014034208400419444248007009400c01c1c540034007502d195291401040009061010240c58607c03000000400011746603031020408064220a45200c0700c83d90301c48041d0108a401040d0540c180c0e1400a4610301d24204001d14200b0f07280200b0b0005030710b0040015030b910580c019645000090b05420501400000811200b0001e2505050581c50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843625179 1250 843623929 843623933
    0x1401050f01170406021c0c020f0717060a0e190507140409050d0804032304030b01050301110a050c0c0d03020c01031b0e01051b0102070f060b03030a0c1119060c05010e0109 75
    0x98480b00820081c05103801040300e244940350340c9445884180242e400344146054000000e503074403244240003855101c0c208000403846461011540d205485c1e60252415036200a1000050020301446690502c1552880040c00d2090428058858410f0010700752a030b00c1d01707051034041171010340483d20484c82c0205070350002d000011041d65030801070900070700540da903040641d80c1541c100c9818110a085042c01035268407854000c00a8078425400c120701c0c0c0c0d0b00d0708141800c136250640d140138010020800041594050070143c8807029501040740e4409a410000c100e802c00c800d031f02100543d002449940c825a0580102d0101100541c008600d01d5000c42c0010600700400900341c5c14070200107200424180044000c0345c2c4106803e009542c3e8604500d82008859000b2006a40e090714001d4494031031f00c0e020089801110840d034402101c56001d4840701800c1c0d460304211644a0040110505203429812803c401000e458946418820140c103100e03080d129030000008250b40f4100d12100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843626429 1250 843625179 843625217
    0xe161401081302130f020a02190314250602180f0f01140403050d020c030f0c060304110d0b010902031005010c0804032a0b1b0115090b0f041401050f01 66
    0x1a0000184050070100300307660001c83d80402407880c1500841c0d040050000c408074171078004000140e21359080303d19500100301c40d0b03c031040b0b03051070043c0024250841c084210b556200500003407052090f43c1400c003044444860480c6811402c110f803429000f007042050303c0f15580d8005450303001600c14003022480040042c0200313803420b846a040c040e981c8030800d0045442e5090301e0103950300404440001c9507510001c0d40d41c0005170000d80c841c0c460000107408010021035100034551020301a00c2c11034640c4d1b81c0d1801d00711040c010242d040a00c0d0400e14001c1a14288054000e0626142c0141d49003041e900344001ca088503002039050084415802000030600c034226400c50741c01042803002c0001c2501c0b044104072404215031000e076503200021034901c0610340100b20618910021590b1002240440c1742a0344c025040485080806941000348102582041803c024010810391200784d82c10001f5080b40d0440c0c1c802c1c1613180c10100140250705010503550041002400e1022103400709000e111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843627679 1250 843626429 843626431
    0x6030605040c09021206010f020102070501090b0609010b0a0e040903050c0105100302090c0c0606040f06030b07050a030606030c052b020409060510020708060c0a03150b031e010b0702040e0703060e16140108 90
    0x90f04018948c01c541c1c1b0018802e50645104a82c010000c1c0800009030402c00118501552114422001540006880421501103514a03082d42d12100c3c094200c4500b040f00911040c1c009405104041003a101d07091000e00c00d00d44148208e001c51081a4250b0062040c89180100031140342003080107440600000094516401003084901040e00d0448501140c05070032503602c01042c0c00041001d10582d140c100d0f000e8188031017076590070820190b075881e040301510643d288403000305601304a8001928185828800303103607580c100c40310349089444d984c802203901c1507000f010100c0d07540909001c0303440c0899102d0100d04039440148180f40c01c06450f40d40318100644004100302002a08408181c000d81241aa16842411840305152386001e02e00796540200d84e0b0102e02d85400c440b01c000191200040342c141da004c3c0c5040d9013001d01aa00340002004502d00c202850303c1650700020011f1614001c03e00383c1400080a44001c80000c030900b50191003a0700b04411900924030300040d1664825041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843628929 1250 843627679 843627691
    0x303040605040e1009020f1804140f04050a08030114190501090e100e0f06122d031e040e0a0b01050f030402060c0f01020309070b0403170a110106030605040c090212 72
    0x1400668032041c825250b1301034541e100c414a10b00114030018408103c070701400c200d0303000b1241041c0254000341000111503014401070000742132100801c01045c80c0c001901d42c4244100704590114100341c03a81517542d00300b68031591003112a0034507055181400c451901050320030354001444a405d20001800035021400b903800301e00d00705000100c2c81d0030341760b1000e40142803040006280d402d01e000190104c1804403082c80c080c0c0094122010300074400500c07100c40f91041ca40c419800450b0001e0500d1008246007480074030321050008184080040521b400015505240305a8843c03414a6011002c58018541c0800901d4031881d8801e030b90300202121810303500060103503903aa5442c40000d6542c0140b0715003104910502c10f40c0c1044400c15402540102c3c0c0132411184610b41d0791040307a8280c4181c0c04020310311810701c003814084200c01000342007141403038103143d402e8080d180b61660854015500a40700c15850b0000d000c180032103030100b0806011a10000d5251603207e400c9155000009440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843630179 1250 843628929 843628949
    0xe040203070b0715110c120c010b0901080d080f0c0319020705030304030c170c0c040905011b021b310f0e060a060b03041211030f1207030b030304060504 67
    0x404556080c01040050203210200c1c640b9450a0300700b8018048400c011100507502e0401e40c1101503200a050b101c1d1080490018200c1ca16440c80f1140d080e04008401c4d000c0c5d40d2182c0300010503940340c0d1042800b822400008100380300302014020074020f4040c044a480c40901c50500c0a420341c1c3c2030450f5030100c2c00842c140c0540c0541ca4a0703900074420054098640d004c04014002015031200314080b41c0e0b800b82404000007030649030420000e02c914424440135078003ca0b18500d4600f0640c00030014240a50000034020a200000f010780710031040508005812030720600c90051540b041b0754250900946040300d04000d45030320214107840d00b01d12150a4001e0070404080070034560404d4001c0d002d2001c00b44001c49049182568520080d170300542010b0a084021481019440a80307102d280c00540f106094000e04130107403251410f5108c20f0f40b0600040000700204d0700408002d2030b1060560004114610b402480113040391141e9148600c241c00c100b204105c050f13808802e407000d4860f0401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843631429 1250 843630179 843630181
    0x110118030f05030d0501060c212a06091b081204091a04060609062a0b0a06030b04030c0506152202040305150f070c1205090d06050906160503040506010e 67
    0x82c10342ca180203041e01060902d007050001714441e5070242d9921844c500c1100279000000420b11200390000b043d4034038100140c888216151903910004080c42540c1190616180d07144180e12503006460303101c4c0c0107983c0402d003540142c80c000500f01e01b800c0100800000f13440b00020062014080707100d94400c3e4400d080d11040d07a83d0300805590129102c2c1e0704024400c10003240e079004082c0c02c3c0d000d54805c00c2e0115049030803264580310002c2d40200c051700e298000b0241d00c4c0c083d170360f51203900300c01402c0c0c40e00035503480c0070101c00280f142d00740b40d005901035143c0e418036920901d4136174640000282800034141c19103004500a032a00e450080c04008402d240420741c42900e8110b200034010b507440a840380c81403014200e0890740b0f105419005990701284030920340e481e5032080e1598040c11200809044085201c14040c9104001402415800500006100c8403580708e01c0b0a03110207807901e007491f403c90400d11240a2042c3c241c1c6c000c00415041ca00c1c15850543c848688030f2505101d4101c070321403004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843632679 1250 843631429 843631433
    0x7030f030c080d06170d05032208040e0c03010306060b07020d030e040b0d120801060513060302030703060314060a05090a150902030708120306030105150321090307090207110118030f 80
    0x1e440b02ca44008400300504c599a141441100d4016003076003106025515034541d0b0301c1c0c4154200c07881960500344400724000401c0c01c019500040c03410940791904180b0020a10705047c80c0054000c0007004c544036100e50650800d001200c510b680030343c082c8401040607200689a090b0007140840d0941003452481c502400460050115402e80c254048001004e0703c5c108003020500c00107040c0540e90701ca909030b0302d0300410b40382031248100340b25080700350300020805d20b80310350000c43e8400d48925021400e40d90741d82d1112418444c1c030007400090741000c070420005000601c96164010100d10040005840300d440701450b001c1d09007120100e46485205039015900d0130003424008010003410ae4179201c5c1022004841c50b0010f0719154803031b5017403c004c50300300c0708110101000c0040007800303400c0802c4401010400080d80c41c00d00406c401c002e2004c1e04495505000000c004c14040d803025a50704060710300f98205c080801c040034148000103c83c240c50030044131108043d40da109811a807204594 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843633929 1250 843632679 843632693
    0x7031b140f132703020109050d0e030307062a230a0c080c1c02030a0f1404150903150e1005100e071b0c06020607020a03050306040f021e03100807030f030c 68
    0x203c000941241c01180220f042550550152046c0c6004109840d1120540482140c0b01403880380e07411341c10380c41400b203500410400ea1007410405001c40c44034000f802c0210087c02c07480414a00380010926501040401c0500840311154620b00c81d00c050745000c9507544050044041034038090043c020204800010b00d00c104110790102c1d5180c000032041100c0c00070300075070b82d512150715400050307503610351340705141d0042405400500c140801503040030300b000d003a100102d0183d1422010440720200000205e0301c10800310310300e910f41920110300c411421410030715001c000384501d14030300d180400f08107045403014460b8040d1182011161129200d1450855582d098a450400d440c0d0306030760241c0030000e48408400840310700380c09a0b105a503900d00141d888003440b01025010039001c10005030f041c5440d40c0500c1c1444210980181810300d6090000062079026014003182c0c4400818070851403400d404400040c100d04000788074003411a665003540b800105401000d2020b2a4003034070400140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843635179 1250 843633929 843633971
    0x52707211401050a0227130b0118060203040f051c060e030714030d180c030b1306050133020309040209061606050118091106090307031b140f13 63
    0x1c402400302d801c00b40140301c0254440c0806a5818000345840c0c0d4240c4944441c01c00c8036900100611000c1d03003071681c41d801034010b071141310b030401c54290b000a0b214100c00303010401500d003a41c019500ca50400300481010301c11a0083e6104401c640120480c2a422482c1d2401140d03011502140841d101c0705a41c2c5503006100340140001c00b03500030303a60140000005480746080780c60341840280084101038544d28039003200600701134004001030001c103000300401608540e102032003401011036900c41408480c02a00500d5644812428007889814251060703c076000701c04000b020395840300d00c001b0790b9a10403e4000360049030003085035460780d5101c41c1520144d070f01c0d50340812000040d524120004110034003620030240c80010070342e80401e019206e84084a54099101841c0c51400d504000344c1da0066030b0540c0e49885004800f0001503540164000c1684031140c00d0200c090609200800444110080c14014002e0501002c1c1036658002c68086130306900c400010401291000c00c94140741c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843636429 1250 843635179 843635213
    0x71106070207181a03101e0203070c060b150a0c0b1b0712090506181e03070306020304050102390d0f030b0102010b220b040b090c031905270721 63
    0x189003003181c40394505402c2811f00b17096100c190701040311440240000c07804156468400241405046000a43d42d54449242d06500500c82c4291218400e04408194014042c110010b0036501d104400c110800140c140c00562031145246000081080390003a4002c007500680203c114840c11070403140603214000240a0140400d5034982c04d08000c1e035010000b5142041c024542c1064041d0a01604000300001c4131004005c0d1000c03501c0c586901020790000350050700c02d95401c003c20055404442d40100407400c84c6c9400e2010082c05215000c84d000c4221088011504502c8465284540c0081e85800e118900d0500050b52060140103d0042c03410030400e6404c0303401030000d41c02d500034000855050703125105051110440e4001440705441c43c0c49d4001c3d13007200400d8045040d4802c171202465101d8070f0000d6415800d8104440341c02651801e0b036a0750800c98910f0210020245c01e2100000080351010091500c00d1425150a541082025282188940c281c20b00000c20010341da180709070078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843637679 1250 843636429 843636433
    0xe0303070305010e0609040c1a0f0315030d0f0906200d030609110708040b0702011205011211060c0a02061c1b39061103071106070207181a03 62
    0x11800e60400340c01000300380074000451001e500001e440e4541071110718400c030343c02448074804070300d840240c100350179040305080c1d038044080c0f2401e500fa620312009541b0440710500c411150140c04010b250134080000326000070050760381c607074088441c0c1000e80c880407a84145002031011605054400c003291a580c140708450003022180300003651700d50411000d80f50f038110208006081050800c099200c3c41400412000041c0800c01030030720800d000e0042c042c01810240c40801040c0500411100c0903004901800300703400140050007040700400744555000e4a40c0d0f4900006120b40e140d82d1010404000d100d0340c40014000241d4580d04004400080450030038030210150200b200c0500040e030b145d15001603461250f455940185201c40c000217010322210004258042c11100420410041d09458079500d45224140110502c0d00841c07103001e00e03948882621503402e10007414502e01404540455002460611503000c20000e00100503400120010720240700c20782c000320040c003203501e8a5145c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843638929 1250 843637679 843637681
    0x1e06151e040203040b07030605030c1f02010b0a06180f21050c1305011809080f0c010b06070b0402040b03010606272105060f1605091504180b0607050d0f030e0303 71
    0x30031100c0c446c01000725032410301249858509056403050124074181e40907850f00622500c1201e050b00d400c1c0e0014007131002042143c154004154200910b5000c0130024101d02c1c44648403c00008d002d0000c1c0010700310040035286080014031400081511441a1449884164003000b0040004400da0240686006038116100101c5002000244650401004038818188808685204400b600780d40003403200d0400c03a1f5418100981d42100128031055940c800c115050f60340c8101c080d20072103115101051440c641803040c0701c140c0b003000174540e0203613040040a02850742c000402e5000143c0030b1540002010406688004400f8141d000000c41010345031100404a0380202c203022407070041003210030343c0c1c4501240b680c0000c000c840408209201160000500340716400401142c03e004002d400c040c0c5e500c8600c241694050742c08920100c2640d0300b1401c0c0042a401054030207002240d50300c1c10601c6588500d0384440e00d0010607001c1200441c54050b0f464043c0d4040145459008201c030b0322 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843640179 1250 843638929 843638933
    0x1a13090516020601050301020304020619050d111b120a0e06070b01081516090e060d05060f0603010614060301030605130507060507150b10050c01110c1e06151e04020304 74
    0xc1c10401d034a920006009281c00480c05040500849026076405405c032881c1000c151410309541c08103443c0002000010028a528620309000704c0300c0d10f0750052222681c40740b00c4c940c072001c208119036070009103401c5110b82200b035040400c240d0300c560310310b0308110519207030660005600d4401e1060080c0b040c0100000803485900008180000741d410072004000c544803c0f20100c1401403a011007000035604400030b002c03002c035100307600f03401c20f50141002e01d0044550303444505046040380c03890b940e401c60004000040c0381c04d0085030010310311032191003030244854002c80d0140c44140406480c3d16110000b283d040090341e404d14070000d401c101602e0003d525220014065032120000365035007200b4409030300d00220140700c3d42d44080d030b00400c48c06540702007080a54443e000019941555541c558082d44900065001014100c1c914000760015680003000c4202c403003000028040c16902c418204400d2074502146030480c4030003203961205001074004405500028114060740040c004024001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 843641429 1250 843640179 843640201
    0xe0c071b03030f18062003070f03080109060b090d030212040e010302190503031209031902100e07051e040605130b031c0c1b0305060103030503150a1a130905 69
    0x5582c400c1d503e00f80190b02c00301c8120b9401442c0c07403160050b03042a80041084a002d0100742e10024140e4000103a081c0b900141c840c01c41d000070500740c40301540105c190080552000d081405032105100401905040c0035005040303000d145d4219004900c2907031304400745802004103403001c0040c200315541d9540c17221420048110280b008a0041d6240e03480c0e01d8440c801c2030312800c140c8802500840c10701501d600c40b401568005040e02c05540410400c0702c80c80b14890440c1803564240390000c012120070071070740740e0403110888413071042c0c3c1e0881039080c00341d030392200c010344c2480c500b1a4103140402c0380360340060024105a0300c0395078400b01c0039814080c403020301e4000c45c2e0000003c400b80c0c3c0740c0c8c44d017545400540140f441c041c500042c8bc0001c1100c0003d004603034950303070440d501c004064682c0c4c0f240e41e0140381040c203030405d601084000c0108540344810b0100c640c403c44055800c0e803996440d048002c9a16580c45410300c0d04244003050b003800b00c2002040c031100030141c1b11002d204a084c0281610 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 843642679 1250 843641429 843641483
    0x12051302060a2003120f13080d02071b081903050409020415020c030601151101020906041403061b1b0309030d030b01032409050403021516030507180e0c07 68
    0x5042e185000307100b000064010007902c944d440c0f0500340e8001c41d40c46d02c8916890140003020840c00318403400d14036010038401ea010346005661f0000041c0c0da00001d080c0344001500d010149102030002c1d000600030668007040080001074480003010b20b00c1d88500e01030b2654050340d04111000b40c030201d000240ca40c00c2d000c0300b12a07003003107400741c5240203a00c81c00c0c15180c010034000d061034a40e58504040d10148104450b07120450124001410201143c00240c50390344542e0100c0e07080c0780529804802d0745000c0c031440d9049000b514811240c0c28031a503d54105000308016210095841c5010354001142481100c0a0040007000d40b1640d008415003d002041c01e602c02a0000340381007488481c80c400310083c03015440c1450020a22a0301c1e0009060142200a10031000c50060140800d40003220410960045850040a06180042d0724008044510041c03400c01080950401d81d030b444d007000380785070080e1000b11005903000d070307100304031900140324007030005010728040d090f01c0b82c0303600309400c6203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 843643929 1250 843642679 843642707
    0x2121c0c17092d1e0a05010603110a080307050c010507080403062a09050d080904021312120302040e06011d1302070c060c050d0c0f17130504050712051302060a 70
    0x20707501d0384001040d10010860351501c50b4800354805000c04540740b4003801300d08044c0451000300c03000b029a6582e10b03801c0d90059030003150282c5c03442d1080a841e10700703180e58401903d1000d0003141411030740e0300d9803581c80b540e03039030320a0501400062036028400104100c40203580c0000303040c0702095070f480000e00700040c4a501350791907189030589100224824801d103000c03104014500803c0c0c80c0b40d5242d030031595001d56041540030707a007004040d01c0d003680ca8034980c00070072903801e420291181ca8188012072059140010041503c1000f05004c0340b8507120b92240c21207420300c1c00d9000c4078060582810240e42c8007565650041440400041c6202c098000b44116032089c000446166507031042640c6081401c4401061504811076448845205804841c0034030f00134850300c0c8420200b91207482c00015a07001e0345501110000c0c50004040c40c9459010043ca800d40d070412061034641401000c4815092801e041d4a0b11940403c0c030381c05100f03002c6042550024030b45541e60200f2034000c6c1450007c0044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 843645179 1250 843643929 843643963
    0xb070e0f060a0c350309010b01050405010801092f1305030601030c0303050703090f180c08010e1503210a02120a0903080c190302060702121c0c1709 65
    0x42a1403505125054440048840d2180b40c104002c540c0d03025204003100c903c00c014400d819401902c007200c200200e0035100511400c260342d0303003040c1d00e040342901c0c1700f0141507043c054100010885039174490300715411a003800d000000d580321101120b4079901e01c11044010301d00e1002c081c40c40c5c070880560091604038500b1802c034600b56950400c1c1a01c03018241300203030180d80320311300400c0407a00032801468102c0c843d25181001301d8940412603a501c1c90ba80040080a0080203040c09040320781c4110821074200f402c10741940c0d8501115220303001802400d40c1e45c451a0620f003094603440400042a18055914400210084844102445401c6400d50b080180301c1c182c641802e0602c0381040300c03854030303240d554048050300316120748455500c035007540f9102d07201d154425224440d03910140400c00e4480d82c05081c0c03030304007140d0080c50040ca501c600103008008000d070340840301114000114050300c402000c46c4800603030409840001801165600701001207042103a04c2e007011620392102060054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 843646429 1250 843645179 843645199
    0x90304050109050f1008040507150206040b010b03150609011103030103140c0d08090f12060a050108370314040b2713110d090803090f15070e0d0b070e 66
    0x104000c10284102c4071250807034060110841c0c094410180b60f907215008800715270050703643d1018402002c0201c0c22400050700140240410041c096600900500c1d11700d150a00b9800c0c807140e03000c1012080300c01c1c14131400c80021010040d9004402031440411040b09403900c960390390038000860b01d200100f902c501d015010040000f40f6244810983e000d4014031054104408a014000310441d401c4000d648840481084e03821007204014136441128010030120b82540350800d603c0c45c1c0340c1404400d003803000803407159858032800141109404901c400010b003642145040a0340c00059840d0100c03008100040c003ca68450020000d02e22482c0200b20204442440c100c61210380340d44d00c996a0340b00308809c6601c2030180c07154102c800b2003c00311b001c00340b518480021020840b030b152803080b12140c01c0401003109900d0140041c010f058a240302400640744849422507015400404a00c2401000a81c000440d1a401d1140c060710b940051048494244200c02400310642c1800c0c42e4800c2421780 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 843647679 1250 843646429 843646439
    0x604050d05040812210702010905010b0f060a260709030506071b0224030a0f0506060c07150e0a0f09180224090607030c021c050304090203060105070b090304050109 72
    0x1080b40d0440d8801400303081201c1301a2403003020b6900070138240b0f03211200071000e16074a803041e01a60340110041d8000080c40000da203032141c00c2d03d65910810380f25004c2640390a1041e02c445003240d9012420b4623102901611080400c026110348101c60501d8203041d00410584a802c460f04a0a0342d001e42e08452a43e41d866204540c12a094001e41103104424807640c1c0040c2881c0b40100f0340240d10035918030390000c5400a0303091319001240c801003080e03203940c905114140c0c00d200d2a41c005030192201454100c81ea03120903035403582c9100d01840170340351050040c0e40c2d51040380522181e0f10300500100b040e503a1400078688840351401050951403400c000001c1d205160b45041c0c9409038050004410040da1920180b0341c60300100300c46180700e104001403a05070340ca640051035154444c1e240c0038210311040c018009510080b11181d00c0001c4c058840c140402d5000040d907045078031001c00543c0d65079461740100c6242c025408001c000c50440e005000c419075000c4042c00036280d0aa80340d00d40c031599a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843648929 1250 843647679 843647687
    0x603150a09060f03142d0f1501090b010c02030a020d05070b0f03010311040b1516080c15090d091203050d1d190f06110f0a020105060102060c0a0e010e01021006080604050d 75
    0xc2500d81b0380c0d940c3c035078403c00c414140018108038050101c01610b01c01c08000701014284441550502c1e00040a28018000307a0494031440001139028a0091010101769000c2951400f00c1d88010388600e031000686010443e082050300d001e010a07081094682c010101074043d990001e0000b19044420585101d1b02030400344110544e0720b80c0245159014045051802d05a610000d8802d49860f00c1042040100350000000c090280581005080c1c11a000445030255400034000e0701d900d4100c03855032134989a1000030f11701503d0540a4000140c0344c14034013601c0d01e204e51041c0d108050b0500b283c0c15901d4048140000d0484400c40c26540c0310000c0d03070031a0035004c0040b4001090007440c1060400030446c42d5000c100152030150441349411480ca4842445404c404013010042c0c1d100d8007004000c0d41c1c14000c40340c02554640c0802d003400c6003184050140c600074211039041100000103040168800c110300002c10382110f8042040544405130303240c40e494111815203081c4100d4103180751a604c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 843650179 1250 843648929 843648943
    0x60309050616110a0f020a08070f031e0f200102030c030a0809030c1c090e040807030f140301092003011d0702010902031f050f060603150a09060f0314 66
    0x40324019201940c1e031582c21030003288207449184200f00c80e5820185000c1c80410480344c16500900040c0d00c1e8210510400003684039540115810782c0041d002017101d01400f04042e000c0e641d000801890742c43c08181d02c0c0e50540b114001c060700c12000c00f2410000c0c0002c50031320224000c428030690f00780110000069130b9038813408041d042158402c221400c0500e10500314150408000c2e0281e070301e84039600e14103510b00501c4600360f00f4072902e8070500d100c01c1c540101c142c0d001003901c05600101c0746070544420145014070040a000d1000e0329190502c4a44520310002d05844015101502d9584a69880c40104450094040b0300c805141844964800c0741c016070303040790107054040340c9202c2e00385582d110040c40a4004010356484080e00c50060b6014060000c1e05003221003040c1a010700f09141c1000d40d0406005005440c00e1030043c02210340343d2000f220380c424034110545010380001c8020980740300083e44081241480c06c0c001140c100d00020000301160300589104180d0307403540c0c50b81d07030703c0e084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 843651429 1250 843650179 843650183
    0xe010b0f010f0207030b0c190305010302010e0f060904091b1a09221a0a0504090f0228030f03031512030c06020408010c0c060c0e030312090703080d05090601060309 72
    0x11084448030003a610410081c200c492440c4103450f640d507034a0303850180040c0141e80e0030f40c240201240d80d00880c5007200305030810004500d010300070307545103030006864030407100a21402020b040c00004070f90707151070b0100d40e00f420b00540700f00703d00c00c0d0711b08200e100184424007030352541101c074600040c0100c01201c41a541e0080e060240e24002d144820071052811a07240d803c031241d040070220f2521102c500c07034044e0700600e8000200350804240c040016222240d00424800c0307241c0600100031840c2d515a0940555060300c003501880719102d03030022542000780c1c2000407111b10400110402c0700b1048401a803e00c00c1c1c50034403480c074580d8000314080750715010359107207940d040140c0c10100c1c0c843c4d00b581e540c0c24003030306005161030b49074402c5070700b500c0300150700002042d11755124904121041c030030700e0900121132030920120001c21000035103c1c407411885119050345840454403820042c0321030001580e1002c40240d407186002c481c900540f40c100d50889850146400000340ca42c028000e1100c12a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 843652679 1250 843651429 843651439
    0x501111506040e2104050103140403080703050919060b041523150403050c010806060a0207061206120b0708101802030406060915030209180303061309050d050309010e010b 75
    0x103941c0d14140030080c03140c694291507900c40c24071201d1151001c000d103888885030f8294059980c0e41040005810341b41d81c0d10355024040b00ca4003c0102003a07010400075000003803880d000c2101c3d00d8051415140c410800c5030314800e810048074010400005a00c0700960850544050101040700761002564040612444000480d07404140b840000e040c1d0071032040c402c008140c450070407200240c8441980182e0401c880300e60200300500c0d076560300300c608107520140486003030b840c00d1141c100003522080144640e509107c0b4010245c88401c4031500940044d12501501440c00800d07410801140e6100703803401804100000e0202c1e142c017171200000c80a070f65a08002c0340b494041526203d0095000600555807599601c101050281c058090180703828101043d0200b40c0d810b500400c41d000602510911140d0701d00104007414902c08006d89034041011203d0b4505803007445180da01a024201004080d8054003004c049111703001005540506083d6008000b08500c0d9810341d822550103500c41c503800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 843653929 1250 843652679 843652681
    0x5030c0111120d1406040923030403020312040e0108070f0b030414070e010501030e060930030a0903030c110a1403041d090606010c0f150216030905011115 68
    0x1540190000c281d1003120404445010400640400c500d030082c1d501214103039160f505051103504c1003542c154001d8011241080400800c0d503d44441c09409682d0240082c01c00030181c013010000d10658000f144c0240c01c1c2c0c0d80f0089100d4036070300c003640140180c185e80c90b80a000420f0007440002c45905858010711101041801c1003030462523908010011640f42c444200040c0704840103100d1350300100341c1c00e0301211071541808005010350344543c29100781c55000d0303030403c000c86800150103074a984441843c07807a42c648000d0300b032054151040d1100c665200000600c07024040d40c0d070056403024000d5404224000300c03840e04a42c00564881004519401402e000010a1522801e1003201110400b00d901d010340c3c8440c948041c00da80b40b0a080031004040c100955160103204440d805031003483c0c448000303281d0b07a076000101d952410014082d94040c5c500c107001c0e450146d048805154107280352038103500321441c0080400c800d41c010f907800500d504000141d0000005000d0300b540e0f224100344111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 843655179 1250 843653929 843653953
    0x30d090b04140a051e030613080421200120060a050709171b03011401090903030213080c040f05090d0507023111070f0206180a0902120c03010503 64
    0x12224010380340b80d0b12407003200300040c0980c0c84512586040122025400203164420201400c02100130980f481601012541e100080e440d101103d087c0d070031010151000700c04504c81d0102450985100900589104c2c1d5603200002c600a40d80d6003140099803940b54080215600001d900707103a1103c2d48455020001081402000c3e41060342e0050462034103000d42c1d07903900000e002500003c81900c800e40c00c0764420314041c500e41040b000400c08160024440102c0d11b40742e5500000051080d8883c0b16a04e900940070180320307030101c07008042c0925031003a032a61907581580d01c6040199510344901c0c94002015020f003a41e010702441020014040c1507245940041501c0b00c2e4010f54089074440f40b00d80c821083c6000c10030210b541c2441003860011213110902e40e82c0c0803a0700904a000c01680140282ca001170880c1c1c1f038403060a68103441560b00d5106a2040c04800c2c0190f01103a40d105110080c081081d2400741d0207000c1c190300750780241145403501c0c0c1c04406644401e005094040d04281081d02d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 843656429 1250 843655179 843655199
    0xe0c030f01080a121d03070605040806010b09061c060b21090610150c0b010e0105030d080c2b060803031017060a02030711010905010b0906040b180711010f0902030d090b04 75
    0x250116034040000c44081c3c43e0170000b400c1150320740002020032800714050103031200070066180581b101c200308a1402440340c001070928002c41c13807008030207846c8a88c00c070340007003036904800014900320501c9600e445100450303180640c001003045104c45251400608894800910540a2041aa05000700a082c110710500a80c48001d2440500544407880c5001405000200d030013041e40405408595040000305400c00c20307410402801c100d5800c2c00e0200e08501d0324111400d801c240107041102c032000c00e081c0d85c1501a05820350b040a8030f4048000b07042c0e07402000542c07184001c1d41842c0d00320b5455a41e603080c01d00740c00f406500150710250000d00d444146500542c0c1200c120300b000212444c01401050940c2d00d501011503007a51260904512414030040c01a080202103805110f03690189011039182c101074500290505414400b060205d800340b80c50910100e1104001e000303a501c3e80032000003803d601c0c40c08a0113845503e42144000d03100e004440141e0b18908a09846e107071800c20340346 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 843657679 1250 843656429 843656447
    0x20f010e0103020c060f07020c010206090309042003041b0f350604030906080f240a0803070317061c0b07090b0403061e020408070515040e0c030f01080a12 68
    0xd81810750810030810111000c0020502c6480d03000b1420a007071a20300402030030040b4205426040d907000700b0600521b60004000e0307840e600000d890000302c1003605848800401410b04c0820b80ca114008180403c3c0300d40c18001c0d4491100c1e07071072115105543c8403003007021a041071080b0250003056250b01251046041c0328203ca04134001c03500395295001c91070351810007400340c0342103011400b81c5c50b0070007400e900050416030000005200070110700c0e0443e00c007840c26000b00c1e50b10f03054030b280481144079580c80070540c2d400340181e00c0c116034079000540382c0940390f0705060311001004841d040000307689142411740300c0c1150306004951080b6401c260740b07044100700c0180003c410320452107000320b8181e04100140c001180144408034940140c024841814540f401441421900401042c000324000150703842c122801035804004280503c00554000e000c4c07070b005103903d8805c1d0030903c03020070140e8002c0c6002d01c800032003405103039036203001c40c1c0e80d01c0c100b0300c00007030914400001d910b08243c0601054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 843658929 1250 843657679 843657707
    0x240a180c260c060711180f012420010915020a03060b04050a0308030a09060c05030612121603051603030b0a1d0c0d180804171f020c0f0f1f0504020f01 66
    0x1c0d203074444041103480706810041f501c110180c0303c3c000041222102e401415a244882005020070f20504840020304000c140c000d0030703c0308011a940b5020b00b40d400d502a19200f41c00c070a00810300c01c0c66200c1320000c2d5201d1141d900010703080c20320115502040307204540c100c1d40001c2c10090150b24550318a003407500300801000d0301c50350314000a0003181d00e0780a1402600e40c10703079032540e5034503281d8104104410200c0070150360741d1042c001086410b402e1011140710074482040c03410000558a0103e41d03c0c402d5001d00d03102500c040145504264054001108514048880d0340343d180e2074013480310018003040e0056800c00c1454012038285181400100994950b101c00410780b0b0915011401c424403840a04441900c0001020011440d918202c50420a0305001604903c0380304240c4500340410441c8881c001d990004558002d6030080000040d0900f000c0140c0d0220021180302c65201c140d11000c00d1a001c0c01d0603005e2440021074030071144610f60091540568800c0d100c011611203101d0131907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 843660179 1250 843658929 843658939
    0xa0c05030c01050406090b0f0609010b0d0e0a233c01022703030a080609070c1e05010b0901031505060a0f03060608240a180c260c060711 60
    0x1801c07800142802030600c220301a0102040e80c0b00c0d249441400c0c018000c2800d2034101c206802c0c48026070b51030502c1811110400c1e20765803581f881818103002807412101e901001d01c00d20000c003040000340304040004100302c01003030181003103080c40c20f40c90f4440c40180c06000743c0d50b0000b800c1c0314142c01072244214100e00c004032902d407407114092803c80c0c1c000b96503c650044180280e59080140301d80b4005405005c0c0c0c05581050410b00d4090b2081d0f5000c2d0060b03208540c0361001500c1248202d1a92940941011000c14103640f418504180110121429103895083c440c10310445c2c1000ea05090403240d02a0304940d96040d80300c040c03002000050721056000e480c440c400a0000c0364140c1140146015403c00584c0e40e207421401450b2114802014109841d40d44040451440c1c44504a502c82c900c5031000c10803119461244a951031643c0c0d004000c0b000c00c003c041580031044108021884040003c09400841080c140f65900b00f80c07000a40c1c08001004050002200e107640e502c00c3e51400b500c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 843661429 1250 843660179 843660187
    0xa0e04030c1a150f01030606050409023919021f11060910060f0509040206070c03021005040501260a0c031e050f010603020c0303070509010c02041514150a0c0503 71
    0x46101900b03401500ea11a20b4080c01c40d89000d5490000d8a4103031000090a00300441485e1040280042c061446844551076010801621075103010512005510300740c001c1c9040c81c10700c007001c01c0c016070540880c52903074401e0080482080c00780003114044282c004080a06450030b0401d90000b00700c4c0c9d04002401c010b0000c5c900710f1a00340805c10305004a003190b01a03c08490030680d010704030f4608d5404140012004107081103603484a06420750040e0b010f540342e56944046c0c4c2000c0003c0d046031303800203411030316120f00c00302456842800390090340c0c8240e0f24144071803002c46040700300d061000c046040009143c8003107a003c010039800024007000c1d904010800c0949440e50f215103105440f500045103031241e01b04241440410038a40c09410780b42000c60070004d041000a56034040180400240080011401c45603800380119154899006205020721012080700142c51540c44c400c5020f824200340080e403141c5084020103c0f2601088162414810304000c1207400b894440016552800b0400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 843662679 1250 843661429 843661463
    0xf07150b01080a0f14070509180c07080c0f030d020301091802090609090a15020408160b0418060e090c040506010507050a260a0201061a180d0312020a020a110a0e04030c 74
    0x61740030744265856100d6030745401c00581444a0038400d50130032404a406582001070041c0400c0944000c150841e203121f440d44c2503114081d10b03100358082040d500e440089803035045904103400450507660504414450820000f40b090121044003034000d61180c100780000701241007403c603a6078007203000700480e0304588032625040140d04c84042e80741e04054000038103001860040041060400100300e034080c00920f0001440c0460255000342c410240d1604001190754003950040405401c810001d50360b0381c100400542d5484140c586c4507400380741000009013032907016800b5034404940010141c08046d0309039541840b0a25030024208001c0d4680b0314588c40f8244003005403070300c0040c9070000641c2d14103260600195111034401c0060040c0100100854610f400c040c1c0206008195281211610300e0310f002e40d0600c1d00380040e4030441e480070800e4844580e0014512080e94024441c994050a14800344102034859001e8082103022200201d80003d100e0320400c0812402120044000c003108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 843663929 1250 843662679 843662711
    0x60f010911160b04210e1e0303070305030403050405040501180606091a03060d0b07020a03030506062a010b130209010e0d0515041505010603060509090a20040209060f07150b01080a0f 80
    0x85c283c0900203004a0030114180c00c2c10060619100c5103514041030881c000740c0066968130a1480007000c100c004000b14041500800545d4050f05d4000c00c00d1005685601c0c08450b00384a4945040c841800e105002a10300d005001050603200ca4032071240104001641115881d030000d454182c1000903800c2400204003020403e5004042039800f0b08040401130400406480000c2d100910030101042110b44516600a5410301c0707800300704400d07414144620000d4014003600360082d800c41e42c80d281401d807030181c070340c020064410240c0b60031110000d21000c0c000c0c001d190a4006005911a4a410740d2818002580b15441481007803000c02c1a101001c01c0000e80d1000e81c004004241c6602c0107101e2894512032140d13200f80706000610041c2d94a841d19030703021940c012007541031b0f180201d440030143c45a4044600050300a0081c903034070020b100003290a540120801d481a0401542102070113207540142405228140c0d102c0e00c0646034a5440d00080c0b070550415412107644850f43d03c00c000c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 843665179 1250 843663929 843663983
    0x70302100c021503150904050a1403041805010803070206070f17041502060405070303031e1a040b150a0f090503010507020a02130b03061503030c060f010911160b04 72
    0x5281c1e01c40626a2691040c040102c60300c100c48450380070288108840206214040c10f5102411100c81c0c0e000e45450400c182480c580d40d501400d060764044414041700b0703000006108564900c031040519106503086001160428001c0d40d150390010030100016280c100054040e40740907400d04405541030755242d8032048104618191a00d001090422030407980741c003010010301c082d0010307003164a46036035021380714042c0340001028140d40c0c1002d04003109a280c0721101c00c040c080400c0080ba180c1203000141305003154102ca01c034508086550029003041075210f007c96015500c0d850800d03030307250000d032881d00310103581c0002c1107115500080d4507079090243c40d02070300280d00500301c0e0703072041d005002d681214180b1020600703041c1014032450f914000346943d0700482480c101c40c0208022400a811442200d070403a0552064209110f1101c10344811141241ca03026402c10803c0c00d1144e02a113940180107503001c0c0c0b40c5240c084003002c030b010303045900e0384144500410382070030154082114030750381 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 843666429 1250 843665179 843665209
    0x21c1209322e1b0b0703020f0c01090b01050102120708090301020d11030402040f1107080d0e011d060703050417070201020f030a200703020307031209080601062d02030318070302 78
    0xc014410502d00c926820352495210003614002c0c8401e0081903c0340c809000c8000c000703000040103800105550300c640c1c180c903001213080c1e03603155841d038001c900c86019018100d002e4501200e1800005903940c0005410b050404c01000a10b09040c0240c50300152074001c0c820842d0195020024102c20002c02e1003401c21034a4000c3c80b403034503814580140000c035203081d07100d450151302c5e0055420101c4442c03001c1e100b440b980300c0342040d40e44000085900180115242a900725030808110300a1000390a10207108181c4030000c032007003941c07990b40132019983e06980140090103040c40e21034100c44a640148942c40c0180112203000e40300309140e501e5603000d50400300000da80100d81000706424509500940c0c41d6540017003810074199000680c64070040c0c48000c03c07071440c1c502080e000c00d00440ca0400100000002d841c615a0b54000c080c100303a103071711420790740c1803040c0f4036403400c1c01c400841c129450081d9600850441e682c084103805ca00450124680e0548070303140d800001a9034980000348040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 843667679 1250 843666429 843666469
    0x20603040c14041e0c0c0c09050403021c0f0e011e0206150303040503060106030203180f0d0809010903170c0f0c030a17090d030203040f021c120932 65
    0x35181c02c0030001c50341e01c4608082d01ca1400d2024507000b58401c1904107007981c80d02180092044810801582c089181103401800c04c0d84040380090542455401244103900076001c1d030702c4030206402000c10303425410004001240c44000e074140c40c13511a891428055a0604050900000d2110f054041c00060380c0c1d80d80050344008100078802401207442c1c00351040c1640118101814500060344400f814011340003050303030200014142c2070b0701100c640f044200c0c030701c150b40d400b050b0204200e4a0f0541282a0000300c0c6940000c00c011000502c55160b107290160380d0b0b460008644400c5501052024044207200038040c0315400340c400920001301500fa0300a0003c540e600110400500420002140c000100c00d101c8208058500d01168088400000e4540140c3c0e0ba40e80c1c5c0f91640c00f4079070404010350414010752400c2c0701c00c40301d80c03244500c1c64003036180b00c118034042140488a0070494000e0785881010383e82c41a801140c41c800b0512442900a20031445100740d10100388841803058001d5448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 843668929 1250 843667679 843667703
    0xf03040c08010612020312030703150e161b14010b1c2102030409020913050901090308011e061d0d080318210a030f020417010e01021608030a0902060304 67
    0x620740901c00d000040c1803031142034a0403100c0e5000a500d13031000c4c001042c0703000c130000001404144a6803103881440340003411070118079110055280720080c216041e0348000803403003041c1040b902559100c20580c80e1200394907528029991440300303024200305145015034980780b403059a692240e01c104040080748480000705d400604044001b6407213070807011181d850148404620036070100480e01590050400982e40360180008922820544194901e8182c0b402007070146900301034110703004440c0a81e8a54804e6621103030140e540946031060ba0f44840c10f03001040003038602400c0b13200c1d030a52070080e200c01c8481840000c80c17035030341c1e171203d080302d8030440041000301100305044800d001c045290300401901c0248a9a288805401c1188020b80c400114038140c40910a40007105c00a150a006540382d0765540c2c7c0c880700e0000a4900b80c003843d42050055190b0900501c2901c040040c02001001c0f03000b85600e407203003164001342590100c1a00d40c0d07070940150300c61900a6025611031071000f085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 843670179 1250 843668929 843668939
    0x30e0d1e110d030c02090c0706020a110c100207050121020a021f0c090506030603030d1d011112040b040c080607020c12010b0d0b0a0f0f020c0d080103031403040303020f03040c 77
    0x4801c0281034200c0c41800394051203004241d211610094890703041ea80041039840e84404c8030254024054010011400003d094511649c01912a074075411880100c80c004030000b4100301030810071031045001684500d1003000300e58440e409604111074094040341003510311070344803021390707000782454005a400b0301c013049608103841000d000c002e984107008200b01c905501c00203100703840c00e2190038030400000c408188a542c0900880301c1c80036001c0c3d01040030940c001c407400c03886072000d0307a0425603502e80b541c424072101e1260110744003c00610b1000c8099540e41d620303c00000400790058a107007110040124441c842080168001d540d25002040d00f2060f00c01040f188555003003074640740e6410300b80c0c00c02064980c030140030401030f44011440340541e115519900142444028454814100391000d01c9401c202d5004080602c2d8010036074922512516090303aa90301c087c4401000551950310368102e101d008000345400900c03034600545000444000d4522541042d54240c40d00058940200030b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 843671429 1250 843670179 843670193
    0x904020d0f090506100b070308070318060c1b0503120901091b090506040603050a1127010f060e010813211101290103021b0715030522030e0d1e 63
    0xba200b108417000c041050705003142e03441c40380110b14004062103440f2000c64403031030090700a5070903590142140d02d00e1043c90309280c2c000e400e072010034001048070355010711004c1c100b00011080c00c0703402100440c40e00004186d2030480c0c41004080b000f965598000b4000060401030180020001002d61444080c0c207020401d412981e024012034850f9160440420001d40041064807245400040c2c200354101c031040410541c034500240450788040d9a1500c8801042c92816103040c2e440410f2001c900740c0c5c07a00e2042d51070003441c4409901191290001a1078240151220031140d8802c030705524800440600010710400d00804800105107030811041018000b40314101c0002407192031030141060052020340218040700c0418105a00010911458001c4902d4030100003015400c031412034ae0750703a0a00c004001ea44418600090400000c01e46140008100072a400c0010310100c2c0c0400040e80c09580e42d1100b0580c4c15041405e41d03048201081c0010802080304c40501c3c0760740220b07039143c64000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 843672679 1250 843671429 843671431
    0xf1407020f0f1f0909091a100b03070c1407051f14030c040503010b030706050d0e0c030f010506011d0907030c110d180e01141903051c0809030903060a020904020d0f090506 75
    0x810100e02d410403210100b4080c2c0c2000700d01c4ea83c2d510307d000f82c0d500c504001807400d49282d04510a00c0e5000410f106070980d02c4103904d900c0074081c060641c100141c0140b00c0e9160b2005100c3e5603440480c0e071000902e106102810079528a6580c00c00315800b00a420500300c1c1c94000701c3c0c81e07010703050300450104014242070007000300488084000c0c0030018208080508335010b01289400e540ea9500d45060040360100040140c00d2001004c179184044282207a90280c02c0445a9a001131010002ca10b11090142d1105083c44c1004002c5482c1e659618011802402c1180e1400304121040e841401e59110500410000304880c2d60340026003458803254841d04480369201d0040b0300c0410004101980c11003541340e01c4804129600d6040c1d940e0399450400215082e0130282660044140500c5071409000070509242c00c1a1103498181d81c0341e2100307d480c0e014580f00b030354142d0040000a248030480e40d0061011000007440142440c100748107071002c0303900c151484c0c000c1c03da982c5040070034064100520307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 843673929 1250 843672679 843672689
    0xc050f01060509011710020307051201120303150e0f0402270901050106022a0a0f0e041a0c03040303050601020106080a0303050a05130206070b0402012d0f1407020f0f1f09 75
    0x2c0c5204100684a150307284007041b110080280e002c0003080e086446101100c1c9090790f02441d5680558482200c2d058150700b0303c0041700860300d840c8003a41780f100c030701503102c0c210b40b007c14081020380d459404140d00c26000820807a440b0604419802c00242e80d04414500f1903041d003800400780c41c01303030741c51421503030180c2100043d0360040012083e22000c100c010100c800480d0194402e0524080100355910460740000780c00e000004400b003400407214994a06c12030154840c800c42d040107103d10f030056907027a075100c5da1001c02003000402080c0240c004607007052041c800010b0007944c0340a41401c0c8010254220f0021351124103000c21800c0070b001c3c041e0020b40c005059121000d00b03600058203032244800003804051640f001070190380c01010319500604240c001c000282480c100380f10400740701c8101c0c280102d89620b10030b0120b0b51144a400c42081c083d40350a0380f4112850b02005041108000d041358814030072011141282c03038040641d8080306011000c9200c00d00f0034035014114400b65000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 843675179 1250 843673929 843673949
    0x207030e03060c1e071505160f090b0324060c15061005091216060f1205151e03030d05070906021f0e032a010f11090f010c050f0106050901 61
    0x31038001e50f6940a0384a0803055500c1c40319a05d880d40c3c070b4407500400c071902541300040e10740800c02c021003101840c40035000b045640d840d10344665095050714029841d00a0002c42c00c0140001851824503c030300c14171091006450b0206148150f0004209900854280c0940e8102c0081014443c003401d540710b0f00002c0031502060841c03441000140381e4000c852120340b01e5086c2c4d04550740801c20500c4600001d0180510000c04ea41c0c8800d07001e859600c003100c4450002d0392400b20b1001c00c02c914030810b8050240360034594a40c042600c2000600e041d81d9040c12208407851010754040da404100510b2929820800032a1610b1318841c01b40c82c0e003010350310803010364004c00850300c81380a54060465105048110024030f480c40741e4159443d5000d0f4604854006540101844111b072000040240070801d0b00001c0c04183e05216102c41603401040f80e60800900612001c07555241c140e802e142c94040c18035000c3c0c0d10040a4a4840c5002641240200c03503956404c01401503042945102c2e01400d035075a4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 843676429 1250 843675179 843675187
    0xc05040936020d0b01080606121501090c09210507121113180b0405010f061217280305010b180d11030709050901050901060302060706110403060207030e03060c 70
    0x11036074100301903001040a409206071804030440d81c0d03500b2220b40d41c58201c403481c2030568440c4002951601d054440602c03c01010110180a45000510000c180c00242c1c0d8200c26902c1d1280b83e501800d40b81c0e81d481c0521545801c00324035859203205490ba01c650031003101190300e1490401070b0074840307150000042d422603411554007184021122051607407050341e840c2640c428248403580203120080e441c02d01c19244412101c18818114055409076000390020406084521003a20031181a44683e440000700f9459107030200391190484d405071013112152901d0180c003488800080d031144034100c0c07010b40515036076030307201541031058601518050002501d070841b4072a200312188181c00c54036104008040c0540200900d4011003c0c01c008050212214551100b00c440060a022070384681103620b08000101154814001c00c403c5940103040e07d4584803680e2500c101404031018941c000309010000040040c0c100e10052660074003d80c1e03041ca0080e1284101400c2540142c80c40042e010184 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 843677679 1250 843676429 843676481
    0x3070303050313020a090906020d3e1204030f121a0906040b1c03081b04030b090a0f0f0b060904171804060e06100804150f0f0c050409 59
    0x34040760f80140342502c401464840500c002440440c9540020282034180401071301040705a0300034040704039140100f44078022a04800c0d0035040d1000c2d20aa00700c00801c1680010072035551422450b11402115107490f01c107825140c400046010341d811000260204050700c02e0545c00175040d0b0801340d20020502c107409040c00d564081000c1803010b5442060018003185240d5510780c86403540c0c81d8041c003180880c2103440c890469480d0b100c80141d01040200340010a00e0b606449d000407812444034206041c02e0660700d441800d01d00003400f516207881020300d00001b00b0781c0c8100e443d007161300c42d202c0713401154101d28003071408a002600840c02a041b0505200006001e540c1502c1e07480d4001c0129615200c9450521144948152040740c01602e4a1404624220380803017840c400d00060398904095100064100c4140e0340c11200542810403810905a040302a50007880c010740d9100000304d50078400050f000d0448580c8110382011640000703080000c201c1030b01031001c42c1c1c00e00c032641d0084420b50b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 843678929 1250 843677679 843677687
    0x20319020708070311010e0d06061406040e2d091b19060815191706041e030c080d0b13020f040506130f090608060c0301060c030807051c0504020f03070303 68
    0x5404014803001207403540c5c0809074414100007000040007041c006c50301006082c41c200807c0366005580e140755070b2109091142c2050700444040381c50004003500b081e40c0e40e070790920b4040c180e580c14000141c0c0c90400c0104400c0f040c680e69016054210103001101050380c0400d80c40401004074500507605040300145002d80c0400400840f9540d041007130091761038030031141d101c001c42d40040394090200e0264440030310100303800c0019118074014446400c41511712290346d5103022500103091041e01c1c020b02d50500381030340038401074510070300300888904640c3c2e50b1003c103a00f12481100042ea40d41e000942c0380d1400200d0242128400c1200710302d4142e070b10000c11001e00c40e60258601440000920911202c0c401ca08040100310f1407d9907078510ba181d04200020304010f10400c48079100c0c84011401054104003124101c0d14503441d41e40060100e650256100c0303000404c540e05008041c801c0203d03100d41d00801e500c584100f118001a6445c251041040f210900f007030003402a840280c0c00d100007608 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 843680179 1250 843678929 843678943
    0x12020d050303150f1008190f0c0905091f1203031e090614091203431805220e0a05060f04030818011514090906092107060c020319020708 60
    0x1030524450030740c04251640006003158030241c030600c912789040c80e03c401e54443d149109407031007195035282c03a07102e0055003626201101c00500b0000c00a00b02007010112031407002d040640700e4140400c0c181104041c15030160115024141900c1d00e41f03007070200b00301b96803142058102040c0304e03a01071400c2c281441351b41e072a01d6071400b640351040000450480143c803074240c155a902484c0c0c08a00c06102d810780d000d07900b00601500030300b001c84084012050b0040f0320380c64884034241007010340580391004014036441c01043d4100170000410381b10a00d00114040d1040d2400343c50002e02c498261491f100346010740c001e1151026003210018000041c0d84844110340008261094510000e051461305004180021207035480202070000050ba51690002200007040700b11429462641c903d4071458841d003003114801060341000f05561048283c10074112502100040940d003052007a50340c81040740c254181910141e4408562010016102c0025068280c91031024000302485c140b60181c2d40d5003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 843681429 1250 843680179 843680191
    0x3050d0c020d080a09050f060703090c090209012a1703091e0a030e0109150806040b040207030e1e0a0f1a070b0103080307030e0d0c20030712020d050303150f1008 71
    0x1e1205c000740d0910004101400405003002c0c240c030580d0901c1034000c2c00600f60b802d000c5031440c2c440c04001a40709c20503c240c8880d80c0060311080c840040d0409102c1154551702c03d00c2100a031000000400310b040e03014030f032000c883e16030309107660327030921440310351500e0350a202c0e120300c21151000752490400c000c20000061a81030500c0f0414456900068a504907190422100c9865038090000030941c040c02450151344142c40801c84240c445042c88181d00c0b8009010303001c604c0c82c076890300c410b0a142454007800406c40c801c002c0000140800a44510b2540d07100d0049842f40c030109210345261288034108501c18460101c1c5420300c02e6840707010a80051101030a0010040001840103000b0f4128030400d09030101511700301141301401600b07492138900140c9161000d9044003441c80180424440b2402c0010b0080400070b181c1401306481400c10301e0126000146206c00100050003000503500171000c0701c0919821140c0d560500a0280b10030a1180c459500b1024801c210340d000080e880d0040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 843682679 1250 843681429 843681431
    0x1e0f0b1303271505030f0c070203210415080f0a0b03210f07050f06060603011a070206070b190b220e01060e011511030a021906110703050d0c020d080a 66
    0xe4001c1c0d02c403407035603507a2004500055034091107003070f10703441070055100e030703e96800001d6a51035444501200e0700402c1c9001307405a00410100c0c00c6280c0e0305a880110500540000e032030182c6400040790318102e82c021090211f00080c06000611074a125a1079000c641c181c001c0241a950b84002a03441001c1d138081078111101801c0c4106c0070204004032020032003c0011642d4500152401c0c80c0c0d10004241504032700e008203c0031030300c945441c00483c1e0480380858400108007252101603403007644030300f0b4200c0e40404200400c20028180c003401c18443c511100024503425114061031003035404410b04988035003a6225814904020340d07280400c20081c0720b0740018090b051000c1c2038010326203500442d41d1106601c00000703421a0000c8039458034880c1d5030702d02241000c0d000510f940c9018000c0d80c24050303040483d84110910500407440c02840c010070001c12101c04c1d041c203004099014510580004000049501c041d5189014100c00c1c40914402003400801c40d4500411907580645000c0c000317 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 843683929 1250 843682679 843682727
    0x20f010f0c060908120f0f150112150e16021914060405010e10050114060915040e060a0e040c0e0a110c0a11030d020d03091e0f0b1303 59
    0x141e10500801d080759a21940800c078410312418107002d40e41180c040802c00d2a10b07140021030f0961070f00e82031800390b030300c81961a2903621403140c03800300031807e0341c0c2250400411030b80384801046140545000f40002119002c030680c200040c09004280c02443e00c0462240b81101038500d69000a0303203260101a98601107900c8014a8880119003051032106058401c4605000c24000103500086802410318203c070701051400401c4000e8410074811320442c4003c0310050304640c10201f00904003150001d0410708003800c4590282030b1500076401c5000060b031164100000360030301c0750300b90000e0030004052802529066075a5403410082d4051021a0342a80012640c6420560040a0341078001d0340c1c180d8031240005003076550303400e114805445100414038400c240b0308002c0340b52080801180d016003d11010b0702015005400314410440e1071500805d0890408201c0141c5000351620071101b00700902030314248101c3e031a00143c034040c0000034174004040003e40040b00030000342280d50746102e00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 843685179 1250 843683929 843683957
    0x42615270319230724091202010606110601030b090f030301080d09091a0f0f0409060b0f0415150c06090803090127030c05160e1012080d0b0a0b0c0304060207080a020f01 74
    0x5880d2220317805002090a02944004109100042424038080c6034020800c0650700d085c200c1d81c07144604007100d803076005840144080381c00307003c4c2e0344c1d400310000b021501052102140149554802da100c1b107569040007400d0403500d40d000c3c45050061400407828065455465400041c0074049000349104c3e00400045031f54a490303d118589441500502c100800d000d0303030514401508030111418400c001416200131a494544140d4010b401070b8031030414803c9c101148412101d280002c1c11050284c8200480001080c5004031032000748100c0419442c0c2c10082031850941c0e140d0b56040d1072002e0038051485442104040c50b0941580502d0701c42c03610b91745810110708080c04094034481040c1110000310b926422064801c0c0242d00040e2404e42c440d541d20b107a05120498020010b10919007081b001e544000150400d00520100800b0124103030f50703400c0900c510f9800001d001c1200d40022904020240e0144210002042c00d82c020f401455100e50001c0c04549040c15003505000329100c188403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 843686429 1250 843685179 843685223
    0x2070e0c12100305011e0605180c1303021c03081819020d060f0603020a06030204050a060806030309030609100c230f0c030426152703192307 62
    0x40d5002130007041102c018000803007800303a41085040d1143c3c00d00750b001070641401200030386c0300c0300030011180040d00d41d244625003651015030344400104014002102695032440c90410401c8500c4100000005924000c2c001403401084c100040c400c4440b00d00340000003066403403501000ca43c204000c2209480003c1400a803004054580c40c0360079019008220310f5407010003500c1c02120745c002015035805080303040e403003940511a00b00c100110100b04041c01844903507007280e00201500d0905400e440801e03c1c0400031a140c480c29071105000d075000b80c0c00e903c600f180207241c2c0e240842914005800d000301d44040120b2080d0520000075001c0462040c050980d030740710762200141e03543e0ba5070328550b2400d42c45030720035652f036018440e24900454210000c7c869042d01c003018503040181d903030b2507210103012003d103062495041c07078081558041d050500c002d0900340040300008525682c1114001c04008a08060940b1104002c520500c905680400d9403ea02d60010b2020005411420004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 843687679 1250 843686429 843686461
    0x135010e01060e0105090615040504090312050708100506091c03110a0506100609060e19080d030911010201060608163c020c1815091602070e0c12 64
    0x81030952900c403020884400d0004102e04941040707651220a0302c1d414100507c0420821003080d5401d401c12042100b41090b40150508034020b0600e8940c026440001d0310588000710707880b1001a0b0480200030001c10800300c00406410182e42507405c100f03680340468240181c818440c0160b500560502c020075214510b0f0303200e0382c0241e8046d5000c0240b43d1900030340e0b0b04000da80c074030070504199a0124009109a4150341151840e0740d840c40c3d1103c900d0180502d10034240c00c448684090741c038010070910b0742000000c0040f01c1c0d45e5070014005c1d40b20300345000300058520130281103904280040041c55848000e294112a808000303242d032256644041d101d50182c003100c0c0c5200d000f002c240f1191148558003c01c1511410250f154084819250880c0c4400c0129459540700c440002000d4002039101a980d902054011030065145003010001e0419541211a144000300c080044032034030703505010b864000c0107606100175050810f4882c580f4a40940300c00c413540341039001d000403a1120362060907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 843688929 1250 843687679 843687701
    0x3090904020a08070b030106031a010905090702010615112a0114070b070e030c0405010f23061603141c02090f0409062003060603070315030c080106030b013501 70
    0x220003d50f65085d281d003c941007442094046850001180c0340c982419003841c3d62103605075610428075080c64200820740360041e204c41c085660700e003004505008840300110f0085410385804080c0004081d40501c0c1088403040d01540102503803030290242c60785640080d5060003420300f68040340c203030071518401e8054008080c0840c4e421105200b040f80d0403803210740500c0070950a071807180b8056420710081d40e03001e108d0410f04100064040000304e580c00042c2c17400c240708943c4440c80e104507500203010381c4c0160f031001010100c10020b036820544c0104c908402032051090686c108010000020780d4203220005001c2e1803500007840d1070059580e9902c007080c45100910400440d002410188020010b002c440108401d4603106585805800001c2d2031144800400440c51591003203422030142600d160500a5000c02400c044002001c0d000340310050001c000000580c00c1c80c0d401d003841d1000060303000c007501c02002c100120f041d0160a07000090707d0003032190740548501c030040c528010844541d42c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 843690179 1250 843688929 843688933
    0x9050607050721120b040e0d0e03070522060f080c1c0b0a051801140402130b1002010f1d0a020f150c0c040f0e03030a0509070308070b0f0c090303090904020a08 70
    0x6010314040c3c108130400d000f418008410008000c402c0240411111048021110369001080e98034039907214610040d026400070301650794051785c58022900c0c1c0d1500b03002006180c4154451082d81407039500ca000014543c010030144098501000c40d80c85681c10600c1c7c6009524100030400d21768100402e42e84281c0e407042c000c00252038030145010080c0000e49091001703a41d00810b900c06407505000300c3c09002c25a902d156401d40726079080004401c05c28182c042c2107038a42a005e801551040000446a1a03903000854500d106030603031011070310b4038180e0318140746068040404c49180004c4101081e94160364480417a00c1c0800000d01c5409400007010740c8041c00074024140c9100494001c1844400340d0b010300910901c0100e40b01507030440c1d11300f144951300900010b000d2180300d4000b150090b04070800c0d031b1441d907140e03280e0030019807080909440c190350b11303c20720220500040816038010720a60700c042c05c241c1d1140001e43c40f0b2068a152a11448000c0046002e65a40c0a1188000c02040703007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 843691429 1250 843690179 843690233
    0x8070c090c020f0106050117090f01020a0203130e010e04081305030331030f021e04050403031413050d050c01110c0606030d0804020906040207080918060f04090506070507 75
    0x50080d000d000d044a0540050085181c6481009414050902518016110f0034007180b601020281c08540081c0004c1d9030707101d14550805401c800b84003c14000c1c501c0e502079680c0c2da020000c0000c0c2440e0755440713820b649041100400001c1c442201c8a60800e9211451a60300e4416011400d04c45085030440b0f1303450301001813003040c407a4101d5070941c00044083e40d5004a0051030486c500196201e100107000701021032070f000c006203003850100b28184920500030b04500c000c0404502107130411541100802c0d61901c03403c40001103030001d130b40e01100c4410101c4c001c0b10142e0b2410303110345400b4100c00c20b000001c52000000c0b9420b40042941100c0d0b640c51540303030000c000b1020341d1442c1c1959218064021180010707030b21442003200c98426a0043c086500c6a1544010301000750b00602c4203907041441480303158226604c0d2030b403444400011488941c1c01d824400c04115204207204882c1c1e10582c03a009101c0c00164001c00d0304c50748103489080140e2a007806003440071041d03005c174a18405441c0c03500c2c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 843692679 1250 843691429 843691439
    0xb0301031101032405040c0e09010501030216120c1e030c03030b012318101e0e040f0603020a0801140a0b0d0c080105251e1110020d051e07050708070c 66
    0x1e80340401305c5404031070600c40c40282c84820340c3c0c001e54a41e4610740029585006000d2540260000d1090944002c1e9040e0840b0b119283c038170029084000710000982280c1e0300001780301c2021034100c404000c412026140c01001d560250141490b1000207082c140c40c0d10340503115038002c1d020305600701c3e00c0c2058400c4940107046101c1066009002030030040110f4850a105410510f4222413003800603119101c51501e070049101c03d012810342c0030000c0003114080c541154480d03020b180a0a40548000300f501801c5204002c00c0c0e1001750000c020301c0e07141078100d00000c484801c015410256000340020ba500c1c09801080d4003822112300540440300030800003c0703685055020034071039801d91651407040e036007540c42d400e070300d0340d1140035003000030b02c01c1d9440741198140c2c04c4020403244c01c40c1049200c6e05200d14949042c40c0061041101459002c5805490b00040340615075020769004000c0700d80d041d0b80140780c0d272400c0c0094410b0041050100c1c2800412003c9421034000f075420a1039491055a01c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 843693929 1250 843692679 843692741
    0x1103031b0c0106061e0201091a0c040918020f0f0f040504060905061e1f170a05120c07090b10110f0a060603021c0c140a03060e0a1b0b030103110103 65
    0xe01d5400745c614260101404885e1061189103070590f4041c00640c0c128500d118006003500c0040c06010180703004020014545085204071032a4003000b001044102005004202a0b0303000c984032140583c0d15501e0740702059031540c5003903000000889000490b0740311814031000400341d0ba50010020710400d003d0122054012440230440e00541d400f070711155668400c3e0220810550314000903106010b5024080484101d240424086100e0100d48038003400b512960703d0b240c001c20340d00b00c0190001403540580032003840007201800c600002030014001080204040301803041000c003c010004050054051003480480e1507021b0f42c0301110140c0d8050b0515500512144c84100d10610710000310004600c031184480221507044185e65481500d4230003100c1d00f102d00392404c182c1c0004a8a004000036600e0310501c039074108032800514a04969140a0581641a2180708404880e45404000d01c03445482200d0550b07600c84404004800041d0042e006480714034020320210f40e405400c82c1010034a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 843695179 1250 843693929 843693947
    0x50904110702180f0709080a0605150904080a020f0111090f13050915010608040b06042c010f0b0d0c03080906070210020d030c0c1e020307030c090c020d1103031b0c010606 75
    0x1300c858000b0580c0310000142d49400380c0d4440c01410b5046940340001080e29640203a40c00308024282040c103816120000300d155000f01c40c100c40540c004140700e81c059904014560140c0c0c480d500030407180540b080606914061111481d10683c0c42201c10409529100030420342c185403100c0500c82410940c05094881e40e0f000c4d03102e042488002c0000660300d10515030240501c2d000390702058a9207800007404003a12000500100b084a1001c012aa10120100d2400310803080000002c00c2900048041d0584460405082c410040d001010f404103000d02000b034201c90784144465594a048004075003035000c1d21201a40c4038840351015190f080e000300d50004202d0303080c1d070204910074940c10b080d98250311080001d400b643c21500b106042c03e88100c560141d01d40010102c0340e01d9940ca0b91440c41c060781981240030902d440c0d01d0001a001d0301004a1101c404141c10100703206910300d81c0041c2c4c0e07400700900e500ba0340c4d203003140716043c0a00c13504d007140c001c806030f28028032144d03440d614042d0100310703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 843696429 1250 843695179 843695191
    0x806040f021f05071b0b070302010605180601081503101a0405010b031009020708121305070f15050306040e01050903092d0d03120615170705090411070218 68
    0x5005000e440d544600c02e00000c02d0480140c549604014054403541701c80800c0c1890710141401d001400319682d0031a20180070b1641c480c2e400410340071b06140502c034000605850140c0c110402d5070030b005591384c00484c00c5078001d404903400c0b40100c00fa400001d280c0709528070402005482c1554610044407600070100d045241990b0030b00050366120b072807600a1008403a00c800b5095008000d01183ca8260001d003001380c0076a03902401c21358132140ca444440c00644200340b100d80e4010680701000020f009150041c02600c46010a0718070b41213a1203d1507a0001020b010840c0010015003d42c0d255070140c611002c0c0c1f80001c01941c45c03c044415500d50101802c0f504c1000003044420002d000c410340340071800709070300100c60607006803001d200054980c80c0341203042c013020044000030440507100b003e001340302c8813030f404800078150403002d0440e05503402c13503400a060000030485c03240d07004402c860300c400040c0c0340041d50280f9443c4007001030041c500c0c025808036410540f2500701e0001c40c0428060b0f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 843697679 1250 843696429 843696439
    0x30c1306050d03110105060f03120a0c0c0b041d0c0904180b0c0406090b040b0f0304021302070605040201202e0e06011a07151104090914010b0103150308030903040806040f02 76
    0xa00c42600300320790a402c0e01123a41c1d0641c0444020003484444c170000d081c00b444d840c1480c090751240c958900402c0c400641000c03103a580c0129040005400075003445c019498400d1400e2403038204029114920721a144140f405541c43e903c9983e40d60007101440e1800d503070814000c0071203043c2009200f95a912a102e440c1c0050320350b06000c00c04180200031101120310700c410440c60410401140d40340358000a1090380d0050440c4c50300c20000c9114002840741ea440340030b001609140c00d1002400502c0485002c522101c054401d8122a040000301c0c4920540d1100c0c810311500fa000c5402c0e40001c1402d44001d00007810302d60741c00c01d20076000549a040c0c50000c0300502940c0415402c860782c83c0a80c00001d03044140c0a422240001250360007000020450f20070315280944070590801560900001110302522911240210755000c1c0300b60310481e582480c0034081c0360104210404403503824000504400000400f05002c0ca0040003298014020b26058075110b1a0505185c2800351900318140c0c040c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 843698929 1250 843697679 843697681
    0x302010605180411011107030317070503040b0f09030f0414100302120c0c1c0507020909070b0702040b03160f0806010f0609060c02030a061505030f0309030c1306050d03110105 77
    0x540b420b984414030404000c800920203aa80340c48865400662a594605204c0d80380d61140c440c04050004102450081d12424107000e130101c0c41000802000f82480c003001420b00a21000451101d010ba07040310b4103900c0002c0da40c2300c01076140e056104030540f68405580c0060002041254000c50030031a04049511148500c6811001c0d81a80701e030781c414003000141c2c40001000c602401e40982071114840085450b01c14010300c159409001d03c143c950041040882c0b1034085107400603410351321000c06800f0306581840d1031104103d03405035100091040c0c2d2588480803894800300410709210b4003c803010f241103070f0740e402170b49040b1901c1c3c09200710300c0c06200c00104805400e020041c08032b40151713680360b03407440c030345481100d03003010341c0340c081340c3c14040d100184011803040d0040784130018241400b44101031400c802c0516000c039040b000c030443d030804e00c8a608103540c00305a035540d08006440c00380201031a00750510040a0715004030b80c0c0610038640040505500850705216042944002c01003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 843700179 1250 843698929 843698939
    0x207050a120b09120d0e2401061103090d030306170c03061b13030609021c03020a03080a020c070b1c1505010513120b0a051e0c0a030b04020315030c18060418050a05010903020106 78
    0x299103407c0001d0742d82c0385000b4004002e0640b1490058600c1d503800c0040c0d90414418500003031158252800070b400203911383c40103211703160f0301c01c10149100219200400803c03c1c03901c0420b4446400411036800300d540b24103040c0c203050b508070484018908500f1201d10301ea4172842d00c41c00038000140d00f40d010f400c0c01c01c0c0312030950004500c014500e582540040c424001c03155030441744054014030101000d0380074003400c02e40c0c0504000c5200039107900304000740c582641c5458030180c50200003000091506154144203000b24040c0d8500640320286021656080402d50b0306103140899841604400c111840510501035403e0340395000e11035540060011b910b4001e0040c0408881c41d0000e07241000c000041110034400b41d00030304509416080102d41d580c150700002c1c1c1207800c1150041d0503004a41c1c03c0d003465103010710502d118054121420744140c0b102001000394000001c00c0300380a00ea441d400c005031146980e582030542503100b021144084500d280180c06041c980740c0c11005503003000b0001c60 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 843701429 1250 843700179 843700213
    0x310060806180303041104110a02010c11010606080c03040c080607030606140f0a08180a0f060c020105131b090603200a050d0818031203070207050a120b09120d0e 71
    0xb0001e02c03039001142181c80390307103800342510300443d6001e5003e0b90f144015420303121440081c0c011070320681c0002990030100c030300145c200300c2032042d80151b80e4508001030203126007054405030400e400c1004181c80b42d4980c41d2503080f011298010400d2032240c5c030f08200040d0b0b0b045e00000c0981d0030319500c0c840300e00980c1203a503800b400b620010b5050f0050070f002207078034140306054056100b8001e60161400c241c101c880141020380c2544280c030310080b00c041c65002e2121394000d12500480910003085649481d13220398040007840c100003440306030301c5548651910103114100340a07101113034007045144c0d601d2400c00c074520014440c0c42d08c902c1050300941c2003403500c0e8580c0401c036980a4030968086600e55a8144554030400107005120641c22604c0560349007000300c958001a5810031560300e052040010780707040541d6004c03510511101c07030113120140342c0003590500b80d03034401d2414603551104205079003080c0d084c0608074000312001c1562220340d03030343e41c0201d010310480310251580c0c0001041101c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 843702679 1250 843701429 843701461
    0x1308061b09010509010503040c0b0a05070b1e06060304080d050c0307021509060718030b070503061c38070216060801260f33070f110a020310060806 65
    0x42c00b083c0144614941540542c2c0150342c0b1078800c0b181225181e8647d019401503401c8103240d200050004500081003060995000e0781040340084000c0d200100081842c4410000426007401035002001180401500b2410740d0300f100481d050510aa18103407070700c0b85094008a6840c40188112418072314107a00d00d034003440c0035800c2000604400d03600e42100740c6d1a038030401175040d410700e203c80000000c5140a02424050740b010396031181d0b02d0400408101c20000c5034240d8182c5005034150303c000181100446c0030b0078840070102c0019086000c0281d9140c01011800c0880d122204020000342b00c1d4040740304a00e401014440300121502c0b40d60881e4411024090142ca001c1c1e2003a00c01e00300c48502c02c00e80140c0c000141203410707080d40d013000c0c1406d0211010346018080360805619407030104010a1041c0b000d40c41021010703d00e040580105403c8211600500748101d1442d031242d80ca806128205840d0740240484c0da01100d210800c200503d03451090115034020080418400b4030144050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 843703929 1250 843702679 843702697
    0x1506041401060f050702040e06040b0c03090a030e130504050709051602030f090f10030b041a0105070f020f0a1d1003050703030e030114010311010f1b0b0c1308061b 72
    0x16030041da003441010356280d42001c45801c00e0000510440c2e0041e5554007030f0b0005000090060182030605241043d244c650182222024030f505000700544444005071081c0f04941500e0306081d03d0091002103801c01c0700d29810000d80030305000400c420700200140010803112808401c002660300d02c4c41441d0994405011180107030030800c0035200240c802e5010f0400900000d200100407010100003c4250340c0b40500d070404240c450405e010180745c144030307401c140040340e81c440924241c01c0c00001c0c004d00c590b080081c020a140d00c00039041d0b44940c4100c440e0074201070482c408050300c4100803184010810b03007100d465804030340003409503c0740401000890745d000c1c00400a450543d034080c0c491154a00d05107416658415258812000c0b81e03280c54005e60007100980e26800c280000108180350321024241881307214036003003040b1850102600040c80e04444543e02e99150a15003240c188070744003040c4580508180040303041c01c0d000c6030745400340b16105c588194040c0b0a1800f41010b0003000e40d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 843705035 1106 843703929 843703961
    0xb180d0207091803050304031b0606080a020307050d03090e0c090409080417070e010b07050a1209080d02070602030a052208010f11040e0105010309031808150604 71
    0xe815291112407500c50034000f400c0d2005417040c480940000c0403c1207503d8480c02d02c450020045904c10b070b00c04421301a403035481c803004d556504030130780030707886030003644400100f5141100c05400c0c82d81d41902c0c0c0c20740c03151520b15100844000205003400a200c00c0081a010b03595520803c17059038400e40c2c00030340722400c00325040380070303c02c60504080c00c7c0d000c500240007112005005504455006070b0890fa40c3c0c43c01c0c40c100741000e200101c020081c50b51401c1000940ea00000c440e41581c280104841000302000f0f4203da48a2807440f410016030001c0007510003d52140d0014074110380d4010029480c0920700e2414100f460b40b56020000c280d6658540707010141140c007034026081d110f800182e080a0804c4405283d064061184a0515644140301401c050254804200115000c41203c40c0c5566032140b10f901c652003003820003059255400026064607080c0309140c40d107128101 = true := by decide +kernel

theorem cover : BRFrame.Cov 843525179 843705035 := by
  have h0 := BRFrame.cov_init 843525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 843525179 ≤ n) (h2 : n < 843705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
