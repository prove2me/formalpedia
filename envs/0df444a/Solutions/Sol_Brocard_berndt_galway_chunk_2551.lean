-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:42.494287+00:00
-- url     : https://prove2.me/submissions/6caf056d-3b89-41f4-97d3-d2233e8471da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458633093 ≤ n < 458812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458634343 1250 458633093 458633099
    0x60609030219050a06030e1f0e15010302030303070c02011107081005130f1707080f1305060705061605070b16120e0604060c091205010b090a060621060f0e01 69
    0xb9001480d40c2c1c00740403040741201480300360b5413100300c50180c45043c640095145180b00e0b41c80d14010341205001c030700c0f040f07204e04004091515000110001d02d141d0560b6a0702a400d500e0040c00300082c0030007980340e04248000b59030148600c5009100600503d015030b0348481c10502d5078240a41608503014076000065112900d581600880f5000110010020951045901c61403290740c09248014614007011030058200071088d4151440c1ca42c0100d070b1241d4a811000d40d241c15a030081252246040001b03000203003032319020051303410054108024100580e0f540125485800c2c03442c00e14420300c2000e120032004250300c1030806126030151810406074401d8040e018110b101246ca101c440b060416004008404020408071b40107076000300041120032510400361344600c8a6046141804002d1b1260000c0c0501500002400349080e00c400026856080118094401c0d81c0039200100d10707803801c42602810741c09a403c0c5140d203c6c00c0009011500c40004802ea03040580c08079603100031040042c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458635593 1250 458634343 458634349
    0x303040b060108091c050903011109180105062512020c0103050606030702030a080c0910051210030210081512010603020112020a0e060c1f050f062b03020f010606090302 74
    0x507a0003003000d0829807a6440d01000c400d83c2c40383c91080d01d01d195030070f00490b866081d004c1c50a644100740f0050090104e100403040544264000001ca28864444a58180e6608404081c42030507514007404c0503203840090384000050075802440d04000f15001e2800708041010880c0c0d02d00425070f564040c1c1080c841d0f0400050560314083c0c1003034031410080003448505ca400100b120010a86410600090384d40c4084070740786401481c1d8415040540048290341481c4e2020003400400259002e050650303c48440741c03441007a15000003500111003091041e43e05002e43c0800358411480510300c0c030460030401c040703030782c100d03e8951035082030791500018411580c006034800040031203018118100b003060310700109807041040009004000000782c5504170302083c4009030b801c645550700c14900c461132200d0800100000c0322070441002e8844040b076158a0200c02104503448140c80103010218010344d4401c815a85403011015403050820142a0721028019500145256242d40c80c405284d4014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458636843 1250 458635593 458635613
    0x3060507030605011d0102070f081c020f031803010216050d090603091e030c08040f0e01060f0804030e040212010f0302010f020a0f030c0f0506100612020708040e0c0f030108030304 79
    0x1903901071600b080014031859178000d21100c0c64501d59010440e507000840f0040c1d00302409a040126826804200411040000900d545141c00c85030307040310041d010b000040f40c495407460b004140170703081080030702560301641d080c10528810040006142081d030003180201512503031000c88180e0442c0941c0c14659410101c0c42c0c004010908003844611160360b10302250f92103082181e4080c6070003d44403c00d0610608000b94004e6211807040e5a642c0c0fa00e685544140761031140b14281c08046e0000b00b001ea00c2141805680605512200e20903180d45d42c00755004102c0c11407468200d40d0900100da03401d5107141205000300051180c5040c00d50650000400e0025042e0746036041d540070800540008140c00f40b500300094041c41c101c141e150480ca80107005000c0410042c0c0103100d0581405520340c02c868140084902980360206039a0110034540309030701801c00050030520092004114903102c0f040240c0c1d100b84003101c83d0b490324034145207200b00782d042a08003c903281d2003c0100310801c06101c45c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458638093 1250 458636843 458636851
    0x915300e0616050f0c0715110132061210060e0106030605030a03080403020a0605010e100f0b0f03061302070b0415020436050112060f0b0105160c09090c030605 70
    0x14070700b8400d03002507030003412a2040303481c800c80c0100d0018540c44a45405e10a00c00688107480d426003400400f00c030000d1903006017201e015029460b01c4e90103400f4884002180c2e10032466200c030200302c1102820b841480c00d500400c6690841284070b034488141c4010b200c0e005c02c0e232070600f1000176494200100480d80301d4058100409152030302e42e00340403641e070004503041380c294586400303000742d03596103022401c0078000e5400505c0941032034004076090307403850444d03480b480c01c6c01e040018031a900c2883c01c050f1411442030354036a40003008003005020605c130095a21a8002d491090030803150040041281c0c405001512803001c40e205000c00c01800c6400d010350000700c02c00650810342010503100104402152203020401d00c402042d4100b0844401e07100340311404501044a5070359201c0300b0106041c1150f04413941403608001584a0749148251003007010107944150401c4805511650201200c0314151007554040c000000c8000d81c5000d811030741c5200c3e01010100b6469881c1800c290b44000d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458639343 1250 458638093 458638111
    0x6061e030303050603060c0f1c15050301180308011208120c0c1c14030a0b10030c021504050d0e0a0e01060c031103070203060403080c160b0601020d0915300e06 70
    0x10138400c4030891390b1f00382c41d10f40422111907a5220796200c5420f1940071821180010301c1d0620315406110441c009000c02121800e8000344032110204801809000c52403030000c000c1400305005101000c1c82180c0ca140942c41024454a0312081a80c28008a44111950340e80c040002446905071142403010640850b140c0340002c021301d07030b41c80c4047e10702040703200c0c01e0ba03c1c0c00c80400020400c1c1240e412007442110043d141440b4440d0551005004d40401c180490161291044081c40208074060b494851504000582030380f10600340c00312a19020f2220340ba510040032a40480c50100318061140202416110040c03c0e803211314024000401e940101036241d08244131140143c0c4010901551007585850000355175030b12020748038114000c0310803840c1402d12a03c20141000120100360340a40426021607003062300150044420460302e000c0c4034080000364400468103800b502680c0d60481c0c002a0450340b07040c03003031804203d80b840c0180d8050002d44171322403002100f40c240001900964a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 458640593 1250 458639343 458639353
    0x31204060f050d06170c010315030c030204020d1104080f070e0106050a030e0708100207060e03250302010b1e09010f0609062303042001020c10050706061e030303050603 74
    0x264041c08408100c1c1c4440d0501c040000c0700b5201d45101e0307000324041c0203504001024850085d00c1035580354106018640400d20700008800452421050a401c072a8000c0e0003040c11821035080c480079412000c0700c1041d15844800c0391030f014a11a0103007001d045850300610900600054082c54140030383d10180d54284e80c04010700429074000115213511345035040103d04a02146002c9140907001c0e401080c050080440000c020f0301c3c1500100f1515019007024000f003c003442041d5241e10800556074500c44110001c583e02222403c1564030490181c000000c0740501030021a40a81d0181c6661010b400030070b000100700d207050002903024107185160140c240d82010006403000c0d100d4001c00d03040c030001618100d00800c0000c4664447c0305441803554030390916141c0006002c0d075035090702404d807034a481052000d510000d94200740c0362008000190803100d09005a9031540504d8040e5041501c850303009c21240380d0003080748501c9075411642c8250310300d1401c000f0b0481304060a014031076084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 458641843 1250 458640593 458640599
    0x501030b0a05040b01091e080c03010b010e090a0209060a08190903021e0f1005090f0303040309032405010305061006030902060702210115061202130b0c01020d110405031204 76
    0x10300c40040094a0b01503500052048203280107941d8607925034000d1380b1480030412003031007250340d031609034084466010031130320f80c1081c0b50201400c0c0c0e88100c4415002481017805000213244c000f21158208120b02c400614100844010a40e035074041c141c0c80000c00d0444007844060b200084207030840508016081141002035135000351101d50880e02c101042070318001062110406100c0c24640c020130404469090411124980143c1400c655a40c014002c3d04091500c891f0040b08403846181d05130740710a4100c0c00d41d6508030350b8095a84041c240048203c0307210030003100b54070131070340a107010707000074010392030103000852086000b50400f00425050002882c0140ca0391010303207401a60485400c500d840d480e00b0390f13901244255041008560a0000b500540c0340000303c202c040d0340499440c2804140b0142d005000d910481d41032010818105e80e00b000441c59480142040140f404000f518140b80361140c5002d403103d003090500400d0300080c04000602e001c11000e180d202d00f5203102c1d41401d00e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 458643093 1250 458641843 458641849
    0x415080615070c0b0d020f04031a070c2109050603040f062f070f02090c0c2109010e0a08012c01140c09011b050105041106030912071511030a05010501030b 68
    0x1000f44242c44904d440400c05c020102c043c6d805681105120300c000d0f68131550b607420030040c1010307141122007881a4403004644203a00c100b01200441d900003848160300d143d00e07416418400400d22400c0200003c0d100086055036440c40294001c0d03020761a0f0304400300550415904031225844e003914401c0d042c043e05120b0f22a40301400e803c1c0c46044452940300d18403401e010819008007640294480344a10800c55041100c0000c3c116001000c0e04984070703003100045801014000d060030318011a400d003c0030f01291b1180c01c45544242d0007614000542d96110750045c291070003d423048504e503103254240703920301d441c496a40c0308503400c0400a0020000d215404001040040c1104c84840800603810b102640070b50b4841003000d020f0034050741c0001281c10842c0c020802990102c1c0d21001c500001161403034080152406800c004014049040b604050804640e200c00c0d800c80d10390209180c08100401103100d4403180c00e0ba80d00d607490340d03450181d02c2d0008860058000c40c0c1030616180050321551 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 458644343 1250 458643093 458643113
    0x204050f010c1b060507050d0219020d0609080d0c0e0a051c17160b090f0c1002151305070614030606070321060f0e0108120906041508061507 62
    0x1038020708000002210505111804488142c3c418410004841d0700050041e4030000901456000314260b030055081024102c0e203a901003054007200c614a100c11314007520380500d0142800d40f007a98000307034042055480c040f16030007026180d8041035641301c40011140e007100da4910364810889034000140c0c284800030303840d41e802811645003803180354000710801c0302884552090013014501d454441d0803101d070a000f0030110580464010303007140c3c0401c240c0e0000040d41d0062903200e9002d0070002c584c5c00300b440709803990070220350114441e40c16203c0c480baa40903e0940154810300000482c034105003441c616156480d07000c40104840e04846074088090142541e4104500700d030359036aa4440307400e080314240d0700645298100210880040812415548688101c904411102e00141c2d03540440030b400d504240b08cc282d903600407007003007030144610350000c06000c04001c2c5440c3c00c0030b841d20a082d0400c40c1c9440000040b44602043c0401468000ca50011222000710a2803505c8078a9032003a10003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 458645593 1250 458644343 458644369
    0x6111c0305040f060f060302040e0c09160c0611070b01080601060906030218040c092412090c0b0715140c07030e0a1d04020f010201111e0d0e0303060112020405 70
    0x340e5640089010040e5411000340308540103181400300c4a042c01d0000024081807204038030451504282d00302c200d602083c03071080c0110003490004d0981d40c030300c02844048081100c1404010000300c0c9000040e09920900400e207c0000d20f00352240213524180240f5481078121800da40d0007180100300441e48407100c0c805984180c03a001d40c540016040d0403c107212007280c03c0764080d0501c440a4206503100c141881150002030810314004001c10811604202c054035100001c0e81d46400801400c005070070142d840e0b8402e03408810495940d080d0402e05400843c07003150071134010b03555001e8002c458000d0a0048180100785003050905480c19507140c40381000040c248001c440003142c480c0e4136490300c0300040c0b020720f00780c10242c4500801184003180440d0308030722a4480c500008559481445100c00b250005041c4a14084840300c02d000709031131400c810b804100080000f0940d00c0a14000c00b030340d2081080086449042c054009000c0c000700155008000b84140b000300119a9981e0302c91140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 458646843 1250 458645593 458645597
    0x9281d0c24130e090111090609010809030403050a140105060a050a030b07090b0d090203010e0313050d0f06090309210803010611010f060e1b0301080a021002100c030606111c 76
    0x8003440880c4910342c0159003004140700c00e10880019514071802001c2c3c860a107400007004050036081c9291001c2c000e02d4562900840d051103544c1ca194011405281c0113462481100e0400c0d0b1b990356103071325203098800101e820300d80c6400308001d204024090b00343c02000407500c84000a05103004200c0d0011301d440007401249000000c00c1802d0b000b41074080180800080241d030352485802c00c64007904034030704101d003e9880c10024411207107020058542c2e03042e61807040ea00051070602080030720717022041c040c0c5015040181201c00580203110b110784036842a118a91302602e000320600300303209142c0c06800c0c5620a940a00b00164012003203a0550b94181492031004401803640c81c014024220210070581c40d010f004a45e1a81d1901603c0c810030f203850800e1040d080c0b1944001c0c0a0200b071103050901c2c2d1000b00341038014a00034410308200c2803148120349051801d0303408102902d130360704801c1d00800d69441c03003442203e504c55041e502584000c03008002e06001c440c0480c503068010040442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 458648093 1250 458646843 458646889
    0x901110c0f0d11120c0112050f06102604060c030b030a020402030a06030203030304050115060203040b160305120f04140a02011b0f0807030918060e0609281d0c 70
    0x1001218640e42c0b00d5403001401840b44d445000d1000da0381d0b1984180e5650100350101c2d81181c4c04021406078031301c2a65001008880e5807035103014802c0329021205000306008218500540c1001c0c1050b40c03c00070110403070008a1420300c0d003170030011211600c0700781041606040402c0e8603920000317985012070380d040c3d400690300c0d60340340000070040c401900000d505000c00800d1200f40071054100c9070803100740c0364001c482180d9418041e03a4070311032807203a0140e107541880700720000004c900401e540d080c001d050107407810000205c8080000b03000c8800d2810742007030009010600059206406a40c0c0400c002070238002900d4001900700c1d0702000c0040721003030800321a07a0800050200c454203196010510f10f0300d401d002d00d800382950700603015502078840e442c0e2104d40d500c0094002c0e1300851b4080d4288640c245c83c1c1100740041d400c40206522164500b04004d111075004642540380b810403403280004c3c003c0c0780c4891803503048001c0e00380f11900e9880310740202c4e099a42c21261840500c01c4182d03803e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 458649343 1250 458648093 458648119
    0xa03060603060f0b03070e060d1e051302030a0609060b04050a0c110c0609090a021b0321060d0618080d0b0307050607080405010807170117060906150d1b0305030901110c0f 75
    0x1403427032040d2500000d10034140042d201d031001061109080d00031040506214558a01822100260384a10003a62540c00301062202144156104010190142202140001c548404502512000e5901d140e8469680c071000e40e400354091b6054400c060b2400240078400358081c0018002d00410010f03030312503002c600100d21a0401581155218030360520200100c01c3c01074419034403600040804101c00d0343c49902c4074404078600740454444d0300010154550606180c482100800a503400e224a010713601403100701040308000602040c2c80030349404100001441c00385820000c017580f00f50b010b100f0034086000010381083c19038054507001e10b400c2d401070355012002c8800070030740304040d01c454000e80300210341481551800400c240e02c030b9040341d400c1e84410f040c0c2c03592084101c40e150001d002c160341c8005645013901013142c1c0f49002d0140c4800140c2d149074a0031100d09103500440c0c50368000140d0410a580101800802e0380c09500036204224602e4040303003204055550003032280102003040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 458650593 1250 458649343 458649349
    0x2c0f010c02100c0b180a0818090108011509020f090103020c100920100c030f120e0601080106050a0806041101140a0306090e0a0f080c0a05030a03060603060f0b03070e 73
    0x2003040e0000d09110080b074412401904040d030003482a185054041c0000d0507203071101c186802000d8000000380326000c01602c46d03881c0c0341c000740300c02894403a422000c10a581d441510460203030080d03100000e2441510303060a00640950380c0f040303082034014840401d0324101442071300d214140a003000750380d885140c1d648506003c20060000c24052600c1070013000e02c00c181c44903444418000359401850b40406003008892164850850700152007280c030040080c1c07051000c206140c0b01400c104140703151240c2c07200250348015007071040c150300c6180100004c1109001d05001840166200b200b003030f0502a006889a00043c0040e0000e0309002405840b80d105003d8082c111a01403001500c17441d903803100a000c1e010310302c290a14581002c604428010010405001c0e080d071050500c0c070306e81807a9946135003940028001150b43d0188040c0b02021450070300081c0359011041d900042e001e82040c0d00a01150703540d030002c0c4208078002c0300c00d20407142a40100c94004c815810700924020b8040c3c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 458651843 1250 458650593 458650607
    0xc030c0b0406181b0609030b06210d05030405010606050903060c13031403070303050609060d0605090a022e090b090d150f06090e010c0e1c020d0b04032c0f01 69
    0x20f0821440d0b256100c0720501c1024190403200850940c241a0f940ba5603083c1154001c1b86ca000c0540030002c04804506213283c101003803843c460314000c0c422a80100030403403900f00030300c0d02c46030004114004100001c0000a20841c070140003181805400d21030440d0100745e480d90020400e205104001528200b69400c840c0c1520082d944001166601250400034588076000140110046428000444e010b03141280210b0701c07828002e00b0180e10034546480341e030701070030f0040c041c840d040c09030240c2607026072070740c140c81c50544880c9050398820b071004200c0b8501c40006500c4800130002142d030180114503014085a01009048030529440091410401d0060b602c00c18080030b543d15000c0840b400002c6600803e0880e414031804002c141c0c000400a800e80b084400312000003400c21405001030303d8120000c10a0719040c11020401d0680c55002c1035440d804c0e0f09050b140c41c2e40b03540c200001c041d444101c403d41d810402c1c044c0f80f01c48120768502ca00903010440d42a2258100b2001c1c0ca0281c0d101d105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 458653093 1250 458651843 458651861
    0x5040308040f1113021b01092a05040e0d1211030a1a0d0b071b0b0c28030212091501060e01021005010f080c0907021009020402040e091c0c030c0b0406 66
    0x104a400074041c07a50404001d502106580b0304030b46c40c0702e10f507001c0402d06218030031545070824001042400020074120007141c002d221039103001d504403c0400c05403103912500707103494021001010401148900038144140782d1300b010802500b4807524070007445c0b408050b00d4114180381c2003ca840340c600e11114641070a035901c06900241840568014480d09000b442d0040500d51250341486407000b0720f0448054808001401c01c03040000801c0500c6440401000c101240c05080507041d8145090001d00c000741a00703003000241c000c1101d0aa64140c42c03031050308079008000405001a0640d14248094014441e00c0700380500000300c4100c0d40d00a10062040b0041c202c400c00c01517031605001d0081c0241070040596500c42d0000c46d08071414a01211401011140c0040c407510060684a2010b01804002260000c5c0c0034440011030751240b5100c00d010b42c079004c4c003074142c00058010b80440c0a0040814808118803c044c21021982100001814030740000840850380c0d039500b800009860307251 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 458654343 1250 458653093 458653099
    0x50403021003060302190510260601021207030c06320c130303020f0607032913020d0f0b03071a03060a05090c03010e07050910110a06020d02040e01050405040308040f11 74
    0x20200c148040d00d01030311004c1c0c0741c0884203415841ea140b14121003002000c0402c2907070b02507503075025a0014090340d548ae80a8014412500401030240b00c24846400c03481c0114003049454004008100140c001d5002d503940d204002082c0c2010004051550300450a5560304841080702003162844001b08642404d641500200300c460380c0c0386802595075814400717485190150902203000c00303100340225917103082e1000e0014034003440014200440c3c400b12400c180d000021848404040c206400a8003804504c03074400640018425074410680e9105040720340300e9007080000380480d01c2410644007502100000c125100e0f5916004a030740c030031054000c658040c041d6030410003008100700086040e141c007041803481680390034400b55039034002d190300c0329445480034003a605036a102d6010b2400d6081e9020445d0039541c202d03141d040032030740080901c1c2c125035000241406804200c4410500525003914108a503150588005002c600701404c0103102990031805841271108450340000000001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 458655593 1250 458654343 458654359
    0x7030e131d0c04060902091f0c02090106110607030b0102100b040609090606031e0302070501080406150f0914041a10030501050112020f0405090705060f0d02040f060201110307050403021003060302 86
    0x1ea145940c0d0349107040c02840f841c1080d6020452034168020749013000409050940d4905400685003440d0480140010803c00051034490259841425590090055031241a110100c005230982406401814001854207050842e01c2c2d80c0d030f00141d070342d203004500c1c00c000580702002d2380041c02426182d8040300500341000c2d465814000154400400c03039101d022213040f0700f201c1c207617401c14040c0c010710082c0240c0c12441c001c02c00c0354041d5010560052107644009054582490b000080c0c00300b903007001d82107596090042c001c55a0782e00c9040c001c07103100c461103540c1745040d650321000c031071000c0c140760003605c001c101007860b981840e030358807000c0d56008000307200940e143c2028a440722200318044c0e10540301c0c0304110240b802c003441094001d6820038007920441d0304050a02031a50300100082c4245181004030764440b0b40c80d0b20160000c0d040a00c1c4c50801249005002801d50340300d000395401000040050040341c980080858045a906840e03501c412080d0304030940040c00158000b03900003440c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 458656843 1250 458655593 458655641
    0x90103180501060e010f0f030308070e04021602030f0a080904270602030624070311031b0307050d030e1b220902030607030c0203120402030c0a0e0103110607030e13 72
    0x6400c55000c0e2804084c030038000d80e0340e40702d204c2d50a0300e01e07104841c4a482d50200038000b003131103540747d960701000604041c1408030078100071500700c0c0e00c042c80341e04809030f41c005000114034080c44041c0d48a0380090041030400007a8680300554814050220311031f40d540d00d44001c0c101a00040140703107104a1002c4003441101d1304145010354005c40d0800c1c0b0424110707011445000444104480180c852445c29080050a94007507030702c410420038101c0103220a10404801f16a0a0000c1000001d41f1018540300c82080c50700303a190012107103002e01414140fa105012a078800140c0c00b003c410100c01015485004102140a03d404841a07140d40c0d0081010311300c03c1d0550303411082c0980d200394121030280d07440b03d41c120200c0b41300075101801600100408605480100d10403504103000400ba104080032100c006250351825500c40000042103000400034098614000310382510240e806d10700d0001140c0d00105880c0119800620541c044200c1c502089001e07400145009003220f180010111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 458658093 1250 458656843 458656853
    0x4050f240a030b1009140d05010509070503010b0402160b040c03171902070e0a0f0b0612040c080f0327030703140f16031205190305151008070509010318 67
    0x100c5800740c07402180c10007a800e02c9034181180402d00c140e407a41d481c00281e600303003080b03c00030241209405070701c4244603c090b4007045081c0300e81030103000503130001d011091510307003030500303480660021601c100c1c81408801105001c0b90301a10b01123a00000c0c0d0420740d5142e1038010b40181c2250000361807a0a034507180310050817440b000f070118403c5520b202800814800c0102d954aa107401101c0b800c00202001c01c083c185640c01aa0003132050003404200c10200101013442c1da0413140b400c05c2d440d8542d405001c1404000e442e250003800f14000980202052000220f95a00c1600104003081c02c101110441040200d90705441c0840001c084c2c6105541d00c0c100034041c13449101406415000301203000741c0250300001c001ca40c41c001694141810303482c5803518003c85883c3e042c40820300608006000403a0151103d280602c501920002402e0405003a0324444500f44050a40211204485181140d801001c4c1d658801c00c0fa03c1c190340e4907000c001c0103d014240481c4a160429284461402084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 458659343 1250 458658093 458658097
    0xb01030b041a1f290c0307080310050a1703030708040614090610091a1009081009260d2705100b03031603050a03060b0d150501030507020304050f24 65
    0x1503d003181400b01d0a07150424015800340582400c0e803002d02c2c040803041010009005481e2a070400707400c1d80c4c00c00030141c460102d190301c01c4402c400a4070300e190f0306005a2030b00d40f101d00042c01219044c14403001d08414155a20300c07000d04108140003108001404100503604030903410801c4516080c954100030010701d584031400d8078030f03080d03600300d183c40440c40300d40c3c500c241b825029070050f60488211458090005910346040080c08110030584040b0702448104402e07001800c0e8008002030381545820b24600240440142d0000d290f05400e0880043c80242c0c00d540d20303010240c60020b0920608148025036030701c0e045840c0e960000314280300061290210f54125148000713941400000310080405403070b44110b000308c401d20031413141c00c04080ba01c140058044d504c2c0d80e00307000138160348526486405400c0603012007411900c131004c50880e903400307010f00c174000e1500307003003c2c05030b4184080b020752a4001c80c00383c00d02407c488100c000f40356503507507000300495442c07414940d0025500303a20103c0c5a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 458660593 1250 458659343 458659381
    0xb04020108070518010e0d0501060611010e01140103111908030c060a06060c03050714010516031503111201021b0106030c0807030b071407050f06100e01030b01030b041a 74
    0x11407808000950301e07902036002c840c5082d500310303101c00d20080c6110041d1400c18501510035080046808800c001510900c02d010103410070380c517203e500072054140c80303003920009035040c00c0c1e99040001e03c00308880f1041c0c0c4181504d40c40384014045401420100e059650f00c08860002898107002c0007900050101c010401c0400300c8058a4040e500c1d188001c054485510424002800031503030b00c00801e110b14080c0518510601440348580031800006080d01c0c011390fa400d0102c03d81819506005416218001c00780b01c0060941c600c062450310f4622200c0441c1c0341c2d66000350803107800c04000d0182075044800c800c0002c400f420304440c031988918006d0140340000c031a016204603011803450381c00191b0004495201c01002c6082d81d5064007110412a072402c0c001d01e105041c0f0900c40020000e200c0d940e141d0321884000c18041c0f40030a01d40c00ca520f0740d0383c0046038913000300e401800440e2100d0001815207421942601141d100c525103405000d106d008001300344c1020783d0600c54505071001811981c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 458661843 1250 458660593 458660597
    0x6072109080109020f060906040305120d1415040b06090603184614010e060a0606050706021812010504030e06090d02011d0303120910090c09091e0b040201 68
    0x5545a8190a00f00d86102e440070750300450402d0303040704618140c0b00901404001410300c0d402c2980e6079544910b0014081ca00c00191500480e03e10403203061403240d014080068800c092507400c016081c0f009112056800c1360240d6214a4202c1003a211041168855440540007980d2498200070486440700b502900307100900072521848603000d07692004605014410f554450030b840c204100140d2000c401d0000c0206510540000700491038600c016001d2108210020420100c007510b182c1c02d080008107030015051a01c241408480d03805020f5800b025405200182c1d0f81c603030858841d090440b100003842d44400c072540c64081c0340c00190405805036200b038940440034420b40701080824007039609c2903600104130403611000b541c49444e0b601611401c4034034080d1540c50080200b03003564491100c218050b29400b06000840318100316035917a014000808002185075a41c0344034144c8003900c1110302803900c6e5076264003440f1141005401700b095424403100000c0c0540750054208404a84c240c1c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 458663093 1250 458661843 458661857
    0x11d06040c150516020307030206030708060307051f120b040204150305070c2a05061b0c060301030309180209030d08091b0a090c0c02060a020708061b0901030506060721 74
    0x503031030740d00b003446180c41c040944031581810f0355110403c880c09501c040a0342d051182d104000f0150f1501e10007107010304083d40d41c4174020310f0048145807900117280d103d280640d9401ca90b59903600c5525803200c060310407601d4a2017580070103d03500d801030090300c0075860b40701e031000500066003040c0d41a03281c0011450b031024450f07a9106401a101000006809031565500218104c07000003058410003101c0136003031001c070700b46844401155a81d00001080b8001801014002201c90700410116801c4001103401c545558110f80e0f00a090311203d20400c04544454012026840f22513010b903480b0107805012200401c200020040000c48107648081407030107440f440945207414000981c08200c0003070300b8161b004d032a02d0604001401a100c50104105048401e1030050366002d000b07128501242d40204205428800c4890810320050000c0761103400c084078001426220704180e50103d0003d00300001d869413454007040c0c682c4101c1500414005440008403034035081c042030000306041658801c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 458664343 1250 458663093 458663099
    0x3020301061d0c1603030c11010c030501080c030606030a320106030c0e06010f080a0f0e0304030b06030607020c090c1b1b0a1a0702180907180c0804030f02011d06040c 73
    0x40134410940300422242c000c5000c0008070340a508202440c03a030320301c2c0003610010407601c800d003110031840c20440003070307295801001207000400004015010407000f030400c40c1864070000e580c0b10b0040d1360081403410030080c1031454240b0141c0e0039401400c241d40040300c1e02202c0592070f0081000b070104807403200f200040441c014114116039842a041a180da02c90342d1100d1100b42c601e241300400380940c103502c840c4070405290560150200761806000110380742d501354945040d90080051000e80031380e1100c800c020306203600050400e81000282c581c03603815210929685241d00c81c4c00310403081c1c4a079014072001d548500180e500140845210081d10b81c0703086000b00071100c1c505114543c1014a4a000142c032aa6600c0050002c5403004117040c2d50204440b0030301c185440c08a40801c10740d00032100c10440004a02c1c10041130842e00d4508004110340401d0250004030f01802c003804011000403035200040c001d502800c5101c100203554000c075404603820b0755071400219411035420580031000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 458665593 1250 458664343 458664361
    0x60603011803120e030d090c1401082202060d021902061005031b03010219020d1b0213051302060c0109020118060801060c03170f0609150307060f050403020301061d 72
    0x350300701a80340e41c5440c2002c0103040303d070028104122900496000c10048205024498400e2900c003070301c1400140409032070054104c4001c81020b81240c1440b5141003045840c25064001c04611000a80c0c0705000440d02e0008c11201d004807840441a180700050303c100c4001c0159420440d058543c0c2210001d0fa615040d0307900a81c29841501c1d0994007054110f205402c0300e4086000c0e8440c0030703000600305040f00c50940c00c8640c910fa0500c3c050781061188102041c0c1c00084824600c020041240b80b4a84613804104001c0f040003203071041c40d81e52004142c100d0092a800c522542d0010200ea40762404244105e00130100060100c0c0800e9541f60001f0b071811102d010f850480300c840d1100340003a0300e030080a40d0107100130141203041212007800c10980140d10b51a4500411100d10600d007145441d0050152005020305400b00b600300400c00004170b65800100c41c03007030b901d90740b41c052801d05640c0f006403040d0045400095055091540101e1108841300300b020280070340305d510021545440082c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 458666843 1250 458665593 458665631
    0x912030f0c021c0f030905070e0118051009020a020c0d15060e060907080403090305030415030f0e060412030603051509060c120610140a020c010207080304081f020408070806060301 79
    0x40c654200d0480c0320380040301401184d040700d011800e4100894240d60590b2020304101058000e501002d0041006000000b80341c4008801040c0860080007641071805103010303900c00c82c0c4180c004158000030042e4021b4400d00031041107590190082c10403a14905e8100c44010262014800b55454401c0c0000c280d00ea415010707018040207080f0b802c1e6511002e908440c140d1004100ba018800b16000001c0020000c10060000f80242910140604030201c0000c0a07601c0e2066240c180310b05003007071120140c801060860300582d01206945a0424a61041d00502640d40c4060030380c1c001c4600a00c000350b10003010714840c0600d2000c0e02c03031550311900820041e0140202143e209200d0100150a50800300000da910340036500781044007880d41036050040358814001e001c0140c01c1018a6070f043d50701004508042e0182c9800f560800381040e510343c1e52162160790071550300d00700b100981d40c3c426069048901800b030f950180e41145445048166a4000680308540a5842c01107039421064072401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 458668093 1250 458666843 458666863
    0x20f0d1a030c0f042a09050a0f03150c0201110706050a1413030c0813080f060a0219030f060b04120b010e01030f0f02181e09010203090c01050d0912030f0c02 69
    0x10540c3c2d00580301080c00000c15080034407000450020951300f10140488070700d0f00151240d9541d1400d80e6051006020214400d40d11105550012010500014041806440c0c800701c00047c0040e588010a008901500e60b07400d20384241e1000080c608144186604440d210300c15a8509004d00100c4c07603400842d1328000c47c0c506c801081c3ca407803010000f9105034200c52241e40103c10302c40c100708151805014a1440e42d000b140c9680c0700c2c08846650400c01e125160b40021008421400c190103403818500b800a1000c5800405644041080f412500d82d07210f800a082c6d441c00c090f4460742c8681a03161449406101656840780c0c0e0b0f000010014140c1c1d0a1905881d802100341c0020342c42c580e02e2400005400904070b0f4042000320000c8815058842c3e01807060031008400c0038004024404801c440300c010f003405000d64010010051a090300107100e9016040a1078556680d0008048540003000140001031080d084142d0429004c1c0c1e01d500465030008501c00204980c081c40314091b40e40c0c40c0080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 458669343 1250 458668093 458668099
    0x117181c140307170f0103061404051905030c0102030f0f0109020c0703080901030b040e0d1101020306091b040305030c01060f06020a110f0a08060c0a02010507091a0d020f0d1a030c 79
    0x30010280803090500955000760550074901d880b043d0803448130a03c1402101ca80080e41820001003080c40441d00900d6070600e000228041107003440d4a035203440303011400500140c020861071140802c20104100c070340500340032008540f43e00300050040350320802500d5213652031903200000f00f50401e0070701c2124501c079203d000601e17201346140d599401a4014808440c1070580c0d50120040d280c403940190f00a503e0b0b480f01070b1050922014028103050814683d41006070b10510810000c2d403100c000d51a0451055001d41d0502c071403c000c00c900303d11071500003c140780000b0820481c480f0054121a040da40203981c40340308503032116070481c0e40c1c010b4440040e250121041d0303203554a00300002482d80d0345101414810b00507440790401480d014064a424511010010b520110141e0a00c1055003208542c80d10714102481c01800c1000c51141c640801a40f4400180144040515504460704a0240d00105440b210780600090082400042c40c00c400d4030001c1c5c0545c201c0c58046505ca803040703070003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 458670593 1250 458669343 458669357
    0x5090f070e01090b0a09020a0201060f0f03150b06210405102306040e0a0524010503120a030204030605011d070311040b18060417010e0105070c08090117181c 69
    0x1190501400c50300c4561178100c6038010004ca0480900d0009000b403888075000410b0b818a03080c180c7c48200083c0d0304c040c007415400c0c0e41c00d00006a01120405800c000444045204541c020000d00b42d4420418500c0500d406001c513240441e0030b40c02460320482c00b450940f080c41071030015810959110f00811070050310110f025100390350640507204e800c080040d00000fa200701e5588464a45180004141c4072680809640004103800b20101da40780c1f103040b50401195403400c00401d64a0040d039010034034082021501c41c414600c2075056500443e00b0000034001965101a0100344042c081c05114110202000080705070f07010740501d807a1340304a8601c0307514103440e0400c42440ca4000018682c1816008560743c7d0256407018050700c09032004500000044041141241c05c640550441c0d6405904210800480a81150701c03514003503048810a035a8100c83e10040f01c0726000b00d892108100c1c522001e0081070145141d260300800710a000325018180249207401d5001070841900300040d01e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 458671843 1250 458670593 458670599
    0x403050d02010f0216200604060905150c0601030b0c0909010905240f1003150801020901180608061e10080a0b040603081605120703020109020405160e0f01020a02030a050105090f070e01 81
    0x41801b41d03441200c00550300104d45040000469660150b0b00810000b08046001e00c810b140c42504602c08106040c1c00506d000d084943d0f003501c0741414400604060400400180003004280448103d00e0000303000d20b8003581c5810f0a00000d000903241800d42124020020124460320090b00c402910000d01c1e0154846210302000b0310046480402d004140d02d070b14400c4085c035100e00d0a50050206c0c0e6001603102d0320311038001000b501b500e2000100c503070000c000800c0a56049010541c0211040d030300382c1d05214010311018400d0054940583d00400c440429100e2039a000400e83d0007024540c00901454081000b08010748689001c00740054004010441070016110244121640300e0010f5410800360880d9a001e00d81010401382c01503510340b0342a004614043c4285584514620b0f02522058007081d8000c18603845107050a006108405c4228140d80c02040030080341c56004048072081d8015103046406050240d070003081c0d901c113921010412400128003102a60014031841005a103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 458673093 1250 458671843 458671853
    0x904150209190f061e09050405130503070b0601030509010207030228020910180c0806040b2b05190f030305100b19020f010506030c040e01060b0403050d02010f0216 72
    0x40120710041e880905100d11600c0d514902030514020b004402d10140c00707501c1c051000d012000d111040c5d201a0311002c41070504290007240342c0041da00d040d54005201e03130725044c1c0e121034600c9800f0050302e544004144502041240111036126142c21b985c1801940ca0341e644180c280d0083ca4801400f41e0020300002012140041030307103c0028080c0002d580e207442075000701c0d048000a0b20285c010044164091103c000d2641c01c01d02480b00383c15082103540b5003090000c3c81c001d80030b840d10703104640759924030129036542c1188144042c1850601155228001c0b4240c0d482010401d08840a02502c560000740c06031046140c55a66040314110700b02243c1d43c0c0e4120000c240040103014141c2c00840c01003240d000640241c03000d0242d421109071030f040c050078081d141c042140752650440c1c1c100820019203880219607111141d40c02d481c046203208440340e1450140c1402d4104041201012800000384440007542c260b164050350000c018400000111400764415110a481001400020500015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 458674343 1250 458673093 458673097
    0x30406020304052709071a0421260702010e0a030201020304030206030a0204090207111e011211090d0804051c020117040206070203011b0f020a170a020a050703030c030e09041502 78
    0x42c98450750f00d104c040113074907081104009446013416580f0969050201311152400044041160968603007028500403504141d4505140022a20b10f400309100d000c10413100317200115208841c420204d00043c2c15242d05094225000507800140b601012540394181043c00c0d10590341c060b80075520742420741e0244601c5a10241440e48055420480004c0118480c80504051782c45011070304002c101c1c0c02e00300700d9003411010268000c0746000140760f80796a0082400d12900d58031000110301326a55403002a400c1c0560f0000c540c1140c060000c0b10200f044403c0100141d42d8201c0d40d010805402c040103228500c984440280450816003112001c00008012158040e1008000c0e501c1c1c03001c1c0343d0219094940c24150004a4518030924104075500038641c503524504e40e10003400104155100d070260300302c5041710941d5016000402100480c0300344403580c0356941040407219019139074900108900640f032810f4001620644607800c0c1403506006403800b032174202480406003860350949000175 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 458675593 1250 458674343 458674369
    0x2070804060818030c0327100809420c071707230601050102030f16020301230108010c0e0d020103050705162405040c1505070212100c0203040602030405 67
    0x10000e0b0b4080a620f48000b0030050404041c0f03030015580301c00d00c01c00ca903009050b58412604200410160007070254449a07030395040d56102c0e16190403907131200410304c3c0c10300210704085069004488501c144031407002c156983c5d824003410741c203580240e000500003a054000da40c00011350743d0030421072021501010200c40640048802e8520b0040e09954000c103110900801500a001c542d842c0c00030b10300140005801088280080c51500c56420b8032074480e885042c0500c1011030640b4680c1055407000d52040c6500d4004218680754410300000b0f120340c0381024171a1030305d991700300180c0003c0c2c0b134410740090301402c2001c0c000410848040c0d0040d40a00ba00800705010020140900b66118003101492170066009110503031051210140b40081c078100020680746031400c3c84144000520b00344244011140c058940394001c1c255100100d07401d00c61218041c2d0710900418043c0000f04c40801c09552008070a24100004d515003034060b078590045100702e0026030000d1000b08868206403000d2140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 458676843 1250 458675593 458675611
    0x170303070f080406061d0a141b0d090b090a140a03050d1a270a0908030c1606022802060601300f150e010e07030903031404050c13020708040608 63
    0x1ca43c1ca40d006e01b032003184601c0c3d10810f480160301c1840010000c9215840c012840842ea250151510032a01c0c0c400180e01c00d55150300800004018400c100f06a0040b8040c960109206d200c0c1d092248099079210003a8600303483c1010b0030900c240d034000000850100017907040c0c0f581c50420b407405100340010459010408245c01600549044682e201002d0341302480c040c00001c44a000d05192680060b00010303c4540940c1c540320520020500000030b481c0d100c042216159a070340c4030300174444e0070006061401000035001184d8200318184003c01400203c0607843e0001c50f55070303206801c0741e403118140c5070a0f020820b0b0f8203000344500201c49204404c03040e04a02c003034202000c0d000540446150001c0354030015911104031030320140e0b00c03d0010080110f03440811455060000300c0a50401c0905003e052507511040c02c0b0406000760000c6076521040360b0301424600d0b003801c10035110382d4008182c610508101028009008a134400d0300c41c03040d00217056a05040c00c100065800c4072000e850024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 458678093 1250 458676843 458676851
    0x9160e030d08070201060902030f06040b030307050a0f0204050f061e030c060c1506030a1a06011202030a050906011e03061a060c0705040513150b01140c0601170303070f080406 77
    0x1580d10200000603a0640c1981e4000007032404000003802c4400c660800d1400b9801081070000e4008101103007500040100c070300240d10951b000c0000d15511501d0001886401201c064005100d10800d200400a000745c03402d002541e85c07080240c4031540100d0300c241e40f12034034107200514009030984042c080003020701140c4450310403a00091450b04202c01e14074041d4000000441412140060940c002d07409900828584419999483c120f1007601140031140d801c200005400b41c0c441c00c42c01800c0c20100c0c030308550341c2c2000e860210103041e0817140306055124000000625260b09d60041603086100c207a808400d41c1580d44060181802180040000800741403050751540c1e54801070004200c004014210700e443c150903c01134480c002c14403c01080110b800c6270210310110008480c041c4850310001c0c03c0701000d070060b94030310054100c01c1980c001c003154a1004031300014185c1e0585000205c140c4071013250491070b50b5603200490701600010383d24240001240e000302c03901da4020b413140c00041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 458679343 1250 458678093 458678117
    0x6070908160e39250f0803100b0a020307060e0d1704141f0b0118140d050118050c0402041a03071e08041a0103051c020c0a0b041d060916 60
    0x80f051200310500660034000000d0b29002032280885038410f03030340141d40c81c0341c03200f111501c810710f01400580002c0d004000c0000040d654192803e100c0c009420040545034841c1c0410000035544d81010508407a40d920306485030819420000e020b2500c84000e5070742442d0441d6002c60001c201d02d001c0c05c220344541d840782c0f400380081014858111003400100c50300c24104e44640c42e03041a621103841d014103002c1c0342000100700c2c1c40c036a000e1000f81d0b8001e20304150520014000305011075031411000e01070394a03200f80508032180303010180324034a0180048541950981003048102c1c891031280303940703020343c1444050b5101484009158401c9440c14422010724910790a00619102d90000c0c0380010b92941c104810013800b403440e0a40c5140d0845c01c00c41c01d40c1503644031795951848091a2408200d1010301c000344a2003084600826440031385483c0340e0642c0c2e040011440d4001d8050440141010048000c082c4280c428861003a14018807150f49520303981c03280740c0d01d041c22409070301c00c10140001e44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 458680593 1250 458679343 458679421
    0x60a1109010507021503010e060310020a0203031501170408030901060614090d0c0b0301090203060a1527090e07090605150a030b04090609050c01110109030c1403040806070908160e 79
    0x16500030688e0b4000b20005180c010101410b149280c2101401d035441407000f03060180d070000c20360390f10000502030007180d00162401600c880844500c0c03030302c990007500104010040c01034040c41c055607241009100d002c1d1141e4050790401624201903445900134001d8500300d24003442079110103030040c030031003516030344034102d140c0b15a2090702b24090064000040c40400e08026003200000c000c0c2541e2540100c107a03003001030080d904251040440c444800043c0000f5100701002001040780c80030400181d0104810300c0e859003258452145514905080015681403c090700c2011031308000202e0301c3c00d15404001d03802810f2803e1141d41155a402c00140051045c0c4a200c00d040d0041d0000e040320408800014110071031900300c05c0269062100072000282c003d450b40307083c02c0d070007800300d02e111000da0007042c5907010300d50252015208e07413000c1c84035140c0c01091100c2512804001e84001c00c0140c540811800d0300d078030034031200d00d0516002807050701c1c6611242c080e03c000718001c04000c40050001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 458681843 1250 458680593 458680597
    0x71d0c210907050f0907050711030c03010f060905070c051c050403020d080304050d140a0c080729010902070305030114041d070e011d04020d030e09041103060a11090105070215 77
    0x60014030b644100c1040c0468a008110100842812540200c652900b11002001c5000320b010007014170b0110408a191030394240701845910304050000c001e07000e00c02c008000a40110700c5510100b6190001040c0058415605861800d41220092400c210300c00604019516100c01c1d00c410481c046c4004070060756262402c0c58a68080d11200e0303260f0070f080c24414140b1a50a4460382841b08201c814036094425078141c90f095086802c0010104a49040401c1d00b03100b02c10000f8220002c180c034a0b0346907152000082c0700080302c0c00c242d00550384c0f91381c16501284204070b0301801040061004102d5600b103119451401d1001030000b144c840c140d03a949030301c0030384000d43c081520b402c005014041c00022018550040c0f544051101000c080019540108080688017030f00400710b82c071a21003030501610400504003000b4203a104285094141102a1612042814800d00910300407440c0207505000b2074141c840c28002c01450714242c04015185039210302c00c201d8100000a41e8042e20b0300203800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 458683093 1250 458681843 458681851
    0x60906100309021504060e1f0c050a0b0405010e19080d0e152419060302070c03050d0f030b030307020a0521060129030705040b0d0605030a05010c02071d0c21 69
    0x2007003580700c9003006c00c0034001c00210016180942d9041410311040d094a90448040c031300e49040203805100796007082400d00b11410405484880e0000c14041013010540c0a00040401c2d0300542d50742c900e40da0f00d00b15800b494150054451003085c400400c820641da070040314208050811903542c5007502440d0a1040402c4900e1050079104140062005c0031441c0040051070080f61000035400c50487c2960036007079180114010941d01003480030402400d500f180d80550341120071902c11018494006007580410311105e400a4244000030100381800015034495070740c000c00d06010141420144a002d82c1d8044254050076008600320390340010a00c1124040c01b40c1c0070030440c554000c000004200c2c000e170700f41c1c494150801c200b006039180e4043c06a4013592403880100d540d40020f101890040c00c2e0300e40207564103020f43c038907850030083d055104e0340c4c400300c5036000c0c2c807044c1c1d60300d103180e42911591042180c0d039002001c000401202c0e0301c00080004120084641903607144015000b007418000710307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 458684343 1250 458683093 458683129
    0x90310090507050d02061206030a080408030a0f030b09070806040b04020a17090d080a0b131a1e0a0b34260702040c14030a0207060b0906090610030902 66
    0x454140d040c4082400360401518040c1c850300c031a00041c0d80070420364800d00c1d200900c2039030404082100c03030340c092103202100b98102000703685580e1540721031900e030360010b40200041039140301c032400810f0003402240c03003000b0010072200156640700000e0321002c0b8003c24040c0e101c2c0c0e0b102003440290740c81c2d2000e000044025642c00c4001840c680411180d003c0150011341140c0c800920014844c0e8450039040c0d1108000c3c0c0041042001b5074082000190030803480c0f000541081e01104450200480048003400304844011100c0c2c00302d0801141e2224164809800019040003841017054040090030380c0103012001111801c61132000e10000741c014644400403552140841e41403044454814240381100d2214400e83d00c411030880c641c52041910090060342c448101440003030040c2c0008c10f035600d81a170b00c81da49103850507142d00250f00c9240112146440d0810007205800d060701e54074031500c005003c0c3e4a40d03441c0c0c90100b0070000c04e1602e80000301030300c884005c001600c41042400200e4821 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 458685593 1250 458684343 458684351
    0x3070b040b040807120b01061d03030d0c180609060302090f060d0c111617031902030a11160501030b0d060911100e010c020108190e030405010207050a0e160302090310 73
    0x11643d6282030840c5030340440c41c8000d519034004045400701045a04480b003d00704010800b0100102c21041c684504c14540c1c180404030742c0f002c03030410f20f07088038603442c91940c0e44029500362001160020a814004d40c000039043e60014800d45003e81d0090500200080c605a08048003400291055001c60b154180c210b49030700110b014142c2000b20075040c400300f40007400b0708900ba03e81024009811b841a1007840703216001100322800140120769242d0000036840c04103842c0004080c0d92a440042a800050440c2100d031250100100c0c214050641750f52880340a1464500110054850441c039907500442d07202a82c000902107219205686108055080a032801c800030415006500380100040c042041c0035848142e901c01031203220a542400c0111140d1603000f80001e003140204150481c3c280740c1001c01d5204a0000081c0003220001d034221200c00b5281c800b4001d00007003911800c2e80f041d0329400410b0081c60311411040c1e00c001d151a005051059a00019152034480c1100c05003856903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 458686843 1250 458685593 458685599
    0x1020c010b0922020f0609090f0f0601030204080717150a060e010b090607030818071205010f02040509040f06090b0f101401020c01030216050303010e091005060a0302060903070b040b04 81
    0x2021822070b81c000c40c0150700e4080f01840c1400f0600c0e620500074000d04c1350440d03001e007030582d50b00c40b026907907500d50181c42c01070f007440e2902c10000b0980041d64840c0b00580020700045240d8424000c84007034484003009402018584640802a40e80030090100c503805820615900d03031011024092180140300d0020403c00d24090410607009030680003400f811404000080c070701e4803003508650710301d40d161510010b00d5440c200303514030030170108004c2e102174041d41500046807940001c00000840c02480200f004242d135011440891146d0f10a442c0c10500c604000380c0030550040d19440c2e07440c01072201184032082580e88490050080310398041e803030386100601420768190f420202c05041464a248200d0000351f002075038903903056140604054001460b5207880102a2404007030030b074040304480d00ca5840c0c800d90881c6800840321030400348512090203584540360300500e40200f030302500959119080d9001d200c0f055008504098040c445c00c0000504003c2000040c002032801d50103041d100c1d42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 458688093 1250 458686843 458686849
    0x1b0f0a1203023a0e0a081608011103040c060c050307061518050f2d07020303161d310c020d0306142407030e010806010203120f0c040801020c010b 64
    0xb00c1020030b10f030b450181c1c16800d00030b1180b0085110320b028504002e841e0102d0a00056201c280f80e030440541030007141c80e186400c401101c2d003a01034402c168024094402032488882d4580802c131405000081d484a0030003404e4012a000603080b400741d41541d05d1718103503454010981d22030b0440c88154900f2800700300405000310101c5a01005e500a0034000ca0404080d42550690040d043c1600038808510500d1450141e0019084003030130f21014a00c81d281218019460740c00484603038900c091305003000c01506220342a880c1821005134805001240d4000504c500c605401040c864450b461f43e4815840c14060708100100e900d80316000304098000341e800a04282c0b80d140804241403d00e00103001c0740020043c180200001964140030304010300e400c13501c0000702c144281001d6800098400181507000c503601e80a0300003038031a1610b948988004907500d02c100304070300030350b4004800429900d81d40d4a0a50f42c0040410050900705611003510038226400042ca00032240e564001541280c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 458689343 1250 458688093 458688133
    0x120c050108070f030b030c04090f0605060a030506010605070629041128050f0d05060a1d0601030b0f1507300e03011512020108091b0f0a120302 63
    0x6428600722815080441000e00725001000006080c15242c00002c902a00e00704606031000d400104140305154a909044000d100d9020041c3c4503903080000003001030515441c26411694404d00070103440e8070340442111590400e09003144c109885021185040d030703207111188403c951000494880001d00420003080307821041450205920610540c15686422207034090391191107220300407060202c0704215060710580c010700c4071060011030a07000860031603202274032600c003c0d078100d00c40988400c0c50f001c1d0000c551803100c40b020040c8001894551003908691080407024185040f090b0342e91b40041e0414001d2150280802004192042070185401c428141c86102d04600c41c880c0314091101140d1000070704030030041c80f40c420302c81103168400358050014090b255092045c0591034000d0b03138a5810b140034090380003130036080200b04851404250602c01d201c40200c0d05551600c4030050042810200c040c1c150701c003541080c0003440508070400180041d10076409030944080c0b141400d0118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 458690593 1250 458689343 458689349
    0x6020c0c011d0312030c07062f030c0703030b0a030803090a032327040f06140406141306080f07030c08060f150f0a140114120c090316120c 61
    0x30b9031080e44180540b004104500120380400f032141e982c1c0d4a80e048040c4030700c0f6185008200c1c03890090010320f40217000043d13042480044c0d0f84590004211003020300940010349480c0500001048640c0000c1d00a034401d14004001911176104030341d8a031034600d02604201e4002d903654000600041c2059131146455454191400c48031040e03200c2062074070a5070141e40d01102e00c40003901e0155003660303180b0500c00b2039800c0082c0305000312a10a84094040c2420b4450100d9606441841c0260f82c81d060052109495240c1c61001d600601c075010040713188ae4100c3e49080e920754039003001c00c1c004014040d0707060451701d80008050f010302d90301d00314000000720b40c403400d5590010410302c0080002c8e0404190840b441170120f8082480800c0090f80701d1052140280e48000391010000e01c40c00a92003201140c0800d1b21801c80c041410710300080396203d030b90150314150381503000044c4400c100001600a404d800350132551401d00e18620342c1c00450ba250084a24080390368005d4040040006108010b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 458691843 1250 458690593 458690627
    0x2011d0109210210050903040303200c01050a090810020712050301030f0f2916090b0f0310030b01080a0605010b0720131d0c03010204030c0603050a060306020c0c01 72
    0x20350319552151410b0080350402514040da200d2108005248200034804c0d0400242108001d1810620030030b940d41c0e8810b2004a011a290504100400e41c4100f1070b210f90110f624064417500c14034900442d01940310b0b0700f000f02488403030301000c9040702040040c9011220680320043c0d48170329504006203110138040c80e03941008410001030001401120b009800300758032425010340c0082030f18042290002028141c0c6034105034040e00e004c4c41804000f07044c0501c81c030401841c4002c00c0303007004603540c0d13a580c0034114001300c2c00c1010810210b228002180d1004003040d0b6112081d03200e544641100200303911000c03555200d00404401c3c40003d10030a401000f4151080340780c56002ea0b51107000c05518081d60f4030481c10600361801985600c0003d2000300b0300710b2000c20211100d1440c161141001c2c1481c14000d00c5403454900503800c05108031420340703402440c164900b500c1c0c11021006401d0041440d001140c81c2d800020000d40107001500305141640d010b0540c04481d103000600d1841c5006244032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 458693093 1250 458691843 458691851
    0x150c1c0b1212070611090603040b1006031503030503041407060203191b020907020f10060603060f053010020703031401030b01090e15100303022a0112150602011d01 72
    0x1c1c101021000c0f40d0071140d001201180700030065085e0041070041703911060304000e00000300010010982d141d00c3c89521040105102d00762503160480480303607142d10201a03500681d80030f00109000d1405598080e1241100ca9800820341c0c0300c89042082d5644400096400450003000b01c8001c41810412424640350241d11100c510340e10301e159010115000c5c0c007c1508a0110300c815109002440102c4090f00c1200c00703550200c1d09520007400548602030020b86440000708201c8800d10814003112001401e0380300344d003440322100b840100f803050690007a00e440701341503c003610244031484140d1207e07240142c581c103180c20f0103000d5442446d109a0a41442001400010f0105038014107540d03614000140000c07554070b10074500f50340001c0301180c0342c010608101c000c0a80030b000c50240c034420742c01d42c1c000d060f20211207000114043c280d0b01240c61216400c200a5105000540c20481ea01002080710501644559071606060700201c1c0181d4503404540440304116210140891904000300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 458694343 1250 458693093 458693113
    0xc161a0903030a050d0e060114030705011d060306010c0b1009061202010228140303070915020307060902210705041a0d020f010522060f030c02150c1c0b12 68
    0x194903403040c3c1d003480d002c1c0b14011500d4580791003542d008a401da00f0030400c8450650b12a001240750040040705c140c0300740b08030310021805e54850050382c42e00d540b0990413168070360710420400ca00798100034030040c1005440c00944011600e0a1540b0740214901c4c01c0c0703201c500b4200700d402c20545000e03420401ca10500ca10f29000107036400100c18800e945440c5080408248002d080749070001d0499018104d00184140810755201c080029409146142c03500402c0d41d550750042c1c18042d40c202400409a0001c0c020403000c01c1c3c2d2600301000607031009014613049100307403000c505680d403c0e1106d8a410b03480a00c00b400340d41068481c01c8200d0741200c0105115480c010b000900001c07031241c0080c00307080c000324807807001c1c0d0040c02603500f0030701d0f0080c0d80400c0140108951000483c14030510000801c002c400c00307009400792203a03018800c4268082c0c00001140d41c0c0610712450041d00109070f00d4400c000521907481d00d00f0b0384443c085011600402d881a002c81000840105221a04034a0700546160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 458695593 1250 458694343 458694349
    0xd020a1203080f060f12030f1803010f11030103060203270615030f030a11100608032d04030f0219080f1002131509081009030314060303160204020c161a09 68
    0x503d10785c0c41c0488070300c0c0342c110250800340e045004090540e252054041400c4203d031401080440c400701068000300070031140c0c58080c10a6480c01c1c40e911524002c1000140301169850f002554024086801c0e0001c0011b2104100d4030010903004c40c01181d048078043c80190401d00c40200304103101100201032001c401c079055a1241f00b0259446c043c8404108207500b0301e0014041d01541a030310007030800046607111111a12a40240041f90300b46900c0700c60350340c03100341c00700001465902004415044c00d0442d507503103040740440402a0390021880410b0505102060301d43c1015100c3c0d44007408186882d00c02c410700d4050403450300040030740140110400c02d02059210801c03202300f004000c0d445405000240d42200a64000380c3c0c040c00755111007100058950000c00d201c501c40d40d410028500841d1010300104400d55503d81d0541003003020354946080b00b010012280d0004000618100028101c64540050310070240c0c3d8131840a1002c20050a42c1501c560580119662841c40c02c0709000c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 458696843 1250 458695593 458695609
    0x7060903020f040b151305030a03171605040b0708130308040906091b030c18030803071409010c0305030c0c06040606060206130c05090a0219020c030c0105040605030103020d020d020a1203080f06 85
    0x5c0071250100106030b512403402c12081c40c0b0014a80541681c0c0710700340c981002400d85410300a180c0100c0b02000128182c50048010700c0b01914081e600c0034141400d00803400115404001c090300c150205006540300000f220001c1c40040d4440c42259641d145003612060a4440540c4441c0e20306203452050a202c0e2984084080c0780c12182c980011b00c082120360940b11161040300705c20702c0041e00b04000c420041c040f030007507000b103540d5214002c0c014001c0802e024940710329980e880c0000d0000c041c4000180c00346010312340214102000ca42002542c5401c5480d044048405a44854039100e01f006036a406126650304921007030402640802552074055250080d8800c060107101c401000030760f001c4590b410345050402d0309581d0100d640c28034400035550007104a4851013805000440c03883c81d800b0303e0894040768002d031155400c5078655000c1200100c0040d00030b03a00050400e40c000e005035038042c00d007801390280e10f007124200302590500510039a401800c00c09528458424030216503203000e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 458698093 1250 458696843 458696869
    0x3190608150a02030402011707050a030b0901080d1101020c01020a05071109250e0d05060708010501030c0210180605070f110a0201082716030303050c030f010611070807060903020f040b 81
    0x78026030b0300e1721140f0040301d42c00381c1c0840d0300c0c00609a80050260440d8410300418034003100740d42c240b21543d001800c005c0a040203103c1c07840036512181888240c07034050b0304040c0003d40c540d8001800c0c45002291542660b0010781d82c40300040000030504108284001136001c0920207880381c1803d4079088c510121044d0100c4c0c2c800c0e003186858002c070400c1602c0750bc0312500c1c0c0b200c05040200301124614140b42d42d884241e40000c00304a0342c0d00045040d510912031000201b50031341c024101c48084c00a00001002d0f150102030a100030307034641101040d411b0240031f02030405030366001c910701c0003c17074000d0500382c507280c18003507503007211941e040581e81c070600c00394210f2011401c0d00d081c0e082c8001040140b105000600140d400b5072004a0303820003010810390100c074000e0702c00740400e40d2101c09014040c84105c07400b854080407000180401d034030442c414242e0446203070850303030b040382c69002a034940b0300694000c2d80000d15044060085040007210b86010744000d413410700000b03002d44001102032659030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 458699343 1250 458698093 458698111
    0x121e0a0f0305071b0b09040506032815050702070e1b190309060911191a09011709011b081911090a150207080a0803040210030f020319060815 62
    0x812100c0034440c00b131551a030365248000c40480c03000d0742d0300052034160304400312484c855850300f00014003a00780450300084811500203a0354680d655509100c0e1702590303a95054440603484010814035034201e205943c080c50050300100001c03440e050741007213801c200610b8804441403a001040421111600b96602150313045003c0e40b403a800c0c480101c0c002c140c0603c000d49910309000382d003c18050120311100b1000d00c00c0d25800031000c54013010101050a82c072800301ca80d240c0918215a40983c240500f001650502d85150b14114900294590035400e40306500503955074010211010381c4110070500d01340203414035012510b031540b040039920000c03001c090455926614005c404258800844d4590300004140310010b0f921100043c07902005000580003510507500d000c42c1c00080050750100b1103500c400241e02d590790ba85d092096500c401c01c074001c00e05403a42c42424507080c40d80050340c17182450809180064501d0007000d802c1c2c2e00c00e80d01070741c0150401700180c5a409900d180c40e0f98856854 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 458700593 1250 458699343 458699347
    0x60f0315050705070f11040b040b06031501030207020a030317060d03050d0504031115061801180b0612161403090a020d11031504211209030905121e0a0f0305 69
    0xc840d00303031082d03c1103038002007001410740381702d90400201c580c0107820942e042d070301000a010748105100464203030304007142e400281400002d03a8035034400040304032850185005802c140465001c10715900d107a41084001c5503030006003a5440b8001d003c03641e400941210303408010a070584010f0540d208002c0480c1641c2d4450000805150068104804c1e00c010340d0201c9a090040ca9403c110051059070b48511694240d02d806961003116441241611814403103e0421070040c4c40f168014184006074940001c814032210510a4859800c20701c101512041c2500c00b102c5800014a0174540c1882084125020b2082c0460300780300090400042e45d050351903864039020350816440b02d0a4071640258188240d005284000c5045103041d80560303c140040c0c0c1079601001c0250807140c094900742e900040d2250801132580a03150000c00129000f03040c115201070300e41e00499004460f211a0b01c1055000340c903441c004d0264030003d508011a0000075201551079591084601c1d10b0020002d0108080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 458701843 1250 458700593 458700601
    0xc041502070e01080f10110f072f041404031407060f020a090f0e0105300a2d0506010306111306090e090109030801180617010906060f031505 62
    0x200105005080a0700072a401983c1d1003a0507640e1750060924004580208102441c00360840d000304248003964850090800b0000303440e868103a00f00c141c00b501d003c20b00b08030300211100101a1502e01d699030310400902c40380840d080c841940d01140301751000350aa001000086039100f91070070160a1005280d5640d4686401c0c0350000d002c6c181019211a8030000740c07100c9a80d002540e510459807625001580c8965404511100700d400348511900104058502a51044400400d0041c03180aa010100030b00c2e45809862800703040540440c2c08155101e410300d05001541214011700e02c483c0000740b40108c4c01c1d500c0e00e131544010b01c0010304650b254030306071040c0d10351007003620b814040c0400a4401d655440c90001c0c10700d4178501c500d47c0400d0291020940c3c110060141504880d0544c0324031500e42d2a10f210340540c0244d808401810968810022030042d980b0086c01060655440001c5012006410200221009a80318807079011445c102040040e0040050940e03480e0750060000380c41c0d032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 458703093 1250 458701843 458701847
    0x60d150c030902040e060108070602031206060310090515150a0207031509020d0b040303150b0a1211131412100207030201090b0a0207060b04060f1202130504050601080d080c0415 78
    0x41103610084d40f00b400c003482c280070040001481c1e070484119800b190740140d40c0b5241030782c40b0710960400c4407000c110b00001484a007000401550007a207440c40111291f0366032003064040391000e54000343d541040c8100b44515203072500a0039110403187c0c2d805494140c00d07400c060365804691000405034410701074181044050b50b80440d0840350090402a450200d92528040c000400c440840c042403421078600c2000000404010540d08002d0040786000801503054039400c8048844510f01c0d6103558201c1c81c044103d20291400f40d0700c2408468490b0700700547c0c40f8101540651b128000c0c010058000078140c0c001507001c8a50303180800041c1c0e2001c050400303d0140480c04405802006050240448071400d64028800039024440c1003007044050300401c4140e905034840c13250801038060f81480030f10360210082c8402440201002c1c0080c521464813030544108540942e0035800140040102100c10701800342c0b030b203425107404100380c83c20240380207050040e405001051140781d15400e241394 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 458704343 1250 458703093 458703101
    0x50a02030a060b0f120604090f030c0302010c020c1e04060f06020a02030c061326061305010b010e03060106030f0209030d0309031d0604030609081204060b010f0c1a1902040b12060d150c03 82
    0xa800040401112885040240062f032007071208800540c645124007a03480d01c08201d1400846005010640b40e401602d4150301507003c118010360f115035150800940c0003104004030000303052540151155419030700406041520041c8002e0090070108695010700c4020880c0c0e000380c6103040d40b40d1007000c503045c0740450b81411031031a00000b0301c0f82d5028002e038050103200010805100340d00920240111070f00444d90980c0411082d90503500c000014002d40c0e01170f1708018000603400e41d00604007482c50001900c1d2811b030170307c0000440d60360030452061503809514502100b450101c01c17020714800701d002c500310744a140b1019005664408030031040110203400c4403203e00c0a0316495941e42801d04240c001880e405051a0210740820340c40c002e014000c145500c1d00310340040070703680308901501d148520940010502d20700c4124032100521030f90f03412b1000e4006000f40340003207621406c81070030351883c091001e00450301c94401e0080050000f506405070103040c588a00c0d000c0707050401d010341540030b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 458705593 1250 458704343 458704361
    0xc1710020703020129090601080a0b090c030901110309030d09030507120e0a14011e11030a2307120e0402040b0f190c020a2106050a02030a060b0f120604 67
    0x1080c000a003120525074150429607404520004071480d50403020360805100b03070340007141500079862500003400c82d8000c13200180d20803804003011901e6820440002d110300c20885811040c3c18002c01800319076070003445000d98050010000364035504001c03142c40c0c1d40307000d171182600d080b5469071341010800d4400c0c41034660483e4040390101d0000d0b40c540c00a07200b00030b0310500700c2c01031001000000d0b89400044020a40c18812f8580090300c10000710307401c4000c46020800c1c014000046132011039400d08000501c4d81c4c281540e6030807186040f00d0960300103002c4119601c104074200340640008a80d1100707082002508600386180d01003854070120b030103805540e100700c0f1b0304900859140808020300c4020f221126540d40d004020f94280ba00c01d039004c00413010085c0d0406080e0304244401c00d40c0083c1c1c60705400d42081148802e0a559a170441901c01c21101d62407403580101c00d010f103c030070a000341000f0b84207480b021402e0032004110041d4900801c02015040412000421016100d641c40000c0c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 458706843 1250 458705593 458705623
    0x207060203071224030b09030f04120501200a0809100e0a0501290d0609150c030e070b0f091201090b01050102060a090c050409140a030e030c09040c17 66
    0x72450850800b41030142400780803021a420501c0fa0045040102c401c001c5040c0c0e0380380f001058605640716440341c000c00078002c00c030a20003008102d00c2c102411000c3c01c02800b003103c040c40d0140403860841c5c00e4841462410604800040040202c41d1504043d501000058034200e0610f90300c013a01140303030440c0707060b031500307181d01d0030015942031032000c2242070155005800901000c45c160f0b448036000401c841c0801c06501800040d070b83e0380d26113001290810f078007503031011411000c5626108000400e0840c034001d465901d00004100580500030710325441d2101016003072440c80c0c4009440c81e841040440405603000150303420042e0b585e540030703603000c0c02902c000300040c80a619020303032800028059580584184800103004034018000c0c5600b45d680004200a0245020306100c060109074108442d10303110300360030301440b0904000c42d0081d0f82c0070381e50f60007001041500341420315407035001c2180240e40040400001c503e416035024210380d0522044ca000c0140d500e00c1c281071003407000700120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 458708093 1250 458706843 458706847
    0x40b03160605040f0b03010b09010e0627100201021611040e03040803120115020a03030903050919030209010914220b0f102103030c030b0a030f14072702070602 70
    0x900154000d000e04152040c4100d00c684045d151080d01c8403900003445052038161041049801951051a0070300f115000030780101d00705400700d618040018a01100c50316400c0340c4900b2060103181034070040c0800314050000b14a44400f40400c5101c40b081020041c05c0e10440a192050580301c5030701841c0071030108019691102e0311114800d440b94000581c68074500f03841400840d100e4001d5801d01ba0080303958004011030b04043d6020f50160031808015414400300b80994441510364042c0111280c043c003100d2118a4150f1040180c00d04e0180c0040300103074504030000c1c18a890880102d070b000003400412040d07030401c48204506c04000403000034001c100e40ca0030303c0800b507030316040607010f2100c01c600940f54076204d10141c0040749143d00144002e40701c00114102003070180d8011680c4240610300481c410100c480850351007200c581c0b040b10440f803c041000240007641040f1440f03400ca0300c0c0500800d0b072030048400c503014040039000e03034800ca406040320b03880603003541144c28641c2e20800641d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 458709343 1250 458708093 458708099
    0x4030f0324060e04050105040b0102060403230c010e010609150b2503050a080f10381c11032d0f09060601090303020303130203030c07080d111605040b0316 68
    0x14121040f0010b0350380203d04201c0081030070328140c024901401c1040e80201001d560366102242c1042c42840c0880c0008164402c0411089034080240f0480307a61100101c0d214104094a82c2101e1a507444040c5003445c04a003804048101031404040300c100c04215502c0c0e40d0102789a000d501c00100c3c804021903100820f200070907070404060003840400f51280000c80da10300000000058084500f0001140747c004203001d0165420111950540090040951a56030600700d10016119074180322440c1c070003003410f40d0030b2405541d54026091901e40c050008004110707228455004c050b014001070216004203204440340c00d0290380916101c1d90361320a440c103000d0148200f0400039a101c0d80076014110000c0c9855014034407200440c0d034550300440c51030350350340080c400c090341a0800b2a4140004c04c6a00300d010300401142c40504402d102030107500303d24440203001c1500034100251035400845802e40442e20304c0001c0422240103030342c0458ad6104120000e42002da075561281d2850031842c0e404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 458710593 1250 458709343 458709347
    0x31d06010611060705030105180702160323030f0f0a0507150501031401020a0f0f110f0d020c0a0b0a03020f04030f230114010323030c0f0d0804030f032406 68
    0x71603040c4610600f669240e40f03980d21300700c0b243e210900035a500312000340c0d201c24021000d0f00c07040341d202a0510603185010345d03c600455041c1c0c100d03402511a140007200d050510700e40151400c06401071840107514050300caa004644a000714040c054015a012525002c014000c0302240c07240740d80601041040980b40d14030000400007808180c82d000c0c8140c6400c0c5940805100700e03a0308102036200c8102c2c1c3c0c4817083c0201d80c100009c100390b100b0090880c009084541042081704020404880908107120304d51030000d06e07044000c00c05c0d03480b03000195002c0181400e400122500114540b4025a41e207a16280080807882035510050021500110b140144014100712401441d8203034201e507204100d25000b03034240e4403a10540302c00e0005c01401007001034464420b04119001c8101e4294002d580000340c641581c10881c20400550170005403640d03261001c1c0719508500140d401c2c030019908107a10005c2407a03400e10400010306540310016402048283c20390301800106200d14100e943e25140c1c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 458711843 1250 458710593 458710607
    0xe0f0706090b040e04060f0209100306172e110d02030403030c0e0a23040608070303090906061b0c030816060b0d05030906070c0302040507201b01031d060106 69
    0x140200086140501058009101c000c540481301450840307281d0391540c1d207800b0300038111700c0e001c090042da08000c42c9071140c4a902c035500740c240c2c560f01d00144032454141d56100a1200c00881e40b5980c000c540f10b05160f032516141c0c8140d459882d814001240365104000004000e20051020101c101181400000400340c004501c20341c4a43c1e4140100b45200383c0a0b101500c10701d652690000d501c21040c006480094980340800c00d100c00781007d10051700001c5000c40300340381c010350582d03004100b0900038035402050b800700400000e03a04001d46440e01c8402410300d415011001e0320084843d62410900c20420b064601a68100e8075155403035007001d003400c0800000d000c08684e01c0d4146403241e500d5240c22b49000e210141c220000e146010415030030032016502504013128030031808180800580c85500c252485103a194454000c1c1c1240f80b139152a9144440f0141d484a90103030706401803075080c4c084a41c045450038240070030500280003a82c144000b4020808080e841040c0c00017a610b07502c904 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 458713093 1250 458711843 458711849
    0x140a08040b07110306090304150201150b031b0306030307020904140f07050103060605120c03130b0405011e090c0b090406030614150a03121b0206030906060f01170606030a0e0f07 78
    0x180c100e03241e0b0010134944c440d0011945100c2c5074100348001c00280000c0320340712091043c248000a001d4820510882c1c1e025010f401803452a03c000c0108405100380303003d003c07041e1f2503c2d02c12a08601c0c01000003982c900c94030030002c0c00f81601c04d000c507003002030502e1403d000440410a8902c0c0040c40302c07001b81ea4401901c50740e40000d00709030000a11900400450720203070000710355041165204d204610442d40003421564203c54021043c2011600041c04c69000314400c00000c0b85904841020b4919882080100001940b42c01c1a000c00500c020305d48204541021400646800e892000a0000c0040e45d0000d403107241000c2285100014002c0850302c034100b201a09c0c0d08131076030b9001b0300c41080d240740001001711101d2003100030728074001c0000e00407850004000f00c0c403100d02c690104d0a250010760b8500382a44c80bc0782409580d181040d14060101420320300f48844010390005140020009000c0900840001001c506104100e400107030b030217840703003007110400298410825503a4200d44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 458714343 1250 458713093 458713103
    0xc080a060e010b0a320a0b0415212012100b030c1c020f040e0a0617030403020405060a080706050d050a02120106110c0a0f08010e0c01020307140a08040b07 68
    0x300081c500940403c00351100c114078400b404581c610400288154032041041170300d004d519150440e0303625200c0390080e04072a40c2290301c8500d400c0b03200e81500240305210b814020410240d0445200065880102c1d81079400c3c04501000c020300d01004400b05070b10b1400c8500d800003040468540b10500c1c081c051000e0000c60b1142c40d54440e49202140002d075200c440d602c108000351002d40c02071080c80d28003080c40d03d10040c80c3c07400300c03d04a138240d805031380b041c0304c000303203c0c0100601c3c0401841407100400c82400c61011034258100c100703480388618003009102c0d81d52940442d00540320101040c000e07010200845d55099121000680340780c2284007111486030500000440312207003802600c8610205402c1c0900c2642232000a40b2042d00c819210f032441d03c20404c0121160391036141e800002d10002c0340c4083c203142041b0080c7d0a641c0d0401c040c802c0707a809215110203d907030000c215a00250001d10158450b4142c0030180d0404e4024800909611400705000c2231b10707030b401c80042031303898441c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 458715593 1250 458714343 458714351
    0x80307030e04050402031e0309060d0606110c060d0906090c080604140703020d02010c0201050d110a0f030e2104080a0303140105240c0f0303040c05092208070c080a060e01 75
    0x400104010fa5400300c038001d4050f004850540650070f5405145a900c803042c034187c2e4100300311000030507101e41051000704105030320b8a43c2008030302d801008079010101c980025081c50b420032000f05040348540c088401460f0f90311113503541486810350028000c9a444810a9061a0340c0d50602d070740c0c5e00040d20b00383c4806a24901000210000041040485c0e6000e45142403603a4140c00545240440e003a06a040c44400c00c88000060940c1c410207000d8021101e41c1d40e210365a00720010300c1000000140c0c002e0515100903200002000030b8240c9034a4504019011860009200340401703001e1030340302c034080e072242070824804c041e0140c001d4141d400582000c0c4400b680d2700c00c04c0000b195071180c681d00d4020328100e65030300c0348800c8400414458080c001110350b03041c0f82c80d4002e461a0b00484055566118940c82400140b4005041710303080400960303041ca03040310f0400240140d401c203006c01810300d44002109001c000d62000d4400051070b51900f0742d4004074490821038041d24464050740c0a030f52030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 458716843 1250 458715593 458715617
    0x50c070201024902071d06060f0c01020a092117090a0f030b040b0a060b09010305070e0a0311031b1c05070f0e06120105071202160f050703030905010206060f04091b08030703 76
    0x10a1b048509080e52815030080c20b071241d0051040c0b550148440f4214168108034045a40109000070b0000b840965a00720405180c012080f00c2540c0003000e002a08820080c3d41021441c0002e140000c81d0504c4040d641d10480140003c03100c50181d48240000c80c220340c400801e014441110b944610300403031056500343c0d151003004003110310342d00442c203101006000150003075209a10a40e801b04850902c03d01100d44580040c172100d0300c6030700440d081d003000c8196283d5818240451200c05000344210241c00100700d0005800c3d400b040a8002808081c40c0c0b00010b01a080040c0c1005001d00d40e03141200f11740752900e100c20002d084481c1c601419070030f0104403241d441440340601c52182640c4030702c0088025000e130b0700a940700800711079406883d000054042041d5890352801584985c00410100d8a1464050b01c06012940b0142c151b401c20001c10010351550540d02c000c2820031200041c0340203191070b025108190b41ca07e10450003c104502086005000000305130349802030700d070050640c138 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 458718093 1250 458716843 458716859
    0x91a0c03070c03080c2a010e0c012708011505030118030e06030c0435070609050f0f040204082505090406022203080904111c0915050705030a050c07020102490207 71
    0x104240702780c00255101c112080c2c440640a0200340400c8441030440c01c0b17947e600c1305600755020b02c52004004842a4810001c40c079091003200603405240058068004090310064211600c8070401e5020b2200000083e0140c0e807100b04480c01b500c50007441e100304104c03071641d10390520010b0b200707240712004040300c442c0030b24000140f00c41241c8c42a5030348203900341010140301c0402800041c4076048000c1e080c05080ca41d49038000342018010080040141066480c020034141e164081031580b0060194002d2140c1e0300e40710402c0381d0160700114056901d2001c01c0c0d41d45002c4020303944400c81e0311540030004c010002c0400040111210849060110364080c4401421601c01d00850320307004001103141c042407100d55040008900c0c0541540d41a100c1c005441034240d68080f64908002080007007008941580e6204040e0001d0b261140c480c181445a40080e5039000e02450080c40210a80300740b829040d603000c1c0300e05100001031151811014400002c403e0f018103521000050300800c03d022641354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 458719343 1250 458718093 458718103
    0x5091b0d09032c120703020405190615050f0a2607080901020f07020d0305090a1d13030e19080f1c1110020715091a0c03070c03080c2a010e 61
    0xf08000042a0350111410404810940c01036810f89000340705000000da40d0314403030756200f01d000034071860380001c21440e000c0c00c407030040d081009c030005070701d9206610551003c10b03582c401d5001450b43d552441e40c2d81042d5094101c1d00c1c020040d01e074001c0748030503203501c5080d40f02d40261034940343c030340d82e42e00c908112500340d0280710041040f410081c001348004d40783c13200c0c115800c54024108585040308540104020300c02d10340060780110306001c0514184103014510700e5102094511005802000342d500610020212880307910880011100d8213056407050104401401c600088800c64a40b84c840c5507114408103503900c10400942100300398003406102c00b1032941851ba000b5040c0c4000c03004c04a802900100c80c191140454151850f0704202c56101f14420f441c003a030550440d0fa8180300f042c13102c05c0d00060060305440c0c4c0500038001e920303070040010f1708499490b0510b1055541c0c0c0c0b40151a00317005088040042c1e00000d0100d0080300c048913a030030518800107009208038801c1341c003c0da54407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458720593 1250 458719343 458719397
    0x509010b010e0108040c1d04030905040b060327010e0a051006050907142703370203100f021306020a02030a0327060f031401030206030105091b0d0903 66
    0x4104112552102c641c803484015502a214950b403400701c5880314295061400641ca02072640555141844141504000e2820003800121410710090706031202252185c0400b84ca041960074851001501010003000718602a0501034000c00101c029100280c0e41d96a1101c000e0740ca0740140010314034285441d000f6002a200c01800e55072042d11450b0781100c03038201055407020303041814000c038601e440144000c1e60518240e000c0300c4e900e18600b44105414200e14201170342600301c5880109540d000e0486e408194440c1240300100c01000d035001003030905032074440300d411032807826500c08101031840e03010340b001d07440c0b5111000e036a544072003040e40e03201c0003600301952651210042d440020f106050010042c2c6030664001000010f607201013001c0805500300b50080740b104000000160744c1413060403600f070a10b40c5048050352440e00030502e1480180612800b404600001410820340c070520701c440300c0d01280710a07a036030400c1c5410800070900d0000844c0001d0341c03c03c15011038540ca004c82422 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458721843 1250 458720593 458720597
    0x10506040e090a0c060c0209070513090e01090206070804080c0904200a080a030f0f0203070f0f08091203040617042003071508010e0106050705030f03070504050a09020a030509010b01 80
    0x303424201401601c07118002410141c1c1481a00c80700310020303a4000c48280240421b0716080c0d0b00c1001803041003001e010080c504402c200e814000b40306030070f0810514004903280f000b40050b0352580e18800d240944061240a5080480022071800b0001c0150042040314a604150745d4000c5420003005502ca80c02e98025008680701824007a03c200c0f07094a07a11144002001c86500d10364404545080c00c0d0b9101c1c0075804210740c910100c0c0c405030400c080c1c4d80008080e20242d881e0034002d42d500303844012445000341185018113080e100301b00a030002c5600940d001000105030900c10306010f40e0340d50290003a8800242400b901030300820318200e2003405030398850036403441e2030800948034810030b080f074038480d42c148210000000c4401c584510204c0c1e104440d079541c501c66042601d00503004206900260420904012103408070340c0210070390f00d030380d654840c0341e680d240c40790003080340c01d801140c1107180e100e00294070000301c0ca1a80ea00500b00c00e40541c90070f00c99a500d8807507450807542c0304040140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458723093 1250 458721843 458721847
    0x100f0216060203130911030a240b09011205160c080d0204031b060f05071506090203090a061a061e07080d020c011d07090b031c021e070b1903201c0203010506 69
    0xc4401680c0c10049c1c445803030318a500e410321508050b0701d80d4481503030710180b800a4001650701d1107581c8034241ca000250305030000d00c41070824850040c00c400c003412880d0100b200e05d1b24001e0402c007500b000c07102a08082c82080d0744071170712420410b5001c0c030a40c400000d18030b5003841c0020a82d028a608240c0282241c490340c0c00c05049407202c2c0365001394281d081e20040d94520300031403400344510295019844000c0201900500c51600004580e403000041200c0c8221810141a50f95040c1c11541c01c0d03007404020201d4100030240b82d003401d0181c604c0090420b100810119060166a40a4014210b40d14002d0008c1000c0c204010350a020340d042d604001e40180400b0b0050344150341220340d6140001c1d00703c0e040d0103802071184001590034004c45006806c001020115085144004441c02c0c482c039000d000c2c0c0601c4d10b1003202a6220311401c0e07030b1070918180112a0130038041e6210070781d01c0010580100b034a954031042140c05620400060315143c2e8444100e40b03412450b0302c281c905a440280410b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458724343 1250 458723093 458723101
    0xa02061006120b030f010504080309010e0105270a0b0412090501030e0705011427090601020d05030f040812070801090f091104090f050a0b0a1a100f021606020313091103 74
    0x14050100b01c0003e503010720501c1003140c0081806d03c44c1c0e5104e1401200b1454590502c07020395425030b100103200411301e0b810300b024404003040d004104100c5001c105c922407404040c60092600300100c0d02e0000e00201241c0040005105901f10030320700d101115a5903060864890005500315200d0381422070a940c044802400703254094080c0c0b8a411000c02081420051035040c000d07100300d0303121201541041d409081445504100e02c9103900302d01c0034001b5007401042a44000e200e4003000305010000b00480c8045024800390600320340b4100300c043e809544c0f40ca413401d409403410600703200315500c0c1460304102e510f00320060f20403907111035031082c665519076585c00c040001900c40e03150140d900e100c0040c0e050b00001c0c82044035001c214420f07a8440701601c1c014068400301d54000c1e5215007155a16040701c2c02c15950200900c18200380c60812003504402030b40c0483c81c1514814020009600c0040003042e03441e000030281c8515813410149460603500c2c2c02c104008d0b51a40310441030419810700101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458725593 1250 458724343 458724377
    0x1d040210030f0606030b0406150c0807062306150f04030615051914040504020607030507170301080c0f270c070506040602041715011202130e030a02061006 68
    0x810440c6129141c00701c2c055990881c0715084030515803018011955814800045050901034100109800d001c10380c80150321240c0a04500c00c000c100401c52000000c0410400c0f400c2d60180c02c1e03440300c10f074001149080000c249550100180c6140f442002c8590001440c00041401c86845800d0b8004160034a480c5580300000342c4061444200d860500c01070109150f180d81c000c89004412200501a4261425004c10110038004140c4c42c0164104070411015803140740481b40c24913407502d80240e1750030741d9060000c144c507681c0c2214600d078040003000203118a4000f0300c1c03000c0d90408403280840031011000304070f900e9000d101500b004c0442c1c94000d0420503000740d9200c1c0d1110a40b6110362070000659074044c00e2000031501165503941c003007010f125041064140c4e000c4020b40a006001040e41d40a0070201d110052107a01c401090796080d110440d2030b90b54000c020a0310b4800705000202d00107203507980320b402915601c2c005119032000241130f1920342a2034001c90b5107546440440803c00701039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458726843 1250 458725593 458725609
    0x50f09120f0a0309050604051c0504080c1c060e100e0c03070e040f05060c030f0601020d170a021c020417210d060e070915050f030f0405120c06040303061d0402 70
    0xb1400900da031300d00201000c14800d00c05944502e200704054601c01e88007600c881d000740da880841004000303042c001032000c0722000402c0c843e0b4200494a03554001c00c092441400300d1003030381c0020b001d0303030400d20440e031000e5002a00701d071a180c403c042404201d403d0300e80180d0341c2c0c1150b400c00b94954445ca4040003d940000c9250b500540104803000c0b101d80c0d162503052401905940109060b2000000c100030340550aa0064102d00240301034032414848030340060900950346140040c01540001023101c00c002541180c005155040e1807046503144410244020f412901c214584a5500c030004000403c2c01700c0d044801c01c816000d000300001801c4241c0310160010100903c0306540c0e0b04020445400c81d28080d4450b029540d81c00500b44c5c10240034011305010000420144101406907000702e0b092041502c0d400320304142c00401580d0749080c0b0a203000d44c60303078007248607160008007080141c0c8045a42c41c4106c0c041c1e02d0600003207940f8802082c020440d941070260710108a004600140f6210322 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458728093 1250 458726843 458726857
    0xa02091608010b09010e0303160c0f030b0a111605030c0d0801080706080604090b01030b06012c01050c120309070e100f09020a030603050706090321020c060f040b030703050f09120f 79
    0xd1b003c07104010502c08685590302000c5042d000d50511480c0301d003004a11408403014288071103141d4444c501d55035900001c400050300014030161916480d0000f44074071410748040503503110081c44a004181022070b00c076230090815000340d010750242030500074040c0048504032078401c0c000300010740c5000400c80300e54002500555001d61510307140340108010b900b86074088d60190101c0e040608108d400584401958280d4a100d89090040001c1c504a121004503100c1800e08005981d0f00c0c258685504000510400340100e403030100501a1f0309030006142c83c1a00c111054011481d106c00e0281c11403441644075084030b80d0b4001d41c051180ea0000d4018003818a0340d0308000c91060317100e585150408420742c0222001a10b81c020410500002307140f5000030100951300c55090405440c8001e440e03011020358140034100000344d019031402c501341200c00800c4c103104216101c0c20000c0c030090141009950403e042001030ac08504041c1011403c5001d0380504d00740f2a1603c0c66508241039240c000c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458729343 1250 458728093 458728097
    0x4020f09100902030a020a030b0102010b100e0105040801150501120b060f2107030e0d050c0a1b080105010e040c0e060f01080a06050a0305010504121806081510020a02091608010b0901 80
    0x107100001e8211680c00554001ca0411801684070440c0310001022186819013490440e03040c249a9007864407501d1482140c1c0105180c50a032240d40300740103980d81e1040b80e01240c039640c60100804e017841e81442d071043c25207509985062a034100c8a0024054481d4840401c0d41f008003001040ca201010000403c5003201e804001281c002c01d02a00009101007203d541c804203403140085640c00f44144544400c01e01c990a00c0f509088840204943e035065840740100310180101d00242020f0180f02040d000305580b0009114540e11a0302030320650409480403254500403180200740e0350050341e8003a10034100034108021241042d0b004403014000a00061000d42d0b444c240800c2c1600c1c0c01802c200514002c0b00007107081e0415140484850f080c41e42600b00304003191440000003442105c0110803201c280c40c1158440d102c01103d114260034806a40394408800080080000d40218045203028000c41d03199010b03540b510740b5030320301220410300c0c4400219076400621110b842c542c090300e0104018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458730593 1250 458729343 458729371
    0x40315050a06030206130e130b040b041e1a06060406080610031806090c090b09130312090f0b0714070212150c070b09070e040f05010e03041e050904020f09 68
    0x61340200f04180d019554845900d4403424081c00305560310100d6981001c81c814040c4c0510030309480d805441100030388001c20322041302021a09012402181c070038988001c03080310400002602c0c20294900d070350503aa12804480700009041c0e132400c501030798115089074841414070b56580f010441c816043c10070240034190344e844ca81802d903106000440c40ba07489008002034410550078849c51048555110748011410070140858a1304e9001c4a0354001c3c00c0c0d8072a0400140b554901a600e01103251420703062607140a510303609012900d10310b4920b1a008158980c8981c0b2001030884403005030040d01e00a110041107038a00604001e6060348403200c244042e120100c6598a0096006038180c4005252a40c0403075203900348640081743c2034000c581d500080c40e40c20310f8503d00c01c0003000e0061000d0b082e200301020300342c18441d082d00100c10070003407881902d82c0c483e1901e48892035104074a42c107a9900d662090080b07914144042c81a00a68000340344035038460880040041c07966008041141035081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458731843 1250 458730593 458730599
    0x3020f0d0c090b1e060412140a060b101701060c03021f0516030e0c0904050309090f09010b040608060a020a02031608090108130b01051002070e0a0e12040315050a06 72
    0x40107949019007514480401c1460b106410004000c2200003001c0720001c089840f8001944d5010072101151004002c80004d000303241094400c41c06040d010700f0460103495440300401c00304d64003081398258100c404c84121400050219443c0114080701c04d03644000100500c080380c0038003007100070984640704540030784540310780100754034520304d4010b00002d07151014000d001c00105000003131060f6503c0c1c104241340544008540da030301810201d034021036041c4040341c103010040c003c881f255a00603121140602b4410210080680211a243c4455180c080304071a503240c64002d4004a0321454000c0a054940c10300520007907120885003010f620040049512910359241029821802064160b440d03c4d078810024080403001898455150b5800200f030b4000346c41d1000075415035005640003000c601c0f03540c409902c0d020563708560011030746042000179075007458019004000ca4102a00d20710003121140d07440a014a0100401e103014084885110700103e603c03055014000c0000070881d030796 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458733093 1250 458731843 458731853
    0x509090703020f0904060e071403090d031e05090a0c0b0c030d0507030b0306040c090c051216021603060902152a0a440403030503040203010f0213080c010c02090103020f0d 75
    0x806075007d1250655004100000c0c56001041000a10500c580d046d10794648160305c2034882c8102502c940616984040c200c0d01031007074490501c8131031021801048a4180904090360340e11122600329180c0d44042c60101e030341890907064404102c140c000650800700c80341107100c041c1c10b000340000101503a4825661880d50204011801140141102c24215042407202021b50b8000d00d400c50600100700f2002c200000007008165120494468000b6a454203003c2203044c00c00e10388444a04c42e90b2168084107118844d0310107880244200e408122118041034111175600aa100c40400c1074802c104040030808400b500c0d20070852001d0540711541d076261f59001c40f0072014415030b9401c600740701c040c844825110012100350070640e000302008510310048050b540c8524040202040408004030381152025080800e01c1f117083c0c0e80a40d15000c0410036250361002612584040d40b0800d041d1032001d5002da00881420364001d01002040d030300355024403078102403001002d9040501c800340f03400411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458734343 1250 458733093 458733101
    0x2030c220801050f04030f0503100e010906050a0e130f15020f09010e0409050606100909050103050a1205130b0732070506030112030807050c070b04150509090703020f0904 75
    0x314569503403514030303400c201e0311508680005002e0044190700000f8000400e401c045441e00802c0d6520f803840c0e0320703690710605c00c55054481d0301041152032810000300d0044415003180007a924180d4801c0b441940d56820900405001c1c0c445504c58094091200040b503002200802c5090007605003d1000000d01942000ca82c0103100c450107400011030031680039a400407070000e446070b04990500c0b00f810035480c6c03a9128400036141a02c112140311441c0c00031405202084000d00c2d01150030019586c0d80d00300382c0e8403821107440403102c0180c100e050009641c026815174400c4092000240710300350600c02c2d0190590300c0114181c1c1c4c0381510b44030a01d08529100080580310105000e001c000100080d1031900e4842e0581129101e00c00034401401400c9540100e01d00d041e40600d0a0805070700e64202c295010721800c06422002c0c0038010010401c542108024070458440007101c02d1009003041d01101c40b802210710803548030054201040180d0703c0b07a005004144600901140f8001c81600090211 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458735593 1250 458734343 458734387
    0x40308100506071205030a0e060c0304060501320402040503010c090306060f080604021912030503010e0c0a2001061707030c0501020c01050703110312090c09070201110a0302030c 78
    0x241205080046010242129000800080c1d03115401c1c5070555950000e42d40c5542c900b03404009011000035500e28081d04034000140b50541039445604001e891400729500480e816240303207060400004100d0380560551840096600030384501039403801c1070b03094521907020070382e03440341e0240000b046694081c8603801c00c9290725291102e0301840c40c41c0040545802e54404114a9190b16041116660101300b160303200c0da048a0940e410051031b0b003c900c5403020350700041d07a4080021108410160800011070523a8040310001c04250b44011454a2900c903814910b00052003c1c8940001041c11107010384c8408480400414120703100c1c000390700001c02c2c641040185a01c50780c002c106201c0e803d4030b600003074102803011b8840c001211001a0480c410780e40c0060421141e420030715038040c1d0a00903281100c0b0a007144201c1d42c00d04a5205540d111080301c0c85200740d8080f00400c0d04140140704490411040310780075400e0020400c400d1f00250802400c0807007400080201d052040c024100252003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458736843 1250 458735593 458735597
    0x1021c0209040c05030606040303030b13140702190c0306150512010c03060504230a020d050c22050a060e0607020d03170c0906070b042a05030c010914040908120403 72
    0x40754a15000c000550341c0c10220f00341444010010f21000781c99040403201900e4143c140410503020600209203040c51000e00c414090b8230349504092495201c2440a000e164507a00310b0f0341c001485400c2400603035102000603c195080c00d01040051850f8005031501d0003c450800c0a00341c0d40c00104130b45c1d41c1c502c440c12045035076400710001c0080d003522660780075200903a4204141c5800080700030040b5044803a05900d10b0702000058442c2400707404540a84044880c18060750901414030035168105005940e208012110000040c2c49114545401c40c0c07002842c110b000c1d8517005041e2030005020601d2500030804201c24005600c852160407210f500c0303a42d071944107481012000d109103801401c0d611120340700b000f90b8512503440800751130344140c21400d070a040307448915106c802c0c080c607000c00e40d0350011b8206180260502d5845030504581064083e01d0481d844a0011291103c4d607009480403c0159180c80040d42400e92204010500c5841c9080c60222401c4507a07044400455003100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458738093 1250 458736843 458736847
    0x8010504050601050d1103190e03040512100f09120302120402100c0b0103050601060f090303270302040e010e010c02150f060111030409060f0f03021f1e09090e030304200301021c02 79
    0x2240541142340f13241401c4c0e4401c11905030880360040d00c0b48920f1154501c00d4054030f2120b60a02814801000181054042006038440c54142000036100b050750030307504101ca90000c1c0e6038103800383c0203e5503015501900c094070350303a0303d50801034101d4080e450344003044100f4100300c0005201d10601c9000c0c1d07000d1802450250714100c801000509241407a804210202d0303820000241c00500a1296409034641c1d4540c0310040d0a443c0c1c5000c0302540088d50050401e00d106030861019881900d00404000007481556002c5e541640e641d40d00b04002d0030345c0b00c0701c1c800044600300340a004c95005141450700849440b00038030b0303452442c3c1064000581d4242ea400c410001e1504500b52440141001c00605c0c501903c0c41c1c001030025800c00e40c08a0b1714030a6120a82c0c0c1305440f0318001c5400003100c0c001f15012801e04540109644514000c00580301d240040c6050240c0303000040d244076a90010940c0c841c0000b200c8170b291080c1801e071a09070950740901156514225418581803041d50b0014010b07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458739343 1250 458738093 458738101
    0x20d06111615050105040902060412170a0309030305090d0c02120a140d02061006080c030a09140a020a0e092a130b190b0a030b030c0a15140a08010504050601050d1103 73
    0x4460f41a40050301c15803610300701c02c0058440205460031900c06980c40e070010f4a1034201407800c24241e107010b84000900282c010b910f00c1c0c240d031003102c0060080c1e40400c20381c0d8902d801142d0b0350b60740308107a0001c1544604202d00601c2e104140c1e00c01e40580c0c209982c1858600e59419203a0340540d003426040b03400201034001000e6040060b41d0340800f490b5800c4041c42d00e401c001801d2a800584510018100040020840e0310541c01008138290301007105603028484070040c0da20381c0d10104040303200f04101440001e6504503001550702070060706021b0200c022003480d4082d82103c0380e1400240c0503242404060081d80d889010904607000d0302401300e02407184204001e11042000c0008601400c1100184940c0c40d5400036a803091b00581800903c1441c080002480e06040c20556540003800f09804107090340301e020500798004d059180d0b08407800440300702003000d002d508000400603038504010020342c680703900000c2e00844103040c80b600d056400f0468806aa00800b0f814465941c004148 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458740593 1250 458739343 458739383
    0xf040302090714070b0601030b150307090503010b06220f0b07140105042607050a0501021b150609040f050307060605033a0512100303030c050304020d061116 69
    0x840d0b4828510b103808192050609a42d4000d401001005030200c10104006030845e4060345c4010104c03800100245c00048200c580d1021039031040782c0100000f4008400003030503040500035a0180e4500400403810a444410850001c152032403000ba03000306c0c00800040d01ca607251350040050944000c002d60b0b9541c0340d00349080004580103014526030301d48001c104c08500c0148036a403901200b000700c084030b03d03003004c3e948205000d03084014210340200141502080700540c000d08410314115076100c054646226040e4449400d0041e1030540c0490800080d0f103441d090301c0c010340c402e2003910508031070315450700c955207035800025085808907500e100034801c81ca010480010905d01510305522f010b41008906800051400d01c45e025125154400b010f500b4042c605541c900c40820407522640c2c5014980035420340c44e03620090700403910700500708501520a0048a201c0c81c0c000d0008031401841d85d031403a000b0520049032581e800e0050200b990080d00c44008401050f000300c00304400d480303000c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458741843 1250 458740593 458740609
    0x60605060d061a181306080d0203030411090105031b06191112090d030516021020010504120c05070302100e130903090b0f0c07061e031509091104020f040302 69
    0x2042d9141014015105148081c100c02c0b01803041c29120944000000c1790b0b000c0c050021500015014002d0f0402c02e01c00590010140d407155000c4c068000c001200b400034442c3d5900280030391501900041480d00500850003406010504050409450003410242d0602e0314542c116414000443c0200e01c808944400c21040440c0000780c0d03005450550510b000030f102d001822401018030601141c510440c1c03440c00300c00800540c001e000940c0e010884900117200341c035a0346084e03101000310300300c80454880c14491948034541c8203100002c51031019038156000e040380203003105c452184100200043c1c4130005040c0030601e4a03221400810341401c200454039440610b40c5981501d03040f003010100382e00c1007120b0111841000c9440c1c0d18642d41104404510482190044034460250700268103035002c0741d42892245004034400085144040c1182550034501140340b164020710802c1c048803030b03a58483c0c0b01491255140318401000c40c8007003016a08000f410140c96240854108107600341188 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458743093 1250 458741843 458741879
    0x50c0a0231050601120905010b0409060c0210090f0201142703120712200d081e131202071d01090e0d05120c090d0b1f0819060605060d06 60
    0x110034042c600e0aa400282100c590300d104141094489481c0414041c00b0b5114443e80c04001d001402a440c450600d003002c2c0c0055400c4d0b1006108800400c04641150312550601640c444401d10103216542c00444407600044102e100e00807007000507124441c0140f100da43d24026a07800c0c000790f101c4132000c15042101c12829201c1c561010032118000680713035a503c0403404100d040c00c0541c451500101069040c9454401129107d6421070140c1541c00402071403083c045928441c600300303014405056a0402503617020704440085c150a400119100c4000160007054811149010350b00d16070070003d1441688403890040e124030040c04510564081d0015001156004203104080c0c800020040d12460044804203100700012800843d0504206c071810f0b2001020703401300e4551030070248400301381901d032242c2c5821140d100000002ca07482c9150112804030000e0200401c0c50aa0142c001e540307a24100c0321690303910750205040e500c05014081c040042040043c4441c1802442040924030304 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458744343 1250 458743093 458743189
    0xa1101020c07080d0507081e360f0915040e16050a08010e030307051c0c022d03090103090812040c031214030403051608160203060606120403050c0a02 66
    0x1c250760120b800074003221600818840000c0b0408444010b48c500b070702404811080c83c00407569038100540d0b6a8071101301850000807800015958403040243c0031480400c1580c0040100e00047d03408544c030740342101c0c0424060404146896170007005414281350b80e1a00d02c0140c3c0201081c40b05040014901020f840e4000080200342c009146050356404004c01a0b8104070000512a00d4540c0c1c1c4103181c1c101024080041c00140620b0002039121104403c00c807020f0b9451a08801040f01c42c2c000840d4416442c03800fa500d0721101c00c0044000e0f0102c55401c1d101b07110100082e011480003079003038a00c128040c500d1486040d0031071429845943c6030101c03030703010001002c0384501d4480151040765001541420302d40e640d003103202940e84080300c1c0684050001301c008144050003420074070740c03209550b1084007074442c6961100c0401255000e02d008061681888800060001c1d005030014184100010122040d0641550003c2e00f00094010030101c51010b0051414503a00014210031413800a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458745593 1250 458744343 458744347
    0x405060109030b13060606120f06030b0a11041a0319090506010b030612100501051908030703051c0903030b09090a0b070f09050a0b090a08070315020a1101020c07080d05 74
    0x9080000c01007040340c04058200182d5078081104040c04150350307090390354020b00500c181d5541c1e0001801c03003a2000d038056501401c0c41c00300980c00203207100300c1058a5202c1003039903090312040540c0c40145004031042c078081030200004942480080c0f40781d03906070080c2070380c03650f02e00c2c0906000c20140785240c2803400c40c13030410769508001f038004a041c41c107484840407200d4403642d030980028460015046d45001900500c2ea40003034013440c5030000c40c1a940160b4520005851184070424400b01901c10080c0f160018000a40064802c800030300d001e40c1c400e124050120300f060b003483c080700c00da43c03000c9001c2580d49090316028207141710504e600c120ba0001030000903030035840f074000d0900d000340440200406414044c005a00442c0345902421014007500d864035102d00e480d02e0b042d44044144e610504041c800000c9842d00050141e045d0b03a80410802d684203042c2200c503010b500442c0500d000c2c400a0744c41e401d42e01c1c000b440901400c1c00b891000f02076840c036040c809810408441054000c00c102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458746843 1250 458745593 458745601
    0x2b0e09130b040305120a0e0c10170901110409050a1404051b06130b041703090a120213180204060504050114010c020406050315040b0a021312230708010b0405 69
    0x9059080d1441e0304a0014852581c9500e8100ca440c0708001981d6441c09001092014a840650180b0031201940c0e04a8844101b00403c0004618070031820100054004000c05a259480c04a00f81c001d0700000c000b0030100d40984031800385401607085a203680f03540b182004644203450146003e0b4184c4003601d5032043c1025161141c07500456000600c814082074200e03051629a00c0880748844c200d80480100d540e2102c0405009034858452094442c0f000c05410580d801c000c001c40d220300c10024440c403e254501400365550038810394050360f010038504c44528540d000d078002c8a0b510500280d0010301d0324080d2040000720b40a940005d40201d00e4400184160001c00640f06070161702400c003084805242e20001d4041d01003900041e8042c0281034240c1c0d00303088160b1278640114815601c0c00c007955100b50920049000b00044000f0005512001300071302401610546111806840d05070304a22000d0b00c512015403454200340003640c1701a0040018100030b110351200250116400d20003810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458748093 1250 458746843 458746861
    0x3300403030c08070c09050a0207050c03030301051c15060b04060f02010c0818030d0f05180f030904020d0212010b0c1006140906031507090311010804170901022b0e09 73
    0x2e075520010060900060218103001707070030f41150000d0945a03001e20451a208002d83c000c2d4004441c200c83c64441c000010055242c040305585c16640041c104050f1590000315203c29078a44035826a00c2d24444155007440c106c181c0200310150400c0d04140c0d41d00d5190104c0104420a001c00810469141403500030100f40c1c8040c1e1a500030074a40b030520f13120b0000c03801c403504501c1580000d07001d03907152444019412a0300e4016911a1524841c1c07442203501d1f0b4042562510412004000765403c1084000c0081c0b803c1d038054001444040d1b070041c141450840f035106154000e030000d00580c0c2c0c1c04503443c41d2250040100807500101403209001c80c5160150160103c20040025841012003c002840e140c800700a000720308081c82c2c10340081420106006080144140001e07220700c00c0480ca80c1801e035000350612030045612000410402e00405440a03042e0070076680c4904600420aa0068a10606005d1000017841c481b52003100000b105020381105000b04030f10340165080010440010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458749343 1250 458748093 458748107
    0x1503010e06070f02030904051003110a060203030f0c0d0c020f060c09090c091f05071e02011707030b060a0315090c0c0b09010b06070b06031b0604050f0f0330040303 72
    0x80003d0400c84082441244141d0541c0640140340d50014909010007120221980c0180112406294402400840c4805211940341e03140a03000c0075074820004260860954403803d6481a0080c1c503541c01c2c0300500510000342c911080d10b143c0140d10140044d11000c1062290582240300800c60600d4084190081078a090b0000d020041020b00800c100c101d0392245100f001000c00050003c095501d80980003030304070b4002100656080901c004041040c500c0c2c0203054400c1030b0161910400421941c40212840000074080020140c56800050b2030352150340103424191010b840104284103012600440380e841907200c2c01006061442200280c0d410030801c40301c581d00044e8280155448000090140c2030780807800f5000305002034407009010302e65481500400381142516280c0c0841403900b0410700d821030304541c0c0110200000c00071864098020700058030042c15001504108100007414900c9110b8500c900902178207406860380fa6416445646402c4c080c910340c24103041d500c0c020054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458750593 1250 458749343 458749351
    0x307021002070f3f120f1202070c170d02300c01061212030b0301060b09040c020f0318090f0106021507020a060608160f030b2205030a081503010e06 65
    0x303200c082140c84c0c01c1d051055121003070503650110580a0940c1c0c0310280c036102c1c4900c141616142c0d020100907003800c3c85100168011680f982d0382039000051140c2d40c1d002540541070848910500c2a0700041a42c1c1d02001e114595203030001420b4070051112001e800e02c110094007000c80011007040c40c0303a8180c8050382d8a000d11908440c6030720751090b407600381d0043c062500440c0f1250080c0700003408000c24401c3e115030101e615601400041041401d0500343c030000e0080020f1510300340140c20081c1000d41c020490040280704954021224584990035644000c011038543c54030103100e1251410140500b541080003541880300e10740c54003500a40740c920b54a07005070851004808256170620810090103503d0b004601040300c5959000ca00707030348156078402d2510101c1300c442d00140e03815181038502c0889400c54404082176032001ea4618a4004402c6101c41c030419200c03810700454001c0018001074044c075111407600d8109484040c41c2c845070422514071981c1071228500030782402040003500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458751843 1250 458750593 458750609
    0x8030618091e1e03090103060e092a06280c05060a0207062c010b01020102040302032112010915470d1a0402070507140109050607050307021002070f 65
    0xb0100d4607903141010180640d040c143c0704240980280c9200100041c80c0d0402c0980b0b0801a0541d18005080c114004945090240d088000341c590144039034514252a00500c0d80d99a00040928000503543c3d00442c40d5130b80034000c041c404518006201c0c811403114115403c0007160703140c4c2551b50b290f440340c0040c115151681c01041e0310b400c02280d0b40060108030b044054080094a01c00d0940c8000304040075009465800e1003200d2032554018400c031010b494001d000f5007809a6070070802d80005560042a02d07031940d04118080c074941d00c03613800b0360103420185c1011a5031003213045090040356940d000000c001441207104110341209408450140008840c02090391003800e0110905002ca080b0100720900000f81303c680c826020350041c1c000c180340001040c070100340002808201d01803907400038855403108406014094030480c45404a1405240c02c0030300da62500040741960b00801ca084840340e00125400742145803c2c8030802c40f00c1420720007030450030b180c001050407030350541c4100c0384 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458753093 1250 458751843 458751883
    0x30f030f0412020a030614151507140f06040f140d121e0c0504170a0b221b0e1803090411090d030c0c0b031e0702030c010501030803061809 61
    0x108644400304448001c58020500301f00b000c006075a50703192000c0440d00405030078140108030942c2e01e49802c007000c08280141c01c403420300399560307985504020001030f83d0f100d0f482900800d0f43c9641c02006502d20842c8a010180301000c02494810300e001c000e155000741a030084080d42000070f500c003100a0640c405014007144504000700f80301c5124410f81945c038406030821035840d0f00641c0110003482181e030100090940581d20b0340d040782e2201f521240092422080b4400300764070f02d90003060422080c4114403d04803400156985203000144241c0401d00394101d03540c00c0201001484200ba4410500034140c0b02e04081e050b01d02e80c40c0c1c4075510600e0300c155903032071403032449800c08030913252008005000035051080c02d0501601403010b211088611503180080407031032038500020383e40502400c01c034030100038951540490103110000e08401c114802440704403d1400240034640c001c501480c403c80daa81420420701580880d85403c203c080c401c800c080c031040c0710000a2402c3c401d04020309641d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458754343 1250 458753093 458753129
    0xd02100513240c0315080c0d1128030606090209130f18110906010c03050301050d0f0807110a0501050408070506031f0602010501091406010816050c1b030f030f04 71
    0x40380d0b80c011940250302d42850480c01e201920f0305a070250302541e030401c44040a071070740d0342c90440c4d6804035807070403c1d08040b5610324900042c050300034200c64081d0040c070345240c1101e43d0203138020b1048804621003820240a404100f40f080d648030b0038028040e2100103500e01031024010500b10000555200035181e52420b0085003044564041c1400100da414040e9070780c0414103080c0320440703040310450720906610000c9000c0398012403401e001c240d45616142e045030320341420841a911800c0c4150799120240b000c07000041c001d18001e0180c54461107120040d175120300140010102182c000c00e041c40030070002801240c4002a00c2803c4520840307055603a6580c00c4c04e4000303003c07803c00d445220712045c00740114071550103402450503a40c1008042200760041e0707503010448501500d007140881c0d200c10104000d4045486195803103010b900f404c515110050054514011040150301840d00c190407040d0160b00c0c05001d21942c1c1640e240c01141403240340d0070428440c1c03142c1c1c41000d00c111b070744083c88 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458755593 1250 458754343 458754383
    0x506040633112e0c090e070504030314031b030c0c0106060e06040b0f09030d0c15050412050a141812030415050a020a02090a1a04090c05060d020d0c020d02100513 71
    0xa1944203004001c1403104d1001824064409015806041d04407201a0000340c50076116006450480f5003582e40d5000200200e0395000303145d400070303000c2d0300c0d0f1106c0d52081e003a40c0440c0a0045004262400c80343c1e9503204a01052803c42d4899005042000002d4908030025940c0c802900d0543d40001030940e0713100c02c13031074142c1c0d82441008801501350150741c09003142e854002450900303040c040d100c10318450801c403c2060844000b110f0041252002c0c61226001905c507801410960540342001c10000001a8601c0b0b41a0458544043d40c200440e880c007141e410a461640404464900210700b000c1c100740c0f030403404c100342c0f041d240d00b08180440c054079410b20801100711302d15009081d00426040c0902907001419030801c206018034094020a03905091910400314010307000b070312a90002e4100707401c01c01c1642c008046801241d03000c1c443c07020a80c039180700c6d2009800d415002072403411041307000607041c46600443c1c0904030740781c4401c0103032032034114080300c4005501c0f64002013201c03820310003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458756843 1250 458755593 458755663
    0x20f0f031c17090d140304150905030309070801020708090f0a1e0e25140702180a0b0a0608060609010306090216020f0a0803070204050604063311 64
    0x2078034181d0440c21240030a07040d0848140d1a11091106094105039a200100c0da030b1001e0a803894000030742c1d03206440c2d2104409402a50308a4031843c2981151000c6c0342c0c1040503100c1e03400041d80c0e103400010501005100c2008000c0061a0f5200258207141054407580c826001d400d05181c006d80501010106544c1c884441ca400f405180b050b0541d03666510704140141c00041c090303044903008100114640c0308110a44080380303c0702e5600b0105407024514102c4000d529441ca00e440d810b800d1040c0d00c0140d0760780280740d2098107103414808151426500300010703075400c0c0c50400c1c000d17040740c0700c148480760784140556031084091350b2241c1d0b140f980380012030080420750b2103070b21180e1000c100c0203954208520000c4449000300c5d44882410a600c2c1003020b0882c2d284030751507199004100420050605422540e4801c500410000b051507403010321100030010395003039030702464102d000982c0307644040e981b90f04a031546141c501c0300d54110a010954803428181c005c2c42c3d9000690510401080d0101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458758093 1250 458756843 458756863
    0x10815060409170a0903050106050108090607030b030c031f05060105071203020c030d061401080106050a050d05130507030c36021303021504060206010b0a02120c10090804031b03020f0f03 82
    0x1aa82d90500b12034000c2c440e4030180022907d82d400c004002801d98030804160340501e50180280c041511200300a400801e141c50710150540900c0030300c041c19a03028480355000400d0306590001107094030841030308944008191074103001c001c2c041c00001c40d41c02130071030702c0240481c100147e5440ca41070740d017407640c0540f28035451518103201d000b0410000c1d40d4000308400000ba26000c0041c5d8913250140c0311030142401d1800000d006014001c50400103070412600107807d040d00550a20302e903110541031145c035030001d03100c00008910400c445543c1c1940a00520000c21420840746140c409110b142c41000012036400c3e0f4010030034903172103c9030f407008100450b401001400c2030100307140c0e20380e0321740c102e4032690002d401200d000103040b480700070440d145801d9940c0a130240050880c100d241036006540540c56510030000302c12150400d0740311b0141e1103402941110348070b030301e580380500e015901c1d81d1102151030a8044200010f0311100c42d40101342070300700d4010001e20601c07804285406000c031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458759343 1250 458758093 458758133
    0x20603040807170c100b0303033603120a0b220b100305161d0907120609090c05040c020c011412250206070206040609110303070515010815060409 64
    0x80d00b800d00e10041200820384c0284110503201d000026050240407a48480c44958245c0c00c104001a4030510091074080901c4442d0701000e03080702180e107401e04e6130728100320002d926800020008090313118403a0071503200280340000e005228a14000c909851011440804944c20060401a00c1160350b0040d0007030072006014901ca80d062150020080c1c030b0b06031101048072450361068040580304068003240b00054030802000800003030288820900002e0501041182a503070240c0103880380c1c09030038002d01d206000440c000e8114106000135860650000744034603d00151b4211598001c6200c3c4020502401c089004580e00c10740800c403803084061090028030b201080024a807401007c00c1010f03550129502000012144140d075038003002d80705080540d0100d4002000070309141c102c1680544140c81e81c8218030b038220007007851a003150001b251141c00202c600007202c01d0080443c0d0040c4040b0b40200003840019200c3c0e48403c101610700c0d4020341d2070301385e018107015052907a081030255403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458760593 1250 458759343 458759363
    0x5030f0a0f150e0d030501030c0b0724140103060608100207030e090a0f061d0a02070c03080a0c0b0106020a0314030c040504020c070b0307110f010207020f010e01030e0609011a0a080307020603040807 87
    0x41314000b4020002400101c40449441c0c40c04180d40d600d01040c2c1c1c003d164001101111a00460b0b16035900c54916140c056a0030f4485e4190b000c0401040b030480e0085104010100c0c603581041c82c13540c2400204904088000d00c1481130101003544064400780c2214140e400c60766984401850b10081c1054001d841c00d03590805d0400180d49012048000340200164413841d140d450303640d40750099100d806005010b0950460092001c9040c02006001180c200d0070b0012041802e540c0310002c40100344d10180143e006842c000051540200a0740c00c5c40c000310f86060b180d1b1030040414041030140b4040c00340282d90104002800c1c45041045c0d0300a42440da801a0b182d00d403604c0c00405540400a442826000783d4201c250000c0c0f050003514222603005000c4000e05c48140c004407038444180110a0405449078010720300400c00384886401407504500100d180184148661040741c81400094010070b00200700300700081010058420540d4100c0300c183c0d0300c2d140c0c0d081a07491401500d401030510a01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458761843 1250 458760593 458760613
    0x80910021305090a0e0a020105130306050106051c090209160c150b010212040e0105041a0d080c0f0f120a180603060e0105030c01090b2b050105030f0a0f150e 69
    0x4001c0110040310310449100029603505200c00082d0380b0380c2080c4003440d0740040480070040d80913501608141041c10140c2881543d40e84883c0140d44003a131103031022480004000c513141c0b00c2d465003864561420745060003048810350100d403407890000d0240301400d5500681f00f28461081c1400034105411440d4900013180c40c07424400201003c51101b4050710039480e1000e06062034a003906c080302c00c40d803044031682c0c0c41d02d0f0500003e003c40121000c03461250300102a0140d0722400341e01030280c080c65800c0e0712844480c40c507518142c41d20f09032280c03030b40c031001103d14020400124003030f080200105560f00d480812105a80400444081605202045401103101540755100d5811130741c080b842e0178507a03683c0d501410b031900c03c005d2055000445001003840840c01a400918a203241000d50546028910020074013440c055813015000031b86940c01000349140c01c02100300c007410040040c1c004500325590f544900e9821540c006d00c6880742d851010802c10b15a40800703040300442050302c0e05002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458763093 1250 458761843 458761867
    0xf20031f09060e07020708031c060302040c0804111801051023120c09010c02121903030b09070f0527060a02030a030e03040630060b03010801200304020108091002 71
    0x407030051441666403c4009403a580c4000f0f445011240200003440c545040091719414030381000b40c40307a030b4540e2600746c0000180c4952003401d035000a55034031a007581c01c1c0342c034094807500440d074500380c8901d0600c0400558404c2c0300290504584044a01c2e00407510300c850151412420783d01103201c2c102615610781c1030112100010503501b00d800c040c0540d90b80c0d41106100550140004440c001004c282041005061103646027004101e5201144d0400846003451581450090411000079441e0041c408030350034800c04040d000202814107004900e017401c401000707070091401050100c000310141c0070143e0303580c00f0201845c108c0a000a6501c01c07030300e00c1c040e64a51051840b0000a881c1415000b08a4400300544003916a541c1d910b01c0c0c1614078100110031080740885845401900e42ca000d0804c051341e2003000020080d2401071503c0350b00d44041142120800c07005201602403000f40300d24807e1813041100c0e40640c2c242040125501c07012122460a458100c00c110501d10008140c440c41d030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458764343 1250 458763093 458763101
    0x7110a030b01080c0a0311091801050108011a03060f040305160203031b0c0a060906110106050d0f02130203040b04061a180a0b060f03180a0f0c0302040f20031f09 71
    0x510580c100c0304c0c0e40750f02100780030810000f0300c40030f866a000110103d5082c60f003080403e800080800c03401c50061002c040f0b5901b104c0007030307000d00011780d503407190b8800f0702c0d880c81408181c000044001c0c080c20300c0e04500c009041c0b64007d00080410000103041006601a010004481c58018040b40c0e111310103011280c50b6a400d80074524282d104404e580185403901c0b0228905030b50b0b00399140c00d207441c03401d44103544480011a8040e460b5490301e1004c9400d44503144040400b500444400340d60819900510a609000c0c810802c1064010000c04c00480c95100c059600154400c2001504800012401110003d90000300da4081c0020140601c0164001c00441c0501501d24081100744560b504100c0588030780190300d0350a138401e10004100416030096002200a16815100928040c0d81c58400101186008460041c040c1c041442541058868072801108415041040c140c02c1050b8056000400d8401e49020b540000012890300351105140d40320726040e01d121031143c1e00d07040194058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458765593 1250 458764343 458764349
    0x1703010f050109050603060d140a17030a0615091412010221061c060b180403080f0f090316030516050a1a0609040f21212007110a030b01 60
    0x100043c80204e21490207800316401454024400729080c803856841c00358a0f0304101d5103051a004010302100440c103441201b513002001c843c1000e07070301d15100403440c0460b6100c0d00541c1c1604071000385140170642101e0b2200076030b0018004501c41c81c030780c10001401c42c441900900200d50000c80c040981c05084200722071a13043d85607040c5010707541d40c81403010f4400c88502481085c0c6840f16408007050f116802030028050151500c0058040368003d680060400e8400310001042201040140b0038801c056941001400808034242d040c0350003455964068076591807120043d00080c1001c06004104440703c04008141960a001150424a855a000c540b0070b0f180303401900301c0d079954030302d207503545610401d0000c3c56a5056181d5403220b1100450480045803418030052481d0814a22081e1280144c8640c0e604d80c00401c0816100181025008c2c0760760360380340d041101d445204400d00d104400403901101c90300f602e64074203040012011541120f2241c0203010b01c003000c03007440720010006042e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458766843 1250 458765593 458765597
    0x619020f04091b020f0c01050c03120f040507050406061403090c03070923060916051e0406031d0d110c100e0a0b030606030a05061210200f0f071703010f0501 69
    0x20f0300382c480580c1c40c2d01d0000c915150307907003140184c042150f020300042d280010310b6104403800c0c0251000304103000e01050701c0c402c580e40c04402c104410004108001d602414003550148070840c60180051728280b6510340b640f40684010000920303102041100c5030741c4010003012258140d0b40c580c11040201100c0c108207400a01035441c0030303400d508200045014040140030700780a90f4032041090311031803070000c01c0010031404110301e0184500241d0115988182441559505d5151000203011907178a030b01e4555002c448501800311030781002c1488002c05559043c881900c07200c4200050504c1281d04806610251014400c0c0c02a40d0183d080240c00109072448210325031103014242d114001101e000da400300c004c000050301112541c05c46500a50090001007054002c01c90b10f032b06200702c0204802c40d075a562803c10417070103925211602d0b503050310080c062515144031040c0c00c292207003407403221055a00290f018200710701c5203440d01d41502c2488940780c0b696100c6141c00040d4080f40305580c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458768093 1250 458766843 458766881
    0x30a050a120f020606060a050703090807032913080c0106050a08010f06050a0f150509043602130903020703020a03110405100b0702010e061b0106030b180619020f0409 73
    0x802e40d4000210240900300050103607083c03850488040f18581d000100c22010010385001c000785a04c01042444060351203580100039420031031a0074802d4000d4940354254001094085c0030203a1401044511480d41052401d5a01c8030204941400741c01203a200d203820920580c400900da0106500190850001c0e02c01840481e94400411440110038024074040201c480f0041203d8560416102c44040a500b000d50601c0c0b010300001d8126058103a425140081a903990000c400880b4004103000000e051843e070b80c40e140390082518041a901d0400107196501c410405145c0200400b1000350741c0100701000303d80d16882c060b10f142c811806924092821f00c8042440c015102d81c1c18415981ca19441c4c6013007800035001162840713621480242c0000c004c001f06000f03002d4510200560320b40c640c2c0049080c518501c0d040c400813a0003005044442140151480d4035180420402d8005103001945100e0060707440a0500030b11420740c091400050004000070501c200b034018440c10014840080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458769343 1250 458768093 458768117
    0x80907060f140325050d0605033909130c050d08030730060612140103030c240606020f160501030e0304090614190b18030a050a12 57
    0x522540c41c00140180441c1c80c0030791102c010703800c60015540c40020b07010510210b100d02050f03450484140c007003000c000f60b800a4130a0039901d0354005c08008020981c018050a00d400909545108030359012590f6000100c440404502d800a01135024850041c82c0c4c400504280e4071140d8282910f100848032021001e60000d564901402c01c0d098550f003100110f031841d614600221000620350140d607015545420921918a4040102001e071020007a000200c00c0d04120340503100070415006000201c1c14050385100c5101032210650440c0c1c1d0505206d201801e0a1801c04940c41c044110703c200c802c04040540801b20380d07500014121000d80d001e80b0b150b400a802c1d0b0503200c1b14461840348500c0701490003002154030030b502440308001c40c0410f8074103142c2c41c0e400380419104142c3c001e000003280c00c81ca4482601d0078900e510303180f03842841c0e41041c00749040c42c03500850048118150001c601e08400f8400c51310184044442c40d0762240555a04400700d01d00840b0540480c103020001a005040c16 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458770593 1250 458769343 458769347
    0xf03060a02091905210a0c03050601080c0604050f04050c0f030a02042321030705010f0f1b120b0d020301090b0106021209011b05011103010806070219020f0915030d08090706 76
    0x20f20560710081c0003203200c0184080c030b4081e85541c85481024030303c80e14044801068858138294040d40c481d0024140f0fa5150050240c80c2c0324030306000501c10803041100700071a0b960380800c50045c207000d89001c43c880c1d9034034460547c1401142001c44aa240000070000207101d5a03004000341d0b40e05080f000182c0d031181d481440704420441546800c10499a40f6000710b000c54100d0f8420807007004216858102c540c0d41d0f071820748062280c10a01c00d0307101c03042406029054040ea90751803e9540350f04a062110500007060b00000031b5030440f01654880070802c20703440e107013038a030340481d0081c000307001022051414250300d00003403080d20014011000341d0007035801d00c0d20865802003030507034440c00800410308030b011580b80040d5040710720350743c0c074036001c85120309010285000b82210000340c082464440000b034101070042a080c0700c541c001043d80c80060346e9204210310001c2d4151220f115940e0b440140d00300c850302c103800c0d036545480360040c50a00c05900c403441621510300c0e50103641080e03a4402003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458771843 1250 458770593 458770639
    0xf180e1203331305061203160605060d050304060f0c08040303050703090b03090a2d0b0106140322050114090a3804081611040c18060e0f03060a0209 65
    0x90b83c40548038009840b01221500843e4000c0c40041201450280301c1c00700358515400108804095100c4203050703000e01c01c051142a900035800d40b50050a925503507500c980381e108500400081c4000452680c0000d44034101030b0607a503901c4011107580326200d003030140032a0000031007200000c2d604a0041030f0807410b0b1066070b000c2c00082004098810042c7d4564003200a038031b0f0710384040f24141042202100358840c1000b0482c6c09448203005950500c03000070709034660382c410b1540b0318008005000c0fa00350001200d6411b01942c1007008241c001c0303403030014050b0400c98044403031080000240700706001c000c9200c503001e52007502c0b501d90880001c95811800725940d01d05031240718001154500481440740303059801841183c1c1d10b480d2807000c0001c4030b402c004800c01a02c003c400211440c680d81424882d201000d4a00d041c206074a41d91110400341112150103140100f01e0280c16003030b01912842c050141415004050303c1c0d461800e01d03141e41c000e40050000a201c0e4001c542c0107019140c800b61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458773093 1250 458771843 458771941
    0x180f05040f02310819262b0f0608100908030a091110050c0c0111030f0306150301030507031502070507030206090105251b0305062202030105070c0501060f180e1203 72
    0x880f880c10040040c6034050a01070700601009401f10307001200d09440361a00c100003141d00c100e100050018284646180b90008002c1c06801c0701d407030411190049103501c0f0513240c1c01440c2860104040500e0300c0d04a05110401c0f00c05604043d14206008030260071001400104030b030902214222070b50000110782c0404103070090b1000350002c010701c0e155080090010355224030007404890854a508400081551007640241c80c0d80d00701c41c40c00d0080006401003138442c204d81413000d45c1009010307280d840c1c884909100081c85013000048100782c44c2d000318160780481d0210703a0a180581c54511421300c145001020880300780359002d000c05081a06c82c80900f0940341c124000301020b660341c0c1410031030300700c85c820804144c10610280d200160350034010b440c814030095407a45510321315454014256505a00002c01480e07091000740501c24003a188445d5000300680301044040c040d26006d0300f854094119400078805c004100600340c0c8884480d42c0a21303003d240c2c01052035461a40072100007501603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458774343 1250 458773093 458773163
    0x604090e300304140703020d050102071106040305060613110c010b03210f0306030106182f07020402070204090b090f0d03110910180f05040f02310819 66
    0x400440d02081024040801544078072007101c50b401e461f600040e541284404044600d07a400064290070032884c04240000c054041c0c030f40b6400c15086550710380c0c1384d42c03000b0030050003080c4040c19030160b0003140e0080802c000b103800a1070b0307540c0292805940603141d90f501d00d902910400300550407080c248400000c10a9098802074104079a001081c3c01c2d0f40d10150525505640f1130b000420404034280c41b410740c0400c00c150000c0d041c0da440c50703001d0018030f01d100c000d900503621200010781a0401c50803255000d17811203005a441c00030b480090300400702444007400741d0905008014244000140b409034150403402144c01d00c0c12042c00450640b0624078100b0b240d400280400c4100c0c0c05c101700e417201d40ca81d50b1f00b07124040b04607851078044010020792260b05665245881040141494894400c50711a01c020940c0b82136400c1050b4184203500a0a01481c602c8900d4078440d990701c802000d4000d030640000340c0c1c9a52a0b139040085c000c2e01d803042c041e00e401e00c100101401c076a444a500c0b501000c501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458775593 1250 458774343 458774347
    0x90a09060b09161409040c0f030b010e1f030204080609060103020315040515060111011401150903020607020123070501090b0f090705131103040501020d06080321060604090e30 77
    0x20040840303403002140400c4001c1300c0d041c010301180e40d40d42d002c0c403040c40d4540e43c0c2d49821030529100c01425240712040c2c45040c800806406003e40d01d603030110705109403041c01a584051517400d0210001e00c40c03076000d01007078002c10040c000020000301310710b8120fa000728101e42c1e08a2071100d60540111b8251030080969200724512503404a80c3c0d03c03a1a40400c0c141000000103001000845c25107010112101070b54900500501c03001d00702e201c507440c102c150307480d25401030f80c1182e020800302e10034108027905110b0043c0d181c00c0240d100c000c90030f01a500c10424682c6803100d80c03a0190190a840ca0300300c801140300000502265910407807148990311030320050261910341814006540384440c5401c0020b500c84120800071030241c0000d601481c410301c0010fa80e811a440000f08485840c1c20101094200304002401c106000e00c80000342c01520101c1c01c41da0300c50200045080c4180d5204001c05410300042088181001c81c404130343c2d071203100ca048104c5c2c45500116920288071401c89950442c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458776843 1250 458775593 458775631
    0xc010f06170a0210110312100914010918140c0a0b0903210408070803090a060509060d0c0909060909060c09050d0807050114010b130501050702010906080a060302090a09060b09 77
    0x15a4448045000d400e200f08a02843c40b4924110b5204000c503003650b000000034008d02c14440700d898001440c5001c0c1c1080092804078600b80104818450122405c2d02d5103200c407040300c00032b82201789299010400c010404202c403a080d8030b818200e65034034031070502c0c9030001a43e404600101d130001d00c00140540540070003c1d201c80e0401a201c2d42840460320140001304443d40200204005009014015038441e0242000c11a0200c0b45030030050030410280070340f414a450b46010784241590082000c42c45180b1000c01712244e940035844640c1e198200b590005203420545d104c0c001650080c801400000301690302901c0401c824884d5a4200241030081408078034030501420a10344582c001240e00e0603600b030100010790081c0c1110001400c00118040d25000d000306903002006c2c01c1c01c03c1c0742081210f4001804251180c41000c00340300b45500002c011108542c442c101030741d8010b02c100158282001a0300040020604c101c81c040d20300040300c11140740c1403c94a00c62124060304190f5007070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458778093 1250 458776843 458776849
    0x60603070309020a12140706090b031905070c0210093012080f090d0507060c0201150803040501121a0609060c0109030e0f0904030906030c050f0c010f06170a02 70
    0x20008080030109640c92030a0001a9901005000140b07088250400058034600301101c4110368005108100d50040c14200502070300418500d0840d110b100c0a41d0322179540500035085003d6108500e800302e0300d04000c001c0041d03080000c800e10940240c40400020f4200d242c01e40d100390290241c0c00c542e000c05800359440120484401081e069408a103440e481015a00c4400708000b80801c20f010071401c00c00c01504c4d40280401592051075400107007402051282c002d8054072408a0240c00342d600c0318140e002c1c3e80d000f504440c510485280055900503521003941c1c0d1650000d026490001c0e040001003d102d40c0240141c1e0440800446002000c00c826070400c501c039030000140c182c00c50710505c0740d920303413500030310980c440b43c0c0c000d40350044001051030030050180211440700f031195000c003007880003113540701d4180750a44071142000071701c003028820103480900a0000b4100c00400010340384a515030103401c440704400c013841040c484103031a4180c0641c1700300c10014505456100200d00e8000d46 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458779343 1250 458778093 458778097
    0x203040507230d05070306180b070f0512090d02070602010b060313170a1206090903080f07030e160311010f230906180102060c090307030212100c0f020c0a0308030606 73
    0xb24000c0300d039407954000d101044510802540665044c0c0012004200740540d500905104203030040001046050660310b0591307540014100c2d10412650110412615018000726a010b0640705c0c9403904c24688a00c0080d616003070340110302c0c01402803040c005041030050192800701440240041d0035075550140c03a0009400c0c02d00c05656221840904210304c000000050040c48140d94600d0015042d6000390001d99040d94401d0082c1441c0c80428804680d2100003150481d560422840140d104d25074210b000e014000320040035800303444d03110000c01401200201c01c6900c83c040c8110000480304c01034a8403501d11900e040803400b00344040e0603680b805415200007281011f082070a11b00311001040c1c1c681c001d480d4a882c020b280040460803503070104652540200803e62240c078010034100402e483e40c40d5840028050403080c0411440014207010552900f6450442000007811030100148a80084c40440340903004011040600741840e10716902525048283d03180355883d15130600c0302e1a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458780593 1250 458779343 458779379
    0x41a01020a032717190221100203090a11240a03020d092301051005150c0105160f050703050711040207050a060c121b0c05030d0c0216090203040507 65
    0x9070501c00604182e020a111040303004d0f1100c4c1d60003400001100c81018900b040c5d01d00c082c1d80900301c401251005943c1c80c0c18081c03c001030110005000c1c0108581603150120070440c01403982d002200f001001207002444010311805080c0501802ca02003042c81a040c1c441c6400724800380034240300052852080300240503920712840c0c01403400c070458454500321090040b088405240e82c0c1d0301c000b01039800c52040481010004e0023000507040c15114182880c0309440707032501481109400694440c0c0e49401e8407a485040c400900461924540094ac12588102006c0101d40c020340049811031013079042d202d02c41e5041e20343c1c2e40741403082e88031a0710715135038020300301d43c031a40801c03e2600203201071081800d143d00c034035004038140285a80260001003000f80365001d4624154403041441c0292800310810461400e240c0515002801d01c01e0440c4a200310095032582845071400b0140d0303000034000706040b00d40f00070500702e580f03a00348901684810b890142050307001c01010300541b2070741c202d08190 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458781843 1250 458780593 458780627
    0x12090d171909050f011b1d010903140f070e0405060c03010317070f14010e0105160c020f030102040b0301030b011a07030f030509070909060213080d0c060207020429041a01020a03 78
    0x1485040761100e425540b0404c1b11440310008004006c0e4403507007145102c2c040400040306144500c501070002800c0543c144405803140c8003221212111807800e11610b820b03c808072055030364494079100869030b4220705860031581d03407141500140d50380075041c0c1540d0689034040c420308103101c9400303144003540c0c02100e001d40f02c103440000b60000007078180c00043c241c500032400100b040303000c05014500b100c5004005151840c188007642c0b0070598050106c05500381d04960248086910b100424020b0040380c00107400c00038000004800d1010806204d4101c0c1c0081016000d5081c502252400c54041d10800501182e407600780300400310b0081d044203502c84450f07011504910b56990048003520000c29081e0342c0542d002488000030031014508501400b6150010311071403004c40c400404459030718a02500d615130110300074003196241c0e04260610240642248e440360401240f4100d240c10184111f8030551400007a55610f1000041c04c1e81400c005030050300300c001094606481401c41c00e182c1c107032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458783093 1250 458781843 458781853
    0x910030209040b060a0809070911093307110d0b0631061d09030406110f10060608070e061813050106030e15101403010212090d17190905 60
    0x1000b80c413008041c0070303040e24031350f0340c286641003440c0064144546a040324002c1ca00740320b801c1090115841c1112000c000548107004d001240800c58103d4101c030040038842c1004081c540040107501001801c90135018040c0406c04211a100700603502c21564801404841484d000907031600d4888150040e0a0248109440741d9080c142101400107840748802d2203607503901010311900b407040381c1b02e01d0751040550501019007060107540d40c0d82d010718411340c000c0101c1b01180f0480b13072000744110908400b024085401090203140c8120140c0814050000000d568a00003920184240071101c018407001e0902d616004240300d00d0401c0c4040216469080308500c0030380301218a152080034020a0035136000550840043c140320b00707140c00f80040c40081740c040c0c0144041148282a41802c5a170320080341d80c90300030450080307406800f03600c0a548400300301804012200001103140d941c0245940d8800711094001040140344100c1613500e5132440c01c2e98001c1d08c00e240427507400140c4280c052821a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458784343 1250 458783093 458783111
    0x503070b25060204140114030a0207050715021e0a0c032a0803031e0903040e1306050412030c0c0510050703090f080706050c090d030c29041205091003020904 69
    0x121001d01c5062049480319400541002100851414540400000d00e48074865a504001d107503410b02010300309010312a0300081200800408000c1c10300103018a2404072190100f200001e9200d60280083d01c4002d00c6401501c50600e05c04a04009501e611202c03440002c0d0075925042c0d8405500e440501c001c0c2081000342074800801d18000b0018942e00008503900d20b00384c10702c0c010307004103001006800d01072075090250307102d000300a5805131141550007500e296503049000000744030011003d0501c82c42c0038144401e0002c03200307010f14000a5610700384a03900e045582161040905103001d486904901c940380d40b032306016004250803108924000c24020050b880c0c15041c43c0c107541084070030000009201003000110b02400d41c0c800003606200d403c0000d2103000c52402c43d1010b100504000c2082c4140c0704110303485903144080b03142012441c03030710720714825440c81266040e03a0541e0008680d80ba10090503206404130f5400e00070180404001c05e0702c1101c1a070203900300204199000da140e180d54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458785593 1250 458784343 458784397
    0x1e08041b0b041409040201120506040906090b06030601050604120b06040e030a08010e010e0f01030b070c05010c0f020f06010b041a0d0207060f050a1a01051c0e03030f0703060503070b 80
    0x100e40948070003107480e650382e86400f00d49810b00407016029805522640c04010160b80c0042c02064612107440303001c500c0381d0707507500001c00a0060007802005a031a100d054810b104590403094880c020582c05c86420380d89a2082003214002c46c41183c0c44151103000b50030004502c2144140c0100000d08045010b010340000c25055400411448000824030320040000c1100c100f982c9004009508030b0642d03500309003440180d4207070140030250080900b41c000c600028460041401c80940007402000000d580036402000b20303200038500c60052041018000c0c107079030041a0241200c485801952909182c520048204416412010b84854041c8081202c07400f035400145011403061000260029192150744129140680321024032480c05001403c90001e07008683c19800003400c059444d5169a4008004083c0181119841da414403440342d000f008000080d40c081c034034500420065507180c0704100c0c125101441101c0c1e0541c401c15040010840841c02400c41101002800030918220380e18 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458786843 1250 458785593 458785643
    0x5060303031f0e310c14030c220f0b030d11120310052b0b0c040801020d021206190b09010c080a0905040b040b0901170a050d0f0905011e0804 62
    0x190150580d040010b0240300c5004003030513822000c000e51410301c404155158112120628011510101c003903803205131040c0d0b0100050503200e4001001e010b9a40ba000c0010181e1b214a00b404489490820070740c010155640d0066000218000d0018000228620030841b64442107030310101003401441040240e4188450007944914030156000100b640390405004000c00101c40959030000d110760580c1c04068035042c0100069080107980394592506c200303021240c40b17283d01021842d0710003d01039080311382c55009001c902a09074411061991004103001807080c05e122840031882c800f00e002e01040c1c4050f130150481c0c407010300d4521800074640d40c500f00c0c0e030380c0500c02c80404220841340800c10307443c1c00c0c01910344103507090390244040a41c00f0045031a40106018140042d800d502d404409500c0801034010034540080c100c82d66000e004070003601203419a00701d8000562040000716031035015002c100d01000300141841102042100c0c111103511020f0011100040d882c0840031100c0b5010300b07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458788093 1250 458786843 458786851
    0x302221b08070f0915030507020f0706170f040c03060e011e1b050c190f0602041526010306050709030b18070e01050901120501091703041505060303031f0e 68
    0x11a8074050038150800b4007001040304401003003241d0204140520700003201c0b0900c40d5101800c01140b280c40300d100aa09281d503090908019108a40c000034442e607009025904950070a902c034220342c2c035640102202840112009818072220050400000e14144c0c8091a8442c041000040c540603107066800f1001408140d0610140c4400300d2080c007014085040b080f58445091641c0b4203840b84801c80c0e220320083c15400006241f20180307105002000c000703404000d600c2078045640d2608c0380880c0500004400c8080c0000311400204c030204105000f4446444440c0200c0d160160320b990307103010240c10014038010410000c601c2c00070000318240c0c0c41c40c1c020300c0b900c1d42c003540103c8201c3c14030b03140203229840280d06840300c00c01086581c4075aa0b15605440d050f44810000340307000e040250150014610080c141c5420601103000c140e600e03405540240c0c03003003103070700c0318403408002c580c0c03c0d00e9041d20070b6a4107030001c0020500c881208000b880c200c20803a242007114650314000300c882158119 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458789343 1250 458788093 458788097
    0x70c150f08062b0602210a141005010e060d050a050f07110a060c05090d0b01050f030a0209040201050f25060e03120109051302090103050c04240501051305090a06080607090302221b 79
    0x9001f40e414143c0a00840a450a010078020385000c0c41114a511200c0c46514140034032840002030700d403210b0707040303418044075800240b1290600d4010403006100403951702d884586550045903055104908400502d01c0c0e500042068904075201d080007050081000024002e007080007050513118810b008038414006d0314032407483d40c900070500c9035015814a18900c00c0e0003100d10380006035110100c00d904560203290294440f0b455000c13003070740e500c0b400c805000070081106400070a060a00308484c68144507080030701002070740005580d81d03800b92103517503145100320703100600c61a5034603807010b0350180c40c0d06181e8006450b40d8011070300c050400e80080c0d800f6003020103070009604080c00341240703210004045040054450a14021080c0c050103994100007000a8003510b951590441c4c2d03024040c0201108002e0424440540040035079104403081401502c0020b4a014006c8103082e049a402034031200070694005005101c0240e040090307074080781c0d01d8500001c214801313804003407036505603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458790593 1250 458789343 458789407
    0x11106011d13200910081e0a021c030f030203040b0610020309101701050d03052b1b090b031909020a03120504031b05010c0602070c150f08062b0602 65
    0x440f09001d541c1d20002c0c20130400070711040080180c80000120b43c4101c0304e0580031116000440d041e12401c100103294042d61044220003054080303c20541000d801c00e129444600031441690b20940c01c2c0e0008480c09400c05441d500000c40038101000200b14003480c1e0704c1580e1403c0190f100242042c105240c44000140380600000194404200024050202190010942c0e881640e00500c140300e44101010071202d02c800d04201c00b08a60140f60f0321203010002407100c061050310055903450100721640c00a00a400009001c4c0d054400300c07401107203420714441d82000300c0c02c0344d2805000d00f003030102e8010880c2100040402c40310310001c13103103001aa895070b540d80c0c60350420108100c82421080700c00c00400d03000700800d0b80c018a01d204900d41c08240561611409c0c2072544551245902072140b52404410107041c003070780f124031001640d00c95141d402c969100e078418801c0d0140c1701d60b0f034051111903200003071b80c07180e884205100807035100b640f005d07160500043c41c2c407410940250082183c4105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458791843 1250 458790593 458790653
    0x302090306010b04080619020403050a0f030e010c020a050f12010c0801030c1703161407030602090415030210110f010f02071401091a060105040902070c0302011106011d13 75
    0x70310003180104080701c1010f0509040511541d181c01010b0042e080351424540d000c0003802c042d0301950003d64002d425078101d00c0c541c5c1400ca52851900108400069010050440d69809022007030081c40c2c000d045807951604080500c0858045180c820f40d100304010009030300e07100240541820b0700050340c0c5040e8554514039089a034039410f6005a42c1c40040d08280100c100000811b0b14460000b403d64908800e8060401d11900011781907902150300500710301106101c80c580013424111029141006451368910004400c507040d03005c0250700128107000105541d01c41c04500c0b1914001070160307030001c070a41016501316028660b0704082c450f0045010010300080105034641002258002d01148240340d4074502e0b240c1840c50b2081c0042551800b24543da44141c0a940c05007140300c41c215074379401800e1607200147c443c4412800a0001440d4200601d00420500e04079985540d00103030150604182c01c49c100e00007030907103491001c0003580c03002040100c18660110a0030507070708400c001e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458793093 1250 458791843 458791849
    0x506040c1703030c030a050705090405150a051918150e0402031216150e03040e0a151809030e0d1a09011509090c0e010e16020a0305090108061807030209 67
    0x8008241e203a241e4100f032003005001d000d07000469030b100d00c2e00301c800101caa40b11b0006a0b4140101240b45822a140108006801d0840000c040000a003101c80c440041e5940e803c00910b0240600145007401341319000304035000c035030007146088282200c07020615400140014200151a50004121000c0c03402400b0541c02d003401044082c000d003514440c5802c1400264140251201c5401000d10f200c1d43c1c09040d4030102d940c007004000894070160303503550b035a41000d07002445003a01d0a0800e5860034024a00d01685a20000103d403803a0001d00e0300748100309a01c100408038200700b541881075a030b24000182c0d552005a054282c4070701546110f5154124521540303200041c0612070680c50003011090100c941e030b03001402c848000502056030344892514156040319035005c203207522000341c004580c0050310750445100d4520512450200d0141c0d8000300d9541106040160125408110040003548030302503855010303001408440401d2001011610086400c446000019902103104e0b1128a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458794343 1250 458793093 458793119
    0x1606030c030603020907050703120507050a1716080c0f19030f112703060a0c12050c0304060504020d0f03020c210322090f0b09010b030f07050a0c0506040c 68
    0x800ca89001c02c0020300f9a4003040c0340c110040c014105000011410b0030815105980c12040092084020b010760300300500003800319009400842c0105040a00d00010f610300700b00d030980b003290404003034051901d40070425a25158042c15840c692441001035007410603003680188400300210015002c1e8010a94000b0102c403441c0d030b1404001400c1c140b4410012019900b510070f4000d46c0140c00d00300c452420b2000e09a0124018055014081c0104110700c403042c561003000000110380380c84101c10800d601840c11948115640d81c9004824408174002c1000f50380003503070051000c0d00c0b015640405444024424001000031401a8000d00c04048107003440100b1140ca0120034081d02940c1449020f0140c4034003410951b888203d140440c0841070072503482c00c180040c0007a510070482d05812128680144ca00c82c0000b5015400420000423280560742c01c89108810581078103225482d00c103001c80703075a4041d5a40800700040c010b180004644280135050240d4880e6040f20300f0245070440740300506c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458795593 1250 458794343 458794361
    0x131b060e0f0a06110a0605161107060921050a060516030b0607060504061103070302070c12050c090415020f030a0c03050702060708130f080c070506131412160603 71
    0x5105072030719441c594451903408020f5078460b00b440303007440d402c41c041c0514007020360390054206420300090042c0d12500d50038140b101900c81d070b074101700c0d10030512410b56990315a00c40c501c0061104141008180c4034101e05d00e09181800d03456003403081d8603454540c074200c80d0303400641d4403c0c3c4d940b0a0051402c06990312011124003030401388001c0f400c8400084050003802d00140c49962620005410441c0e04d81c00101e21201c004002c9460b4240031030010000d410aa6003256045010b0308042042d107051081c107150161700c01e00509170181144240311040c54054000c407007841c1248540d0982c44002c0c009402491312a8012a4492900182c0d24059034407800c0c2100516180c4810311003415400f1034140c0e0b2081c15800c001c001503c1d405221721003140d50700c40103803c9900d03803489201048031903801080d03009081c1044400b0a81ca070820003c42d0700c1648414090605601e030100300c1d004030580e081105100091601c40305080b1134040a0401d51442222049030711068000d1000b00d805110701284 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458796843 1250 458795593 458795599
    0xf1d010605011b020303040b1c060806060a0306020a09080106090905060c03040305040506070302070b0708030703050907050307090b0303190309031202070b011a0d0c09060e090405070e131b060e 85
    0x2026207048006040ca422103a0444030b141d038040300380da0964804004890040100c100c25a58682c0c3e000320709007140c80d100c4403890107603051640001d5080e100141041c0564401010300440615640d83d60380254042031040c0140001c124000410703050a1248400504021101054050380351800341d040c0a80244540c440c002d0920034400441c0d4441e040d42c0542e60190780c035560350595410161318041d56039022a601d0b5000160300c3c3e0800201e40007550042d0380702d80b01440300f6210f130f040003501d628641c0140c41d05a40320b0001001021181d410a451101025042e41e103400480c8590500d031000b182c070410042600c070b2102e00308259020f60141e0b400c07543e4034011400c210395541d4503441540c06110f802010743c102035821548405000441d1a4400c50703000030401421101009842c0e00d0036403050a001c144080c0102806003000303100c00e841147e000300505091800c0c503082d504804005411f2500c036050400403900007445032a91050ac600c0a5181212002d1501c03a000340314804010110740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458798093 1250 458796843 458796851
    0xd0f02040e032a0a0f02120304090605210c010518030609070e1008030913061716150c170405033403020904021003020c0a0c1e0e0117100f1d01 63
    0x344100131448a86040c0e0100074500103035468000182605a0703007940c1300160000050006045035117a0003030007198000c1d1040003000c007400d070b01800520010000c01250303800070118036600b50701c180300600002d0150341d5000d00101641000c60b290600458007107040703034422a014000e85110851556000050300749002c2103c0c18242d40036241d0082c054054000d04014a80d0040d07407100360090b102401d01135141341061416440c001d0780d501285002c1d20004100401d0204503141d20800d440c0c10104a500c0380e100b00601a40c1d000790f14038030171000c61540002400045100d0b50240714101d4840348124229046180321901412950a1400c4100041e030b8180d40c02c20060315486101e660240c0c04450a0040d42c04c174280980c044c1c400d1440900e1300b03006178500e500030480010b501078160386601c0341001443d0004110382e001309c4041d005e0701e00c2140b102e4004012419030b0a01c055000c0454200740d44501030258104c0003510f000d2100031501c240c4440040d6060b1540c2c1d000000200480c50080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458799343 1250 458798093 458798167
    0x3052808120c04051e100503060604030b042d12020c090406050a0609180c050d0f080a020f010903030e2104060e06040e010608190501030309050d0f02040e03 69
    0x540c880d101d4004028109400001c00c1441060180e40003454085c00072000c8460b0104500c1105855034903d0784984404c880d0080024031030010340303103d01c40c050251440c19003140c03203103006448014003c96040c42c44503084211080c0340101400801103098401c1ca0104941c901301040700440010703841150b0203440d00b10700e29510100455005500002c001030240c4815080001416281d00005903950400354803600d440c0e00804103404641c002d00700d0303005480d00d0343d04125030402e003044050001c5071204423940214010790002c0c6104943c42c01164083c00c00303000503a00351507440708168040307a515440880008001d000d18030381c070f00d29203902401140d840c6e01784d03041a004a00441e000c02020500440b2945c40303c10441e0701800003807900314955a03444800401280089a144010b201c40c81c010801404041c081d141c10b1b02c0e4140c031652502070070107043c041c03840c02c640002e581c0e6422520700c3c8009a01c441c070400340b0b680c0c040340245a9440110703100049c075214000c505030642100e00700380 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458800593 1250 458799343 458799353
    0x5090114030304081e0709020f0a0e1c15060906052b1e03080a090201020d0e060702210f03070819091805061903020d14030c06090f010f02040302090604050916030528 73
    0x2142c80b2b190604107050301e030b030030030010505d0440505290f15605683d4032084060004010302d9200c2e42c44103c1c41400000e0300d41c07800c28103540881c42516004168505003030501a01c00b10300950400ca10a40d1a660307500765190302d41c400241025008030050b800303005600b03141d4082100c980c40362170101e00303201c5c155103540001c1d0b0750b9004840240400c40b002032005a10ba48150445031900d400800d003511b1002107444145000e41d11111905551255600081e4421400300c1a55001d80c2c101e600c0500b482980c4844900700d1242c00d02c3c0c0020440c815002144d400880340710107000c010100400034403881e0800038400110035840b03803c00a01810a020401680e03101791104846620900c050141803004600c58034600800d0090a4030b401010100f08514a000410a1804060340020300141203c211100202e100d1800003030342003c604000200103007440e0f080300d900480000111140104124012605510f031034000701c410b40c0250001e01d00d0281d0400e01d11401f1541c5860910711401c941e900c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458801843 1250 458800593 458800597
    0x6180f0506120709080a060e0d0906170606041203020c040c05180409110a080607020601060822020a0b0f07031403010608071412010b0a02061005090114030304081e0709020f 76
    0x142c10400814400a0f079001d108010040c010520642103998450891500001901c0401001d03034892160b185001041882984120704480c1d0b0346c0c4803c1c112801e488100d07908200000c05107a0030140030000016000890000d46204034040c2c2d014012801c3c000080005917006064010100b010510003d03620604010382c0000210b401c5400003450411449d1040d10048403644541e48040400000102c01502040d003522038506079003510100d80e2200c005640c100419603064000100040110860b40c11075081c000621b4001031602403003580d5440d0480c429440807464040d481c0010641c0400c064000703101307003001c20082207864107660410704010640e54004110b901003000038103800c80342d58400e204440d51511030b4403100c00c3d0740d038450240b400554001c0003043c0051180000140d41c1441c04548441924001002540640d18180d20302c60801003078a4040d0b4940000c000006d4a00810001211031541c142235070300411040003480d50404501d940807180541c01040b001343c3c0c607001101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458803093 1250 458801843 458801857
    0xc030c13090f2306011a09090705090a06030b03010b0a1d0c070f0503120603012c0304210302190302101d1005090607090e130314030106180f0506 64
    0x1000030345000340342030a00c40b030581054050b000010b10035100a00410700c00d02c0c1010660f0101c202e80c10b5981c0ea10490b613030701400d8400b07510300176800e1084200c54940902001e4000c2407070315025080400c0e01e000221180300c0781e4400401f10750b44010318802401c2c00c3c0201e030048001120005e89003407810584101c1806200c0480034000300990009141c0d00644042c2e9200c02d8001ea000d009512007440c00035601d0f07003c0070325100b0031108100050583c0c03505004030724140000c1c0c800009c0c80400300b9034800c811054003411091500082c4000300700c0802c4c2110003030030102d00403a5000e2603001c609004c2d04040380c0690000e50070000041c6100803d40004012043c0842c921001550024000140742e103900740340c41c5c00d502801406002100424107800070b5020702400002d441181c1c5898405a91001941c880c08070058080da001500201c3d5441c1074484c41406400c080590703404651440b41f40d640260484030104a80b112104640d1400c01064009400e61004001c005410103001854078000c0741 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458804343 1250 458803093 458803129
    0x1b0d050705150703110c0a060b0a03023d181505031b09090106030914030a1d04090605040309060201050907120f03020c03030f12060303211e10080c030c 67
    0x12003c61100ba11980c040110388110390a00d9072a014019000e40d1245503024040d03520900b40300d10a4554940040031a04480d4002d00c5042c08541d903038031910b8005000d04121002c08010440c080c200c58a0f400c2e041c20754000d6a40303e510144e94045035100c208645d4000c010001e40040b0340065054206007140d4112000f1008461081e16101448400741b00f08070b00c290704544040000509960942c02650703040d440354401111180303100e4104c6689019400c41400040c060241501c0740184070281454040409000401c100b580d0b0b0301c0d020b041e100b0941d0110002440d0b000100441c603828483c003134200d484800130301129803070010601000340d5030322005003001c2040301c10041054000c100c400c040780700c0035007500d89a03980b41100c61001e130070514014074a603561038001285440e003c03046841040d4000d20305c514200c800c1d42002c201315001415030710440e400480300c0011003203501d0311900c50b1540c0c1c00c140c2585c80c2441c1001e07041001d0f003410305000340e00210107a01181d880c4680003079003200903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458805593 1250 458804343 458804383
    0x40323030301051c050307031e020a08030c3601020607020c0a0b1c2d020309030a140717070c0509070f051e1809130c05150d021b0d050705 61
    0x81134000c4103c0421000042043c40001000800c241e00009001c0c1c0741040e25a2030a01002d0380352050381c6602c18940000d01554040000409a4240d0000791812089000841c8907030084039481207111084403e03081404207400f40f10350350640e810001941e00248a1015001d950030003404100c0b001140d0050807004140030031102e80303039003140100c1070000368901c00a03c40c00c0003d26040d254103480319060480440a0b00750441c01ca1014002c80e800365030200001d62400c4442c40d0210b64100401d01c214040000030090b2001092125070080260303049043c03840c7d80c800da94541800320b6952540014041d950f01401c00100c1600700d01140040e0b506402d00994550701c4d15000c038a121000146000e40590209403250024201101c0c4a90a00141c0d5021100d46402020703d02001760940028040b442880c000c0c01035007003560a0750344460100880905003961650794030709030b8000360b07450402e060704498941030001040024081c415624100945400c4807034480741d44441c1c00120841d100030381 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458806843 1250 458805593 458805619
    0xb1e0103020706090605070c0c050d172a010213050915040b01181212030209030613060f0c080a0506011e0503091608071818060e0a0605090304032303030105 69
    0x9160000c0d030f07413568070040c10895880c4c0002c000c0d0003801165804d544414420780049032500702030041c08082d542150700068400000c03940b02d00254480e15099251101002c48607424145414644010350030140015032507541c00c148404074080036503c854881c501300310500c10188240e912010007039405840200d00c1100c4640140c41421a021600d03406000d100b10009400800420301410244107a4031116450f01c1464100c0990096140556040d00910007080c0340d0f00c858110645041c1c407882c804910f62031400004011035801183c0c0300c002c5826081084008a0184209580702500342417010000719405100303900c20f5151011f41041c04070000114490f44410081141000344203800601d80c02e1b00c070f0b6000e94448004c1c0c03107910200ca0040a09d0a111007181c010218a425240c0034440d40d014144c03036243c090041000080c9060040900d188003150843c000d062103064941c0c01559624914504054103101c40e4030342008907205c01400c007000210100850b41147e0f021610b40d0110f40c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458808093 1250 458806843 458806853
    0xa051507021207061205100608130c03060c03021c0e10021b0303090a050d08190c110706090501090504050f0f070918050709050303031303030203090c15040503010b1e01030207 77
    0x203030340b01041414070908200050003a403200300344031a00d60510050140da128a10000c0b02c0350401c6c0225000700c0d24030b000041c400280301c40303116060307801404110046a0350741c480904942e41808404c0000e5000160f6011114041d1b082c5600380d0107403182001018005843c0030f490700003c0802e0b00b00180c000401c400040d850503503248040c1a0320003075990324146595107d99400c81e514049035070b4000c00080d0082e2601031101039100c0d41070401160380c05101078581d071000b000016003010910041d003610b00c0040000300085800f40c40d094513007907080d6040c80c0c00034000a11560020344101d050804106200b50a03060b195003250244a02d094162210b030000d890000c401c0e002a80243d80d0643c2450340b9400360340095020320b136543c03614580c0b20744841c1415128402106d11403030a4541701e145c6000688030340d0083d50f20100700030584500c80d520f4030002c0d140d07050b01c1e41034aa1064000c035081c0070030b107020720a0745892441140e4a14640e02c980303407903840c0d400c00100120305069002c504542845 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458809343 1250 458808093 458808109
    0x10f080a1a0316090b1801150c0b150102010608070f0b090102070506270607020603132108090f01020304210309170a080c0a121503020a030506010e060a05150702 71
    0x2003402403c0e01e01d4050745002544896140c1d2240522050601c0c11000345c41c01d03c96540700c030406082c0101b00f256800c0004104102c0e607029045410421600c22010202c0c00c1c1c403152600980300c441030b00c10310450b034000090a607100c9411409a03500b010004001055038000aa0112910110895110f00320840140d0401d18103a0015400ca04c0010794070f01072813114001c03466800c2e681142d05081e107425600b4403109000d607240c003d410000804c0031a990303400b43f01c1d09108842c81801c44411844c0c03001d495002e4054482e0101c004201c0c242c05011602c8020300c031449244124000850031481e05403501c1e002c61580d0b00910701164400f41485412910a41180040039000242018098407111180025034000c8000c140040e4458010406c502c1e2000111040d0030403075544d09030701188200e040e80040c42d038920b01c9040c2c04518000040141c9645068000643c0a42c003c0d029561404a004c1644a001010144919004041130005a8a036036080814070f88000c0c03020380f549030703d2011881c06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458810593 1250 458809343 458809391
    0xf02070f05210d050c070b0406200109051c0e0d1101140c030a1d010207030804150e0d03030203010302011709102f0c0705150406030c021207051605010f080a 69
    0x600aa030151583c41d0381100013004802d0200c811100d641ea030354400c66030316000740d014401c0020701000c07951103042c5510f542c00e00c0107020213000150309150360780c840349045000f150000c0c8800705920702c0b541403504002e40c210f0240007502c40c8a810a00c503074489140040007250981403001c9602c444a0b00303e054002c2d90b044080c54400c80342d84000c001f0000d0202500da03540d08217aa010014400901c2d4400305240781141c0c0d020850f5410103007000c40c05054485070351090b00401524071800c051654a040c1081c15150180d140180d80c0e50550000508501c6412590364103c01102c05025483c800007440840e064400b1100003014100792000c1641c0110141400c2206110b1003507203400f80b520341c4001c1c2040348801080f07604003950b0300107009485040324681e00e14468180420024980240c0212003d0051072050f610022034070019603442d504062003e2310158090030301c0d01c1c2038140480000c80600401d0a011054403142c20001348030145c010484a891900c42c0b042e214803070001c0e01c45001d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458811843 1250 458810593 458810659
    0x110909060d030c0b09031c0b0904030e060f130e010e04080d05040215030f0a0e0109050709021806130501020c1516030203040803180901240302160602040e070f02070f05 74
    0xa045c20480346640350070144035500c640594516101c14541540724060307641c00f01819200950b680d035142a1038002000040c281c115104000e2080e284034408010000c0140c0e515102020b98200101c1140c8004160403030f240500d020b40a01020801d00707400d031010498080c0c4049405d50369880420004034020064072640d507008000c1c002d0785200702c05c103d0711a011201042184045014086080e1740034008098004e801c604814403030b1005030780080104200444507440b0101610010900a0340104004100a81c840740140f040e5a0705202419942d10101c504420120003c0e00c8043c040c407400e0045a108051f4041440c02c1500070b009031070044c9080e5050729126221022190040140c0100f002c0c4202a2540003156848400c4070300341945c0301582c074005152221200070740003540442d85c0138007040389450100c1e001410758001080501a4041040103130700780700101a01c1000d40981901c10b541040e9014444034130400001011920112000c2c074600840d190140c482c0c005505950071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458812949 1106 458811843 458811863
    0x8180a1d04210203040305070b0a0509100e0303031503010e0d0f12060504020a050c1519020715020c0106031e1101050a020c0301050910110909060d030c 67
    0x41c0c450300c10031102c29558807607820b1215010b0408140c20050780000380a10030040e05100c560000c00e02910580d00f04203030a400a0400c0c001c0603070703050242000c511030044a5100300084094001d010b004e41c1e0b50b074180321240c99089042500124002c0d804c054044071008000690f41070307004041e0352aa01388013896142150f0341700e420311445144a4540601007410f0b82c0b14070091a0340151600d1301a500c8080c01092030a01c541d41250656003502c010811044810000e0a40c150384807101c00180d90b28054940034415075111158120355900c0860940e042c1c01d01540b0450176079000e004410006080c05a000f0040000480005d001410340307001d400382940074202030018540d450066640c5101e9080109003103880072076001c01550b100101c0c1001c65001c1e449500c20340140d03038124514080400b4040703008003202401140c0542c003031007002014180310380040c1c061140c3c003c3c2450 = true := by decide +kernel

theorem cover : BRFrame.Cov 458633093 458812949 := by
  have h0 := BRFrame.cov_init 458633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458633093 ≤ n) (h2 : n < 458812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
