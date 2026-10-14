-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1975
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:21:50.8033+00:00
-- url     : https://prove2.me/submissions/00d1883c-33f1-4a84-855a-5af030e7922c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355035971 ≤ n < 355215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355037221 1250 355035971 355035977
    0x80316080c0a021c1a040506040305091c05010905061305060a020d0e1b03060106110c040f0e0a0f150501121509061b0305010605040f180f05180609030405010c12 71
    0x107501d80241e40c2e0b454812003c1341840d0b00c4403440140d40d25100c50701c06902c100b10158215203404100100d4000300b4655440340d01410100d03910000c0e0030001d0b06801542c01c1d4000803038400c070140c40a001c0305600400e07100d88240c1c1194031a40b6600440c2303100c1c8184035001801984848001f40501816401400340f03546c03038800209100b00018926420440079440f165440f190400c0010b01520b4100031407401407140b420000d10840c104801c160311113903102034883c0207a8484140028581103580a180b01450301020384807442003c3c9010346c40e0742d801d918117580941034000c1740301500e502d42c0306241c103d074440c11000140c10354036a039a103040108100c4401c80c03940c0d1150b44101183e0180200c0d1009505540c01c54075400d03000340083d0848806070400800c01074280402e20025040000030070a41d510044d15001d60b055500300700c0c0283c041c0320401e01c005410901803140142d5106451811145000c06840999480000c1680d5034040d81c4503070340c00590118101000b1500a02010100c2e0010b4a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355038471 1250 355037221 355037233
    0x41505040204120312020906070b0615030a1409030a1b15020301060302091003050115050c0106080312010302032a010e04180302030307090e06150a11070306021201080316080c 77
    0x40040d00701d820036400358501c0c0c042c4668050800d54880d050303d80c6609800b40842c144524400410858000c901d0001d2451800a005c944a80d580914241d0b81c100b03010442c0c1d0b6a07241100000c006016495a600d000c01d840381e0200d202080f0110aa688122490341d4610400c3c040c6080c05000c64810b1b0720a4500e40e5004000e1060300c00140000c43c040c054a41740540c2d90340c18481031000d0070100221590825180000510550f050440d09003800f06562034000d890340060719005004200b1680910070f075200000b40c4036020b0140709880d60403a4000c134141e6250f0360881c0c1c0d040741c03c01d09000040f28600caa40080c00065805245030441d03c0d480a4030008418040d102d0400010811100c150090ba101204016400c0d91122480010b400d03112802011360605202040100300c0444d4100700b003610110381c068005103e05030030f51124040508035950341d0360b02d04041c1c0017980815090704101d8841000850090000400c03140220820410141c90b01825107038150150000c0007025553701404d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355039721 1250 355038471 355038479
    0x81504111504060e0907050702030a0204051905040b1501050a0504060540140303030402040b01181d010608130f020301021e0d060609030503070f0f080706021206090c090415 76
    0x300984080c003c2c44d104c0b003440c030303007090100129548010316a404120040001d800140c4001c0380314450141d0642c0c011810761180c01c41c0c03020b00c00403001c5915182d460070041205001c90743c00c0302c034000d003000c802d40d9180b100c4603001140c0328030400304401c000c5601040208913040c4240014202c68108420300686414000c600c814000651b10842c090030a02000149403c04003280c85001400ca0b03035404d00e13400c89141e010907240c0c00b00400c0a0301c210754a078210801c83c3d02901e002c07428107804c0e20340c1170031690720f82503a40c940300d050545502080d01400008568280100c50450180c50b408220300c1180c003441e503e80402c0040e913207089070955000d201041e40d0300840070f01240c80080e1403142d1610f800728148400220742d0a40d0241080203030300001000815000b00458100540180848607040c5071401c1860640c140e40c0c034024900040042c1d0780040c05640e50180400c00350b141181040c98032a9400c00808038800e440b07040a0b100100101c1040341761036404981940c5441c81300d01102c580d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355040971 1250 355039721 355039759
    0xc0b090913081303110a0801060f0b071a0709090c030c1d0d0606120203010e0106031703090a0b01150f0212162607150216060507020109020904031808150411 69
    0x4a84d0040321301004840d0801d03100e151107043c4902511004000708003492400d910b8498452a91140c00c8a00c5000540c0d80300b8844a4518200110085503c031416410440001040303128140b1a0440491400c800d00b0312151080c002e401c800800c075a80d00c020743c0784900c8031000700e07008032407030781d5200041c0d01569001800a001d844003e005802ca5440200c800340141030944080324407051559240080030f00000c0c8940c1d0502c4161074000751000e89030f41d1144005031030a0088c06000e0302c1c0364108400018640507820410820965aa43d540401c08162000340c2e9150701c00c820444140f0344c14041032050300c08029402c00380c03901071400c00302c017540300a40c00805d403800d00800706010b02c0c0001c0c4c003900340552095007800c110110403007148ac1c05e01c4542540c0e00681303240b0000f00b040f07803030708007084a0718400d4104d03039801600189202d615081516010313200070040d28003540640585940018406c1c0e0109100e03180441801e0555420b0703496a9030b03d50740d85941c00e086a03018900302401004210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355042221 1250 355040971 355041007
    0x1081305010c0f11060f01060503040302030c031804060504020c4c110f0313020402040305060709091808070209091e07060206060a03050c10050f0f070c0b09091308 72
    0x4056164580ea181083e40020200b400c48042150580d001000b40a00280d101407958112200e51904544907199840c04a0861007149003030065403101103101c2c0c840c054013400c00084030b08103c90400040d5503480038801640981441e6903043c0e000407280303500c03010705012001c0459104040001c03000c01c80008a03030b00d01d0110040e8140800003150020f000b91541d11500400381480000c1d81e081104105040409100080110911045a1985030110f40755a01600d015580c0032040e5002880e10020080280d007036881412402810420800e4101c3d1010901c4c415450300600c0c0245402044d400b4005154000f910348982c6110701d100008001c007010750141d1101c400da401030f00304c0784e107842c00003880d050002d4602403203082c0c50320701040004c00001e070b0200180000daa08403d03800c0d483c0000d590754000ca542481d000c0c000010041503111031030000780382d01c0380f08480714803802d9244c0340c052030a80070b000c05080e001761040c0c020800244124400c01002c07480380502070b243c0800c101e0443c074160 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355043471 1250 355042221 355042241
    0x91905180703150902250b07050a03110a030905160803070611090603010b300708150a0f0501080a051302060304060e2b08070f050d09050708070806070311090108130501 74
    0x40e030206e8014802c0d2000c03480354400106151180c001d1007140d46460509040203085101403280000d0803401260094011080000d110120940c2b1500c12407405400741060240072034050244c01c03611400002c3e0b1446d000203550b650b0700294140351a80d03460303100a14451a103040a1202030120408907a1000015400303401c4500c3c1c0251513980d010046010600f844990020145e030070704c0301c1806150302d4002154002a14500300d1042c0e243c082c0615600001d0b50390050f00700b9800000454440404030f0702130b0881744c080e03840742020b588881d110790440c1e00942d4100a0205904031240161909401440d0460300821000504a403600c00d0513181298018042c46e800c40c0080f0207110b0f4200111100e686400c2d41e0800403d18075080750b00400c0c210403200b0000500101080c08014105513a101050059100048078070003a2903403c1160b44084500c560140c9202d080e002a206074441d00903034039a842d00031b1481d03080664190055400080c000c2203004001c1da4120104d0110303000f401102894 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355044721 1250 355043471 355043489
    0xb090106022a0108040b180106060e011701080309040c051314040c020d080f2205010218030d09090c140304060e190209040609050c0604080309190518070315 69
    0x2003000c2d080095095041e220003440c0306554441d0742c0910b9821040d625801036000640c0c4400b6603074103441401405d03550215200c00c1d841d020010030711a40054004804013001d80718000303825150400682c480c002401800c2c450341061040c028076007895001803802c483d450404605000c80010032201282c05c55001192007000074a0480045c289445014944130321403016000c041d070480e0340501310540c003800318100010100300240c0e03146144028444070407104112041c501400d814485e020b50880ca54110118030300100040c85c82c58006a40304c010384070f40d00ca031000c051800141200038480c4207500e8041c0f02c030b204055003030752940c0c03002144181d04c00da0340020104103200d00b241c070340381d603013528807030801008500c1001580c0c80441c0107074071582c40080441c080040c1d03d4850700b4440d844201540040020a000c101c00b0740c0440900700c01c4100343c40058111907826000081a801c41c030490b40c104401d4010207400104101810754490020f040115542800710710201c0303150440e43c01351040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355045971 1250 355044721 355044733
    0x1e04060308120a1401060e010c11030f03120105040924020409020712020c0f012c1809010513020a14150a1d040204030c2304021819030302060a0c02010b09010602 71
    0x3442c3e1544650888404c1c440f6513041598100680a82080a41c12070ba505200280e80e00c1410080d40313411082030900c4c0501038840e91090b4000096407a0440750880901800c543d00100d02e82c00d103842035021260308061201d89504030300c240c4001c1070a0010f010b00c0126003c00010aa60300c2c40e000400c20980300d0340c405c0240c00158400241000c1c0c101103030910640a407941000c10303a0b841111130001055520b044070412601e03441d50102c15001d00030f0190011103000080d020070050806040c40307210720707200034800c1340c0c0d4855040e402c80c0380c0d45400035400030120301d042c00322118007810700c1030032070010f40495075580d515210070b82c40e504421004400144010007494082280c040280418101940d00703504107070442d5503904a600180c024031020307a040700d005081c0c00d031102c24103285512000e0002c42d5a0301c400002d009883d8213440000d8000c08044440a031403000c079900d44400c582d0964081c0203552601d19001d405841c17440c01500c119034072a890344d078059540c8100d0038024201d42e002480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355047221 1250 355045971 355045981
    0x3020c0d15051b04050f0d0c090b031b0306070f021609020a03150b07080f1608040f0501111e2406030105240d03050403150c1b021e0406030812 63
    0x810b03210010100001800c1600d64038040c02d00c0340c01524141c4404403004a540b035800804101c1100786650050a4000c0c004400659040560300188148005a054a0f400650740d03580d2071a04441d0b150a5826500c1800040c164904c40d180d44082d400292042c1c807500540c1102084007800250002394046500040500e01140c1620444483c08100700510441d6441c00412121f140551800a80120710000b400e00e5007100500484076407900e800d15080819040d0309024040341c0050081c00050112110b004c2015030041c1109445803010034018019a1783c8101d08240d84030120260440e503208038074890504844034001d48070040c204140318402d030300e0407070308041c01c2d540c000d00240420301a440407811a0600c0c00381c0701200c8802620f1281d0351140500e421650ba22451341b000d400d40f0182040d412150b04a40c21403043c20020b55240750303103042641400b919665000c1c500075400141403240401440c2a254024451748000b4000102580e4a85036908a6404511100c10401840d01048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355048471 1250 355047221 355047263
    0x702040f05070314070c050a020405151903020a0b1213031b060e01150b1e09210c010503090307111302070f05060702030403030918110a050918090706050703020c0d 72
    0x42e503c17441c54035103001d036498691105521200b1100000e8002e5495000064104d080c4010821075140c02078106500d03402e141c0000406542c0070300040f0712403100050000382c408424410743e030b0016074004004100303032038541e81c2d131000d01c000b00003c1b4140f2072680011099000118405294035000d0b010120304000540440307400c403013503030b4540c1c1c581110411061100c0c14800c01610b117041d0a210849040030f4046000341c1c1e2a01406003015401046002103090001350f148440000055850888048001d004010348540c0412207101c64203900a103c0780004c11100d00c41c1040030040a01054022500754404009a80c082c120a0b60304040000f550740400501300040f561010a130b00c09503040c14116600103080140a129401c070348401c5080b034000140703140d48043c600c82075407104269181031543c1c0203805c9030042202c00784182e00700d10143c45540390000c03000e440b900078000074040040c10518117031000e4020340030035421441400990541c6442c1c94401c504400d001e11101541d42c07400300d5083c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355049721 1250 355048471 355048511
    0x52104050f090112030c30030b040e1f09021201060f1707030b06010e0a0f0503070801110304060507140a0c0204050a0b0a0303210203160f020607090b0702040f050703 73
    0xc07502030600c94004000c440e004481081c0d00c242d02d442d003000200003e0408416540e5400d65802101444668081c51802d015820f508a400a40c40511020341403004002c00c40c0c02e1000d0540241e0007070719001c0f008660310780d42d2249400060000045405071034010900c00a200180064103a40d40c40d805e0000c400f8540701d0714001c007500d225803100340d140702d42c1040d1542010f220080150b44080d02090503a8000c0d250174034082d00161884c1300066441a80071110340d020b105190090140103404121401c0600500307006803201d1101c2d600e151500d64800c0f00521006028004000d02c10301103022010050006000f1000c85907a0f0380b03a008030900400084a40190541c102d692408800d0800c540b24000c9441c112501424007588111082c40d00b000766104d0f0a1b100180780e8400010403208020030080380c40303804d00b030b551940e15030f81110f84143d0303446900b5038214000c102c1c41c078410814003c0781402803011610140000c612100e01402d26410b4800c1962a40013007602d6000f00a2011000111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355050971 1250 355049721 355049749
    0xc06181a071a01030f020411070f0309210512030a02041d0912181210060801051b04030506010e0a0605040501083f0c1e06010f0603020406051605210405 67
    0x1501030354591794900c0c84454004500034011030322101989a403111203415201900d4101c0404140000d13a8034000b003c0c500c00b405801c404090100f400c1015040152035241080c6e40702c0000c0400b10407001e0884c0c210f0b0001414a103031940c08100214510f5042448480c1c0c18501e2884a03029003002c003126400c000b0000941c01d20b150050042160507980c0b1003250702c6040040c1c0384210f250300c03021300e01b60908104500301520141803007800203400e641580141d11031320310000c00c0c8011a0780e0680d120075038461480003506540c8020018401c05200181c140e030020807482c4000355486d910004039060351001d03803004120307400405c1507071107804060b01c01c3d850a08a03510f040a4000c0c5802c1508a101c0c8104c00d810441003020412440c0c00408105480561501003401042e0441c2000056515042401008124001c0b4030000803002d0081c000d40d0b058950540f2034070f00b0441d01d00d8201d100c81d4182c0406560741d1055240812901c500741403004840984230f001c007541c2d10f003441d003030004900c10940 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355052221 1250 355050971 355051013
    0x31501030518031605010f1a0d05070e1302120606010e011103090907080f1b0409021602060d0902010f020706080622050a0c030e0a0503070f051e010b13090c06181a07 73
    0x210b82c09071644040c80d40070a44c9009c0b590395810f0109414184e2611406800800c0030944950920850066000851007040e108031904044104580c54654880c80103031070050104070141c403560aa58051908030050f4800c480450b030030850910000742c0035403c192781100c08035110300280510050244111039104207401d03034151a03510203031030f9618039100c1c904c900c1c0f0303103030b0340c049401040c05c0c2090048104168000385010707184c9006000d00d030b00810000780101e001c2001014021003075400460301707404a1741c3c181c0320403040366501b00c1413140c140c100030101d000c61075800c0c90005400340c551241c2c80c020000c0050018002d0030400001c1c08440c1da0111104556001c1e000714000610000b0840b030040364450540742c41911076250403441c01c0c014450b40c010300c0010151162030010158132031710312024211030501c04c1c0428800104100c031801d14028180140da80300600501d40100615080784014865404030607079580d0396151500031144203070490078400210b00003405100400041220100340b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355053471 1250 355052221 355052231
    0xf07020a021809070503100501050a170a080d0b0301020324060c1e0703020909100506040e0a02010e06160c031203020a090317040320090c031501030518031605010f 72
    0x28002079000610442c1d0904440030400000340d030301d5401c1c032003c0000c0001508640c1401e001000c4140078040900910340100450503001840c000500c0721145800d10590282c0171012860b112000d20394000c40541590548600780c0317100c1c0d51000d10040d8418060076044424a1155242c50910070321803102c4c651188038180a42200c42801103007200786c03440441c0f12a1400c1805600150402100e540069803045900c000c1241220300800c04005580e0607202c10001c2d513854100300411201d040b01c60508683c0100040b500550103110202d10701c0b031000b03009030b0501070028614402045d50341030881d190300000d1000c0040001013201a511100141000c4d8100820540000c0c140041e902c03000e01803030a05036260188048010443d80550f0300301800b203558170341160800200d028030107840c5003e41040310010301c8040f0041c081e80c0c0900314403070b0400c0c10007071400c00450103007401800c00a6070454030003401c4941701040000380700c801142042500e000c2c00608105084a02d03250810004078180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355054721 1250 355053471 355053473
    0xa0305060301110a18030c0305070e060415090f09060509011a090103030804030f110102130611060709050f18130309080601080304030f140d1e0302040509061c17030f07020a 76
    0x110070344000e080c2c1860681c0d6900b48041178400400050f5201814a049440010081c4140440c901041d41c140c08032082090b101c22080c4001ca03005000c0c1505281d402e0141844211215042541341c100403480100b14043d80340c0300c00040310300680d0102d0703440e0342d80e03a002d00c9a80e80700400c41c0c40340c2d0411540c501541d899610080c045e0301d03004000404008170900c1d040340c0d160213038071842c12070014071000315200e215803d10440000d115004d80300104054060344448620001002031150b241c0e0741d942d51700d4901d001d040c0003014100308010780d44081c11890b1350307108010041410748912940301e654524441281005400405c194115641ca42c003c0070050208000c0002254100c0b54041d440c0491081c80c0d0916100c0108190300c816124003510040e20070003644111120006d8040b1420b0300500d044c81c00341030741244954030405800c540c4040c0098468135109142d2005810705500c415000300036907a801661081007072480c02d00910120070301040c50300d520052540030005000904000a00e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355055971 1250 355054721 355054751
    0xe1002070c0306021b0303010f180516120b0301020c0102070308010b03070c11010c120f090803091c060209030a060203101d04110a151d040506180a150b0a0305060301 73
    0x42e01028100e01d40000750400302503802c440120b90803100005407500d0796114040481000c40610850350392522215608066000c14801d0320301502e10385407030442c800c0382d100c0217581040c40310b01c0480034140e03a00c04940058900f0300040400742c443c500010303525801c0b03103009020386c0d80c11f8000b03940151050080052407078002c01506880c5801c444071070108200000100c0b89907103079020041040089411911607241c114002912841c840d8035811046a11001074035941e001c0c1d041120b9020104c800c0c3c0418040300054820007050042101500d2302d0068404240303864549041101d00a500004003c02100c4500340302014140320340d18100380302c451500000307592101400191404c0c42d02c07082200255590321421000b0300304800100300c0c124942c080603000034200042c00e48a410100e4070600c81d46402d200311442303003400070f2004850000c4581c6102100ba40200203084090391a10921a9407144102c1c1c103005000d4000d8941da0b0301c80c009401030644401410742402030b8113095186000d008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355057221 1250 355055971 355055993
    0x602030406080c130b120702010c111506240d0e0a030e06210a020705100902010203032716080d09050906040902060f0304111905150c1e010e100207 65
    0x2c2d6840119160403800f000c101c000c090715400500000000a404019007846c6001c040c42103070603800030400317109021006e0f02c0304003400d0020403603600590548000381c0710a200b410340101000d865001860b01c1c080700c0542007040500c121411400100312001c10841500601a06401020207015151049d41c3c02400d41c058404803240700c0d440c0030401900c0e02050184c4100500e54203034004505082020b01007000307601496081d540d5005100349030661041e01d0280049240c1d040e4020361940e50f94280b4504403040d69240c13245403000c2c9074074031110740c50304102c151980c0000180c611f001c031b0701e003020281c40c082952560314180150448100201d96881010303030340c40031042d02d012819500ca803001603450300c954100c0303400c0100040140428011103e10404036101c09030f80c0842c06003003c00c0d050707103103c0d0360744030700c6a000d06031106d40d440024207480038121942d1254103d41d03030000008040d500c1c40b0b0168200030760503992000030040c122800c00c0906554580c214045280070700342d0303d804020322 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355058471 1250 355057221 355057231
    0x11030a03020d09063b0309090606130b12010e06090411010212120103020a0b0408030d18050f06070305070e0612060118080309010305060f0f0d0305040902070302010f06060203040608 80
    0x141e80400c0041040a1980246082030361000c010821a800d04c80c524016040000f8000071814202000c0e078800503101000703600449401005508005e0302204000e40560000c3c0b80c281c103c842440703940b0b102c0d190600503201030582c0b001140e469000e102e528010000050f40b08504640511742846101d807100c2101030b810941080300c2d00f00d51542600141c4c688a0020035140c0c0d0f402000a8500800e415001c0050580c2d20803100a95290380c0c4030214040c5001d1030145042d260802c00404140d803800b5406900448100141080344079142c2d203400f410b0181c14211000305400a10400800c01e9252181e0b540c001001d050110040d110400864254007524020314048141c003008102568010000000500e0a40b180c0c19840d80e00c0b80c400f180c50350443d15049000c40e0501020866900d0109212035020324040c00c103003005000c1070108a000740079101c0941c11300070200004100c101160004103a00703402900081400901440c0c107200b10ba142d5070100085410a0200380300441c5e001c0c14041e001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355059721 1250 355058471 355058477
    0x80609011508090304211205091003090f020607110108070f0c0206030a14131101020316080a0309050f010c02060108150f151801060807080411101e031b11030a 70
    0x207503480f04406403440c8207540001d8074880215610048018000303003000682d0344641c1651000d1484030105803060b0042c03081e6503034040f086800e041c0e0300d0303442a031014241d80c0c01506640c04104058022441541c08802c003a100040c5518040c2a0365070094142d0381c00c4461403406903c00102440001e04039020413074001e01c50b07400000421104142d0ba006003420b010f0303255485145060819945540d01042038044500a0880c0c910b08601d6001000b5140380000300070300d1003003041580c0d50302200741c2c3c0402c0b001d20516580b502141d011804c00c01104450301603e000001780d5a1000d4400b0b0318002050344010340503801000d42d010303105e954040f042d402400c0c2c1c9000b90819180d084441c44000c484000c01a0485042c0960008900c1f502c40254102c3e00140c4400045441e20f640441e02d00300129400707008222600707860142403c010317441a40f83c2c40c141c980000c4c00c1441d140f440031814004524100042c0c0c403480000c0703141544400d031444009403806e1200c10007010042d455100d004d010b080b2414 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355060971 1250 355059721 355059737
    0x506010305060d031b0812010602030a02160803040510050c0601031b1703090f15030c0406091e0b0a0905040e010608070501020a0c1a0c0d02060a0b03070b1e09030a0c05010806090115 80
    0x208003106c800e03149038400c000400c110940e110b400081d940c1d005603103980014403a40708420507614485440301c080c1c40c40714000d589058100018001840841d89803e020031108005140f02c10801344002400f840c4202580855800c40711034101d107100980c0c0180c440308011100403643c0d081d0000c122400c0e0041030360a1201c00f0710100020701d081c4558640902604130010070408400c01110080096078099140e040ca000e45543e01024454a9000315250f401c0401c0c0e014418244298050010240f0900c0c0005400d511030300800c059079010072819665a44848042c01400310a000030341c0a86401c0c8001d0060820715204d18014054074410411102c0c54040e007129010810b00454807114264000c8802441c2105802562081c1c21500480941e207451524900f918012581c0d400b02c4401c0c203a10b80c2014070b141c1442164019024500d220950100f04820346a14203105000b8081d0054600b4136003585458000b400041006007a94030542601d8010b002080b5a803024401c002018908400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355062221 1250 355060971 355060973
    0x31e0c0b04020a080708151605030601030522081c020a090306020904090f0809030607090503070b0c010603050a03020312060a0e01030b060103110c160801050403270504020a030506010305060d031b 86
    0x9541c0d000b541004e480d0740200403010886110004a0311044282a01030a131a80d8030500f0365109a000c070081040000e2007040440d03000c5d8465040a5000102c8811004030b40e41e1065090b0781c03510215004941400b4045a0b46201c200010500311031269071407070a601e410700e0650010008620340c007000302669030101d4807111a458590003500c96550001480358805440c0c00c15481d19005150424443e100b440f00040c51140314208000803648007074010020a0300f004c001181030f0300440c50150b800e40d030b01e403030000114804020f15008140280c029641c0c2c1c140e1684244502c4200a05450082c00201c80800005e07010440300d9045a8102c15601d895854081c01200504440324044c2d4841c40d001c078000c804542c003c240e1488840b940381252031080c0d5a954030900340e5408503005000f045c080ca800d1540c03403041503a5030314207841e142c00c85450340762540c0000303003260018008240081d40d15810080c1550f010322402d900480100d0300c5c25035054869030b008142d80941d102c05103910030f15001c0e00c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355063471 1250 355062221 355062229
    0x1014070f03020f031005040515100c050a0803040b0108100e07030605040318240804051e070905070503011a07171b1e1501060e01140c010f09031e0c0b0402 68
    0x141210030705060480e52403d10b407494070b0b1460705d24000c0724401c80c580b00209902c4040e482c0544208a4040c001c10725103847e511042ea44042c0b01c0c0c0090341c180c020b01c042e140c0099003031401184281c1c4201007100300380d41041016071401101c19042c90100d0300d094150041c02c50000703104802c50ba4810000b058548c1da80c03a08a0b041c0e00422404841032140d0b80011440b206e880c2d42c0301c200031a00f07403c084081d01c0681400c40300d00b90705941c0070f011900a40100340003e0305c900d143d03600f00d42150b8200c946207941c03962480b04650080340d050000400c08070050000c0c00c1400f603a414000d4404003218100001520761178840c071810b004840c0850000212111044a0103100c030b403804202c8820b440b000019000510191880f43e0804c1140c0c2c050405843c0000d803a91910782c2c103079032050741c0e90010b240c0e41e100190341c0d0580881c02205821030038024604504000d008046070101d44910100780d64603d8500681212040410408401034884407080901e50040d0000300058202d0112505c98841380041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355064721 1250 355063471 355063477
    0x1030f0f0317090f061e06040f09050303161b08191101060b0c070515030c0a0e09130b0907150302090a030203060f040c05041e0905010b100e01021014070f0302 70
    0x20340d980310110020000c0301ca00105000401003112419038009684001c446e202014222040009021251001c19218146588003100f48031019500081d40c0100d5210145550002c0f11310b085101d000c5100c40c034180d9804000c4107450350405103103418404840d642c0390390324003480c005c560f401072003002140c140c44c0c4192021400c4003031500c02008050303242c041c4c03040c0e207603c1640e0806540c0300d0070100103403034101000810754560907283d885040d85c56451901c6120382c0820240d40030441c0301c8001250303660b14600c40a003d0030100d070300c075110784015103001018007000810003a90358204020801541d2400501c80c5401e000c00c0c600180e45195180004515410303270b80001c1e4149c0308020410121005203075000740214010340c2d640400b26a20700402094802c11150342070304062002e0452140c08880e000008e945116200106404c260140450139403445d406a410000303001c0707000f640141d601030112142c6800c00c8801804141c1c558001140c1c1ca42002c3c0004041184204440600398400d6050b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355065971 1250 355064721 355064747
    0xb0a290d020d140706020c0303040609030311150a090302061803090415030c080c1905010e060901051b06181b09040503040819060c0804151503020a0b030709080601030f0f03 76
    0x80c074a0b0351011003115513580e00580668405845060001100c2e45400810b40e8200c86040c1c0e500e00b1032a0456408440e94180010101e0440c070541c64900d0344d260795080300d00d00c100c5d410400080c00c1800b40c28020301d0024098426412400001421159600044101c0c0ca80c01707401c0d100411061003512103104104c0190780301801c0c48552410105a00304040742c5804022800c03603100c0c02d180c03c0751000c01c4620000344075940c0892103c3d00c0030b1640b07081450182110410504041c0d0800c0010350311600103954600010805402890420070760150b0300720010301d51441103001300518950401281802c00550851911600141d13000500304001001100e02409010047e0307030101c19041020340c002d1102d0801101c5141c1400085014103200c0c0300d016200e240c0140c851444800c0c01c010340ba0041440504038020398003a04000b00158440350281da00508030700004540d04d00c4d12081c01032402f407580e00310900d16040b5000410106411405003250690861510f183c00e0210307103400d071505410010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355067221 1250 355065971 355065983
    0x409031e02071707050103050c040e010905070302070203030a020106030b010f0815062115010504050f2a070317090105010524190f030e03031003140a0f0b0a290d020d 73
    0x965204406000c210441245c4081e20280440d1300d41a420368924002c50040d80402020080100140f60036504840c0d0407020ba410014a854040c0e00400c0c10360f840102e45401503034680e40100104402c2501c450300402c5222411600350b0701708000036869505c905400c81001c90b8031301c0030500d66651003409281750b0218602011106040e0318240303480e04403159603090301d000b140c03000051038182405007610074542074022030881eaa442d00386400020380042803402e004007042801c0d01c3c0c02408130040c42c1060090301c03041c62001607400a614400801060300c1d03110790500300108115251405070ba0302032601585d4110000c041c61860141d039000341f16480003004004240400265000b0b000604648450360f800e11242092164460782c03840240c42c001c0d400000c10608001083c44180c40c100307805010400d507074080e01141c554040d98014074506540c040462000e10401c07040c44d2041ca01030340e00d82c01c1b03403840d01d40c606507030018915541561349004081e020711540465898900710030103542c1c401c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355068471 1250 355067221 355067249
    0x2040b04090c0f06140702011803020301050c0c060a020a02150414060705030603010e061510050d061e0e01030803272a0a26030d0507020307110409031e0207 69
    0x41002c9900c801c140c0700342000c01001e0140490320138441c5081d681c42d40b1140400390720740516680115000011105000c444010200e0f0201c01650203005441c01258010308054607401c0111400341005009400110024410819002c2d41600820308240321000c601d50003000f65034a080a0702e110503078188103069030080700b04102240c0d03001405103000b80c0f0160300070044840c0a40c500c40d0b41e40f41c00d5410003144a64130080c00c0e07903072403c01c0c040c04c611030051601034145248065503c2c140d518542080d0f000303160a05001444da0107141e000070080409540e90388155141d40c43d1360500f4030014001c0909160550300c1e1407449840e4142440c803611074007044600d0050601c0e07111440040c00c2c54106851040c0301c201001d0351130039801c0c54050b21140506084803c070301c60920702c0402030a92a80300280014080802c6103803091081500c5020303950043c541c0d41d1503914000101c070794030307425040c4914580700303000f00482e43c440500900c1680000c0d43c44d030f10303482c021801d07480e0030b140da0300004040e034200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355069721 1250 355068471 355068473
    0x10032706050103030801120b060609121b01020d02060f0c2a0d0815011202070615060c120512070e0319060204030203060109050c0a0f03180605040c0504020c1902040b0409 75
    0x41e40160304982c043d40d143c0845980754031403920b40502990015015810307003004155646800ca000708040a4010300c010821a01101c0322418001185c80130221085441fa01c0061365805008201c0c3c0c0a0192018000d5403030104090074141c400039101c2640b04101083d101c20007645510003046005031010001250b004050b40ca42d65038038000342c0700c0000707040140400d1010fa0b18071404996504142c51300c400b180e00c3c000b148802900582c00503070f081a128a038019800c1003044508000d0011076491000030b406901f0281c0c0c401c0c100c15036807020042c082011051000320540b43c1504150f20f1b00c0c003d491030501a000a1170700c110f116400c0300e060100090380c0d08010150340100100c034425010349241c4d80c1d84030a50005c0764000c07100b400b2402c03c10010b09070094401d20030b40b1940000e0f410000b0b80313102d2499540d00c15501c115412151a41e4600078030091100b000740e40401004d003101c042d0310709a41c045225441e1030016010000354241520310703a0465403540c11030313640400c000d00308202c01401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355070971 1250 355069721 355069733
    0x311060906030115020d02010e58020313050105090102070e01060e130e071a0f0301030609050f0a080d0c2109031727030d050c1b0c100327 61
    0x1401d04100580310b5925000b006c240180144840102480041c212090514800d110711030380c1c694195107031000e010340b05a0100e1010782410007001601c80301d50344916001006d24201e08030301441000b50750050201d1031020302103a1050b000d0f83ca003842c189454010140050f4a801c4142c0c0015500804120010401c0c5521880010002400706c0b0032a000c80c06115642c02180c0180c00360484d641c000e40723001d104a040311003c030011041c0c1c121085251408a5010034441e410a0308201d420360b86a0301200180310040020b03480700610540a0070488a03075540300505031003818840824aa01d816400b0b03a60360140080070500c2c0314100b24100041c291840c80e0000b0108031908130040f0702440078249203081541d02662003407101103c0031840d04052000030a104240c4800b61580d8031081185251024a03030040a016194286040f51901401d507a254008120303051b14030703003c0c2d0098050100b20394900d5a4510b040340070341000148a03d85001c14050410042185000700c00d017502800f0030090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355072221 1250 355070971 355070999
    0x9030f0105091e0303060108180a030806010305010b03061809100504050a2307050616150b04110c19031808100501050402040605090103050a020421021002060405060103110609060301 80
    0xd01ca020340d41021041d04030000c030345040c003009805513481880029010f5011f07014160f00440c80a200310103c005100f001850f060304a07800314009040141405100d5805005540c0540040034100d415481c004022403d1080c04000707000003940d805c40480d004540c140040704071550300074004d04c51071511341402c42da40c1c21154021030305904c07081c40301c040100a01d400c140100c1c5200380904403081c904000c1024a4010854107031624200001c44000500d100540c02d05050301c0d0480814010f000a040004840c40030499600704c00c01003140d02079484010a0304155400708002d01035a418a0f03043c02c07502d0a14000503c402807890301c0d00440d05120014010694070710412003801750b0307070302d400510081c2d005a206801c0854007d002c2444250f00a030451a80210203582c010308040d514402e2400199142c0c000f0354105207250710750790660070b085000c40c40650340c0b4002803549080642d5107a07a10001480050581c0f1600450546030b991210101d58010800800c455201d584507050202402d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355073471 1250 355072221 355072231
    0xf2a0204020d02042d060207150203130801150e01050f010507110604030f0605060409080307030504030e1e0f0a0308040b0f0f0310091a03030a051b120406080106030b031c030209030f0105 82
    0x2000b51020506115118031704181c6d03205501070080c0d2840d080b44e040d040c22483c00d5800a50000307021480c2c1c0e0030091150f01d801851190b0006c06c0302c00c1e1007a41030f24440c0e10342c1c001c01c007507941d81d0006100c01d8880500c0501e02c880c0a1070129079a0300f0604080186414007501c0503806074000500105114010030000c001d640240010001078030784c64108404c850323014400a203a00703000c0c00043c481d24001e501480d0300c00d000741415500101c444000072111034541000502c46154140c45401c50305002c403d4041a80042c1d661000090031515072814600941c401d032103011900065068224040000390303000400ea1070b050a03241e083c04646070070303501c881d4020ba0740c000789401202d1781440000b80800e514001c014010314a0f105540b441141c1071361001a4440005101222446020340200400d00308594015181034503542801402400080c1c11f07400041050705102c0c05a190f07a4000c00c01c0c401d05801d0786002c60100200d16000c0d0060b0041e400d2643d818003440001044114041d0130640c461 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355074721 1250 355073471 355073519
    0x5040803071b0309152f070b0f0702040c1205040c03022b060c0e090a061403060c0d0218060c010f061a090906150307050a0f2a0204020d0204 62
    0x141e640ea10381c444120b19502c030040d000503420601001504c1501c0602d400b54a01842c01d0181d4400803600a0703410580403c440c4840341203401a28000c10b0140038460151020845440c42e2250f44001c5036030034054a00302034403403aa903c03e5040d410b801079080f41d0036102c0c4000d00340168546801c050700361440c240b0081c2d000d01c100008800c0c10503441d034050418501500070030f0a0f0060b41d51103101c0101035841188003800f0010101d02c86640e50304550601c06d0a20345000b0606500b0440c030400c1280d03030802c40782d0080d4031038402c2c407421301117400690300c040400400050300c490301142c0001c8072020152525820020021700d054010106402040500204c0102480b4865981020008203141c2248486000034180404001450044a85a04440c0040141d590300444000e211119802030351070740003042002a0301a0440d800542d800700c511b440341000d02400903503540b50311000264030701a458000e0303800400340440d5950350542e03400101a040441d11251a242440c5819101d04070380510303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355075971 1250 355074721 355074737
    0x608070f03050c03070c02030f0109080306030c10140f0f071110020304140d0f050d17060d0b0f0a0603081b011a10050f070516060e01031103160201020d0504080307 72
    0xa094020b00400c0c0c062036000d6070603441c1d035460880450b101c00990204aa0502880d0010304030355400740540298540545001942c034100742c82054a013111340e120071401341001e0b01d0f507500f400e901700d442c0518200c141d018050f0f0744d0b44480040b002c544610202da80b1009004200d1009000c0070542100c800d400c02d89900714095501c041c2030380d8a004a02c2842424490f000107c2c43c54101141282a079a1140c5001c0320301e10005e42d9214248529421441d0007e448401d490443e00d1501010b41d800c18401c3d10400b40e103540c40d4450340500729009104008125901010031000a1160b10060086810044664690410b00d0610160011505042c002c0f5801c002090500d140742e002441803216005002074810b500c915010341d802c0d04031321440f8000c03030310030311010004c80c406200100d0801c0c10903180385003076030605d84003503d41070303841211504051600b0101030800042d001143c1d040700c880c43d000ba1070b441d81a0400c03406413181582c4107507010f0410092100304183d500166000701c03103a4480f80f407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355077221 1250 355075971 355075997
    0x19060b0d0c02070510031d0a0305030915040b2d0703020a1227020114070809120105070905220e030904051308030a150308070b0f07050c060c160507060807 68
    0xe5108494000e032607104400c0c5e040c00c440036010381c1c042056400f40004103182031030426503c6003841d5074940d058002c590000100031281e8018420b001c1e030307034034a004040128146a226010520b0004055071f000d054101c181d0041e1007005807042d0b80030804140c84d8542c510340705c04e0050280d0015071005c0f010500c0c4994030408410300303005506010b5401d581d04040b241d010864a1125004884c0c140d05024280c618840000b010200500c80c80380112801c1e69103403000c0c2c1c01e01182c080d0003405514141d151905121290380d001001c0740884a040720f0803847d428401040050f2000d400000c10320661910303030701d0802c1100c0417014040440c800c40d0200000e5803104002500300b407540343c005107808400c20003d94903046a80c041480c8a1151001c902031a8580c0e031000d03c998400801070f900340a600c0308000203030310440e411a61001c0c451a15605103010510801c0d503541d00a4840d00e440d40001c28880007080c42545038544468100c0121104170755030b5800034018204c286c440900081d0707000403120f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355078471 1250 355077221 355077223
    0x90515090c0102030f0f1c1e050112110103020408101a0906010c031103040315090c0b041206050a090210110d090f1806030b070e0901050f0901030b19060b0d0c02 71
    0x41c0004010380141d031408010010f1441d840e44155151581780c5400c0c080040002c0503c01084201c0c180e914000410581c2040080e045804a040481909007040010300c21341503c5c500e0600d4031580100000c580420000040e406030007223400100441c03003000c080f400821641e0300801305102ca00d010b05007104640c501801460030702225110f000c500c519040100181c0b00e104040b03d04000c00040e40d013017640366510481554450b4104004c40360301ca07018041440628181344000f0842260140d1505140c56030300031800034000800b92010703507228000b608200150f0002250365600070f040b4a112149007102401c3d1400d46a01c241082c8200c83c0083d181c03a028403904802d41302903004202020f484c03c103082c400232601104440c4590380b294400000502c0f00542d442c020280707507d40c91f405200c000f0901051300416442540308005980e0000070546034820b045045d00e4000852040a94662900c02c0400245d400c16424131840d0050008a540b41c0b44050104541c039044248030070400c1800c01c0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355079721 1250 355078471 355078483
    0x3192d1d03040303051b0f0a080712020a03020c04110d11030f01060309050715020c09010311030f0106030209070807170f180d0206061903140a02040b182809051509 72
    0x313002c90410000044800381d0070340082e826509034822106140107075603a942c1807072403101c1c08079449140415100c04220b01d080080342c1203585407001b09101c4c036054034002d5540300c8000303445000341e90740c143c000741c2601031008940004460020511205140d1074001c06143c0c4100d83c040f01070050364002280d410f04c28040c450389280c200005052150030302c81081590420641118190302c1845480783c0152106c4100394000e50050006141c6807810f03805160601480c126a0030040e45000310034801640c0740f100041e0840410b10b4400d810340d448031020307102807402202e4940c01c09001002c100c011080765002500c900d45184000c001241c3d01010580c0c1c03040061540030158001000048041c00c110742d483c0c07040b150050b40b00b61400d6581e101d1441c0c6c8c0d208415005419049080c03090b095040a0003140d1100c8001d485400c0c0340341c0b08113004140c24130040c242003200c40c4000b1129002f065441801c03400600000000c1003555840c0c902203549419041031444680100b80019082c0700003c074071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355080971 1250 355079721 355079723
    0x1306060806040305031527010611070602031c0b0d0b100608040f060b2106100f03241d01050402130c090e090a1e061103192d1d030403 59
    0x184c1e42c01c54403034180c0d483c00c000d0071788843e50f08800460041c44103092a40340b10001111440c1c001c11071941031100c0240351f05005900c141069002c60800c0043e944d00004490302e4410b01e0034042d02071880c0d040e0382005081c4c240e0700c00da40615030603281c00603c160748032154001c012003075140358069940c000503640c080c2c08607000750280c05400b400d0b00109800e40c20140c0030180040900060348181740b120003462a9003c95856a640070b9800c0003003214072400d241014080c01030b61402d0551455544691782c1048907084031401000d04d101307038000c0c2e0300d07034004c51000d440305a0083d01c10140c0c5180c2600901089070b060f4031801206c0024500e28603944503c410200090fa1440714280c20075004a01c00207010784041c58500c03500e811034000c02c0c00300104000e40c000c504525122041342d070804400362407001142c40300c03c0c80100240000e0b08101c5801d20440b140382d200100d514102c0104054001c400b510f01003c800038070060240e0403204a0780a0408503505082c5c00d040141c0d40018682c0d68012800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355082221 1250 355080971 355080977
    0xa03021302180405010b070c08280c090f02090f1203031f0302060a03050f0a0204080d1209050105101809020315090307060c1d0301050609011a04080613060608060403 73
    0x18080c44000c0c690010045000d01401540550340301c0c102007400c4520903848402e500901291034410010354280c403c2c010f043d550700038095404500e03800010341d000103582001d515080710b86441046002d110302c400820107948100004020008040081e41c4a412540d00c40e185482039113603a883c1c4410354000ca911480c00640c25940d5100c0300001400c904000300103080c0c01c0301d03800401070b5292001031641410340d950118150030844441004510060070403a803403030040c0014800c1600000c0c40800c80080c07840e103000413407050148400189044e500281107035080c003007004105c1c811000d50304102d84902e4500e118100c1c0040417001100c10541c00294150060000c10700e0600c24448000d0b00412000c1c00d9a00c5c051165076201d040701d42503c10ba002182c400b40141401d900e410a80f103050314019402409603151050004c1c0c5040b905008400d00042c00250034081d500b44102600c000c0d1071000110b4000f402c00c031413040e1291103200303411240720f802c1007004501c0c0100441c4140c06030f58561 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355083471 1250 355082221 355082239
    0xf02010806181b0f070530031b0c0a0c080c01022130040219120f0804050d11030f0f0703030f14030406050901140105150d090506040507140a0302 64
    0x43d40341c0c103000202185461040106200c03141d000358030080100359540c49a4000e00010240d4960100300044030107032040004140c5580c070640c00702d1041240d511403145c1c41072190205004408142c6030144800903110382c8248200042007085075082041940c404a0490703411b00c000c8001280c4d00c4c5030000c50290318011043c08814810318100c0a092480d00f1103c2840035100c6034050f840000c03200b002da80d811050174009000a40c240512110b07411110320355180700c7d05080074110203000098000003480c240314031a81d5000d00c9044c0090314054100201039130361180d40d608012109124040f20648039004000c1e062020300300c002003c4106a02210140011914544040d5030380e40000150106120910a14050442c6940000c610442c8203031381c005518109507281074210f40030345070b42c450109071402c01480a9603c4940e80314214990395003550307954422505000240900c590000e200344980f0080c4803c000740450000c042d20f4806601c00200c041100c2004030500c0c441c48089e4108501e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355084721 1250 355083471 355083481
    0x7060608060c1e16030f03050c0901050306010c030c0210030209010314010f05090405010f061205010b0d0201020705060d0b04050a02030718120b04081c020c0d020a0c0b03060310090f0201080618 85
    0x10003188400f000c0500c005080404040e000d03803804007001004c80005039000c013441c00d070076014414139800c414a00c07441070410301003a0010b0044e200c054000307814401a029000e04152140f1b03800d441203a4060b05850349803e4000010b80079402440c0b01c50702103810598151000c03041e802d0034034100c3e00c14050443c0054644014041c1c50000038005861039502d5543e04410804107000c3c420041080880751000e0b441c6d682401421500d65402161041c1c41c03807080322002d80e80c00140001522401c5900aa98581c0d0030080e00041180100664026050004000c0c945000b07a002e584629102d0721010503241c40349070b800182d28440d000d00d0200f03044c440c0c1450080381c0781d82401940f00c2d10840141d850300c010b07900c080300074107071120442003026000914100000000e104d900e04101c00d60000380303419000c682d6244403d00d070a0107138079100c41c404800101140d03007c01480008401d24075003008503224905102020218405041c5d020400c02030100f50759003080c0d04151140769490208010316103038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355085971 1250 355084721 355084747
    0x90603040f030c0803010609152d0e0d05060f060d0f060b060c0f0c0a0609050d0f081309150605091008040201020c031e010b010c200a0b0f07060608060c 67
    0x1403081c1034080181d89400d500000d45031800850203007009031034041d9250301c2d0601c981c3e00c45100da1000030412110810030349440d0016107e40c00c7c00a40c4824180d03000d40c2c1054200c9001008082c06035005040b110700c45c0c18030401207180c2e8003e98600401d20304035600c500501c101c0e8050f41c10002d14080c416480000455200d601099103400018922807500c2101c0c0d11503850302c48044203200709504100816101ca03d0107500c070000400550500d4100341e49000d0000c2e051020703070f200140a03a14001c004a04200b05202218a500c85950307500d03841503203804038880140760800700803145644194000c5001030150382a10940d03100101401d46101910b00c00303e03100030307019200301d055118102e44008507075400e01110303100c03801a50308440e80700130f25030342e49003550b1140082078140300c141c00c0303402d0100d195643e98028042039004862210951017012840060440d80500c0c0d801d080400d4106d9400d14035001020b0581c0189000d104c5117440d0840f154540b0f0080d102d8500280c1c08104400302200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355087221 1250 355085971 355085993
    0x10f050d24060806130501260a12110c0109050f13060b0d020a090e0408030610090503031602040f0b22060b070525060f08091e010203160509060304 65
    0xc080281d412080305080c0a01040e40d1a03044800402d03c00780c200311480c03d10342e140c50710041c070640041c852945800c81c44403202e1946499401100e0102488905401c01080307140700b4141c0c000b031034184051031818014044444140c3c0f00303502d0300480741c04400d103601c120741c9801503600042462045e00c00301003c01030b19090000e01c00051548485c40001c0b5580280003601c5121100c1d0400750b5510140c0000601c045655080701d0000c40581003404040f0700490f0549611081c251107903450482c41510580300e07400203602080e414440040c0c0c1c405110fa0546180b80714a20030303079042c00001c48541100c0c041e103540c000c03000d82005c000749544a0100b4140001d147c82c0f80d0124000070301c5a1225518502944401c006072407541c4003603065040c50a5038040b90400c60905d0b0f11500080f800c0400081c03100f030304890320008201c94035000c0f03040d101c0c0900c044842441a0891a0041c0440c8a1541d0103034204441c2403540d40d442c0c03080e1085560060b030486010802c01840305107160748550720419030038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355088471 1250 355087221 355087241
    0x90a11090f040b030a080406090b2502030f06100608090c010e040f020d050a090506090a0809010f09080a031d030a0f080708070c0b072105070201031d07060504090506010f050d 77
    0x140e150031043c0103640b000d01c1100c40090061110650fa2030030444040c2494105600a40302d904c0200510042859140900290080d41401c00d20146403a800000e1400c550800d481100740524400e208030b862a40c5011000c44070151908595643c4c0d00c8506502e40c404410b02c0c60106040035212080c0d440d2640c0514203124060070014200342248a10b00104c0300e0803101d139000c1540e070300c842d50f0a00c0001c0201e0743e40085210b0050803035411641d1036030f00e58001c5031482c1e0705200b410310556410901601071b441c00b901d404803ca0f503030921142002446040c5040c0d00340c19600c86084240002d0502150303004449400c11050099624207a55640c01d0b5400b00200340c49080c0144605030008084a030001e0080103682261520f03080316003044680445130a60340000b0215030940c401c52280c0140c00c2d900102d0302400d00080c144a52403000750820840c244030340c00d40c05400004039105400201900a031031f41030700104001c1d81e5003c019030303821034a50040d9002c104144445402055180c000350085 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355089721 1250 355088471 355088479
    0x306060f1106182406150c0307060203061507030c0c15020c09040c05101107060206151c0501050a150b0a020715021c0908010f06140d0302010e0609010902090a11090f 73
    0x3244404e151003661600010748050842501410705c105c51402841410b5483c1446009610f4488011080e9070750344244900105503d802000041032903482d07070f0f40e9841c0309480d0750b10680e40f09401e1600400c101401c90b011260b020f071100b0003089880d4003035003502d2481d00301e80060400c0e2240700d08000382000c00038011260803020310b8010416498420910380c10030015154000c800582c0f005684c14000203801c51b80031036100e202000542901c400390308044880c01e94065200150004025400b014039004c058565800d040900c9080340c0d0726070250140c6038101c01c10340d03401030301c440500070b41d40300303510900d401a4084a418054030500a07040412a8501d00440d5010081d0382c0c3c8540d6004a0b032243c01000c9004020100b00a260038084c03210480390315401000641c1c00c0000c0c0120209441c005603014852649452003094000d500c501d90050003079080b00c04030310700071284074041e00f200d04d400c902803500c00002c04d8050099000b8040d9944041c190b43e03080c51140002c1c0301d109800701c5446580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355090971 1250 355089721 355089733
    0x1090f060317040305060a0c1202070201020307023003070b04110a0e0c0304150902150a0203070c0f06020f06040f021009030b070801090506010e0a1815060306060f110618 75
    0x10b80412010711144000003040307031035600c1c6080580c20910010001203100b41007008200c04198082d0800c21600340c2641c006858244900040349180a80c1400030741284005030700e13003201c644400b0b1040f140d280500c41202e40c503a5550001d07440e4092400028000f8140e613002c0382c00140c0d16407402620f518082c10a003003866450059541d407800c250344160031001c00009110500842248003803045110b50414040400aa4085889a06c8401e100c00b02800c0124105041d00c4c400c0c02260302503500040f070160003e8030346000000503681c80c42114098480d009000c2560140401e8041c03041c1e40105c40e00c0114009034003444184135100380d89404100c5024000f20018030040a0107004180030b85d201240c0f50f0500c842941110005044c00707061003440e003880398180d82c07840200020b842d82c4903e040000361000000e1009010b40d042030001082c0c0b001d6020407440e0341030303108104860640d031710100ca07551003000548103041c01c0b07920540181c01c02d10004150b54011030b92100607016210403504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355092221 1250 355090971 355090973
    0x40f12080c0a080919051f1107030303022709010e0402010c120e0306060319060e030f190f050721020f0106151701150c050c0a09050106110c060301090f0603 69
    0x4141448820125540030010484600b1070400c070079400c11820760020041103a5045c000080c3d07c11140031348200c0f0b038824090303c0165242c40b4441000d040c5243c501181c0307071146c0303a18003d0065008402c5100915500800b05104595003041d0844418406840b81280364240010700c000c5400c010001d80c140408903070400002034104482d407440307400d20b41c1c074202c0c84000101010706000025000510a0b8482e4039504030740000035121a01082d40001c0028558605052550960080840c8100c1504001c22200d1110f0070f141c4007028088110f55550341c488820704c1d0305035658003d00e41c2c003a0490421403420420110b401349602254651801229903050244200c0d034255240358204400c42c0c61402c4241240350303000320b003036030f00d81104000114246d03040030f401c81c1c00f0052040701e0408004912048400740402880314020580c80600510f801a40b520021001350500307100c2c0070002001d5140b0844418001b08079403a4100f40200300518513407801602d8806070000e400146001a51814008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355093471 1250 355092221 355092223
    0xb07030c05010e0d2007051509010903020303040603050f07081b071104050103081801080f070807050d0c0e0f0301090f06200712080c03090c21150108070902040f12080c 74
    0xc20708040d5900c91140709071941401c5d6648170009010002580407034404d016603960320042044900d00d14200d04c2e26200d9500040354011070952000c0d4042c0000076010801c2681034001c648038807442c144184254072540c00c2218036980413507415051052409108040c0d09000380200102c40c080c8800885c40d100c104001000c555080e401214075200c0020b101d82c404085020a005c50802420045540e10b000c1c4180340301000e0003001842041104000101c459000303a003a070300406a00e61040100f0842ca45014190750990b00030706200d00c9500000e20500d01e014001c90311071980c00044092548925520f03d000b800786d4a41c40d0712529640301100391605113482c003814455020390b5000407001d40000b00030b0091a8081d0494040030420020080004400210340880c0041a41e02c036240405050040c4d0700048ac8440032442c0b0300902c030140c1c60152a074101c0c54140e400e0182074070621542c07081d001d41248103a210340202081e44800400600003680c2100d240070f0b020b200b9842c60554110440c17 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355094721 1250 355093471 355093483
    0x70e060c0703050105060d08120604060b0a020c0a0510051e04091a04180503120613020301030f05070503031c0b0409060e16051806040903120c02150f010b07030c05010e 74
    0x550656809501c04009022090040d00d81205003035030001000d141d9071b00d8500e014868158695520702891000c41c040d43c485500041c01848000750132074845030f066100035161020700c02c07880e224146050010400c2e2502502d40c426261090b2a410300c3c00006050718405490024259003480d50306220001c0c0e005590700844500c080440c42e1002e20342c000d003040104680c50140c042d8000c1c81c4c0b02e150781000800c000119840340f10120340680a075600c4000152607a902c1c501c0340c0c1741c81400400000704000865401c2d50307045200314199a40246c0b61000d01d90b0328000c0189120350004005400724011185030f001941814000d030012850715007544035202a03424018200340160300482100303984021900c006809407008545000300300461010200f010740001e00035500c0b50760b540098804060090402141e07030204058248080b000702040030307403100c2d05004c0491030600300c7c0740040d00c451100300b0854103072800c941700b03513042841c07030f031811504201c494004644940d81d4000d0900341c08410401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355095971 1250 355094721 355094737
    0xc020c09071107150905091003061404030206090c090105040e0a020301062d0501080106030b12060a0b010311070b040f240204030309051f05030c0f12070219030f08070e06 75
    0x14120700c4510812125180860982c0140d00d80102501c00b004c2c0694403007040011250111054483c50f203035400b40c10f070554090b9100524540c80d05aa5245908800d0f0815120341c1c020b400b503031150350303824180b5500c41041d0000f040d030020b46074005020500c0d007035000b402100d402008a80c140c418a44c0481e003195455042120013007105c3c006001082c00d40c4510401020824414407201841d06002a150a03018000d69050548840c105016519140741010141c2c034142c04031406800c0109940300105098075505000130300701081028030145070011100b50342d40c8030b030a000307541d940e0303440754541c0d40c031010000c890600ca05641d500000c103600e54071142e00c001c100c0005945500e18907010740f1500c042d500150040708001c4510494107650282c4000c0d01e126828030700d569070385007002c4034007603c22108035007801400490766000d0460400c2a43e841180c01c3d4084503802c49051003480b500d001a000d0042c00100c0c01501c003c48207100d40d43c00768000b82241040c071919000c500001e000340d000444 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355097221 1250 355095971 355095977
    0x100302130e011406041503030c03050313060c081b0903030403080a140a030c0206062209080f180a080c09010614040e0906100608070c0305090a0e0f0115020c0609040c020c0907 77
    0x2080c441e4918042c07086c440e251b030201103c641401d10310f50300500f40c00c0c0c01150241c180000480083c1108400c80b444202072540000c013003142410a20025211a4082e10b1500440d450710a030403a1b085074400c21200c2004c4010300541c00c0c40d24641d41d00340c055100c00b00210030030001408400c015182000a8041c00f000c07500d02040c0000c614000a01c2c21000800e8940f0600645c42d083e01010f2100145d0342c05840140303408141e071602810113040c00d00c41e500450021140c0000d189202040100030741d0703014001102c48082d02607171486042e40c1c0e28070400d00568400c0c0c0c4400100500c0c1d0140c0c2000102000e2080c0e00c40c2000d0340d034201c4400d8400c4c04c95011059402c12380411803200490326041010745018180486241030812006013000300495004052003400200c0e6041a960340d4a120014106060700802e50f180044150811010a2040e6481410403c0084c0065030010411003024100580742c6030504500000b0040600310101aa00c00d5001b00d2501140c02d803111008140b094205403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355098471 1250 355097221 355097261
    0x22020402090603090304090c020307031d220b091302090105090703060801021303050105090a0b07051b100e100e152a180a12080a050d0c0c030e09100302130e01 70
    0x100c01002508e0107044801c045400821803400081c0d048062001a490414120f2410300e0341c0001040440e0300040100301d1608940322010f0002001c0e0700240b83d0b1078025100070460b0b469101190100500600b8000c2d444410400184058104141182d03400780d03c03458080744641d951100c2c2c40c2240d10a000f1010f10714074911050060050034000c40c2c1d000300c1c0341c1008118850f603d03183c100554030301900505c10403000140030312003130a44c00c1d40c2c00c0264070703814107a840c21542170307954000a210781090094035006820204001c5905441a401505409406000340c111040350703114402400400440d18900c4440745107100d02d015042c1028085089015203aa46004107c12030581034101e564074403c10451500740814171078090743e0221590300116880d02c0303000d0014251207900501040d080351034501041410010703406000d6030740645c001c2d100c1d64001d003c5071050284c062802c90b5030003030b081c003003040070401401c040b0702c441d001c0300700386000049100c001840c983c2500c14440800740141d04e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355099721 1250 355098471 355098479
    0xd240204240c020d170c010e07060906050705030a0e0d0f030e211203090f0d09060f090806070e010201021309060509090105060904080c0a0c090e01050108030322020402090603090304 80
    0x166010102a01d158100344007041615030000d0550641d55600504220100d11a2072a00304030320241c40104604400a102c0003044602c2103580b1205481004000b560710b02000039510301400407035144540203006140f0302010000d00b0384000360955200340d040300e1101250310200b041102a201d00318802c1c0d45032040001d40c4020094441d6640b10303a1440d240703060340703014500c03076002841d025100b4080f20743c00d07181d070342d0910081c0c00c1c0039450300f0500c650f01600103c98080c40d0b10841d01c20031303644544c4404960100841080714108030502a0712040d03400440403500c52405500b0160001105100240c40e16000b00b20f104c0f0a0203182c0c0c01071448545850040c04245050490194800c0c03119000708660300d001c80c000b442c2c9041c080c0001d48404400119184d441009120720400d85410150407890325640704114001018207144003c029440c15002082c640d801100700c2c6d0281145490300301802400f0f8001e0444851f4002c1c0403a80941d08000c6510162240c40c0503500ca5071103030001d15210b41c94 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 355100971 1250 355099721 355099769
    0x2070320010f021204270203010605120a05040c06051b0708100f090507031b05040903052802100f140c07120e13020f07021e0a060903020d240204 64
    0x4010b6009540000c5102100385210a0070b0780d044031544d900080080e00d5045038084491745403200e400c0b0303043c000000071544a030048014030540103c5140d161341c1c3d43c4c4510f00303a0110703a020341d001062420409400c000c40b0f44508050300840400303100d0304000c1088150b844c1e2030140150b0002c205a0881294402c52100600c0340c1d070030f2826141014841c0900c0d540d1501d450301d241d80401010884050038400c001d07808025090081c140c090300400c60004203003005001c98101d81d50784a0154440c241116202000c5522402018850340041400c040d0a41100002c0e1807000074507103200740c0c0c0e582020f04c50340c0024103c0d80504012812580e5801c1142000490f40c1c0b4803106201c02d010554824412503100d107150b00c5211810ba990050b215510303081d1009941c407501d20b010f907012010240303004114414090080c84103104541c00103140360382e42c0c400d903074882481c80301a51103c4d01000110203c2c40490000ca0301c883c5040b240040c4a8841c9296001ca030480e410900d10300b00d18410254416403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 355102221 1250 355100971 355100987
    0x90a1b09080d080c0a0809070902071505060d1101050a03020706050c0306030f030a050a05070606120303050108070603091713080a08071a010b07020f190305030c1c0207060f0207032001 81
    0xb0303030300e403800706440d1504541411344122040f0f60708000c1110001a08101e0a0001a0240c210300304c09560355111420101c400380010584154101e10f8100896003914110100b8403107990302401130000d1115040065659400025045040c103400700311003000203d003845a5445a407441e0500350303c03400c1000606140501020280049510400144450701d0f04001666940750723040c80c1c8950386104a141001c00361007107903c01c9110b9101619031104150305030f004a8162180340381100c00c10390343c501d070440503110a0500542091203180c04c0b403003c0709249005140042e000282810815030b207295262030700360800c4098a90400204107001080f09400d200955051444042e61540d4144102d550f850f120304030740244520505184040940c40f4110312480d4a02c1d203541d6440030313540d203041032616035001468130011030003500054080c5051082206503080481e07030044c00e48a0610310156036105551998005604c26821300000240c0400d001d0088801500a502e4281d1032010015010700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 355103471 1250 355102221 355102243
    0xb06220e0703140c03062230050301050d290705130801060308030708041109180c0405011202090912030c09010e120d0e0a0b160c0b090f090a1b0908 65
    0x1402c80c07404d0090b50b40c2c0002c0c201da0040300581c401c034003198044c0e0301e02d103072403100e00001847c1641d46140202031020b1004c6000a004040701e00d0f094003500d851040300d162209024060340624039541d0070001c03c500d800d4254850700d10080f03442e480c12140c2c1100400e580202c070440001000022100051800c0c02002001440d01d200240071041c1103644103081c601008210804002020000034203010441d0840241c0071350181040d481c40c107001d907003d12204284c0c4890070440c400d40e9240020303400d00d40b192904885200d000c044803d90142d080080215003d000103466102d801584191303401e5801c01180641c031540c840580d078203041c41c005004000c0b0359800c18454074001e0841c880a10340803500c9440500a8038010820720803080002e444444d00d070b04251940d86012403400040f0807013410141c52580650b803035003c815604c0240001c58800c2e071030501e40040d003000022075103042824010350400d542050105002c4000341040640c2c501e03407540390340007e08000d002c000c401d900b44880c2503d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 355104721 1250 355103471 355103473
    0x503160b1f050a03022b0c05012c10050d020409050a050a05130602210406140907030302150403030b131b02150114010c08340b06220e070314 62
    0x6528000c000b59050702071380b0029014402c030a80e50a54045c0d030f542e00941c0c0d0180c071400c039201c944131428098070700380b0980911404a01c9071313140428a035a20107103c400c0280c1e1f241b200d0700f00c20049410300c9560082800300c401401000d000c207490200aa001401c00340030301c031500181501d040c80a2400303862000c1c0c0200c900328505001e00180c640c00300001503031581c0140d00940d444240d18020326203130803556034110219690320284410411590000c2ca48245081020440c9458100e01c40fa01c03800d00d4030000b409079024800301e0803c0c402100189510070701078100000c0020a410104100410702040c080b44136980d010700303c0304440b90150307441141400d807000304002d0903041600c000114040c01481c1d07102c00341c0390b088040e0b40e10424064903450303440303002d80380c0390303507060990450a503194401075188445200100c0d0030f100c81c00c2140b400203a08401001d03c561070313400034080103129210303080d200a4602214001807402500840900601480c01460a9859030030710000030802a00c4400039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 355105971 1250 355104721 355104781
    0x3070b0430020f010305090f01020a080a14130f030201060506190216050f0411070501020f03012103050706020a020c04060b090405180a1e0f0309030212010c14070503160b 75
    0x150303c0380541240c00b01020300300090b054840c1c000981c90200485500342841d80001420b0102c15403189180c0d002d1000042c0500495030062400c0c0d00c4550304a40c2001d4020868580300c000c15061141900024000d000004d0180d0b01e80700800c4c020f40c0012074944007040600c030342038140c6030304020362a00354660342e01042115040500041d40030003041505c034440c0307484042000794503502d10b048a0506e40d000c0c0086540384130b410344401c51a0024070030550007041a4015607008030a60840c55400d65265941c0b51030218150b440800030341111810300110b20814880c141d89803554840d180103080034608058031703074402078100001d0341c000800c0e0f441054482d04002002d1200040c1da003903032641c1301001001c615019402860041c05c4064050301ca000b02c90010414150001103001c281e0303000391401d0a91015000040d401d86251400c0070300090400c0c100b103100001d184005c0c1041c1407084094034078120144004d00d443c5da0300703400195202074094080c841d095041c0300000d02c01c401c4140030001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 355107221 1250 355105971 355105973
    0x6220507060528081305030f03070801031703090c011b020a301211031e0301062c09061809010e01180c0510110604050106030b150a1403070b0430 64
    0x4800b02000d8040110030610341758907410000144165200034031403d00313035030300d0b0316204d00b0082075001c00303100944603288100300d40048144507508aa1040346032070000c05c2c010107080300440b086524040e011500f01085100c640040e502d0810080c02010000e00e00d1a00001d40680c0040b03c4080042c491840030641c84484001400036408950b18900382c1091040510100b000604610410101c19141076411803010b1820342c402d0007443c140c0700c0c40d139a01303100c91301201503150b0010252400400f2130703100c00c2c01ca0072552510003107696024001420520100000e0f000c1c482007104280c6065045944442c0141c503104e02c24071170811524045241040100000d4a8005c10b1030080c3c02900c1c0101030002c3d1014256000f01c1610b280401d0b140c0c11030302c3d0351519042c0a802407005010880e81a400803000c40c000200230ba10038800d00300c0007405e10030100c0c545203203a5a10f50744002d156415014032480001c80700005d8010b00010185801c06540f0300e01800c0e40a00c4800d42c5d24103602001a48546d144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 355108471 1250 355107221 355107227
    0x506120a02300a060f020424020102040b0c01060e1303120b04021314041a0f010509030c040501030c1a030705160c05030d0509010314060306220507060528 68
    0x18881d015111400b07050b5090031a40781c2e08804618040344061260280000c2d03200014400a01900070207040205080c01c1c40140e040e0700c00c601c00d40340c01c0a5820304084546030900d0404441c000da81c000180b85c242d6903031402130107801090341134500c2d0b5929402044148403082247d98010300094080c8101c07245642c024201101014004603a11359484401c58151155412604103440d065801784005a907a007040103180b0541e400b0500944c1401e400b1180c1c6d5001500c50a122a0300038a40c0480440e008011100c58100b42c828541c50301c600034650030f15403034620a10340654011080522907504020500705003446240e103050001f4010001c10041541c42070584402110a150400081d6014240000769801d076400107545801052440464981c1150040c45030754001e0b00c06005554000c001c114a010044545030b4064102900090096400304c0c03800b01d42d2000403085010f410450740b2500c0c5811415000540403540000d2103044400000c4402c0590090b22003e94600300030a280007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 355109721 1250 355108471 355108483
    0x70905130203072120130903170903040501030b01020102040e2a071a1906060201020307020111091305060d0f08030f060402090109031101141204021504080303040813051c0204050612 80
    0x240590004400d901d10b02ca4507080e0b42c0801c5d41c0010904d81803468441480700003030603024421004a101c0001c41c454070500050618405ca13035100241d810540780200540107407224025480c11954208400b040b0009070101d0b1170f00a010040b1a54441400c40146429044410004018914007480b1503000030340e0b019110142d103503d00c12000100d0b10b8507841d00707000b0044001c950000d10306044011a2295055028510441d1320b54028003140030b005a0300061841001038180e00041051a050344282881c0c11180d000311010b400240e00782c69a40300c2d0010020424002c450300c800000901ca48901c0c4001e550f5003104040343c007140381120510001c2c000401602c401420700c003811140304a26030140e40d0490039904c107031b1006541c8003004d404506803c43c0c129001c80c41804c54018042c1c00c0c1c1202801e50307060b80c4c0c50900651941d01e4a407122003554000250402241c22216000318007a00c0c0c40034486045560609604003008443c4100000d440c4003c0580f4050140c1d41100581d40500140f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 355110971 1250 355109721 355109723
    0x3050c030c06030c0426030c06040c0f0e0f07021207031106010f0b07021012091a010e091e070504060e0411220b030a02030d05120f16030e0709051302030721 69
    0xd10608a1b054800c603601001894070b01c022503000c003041a10050301c0101d50548168030480c10320103495220102d1400c01a0b00f030003200300d90080c80d000148418002d02e206074208040d4011510b4660103440500c0482e8001030044001418851a43e0a031a1040060b2405400c41011a10091b400d100000f0030714021084040e105030000da0010082500412030540304040b40403051000344041e06000c1c08803001403076402d140e05040c800000701407841254182c01182d0200203002d41042c984080c04400c03016890b03c10a50280c0d00300090b2036912403086100409507030b00d1305201d529060810f2052111035030744860040796000000c4007280f8007005800e6609140000c00502c0390b21403004a458454907450003501445480344600c1c0540c0c1240c003134140c3c803414403c01d5103075a842242c42c0d142c1c1d0500f502c1903210031908080c0085e13458002c0c1c03c160800c010840c102c840c02907480d920705050303400c00d8843c0c0b0204e0041c2030020f0194101400954081d00810900594103c80c5506c614413600300144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 355112221 1250 355110971 355110989
    0x190c0621180c0801090b060f090718050901150f170a021c0501030b04050f010905060408090301090b01060306050301060b0306030a030e0607080706020d1d0d0809010605090103050c030c06030c04 85
    0x4840301e0350320500411410316080a5014442501c07400c12500804103c0402e42d83c000310741000808074500f0105070802c82e64041c060507015180c2c1501959145490035004003c208101e0020516480e0b401c0c001d802030148210804e49414040000340501c40c20302d0040301000103040d001c80020a110400a802c4000c0700b00050340d50305142e04244e03a41030307058084031980d8103010000092080f20658940602c1c000c605641d03810581607060380c00c03664039aa004106410800c0042c02040e840c1001e0100d2100c09400131902d035031950b99241b203400d426049100402e947d00d030144454102403107444040e0001640007407450510030300007940c40135020b000400304003501424100c1600e8800940e058140c3c0400c149403900d8480c94958007035003002000503015454140281c4804427814402c0409004e890081c14074071201201c212107030300c00208002c0e41992162070004441e26400c40450003580102c014184a5104604040c01d020044115911502c1d0501c02d0103011544070085070100e515400b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 355113471 1250 355112221 355112231
    0x90405070b1c020c03180603010e130f0203150708060303071a041a01030303050105041406100e01020309031b0a0b0a090b0919060e151e03060a08190c0621 68
    0x9414241c1e1051a1038800702c0060000c100d00d03a0f80240000500003c0f038031001c01d04080c0d080342d014062603000900c12140c055881320702003000c00d2034070014002c540e4002e0101c012844015004a841e02e10310130142c0400c8100181000011980101400e400040850203903151904903228000321882000010074850540400300b403c00680354480b12019284503601503003581c2d68200940200706c24421140610708140c41010303c020319408540c402e00000b0302e010803501a540e4100c80034110701c3e00d0707141544410041400030b564100801d45910701c000c1260796040c0d4800c010700c90092103030f9010074000c404c107101c080c41c103c2d00300c1c0100e810380d1112003c1c01d0722074004030005a42085082500704904c4a04840840c160f94808130000040304241c4200003182000d00c5c0d0b032039180c8207442c19402da41281800b50524005038400039a0021001031905d0055900d42c1c803103d00f000300c5a100321203d40c01d0b6000c02010003602d043d6590060034241001106440c0d00e181740e1168440710403080c50ba0664603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 355114721 1250 355113471 355113487
    0xf030a0809100606020d030b0315280e0a050c0406030210050a0203041508060316060f0c14061e130b0703021b0106180e01060f0e42090405070b 63
    0x1c00109001c034590020500c203c2d60b5541d0042c3d100c03080c3d04501c000103401c146c00317820300c0c2c20002200001c0348160b221202c4182e0381c08108a2a038241501303a05081c19552007002c22040560046030325240c403810203400e0040321450107600d4000c461680c2406030742030960400150b41c805040e8980082c40741031860f0b5881000c3c4089055100e0f0b904540c8cdd00c10a0b0005200900e40e200f02c450748038203000d41c2110b102040040c05401c91b801b16109000029070300b04200d0041921aa0500c040d0743d01c9500d0318000703984a000c45508000d01143e501480c0c0410300403410288140403080f580000c006030814161900359140d640443d24000d00800526030009411019103072102c51115061101100801c0506d864002c1051000c1008034040300150500314034040300801882000111001c408919240754900040005001c0c0c004040c2d602c000c0030304004514100075448401d00004154080e8580410300e040c1e601004841c1040c51800344046000300300c0080c4000440c2d6081e07540686000e0348034000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 355115971 1250 355114721 355114723
    0x8030a020721031a0409110f0d0c080d170705090d2d0209011a0301051c0b0c04030c090606020d030504060b0d03020102041404180f050307061109040e0f030a0809 71
    0x9451142d035510340c03541d07030101c602c0c1e80c0c554041e0086106601180c1a118100d1003088190740c4080009801c19146144600c2189000094450600d1020305240180045130320343c3c00700d00c021648510f00b10b40003410605110342d031000b81041c8400f100041d0854034145524000c10328007640d0401801084514841c4081c041a01c1002056103c40303034030b03a041c8a105d2401d510070101219400c0380035602d8540082100b808007140d401490803024070041c00e50386040704008480044181a10041d45c0c0c400031040810400039400744a828202a4503a07914550718081042d0201e640c02149150702d007103000e01005e503021039601120945454086855116400c20000402020f444141c3c00003c0310700087c10150190042d004a442140c40d1400102402d01803105492511f180140c2404640300018000340c11540c900311010302420850381440b9080da5001c01303c0780c075845001c0c84420b021540214526103401012482c840d504003900c440302c03213858666038034043c154540003480103000009101800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 355117221 1250 355115971 355115993
    0x5042106110711090601021b012001060f060f0806090411030705090702010b01080f06031906061a0c01180c180f05070c0512070c230307081b0d08030a0207 68
    0x7414810042c0d4406051402d00308155200c03140034024100ca000041c400e60002c0f440c3c940884100f4066214007400500440d0700300104d540c0404030341202942c0301083c00c0b00741b144d900039114028030108a9402c101c001f07040c900072803070940c0410140e6030030000c00d51140318100c0c0d04954000355840300b000c2c100000070b041c810180c0113580c102c6845010009103030f6054200c03568042080c0c84456442e1940f400b0344408610480b8507a405a0000c160300d1781d9070060039000360130903001d500300040c501e071a2401a04900c0010780e01015285011802d040404003e10a06000180c0d500741c80c0928203007a41c5081000b002e81c441d401d481f00e240d8001c4403034448203400c61101c504110100b080b561074240d4001d84101c1242e842a18284140281c4002c00144402110100c1341c01c16402c1d00383c240f13454020414600c2c4020403618015083c584200e013074038104400e00107001007101901c80084100c4129210030600d01665100740604005000030500c0041201d420880904002d6520780032070402c1e00442ca = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 355118471 1250 355117221 355117241
    0x9150306040305030a110f04210b0108060406050703052404020c03040e0108070b04060e0904061b080117010c0c0b090c06070f030f050a05031f080f10050705042106 72
    0x4000d080c1000101640000250302ca000000d404100c0b00f16141c2c5006440d0143ca00c240c18a0a000c11042c86407002e44000c4a0444400e222080548000c0e640c88041904003a848641c06603c103105200400545000d2140d0041d210718007040305203085030307030556600e02444541c0b460300c609107021055904c40f6011126161243d41c2140c2d5255aa12000001a8400d02c1141c100f40100c0c0c0012038860180000c07941201c00a84d1103100c91400e510411416680240044910b00e0b0b590412a0794003241613850081c0741644d44826280e985014562032181017503000c0030b00c5030391419a1655096030451803000c030031504088811078030781d20700c861380d85058038802c071207a44140046194010002103040f00726105200b0f507614156201c1e1484151401d0042e00708203004124288005076a501000030300e00d015114803000300c021660303a01c40031800c2c007001c440d810104c1d4212284151000990b03008840d000440d44c41c20303601e4149000d281c07000d4602c0e89500c1000d41c148a11018060114a8014610711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 355119721 1250 355118471 355118473
    0x40b0702100c0503041104020703050d0203090109061a010e0406080304091a0306040c06120510030602160b070216080a0c030b1008070f06080a0605090711030d0207061e020406050405091503 83
    0x3145499001400c0c03600b0880781203d200da0a02e500840c10301f0140240c9804640c50f848043c1010703000a101006900010300c0781c0d003030390351300d03080100810440e000308428269180e0100304110482000103009282090030300d23018600f014000c204c0070798008101d9046982000740050070400c00344200313410149180d03d40d0b03414410001844103001044825a044070300e1612083c0c2e8081c0c41d02c014009440c01100c2160150f0030701b642c04c10104030340e500200200d082c40f08001214282c0d685d90948042c005950360300c01031f440154601c20101000d5400000f03000310a0050422480c580c0d59541d01c2c00c1680801414a810744010800480420000700090006030095410007030321038000405414680c490400007404940105a040c240ca10070b80781070381c101038000101940c070480160340d080e82364641c0725050f2208210300724030b001061018041c82071289402250300101c0d010b03480300800d0b00c2d03402e560040b441000200728058000701180d00f00d0f0825108003910f0b50340d100d40325170407840794402c00b501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 355120971 1250 355119721 355119731
    0xb07120b03150916060c030e010219030305011409010e13051204030302160b1c05150604080109020109170309041e0f0e1c091a0412030c0611070b040b070210 69
    0x60720903038203859124100000880310040c10b4001d030800701c0d001500c120000302d80c6610720800848e106607aaa0344142040c01102c0310403903610308884c80860800402c1d40002c0e500c0b001404041d07082116058400000c403031516442d41010402c281408001c2c0404086802c010050820000203224004090559480303494465681e814040d4807200c001c0d1650b120000d035510b0100e40441d5120130b84155200c1d9114420140d114180d1010007040003034501c1c0c030740c0c0620000d180100c0c0c0e075500c024405041a40004684101180b0002d031200e0321370b4210b48041450030407002803c043c000305688030568200c60103d00225031650440300356120a165001c6642441024442101c05401012095000c401222608903120310300600c40d010034081000015900d5908003c0c116450301680403480948156528082e5140d004103101014010200c01007801c00c90b000051010034440ca201c203c20300ca00c12450000107a403101c0101f18010001001e556202000c81c003c0c034402c10a1401c2c1091101003080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 355122221 1250 355120971 355120993
    0xc010e060c010b0913120f050a080a1506020102040e0906010501050708161403090307140127050414010306060501140409020d11030702070314032109190c090b030a0b07120b03 77
    0x1481036556501502d080c0c040074046c00032288103202502c403031074040d500c2c1c2d03081c4104585e0464203006c01a0210784031300e40715004030035149107203a0741700018030709600016515803034503000c4001608010007401c500c0d0440801082141d070820101c4002035445200540d4030400054020481203000388080c002d18a40c540315070242000000800080208804540e0020f80e98403c0050310888280c511380000ca003003030051814141c50208043c0400b00100007000c02c3d842c0d8001c076003140e0750a04407139680c3d44c14a0040090002c01e01c1407074060b080a180c4030b00e484800b4004400b0b580f10720301c159000300394005141c0907002d41700ea10852014506074003807640c2c0d06088034000d41d038680500094640100d248207d011103d8000100c5114402183c00044034544009400800c0c41c0000d0071840e0317070f0081042c0880c18200c0115010030407442440c640031890308000907203040310151440079000f0b85c44009140b020800344e5540d0781e4005070328900f0300300802104440001620303413001c07802d80500c1540c0800b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 355123471 1250 355122221 355122241
    0x70605070f051018061506021c02010912030903080c030402150a0201090c080d020709050f0a05090f150a0b0121110f070503090415031703060120010504050d020c010e060c010b09 78
    0x60320784d07030260009028900060b851038550108500c40e400c0503902c02d001544511490015107800c480351400006810031302d9440b411814002d00400200003079840340071104050300500c06a800c16400c21540d030031440c1c10781c080748040f10103c031100304a240106a4400080c400d40103031844583c808034039a41169104440c580d02c055102400c0c001d4002e001004c0703201d19603845010301c01d15107252500500c5d21405210001041b01401c040c2540c0101001010a8241080b5104040c0505504443e0919044008108941c0c8840c140350420a4140c55548086c41034101448040e026010000710b42d20441d000e9403c1c0d224010a20703d642c04082000f0082c4070001c4040c0c124400113840a122120100c00f0511001d40d007404014009480f0703c01041c407141c004e1010350f44c400b806040100100200d01c0300003590100c42940303282169100c00422042080034001d2a00340c83c1035000402100c004480040c1c42c58038070744915801042c02152504804030250002c491000c030141032444e06040c13484800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 355124721 1250 355123471 355123511
    0x803071a010504140c0c0321010e01060806031b060912030c01060b07020a060807020a020d0f020a150522030210120b030c060703030506040b040c050417070605070f0510 74
    0x200c00010304000a01070400c0d004c2e4450018a01c1c0356510300d80c1c0c841491002a03000516112680d1005019140000307692159000d00503440307810111096140c038500c113100f490140c10100070024100c091011540340003a0030f0842c034603d03c007030b21006500e0101003242401003007003441c0c3c80000c1a00040c00c0c403401000411400c66180000e0011baa1110100441d51007100c20007500321660b080108615071003040d07429000b6610780305413048040c05400265150f0305284040e039030900340d000440c0451030b080e14104014101c10a0031f81915020313040280c4140a40d146404c001e0320143c03058405a107031188401b011b180c0c01419049107a92540004083d0f80240d07107090412803510b0b9400c5064900001c0080400800030a02c40c68000142d90440250001030070707803600507855a036800c1039503071940135a82c0b0042c00384d40c0303d03616545090407206001007000410700e825008038805110082e0701c1022289100e4000001c214103881c58981240341c40740342150501d00602d001800f4600031015616 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 355125971 1250 355124721 355124753
    0x601180f0806090c0d1202030906040b0309011d100c09090203070306230604120317010e06030d0809071203090b04080309040c0314220512030a06120b1b04080307 71
    0x110381283c0d4402d01c0e4140c0d0340020f82d0750258040b40d40540d441c0011030740303d4a60954105881524146000309000c07401035081500a0301d5032000120800c41c4402e0244100c40c0c2c2e128030a000c10484d01c8030820f105488034001c0040d50000c3c1c4c1c41e66a11090a4000c42402c170040c0480e50b0f08540d41d01d0044001402404140102108440c0c0080c60103002c0010403c24411107500034241450140750450a1044074007000c0b0032414404070300c9800382000c800e40382c200d000b85044031094420b407030102c0c00c144c1004140c03401c0c003003400f10000600c000721078001440000e660150002801a624a003001e8800310300582c49452030343c0d0005000b003044440030001d40100d4000365000d10440308490002e5041d620154000c1125080c01800110b0030401241205181d5000004010091f00e1903100c507070602c0409059080c81020010903c5290780f40c6100e020003d00c01090030040c58601e0303560f44030301080c0281107022014041e1140c0d60840030003104840041540714100d9540700828900b010705141c410038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 355127221 1250 355125971 355125973
    0xf0708030a0b011103120a1803020106030201020d05070c050d0201051201060e0112060308120712020f070c0503162d06021507030501060504090f0207080a0c0b07050a0c0303050601180f08 82
    0x100002003035004000b1311241d1640030019505107808440c817590302c007500505441d1b6842c4c9a1070048985038400d81d9801b4094040e9002046480c2940006445d18500032075490404c40c04100e03603000300708c1c00c6c1034000545104a8060221113901c3c00100c8640c0909613040751f1030440b6000000e61241c003c4003c03110b0308020307240c030118000c00d2460203007121254400600040820082d030550b4040c440000c03544030b0510b0408070f4006400311002c00c12a000b400810340c41010000724942070011444030304c0c008150440041001841c4141c00780c1d5135285d14460324080109140e048010382160b0301c2c4001401c004d101b40340400c5075881d08001e5950140054810b03140400c000840c003113510a0041d01d05036001c81e00c42d54a407920340420714005110500409515550a0022000140194004180400b0310b9910503030410301c1e6040c041125003010b0803e03002d10404100038080581c0041024250941500b4005125a110710040e103072056200964256005650320104101c411a4900029116940 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 355128471 1250 355127221 355127231
    0x40b0703080610081f0f0b09120d020304031211060c0a030506040c08070c0204021b01090203160e01090905010e0a050d0f030e060f1e01060e01261b0f0708030a 70
    0x2c020300c524890a0303100c201c00246070b070000030075908082060103454007421100c1c040e0140e503060341c0c003581c80369500484400c0d0030000c1c03d1820b07850a1218602410140005440d0101051102035503e01c40d0744402052004101d4a20042c5d502504a85403162804001d44402c1c1c641824143d030164002d00324000860b2405011813800e0625200d810440d80351621860120780b0748503025580d069801c00100d9106400304a82c0e040781c17000d590407020000e142d40000c00d800c00c5a02c109070805002c0c806840c01c1e42c0c05050200003030700d031031811141198080007000400341d40360b00b810350140034594450469885002c503442c00b000000100e40c41c45000c90780d41c158005c414844d0850a03103480c1002407006034071803c082403c40b01c01c008910741101007003170b403100d942000242680d81404241c0c40100801c0010360003130610758201240501c45210300c0042009a018150969030b403103000341c1100701103081211112942001141281c0c1d05561008000d600d401d010310b462503c9510407244c401000f4104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 355129721 1250 355128471 355128481
    0x3060903120b10030209031e0a0b0105121b010909020c0601031b060503181e030a02060a05060102060411040605030a060b03010605040c0219020d02120102071b060e060c0c06040b070308 81
    0x80d00ca401c840070001014192840d030f00d014101e010b50808900d959150052000c0d0342e0101418042152500640c0740c0900000304160800f90300c41e140c140d0085000312080311345507060380c10200307034140b00341140a18409040401c0740104c034245000d422007101c20340700003105000c0c00c60004401e81268031480800d2250740b0141c100800b4108184600f001044007400488c0c8040c40002484100381c014004480100a002d11100d440031080181d44031207800004184201c99414030005a00000c610403d105500b081d000003947e5040c000d1028004216229901190340c1ea2908901c000f04002000c5071503810176400c002c0028070a94082602c42d61a0490000d168100350196550380016900600f08980200308030b410540700002e005c03a032100a4104020050355400c2d0070a5001c42450001a00c51440d0b00c0d0410b610b8040032360801e0000045402040000e602c1a80c14003810020f60715552254042070304c00c2c3c54500e100003440e621100100b004111003400a014025450080d5600c01c0161030ba = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 355130971 1250 355129721 355129757
    0x8040905100602010e0c0d0f061508010506040c0e01081b0d0b120d090b160c0303080f090a120f0516030c020306070503100909020105160b0a0c02031603180f03060903 73
    0x91062060266040204011b0036403400000c080b04841c000c202e464000d00c400d43d182001c640d000528004030752424142130181900034030483d07910400a030f808100b81c03096a58050500002d80c018107040125800015443c41c0b1510b178114001288102d2440e00e030002c1200142c0500042c25003540212900710340b82001e00000200c0a10344500d030340390342d007959041c0f081814032540700d10121450000820000d074001121107408100842c025521400141001503201d650070700c024044000c9a800900b80001040d070560b072482001015041218074142d10190544060041d0240010142200300e000000d068200710100c0b0424401c800782d4041d40d60b0680f060b03d07640410359041c849103281030b40c14091464035610010050b4014103119003009416040000903c803c0700303044900110100a200e112426802440d10901060010310b040c5142d22502410520301040f028080250b0180c03107180448400d081d10020b4105034024140094407418001c000d0894500c5c1200012a0414040d4200e24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 355132221 1250 355130971 355130981
    0x1120c02210f0f07080708030f06010e10020c01050c0703050105010e04121d04020d02250b1509190b0303030a1e0228201608010e03030a11070804090510060201 70
    0xc403042240f4105000d070070a00010360400c2c1400c0318041c10410420020908080285108000ca10f1580d02185800300c0010202b45042d2a150301840d4040c10701504540c01041030400e50b107003882c2c00c50b1205c5012603202e244c41c0e0305500c05030031035203040004100343c8100074603d88100c0c080c141c480d141c803903010001c840385807024040520103614002ea070781c003e20f070a80040000c1c2c1081e0f180942086518800c0c175000d1010140c00154a1954111110812000000701c0c0e41c4040d250300510b00f512078090100700101001030107030911003525403851350703207600c158080c000512029003126100c4c80d003aa540c100038101c007051488a0240140203c046074414000ca0b140307128241c040180641d6141c0c0d0344007440c584150030000341301c00e40c111140494212440c000c10f2422003001411350080c0440740c513446030141d80110f949641000000700e101d603070010032240c01450303a120003d0024103041d0249264041c0103001080b084000a000501c00c0742500200c2c0503c0d29003105103611071392040160b080711 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 355133471 1250 355132221 355132237
    0x90602210f011205011b0203031009151802191805030d090501080403030b0907170a090b1305100c032301030c062109060c080a05060d1101120c0221 65
    0x1c009800140301d00da002e44030040c040e510800c0081034101540a030141e000e0301c002603540040c0c1c0b0100412440c1302d010311078907005080086003084460140350601d03120202074040c1d0401071648441d42c2e618140264102c4065000c28240d00800d0a9003107030080100c0320321342c2e41101c0956810000b00303080c5404a60600004980e4840030346083c5000015104030381c00820640c14191b50b01003412090301d80380805440b80c0416035440074032001500c0d29503aa52000350641071071a01d031008000000301407043c02500949449940d0fa81640340b441d10740d15103034166a01d070746030074109020100000e82503080800403102588249c0070980c0c980c1c91401d4420310910000d0403180700003104112442c011840307030210321130441c41c403ca4811005c040105880400c402181e01c40daa5042174031000d42e200140301d030400841d001c1171100f8240100007030b0000035914809050035803c0007080c0c40d503a0046903042c0725800b1010080c006420f0f92080a9100c80301907144c02d0b4083e81800685110b04094012102c8035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 355134721 1250 355133471 355133491
    0x1090b060d050a180308060109081222180b0901050102030313030810050909071508130303391d18060607140d0e01030c0f1d0409060221 60
    0xc40007115034018103806070041c440180e0f9040308002102e2542c225210183c06030b00d40380b14604004000406c0815194012282600000c50f0300b418564086c00320340c0c1d07040c0f00a40b0a400c12000d100c1990b180c103c6a482080c10300c0100b4840860344005402c030810b1000212010b011580e42d4400690303d034070080313804403d40214400001c00081c024003125030020f03020450200019210408104051415a11908a41d00c902e0040016040e0f01b5045c1e412902d05c1d240403206820541007400001032401802006c0c5911075406808070300c600b180840f000e080640c019203c1c0c1071141003800d09418001c141070002048101ca0700114204502c08c6080c00502a003840341680e1902c010790b107004006001c09900000401501b40410140101a51040c10382005040b03c0c0a400c03002901d10481104224140742c1411110000340341c20890048000c0802d0030841070498148989104074160020441d41c42890412214240810307039000d401100c12030040030307429001148641484d150100c03050180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 355135971 1250 355134721 355134727
    0xf0702011e1a060c060f151203070204060f0501050307110c1e0108070806060711030f060903040611070b0d0e0109021c17040b031303050f03040b041b0f1e0b0f1201090b06 75
    0x4060812074081e0b400805d65000040c50082000001d4602340001d400320119400411000c00354500b81c41400010070350461840801494400041d1171740c00014420424007450503966140b0030011b0051001c1604010650201011009148418152501e4104e07000452590005500c2401000518000c000042c02207007003803074036603542c0c00582e07003245540d03050300170300711100311400b0100411401529464065901d41d400c1030401020821700076403040b60b5500c117810400102c005c0700100c4465422052012032141c00350b405c01805809200d034000c3d0407544010840f240940314642d260040d40c4140c2d140c000070311044904c2001402240102c1c4032402007040800c4d00345d0404a01c0240d101d20034144a410000c0c810300512560304121002c1c1c54210f810020401002600c4000320880300b03030320340c0700c0446904091004090420602542041004060424085480c0b2110510050101500040c0d0707c41444900301110380085407030421813500b5500206000764140502d003090b0030060a038900f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 355137221 1250 355135971 355135981
    0xc0d02070e01140102160308120c090f04020d24090b0f0a1514030f15100e01030e070f090e061e0403050f04090507110607030207020102060f0702011e1a060c06 70
    0xa10001541c04c0c158441c80101044d00007451801d00c00850252044a880381c034001c41003143c02c0c0c40101402810201040040c0080d40c80008001914500380c40c01600c0d8000c15504400500041401d016810141031006078048502c030048010350f5213000d07080c0b00c480410028402240c6010749055030144030b01c1424413400843c0c1c100c0c80000d224a15002400d0380301120405800e42c01981c064130b4800004e000c20101014680d40680100c00544081700a5456080010420b18440d8189810192a20400c10102d54104580e4010380b051030300400340d8a648900210045c135601303000b0303003680c02074200140710150000c0c04d0034503010300c0041d641920b50740d40d0b40440f0f241d44600940d00b2011401d000201d803045103480317168494629600c070310518414400740e00e403070020020000b0007010b0040040740e0050b41d01040454000b02102050103a07a240d111050f401341004010f481d12111001c43c13580000d1349550031003140401c240c0e000d907948021104c14080c081c80b03858401d040d00c0d40140040341c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 355138471 1250 355137221 355137239
    0x91a0403020d0503090904050f0106061407061a130f0c05030f0c0901140703030212011710090524010303090807140108041406100306151406070303090501110c0d02070e01 75
    0x11000e10540550f07161285c1c81c2c000400c5588180e40503541507015a41000e4500404d10602016000030700307107058014840500481340d4440c19034010185078840a0140c000400242c00000e40304008015100c00d001c042c41e120300910442d00308144141c108000300000a01841c1124082c407000701000b4096038900c420381c0099807010007001d04000e00400d424070a608844058050244a5a00075130780d0a1100e052003000041a0001c602420110202c200100c2001501d568000002080800c1000440c1002800c240000102c0034404151382d94110385560b2041e917041c162442501e648203165240c0c003600b41c3e161618042c0406403401f2010784122036005042c1c0c1c50b840303403107980f058201000203058603003010401c0d81d103501c4a0002200038420420340d0b0140c50401d01305000b101d040f17586070034000e50001c0c00711180d031030041c480000c4403001e052083e04030517640c940000080c000044120001041c5070302c1040c0702503182c0500c0021084c0d261012480e04122000c20b0b09405041c0d092119407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 355139721 1250 355138471 355138489
    0xe010c111605102709090b06030c1c061d0f0d030902031e0c0d03050d1d03070204091a01030c06030e06060306070509040609060e070f2a1e05010c091a040302 69
    0x15500301346034909800c8085404c41d054000e0461500701140361aa913203030035081e4038000b50003d1b209400c040e203a4186a1142c00400a012074820b218444400660405a0007809814212400e0419100b104605036030b00013070585114407000111402089980000c504547e06100c0007903158220b4281503041e8401110034404e080d40b06401d4880b54441e540000d004406c5001c0101e02103036000c55002403412081c420840300c04038090300c40200c1640031031520348905c548000203200300d0351407030307078200740603c0e1008c60701c0c403070340d44040512156164103285a85a1041c410180000d0500320b45200c1103501050031801900054001d00380c549031420f040c1c0e4150010004950003580c4c4000c00506103081d4007900380141300b54200345030f4904201d180240140c1034a6014024000c041c0714a03030682c0720594420300b40c00031000d103440c900d011502d40030307120026001d1130170100306001d4102e0080c0b21041d40085200500341c1c8800003984e40d101c1443e072809203130381582075517508180010005420308880d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 355140971 1250 355139721 355139747
    0x50d0b010b091201150623190905100c0203011107050a030c0203010f09030801030c09020c070e100b030c0912011107030507080d1104090f021215040e010c11160510 72
    0x44100740014614003800c440d85c0300d00c44283d060707440204000480c0c000c445040da0764002e000c0340006006106080900c0d100d02034265040917040b803030280d0345500c0742850320050100100024035106c40800e0040c01c00c003954800340d00c40c2d4a420030411040d0000012150000d40c0407020380f1741b071611910192514000d002050360555228603401c030803070846101390fa6901e8425141c000c550b5041d030415818030050b41c1c200920191041284208090000400c1421900040692500c50f41e0390350148070004415401640c50071400704c18482048062005052250f60550b05040100c0c0c4601c801400d8401d80307a2010501a420804540403e200d40d0040c11602c5c001c1c03002d00e140603011400750003141d40518812281c0039001c94203000744182801040c4084814080650070600c0b085e6070303010601c03006031140b04504800e52114035180c0307030768001c00690708200c0004c1012407038084024091340c804900c0d4040c94040e98104500381c3e80c04080c0e0b2701c00d80300050071201800d240c4410a0380c00c00c08100b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 355142221 1250 355140971 355140979
    0xf0305091203091b033007020301021c0e07180b06090607050109051b030c0108060d0b0708061305100306050615040b0909150904060507120f0e0601050d0b010b09 71
    0x4a59900e07803011002103004400210081000c001c181c001080c4603661442068400d03082640d0070a440d500755241403d11000886100800113a0203075036105a00c913240b002901540003140340b202141c00c00030f0709419500d2140c3e0521924603002e5034684c0341c401c2c07030044520500c10b5001405081020354062560450003403c29032030640c0450004c0c0e0107070442c002c1112107a444d21841c00801006011036800e0703c041e18110703904103408400080d180c038540d0079881c1c1007081c40c030001135050341d804800b6143c40f50002d46135030160400010007401140201d41c01c0b0b01410040003007440c0750038988990740c419480c1c1d100310084142580e03604000f400c8003400d001c0d8000320812503e544282d0140003400103100f0703020038581d5040150203003e6442c03c01000c40c030214000c280484102e0700d070340c0c940d2548035500c1800098a990360f90700540e903900352054036130000f510b000503015488100f944802c4001000500b21003180ea0b03508204411018902401020180c40400410240d40c600005c3c007241c880c014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 355143471 1250 355142221 355142233
    0x80c0904020403060f200726030a05060a15020303010b070f0b0901050601090e0105180907090e0a21021f0b06030c070b07050a020a030e0307030b010b03090106150f030509 75
    0x500094166086a002139400a507658030f400c03250b000511038031240810721008480a00400101e510944c00388400181040745084100c0c1d12010301348100b80449509002c0e000e0f101e0404440d1100180030840303440c0c0c01801c0568021901c0e41400c5080444580550700840c5145e00b0510300c4901c982141d14201c13034840c982801d002c00030310103180e60f9220340359041c000181843c2440004026001d95801001c18100f810018455501c40d41c8954840c042d0341c120106c429142d405c60b4510340b5007103621418426150420720b14420703401245000d840d0780680d03120888510f01c2403c000b03580c0904200f5001580c401c4110005500340303000c1404000c90660000980c1e00c807444085070040c0d2049501c00300503000003e0480c00c00102032405500301400346840c6007042c15002000c0e50340c0c1e072001405002d0007a865848a1240d40420203c8040e5500080c23480035560356080c0141d2a40040c1d0300d1a43c2c07542007040101d0584c0380d45a080042c150280c0d02c44030381400c100816070007440d016140c00c0d041e020700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 355144721 1250 355143471 355143487
    0xb0c190f020a0305060708060f060307050a090b040b280e090c13090903021b06040501030b0a121110020a0b0612030d09050318400e01060311010c030f080c 68
    0x1080c02d0000540c091009400c030786c40c004a0042050b280141114441c000c0003102002c0d42d16241c0659a0104035070402c0390f17444401c80025aa4440c5039070001000010010b0045049001080580703441144400034090300981000010240c40c0901e00120002d148013540743d20918141d910540c1101d08003440f90303d482a041800c0d407038031445070000c1c0200d03921355210381c081580c1081905030b1148840c650503490b01c00c400000c4c90346c3c40703580301c0d0342c0c101030705e5000002a0fa503c4071301200c000c1a40c846251040c000c076161a405918003800704511034640705c0c00e0b40b0340460006c10314800180c1d020043c0061070b5555001c201c607a12240001c3c178000d01c024004000b51404c244600c40340c15004070001c588a40c4202010f5101e00c00304620755024241c41c410410010100c901006010000e0200507801e0108138418001c6101c041c0000c207281d141071045a05500070190300c14000da034002c1100c2c605200e041001175031980c29109008000038a5041840c40d41841500c03c10f40201c00840c0b007916229030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 355145971 1250 355144721 355144729
    0x607080c06010e01060f0c050601090c09080a06150e1b03072c0916021002090303121f0902070b0a09030207080a1b17071404060905010306090c0b0c190f02 68
    0x26000b4403041c2c1900b0780140505600720802da5614070040c5805082003d440c8c1e1507684817070b010322602c0186515038454080ca180161507010207040080c044030400309880c144040a4400b0140103c040c2e000c80307102140100d40092114480c07081e4003011040c0e9505030a124425900041c0044100060780580802080050184480002072605600036008068007001444070016264001d1341ea850031036003c00e5074020980b410092842c0c0401a01d9052620121781540f0503412003070b010b0ba021004102c40407004c031480c82900340740c0411441344c15441c0d000030000c03031091040c090f100c01c2d0751000041c2d4169082e0014030002e88a0301c10f44030510380d41d0807403c0c540b8070408400c4590400301840b8000780b0089801c0d503030050441d11500802124850b401c1b50700e407210f50050b03042d246103042c0300c04055100c43c0c0045c0e00610170100100400d40c1d50342895002050000811514a5502c01c00011102955000d550707000d00344801130050341c95451920201c104004c40c0440c0d1040700e981c0c603078000d40d071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 355147221 1250 355145971 355145983
    0xd0212161d04020d062702040f030b04080f0c0304060906080c070209041506080a0302060603280305040e01090209030d2d200304050a0e07020a080a050d09150f09020f0607080c 77
    0x1b07081d030400e41107280c444080288403454810400d04544180001c1003082e5010544138200c81c4c03c6401c1891548540c10001c1d6240319000441300240d5000401e8001040700100600444240d5501c2d528000e4840100b03c4025106552078031000b8020b01c066000740c0707440031090740c000b841241c1058401d12840c1d2407030140e806d20b5108803566000900c181c018550140503903507000004602a00400301a40c66441548080746c014200b140c0c411203400c0c00300360281048401902e5000d000c0b000541e5201c0825000c0c1d4041e84000d4024010403c400d421035001e00c0d01d01140707001c0302590041440d40080e1790118000d0015100c000c00c50811550705442c4569554544c2c42c44486000c0c5660b5814007042c4a50110540c1c0440c4401c101c00c0208410142e004c076900e0003e44d404070311240d0300c28841c9002ca54600030b42d4100c55141d482c1281c40402c00081441c060440b1030803685c18030411280300040ca04407040d49030080d4004001090601c01c41ca00440140451403084442034101405a200c1c00e00c2c040e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 355148471 1250 355147221 355147229
    0x41503050c010e12120307120e0304090e012a020a08070b041106040b0d050621010515030304060c0212070f090608120702130b150d0212161d04020d06 66
    0x14005900c101c000d0350344100e0740030001801340c91032643d00003001340c0a0f0b598440c0700c0c4030a401110200c04510054451445d1480c0c40400b454103200c81041e084101d071300d81d0f01620590500c10300d042480034083c601030003100314240501c110176200047c800c02e40700c90391504d8220750302140a180547c100003010780000d0b01c400350042680e80e01c28079207841c000349034100c912072107840380310180000c201c0ca4041d54212107408038400b102181035260180445e001d45071401c50744805255900c03459081500c1540554072400b410f58120003010401c1060585074440c5000381000190a8010750001d81440360794504c004445a003207400c0f040e541c004141d10b80d0300030340100d048161280c00420001104000712110740d040403441074030b001c2d041d5002507011002c00406800707258030b5482c0d200c42e0303581e20b4100c0604414800200b5541d614002c407a0002507011001134414428480007090100a0b1113203c01d000c2d05194440442640c0d409008c502c101c1c180c051025400fa80801c0b00170080c141c0c500554000b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 355149721 1250 355148471 355148473
    0xc120304020415050607030323090609010c1e080919030c0308010902040b0301090905071703040f0b09010f0809030f0409050a0b010e060a14130f0e010f06120b04150305 74
    0xa040c10320410003990b200e060310802c000c496500511507641c4110480d1140e0750305040c00120306280074185a20303044e0400720850403070880d10410403e0900031400070f2007400108000c02488620000a4501c1071105888000b044000c402c242c80d041d000384074240e0051200001c48816010140495031881c22945084001541e981102401c041c0c1041c20070380900800fa80035800c060403c0b80f40c0000d400140b049004a0f516402c2078428001c041c00302801070580c1c120051403000c1c000c1c82c0c0655980c80340c8121074003001d03075040004001d05510b0540d456450160744159a02e00c2c2c5210490f00300d03001031700c040c600e40030030000b0300c842d1085000100010420310802094518122840c80700315512210380b60305005d5605c83ea80780c00ea0b1288212030800146061014802045140c56040c50080382a4070a900c041c446010400740d082441d040106c6140d4001381a81c1c0e07032204220100c03180f241c81241c0c04500c508003280c2207400306422608245001400000e4800c002ea1810842c250140c0d10030b94407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 355150971 1250 355149721 355149727
    0x1504030215071706010318021302130e0415021e0c100608031e130905010e0a0501170a020f01120c0e10020c0102100507050f040e0a0506120c150c12 65
    0x250380c61420700d941c00007290400702d030801628003980c420300c00d00400503410180d640c80704a0907100110b100030010364003c0c02800c5843d00c8507403094000e40c00a1900e050500c0104070014280443d00001785c4513551140b0400c031180f030401449000794101405800001c584141c55841821644003d0003082d500303030000348503441c1140101c40464a054006a180f90420071030b070740b07101200d101400c10b02c1e4480407000741e5074043d94408880281d019000380c0080c5060500001c2d005025004280c05114072160401481e642d5081c0042403501405a68045401c01c80c0c2c035001528008060801140d0181069040d0078a14001d890481b482003048034041002d1485004c65400c0551403100d605605000a20403000302c400040d41e5040002c0c076a56040f5201c000084140740b141c0d0035113a0000b078210305a41c0700c039140e104940c41d903001212002d076180d1409000540d5071038a1040c510b240740d40b02d07003e04000e180c004184460081c1d288481140501c0c100041c0e960503c0810042a41110b210102c0c0d071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 355152221 1250 355150971 355150993
    0x210307060f0c08040305070b27030c120406170601032c0114070903080c122b05011202010e030c100207080f060108060609090a060204030c0302011e090b0c15040302 72
    0x201c0d202c030282c0c41c0400c4400020000000d80200803910401d8000e0120f640310303550381c4412100c041c41da081d0f0007901c020824510054a000101802c92161004181c910419042032750070480e000701e1103894000f500c201c4080b15003a142012070350304090103160204075140524558040b08541e02842c44c1083e480000302001e00340f0070701c100268410719107041d01c058180b16000038001c411a020203003070242e0000710031134080740800c440c1d02c1102025500517200d51000b00a981c0390581c3c10480780c1c110440020206000542c0c1c82801e050b03628070300d800d420303480b8140c00440f00304040c4514640c01d071203045076110300d50313440c050508418031682e13006100490030104c906040029000c82c2544a52004005100002000ca90030360b2049040d0b52104441d95601c240c1c0d03141425107180034101900c0001d01000380aa01c0c144441641d000b81ca8240d20310400d4150007040740c16800031800001c40601c01071100c0c0c2041d400a01c4000000000ca64403100c1c000c9064400110039181140582d0105404503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 355153471 1250 355152221 355152251
    0x60f070203011802030615040e06090d08070201060602030f16020a08010608070b0304150e070b030a0b01030605010c0f06020a11070b1e0c060705070305040e1003050c030109020d0221030706 83
    0x4007000d90101100041c00e21244c0c00709a0f01c60007c0c0c0038520710404e2000c6100f00ba15035900c011034151281e021a00c1c281096282d060301d030400f581c60040021443d40000381139030f005014000c101c4070301d540103503e400c0e0140d2006599400c49503040c3c0002403800100d201680d54000d0042c0a8175445000280141c5482807407803030300c55a0ba00000c10301d01d041c02000082a90b0745c00152124030504000309154010f0038049041900035017226004540c0403042c06009805507000b40c450520030307201085404d860f04019034114194040050807034006109840c00154241c001d42a601180e0909400d00400c06c4101c50a001068214000391200800d000c140c0e80ea410001500590151146a1030b02d41c451500948880000700341c2000e0240009100b820148902c04440007802c004015071000d05055056041070246071201303035520700c00d4145440b030514062040031081540282102c80c0007080d03900b4000424003008050001d031000800c1d4a044c1c4a0030700081402c640300d10400941068409855 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 355154721 1250 355153471 355153481
    0xc06110a1716080406020d02120c0711090108030a2703081306030b0303040608060d060606020c010807030e0c120a0b041a010f0e0411190f0f080d21060302060f07020301 74
    0x28800c0600d9200c25001c5643c2c2010040750841d070080c0c00580d030741c40c0b030600c18006803090404041c1c15070f0b003500820644110200241c5207003807003401484142e150038810880040401e02900049070410411200158082c1810015030b0b040001000c00203451600c0c45541d03286942e105840810002030310a402120407480840a8003007130804000c040c83d9030004c07131303907a015034040c81c014003201101143c0c1c80c0c1d44007a074045035a0760200045c0041e548a5100035181c00c007640026004c00d0512000c10b14070390080c0240c6032160860b00081c20102c202c4d00070401c800c1405074481d00a8010500360002148840d203c1c0e80c45580640c0c80c2c00920201c44075001c40c90041603100025071035007840c0034085403040f4420103400613000003000c584140030000180c04000074004944269242c4400051030003e03400c03505d82142d04141080c100c8a42d6200d503691036403180d006c02c2c4005403100c00c5a0f25080c246d03925001040c10522400907042e500c03903001c1000c40d48048544240c01c20301280035030031480c09003e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 355155971 1250 355154721 355154731
    0x2d060810020a02030405100c060614030607020109020f010315080601091b230d021b07050414010f06140f040b03160f090e1302031903021504120c06110a17 68
    0xc01c524000621000a440f4000d80c001c83d407081169903400780751240304020866006e80c1004c1d0401202d941c80707081e4500d82c100c40c600b8174040d025210006805900611950182c01c0c0c021b030a50201d41c035034000440c01407d081041d4034041010702c80204030001c0420015010703121001d00062080f0250001d824243c00060f00d01c42044240381050382a00c0090612408102078004255200d6060315445406802040701c0c5034801000e60301c0c8610003582c009606c0d001c480064504002c0d040001c001c08079400000d0050340384204c64140c0c2000b400d803044402d600000c0054102d24200507500b80611481d41c17180c0d02c0181001070102c00e112807241d0701e00c2c3c8a80000014100706140c1e162014002e0701e90205846400390801f000c400284451285040c2c0990580d4010306995200e040510340315a00d054122017500184908070318800c40d80000340a140c0243e400981c00040101100802c0700c200700b8600342201c101da140c0304204801c80c0b180300600130391402600ca58044585400c40305440100c0204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 355157221 1250 355155971 355156003
    0x3030408120a02091801050a060903051c05120a0b09010902190c050c0406090f050109090b13020f12030a0201051f030303090804050306071808030306060d2d0608 71
    0x28400095280030485101561840341c1c40e085035642c0380072200030b0180c502c0690f084101c1300c0450f006a54690025410303644115040403000d80c480c001140e10031801d0100a01d03540c05844080480000c11107034482d40403051814078540010000c4050f0004025200003203a1038807001401c100b45001040e1030b01400789101c085082002d18104039404115011034982802004006541803040134080d10701c1840001c1c0c0140300041d6910a103d009200e4008c4a6008034940800810500d01034090380901c160400d15150076a01d0700341d0400403015040c0f40c101e038400f003000e0100c803050311800f0a007001003084101845c2c841c0004080a82520002000f180700c41012001c2541115818055513055079054a00020509610320342202a4803881d00100d03890300c500d000300031026a004880b070004000d010800d80501d9506c0c2030b40c03643c9000590703900740c0c8064180030400211440c6c0e8008115047c00100c00364400c42d000401d0900300007528000c0111980b520000d010451040000d0204081504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 355158471 1250 355157221 355157227
    0x6080c1602120c0919060f03030c0816050a030306050909060402011e11151012080a05030c1303060b18101214030a03020901090603050403080a0c050c0102120402030f03 74
    0x1428400c284065004028812100410255a030400400c9102c00ca1032001d0a200070301c1c02c03c2044000400d6195690f42d0f42c06060520207d030110b81c000340312040b03a070b05845a05013841c49903181065a01b0924004801c40c40c0d10b40c00d000401c8080050a151500a460001c0e4840c100b400f0310002e110010701c0080c0785c0c5d20200c240001030360b002e420400b21013480031440b2805210500d040340c8094003260920194465030200c0080451a4079065003d00c0d19505c0c0103440943d500c90b00f1084900c070107406088050180700d25040c2901520066902c54030b608a45480c199442111240c8044035803c240c4007260754180d610300034100407103003125100702400040007501c3e01000b030000f1f010441c003c3d0b140d10b0b901030b00480100448803040b00d1030588a5419251181a0458010004e401004d8218005843c070140095118003c3c412035009039003507900e090650340c4200100c0003030100c0c90103280800104101e81c1149180a20250405c03014840802c1c600e41054010546091034001c10700c40076401c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 355159721 1250 355158471 355158487
    0x108011e03080a021603060c20070902070804080102180406080a050705040b010513030b041704050d020409210903021206010b1c06150203030a050702060702031e070c0f06080c 77
    0x1464401207990040440e907a94500b02c00482c00c01c40c100101000400142001004014042e00020340c0780c0d03d2135448166802c00310000c0d1380104445111144960014081840400080c2d001041c65034001e50301c4501e80381d61807600d0f90880e0300812401d240400110a4048a4a054000e0000030261280180501d20194940740d460300c0c030034030825218580e5604584126402081513408000750404616000382d524200392800301400c65044444420f840c01001d650485401036070306490001d81902032a10f03895080c4001010b00300b005440034040c03180d0411080c1464404840006030903551070032000e2031403060141c0c4410400540384a900700400510440c11400180e560fa4103140450b80700322000400070740300400f090f070007250515800071419081c0c0c94000006602501c182441088207a031128401c07a242e01d004c0c0c4030b480c0180c1041040c00012503940c004400942103580c0d980385400c500780d45026070240580d2180c4070001d0200801c0203055009100c0e5030740300358a1124240303020380c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 355160971 1250 355159721 355159769
    0x2091e2e030e03091e0f060f0c0d0203070c0e1905070210060504020c03030402060f090916080702010911040f060f151806080f091015090c0e09070e0607060f0b010801 73
    0x9101c080c0d84017010030100d00c04407951001c5c2407101c000005000700d5981c3c2601071154400740d100e004001c40d40c0c480c02081e000c0461000084515a40e001880000340034100a0132a61508001d0700850002003140c000c1d114a4000b072244078002c3c4c045070028a4091426400002510702c0f80e4042d03445544140610094114044200c0303a01550440c1d0072945c1e050800c86d14078460180c19a02c1d0780000782c46040003540981c1610b140e904c090191645c100e10383c0c0b407a904909850740301000800350001c003543c5803070900701074009241c60401c0c0303040030a00740d40302c4401c80408a4554040e401420f006012218060741241c140b030f50407200c240341c41c000036052103030160032804050503135007501c200f210004400c2241803000240400040206104803011600c403d59154a140181c55140340360420400d0150b005007410400103402503d00001a9210b250580311421210a5190048800c01407080042d54031b114440e20290032010000c1d03400d0b1030000040c040c0754140c1002c0b0800fa07410840e6220012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 355162221 1250 355160971 355160989
    0xc0a140307091a090910050109050609221127010e07050414011b080706051009060e040206090a0509090303010306140c0d20040305060105040c0302091e2e030e0309 72
    0x80f00ba5040320940e11a0385c561450071080c00120078a4070300e80f000209400750300d504014060001280c28104c292151802c0c03040ca41018410b42e40380100642c0041c0018905c560300c6005040c00a127420100c1c0d5102581400030350305180144d60041c0041c00500c074a1014054940d000101880e2080c18103081c20510400304240b003119034140039000c9483c0340c82500e440ba061901ea0b6101d21200d80b2100e19181c11400ba1100b51200310449416900c04201c91880303210310f000b10340c505624045d0a48440d0240320044d446110b46580104060a0100e001c0e214000341c5801081443c0041d81d603980340d4280340d0200c0b8071003502400d0350502d40c0144040d6203d05819207440d20482c0e100060041003c0700d4410340f102045030b0b00340a4520114000080c824040350160403504240d4050201d003030784c03403012400c0344100d000403940801142d0b0320907070710103070a0107509201e8400341c04019080307490781c0708050303100b40102e4000d0040b480104c2c1c054800c2d414043c42140008600c01035080245480004035020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 355163471 1250 355162221 355162271
    0x105031219081f180606050a020d08060402070b01030f03030507020c10030c0314072003070c0b0a020106050913050d1707030c030b10020601030318030b06010f020c0a14030709 77
    0x1001d103001007091003d8080c18524182c0c488420088000d580d00a901c40b0404503503000e52a10340f40c00c20010b01c29000740c04031032144550360f001e0310b1140c0d100201910051400341040350171590900040300081c10b00a102400386020307101c400306a40d107901e40241075410090031542150081c04400d00395449540700092814094200424651a00d8008600074181903c0001c0401800800e22000d203400120300f42c1c1d01d5001c42e07014090710030740040c042e540c1e01c24210f000f03112407132581c0304025050303149002d8601c0c1201c5100100d22140d40b030000903081001a10800b0707448507241c560404210081140c40780d0b014107800d100400499104d074018480a00800001c01c0c1915180c103162418881d03030001c1a4024000d265134104c00e07101130002e603561024007040340816a0b41070742d0040980e4803a40c4804584e80091440d2081d0b0b0ba81c801101c0d41e0221191810551042090b000059958110044041c001800104402e40b07150010540380c061030b5444810b859103450f190065452000c4840b61500b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 355164721 1250 355163471 355163477
    0x30604061508030a050f0a1701320604050d2a0510020607020607050a0306120b04120203040b0f07060f02030f060406050d0b0a09050a0203060906190209060d11160305030105031219 79
    0x1c80518a0569650402380035912199000a0011514005054580c0e03190501c9800c0c02c81c0340b04070000000343e10342c00201daa81e80b0040038802007241e841c24545c00c440c031901c01d00030b20b01503184284003030500d468070302070580c45610119024040703800c120708296401c0d00984004c00c044d051000d0040d4481e60007130606400c12900103060030400b8007a401042c028504403090710107606107820004d070000d90603101124145c03400e0348450702c05807001055030300707484c0e4051609190040809851003550f00c0a00e0071a1455124408010f00c8808d0384061031040741c000b000c4010360302c0d1103401c010450f0320680219204811518058010540401c0307910340c00b0940801c0025040c01c541050303480c082d00c1c2d046c002d6040c4202801c000320100302040d4a402800102004c2c0d0360351009840c100d060380203040e22150040c0b010f000c04461011680c0119520104802d10742c0c0c50034080001c0e207004103041c0801030300400c0e0b000004026606003004900c0b0fa20603024402c6052102c584600360707c0380c24040f444810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 355165971 1250 355164721 355164727
    0x1d0108060f0604080703030503040507080a0819201c03060f09200c030408010b0a06052b020f071505130f03140a09050f010804150c030b030604061508030a050f 70
    0x1a40b01c0000b2038000e400d0754411203038066980c2c0340007402a40200d4086966000300c6c00c0015040f100002c2c402c1d01c10354058501400c1131071100034a002181003401d000104110074200440f900140100c6011b00200c0c6800b608130140b500d88403114026410321004201480c020003003040c28110103803201901c09202010403199407030b010348e5486042030842c0380300b80c07880018480ca00100c008014030032949a10028018400d40904116220310280718590100704200405058002882c040031070b06900d001c46540c1d20100e8440034070490b0003181000008400c0061a6000d010300ca034011101c142c8803500601007444e21411508502c4001c0070001c1c200d1003c00c41c41d80c2054081c000c6480e18140c8078540075210300403030f0401402c0e800c0c1441642e00030500340c001e084941d445980c1441c42241c010141000300000d1070340283c0200b40da003190078205580c07500d0301c191698007488203a00440c062180452040151300c0900300c13140c40c9074840b29643d0300400803d2183c80d000002e50b003001051079680d07030f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 355167221 1250 355165971 355165999
    0x130f15080105091810020a170f090a140a0f12020f010605130b1518180702150907030204110c0111040303020c01050d020f0304060501090506061809090109050303070207061d010806 79
    0x1c9018074481707594801c580040382c0b0704c142651004071030b86450400c5000110a44501801981e42c0c4003c2d180f01b0700175002140c820022400d0184c4801103080124101c0e03181d80180e84550401c26040c0c3c030200c40a01f81c002c80d0104081c2c0c10800489407070402c00c02040441d10340300c0000c10130400d0715030003c3ca05032140c00c8106203035581200e0384050307280359115980c5c0c1c070b0f540324078000034440110b05544560440c003029500d80e903220350304904c00c13003880d0028a40503100300314090610400414040c4140708455011006844a0040c0400d50101d004013544030340da0903284600b591810350210202c414103010410100783e000a14444440c420b08107255240f5107102c1d40c0c03019100d80080d03120784402c000244420009141d100c1412984400360402c40740e00d400d0100b0001e4801c0901c0381028801401202160385040003695400442903000040d01d19025a0b403241141c1003110b030b41015800101d01040107a070003000c415164142c80c54211146420748001801c4048013601c43c0d40500d40b041d0a00d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 355168471 1250 355167221 355167223
    0x10f060c170c0d0306060f0806311409012301090c0c0f150b0609031f0e061f05090f0f04050c06030c070c050402030106020a17130f150801050918 64
    0x205a020307120182c42120f4041c60010b0007410043c80b0320000210304001e1225220b00c1130104074002d180092424070b042d1032a003160074a004d85c0d8259520841c00d48034195114402600c07a118004001e140025120b241841c40c250840e841c0c81c0e800e032036103494a0305503d46e61509034221419501400e40010764618002400c135811411052b00a10303910000c5500000d01c00311038801040e17a001442c040c4402e40002c014070407240150101203806512081418001030b04c800c000d0303d651361400c08005280c46210292915042060f610090080c520440c031040c4000200302c44400b40c1000d4421030180d00b4800c1061644580040c000705500f0500c4c008281040814054544000002031aa50701c905103d0300300c104980c4515811900c8200200002455040a0081d01d040380c4003078010f004d050302a9122140803080420307000c0c18441c030420201c10b241e040c0e10480c0001d1320070501c00c030103528140006440310003030b00703001001032110610041050303954000300c0542c8100044800c51080011269403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 355169721 1250 355168471 355168477
    0x418060f080606010c050f031c0b1906030b0409150c02060a0e0705090603030d060e06011814040203100330030207020906060f0c03281b0b1302030d1205010f060c17 72
    0x2198a000001d4540b0070b0301040440c04001c14002c031002c100d40708501003081048bd0178400c01c0c403c890b08103102000300601030303032000001150150000c9242c6043e03a46591038000c0482c0e003100c02c1651518480c0100b80e040104981c4081d01007000c1050000e92280f46130340b0340d11445658464074141d4001551502d0500a8070040c0c8603e00041c00082d4032100c0c1d280101d2005c44200e40040c030100c8480c00185002c4071088200c0780c0745410166250100c1003440080c0d0300c002d1010030040345014001001030050154881c0d002440c2c0f41d800322a48000c80105a5183d43c20700030070030140144088005a50b900210755041141100c000d5039980110519247c680034080840701030b4003001c100300c1404c80c000344030744451010301c40c801d29000c4c0c0251815140c0741603480c110002d602d2040768a02c0000c1643d1021034000e01100d4183c0b104403206d500080c0381043c038041c408000b680300d00c2c9030300600c0382c58007800c0c1c0500031611008041c203080c0500181003a00038900645060341c0c0710155a0002090422 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 355170971 1250 355169721 355169743
    0x613120c02180412050f07112b03080f0c0313110d0507050a06050c030406080a02070f050a061a0607020f06160f03020f031e1e0418060f080606010c05 66
    0x1507816040c5007095480603a41d084600341ca0300c4813141d59403030706a88160100d40303841102d40c6035181049255100c0b28035560800c0c1d002d0390000d1070000055000c1c8200740403000160952a41c4184907031442ca0018a401030103844410444181001e00500400035400c0c1c0760722202e90100d980120302c0c0c0b4201138504400c9240d205800114840c1d01c90300f40140800d441068071001e4801210641d603a074011200b034480d20340045002d410510041c0304891181100d6a004591582e015040c0b90305a140e080746004852811166684003030380d84030401a081c000d4001180402418a90b0111003102040b200e20602500a01c41c42002d18400080d5403500c081c0d03210b0414500c0c2203142201c403803400421007160701fa0250b0140c428001c0b103108140c03002086492001150340c0c001610082a66000c0d5150040c035410b2500d55071018000328450241c8020300b004040718000d12030113078007004012007110703019006401d1042d0040130600c4024400100990400003e01e44840c17509054101542400c80d4850 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 355172221 1250 355170971 355170979
    0x80a09060204080a0203190503030106180b0315011d0105091c0b040b1801050403090b0d1d07150c0809091b160303060e0403120c020114010b040e090613120c02 70
    0x4003c60b80d0100051010140d610030342c2294000086098074100f0580c0c15a0000c100354800c00061044070310400e4820003140d83c04800329282600d40b006070b0101d80040315405034590091481511a40c2d02040810085545800d0030317045803840300c00204144151010103008030b40c0b2030600401c0300510054680140d4200d4031034440c0d81400c1c981038907008410f48413030f0f5160380010b00c2c1c06031008044c81020300440c1d1545400f8a40c92810b4014580ca400003040c008580355507458440c40300038420015881c1c00104406050910b043c080d9403034a404904a00008204c0ca00e403981d0001022442100e03c0300d00e0071100141d003981c1e05086001e01d11100d0341c0000d040100071030300c1c840000c423504d20038034036071310a80b402e105064864510300d040e07050444001e0b0024000140713883c24803032103034081d00071155140b00104400d000081c10900101081e40034080b5004001010400ca04a0280c10350300040428047c1655003030522040011010100000d00a50004000406e0b02402a07052240e1654060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 355173471 1250 355172221 355172227
    0x62110090507030302011409060f1909030804030909021806070c050619090e070806100203091e0312130306110d060909110f010507061d03030103050303160305070f080a090602 77
    0x403030050b441d45001d1204070055801c20b440001006040020240f051105600400d40c558903a0900d200310440604117800040c50076483d1159000f641c010000802e0017030f00d4408043c2403d00d0014140449a440900b203540305000c6c80c1619125070368201440201114290b4450703000e82406140c2150030741c4841c1e80440700180700030401031403c07110f17148005292260340b110340ea80d40d80c0d50400c2d0741c1298920001074441000425501e80407540107861602c46c81104d05048a00000c1108001140ca0009485106041108481c0303010450440d241070034580460610702e1001c048030100c0e503540801401d103034880c1d01c0c0c4100000c2140c2520b000d510114001d000250f074030318910000f00680901510721500300f0040661a0804841c2d001102d00306035a258601100c988401c2c00501c02407400d0001a44081d61496170040c04101840c080e501070809103540341440f0132920002e580d80e1039074a060504000030403400603005400c002756801c05041c804026a19a00d08030001c00c0c4007800101954808 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 355174721 1250 355173471 355173473
    0x100b0f150408072709020105030402061c050112051006060c0b0a020c120301170c03030a12060806090c12010605030307030c05010b0a03230c06040902130312050a031406211009 77
    0x104c1c07609881044140c022208010600b004003d13254605000707800301d6402c002141c0141408401400390010300c0e260701d02101126102c9000b50b0780203900007045404058052014800d0070300941503010701004c01003058074500100942000b2801c00050000202d4000103401c140c0640c0444445081c510180c0e1180090841c81d84519002809041010b01c0d10040300e40249a00042018528074014000d6040680c0d44904483c5104c0300307d10303080007544619000034004400c000302030040864002524001d0100410300400c1c3d1848801500b007a81401f1040041da240881107030145509450440ca14500d50309015000d0a0f5800c1c81e1ba4109100100000500000400000c0780191a008801e00081c06808003aa10041204c1c82d44c0c0c030060800c01000300281d158010b0420328880c00c03041421503503a441d81c0064268201090021402c0060541d1005505201d0918aa011040c0d105154189000440d010041c038403040f01e244906840500300462082004000b8501e020700203000ca2030366 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 355175971 1250 355174721 355174739
    0xe12010608010501060801080109150e10090b040614010e060d020a03140627071205011503060212011a070f1713140405070f0f1b0f0302100b0f15040807 67
    0x3c2445003a0016000c00008112980b042c001c8400403a000342d4590982d10004078001c0c01841001c06c190b41c1c3e841030010015041c00c0e41d01844036102d009065154245c681414003900365050403500c600120030f000018011546011615504541f0a484d0312143d4000c5102055002c045600082c0445074000b0180141c0d03100051410710512404030074200c0d507a403841c8005600c0030421020400e5401c0148180509503400038800e03070340d034003950020600320100c0110b072501000c0d42d002681d1017600014030940106c1071100b03160041180c881000086100443c6031105c03401085c40007881126094008424400250941d0704032071524001075545080b00b0510000201c2244503815211f49110200c440768500340c4502ea203d0022611814403021010307800701d0708130700145040014020700030414058840071241c4420018450400103040a071581400380c5005e11360302401c10098108009400d50791200b18034074103101c9040d2448002c12042c0c400540c0c423070045410140403442070010000341000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 355177221 1250 355175971 355175981
    0x7030b0a0906030f2001021b030102040902040b220e010302010309110303030c070203060a05130f051f0204080c240a1709030a0f170c0d0219020105060a091b0e1201060801 75
    0x40b080d10001145c0d00c484881c08039060088000501503004401764640c074807441c40035001400c8000f4001868542c43c3c500440490b0030640001c1100c2c1c1c80494106a001031003c0503008035000550413140c0c561520301030f410609030500000781013545540589040101c003184030225a03400030280ca0301c07490015024860707a042044140e219204080110701d07070710b407a44502ca00035480c00400080c48611034031469039014821400700d4072407085401c4200103d48684846a01c03103c204030169555141c0800709203011403180010788107290070386000c0712602100400c80800502c040e495911403600d000152280080e050451084490580c1001880341c4080001d007031020345500c80a00881c2c41d0281140c0d02c011140c100c155410511012440381c514000c007401000041c401d000d450500040030740d0044412054588002d40e44640c1030041a240101a08024201d1050104140010320209010190961503610280b00c1d00070035000071a1124100e081001c140b8900078032000c1d94031540580200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 355178471 1250 355177221 355177223
    0x619140f0709170a0b061801080304030c09021603110309030613120203071a06040b03030705100e0c0312030907170c0f060c060f090715030614040b060307030b0a0906030f 75
    0xd40b040c0800314500e40d01910038505070034038500502d2840c0b0309030f80310000d070315010b045164031281d112044070482075010101c0d40a020f59a019645035450b5181001c4402050b0b0000e416150050045039000c0742000c1c039900038680c041c5406e0415071501c2d8489410740c46060b801d01d130140079110800c00b800b81402c8010119520132211100c0c0d41c11195012600d9003e0600300520070741c82180c100c05061600d000c15600304000400010310000100d00007482d5601800007112640c02026482d00708915034402d02d02c4005400c070142101780307205000291512000b00811000010103c007041050301d0402c0300d403014060600610801c504011307001c9540380124220750740f01e864007641c6c000e030702e08014058655560000d402400b840d1600c610642c51078400600d101c10ba840381d00c20025070074515080c0e5040e102020f0302e0002c2e509042c192590f030001c232174840603801141410403c010944a50007142d62000440c64001401500c84c80018a0280075602805116081260100c24004400b00c03200c1a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 355179721 1250 355178471 355178477
    0x19080610050102070308070308100b0301030605040b060406080705010c06060b03040302030c06060f010909090501291c120f0c0210110114040c141203030106080108070e0103050619140f07 82
    0x31507075040126680c500ca804001c000200c01c3c040c00300000d0180d4095504071085065a039001504c640c807000340c50b0001d0344180c03565500d4206100c28064003808550304060241da060042d85e0074404881d542d100c8a10640d030400490a02240a21142d54064000b81203e540055904c0c00c0604000f552500700292000d41800b403100841d1701850614100a5495410b0712203510321440d08001000504002a0a8840c2d5481e8004a6201e8a10100146a81c482040c080280030114000c1c006541c560710f8070000070f6425580180081111103003c694101c80c1c3e46819204280c0c80b18080303a40c000410b40c0250011000d42038290070581100010068600d80c00c001c000703401c1f0000e02c810311103a0907680504004880101400050340007401c04c5c202503806407080721003041c00080c2900d03540c000d03406400080c075508010300c2400014850780c801494180103142465045407500c0d0303114007000c0c128010b2f54116140200c08201203400085150b80030590341182c91401196991188008072071117000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355180971 1250 355179721 355179751
    0x9150201231803190c0206091306090b150706050601110303070512160c15021b010606140f030703051306020d0b04050a020c0307060b06041e050f2b02190806 69
    0x10303540000055407003000c84445100d142c60507442c400d499025405c0c03030690f0050002c002c198034540b00c29080300801c500d401300010f85140f50083c50002c0300c3c1d803000c4062181d21284007100565980c8001c1c0d507a4036802c801c00080035254003005031060081d90313207c9000c6000c044108552142c000d405420304810041c0701d0b01d0203548101103001d1041c42da02c030204c003103050302804101007150340142d000070110304000140341004101c3e6081d039600700071086c141b071603450320018030203243d0103090700700c003118103100301c50070415a10a1551980001401081010380c0d90700040c0300e20343d489031042d03c400d4000c0030441d540c4001c400500040d241540c440e50040d4208804102508298130031280e0500030800990b0900c0c0340d96a0b40130182410003000344c0d101e034042c40041101950300071340c941481500b40c2c11410241c54101032148545110b207215108001c041418000c100140c2c4054003549682c044200a80d046840054044030040f8010070b106c600c2c48902040f0304000190041c0201c00e01c0300ca000c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355182221 1250 355180971 355181011
    0x91f0e040615170a02040503010608100c0c1e0201090902070516080303070c080f0d06060810060504051e1f020a0c091b260c07030305060a05010915020123 68
    0x34660b51610407010003d107668008007807803005543c1d02d80d00012000000b40c03510380e0300c400003825a9003507089045190421b0440604000e4148101200041e060404c0c0319074440c0e60310784038a540880d8000403402a00041c1650841e03200c5c100103800b401000c1c004648803401400c0181e83d5150f904c094101c408401c03500841c99810001c2524800c8200f503032089444c0c6415564071444d5042104100c1d900b0109216040d4414a58010381c0d010307003c0381c0c7c0d076140355241070311010100492682c4210280002040188030f1500c0748850466400386c006000030120005001041c00c01d41481c1c0d0b400e00e00c400180984c1aa280d000c01d4105040d0b0046e5800010030342c4a12240d01124001c40b43e02c03203005007078075030008420b0103002612008540c1c4018051201841c6130002c10f185021502580d100038000340d41c10170503070580b140680040c415601c45140c0e41c20100080e140186070302860080345950415550007038800d400908464040c902860284001080310b414924011340c2c8944d0f00440e113450b119 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355183471 1250 355182221 355182239
    0x30114010509060109030506060d0f0c150206100308090103110715023a051308040902120703023a0e010b030f0f120313120c1103030705030708091f0e0406 68
    0xc03090321f0308003015040d20b86800c002c2010420031204100e84629040d12020007003110003841000504040b40b480601d900c0e20b04000781000001048100441500300e02400882d42c0241500c4000d64203003000248000001803200d8603001e1008000d000e46040c030414000501c00350060b01c0041203000c00b00401e2000160602004141f41107030919103100084140601035594203d0750f0042d68421003030120060503212407042c0da1098001050740c1d900000c3d142203605d01c030ba0400341c0c4411145011810030b44c108441d055600548a040042640341e1410400c550841d44040441c41500a604000f008500e00d200c038007a04c0e41050603031080c0564401c44002c80c1020032858241c1c10050043c00d0300715000810b88115420203010250880303211541207000510715280c04844110b0b5840e80c000481071482e0020081149500140c00b0f50028025540024800015070f18003d601c00c90b001c0d03d030300b6541c001c1001c040b080d619080c00b8900d242d104151a54001411404d04202900c060002507140c85070310b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355184721 1250 355183471 355183487
    0xc0320030331230d080304030309050606090f070e011101020d0501030605010909050709050406140f040b16090e0408070605161101020a0e0d0c05120c0112060b03010b070f020301140105090601 84
    0x3d0700303a040f80c4080186100344400f03408403003640041c0241e502a140740c03034488654200302c400b100400c0d81c1f20058070900c6401c01c40142c2c0614111080c02d841d190181140300c03500320203040071040c0035000750000311a038060280382c0030120140703008644413400f0543d80d9014003420300c030507900d0915060020501141c14010031a890b500040100305003491300c0340c04002408024400e585843ea5465400d4120b2020401039009110200d02600e241c00c250070008040d00300604451141c0700c07100c10383c0e500c0341d804ca00c00c44101e030001615040c03103903141c0c00d22000703900c1003d90080c09a40382034100a5000100100319604101d0760350b98084680e01d20311018200e10035580300c030012410314850482c0034540258400d1140c2d205000c040c090301d54800100340441c600f00d500c0026604600703441c4586503809071888c0038100c0c1024049c00050b2801e86000460f00c41070140f41904a40020004e003802940c03070308036041e01e40c05002000403a0902da00b110707028500380601c40c8a040d80c10040b40c1198466956 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355185971 1250 355184721 355184729
    0x4060503150411090406020d0c020c13181202070612020a12020a0c051c0f050322050708030a0801180b09221a0619030c0320030331 58
    0x1d040c000d029404001d11001c0040085400040201943e801601c80340050760080b4410070016803a600c014200000b5500111108070465010810411141da80c1120240c5855182400015200403400c0c0c3c02c612003800075030242420001c444900c400660001d1400101d070318654500f110340020004031000d030702c200d0018600107102c0500c0c0a043d0040c0e640101081511030429280d41e4445503181414207038801c0090210910701c4265640c0250403000f90303403542c01d09240041c610302d4100075003c2d100342c1214441d2040c100e4690900b040007401c2042c4e101800d4100d0803030740c59046a000080550209009040b0107203410a15034140d9030842c010480e031810020020080b59032407007190602551700c224626480551010076001065009201c801e081e489882103804070314142c014415440001044118000d00050007000440d00c1504560280ca600401e181c64914520304180d000c85030b43c4080e9a070502000500003c650703d0b0f1507805c070000018910490702c0e80001c0340703109210074203449 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355187221 1250 355185971 355185973
    0xa0b040207080c060906100320030f010506090c040b1c11030103060603030909092310060608011d0105130f0f0c08040c0605030c0f0d0608120d0e030a05070209090f030a030903030b04060503 83
    0x4401c2c00050521030031550303000154150610b40b00b04410002f80380800351203034050665034030810f05c43d8a0529080d03403907100100406003443c181c0782685c41c020504c18001802e03469070f0020603104041d4032903080b40c1145101d0400301516540c403030501d03c0040c515480200c001c0786e030280000509800301d01800841d190070952007554458058501d000c08906152140d03500c7c06011000c07900342c20b0500c0750101806061752801d07000d60520803015801780904150052a000710001049603903500d1a80310201080f124001c0b420401e01e080c68805409802501c3c001d0034142040701c402c2ca9400800c0501c41c500606d03811480e80d40e500e8040c0c0d503030705c07041c0c0300203d485908002501000e41d014005004299002c2c400003002980c0e007400c02d04142c05070382602001900002c0020a540741c60203002e48401d0814042e6107080c510f440060700c688211070000f800740000a000a02c969014041141036803021810340366038072043e01c0010024102d50000b100401e00e00805104e550070309d84030718410390f00054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355188471 1250 355187221 355187251
    0xc08160c0f1d040320030a20031303170913050f0f0906010b071412031008030a12230106030b01030c0804020a1205190503070c050d020d02090a0b040207080c060906 72
    0x9142160302c01170a040c1011030f0300d0142c0c00180e506604000410500c0d040b996580742e8650800d90904110500900301c00083d4020f1000d00c031500840c002d507800b00d981c0404154402d0780303181031502450064000f43c42c2d000c1c074038500d80320b10007031207400c0a84622103000700c1110300e645211000d50341040a8a01d1182e5038440001440311884c0a401032099030702440400244013001e1041502d003004400d80041103880200601651500400844001e00007240c05141040704d10800100486070295601240b170762a140c1a003010b003807602d08081074148001130030703859684541025002c1c01c0a080c103a8002881c14440c0909241b1407600302d8056503005000303080e06850306140c41400281d0400549240c021544100c4080c0013420081c08210300c680c001d96101c4805040030108008035030f0040e4040d00b08a5010380c0143d450340d486a04659044074184055200c1200c4200140b0f5102d441d81c4e002480001c01c4020320200c2030203420f490b0000c104650301990341305200e03622400103540c50040d821842c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355189721 1250 355188471 355188473
    0x10611060103141e0d0f090e0c0304020a030b1f0f0303080604110c060108060a06060809060a150503100510050109080a150b0901060f030b010806010207060c08160c0f1d04 75
    0x883c40440c0c0501070b0034212451548081d030a000c50a0100c44850b00a5128500c880061703600705041034108041c03420310090052525400c801e02c0b000c02403064049560001c0040c04541c2e8541600000e1904600c110103d4079047d0910188042c07011038a5032030030000c4038006000c01000c8907140c1a6941517031084c00d16210441448003400c55410440d100c40703c14480c000d1420400c00c44103008210102c003e00d101c0c207109680004591641d04190304020b442c00401000107000110580c10580030080094800c0f00429554004903140d0042070341809006141121099a904030034095075901c1a9011202d68603401520014507900c2140050340208000c0e00120700c0300c81d9500c00c6420300c10408030b070250780c1c0c000180d07030450709812142c082095045080790079a494850f000d285413082c20007001a00300711380042d5540780c1d11301c02c40c410040c02007501c004002c4480c0035250a1200d0150080000400303103400001c04070745c0d020340800ca0a01e90070000b116800d45400324144002e03690103066985603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355190971 1250 355189721 355189733
    0x10507030513050d0308160206040f1218060c030e09090c0910030204060315050901141b040801020703030902130903050904020c190c0521070902031008030c0102040e010611060103 79
    0x8603202d00c00c21641890000145602c5440001e415540b0a0b0348404051070316030240c01c0400c0c280f14698003103600c142c0c108000140c05903003444085801a900e17114544c60b02d0300856030040c50741184403400200f410005201500f1801d13400850303109403184014202d5010602c20501030480d00100b1544c015151341200d400c003402d84a412001d0101c80101e43c41c1c50341c000c903066400a620840d0384c8000c5420507104003080b403040c0ba0300110120028805081d451000071142c5038081e0880b5072100328840ba6000018048040b100100b84001c001e54440108c0e0801034003d04a201080e0702601c1c181c1785460341c00b0050710540b0700d142e074503486c1c2c2c6007080d5040c0305110080d00319200280030741c42084200209846203d1249080d248503403980040b16040500380305041300c1d6121213240b0310b1080700e41170b280404081490310554035540401604ea0b07940a52000d500f9015920400240c00700050050700c220301034000b082681c560651494113a40e983c00215a0301005201355101c0341c20042c014000500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355192221 1250 355190971 355190977
    0x2010e0f03031504150801020c0c011d030606010807020f060408070201080c0c250305060a05061215190902060f03160503040206090111070f0b3a0b0d1a100b090105070305 75
    0x1101c45d507404075294071043c4003400c980c407000040e41305e503021031500d5a556a2107551440200300200b141607541c8401e2001c45c4e036403007001d4103190600c0381c4100010032039442000701d44010082042250392a05082c03d0201aa0303000d8082640042c84110000e40390402c0c450480308010901c50081c80043c1032642e960048000300464076098081e11500000820b00c04c0068a0207031086040001d40360405804121154a00b41600080b94008a2046008460701b001c0c507544000019002d25030421480f9004000786062800258011800b10303102d0001070201000d184030b002c01044107404148000c1007507071903000c00c44001354040c0c03040150300f440e544685040500d00004c4800c07039600584a4042040e403100da03800c42e218003100403805a0904440789a2000c485a6000e4050500d540d5407526252000c13034240d8400225440e9440581c468403070541c15101da5802403018003042680056070640000c3c01c1c0c0325110154102c0c0c0c0c010540011000407126100d80585440380342909541d42560550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355193471 1250 355192221 355192241
    0x3050307030f1109130b01170a2c010501050d020f220c050a26060607031b080705010b3a050318090c1303151b02010e0f03031504 57
    0x55118900b110703008505000301c0d0740070f042d0650855250003200702401004124003080007041c1d8145034408160342d0b040b080c4081c1c0703174410040408055030341103a844040c00c6a01122082c84e0310315081c140940720104d01e940c3c1045035000c000d01690341d981c81040303025500b603040030390b01a5850714441110b140c400708105100440741c151104008031513100708111685a203074480421000200094290b41c07007912001d1100c0c80201740540d0040900440c5900a4002c149c58094100005c40c102414000c0c10030350a41038942d0b020362860003440c5030500194101c1c6800b01c600390300f050038040981c5052001d00c190201c010420031b00c081034041c682c6c0122090807204034a00102c02010300d001c58000d0004000d0305800c01074001801c2c03402010301c810004010401015018144060310050000c191a5000c40f500004ca104946401642800040424010481c007078222081c884000c1074040d00b0181203801100d003520540502151401d40728442242c10803001039000302e0107461842c00d40e2020100d9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355194721 1250 355193471 355193477
    0x6040b250b06040c20070504061d041101090f030804140d0f031d0d0804140d0302030906131d090c0d02010e100207171506012d0e0d0308090c0603011203050307 70
    0x4400032201500c043c001078a905c540044405010034189409044001d0a550004025600c200c00d0b46402c1080080c000801ca0b080150100c0c05580c07107001e104000d4002d050700040300e141d691a1414003607029210b0800c020108200c0d803029898180d40c02421a03401074a110400c1c815503804440e41400d070b41c141001e07451282408003403a102c00350414121440303006960760741c60038032166410010312504054800d500e41c05000d00065800b00540342c56841c01e540d01611481d1003120044411000c1e08a0f000d0740d440c0c007102d4280b20440d6505640100d00e40380580384070800b039034140301c1401319242e40031380410801d400e40307801d1342450348600c0d80214052041c2c2e2000e44e00c1d4091128104003207140181564015103001840c4180718640c1500f0040c00d003025004a00d081c00010150700b00c001141c10b000d40740e50b00304485107000b081c0340c40322410020f014140c121001d24019040040aa540c8a0ac0384100b0340220058203245080b02d058079a008190350540307406035012525584014021010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355195971 1250 355194721 355194737
    0x102210f0408010509010b0d080a030507051902010f060801050126010b060f07051510090e010e03160b13210c0b01090c1101060f2306040b250b06040c 66
    0x6003015020107040501000c0001280380d041240f40705096840b400c00302445000103414080000b482a0308840209900381400300382c0342c0d076a0006407500c3c00b84c981900c101e80003030980880c070182d06511480150740005010072442d0b440303184180c205c450034080d01c00c030780f40002d8070f1138184211707030207a5140c0302207280010860301541804200103030811004a0381c454400b203012000c104c000e00800d076180c200d22001c03030348601d06250110b00d6180310384511210555500d182c014004029040446254405001c980e82c500c201080d020b1035428811060300c2d008161008660088031100d812040e468008017040d41480d2807014509140203081010300c00c0c041a00b0030500080e903d15841c6009205610b40040c1031f40848001070030b0005141100784159140040c1800304040084480c0140d8040e00d0300600c1d4a81da5010103005081c40d01410307940324002140000c0d091081000410031942602ca41d040d240d030201d6950745840c0544c050050080f82c01d100000d8031404c040c4d00042401102e440d007010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355197221 1250 355195971 355195987
    0x80702060a0e03040f1212081e04030315030302070f090501080c100210060e07080f07080a180803040b010512120904090312020304050a03080c120606070206130e06010306090b010221 80
    0x401e850150b00900e64581111b100c4020b00c02550300c010326948090a00340d980340740c00c1540b080d081102c0c50064518141c000041030a15200b5807100101c000d1040070082d01d0340e2241006580c404a038800d140b42039284100c040741d062444d005490407610316038010000c00c200182048141c000e161500380c01c52040d04407080580e1040d000d110f0050425500600c0c4070304150308000d0203c50000d1214421940072418004134960001d4070310b07400042140001481d0401ca008004221070720314014250040100c14401801140c4000e14101c9104480c06032140c415010b02c95194000001f0341214020240300c00b5595041030781010a0007442072810110203101e2600c00c800304e0b00151401d860a5218170000020560410020b0781c0204080c0e91582c100741c2c0c84003403020054801000e040c00785801007546000c544540c82540d89076140340308400c410301d8440c035a44002000071100d041c00a0304091001650b81810311592020784010383c058498017014080002501c002805880c00243c02086010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355198471 1250 355197221 355197239
    0x3090c0a14010e0a03031b02060d0207050123010501050f0a0507080403150b12072303010c020f060705031605070f02220f0b0609120a05010c090312080702060a0e0304 73
    0x800038001d441c1003200a5040348000401410718001418040d00c0000024000300780c2040020964810138000c849100d0b090388042005401603401c940138050001c1407090030058103420124042c1141188890440740030362000c45000c1c420320485005c22020882d420400031501c004103540103441c140245840883c0d56904059413240e0700640703402d40700040c45e1424140b140101180c1d604101d500f0401c14000401098440c991441070300443d108070302c10750302201c030606420900c10f64028000c10440f201c000700030b03444140058180b01f02c4c0c0107400010310400d01440949014141004507160451031302d18096503668404a81620340a00c4035103410016540c4040c0004480c044441e0441d501c0a40c828510645034101180c0b170706503091020f0301c00d05413914000e8900c1800c08992201c032950070f019070241820740c1480c01808950805005880c581d070030510000840c5d1080400707039030717242c5800c03070403615603200303854a8006030807000104a040c04039421004500003904d040d01d1400e41e0f104200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355199721 1250 355198471 355198489
    0x1205030702010b150d050603070f060c1a0903071e0c051e0d1b090e060f041a01060e0906040209010906050c0f060f010501022802060d02040e0a0b0f01030b130203090c 73
    0x15843d44d0301c00210b807100312200340550354014030107038004c0ca80c1e142002074488142400b03004041c10820194030b608140030f0743c00091400c04220500440460400b401d01903160350224609903080c250280070b6101c400740140c10705610725007040300c001400b402c00301046528144c0f4441c60040d0080040c2500b4255114080a42c0c030501c60400c2c080b1001a40004004074075140c2c0c041610700f80b0308129800d0303182b0702192039a0f00000140c480704d802e58452810700b0001010007414407036120203100100c3c0694114102a110140c1110150600e9441c14104002d910401807514000756022070704000c440c0c00341010f060381c4501001641c03180c0540300d03402d9103050404c894000e844c0514000400c4156010300c0007110403050136019401181c0d407803440c2c071480c1010090083c080c800004048410061580c1075601510401d00c1c0019141000501940038001034098144110000340059041c3d6001e445a00d1040e10040d240924800c09840500001d420007410100e1600a602c51000b255465400e1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355200971 1250 355199721 355199749
    0xf0f0a11030c0d1d0d0809030a05070e01080610050315191a0a0801020c060c07060605150a080a051003060f0e010c0818010b010912030e04050114030c0303071205030702010b 76
    0x2409490340c2c03044020b003400344400010300600d200c0700a0113599102e0b1001e032180f00e0780040704180e80b80c1e0040302080c41d03d03038003040140032401400f1000ca4482c024401060407155140200e0b40151144c015107040c030840c500c94103500d58091440e003040a52102d81c0c140d482031900d1261350b03180144e0340c00902030304c0502604001c400546850346030989070103402e000c00303010588003c5052000009020b5a0b543c4060700d45041440d010170040200b001c15082200980710262a0340ba100b0788541a07941d03140c0100b0810780100d10f4040c0041d070584842e11580b4820700000c005191600e2460300d50100034441440c580d2010354940100c42c401d600700740030340410f02c1100c8d6540c440a14090003812528103103103012403030590500c24500c0c100c0c0e0340449102e05403500a869a60300c030129140966010801c000d12640083c01c00000190100b582c1111b40e81a00065098442c0c0c107454000305912803040940007031410f0764803041201c41c244248042d55010070b06000010320b110449000401c100c0400071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355202221 1250 355200971 355200973
    0x1107050106080303061008220b150d0b06240708040314061b160615050f1c0605040f050f340504021c1d120f0f0a11030c 53
    0x150041041000d10441008041100240d4218203040d00040d5030012503103510001c1000c10401300e05290203034034071a420120000c04075004410030303151200c0c100d181140d8004259015824610481c28144154030b070180d880a640c44d0196900c20030031010303034005158008108612002035003544e03a014014030340140500c01e416181c0c1e00d140340c207001d0f00d40600c003010041e401c542d00b44044915010741c4d050318842c1c1c0030056a01c0e00c01d00241c90781d40d40030b0102c000c6c06490500c600391f0700e100034002e1220160b030025181c1004244140042c42180b03019840440740c200c090308080000314403541d103c81c3d00030b88540d85e200c14689503030300c40c01e240ca03040c004142201d40111407002205d8419280d03802081c02c2d49061010154803c0248055040161003414000e6400192016402900c003040b82c0c82d04401030800c0090490808140e80006884191b201c410306c10280c84849041e81d40094864508425418a01d00000f811040586400c4000550184130001501610415042c00a0820640104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355203471 1250 355202221 355202227
    0x20303270109030b04242a03060311040e030903070b040e0f0114090a0621021305010503120c03091c0209060a051318120c03020d0f050a0c020f0411 65
    0x112a495580300300a0500600000400016a82c1004103030300913000030101c050a00d030941c050326002600c00b100301d4802d00c0d01c40300140301c14166980725217041401d50a2040d440e40707220300740c080300c801d0701019101c84031200b1400f081e850160400706014042d40203490503d078240000c00d00c0c1c40d4907500065440d038400309040c0005800d450805510040c0081007030309035403518005190141d640c0b8503040c02141e080d00001d440d503219410450060402c43e911400c3d001424414418424800c40208d00c203c0c421008554442c000d170040c2810b030350004018103e441c2481488043c81e60100c0104440ca01050103818001c0c1e840205042055052810603000c01119204000705010010180c0340b08059000003400292584442c014030750015010001e6010f2040e01c10418841d140c22008019020103003a410825500011610f4014840d408030741c8040c08a1500344c403001210b00b00d040c0003580611030b916445200b003525460190004e0142c100c82024440803034155049110b14018002c000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355204721 1250 355203471 355203517
    0xf0d24230907031a24060708130b0f0406080a0605010918201c0c02120f1303030e01081b0f03150a03080c0d020724050d14180d2307020303 61
    0x20880c0d0000d4220417060100140d000c140c0000d14501034030f24041d0014170080380c041e8000180045c0c08000e000131660142e143e504d00741142a4030340c018054500003810040c00310760f80c510540600f00945105848a880316402c2480c00405c2c0d44c2d4000c07020b155181c84000b51410640e02d4888a10002c1410310400d0ba154042070b610b80590b84a8054034000328500454801c0039030b800f06400528800c45054240d80d690095441c402d04d01400301d02900301c0c881401e0000c2095000003122301c1e074110a1f00ca001640d44c490010072000549544025281c0004100c00c0f00c05405e540025607000306980031404000320300001042050b01a0b81040f24400300000e030003000d0305c4007044074003c9001284018500c0c1c60414100b101c02e0803124081011400d480301c0c01c4045140140140c41f82144011410400d15071100c00007001d2076030585092000c800e1142c94041101d101040c0b281d02500540c40b0f06401c81c404a0019603225820b000c0b1803244903050100c0801607500b8001004a600e80c20340a08081ca84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355205971 1250 355204721 355204741
    0x2d0c071706090c0915040609020a03110c0a0813091401030525051c0b040807060b0609010e100311160c0b0a0c080304020f0d24230907031a 61
    0x18020141440e64001010001d107110002800410480241c403e09001c1c2c56080b207600070102030a008952003400c00b20081024515030380908042d6405540911000890100580300c0c1d10561890385c605030010390004010503c450014681490014103c070340050351258400100e4050506170154184c10f6001001400000c02c1650010320015000a0700380c0210007161005105174400c5a026a4611090a6036030b004085002c0d5141d030442c00300b41c4146050720707090b01c0a41c030011088412901e0b1581c0522181040e6040d03400001d0103031549400a81203404009000c0c00e451111070805464204800580d120b5a0150806485002c2422220501131511060080c041d800c02c801028082c03200903a81c1d94000384c90180f003034018140a0b500e40300d5001003820749490b1048a5001401d0000803806c000ea4003d001000400a002d149018091510594181c80360b82a1900b04031a41407840d5006100d1001503175002010749040740c0820f607880d0343e00515050601d00a02d0a82c504400300424109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355207221 1250 355205971 355205999
    0x905010c020d0906120f0615090e06060a1817031b010b061c0f02030106120f05010b1806040509070305060901170604030f0c021201020d0c050306062d0c07 68
    0x5103600241001048042c0000d140c80f04601c00c0c02c04200145000740c8002c5400e0303104805141c244d0f03005020700364944485504640604414a000035410240010b0140001040d14015400205030f10b1518503c0001296000411080e40854180b08400000e2120b00d03040c041c1e58083d070520107192116004203680140545070702e6131107401d034103068060b00e6582c0c2d601c04803800b02300312000140c502c0320040c03c92001000c00c5460703101d201d8800070000c030341e80350403c013582c807e04032368181171080725842e545034400e4481c280f00d045246a814401140301101c01074031600700b0f010141a103070402d81c0c3e41000681e880001e80d40038001c02d60b90014400f46051640301343e80582410b807401d1040701e401c04002c5aa8500c01400a41009041d81c49910f03d227125001c0b40d22100d40080c051442e02c80081d41e140d00035072203100004410f5142048aa1401d4040c2013600c0c842e0034010072a07410202040c510072465110140d25144041c0245500c040d01441900506684121840101f20090400c9182c0031124 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355208471 1250 355207221 355207241
    0x80603100c082d06010507151401033e0414040804050a08061902071106070b090c04060f0902030402180a02030f15100e120a0308060a06090b07060902061c090501 71
    0x1110441001d6400e0300c3c81d640a5400c01c100b0b180403942c0d10040c0c100440c00250311441403031620f080080d000703403250022801ea07040e40d000c0d00d0b29a200350031a0320f0144060900260840b4640c061640f00654041520107a40140002070004604d0340c4041a5001a1003807c8404481300040400e040c00343d4200744440034080c3c9000001442c183c100300340e11a07013002644132880410f680000303c0034200102248070440c80398000d42002d4842040385005103521101711072103800c5103c0d0b08e00f2440d032032030b2500500c01180d0100036074403241c80c1030074200400380d0710003403090f41c00034030703280042511041c1d01031514440c1a0030000141c03030b801d220401c2502c202000d084940e200c8103000b90610f10303690707903110b00b02c0c0b0400c10b04103060607040b403c6c0415a000c4c3c4c0c030031036141d00740265900981070540040050340f08040c22900b4882071030b1111001d54946066000d0505503150902401e0001101079010030020341c0000c10712410009200040e4809000940c05000c03800e44948920702041401d014900c0c0071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355209721 1250 355208471 355208521
    0x2071409070903080f09060a110f190209040c2408010b030105300609030408070b04031a19020d02090915151c06120311060405030a080603100c08 64
    0x50030141d4000702802c1e100d02015194040008482c03500306095000c640c0008806407038552107400c1100080c00191ba0300c480300c0000e01030300d4103001d80140f0118559045000e0382c040ea0720201600d40a01c503203100010421508200500404200b048015030402d0207521500290380c50700ea03404100600204069120090104013400184540c1d0f41c2c503a0740140e0500840c0902e0b41e0000c01d5440385002803c1c03003010500c5401800c00740104c0744004030081040d03c552404450f8081d03500c043c031000d544039500c4098810302c60f130520980c0a107014105680c101c60b021171142020415041c0c01e40899210050054040341d000074003d0442c244440c411f039016440e020404d44500002022511000000040d40180f48000031804410340300103820f12000b060000040008030b443e00e00b888903260305010158003003484240309010598000400610032640f2002031400c01c0c005003820354002901604a80d418041c03010740710481c01c50b91003250010490b5980702800c2c2d052030000b01c0d184075282c651080070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355210971 1250 355209721 355209739
    0x915040602030319090b040c150203190804031713060b0409050c060306060f0d060f08060403091202010c14060f0601030b01020a152406080a0b100f03020c010c020714 73
    0xc103402205036584803520f007003407182c0c2945a103030002c024900c0340c40080c0b5511850007440305128000031040d05071003030b00e12001c2170a201c4d810280d98078000d524441030760700743d100c20002c0003921400d070813a04184a41071004070541d84861001910324116510149584000009030a001150107804000c00c01980c1c10022143d180d00c81580f161940d11025004c0c40001000c120940c17201c5044420120008142a0326500303070b415000c000c2c044904c10201515500344010901c0301010070080d0003240c0c1500c0383c1fa20685021280444802c04031b0090b41841500442c6401040f000308401c1c80403070030700014194502e00705041c4880b100000d0605810503117400768581041c2d800003000645c094005564000c0601c3c0d00f5040d80190068040584040c0c40e540c00030b554118010862400b1f4071801c1c0c8580e10745a54513202401240c68441b20980d001355104808118075020b100c1031070380c0035240d1401500d0300020246090a403445100380f100142d10040d810006450150115080c807030b030407198098 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355212221 1250 355210971 355210979
    0x100206091c05090108100512011b080c04030b090c060c06040201030c0509150c03130303170703090f030309020d061805070f0f0e0901063501050906011215060b091504 73
    0xc214000d100343e4505112900010540200d40c04041000404000303000c1c100d00d4900f0340d0400c2c041d064120781e07030b0303500d451081c01c005001d809100c42d00d20034114880814101465519449803504024010520501908850318542d4035100024241015040010202800c0904c00141254000c810030b904000302881070030602d0b41c803808880c1003150403001d070617101d003494901d81d4154441c610000c401e9050f0b00c0f130000700705501b2006085030859209000d215035500c85c0c03070980a84035200e400030124200e000e0b403c0c00203402640181c96442c0040c00726802000d20b13644490890b5026103681c49031111440b000030800408014400140070341c10f03002c014152416880440b024114000c0320080b2004000042144409500c0381e4000d1010000344000d41e41c2038800302054070304180807040002e001c000e03440c5100c0014041c0324001c9064a004140311b0303180c051071284050461034204c5000c40f019000c406a0b0425004210217080b0350740781c1c60340e00c0150804114080c40400d407124000003007071100304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355213471 1250 355212221 355212227
    0x2060c030c0a031d0a03021b06070f060227030f01020906030f04030513030b0711030a0e190b070b07020f06010609030809010c05300f04090e0c100206091c 68
    0x94000062070281d5480d003800c1141903010306541072028044c6041030a00004504000848404480c040d8080e80e44081c100c0000c801c64011200c2110740041341049410f00040d41f54460880c100d001d035034018180701b2070160b040410219121054ad4022820b4040c0740c0700d00c1e091000303040150038803000f1440d002c1c501d03001c1511400010481e80303130001c0080c00a0117150044089034200c81c48008248100798030303403070050f000725800d0b0703036450024408949552003070900108450465855882d05190f40c0b01e4802007001064502c00c241c1800e0809100018404d5015800743c40c06030721034070341c03501213241c198802891b102140c19207007035a40c05003004000681c3c00112000507a600700160303540c0c1d00c41d040700584030200d02400c0205144600795504140a00700b40a855105540012054803400441d0043c1510b00901c0142e00170f280c000c01c01000064003c0e40300303003902c01508003514040507000002401d6000c180c501080540c100108000013100e0a0144807414400760f2412056107160a07401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355214721 1250 355213471 355213477
    0x3030216060606093309150309030f0c030816090b04092003040b0f0924060a0603020a02030d02090301060b040e01030b1e1303090305010c0f0306080607080420040507080105030c0102060c 82
    0x7809100c9041226004698031038982c10014003029021fa800030340d00c4400040c024019020164000341140012855240c45070020794100d0b601a5107400c00c546802c4d5103526424079650512091002c1800001195404c8030301500003003100d658001039450241d0010200704030800c05691958408004110000e01142c10341500944400c1481599030360b8616030ba45410003001c0d111782e1031170590300300020b18503070b90343c2e10b91003024156548035107070792388030300a40580c001d00400b0070142e0024090040e0705800d035070203046100002000418a103540e00c0d401c641507842a000780ca65400410014420700070f1440220350840309035000c220301424044550307058520060f0051807e1b841c088030b6203003414495136000c405550444001c000107610751b00041d02104564001030f0200303045c10400030340442c2c0480c101d4030070030260b1148695036450ba900e041105217581403401030700c02448002031651711640b103210f200c0c1c0401d8036640195418001007514010b10704000d28115030121040150f003654000035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355215827 1106 355214721 355214789
    0x114031b040b190212040603090c0e0a021e0a09050103020906090405150f041407050c1e0106030c2c1305011e060f0b07020d0303021606060609 63
    0x401d17a01c40d8042058540c52003020300040158601030380260307000714070070385100340060b484490080c1602000d80e079800042d980030070100d1a04030749030180d0b81c514002804035424880811001400702e40c00d8040c50b41010380100b181013641d280c0d401990301c40c4070010020b0180e03243c41d041e804480701c03494036040d02c6100c1d8034031b0300710341c074101031003681c903113154580042e43c00c2c1d42c41d06000d42e01d030303400740d20405071612440320b5681342c490121019a140c40304280002c01c1c0c00340b660401e03001900440d00501a40d04c01008400710310004000c107064011600881c0d40c1c200d5551019a070905010103802510035401c107940840081b506884c13900c41041104010490a503d0341e408140c2444980a048042c2130b0821800c005071a180703404007200c0d8400e207005841c050441c00404084003a070303901107400589a40c400e000c6540c00820601c09803000711140708440c01600007e0000180c2001 = true := by decide +kernel

theorem cover : BRFrame.Cov 355035971 355215827 := by
  have h0 := BRFrame.cov_init 355035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355035971 ≤ n) (h2 : n < 355215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
