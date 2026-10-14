-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:56:35.184625+00:00
-- url     : https://prove2.me/submissions/bfb44272-33f2-44f4-a16a-8a75c158336c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 393884892 ≤ n < 394064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 393886142 1250 393884892 393884899
    0x90b1501050d111201050a031203150e0f070f02010516120f0c020717010605010f1b08040902090a080f03090105071703100524190302041d01081c0206010b03060f 71
    0x142c14441512a2401400b801c4c1c1c2c0d404507618540c1c1c070f42c030030030490505a000161281602680042c4154025800890846a103100c0300d140c5ea80d82c2c84007000e028030f049401c91480c85000060040840e00003e4021403590640002d103d5403414403440c480607621411705c00300300312111002c022004801c0e0f206503011254050244201464140082d548038600e00c00e403103250046200401d035210040c881c4000351041659101c2015810380c1c401c8030b520310070091a00701880f2510328000013607440c800030401040b80d0400135881c0d018910030421a260359030b02034502c1e40c00081140b01d0040c004030498801c1070003400c0858903140d050030300008000c42e105440c0e940e11000010b00946810001c00b140441340d0803260310303525503a909000c5103511035103000402142000c1c4240b81c1540e0004d0002aa001054a001030900b90340b1110694110001020406401000c100601c280e4005002c800b08402c13180490580510000900a540341c0c01445003481300240840411000e6903841c80201e00b420004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 393887392 1250 393886142 393886151
    0x180c040915020a080711150105060d0f0507180803031003171215090a0e0601090e030921010509030403030c0308061804030801061803020f1203070b130b0109090b1501050d 75
    0xc80000d0690704d8266079070b0340890195004140441c0700010060342000200d0300c1b21507243d181c0401d100d1141c01840c05003040a4561000255101e11842030310b01c685016a1110007540d03100140814940346500000c41d03d030820000c020701403449520020450b40e11101e0b050840c0c040c00300c050814082c0320007864103450000b00f440200c02c07500782c40214001084850200503290f0940c4003040368034451068030150442c4004104100c030f80d80c8400040ba0909059070702d0a8a007a000a100c0d400000300c0e03194008030b070800c201c00344400341b10701c0360b10011202c02180341c0b03130840c2c8001c0c0421000310801410800d0721000248541c036074803580603145211032440e0b002c904051401600841d130034003035100052842a001b20690400180100840e50003511541e00c0c0400e10090044048001e48585d070288401c010340800546a82c01840c0f140302c0307071310000e00070384561b2078040c0540d0b8043e400402000e00b025480c40104501d501810703000000c2100810904802c1001a56980151155440800c0c5403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 393888642 1250 393887392 393887407
    0x5030d0302040518250207080f030d0b0f28090c08070e010305071b1b0312090f030b16020c131d0f060103080c120a0314180c04091502 59
    0x16402802c191002241c5130000803403e41d90f20380d9681021540181c0c8030982121840000903003200260418510340b0568070080c1e1100c19039450101c542c0d0200c3c2c00c5500c0000d43c0303110300e2840d10943c6080c510898242c00c2140358040007c1c00800032039000307010950000c2c000e99854044c6019030b0002c2801c40004e200c41c814030000a044150100e0300038021882d441902c413020342c440d12581d445203441e51a4650241207149087c042080b60100c22100103025280d03114510240c040500001e520919000c03504600d00040113100840550082d44800503005082c000101103680b402d501240d120f10190006014102c12440e00c094441d44580102e03210107502c070a942c00d43c0003280c4515210301c0240f5500440006a940d8496030100d4040c1034000b03000502c0020b100b00300810a84240300111281d600240c0c44600896001c00b075090f0200e692011035000318a00e110701d0982c461101c1d00010041046601480c0e01e800a010f9028429581c5068400802c0b00240303400d481d0410f012411500c0b4140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 393889892 1250 393888642 393888647
    0x150203190905180c0a030b0a03020a1203090801060e060d0302030d09080c010e0a0503030708090a080a020106090b030c10050901090e01090c390201140a020105010f060e01080408090a05030d 83
    0x707841c001c16001d80140743c1103d46a00e034103490507008803501c00b2080d01d4600c1d007400c00c40040120304030b801c1e4081e20000d00040580d542c100c110018000d4040f0354054842940b4010308242034a60086c84a40d0400c1c0042203901d041c0505039900217010303643d8045c441d03a81c0c81c1c00c03800c5104041580c06c815140c000c1200520000384041c0c039090360b1400080082007914400b10f40c1e610002030004090750720420004100510a544c01e40c9c00400d0b00c41281e20f404c189596011250b086000380300c0050b0f540c0c031010010701e030b024021101001802c0e00138018410700381000c1a069242001d69405104002a2042090340b00300d941c3c0e801441904803512582d41c450884c1c034050700244503c040050000d441c030944800d52140031588103036140040c001034070b0724220b010311040081c04040c5d05015103c0040c04034607040e40000c2c411020b45900002e0b5943c10410012408500703030300400100008660040150b03604840d455400c25040310b10682c440f2001c000241c11081560002038160144094100d42c90b034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 393891142 1250 393889892 393889907
    0xd0e190b03100812040305100e070e0c1213080d0507050903190209070f1d04090b0403020c10020316060f020c0106120b0c07350c0d09170715020319 65
    0x60f080000d40e00710208628940d645400b80e03000c0600103400c81d55502d0b81c1e1100950008003441c6162061313410090340c1d4101042004812140028803180c001582c00350722000d12140c550120486103008226081074803284050f000d0848034050003545d401c04135542c9401030040d9102000002c080381c846001d07040c0c250010152aa9041b800f0b4180d400c0815103481c002c100c00c501c641c001e543c4000029128548010100c140314000582007136a034911200401c1d194106288100d01a170000d00e180001c180c24402c80454464941c0e0031904148803a0828a0988101111140d04840e022552944005040f8000d00c6010045002c070340c60003d0020300c02c03484d46ca401d00018011042900c0950310356010103414851101d000340010280c00c100085a030031a80b132030040303440314200244941c4c2e40e21640010b03980152201a00d0390b0108a0a44041d40d200d50081c0c003800000800700c600d110509441da13640d09031802001c0680b070428001400440c401c0058420500b5902c403000c00035081c0b080080d042c071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 393892392 1250 393891142 393891149
    0x103091e150c020a030c1b1d09060121020f060d1506020106030f0b1522182d051c142701030b04020304050607030e0d0e190b0310 57
    0x69403103022071050010900c500ea000036190f0300074142030f001aa50403220640101400c407004039003028115540c050600c0004090b02c5106080032408940c80b0300d10305240c100405452595002800602c0000d03003c2c20780d20180e0b22103003042030342440e481c03000400c070000030304401c1c2d002900031800c50384031100c81d0400400407a07242504120310b501c0351800ca00b039400501014186031860030180000907007941c000395220010072003c0c0d04608407440010124084ad05550144c4014194856840706251044105102510200c2d04520700b440c1d6550b03a4506c0848402d2101040380c01c503007142a8000390300e15848640c4082601d06109070f030b084812380304110f0001da00c00602d012084841c002116000c40398180c0310504076002c0c402991200d0301e880001d099149042545403030390444162128006180158450409400c4034074088400400322a4103411640c5943c0c003403040100310640048061240c40300c15640008201d04080035000c011009038410141c014000040244810044c81c1d0300701074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 393893642 1250 393892392 393892403
    0xf03160c0e0115050703141b0c03010c080112080405032b0f021c0203160c030506061f031a181f081e0708070303020a03090e130602090103091e 63
    0x1259110149801c2500e400d000d682070030303002103600e044001c0c003ca018050b103510a103841041045441ca031160141c01c00500341c0185003500203121308a980030300c601c4440040c00d40082104243c4180700800710305061190300b090400d1a048201840900c400300d601030140501241c030944c2000340181050880b801c81c0600710841461215800c52160301c0d040051540b990044c0051805064403d4101000c0c004900139844204074410b908110281804901801940801a001d155050942c00d1400082c40244a070210414000a0001601040078920141d141c0082e940d0300001551b6501c00790100100e9114500e485500fa464016942251091820a190522840301941d0510341d146441c0102d9010b6008904a107a04c0c425029440c0b22000000d0b08549d90715640d00780490030a04190402d80041c0c1041504c0818150040c040d60b000f403962041034011071510740820303403600c00c1d411b03c010302481d00040c090105070300c0398100d885016000030320002c003401c2d000341d080c0c581003a1300c404884 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 393894892 1250 393893642 393893663
    0x1090501080109232b0201060801180b091207061a01112104030c030804080f0c0612040614090d170f0105010c050f1504021305060d140f0316 62
    0x5007110180a442185580721015031080c0307000584a03091048100ca0b222202c1c860a40400c4c04907204000c04041d04d0340b505c640c045040c40051009007561800e03040003150b0703810140c25031800b1b18040f00100f41d0a400502b420305c582c9500c600641842ca00c0c10010309043e10205030002445403070307440482034000540507030300400b50140054802400214181209400c0483c4504204466a5120300c6138861170b040ca030f01c0d0549035507030000c110f0000d400c25200103401050611a040f02009a000340c544188020452040d115001541c1440b40c44003e52000c540d45000c2000c20180c3d401406003140c415414040c0351034080c609660300d60032030200e203001810580e040224407a840c40418000c000502c91068184e08090040d9480351120008440304d03c1200034114444a040c40349000001c91582c604205080a00400c160080326554450b40585440180950781c0c0d40e461b0b4044003103510181d4000d50300f0114200d58142a0344508bc000c0b103000000b01c0740c4441e400324030303001407251140844a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 393896142 1250 393894892 393894899
    0x1060605040510030b1518040e010213060503010810151d06031b03071203021f0902010210142e0f0f090905060c03131712070e0f011407050102070b01090501 69
    0x6054649062085400c81030302207001890b02400c2c0c000b0482620000004d007c0b43c009640407804039001103c180c1e429035030100d8008407009000700e102000744060320700582994100080940c45901540070862034990750754504805003100b607902c01c002c14660b8255140d08078a10100f0158200403220b080c881e010f02c0e41d240d02c090440481c0780b904c0250140080c601a070502640100c0300c030000d50290b007503104045500400021211107071032000203000d404100c00f0041d200280c540707800c40301000880c42c10038420200b640c0304211855070160003148400402d4016000542c405001500704e0324042c3c11341400404c3c4010b11017103400480d01c1c2100a089141e41d0f6001c00c0080740c620003402030060f04034402007102203181c0800346400610350400010080426a1001e410412030104407003084804206440c800a21b000e1140d40f109441c10881d06d80b92200e0002a1500e0f0b90842c09030501005100c0110000518001d95050b91f81c450000c540d101500d042440c401082446000d2841d4101400070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 393897392 1250 393896142 393896147
    0xf04020109181b021b06070809211911040b011107080c011d1c0602130320010f020601152c030f15040f02270a0609090b040b0c0c01060605040510 64
    0x1840a0501c203000c17081d1590b07401c00c1110729400f80d10141e070700311018001c141e02652510503d248480700c40c1b03440c0c0c6101c42a0a20709061241c030249601e00c00d56400501c60210310031340c00112851f01704a0b0005128420080183c2d08240c40c9840b03122584142c8078046484e00002543c540000000d80b0b800f6000c07401c48440c2c65295400c076500301c3e040700029185011071a905502180000e11414000d410308aa0324540c42040302e90740e005440520890b1014903002c5440d22888400c481c003881d0000c0c80b07291511004c2e540f48018451500f02880041c0b803003022030f20030669900ca404912000c240f50307408011084962001c0100c0700c5119010760710142400b02c800090081c1c4490384144400c1c4107540c0d90300d4a030342048040c0b006a810035107246400340140800d00310498070300080303070a4070b640381402d00510080782d499070460210946400c0101d40403400440d440c0d036005d1391003031800b0038a9a4000c0c000210340182d42100d45258207012010640a41005c09082910801c1d600c1080325400303603104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 393898642 1250 393897392 393897403
    0xe060301031203051305030708130e04020a061b050601230907080115110f070f0b040503100905030909070906030c03020f0d0c020102041d01030b071103030f04020109181b02 76
    0x24a68020080b00d101e0140c00303504001c1c3c1c410b0110009500308172443c0c403220305580c0309050440c0c4458000801c201042d002504100142143d00d42c00310703851410741e021544030300007401100188244502c07818240c0b400300c1c41f410a20380d403040695500d0b5a491024081506041c600c2c0d0ba001c00fa1204203a840d401c2100e0583e102c1e2982d503075427040702e034a00500d0481190383c21081c041003101e2058880340d01c0f0400c22511918120320720041c5441c41c50010138561208450704820200e8100308403c1017165000941b554512003825000541c03c0100d1803e50714601c030307000c2c000c0e402910700410854440d03017004019088610903107051110700b008038821400c0b446011801003241c1e2051001c000c2d550a241e004480f44d410030300005150a07101d0800303c6e13180a095506280d0103145000510401c200e40300f1694101038641031201000c990781e0980c54072400028403080c5040300745030015065a1240740d81e14001d09000080c800804162100325020748400030703401c021003004018140b071680c4000b41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393899892 1250 393898642 393898649
    0x181a0703140a15030c030b060f010306050114030606070c060507051c0804080c10020408030913020909040f060b09150907080f16030b0405161b03200f0a0506070e060301 74
    0xa19100555641d0603070342c003d1900b41c034220844810201c0c08000241c1401426025502550359210240340020800008005c2030050504050908404218a0b6004500f01188500201e10180c407580c5000102c0d16030700070100f0160101c4036160001a0a0f50850700501d040c0e8012025200d00b2a080c84084401e0164501d02400041600c00000c007c1500f1034040c00c06070a40c403003602c101e0188480d041041c4d07000750704031a801c0c0d000000c1800b92440c00c00e040300f40200702c280d81941000c606100040010700000d00c0a441700f480031702103004010300c1c0c0d4032040c0320410042005690b070800c841e1600c5101047c036900b6005030070342000300b46100e000745600d034070490440556442c265a21541c0325589031241d680401859107420f8440c08544c1c460041500c502c0708800c514090701400503004249202040c910a4800303800186200804e6010079400014400701d6806008080070160061400c80320100c080c545003e6101c000c010480045031050207103045035903c4501480180402074140300a10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393901142 1250 393899892 393899921
    0x30b090607050f042d0303080601020d08041a061507030c06050c0310140102030d0e0a02150a09050f151201050906010504060203090904031107030b09100e1906181a0703 74
    0x110810540fa9031354074170700108040c01c0302020813008004140810a8094004a0209a01c0b40400403103581c108040404060103180036096410b03d503d5030842151903414003007042000c0390004050740c513001152002006a400b4031030780c0b1034032424001c0055180c0042245c480782000c022509000d40b500c250f80c0141d00005004481030304c0e16241414007904c12840605500080c1700f02d82c100b00f000e06c101c022901c24440500f8203246030b80304001c00c0c02e42a401e003410000003400b09001f1945d0100c450000e90380180d07a40c281d40c040078000070300d403201200882102c00ca0001410f8007490480c41e01c0341c2c102c62003034640c070009841c1c07d40151040c2c0164000c880c01648240803002c0d0900e808502c041e0064080d01b40240c99034050840d141c01c0036107075003065400155100502041030020006c03184000b16650003000341c60b8402c01a141c444155062206080300e00c0c503100403e0201c2e036800120700101d4860303151a03217003452074841d482e41050180054441245000600e699003c2d004841e12001c920 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393902392 1250 393901142 393901147
    0x70b040803150a030b0f04060b0a03080904050708010e070806041d1609020406050a0c080f0c060f0702070f120507180b03010605090c1b0102040509040809040e0f120a030b0a030b090607050f 83
    0x41c02c00e4201400700400c1a40e000b616809c1c4201507894103140706010310302803003000b41e50725418418003003501c2000d410b006c200040e54004001010441d000030750482401c0c80d018910340c54050000d00940b81c0640d9880030010b82691455410400203008408200e030041d00681c1250758405120417801584902404241d0401900910313501c00d0010407038543c030410516007800410200460280c112411104542d446101844044441c420240ea80b00605200a05140d8101800600900314520650340708250307a00c02101040b8044c0002c1015281151003405002d04818147c2c010f046640d0030315019500c0d206000c40c00b810003a101d0b81c4210035408007a46805a0300c03009800500541e00c3d0301c0910356090101007039a07521309891901550183e01107a8031030341100100320869030f400301c14190315445007210044031074020a1410300050134107002c5440f0106000c0c150064060211040d0b03000c0105c28011042011030031071103004003101c41c02ca5046a96200c0300341c1b00346c810f81c0034401286205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393903642 1250 393902392 393902401
    0x1090e0c13030f0501091b05010203040510120539070206091801060513060813080a030e030304060c020105090307111e1309050f0109030c0f0206070b040803150a030b 73
    0x200421070034882a5803514042e07601d448a101c2e40c0a121003c4420b85d440700d44040511064441440440c461202088403061030640040e40d40c1c41507119460050149420014110703005404040c520b9503003920500c07462400304080082ca11404032440d80a20080701c41c81070728a452802180e805913000c00306440d0410a40801c81c09400c000440350b4070100c80010b041c80344c24606041d5000345a10b8541a442d0910550217070701c0441c59402c08000c1108060030003c04014030015004140d802c0050715942c3c0b90785001c01c80180810b001c1070b4a07244000010700041005540c8401e0604d104e90b0300030402915100c0c2d04e542c6030302c11150050400585901c05d00003500e003260009440c01021a0000c800c469a6004912584c05110118028507954100340d014060103000044020000b2402041100019034000d48005103115025001d01c05101803d021502e604045172030711900040d0034105403816240602440d402100e0a80307100366020305032070030350030003503881d02c1600c0c4e0003040c407032070b9030b44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393904892 1250 393903642 393903661
    0x60623010c1401090c0e04031e080a090204020412030c0204060602070f090e01060510030209090619030f060908130305150408270a06050a0e0d0b01030803090a1e1101090e 75
    0x2420728403a0b40e6550700e58154002440d100d501c076004181c114448038103442d02c2d04001d41034200c1360b5004d81d0107000c4c8550035001141d04c0b07a103040d4059076005000840c042240003041c02401242c2282c860110032922080038550030000500c052482160144000f41d1504c20880c1c4403030007071242c40301d9405440070a1089006a8102141560b440400041d407259101c002850f41c081c0461354401190f80021190300c6810000c070b0555110741d01351410301e041c0340101d1075000b03000030901c00900100002c0e00e460f82000501e8200c2d507030564000c1002c548078507615a01007959100b9100485e064428101e81080318880c07031801030712a03504514550304000020300308802c01940d480c10300381c1d0602c1294800046541d0884284040d120658031180c440c0c0c41110702030100c640c01003916100382d14001030380c0e0018030710205003411740381d201c2e101940360380300c031001e09140c0600c2d440010302034902405820600340c030359000c0c88011409800c07000321400308000152003045450041c20f0398280e200780019441d01c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393906142 1250 393904892 393904913
    0x20a0209041406010b030a0f0b010f03020c0102070209010f08060a05090309120109020a0b2106030d050702010210050108150f040c030230030d240501140c0307060623010c 75
    0x1809030140196800519555609001090304498042d0030b001c01480602c0f10f40c1e100c1c05405d61800d08c070421071031840d030340003810311054445040200b54000070500c0740340320203405591016a014101820a5071540842c403400c031010702481905100314400151958000d0003290300a40e66240a10300e045c4094090040b04000103240318059900d84401e41d00503220600084c1c01800c4444125865404000d61102c3e54403144400002040c0c0307110038080ea9070340c00708454445030729500308199100b50354401070b4148441c0c000340480a500d842e00000700b5940100740c800300e0720f91800c1c011070a603417011407681d100e12090380e0141100c0702941d03082c40141050810308a815544c800501e0f0f010420700d0081c032681464001100b02c64002080b9424008498003811444003130510140e0b40d0b40c01c0041e030808442c02140b14040c10007101c4d400030740015080e402120455400d09090766030710b22040c140b0030090042c03849481e034200c0341d20301600c2519520350422120100d0503590122040c0b1542c540c0413410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393907392 1250 393906142 393906151
    0x80304030e0f100305060102010b0d0c0e10051903030206010603090b040633030b100803120c070f060911150d0b120a03021513121b050d02011515020a0209 68
    0x8240c0c64042c02403543d840d1103003242c030a650b43c2c0100f25464090002070a442121174114020140c3c550100b000134800d40303605042d03031660000841c19540c1d0154242098120381e022542107070305041d1301608405a21040d80c1968000e40846c1c8032640d0343c030030440443c0c1004c0c001401140516010038000b80c203540000346010350341c003500100520a41d00000e1003200211581003824100c0c0c0c0200100185038110561013500000000e802d10701c3d0000c0151248a0510b00e008980d050360b000500c3d00400109880c250b03600480740c40d15140b814a08980105201a410b44078000c495a03c4032841c60107041940d0840d40109090342848003d102d2940540300d54101154088005c0c1104824010108294906076000c0e60003004108118030108182d804060014045580e4030840080450018100402c46010524003000d03848000307602001d0f4007100b0380e002442402610084500c503a17054001901c804071034031140819643c2c0b143d03981e551281c0c59840308056005011a20054503040b441c0a070310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393908642 1250 393907392 393907399
    0x170c070305070f12030204050310060602060c030a1b0306080613080d0b0103140f010f0608070c11010e04090c05040b1806010c031707030603031101140f0c0d140103021804080304030e 80
    0x211415580c4000e04071402207281c034006079000c1020801450304000c44003e82d082b40c00d0810625007441002520f6180041104c12019800030109101300200e80c491459048c991021116229078490020b0103020603120384150b9100d03420214200c0b020751b03400c190301941c2c822842841c14034080b203002c0181120550785418941e840c10940920440c0556040c07103840b1400c0070651541c10300c400c03285407040c01d0304207004001d81d40080081a5400202c4035886980140144014407080380040b1004080000890381250600f0800405c10001111180c2030310f10854041c010001854140002c86400780c00780d26003011018049803040d4004c02405038646c3c0680b42030b02000d5000c015180b0300d24829210040000c1d51920100b082c5a405480d800012552100a00c00c41744110280c8510060142224011041a034042401c0721034a8003265218000a8801e102403000c8102451003180c00748000d0f409607610b150081d4140c0480140701d486a64480e080d2411500d858030300315051074100a01540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393909892 1250 393908642 393908663
    0x606032508030d020901020f03130302130609020a030506030706020d0210020f13030b0108010b0405040b06090c09030106090504140106060f0f170115030b0f0f0f03010f050412170c07030507 83
    0x210070758188000e144488001d0000351745e80d030211703000920703041041d102c0c004680c00a21001c851032030304800860480e6011513000394902d00e840005401810241d100c401000d20000e481c1c00f540d0703090307006140b080e0300880c240e4508590700d000598a5075500e42c4000c00507005201544803080b00b0f81d018044000c00d02104508141d802c01d90f08200e810281c000340c2c0c02c0302a103001004006004d00540480100544061100b03041603650305445103c050101845141c1240018140e038110101781c0d10140d2009000f403220a94800b0081d0042405490583d081c00c507400301b090401d041405030500310782c620b688094001c80a280c0440c1c1c01d0708075170f401404004103503942c690720384940005103010381540c0c00d9844203402c6019001e0102d49030305588078051911b1030301070b848995402c2c80400849000340c03061071241c8a244006801410440e09003602145008103000500c10903494550b003031041610356490b100880740c6085038844045811580200041150100191062000d407806d284100c0c030458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393911142 1250 393909892 393909899
    0xa050d1503050619200315091302030105160e330a0e100509130905191217060f0303070501050a0219090e0106080402120a03030b040e06060325 63
    0x211103a0641c001d84460780318100f80b00c0c2c040500302e0a400420421030b410802da01c0080840400802402503808041c1008400500c82c03000306400e07010b01c2040103000b1242440e080c1b0b00c40b494400c0d080400e901039031820f800955012480c4110303204e4601030340c46004039480756400304102d40c0f10210310070200951b0103890015450038100306490070700c03000d5040341e21496070700001040c06160584d814421212085001c91494001e82281d503d000c050703462140002d0401311400180007812402095480f0b01c0728222080e44e50483c3c4900c003944a00f4403058440d8000f038040f507076018049501501003901e0750204042c0e14199440807000c2c1805029681000c005031285421100c048440c0e1105507000116001c82500c0c265070090022510304040c000d031807e0003240082d007a0140142800c0c4602140810259560502ca001c028207484003100c0540c1d0017450700402410f1150080ba008070300303120800d046448082080f9100c0c40010340140110b01030400d0100300002000180030703141e0055100407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393912392 1250 393911142 393911171
    0x91d07020a0f0b061008100905100b040807050a1d0a020313080a03143304020708070c090b06070230010e030310080607210b1806031209060a050d 64
    0x10b0380c1400380ea24280c46244c4041071240c22610080004100300c21641088246500c4440c4c8009036880e034080001d0655800300f03a00c2039590035800c034580b01c3c1c10228000447c24000030b4088203561044e01c0244800c4d58907444d90003010001207080c2202d4000070006200200180c0c0a19481401c103882d4141c10300c2d0076100c246084c1d00004220b800251640308180f00300201410441c1c01c500c208400011600388103c2040396442280c400d402c0300a074010100040b40e0315901520700c040d4210182e0ba40e60010361810200c0707810240318102038141030181d9400316140507000d6901070364000c0e2507650030300100038031651504420490a50b45600141d04070038400c2091065444000000300250765a0600c0b000040c1c8643c4140e20940003035206108209846501c1009178003100075108580c00c20a2a040c8800c2c050020540050782000c494003018880110610000380a00307400d4060300c054003443d040c50942c078441c2c0300c1d049070018000c0040c4040d00d03120b0b41c0108100ca6041c1000502d540000480 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393913642 1250 393912392 393912413
    0x1a07020a140d020601150e0d020a09020a020d090506070b01050607020d06110d0f0902240403080a0c060f0504030206060f0d08070501290d06021c0f06080d091d07020a 73
    0x81242d01c4514001295030301008400d024198035484a5500303000e06070b0040c89182d0101c030690164256020007400c640701c0d24042c0001e080030a00a54450045400c001d607100054201c100010b030307000030006560308045d03003269031403508601c801c04182c0c20a81880096881044126000184a205c41c2e0100c0d035281b0078407004c00440e0500958400210070b80c0e506035118410092101460124104010382da01e403c0d000c00407202114401c402c080d0f501e02d980030390003560f0020300440720003d103c0001980c0803e01c903140718400c2c082003104c4052413401c0012944103d5000340036a0003403000c12000c2c40d203030403010030080c00104541c00383d100d103503544651500108001c64050391107a484041c010310f000020092010f096031410103080f400740c0059402c0c00c28800c043d00f4680d000074101e04402d040800c0e0503100c000000d091002c90580888040203103281e10400c010307405a16010b00400e84a603880c035085404c03c603070110890004100060b1214030140503a004c0d4400c2090150004100508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393914892 1250 393913642 393913673
    0x2031606060503211204141005040201260a02160204110406140a020a020906061204050f010e01060e0a1d06010e0f1503031b0c0612150d1a07020a 64
    0x20301081441c03901043c5450001c0320340440c480d4a08240004140100100548075641400c1c245200e142c1c44074140f030301e110341200d00400001e000d18215000c010350310740c00c21070090b4400c1c0d0300d404210403540c3e00320f00082a00d610000f200041440400c224160f903030082d211a9000342201d54003207880e0b074005401c403074a600c84131003600400300781005110340142c109146145525003840c40d050003904000d403920203980001313201d10303041804520740e40ca4100580e0701c20b4071006020402410320b4144155103001c8010815101e60030882030342c0c1d041c0d806006503c00c4464140c148182519002c00900107000307002c3e04101030410700d54030255801c0d01049003a00800a00d03524022074105200050403038000205034161000701641c0d041c005850000840c0c920503001ca0b1a15038150a0b21195801e003000c8030007282d4055004655012170314043e68a03240101200500944100312400900000d0600a580a002118181c034412030101800702019400f134118811344855210f540d0303070007051400940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393916142 1250 393914892 393914903
    0x182412010c0809190302030d0c030f020d05090c010e0a050105071406180f060f041112030a021e0f06070c06020405030d0c020103141909061404050c1c03020a06020a020316 75
    0x3083c00700414090100c0c0c080c01c0400d2000c28492089518069520320a100100303100c01c0d0b45020441c0c50038800e80c001d011010042c0019503460400c1c2c440d4a014000039107208085004188090f07500c0e6000b0740320542e8800025260140040c90100103481e95002a00c0a990b910090300d103d104c411428041c1c10f101e0f0303048107105080900301100492a00c004201d22500c0c9a20000500c1141001d5000940d80264010700302e1165000d010041120300e04c80e2041d0005510010804144d56a00403444041c1c400903581803c814082803906145d032402903484410380c80d000200860748180c80b48404401160240d00c0140c503043d540c40100349000d40d41261307500002c42c955001c1e0110b43c0c0c180107048a040d4980c2c82c0380c400c0d0411542141a021540d80e0800c1c84940d12018001003203026041074080307000f420310081c911b00d4241899620b0706081003506200310070828002840c1d5003805965851290186d004185096440d61000002d41c000e414890541c401448401d04140081111035101d0b1300c201d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393917392 1250 393916142 393916157
    0x51806030f0906010603061a0702040e0601260a0218072d120209091501030b0d0602030108071203120c03090212071403070b09040506180a0b182412010c 67
    0xb20800d042074410b810090070541003c0d001c01c540c0c0b10f00700b6036001c410120b2104030740d6005c06100180080c1000051610755010703200c00040c3c1c0045010080a0601e54200510043c18001c03400b9034440c50811002907000a041e9a101c410845915009a201d08107003442d02ca050074503050041d1150180c82541e41e1000324044120020380d0200f8445011001c1c00815414240d040b400260500c800400900303c00045018080f00303070b8400e130804404500e015018410003042405c10230045d5100f401200c031144030342c00000880c40d0110720481110780d010b030f49018252119080103400b5000c0480340f0000c143c1ca4a0055015964031069241c050a0a03170042504030b2805800312203400d801c50100d07101e0f40000800300041c0d00100704448901408582c0020581e0300c030000a07218182094524010604241c200300c08103840754000190703190b0807100e842110b88580583d5542c1041101c0240302015045c880340e00720350003001001e42d02c00008003980024401c0c4440c481c03c4840c082820000500c46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393918642 1250 393917392 393917401
    0x801020d0b0105070f02010c0501020d020c0106140f06040605030c0f0424030c02030406110f161403032a1e0a1e020306071b0507150206060406031101051806030f 71
    0x3144a030a80c1c1c1e8a00f820401e0410325103840749244888101c0010741409029070106080040a5049a12402c0b4200c021074903151200180b600078895070068201029090142c2103071450488104200e0940013810b4624150402d801122142c00107010765042003001d200e007074075165582000d4005041c0040000c0700d2005070301d580030031803704030308901c041c540343c104218a1194040100c0d410f80c0d070541015000c02940d90206490880410081c01d02406001c1c48001c4a00004d4004022100422049080d140003141015100c2c400c807082203032141c2e06140c000395800101c070010034075007591606584010103003161100d001010052030203001c1d084a120441009542d482130b40003c0e8109000c01c54450312940401c0d80e5010140c003200038000f54030000b41c0c0300c080c4081480e40a0358040152000039036111100080080710034140b2000d070044400140450800744105011039800c80c03131808140701180c00541d03595001a2600540c2c048043c040c1c051511144025401103504e0744034210b00340350 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393919892 1250 393918642 393918667
    0x80a031505031002131a030405070603020c0a060b0d0f081b0106080a02121606030f050705090a0b031e0f07230d050c270405070e0a0b0919080102 64
    0x80d80036800c024150041014006501e0000704515481da0000c00142c2c1d500001e207401e6050201580f0400326000983e056061141058000e18040c2c2c0c0300c1c0f021102503645810050b07060380a5110049010340c010800940416429006103030100c20161200c4500d882c1902e6440c44100b9100301560607a6000032401131021302c240380c2c502c0c2c12400c03500801c01c00d4180301c81e0580340e240c0e101c0040d2066024054014058801380100c1904441e9110400a01540c400c4041c1c0580f1141c261184001e2900d00050041d40c01001258094980103000d60760080c28032406120681001d400100c0001e1061544441307014414050740c02540c3d003d030032180034034200400801c4c3c0032030045040b800303003210b00440510070b00c0e1006640840314a0100400c2e00c3e42ca42c0511100741c00b45031514820b10f1006a4030f00001c40004200401021007a41c1c180a180d03030300f40c000e8408400b180020360300725060324010003070301012401070003032614020811000840220900301083c00140c00043d01c59600140e480020710 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393921142 1250 393919892 393919901
    0x12020108191d1920030304080d120c0f0804032111122a1e1c141003080d0608010e06090d08010b090103090f05010509070611060408190203040504020403080a03 70
    0x146401052400c01d21190750380003030036120351484c4103410710441c00c50b64196810b0003600d000e084503100302c410a48411000a102c1245248a1802103180c01c40d881d24481c86490a189130b80090b4846200700c3e203d0350340850740580070303003070700700b00765450b444840060540ea000b445000c50700d01c1d0005440c0d2a001c081861807510103441c800003010300700382d01d110f4448000e14000040b809201c0311902c030000510911310024007042c0200309540b0000384020b0040c00064000b401030559a003c102c0140c4030840065000f60603a840346050b01c05400400010307003d071001745a0000754040c04250155600345075400c0d61b83c5500200c41c103030460340030811240300c1001040c242c409180b521005551414000711894422b000540f41003540300e406002c00e0050b580203421501c0d03802402004185008a101e13610346500380120740005180d4441244d00d8000011708500541d00540260f140210490080c14209611117180c4254002404006803d07951440a0001035008094a03555102d032200010100c1c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393922392 1250 393921142 393921163
    0x230a06050112050f1603022803080c0d09051c050a080a050a18180e010b12010e070618051210060e0612010912031a1c02030f0712020108191d 62
    0x3d5120076020341001000400176000c40e0b405031003201000d0341c00c282215007241801c83c2c0528038a141e02c0e0000c2000030300401040701034002d50907507015801142c4100d405201c14030031541d02c000d950040c20103580d2032401c1005202d103d6800c0741c03855111555032201c6034001802c84004203401044c0540c28980000702d100005044030660040c46d17042c07224440d125403820440092869a5080c40f0140c45425404002d80e014010a4100810003101441d03019201c8003440d44a64052220300040c12750240841e0130706280e8148008603090b00342028094003108110704443d00d1b229500d80c44510103141c0c403d5501420340f2030111180340c030381001071003848000d44806418a030314007003420f408a98001d510407410841450046030441c403140880303007030811035680160b1110b002824442d0f5468140b41b02c1101f0b43c403d50a48415549440c6100d0311411540310301c540c194180c01d000c000642c45400c0003584904040700c8001911103c0c10308804031209070034402c0107402c1c00c01c1c1000701c4075000c000788800d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393923642 1250 393922392 393922423
    0x30e072402070501020a173403090b1309090809060a0c05061b19030e1f0f020301031a06130911011404081504020607050d0f110604230a0605011205 65
    0x986c98180e4070850b10880c4050441142080031a082410054082813250300d022030700c144038103080400040815076840640c0032008240346003030014130000c0a109580300518008409445645004417600c0501b8240004840c0c00300100110a81ca0391120041c107084e8446da6200400410035203031092801101a0003902c45404001d5600340f40e9040504584112700d5003442d00c410428131010a030040c0079a180d450503a400f8505001410078940d02d06e100c69030440600601c910951600f406d8200e100c00e00014000b280c00c1e00b8a0209801a05081500071201500480c0c03d81e540d4000c00b800c13201600030172a40040a00607882d4690782c8a0140c13118407030089240e03890a803901d40116070320140a6080a00f0084441c002020b642c2e0342d1041c1c84159130800d060b6201c00042d1040102000b022117000000b0418146881d19a4000001c00ca48a50b41c05a0041c40064102d07074a40c204d22205a201d800758451a12840c0c000780484c011603000300b4007030185407902c40261912905110702e6480c1543d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393924892 1250 393923642 393923653
    0x20c0a0804180b0301111b0a170711190302010c031202040f0503010c0314060415030503030408090a170a020906190b0d0b0607020a1a0403050d02031c020702010906030e07240207050102 81
    0x82101da11b0b421500c0d06404800e4a010009500a2050514110b80c001900c0301c0b042c8180e01c803101010400038031038644500ea4042c20341c2c6110f0708200380c5001c16050483c01c40e07060642800103500400d00c00305014000d0500e240c584006040381d0050340c0c040c1c2c00090403800303410010040ca003024011002a032026090902181084030350258110100400d8544915128019001070010b07400d5200d02a41e001070030b40365249000d0901c0b01455100f205034070700400c3d00300070024030301c210a41e080886811100c00303450100340b26001c1112801014000b66446003030100c50003d080301014482c40240040c01046403140750740100b2204480c00c0d0011300c0e014800410210005030b541940d2102900e0500120f18001e080d801c0801d40f03140038503040140b06208040402e06629000030180241d4080300441d0007441d2200440304090380100030001703020070130450090105030b02a400585180c410f0200b01c03880340765100761807a41e40c400c80050b604c2c0c2d00da07000400d1b2007159040c88400302800e000e000411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393926142 1250 393924892 393924911
    0xc05030d0815040209090f0103020108010e0c040317041706010608070e0f0402032502010e0c041109120c190f0801060e0f060307051012050709050d06020c0a0804180b0301 75
    0x60454500070602203904070b590801c481d05a440340c0c160740f107118014181d641079260100c0074454141c000c0c0803da010484a500008840d118100d40301e00c0356101c0c405050070649076658100d070700000401c902c08060001d200105d030408048841d9860310302030000402d0703594035040c805002d0010161070740c010040001401c040b00d031542442d51048410690300181e90740d4814a680404d003440322054100041894292102c031a815040418520100d0301a134a1003e440c00c2080225445003002c0c5103445800e105003c1c0c64981800d050004000c040d040e10b010640020000d220904501810800b6070001300090001c0b0103815200303409411050001c11403e8203128000c1310112008101030038086440e00003a103581c41c240b00c10704c000c010103403400044c040300400242c810843d4401c5400118034002c009500c044c031800c0d110040340c5024090034004080743d100d4001a5005a11005e079a2040000701800158504028030003084602992081e03d05035000000545583c10740b070b00d1080c0e062074540e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393927392 1250 393926142 393926147
    0x1a04060e0309060f2101080a1a1603051315060905011202010206130813090207060e010603021e04060e09010b0312120c03091932030301090e030f03040f0c05030d 71
    0x1c1d00150084d0030956194030303198268120442c0c403080030b5440c8072111000040d0740b030310002e0040403140c03192081d440b6040003c0c1d0085d41541c01251213031350032040c114a00c1c0720785029a106a420113103205030b80000c01050785a54050038801415038864560780c030020003c081c40c030320840b405815101046140054683c00003991414007501121502c41045410420400040f045901480422804900c816607405a00000f0b40011b1400e48420b404c05c50202a814410706c545c8055036402800b03c000550740c00202546c44034a81c0c4e105401655418000c118600c070700b0050f500c1041071400114a014070700040c14200300c015120751008540034071030001a0f818480355a58017800c0300800c1034495803a810a1854415100984075120900788446402d000c84030605450341d04005c0035055481c000390000030140340c5005034000041d0000d200511001d81c0c10380045103510031040072203040c6600c00d400242d0300c0d442a2000c8400300e5114ac205401c02c800050610700802c0e049014209804414102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393928642 1250 393927392 393927397
    0x1703150f090703110409060308030709060e0d141e01241503050406180c09050115020307060203060f18061509100e0a090c0e040b030a0807060c0c1a04060e030906 71
    0xc60b0309240d120709486a001c4028404c1d2070082100d01002d03c4099568102104154401e03900040020300a1401046050207800340000005015020b0100100292a152913602e4803252143d0540559101c01088200c0d40012041c034000c05000029411100c80c0b0286001000c0b100c14081100b00020401000310074110034550419103041c04240b503517451505000410440c003400300420007105024050190040c2d14009a4040102c10002a40c0b03450701d01e1500b814059003500140c0c0108400c1c4000b03040c41e006190850005840b6079090428503001038283e103800b00100a40e081c0d070104100852134410240d002d0307940c0030a07402d441c0045480104141c861611111401c0c4007100c03032401c0981d125208150010041da46003006550b48000c07005211040e01b28002f40306606001104145240c0810300c5414954806019460a5201c0d0b4031900034002d542040024401d54181c2c9071f020071190000e0404015040c156610289858a020f408440001c48401c9080c0d01c00c2c00510142c0d02c44a04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393929892 1250 393928642 393928651
    0x6060a030f05070f1e290904020706060b030702010b0a12020907090e13060608060906241011160302060d1d010e1c050a050403020d0201020a1703150f09 67
    0x49070344031001241011031500d80b080d0f00011840741c5200d0300040030142c550b4002208100e02142c02140d81c1c0e120060304d0200c02c1c050320f686403c25901c0e14480c90860020080034800c0c00980094180030607516600200c44042d8400d01d120030000040050555080c0300707008010034100c80c210030740c6040c40340c1e11141c00c42c00200280a030200101040d0752130700486454004044902090301c0314504844194404068454100e901d5405c180c40802e820030f0218040b44607036610f1001300f10030b5a4419000d8401800b0740c8080700840040d417514503598943d80c0c0c00300c2e15010243c4403c010f014054084620340780c0a1142c1020000c00003e003440181c0d00d44007121141101507202054103061003440e001d030f6800d03030007c60304190310f40324040303610803c0895654205c168814020390145200c20081e9070b98445d40201c0800240d00700000e00052030f2840700b201c4c000f130041c0f04032000c1017119551140b210b070015000402c84840442003004140c1080144010315400380c404030000603200003c01e400040260 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393931142 1250 393929892 393929903
    0x509070504020d090b0426030c0a0503181603210f03020a030b030601030b0717010e06060f0705030d15060e090a090f020d030c060606030902060d0e0c040e100506010206060a03 77
    0x15803240c01003d0303800900500350402d49016441c00c080c0b4001c1c0c4449084030110500060804050140310340c1002a2440b80c001c032003a40b4903041800354111810351005003008035000722005a5642c5c02001c111180f00103410750300500095082d0b080051411814803860040c1800304000783c1700a55225281010300152030501584039928884c09034080c100001203a03800d44907400c00001844802c2a005000e10483d440708010000d20030202d80103031200340a06940443c0102c04614241000f01c0286141861520190309180c802d0b0f540c42d0856200e1280720780c4054480e00010b03094926021060001c140904040d00780100c03403000314078902c40040c1110865a5100081400e01038904240101154020005100380101b4603010700701c5440000103030fa00340e180c140b010648500074822079500903001084a41803044082d80d25008d0a200700490585009003440340c4400c0e2541d024441304010460040d207468080744841c002190001403049045511100a0000c6a11150250402d803a04103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393932392 1250 393931142 393931147
    0x405010306051518400504050d1101110a0e1203040807030b09100e1c0801030309050409030908101410050d120530090d0818070b0d090203060a050907050402 69
    0x2900041150354000f000c9040e0700170f0151810b4802008186601c2c8154146200c0800240e01404180456008440051499000901c40c00c42c041c080c003c200304050031140080b410210244c0c100391982c10080390a000300e81e03c0446d07481d9a20703001691401e90307000c400c011420076181a01013035403103140d403001905608000010078410714042c41aa0801c001e1500148035200c1100300242d500e1606102a0340404581c051903000d1501ca50f80710380c101c0f07800d07980d1007050318148400c11006109504c8200c0910913000d90001d030450040c040c581480121000c000b8118403403c80d0003580c040014540305040c03a0090701405181d07900c00b59901c805400c075800800c6195010780035541803040429040d0340c034000440102c50f0510f03d02003000341004103007806400340c4070400310b107a4440700e1141c06404640c0200000301c0c0003d8000107591414000c42c00c0701c41d01551a0107010300350f4401203018003280e0f1201c00400030b50030b003086940d0300f020040204119500d46016003035101d2419014861080c0d800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393933642 1250 393932392 393932437
    0x210a0e0d030f0e0304080a1a090a110609090711010609140106050c0727060902070317070e49030e0409080c0114091f050c070f0804050103060515 64
    0x5940f00c80701c03200105003141e40d40c1392900c920ba44d0b500107240c41142c1040c402038076175815402d10024240500094401015080c10940e940c0b940245103141c11500800c0500c03c409c5566174001c6411700079400c076154062401e82d407691903401e4400940010311003a0030100c0016a0070400e1401604480c524984145c49881740000142000c0c05640454401082c810350007880c10071840f90001140c40040c0300b0800103507211200c90a0380112031000d004104d0f9030760a2a29401e07022800c07540010103140144c1051451400242010090803460150761000d2041008540c02d555084d174421110240d21102c0354031180c0341e2034001c0c03046000181000003580101c5299140da4114044683d0b100002c0c075241c800119086000300348641c0d0503010100d40002052481402040d04501e50711114440d944094039204014084c00c000f4101c000031610802403840070480705441561040e04c24042e450355545803800040070707902d19810062040300300828101c80c01506108a07076130407285d0020004803060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393934892 1250 393933642 393933671
    0x1a07051507140409380409020f150c100519020a12060b0a0f0504060c0f1401230f131e0203010e03131a092103210a0e0d03 54
    0xc00d8000310109101090102e114007050f0081c2082c005441c00e10009080c51740e580c0f50018075450701142d400844c0385d40d84d035000d00301504020300c02170000d0549490f64500ea004520300a1610600203544400031030000c440c07500a003c1c01781c2082c00c1003002c0c13015042a5001c0d003010300d0002d51107560b0701e50000b001e007410343c0200c0c4a000e00b5515001c080014561b10124103009074402954000003c03040d100c40c1000030f0050050310259a0150b4a4403091403007a581c072070050504603001c0c1ca0002840b034106040c60b00034010741c10175a80e0035003520140c0324030035010360f58a040a4404664403008001304504c1c42203d0b25100741803034000c40540340f86801007417444040e602c894406505542070410380030305441d0010040c00c07000341c0c055201d03040c030b55601c00207000ca103401c190040d501d80e82004240d000f0b1074400700207500645d01c23084802c0e0001c44440310b5451640b02c0300e4a0384003001d0503000220b040c04c001410303c0d07004918076018884081c003003000d20740341e040c5107600c4000e041da2002c2d00d980d80c54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393936142 1250 393934892 393934907
    0x15070c120f061401030501050a05070203030610112410050f06070f1205040f0b0403150b1305010806040b06030607090303030e0705040501090e07060f080703090614101a07051507 78
    0x2c0c0c020504120120b40c141038003030b1584090005888940c00d0001041814009208080c0b040d1160b80c00703141152212401c203d07100d15440388500030415035004040c0040700c148020b44200044014203190006884850600383c1d000030400e040040c26600104030b03540301e94000310030100d0704903200c5654140501d001c07603011340f0028028201d01007281041d090720f60808001c0050300c150803480f40001c1d40e5410000860322841c00001c03c0451f0080e0a0701504000c2c0e002400c460000809000c64440c2d4050140e0840d5005d038031580480e40880709010612585a00840d0003a078180e002e0719644c82e0804015280750542c0c4402400c040d607840c4050174001c01489840d002c2d0070010802d01240d40e542d8a480c028020301c003215899070096010015a80d03026003034508101c0d1803078640b44501d40d2541c4041d4010f008440c1d040d6602a10740742410401c1005100c04c0f403050501f544107200b01e0307050540610310650441c40843d01c0140800290010600000340c0e2201d00080b07041c1c030703680740e40d0705c89007120403d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393937392 1250 393936142 393936173
    0x10813080304060c0810030809060304031103070c050f040209210102040b07050601050405180a03030513060606050d0b0909030414030c030a030206043309170307050915070c12 77
    0x2040032050204001c1a504510700040c0c2940e2517003815112001d0800c900c0001c0d220041c041c400402404a40d4203002018650090090500c060702c1540c0070003460039680404001c8400c50200433080c040380c9800c0c00700300c000c204266821401c00400002040c901c070b414030006001514141e0800500d103400b50125800b0741606840780d501c460f0385241450317807600300b0700403a03103d1820500000e655100d0f5002d0401201c006a00800071600070792800d030000c2402a0011004640020360203000c03461a0180c0070040c040c03941c07040c0c0d59051240904003117440c3d29224600c242542018401c4c514000020703034081c2d841c0d0010140301c00320040000392612004119694050003a20b244038181030700465001e02c2240100000401900c00781d01c03240c0c5901034014502c0c51a0b102c1d00e010004081a0b40c003142400f032007022440301071406800c0704c10312034204950050000b800040c060541d402c10178a490052003013210500d01380b1b01681e440c90304400043c000ca4600c1c8a00112040901c8103001c6501d010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393938642 1250 393937392 393937403
    0x50114090d17091309021008150a060804031b0203070513060f150f0c0b070f271806051f1b111c0b070e060409050a050106020118030c02010813 63
    0x2c40c80340c2401d25601c0c0c00c5009090311508280303e954003050064050030142990042510640103095401500c1c2240083c10840e15100078201020342515003401c0c000c054156610f0f01402e1385040d107002400d049158060032203000c0c0802041005840005240c0c0954000715416218008550448402010300e07034080c1c117080198000002d10744a10185c00440c80c1c0380c075515040d0b58800705c0b109459040b0714540061a91034001f00068803103102c0c507554a4101860300e400700355649001403411181404001003100914000030800803450001d48581140303041c000d02b48441490300c03001403170b10210a405480d09403035480705004540d108000091300300d1040da140d00380080003030a280e602124140b11440c020074035039044400c00c40411604411003503021113103207100ea0b60140e0482e1001074800c03a003074004406200201c0e844501d409130b20710030215260006810341c54140003e007582d038088440c18940290041480101e54400c03400034030a80c0a00b8160b1160f01d80000c10f1042e01141d1102412 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393939892 1250 393938642 393938663
    0xe09090c0607110a0b0a09031b05060a2d0914030309100507050c06040b0702040e19031805010f050406141216082d090c04060314010c09050114090d 65
    0x80180f0080b00c0c0150750f00556040600903240c500f000102e215154403000402e80000e4208001282c080d81c5101d03030451760301c2080489a840c1e001c11641e810608032034010078023800761031100700c1e02c0d4401c41901100d0300c1c1c15914136009603100a0b1804503603006402c400c11160602090f517403410005c54200c4c2001806455409100e0680209250443c010458060080c01071014a502c2e250054506560490400364900440c9a0801008103003e03406041180100f0703101070500c044400c00503c102c0d0081e281c0e554180e212603c0d000000d40300341c2050307041c0288105828801507012040e6000e442c20780c240501604c4441c140350b5868000c81044402c140a2602008680d5030032041e2440d003200745894201c000d850700c01072440c42c500e42c21100305150030480502020103040c4128150082000815900f1008006c0041801d4600c01e410541d6050254900e01400e40c000b4412001d00e10b040d0300e4880049418140002c019802c0c2606c01c5d070031214085071104840e0b9800840c1319407290701c960000e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393941142 1250 393939892 393939907
    0x507140c0115060c0b01090207030f08060a0506160213111207020a05060406020406030c020c100507020111030c0705030d030506153007030b0108041104051009020309030909070f0e09090c06 83
    0x1c101310209801110a080204000200c89001c0c0c0283c2e0000c03985502d64000814103582c0403641040d004000d1030f405003540300c0c0021252036281c0189a110303400c46030980c2c4c0d40520b005101e00c03002c032841c40d820342c54038050050414034011401d498411440996814254450360401c918050308014050900d000b90028001002050340c02002160b0042c0c501307101100c01c11805a80300c6042c140440c1c0c100c04418a0b0240c1644642e0060585d280305043c00c19a590911400c031346540c014005076480e95014000070b01c40c0349810040702d0140c2c003081c03500707000c6072030900c0104101c00a80040c42c102c0c01d0b00810010308043c0c19648180c01d252400306d5603c00000445007610402a080d21161b000c01c1c0b90416401e400c0d486240301c644555001408401b1141d03000d02400000d01c802405813581420036040801c6110b4940015405402c0c19070080d5101c81031a4200040c1d1480640041c05114000b6600110103030068000c2d103c40008a90b40030499941420301e605100700204280d41c800000548903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393942392 1250 393941142 393941147
    0x1104170102190c0c090b0301020c0318151303150b04050f0609010b071a10050312090a09061401080a060924170604080c0a020d061e0507140c011506 65
    0x1c003800c81d003400540c51080c2c0002c5059a1200c03207444041c0110b40000c0050240318600e810030180903002800040c9000c0c907c070200e50540d0411b200030b10f20313544142003101d41890310390000c0301005029001c0900d001a0030101050701c803c544002000c01e221641c9110050500340e000317400102e0b010b00103000710b141440c2d9039088170804860181c45080441c002060009054090321030007540424a0807402404690444070340c10b0050440c030780c100e40040c010a2948041c080d0442020400103002e489012580412a1030201504250302d000e01c0d0800400c11b09110f94014400c00c0c00030b00341580ca44d140c00c000341000c1d00312900903054840c00d001c014450161030b603040349070f5020416200101591140108185480b52a4400b4060b5100300045404182c42031700401341c0380c0c8071a080360b03a101c0321035020075081e22028900307031903840c0d95070901061051041c1d00384584135111601000035180010703000e0320201d511036200d904d00e4000b007071a0743c2030301e003d40c031420061013051a01c0c1d03003550f0b540070700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393943642 1250 393942392 393942397
    0x605060303120c07020a140307061103090a1e05030a020105030c070c09020c0c031c021528020706180c060e06040506031303020708120904050c19021b0a14041104170102 74
    0x89024503031034840014040401c0701d01c61f050000041c09410394501e0010200c40e055103900c0561807a01041181d0720080e514440307420000c001c54014640d4003040c0010455003010180c0c8828065041240c803d80140e034480210b0342e0140b0f00940c0240c45c3c14443c184041c68941c20f80010880d5440002d11898074000018814840b0100310101c0c0c41c00c5400d1402c065154168180c007a025900440f09144840b202d0b204003580294402d180c41c5a09040780c020114401810649032841c5a0000340002404950701074003044840580045103070702110303034502d40031810900c9140304106011014124580d14081110010903005000c01c0e02d9003004030549a1501c0c01e1a000c03405445840c200007010040031801048125005103a81d08000005d42480068100104441071401c820041056940c500c0d40a1100b090310036402420b0f940c109a56101007501802007a51046020304410890544c140343c1069016a05032000b00341e440041410f038036a8010741e0856040743c01200f11444440c01c05501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393944892 1250 393943642 393943657
    0x3010e010501150c050330070c0c1509090509010b03010e011d070b030103030c0f140d020d1803081e0403110306061c0b100b0418050105040b010c0605060303120c 71
    0x11500042c00f10003000e58000c441d4000c0100181c205101d5418001c8590f903000590301c00c9078012940d8201c54020780b6403415412141140440d40380309100d01800070302c51141c00500b0b001803450545181d000380c0601100418072900c00030548800010b4100c81c800c0d007103500100701c0078000313000000d0081c4607280641101c8489218003076400c1c2c040b214036040040c544045a8061821601d142d095880c21145e010404105917448280c10500900180d1000100d824030244100a40101201c4100007400c228003181c10070104040e80c800c0c0348c242c03200d20041d41c088035840300c1c40d55564007122201e402e503500e040a5109032280c0107c0e001042c4030003400017401200044050381d11540d114400c200010740101c86503010500c01100080003e0900d5900d190010b156095414045684844201c02944180c020a190301c00800186c100791500307000302c0c1e024020845082c0006040100001c02d180311608014204a4803080801d010352018411500300030019010b0040da8a09007160041e00d030700030007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393946142 1250 393944892 393944909
    0x613060f051e061204020105071403030604050c030108280506090601080d0810030201080604090501020a02160e09030313110a03030306030519031b060227030613120f030b03010e010501 81
    0x60304150542c0c0070440c500303803060014181410450304407141c000703108005100302c0c1400405c100b0711001c510098170201e075030403120000316501d1030030409001c140c80c8050b00281e44400c0600040c03101c07210101c0c0a801c0080824241044900040421240050603038800703042406004284464071901141c2541600d140c141200d040f038101d144100c50100c400c841c0d864180041c18000d000561281e00e074160010fa00410202c0c00d4821519010f08a07070280c8803501c0580c1c0200300f11240344890720380401c01015194840000d529062170354980b2071000900c3c10306d01100a42140302006114400b408030550094140e64182c1e840303241c09401072609010039281441402600d8403071120303a10403d40c00d281e15075212011030408000410041c04040c9045511a800b44208030013002c610801841c1000176000d140c40a4200350141420100302500d10b11615204e2140840440e0110a001c0c2d0801c0407403a0540d034240780108c08078020f00b858048240d1550910500c0c0b140048150401410786010a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393947392 1250 393946142 393946159
    0x190801030218090c0409061b020303070e030a020901050409080d090503030f0c091f0516110405160e01054501030605010e0f03070506130303080703090f0b0613060f05 73
    0x5148a2891078100c882c10706960000c2c52001302c80c181600300303842e0310707102c0c7c40041691503a20006103a0828120ba8060050b0300100030860344a81c095240c0e2640f0809034090714a113030498001c58454030050203000c5c0226115400d1004024200b400c03202041c0804504000c40129490b04c561658801d940c1c0780b110360081008144428040011a58241c500030310301c1d085000b0000310140316042c82e20759181403000038440440518844940c00c40c0d40e0f88546c25081110703805038100411514042c0848010f400309112680c0580d41003003a090340300e0424206142c80d600c0654500c50b030104a01e145440c06240780000000c0390742c00b0041c441c84410802418081c100380c00300110211091442003a002466415104071182482046030304c0c1d4000140c1640e004a484002103030103a40400d503140150380c021071003081410392058410303402000f646070901c0074000b03e031201030b1040c6225401800ca1100000400c109603030f900d21081c101701d5001ca0511040c2d40d0362038266014200340c4a03890195441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393948642 1250 393947392 393947419
    0x7050316051219020f0c0715021609021e12160305060a030f230f01060e061807030e010e070501020c0a1a0d0e0a0f110415060e03031908010302 63
    0x70401da44080d642801100e00a5079180980158500740481c0c8080199080081020158420009000036000c2800810301d0600c1d001060094a138040b800804541210601c514030000c0c601c1a034044800218000d43c8684400304d07003000202102800d0b428654001503140300c524030161070300d4440c004070407511100d54540e00e4283c0903107070125179a96200030303110814400541c1c200402c0017a21b004403490b02078907030141c01c12000c0e8011000401d206034042c522180415100b4042c403000344c032108a40750228105040070911001040000796400091380c40050040791180d80b0016665003030308002c2c80b1052903508000c0e2590070a0017450300500591140c9841ca080000110007280e8031070040c1c0c01d041070340081d90b4031150098620300e903241d0707203a00001175200d408001c00300a0b0307805034035540d02450300d9182511508003001d8205006a043c10307803d40c00f000c41d23580094215405406e0031100048401d00090840c8071b02d55441200b4041d47d48180d0307a642c0c2c040c04082c1070b01d00c00da40d078904c424003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393949892 1250 393948642 393948647
    0x1806051501080106050c0304080a03050301050a06030b03030904020c030903010507110c2704020d0b0406020a09170c060903011401030605160810090b12030304120e040606050d090f080307050316 85
    0x1400c440355030116882c00e00400041e4450001007260003400c80030b490506031a07200e0241488d84030141500000c4003c40184003c0c50034909080c0102000d0404028404003400071035260f004050015200700c2e80807442501c11030040c8100c546003540240200070f03902c0c0916000d400e60248024400035031240d42030b8081a800d0600440490342809041008104008418410503020040c822a04402080240c10011748510003241c0501d02c181d0003d0703110403941c007008100384140c0c0d1105900350b0381c3e01d44a10341e0860225620b4a100c81c19108503940b843c1c9000440e0250034051000d03a594861000000103000080d1b02003809844103c5040f02110034071081140d1000c000d0b10000708090f03d5480800c0721140c20303440003080d5480a40121450b103201d0090b2411078000311402ea41c1850703140d806038641c96002c100411a40800c0f40e082080b6400c201c80200ba90144940c1980f080c0c0d44c03410050280118114036908840d440500a0707600e00d010307840100180c10564000741881c94010b00c00916a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393951142 1250 393949892 393949921
    0x150621030e060909190608070303030c020105070801060e0d060204051e030d05070209010b0c010902041e050906010b040b130b130e01090501140d140609010c0e040c08060108041104180605 82
    0x203c0c02420882a070302c0c1d80301a0048070f0101030064590b20390320600021450418080c0500a500030b0300c0c001129048131b0380103400e40c0c000500480401840302d006019a581042c40d159008000303440f080142983d41c50f00b00024881c0d5000994049150040786200d000340c842c01c049000340540641c2e6418511040c1a0380780c0c0901e08009501c1201ca0703006106c2040c0c40d0006d8000d0303280100002c5055111074001c14100d9900c0300700b50803041c01000310070ba80f82040380219904821028001c212a61502c82000340b01e0007103005d08040540c000030016501034504900b10041d2160450720f6070340d0710200003134816a000f0f5124500100558100010f480144d5218a50484948482c5260b940c10120b08211520340c0b032134000c80301070043c40010115203000308821032040c0c0d825000000e90f0030041c0700140c00610920301d5940b080703081003807400040340c1c400509a00801e080c200700b116a00c5510305180d40d090010781d0ba41e080340c9030981d660700840c6002e42800030385014180c10090f5440300b00c400207806 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393952392 1250 393951142 393951157
    0xa0e03011e24060c060f050c040302040b0a05031f060b030c04150302160f022e0e121005061c06270c060503060a0315020c01050c03070c150621030e06 66
    0x90000c1d600c00c00165000f40c0b04e04074501e01ca40c1c1e0000740040b26940308802c41c1c4081e511440c1e6081c0104040c070460800c2e120700c3e69411800c5074240b04803464540041d540b094000c2900f03085019054242e15920001d030030180c0500260740c3e0407512480c2114000005400078421407243c15189031000c0b01c458040d1080340d840702c8003104030002e0b285841d150440079003807040b030803600940d4080d00e2a843c0070309005408004183e859546441032409040100b44112a85900b4070841d030140440791801c0c80000c2e8000f44038404440807a442d96000c001840c007015000b005082032140005040801009512415656400624200c0c1a0455402d41850780139503500c006e000d4941d8043c24071209020780c0180d64072410042c0a181095240d0f0740701030907149100c1e00842c003146c0105002c8100c800c01c0c010f099000c0d25070b0b403e09003545085940101208090306001d0911151200741c600f80d100d41b80c003c1d0b000390403540300301204000085900300c10300300030741c2098000604034050307900329141000450b031340e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393953642 1250 393952392 393952451
    0x3082d030921070303020f19020708060106030c0c170f0a0201270f110a120506040c12020604060809010f020c0606030f03040803180a120f140a02150a0e03011e 70
    0xe00f603603954181d000750f10048002ca513403541404a6072a1078010010700081040c154043c184107458098914582036040c1c01c9070040c1818008040c1d049580700b88140d4155400801c9076243d003200310741c410424454980c000f000f00340000b078040c580c0d58054108000c90340940c150108000a8030090040d02003c010004107076002103910780001c42c43d6400c450584000c01000702400c140c0c0c9031048030300c0c0c103c0301f002254076810000412007442005c1c1c50000050184003c050781403040359000903c0c3e44a030f07001d600184000d14010400c040425030013240c049407801d00c00c640d98010f0064096694000700c1e200e5201e4403071081c0c4440c0e40d41021042d10704036046400118182240305c00030141c1c1c07440c071020050704080230403400120348241d070901c0c040d082c0c01144100040f840c28102803d4030190f03e41c11a5007580812010001600c0781110715015410f000c800c5600d070b84080c001141d014032040c2155078150b0a044155142112201000d5403800c1a101d0400500710b440d500d0200216504590048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393954892 1250 393953642 393953647
    0x90c05030c0a020f0601180b040905030a08090304050901090e010f0c050904110d0504030905152712010906021b01091e0f0614040309090203090703082d030921 70
    0x300340d08070344082c0091150718010340314001c42c802e054a15100c0c007640140303070780e001c002c10000707191a1612a0418254094409100303031407641e20344d80c0d5244141c15013542003020720000a85c0500080c401d80d40035010081c0000b41c3c03035a40c0e081c80b034041c00342c0040c119031652900360b1448500503148200c4001111507242c003801e0400810412005200c0d800961042080c200b0401018034420704c80e681c17080c2e100c0d842d078404803410702051203030010b00c0c02007440c0c4810041081000d1902400c02d43d0803041c40d4410700d0ba89928511012480344040410001804e60034176114004001e10b64015240c50988005005516403203c07404600b40c6220b500050644031005038081d0071322128103280700302140103001c900c499801640e02c440031100c400c1d03800301007030700340105200800d0f0344205d00300000e20940341e0550540c01d00c9001e81f0b0f00c0741c61500c0010130404000550079202d0701821f0f12906020200c0c80011180d40f41600b00b51001c1d03100b00e6191005002e62116070040c8200800e02d40345404413030307030320a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393956142 1250 393954892 393954901
    0x1926070201080c1b0f1b0303040335212206020a1107030c050f0405010e1303020f01020c011e0e0a060b03010b220c03021e1c11070507090c0503 63
    0xf903d076480345400d00d0041034480c109061103c42008042004454100200100b01d100e940684030404188551071090b00200010008074040350200000c1001088000005a50f40702c19010742c0402240c0c8003001c1140461610750002002d90f007681120441d00c03114485a031100d42d105c061039050803182e4001e612500c2d40c034012030910303805040d404416041000180c405c0d54889450700c0c50a9204039000c000049003400181050700504940314000d80d418041d030b50414013507180c1c20000070099006c3c40c2c1041c454006040c400c01000602194900085542e074280320a0302d400391407499035070030316507001c1c88032000b2007800c500c66000d401c0c641c00040d0190446a942d47c10141020b4903040b90f040d0b40b1010840c015990350004684409050712803260003052004131300041e00d586030251400e151041c06450190400041482041e090b1040c049607100341300b43ca00302c9202944e500b03000c0014035183d402d01e11240f51500410899000b0000c0395075403903030303028000240d0354001d1070440012820301c04107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393957392 1250 393956142 393956161
    0xd0215130605150a0807030638150a09050406050a03030905100c150504021206071b020612010905100e0601020c010c020d152f0304080309192607020108 67
    0x11900400f607120b481d0302440341c58000445605480c0c011102c642c019003010020440244106c4460105262000b80303100796488051503200d45003441c1000d54503c14403d44040d580f14602180c00010926045840d0940f00c03034000c0001095010362400369107000c1d0701088074680880540c040f41d9040d6602c01083d1308220031301540d86041280e06040c0400102090300041c0002d10140f2052100d40d000034287c0750031300420001c8200c0f00040303400341d0050010f00049541c018800c400803002a03640f04059001880132941510a00041e00d0a0420b030701d002042440c055008207010709103640c07070420381c80c0c1c0722200380d032842005507007003405a40841c48481540d401052003464040c0000e2445600d9241c0f5145c3c401c01d4242c2ca03600c840c0705650751012102071454107480f0340058820081560307241522100d180070521000c1c2014214100100000b02080710400c8011801080b9074090303c001c03121884d1007620100103410707181070f01300c04038141103805001009895550360140d407083c6098581c001d94 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393958642 1250 393957392 393957401
    0x14270d0e0a091811090f0f06120f01060602060f10050904020f100c15090c030b0a0209031605010f0807020606120c1005090f06091005090a0510020d02151306 69
    0x941180c0c8012001401c4102c512800004aa012800301d0380b11400c0e20344001c4003482c42c00070307620496403a003e016441500401ca10351003010b0b65100c034065180c18001412104400c0848006840350b000f00015070001900031504580041c1c08646a58450802c82d00c80070ba0111400180ca1094000030490340c540724612030b40250000d00310140d1070307000e840400e405103011003031030000c0b03650503134000100a6040b000c02c4e58a003d00c0c4040001d0788480d540c5c24140000b520005c0c12062840001c205c80701c1d480d504980d00240028100c8155020300201096002c1c90351183d0340c00b0400c02c41311640391501451581e032007140319070702604c2c4540d104800c1081c0c0031001009402d25100303078840524075843d41c90800b24000f100d23172915622100d05008009107043c0c403010040c001c000522409200e601d86d02560445070096041880d110047c1c00007088101030264042a40011000da00d000019008907541d840450694242c40c0700c0c0b0060554481c40000a90340486240902001d850100e01250720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393959892 1250 393958642 393958667
    0xd0f09020303032e080618010c020a111302190e090403082703130f050a0602030a12020d0623041a0409030512090d0801061701171014270d 61
    0xb600c1840c0c00b24051001d00f130301a41004c0320641c050300030300001c01408106050010b08000091001500400d4000c0d110030303072404024524200b401c0074581d0703980c88503820480380d120f40d601191203412150b64401ca180bc80461880400c0c074443c0c13488924146400c0161240d5059120392107541c50314501d031003a2003d400024a00c11490044203801823105000409400708085964042d141c10840108500c00c680d134001403003080c1c07049081041c2d64022081d90a6001c85e406d040002001030100c00019220b0f0301c0d02c0007031043c80c0503004681c4d0b08840040d19401802c2050010340c890360316007800100c550f604403d15030452101c452101d2458660055081c0c03a2007813400074140031540d114541240e030705031012441c2d908001e0242c0d103560b50240781903006120604d42031849091035800017030900710600643c0c9203103c10902c1101e885000f04100415440503040400c91b806656800700049441174510b02956030078481c1501800d50b40203a9154540e5640014091020b1994015507200b0082c0e80b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393961142 1250 393959892 393959941
    0xf08090d05010e010608070f150503060a0e0a060303030e0102160204112503020f070b0a0e01170a05010f05010f0212090a03050a05101503030f030903050d110d0f0902030303 76
    0x88918000070420b00032224403805180001c284581001d11803410f003103403a003024511000d4100208911501503c0301e0400e03d0307040c1000c1e0341d179403692800b041008115030889030f440c00c4060140407a21540758050340c110b901036a01045440c80e011201402d074420400c002411000f500f0501c009440c25034440e44c11103d0320b02c06a481c00c0c2c0c000104501c800c004944646660320300c0b8920009241e010722152828090230b82c00380c543c0d141044440c034118082c0000c0001000290310207010681d000c1c0855030f0352206c019982d010389191020030f14020b040240076100705000c4d40300000440d94040c00da10040101c43d50040d0000e040d41010185060300280c0b15036074082e561507000404100d050005803c0a8041c4001d001124604010b1405560048000e9980050b801e6001c00229500544883c11003100385004144220241003c448501400b402d8518140c40c01001040d499184d40003480000c00700b640038066403560035500310494006140217034168100300700140098099194040440c041070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393962392 1250 393961142 393961159
    0x908090120010906052e03030c0203070e0c090310060803180301140f0f091207080a1e0e01030b090c0f03090f03030a050106020f0601051e0105070615030b130f0809 72
    0x103144582500c114840035241c5550b100b05000c21010300c00720524406c1b82c20ba44404400020004010000d80c1910000c0d040081250310b0004544d01400500000c0055610415075420711600e8030403030303030f02c140c101501c40c0c412003074200e03034400d214041c07103080302c00b1030016505025174030324500e000788a0b0040c11076140d540c51000205202c004115280141801da640c0b040f2362400c08280183d4080207460048651300554038801582210b00885040d258000d0b5242c2e103901c4100c5042d9060b80c144000903040b03131484140030304403a5000b004442001400d90701070000106910130f00461a0080e114040b51080c01c11034040514844401142c000151400b201c0208500d100c280e429500141c80da03003030345500c4200401040b0f504001809070310b5500e01c05410a03500d0000002c03d10b49110040304a6010b60003508150750380034100b0b440c0015041101440081400040c40d45000612b0104540c0c0602d0b071307000705c1d40f0801c030b0b00d554803a1140c1c003d2040d003514004d511070301140d030061440b90394046800c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393963642 1250 393962392 393962447
    0xa090806070302030f01120503030103030f12090521030105060f070812010320030d0e1903020d0f170a02120d0f1a15270613062109080901 61
    0x108152445520a503030b0040e103904000840c01424071060380300d440e5541c0c4481d6800c01207000407085031b04503641030030004031203c2c00c00b400740c420510038180401d2540c074140c052030502001182c1440c110100341d814204802035000340707041c40d001c00e0040a400403024084000400c060000418482c0c2c080d40105042001040f00c15400034006d07001218180d1464050100400c081d9009e2103c001044014103040001c1c08030003009803520f000c250b4883c0710800c0845003c5146640785402654000d001081102001d08040703035010041e0070304403191820301c0c800c141074103050300c10b40d580d100f49640905181c642c2011001c540b9001840040d000b143d27951041030f00c4190921941e44480c1d00c400c1c050000c0800701082100000c0244400c1c1d003181000c000880300c110031b0111600b800b000d12100e1040003051040031400c203015080801e10b90a0302101e0202d0425004010000318450310304807c03070b440c401c510b446000d50f0320303804000f08240c00a100c242c80544c0a020300c0d402940c1c0d04441c81c00001d41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393964892 1250 393963642 393963659
    0x5071404020f0c0a021903260f07051509070807150915030c0314010b040b03040c0506030702072108040b030901270507090e030306060c010902030703061a04200a09 72
    0x1c001881c81d140c4c412040c0b42d08604001d540d43e02c08603040c03d07080100718911703240c006800c107000900e0b44211140a9903640d0b40800e02e03055031803041614401c541c4511642c541507035982514030b000c0c0c040c007003c90000707598000d00040c3c400c291074043d0050101e49140040b00003801740d8429039107080c805142c1e400b086084850840b4440d44d1003541e0003040360b40c1c0c21803015040300e24030b0140b02a00c0540ca801032011108000850b011602d00b900c0141c0d907503845003000d8981c03100b10f400041d03010000009206403150700250980c01e1f2902c032490f000461407850108070309040c0400e1f0003840301c3d50510040010a6a80001e1a40700c1325603000032500d403051550141e24030146e0a02079000e40c40da1070540d014002c00300a51009800840d8003000822940300a4030759901000b050540325240c00076150101c45404c0d04401d5109501030112012140c0724a042405056102e08602140c200c80d000c00c000c5113018080c1c0c40b414492403403039040200300c420740f8840341d520002c15101440325240c1b0004d070740903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393966142 1250 393964892 393964897
    0x1127060a09060c110405070c030f1403160302120a020310140904021003090b090102130608090340061b0b0f06150d060e011203050a0503041703040c08010507050705071404020f 77
    0x10b45960b5203e123803004519024283c9000d42d4511710400a286d000042c81d9034070030080b0b9404c11441c0c8548145410300800880c0030344600c0c4214a401c2d100c03003042c89103c04041d0091030040b602030381d16010580e1075030070010814098007402380d4421101c402007805403c0103810313414202070601c0c0105140d10390340c4030006401ca042c1c4d00d03c90241e5000881300f403442006070138a00074015910308081642044090103a49010758041342c1800141d0a054448581113003800340c207041d003900ca03804459a580000c141d80303820144078403400315561840c1404a000b000406003102a4088403810b01d98843c0108210072203c001d04d5650452007030861034074010411805054816030303d1102081d140e08000c004508000d041c0e0140d8103010488124a00290300032046d02c0c1008500e00c0c159480742e46505082507102d03042c0181c00c00c10103001040c4814020480b8181c02920200c0009100c0354071844800c030b9081c07265403c040e11f150000c070014007842c29004913414043c64024809070800800040d0011640d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393967392 1250 393966142 393966151
    0x110f040507021f330f030501020d061418040201031107062702090f060a0f030809031605100302070503190215070819020d1127060a09060c110405 64
    0x1070b4840c82c5010800425050340a1a03c080d0b0b5000348001c200c20001c0b144451040940f940401c1450b011000140101c10302210091906909a0b1400c1d942c904000d4004d611508a4807900382c10203c000c0f9040000c0c078180c0c0b44549016089a094040d4202c1e0448041409001241015140c285001e4142d0804024125150184400103402500500748521260703080241c800c18a441300d81c0c00c00984c0d54500c40513400f20600303554041c03070350b1203200140345181c03550040c81402030103043c04400e001001010300f40903c42901100e140000d18445035070301c1001c0e40300381c66200029032110a072452090f0040c210443c030070b5003141c0c00c041c0d101c500904012259101c04005034401c4e040c031210030180c005515041600341c05c0c2500281040031022480782031a0b40380400c07994001524800e41e9036954004803181100c03038085511400d44400100207a500d46c04d10b02d028101311801c240140c64420111116010302e41c1b12003662a1603c0e205a9803000c070042c054440e0480c0000300031450710344d8080e441c8107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393968642 1250 393967392 393967397
    0x20a15030f050603061512010b030604060504030e030705060d0b150c010c0f051201030b070203070b15040c02010b06180a0b12061201230604060b0f09030715020a110f040507 76
    0x401c1201c1c41101c04503500144102e00c0307a4001c0040c01914451340780141d8030000c040d9552100c03440c0c5048410f0241c030681c6111501071080c4010801404015071200340100d2080d0341d140341070234410081681c1c2c1c0c2c0c054000d07668410b004229000e001102d0b83d2001200d83c1b0054001c90000440c00810101034000c0140c903103113a5100c01d40300c0300342540088a02c015904130b04249044c90b011562a00004505000082412060001040c000c9008000365029030754000c00041162401d144c0307007080303524031625071030049040c0000c4c050414010300031a100c0c640d014045508000c481d03000050b00703040c5583c441e030300141044004284201190b00420521148182181b65800c2c01420f1042c010308070341154105034540000c002c0107040380e02c2c48441081c3c4040c0601c150342c9400c40010010800741e84a50080300d00010142c01e0600c5c00006001c1c00d404c124141c030f501503500c044031400326001500050040e000107041c1400038145944006002101426040050014501150403210192030b102d01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393969892 1250 393968642 393968651
    0x4090204030201090b0708030105060f07050d031406010509090f0a020c030c06040c090b030a0b0403050f0d14010602011b050705030f070534060e0d05150108010c080c0403030c020a1503 81
    0x540d41c0004440e8000d2004815051400d000307500e40f0041f6020600405104d00b50014086c0d0005051200395502540c000040d03039074540c00c1134405070083c11080c1a01002c1c012240000f1160343c000d1040d10983c02014081c0003850f0b407002c2d076454101c28020301e6081955070074045450b0000303003000036000c0c819003200206200d00f042e0404d1528400d055000020769420300c0d01341d4480362804078241000c50760101c0c410a594546240c04e8400b0b01a02110f40c01400f400320f0500030350140c5800100006206d2070442d00d20741d8840340100e083e0b07003100604e00daa00d0201f030514101244140010f0400b280507009486c10610843c8075a5020303441944203883c1544000c5a0710382c1c0d20504006101c0f1f04881c011f0310381c00c10340d14031043c0b00c8103019072040c1002c4c41401c10803d00d55440345030425000036401426540300414030785064540c900c0a0144940340d41c03900d00c04407020303405140c5040c010150040000d0810b45141e83c201c40e100440d001c2241c000c03250f4603000034080c404684407070841c1d055890114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393971142 1250 393969892 393969899
    0x140f03150f0708150a0303030c0311030c04030c121109090a06060b0307030c0e030c0f0d120314090c150f0d29150912030403050615010906030b0102060711011104090204 74
    0x2851010090b050350b071041060139206550340c1e640c140c100c0841c0c2d81070401107200145a0b600b54000c0c225480b0041c2c601c0d03000003c000c000d901c0040144103603407041401c0203071652902d00051030410201c0303000b03002201d218050303c0149081003a42c0e0348480d04504407038142c8000d0360fa4400307442840c1d0119030703500408002d20000c3c5406004041c0c05e03030001e29040e84502e00500000341e4440002c0007041c05105100030046a80d10785049003100a40c000c2191022048007000c024024050743e007080c1400013080d4003144011201160301c0c658a04000c0c10302c540400100c01d8030540ea44034442c59400510100508010b4496601640301c1001c610b2030000021882540c019450500c106d017a11710645010384418841c0c070400066030480f8070241c64002d0540028807070f2078950f1182e504007400d540304d04010825002c2d940b003d007482c02c1000fa40c4002600b0398a17007050381607030554032685000d038004800065845219910940a003100b040001c1010032084012001e0f503403090f003000c40f009030002000d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393972392 1250 393971142 393971147
    0x90602030604061e0e0a0605030a080a030b0d0c050907050c06240d080414030304170304051309051015090908040305060c0306030d030e0703060c030b0a0906140f03150f07 75
    0xc1c40140f00c01025030b00c0c209604000504800c03130302e0044083d54000500031a250051640c003040141101608450002c420382c1414010381d0000106032000a08000c14413865091440c40010f075903074000845c1c03102606103401c00c900318034024004802c1100171710020500ea10308000c403900603455401c945000050326510100e20403a804600c0b8003601140d40d14800185280040701d04442800b202c3c010340d01c2c00c06000070308500c1281e01c40d01448507281702a0144203404002081110340842e520400d0019400840081d81c094241c05003040c1c014034240c3d41302100642100800c3c2114091000f0b4050300c40c2856421980c0000341641d5030540420f00b4010030004202064100080c2525a400c5160150000307655501909050f400c01d0388030203003034004420030007856010790b500c20810700c140354100784014000d000080a15118800240c00050219000d10840302a1840e1450b00011021100300b0305c0710040300091015018070981e83e8440909200d002410700600710040200c0c0c003414a00c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393973642 1250 393972392 393972401
    0x30c080f0705060a18030809030409020f03180a11100c02040e070303080603060906060d05030415051c0509030a0e06040e07020a2a0e041a041401060b0304080f1b01090602030604 78
    0x200200b0310b01d0100c900e890303460419180245c055040c500f0200c00da0700d011700c013400c42c000d031740c00703a61401d00200e180300d000164640950b12924103102401c011000c1e80038017955031003c0780d00c080c140182c21004001c2ca4280b0030f491200903a480c0c10550209809a404681121800f0300490070307907041407400f48205907000d1441030b04031808800411031414440c407001c0d00e03450003911080c460b141e0300754000200031052098400400c111030124800001c0c2d964041c2407640702c2032007961131945810349a040400107114075030142182c0d800450501d034911a09031101c444141d030349a40508280300008006140c101613503c142c9296000c0e110f111458908aa25001c50702d00c0a901c000160b070840c0541103081c00c406049480322054201b15845600784442107551840c1d600c0c2210b00700108120030701c61240240e0405904e07001c020042c103a501c000c07030049400292001410001c00f00101c050758141c03500a0051f001344407124045101e0b908240c5403c5840b01d000807203105d600401040180e280c248207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393974892 1250 393973642 393973651
    0x40b100e1e09151909051603090b070305090106030203060921180603060609031c021b010503010b07020a0f03110f060c03030a1d030a03091401060819030c080f070506 73
    0x4071003001d01680001401c080320041c03244015103150310849450f5070300c01c0c80c0c002000744510f8840c04c400f612060380d403018080407509607641c80307020101a400240701c0d100b281c144940041a950b8240c5460303000701c1c040e12000d440140c2964a511010000d80d6060010502603450301008100a070404044074008204e0880180001d80e4103001d9204580c0d944d0101d44001c200403100e0980d039948a000141c0e6600444190b940c140c4600c104bd040d60b4107469203890106001a000c850300340031000c400300c8031400603000b041d0020b4414030040101880e050040d0a0303903440140075140b429150303110890104001e0344203441410b00e04440e0784440c00e101d0046032083c8410f8030028500b0081c600c540e80d90b480060240c00013a5030b10304108440c1940380c008414a240c1001c00d80780d403802600c4006002e85807481042d144102d5000f000c41c00c80d141442204202c402000281c52070200c2c10203180981040f64505030140034400e00614005a2150002c016485581013400d0300c58143d41000352500c1c400a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393976142 1250 393974892 393974929
    0x9171315030c0f03020904110a110f01020903070b0c07150203130618050d111c1103150708090708070308040611060106050409020a05090d03020c0117040201090303030b040b100e 78
    0x80030061030a82c00441c1c1c210f080b12030700340907a0340d107981c502040040007060150580d00300089921300095500c1003000d03142d0020401200c03100c06110344901c1c200c4c4a036200841e41644011810030028013514042c1158420328000d4400540d0340d0a49600204011903882006030400140400320b801c0c20750070140a48130034901008100059109001080e1150081510402d0040050001c1058014640c606410301400a6082c800c10444200c002200c02104580e4062901c1d0f0b00a19810006843d4040760040112402c854a6511040d2000d800241903110107018103100071417174003010480c140c000e40c440c142195035607281200040c415002104c4a078800d4104a004100a9030720005640075108203110040c3d03202c1142d242134030b07240700f8041000e03004030210480700103054010400c100711a1007a200c154802d02605419044054200c1c0e009006c00c00001040c00402e110b0341c000e041d140c034058000075540090b00000f03480e80c003400090b54000750b00d40396413803418140314204030084101e09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393977392 1250 393976142 393976151
    0xa08010c1202070629040e030304050a0f0201050d051015020105091b01051c060e060d03021b01170405070807080712060c0c0b011217030c0703030917131503 69
    0x403000203201035200701d0441560303070700440c600052020603404003e0704100041c4615a410304c07081036410400800030803034851494a803604e402000080b0840388107940c0080a440c00305e41c00c1e17861851010001b101681001030501c0f03038464081141c459503000f60b9030310b4150200c403032400d40e074440d0f50000d02c0780c49811a41000b050140540000840b000b2602d00060820b844c4019040100c486001300d080c200f580e01c00350881d10130080d845610420554030300c070100458943d40c1000344000c1001c521390040041e441b40b1003109811220701880c1050307040502d403048a5040c0404103203270206056600780c9268010500410041c4002c000c8000208060406407142074a81105191040294100a8070b490340301d64103403210521030020540e015034440c004040c1540c440c840c4080c0c004c05031804440705444114075a0400c00c412065904ca0f440b40c0d2802c42c40d005240c3e40803405000d9041044444088207041c40540e1410076010300300c030402e0422040d5480303180008116912141c0c072085028107250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393978642 1250 393977392 393977411
    0x902040315020702031b190b190302040f0303050d0204030f0506060307050a0627050904031e0509090105040c030f230114011403180a03030504030e0a08030d1e0203010906050a0801 79
    0x402e00002c00c00c140380c88600c1000402d400720311324010a07440040351111036800800c0e0701c213500d0040c141904d82700c0d815030704d08942900194124421406920007000c0c1d81a000c200080c85030006100c0604004805800c1c1581c2c5c2c1e40c0c0c80e000c0307201c10308201c3d000d03045403040080c0c031704080003008028142101c0c20410710380342000c0035000c0c1c0c0485020100625158814560b100030415180f00202000b0300240039915041c10000c00c1d01141d015200007140e84802c2c2400c40510800944080c07107401000489107074640340821004000103500c110601d525021180544003c503c0380803e01d4107140d48a440350007402c4503038034404005030030401e2520110b00c080345240e40c1c003400030604c00140503070701660f03601d50300240d1000303c1d81300036240450720a500601003003560540000303008500c0781c0c4075440000d2000d8100240a140c502944035140e000703016591160046d6001504d1000c00e04044030003440c2200c215109030f9009811900740b40f034071180300704064201107041100822901000b000a00170 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393979892 1250 393978642 393978649
    0x4030201082a090a151701090b01080a0c02100c0306080d02010608030d0905070b030c130503190215220509010e04080a0804020f0409060b03061806060d0c030b010902040315020702 79
    0x342c150088041c00e101150300c408544034440060041c2001036041ca4009100d07003002007410615440307400c804a941c000000c3c11513254015855501d50503104e0b003005560307014030300006200b840c51807411840f0b80c5d1047c0c50b41c10090307c0381060401095070040789207410461000e20b442400c019074030440e0314101040100039000300076580e00c2100e025010813019801d003003040c40c140f030765004105048800030901c030324141c003a8014202c0c0b000b40008110f078165a00e04050719010350000300080c040c1c00c240c8200043c0f82c031740f888040b080c1c8890f0849040c54813aa581101510072410061460200f1841c00d100310306d490316815006100140b403588407464280e4031444140580c6a6203028008008042821541d0b503009038107941c50041c0c0200030002c0141008000b43c402200c2543c06809100081041c1162204a007441822034200030403a40e16102d00744080589004419900b80c075104a000c40000c0f0f495076058001c0410110260700e882c114101200d0b0100d515003030380724040c81008110010384 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393981142 1250 393979892 393979951
    0xf1e020f180f0c0906160606060c0320070909050f010506040612060906111c0e0706021e0102070203010e03131d0103110d02120a030905121c02120406050403020108 72
    0x55224003064031503c0b0000700c45000c1c000e04240c0c82d8440004210700f081011300d002c50b0058503006242c00c1c0b10090b1344c0e9109032141682c1c0c008c0070300061903038408002c0c00032150121040c0c01c2424012215880e03900d101100403103070760103012212a0030180d850702c00b5442c24007581d81c02210444081000c3c0e407074000c4410051100200042807651a1107002c01440501e0380f0040c007251465881d070390781e040b020741f0006600e0a4000c501d1344403460081c11001802c2e00013511419940603030010000150042560074458100242e80d406940d001c01c10200107031000e000300f00c0501c031301800440e2100f840d01024880142d5035042582001c444403004c1c1c142d4174441d0511411640c001d54408503090038400403880890441d0406500300caa0344904010700200099461440c500990340c45596580b06d070100b00e03004200c01c03460a1303560302860b90300c0c00500b04190304100500c10f500440d14460841c14007100e013038009501c1a008504041020002d65070005c0c2c0d126444010140b18160501c41558003d8420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393982392 1250 393981142 393981151
    0x321204060503061e180108160602190f1217010b07020d0303050a200414030c03030d111c0209091f0e06060403080f0d0e061308070f1e020f18 62
    0x180340340c044da000325140790f9000c1d0010f040c0161884042445841100400d0142031050340c0d850711070050490303c040b04105018061350004c0c0d0103000c0c1c426240c22a029500e090f510113545251b02c40c2c40c00340005282406061200c00c00e07407143d050004012401281d02c590590001410701d200b040300c0310050f81c944c1000b074040c41e49402c00080c1c58498900440080a14000d48051140c1307100c0105108005440a002121904041903400380f501905154a51000d6401c441d0507510600070302e840004503800c441c21030310340000740b42c3c10800745c0400750741405003014034200b403283d00042c100ea0b513040c00c0404580c04680c900d641c4040344240c041d220100300f6944540c03082c009028010604a80d2403108480c01150440c490300d4840c40d031801140381d1940011401c4c0405850490304007600341011441d140728103912030340303800c4104407602c4815142c0d1120b0411a17502c0306045441000500e20800d40b240011104119620411079205020291340d10002192048038210110340004040400c0164030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393983642 1250 393982392 393982399
    0x1807030b040f0602250209010b0a17040f0218011a0702060a111c0e03010605010315060c06021b0c01080108070819050f070e0a0513110103020732120406050306 70
    0x90b0059062000c02402150726950690321615182100f80760302900c250159402241d51201e00e907030b184540b00b01ca10861101d98040b65440111002e04a100f4044550182c003844518444415036800560070640060f2501c1070314402000500c92103070340c030750401e000c0044601c2c001d1400b640c80d000038910b0301034850501c0c10481c202042e412490400c0c08400304100c6145600d03c030800081c040030f00f480d80e00203942c501941c40c10000041c550b1190113001380740111030100071b400a040a00441e1100b15080b0160380480e000c005040107020419080d80b01d0f00509009003a200c42010001011614180d00504241e444840d00740015500030420115030003403204d00002d070010500c0e1060400242840945040c001c5503400076058540c000e1040c45a41c2d601410481c55a07030300100104103c40c590058141c40c0112030248455000b0f42c0107104041c05040b030712886120240030000703000c84400c1100400d59401110841d407042c00c11901c030130030035011500e904090801000034140e01004051511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393984892 1250 393983642 393983663
    0x7030908010c033608041d091b0607080f04030b0114090f0105012f0304062c040513050f071e03110609060c0706050a1407030e0f12030706051807030b04 67
    0x80b0760020300844c038560b11924194982d65902d00170340d102da1404a09000d8540c1a0b40040c8500c400130130742c0c110010391441600710422000d130034401250403107a41181d50040400c8455080d0301c224014200840c46400011034660420003100072004050344214014060307042800850716036540d015040d03c10030b10b420b89401106c41501c602040569a0b4080c901c4220020740a803840c1c088028030076104151141e1840300d1018120b07184003591503807a8641e50045100308110351030030340c00064000000715507401003d03140341c45050410200500c00341c03440d8003211003041514a03450030b10140e0034074038030580342c5249143c0b03032900705005170014070f842254006803501c1701d5950007040e2105424032601f22080035403204005489a40130050100c003180444500310f20072451201203503051075041d540c2244091107242401402c070000700c407440d1311911040703407070180e64001c0011f4008180500b0000c1164240709061140302c50204d00c4220f001d4000c41403d20205011181c001d4200d85e0103070314101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393986142 1250 393984892 393984971
    0x3020f0414011a0723010e031303060b060c010e06040209070518060d02070c1502060a1109130608010c030911040c050703080c070209070507210e0d02041107030908010c03 75
    0x212680308004c13009140c00c400d600d001a80500c06440c10341c01a03050780003041504141c1c5000d6a4900076100014800a00c080d01480019100c0c0c010514202010f4280c40c01c044c500c855050a42c1e0800d40410119813040041100791300c0e000140c3e030303008506030410307038a0100865901c118801310170a113a03000700303030000c0c24420b80801c0790304403941150020100001c09840c3d00c445601a9141c0e080540144262030120701800c030948140100e0440d074001c0b07203140900100c00d0151041078509400c01241e554000081e0b400428003609282c1001d940d00001d000c1c0796490628098200c02080c0d9004038a886210303000710f50060101d605454040c10300c1101e669602048041d01d1286d500c3c002c0d0400c0007501442a4070781c0080291140f144100d0500744102000301d4400300708070450701d14100280356644600098140f6610a0700200e001a202041e01040c02c0d440c4106540814012000506100300401c98410300b80724606504800b03140c180880c0c041c010310304000d1750194104071301803001414200d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393987392 1250 393986142 393986189
    0x604060c1709092403150a0c1413050406090b0108071202070f030905180603060112030314010b031b09010215060f09041103070f0312081b0309030403020f041401 71
    0x40b624954001e1000480e49450f520041140c0b00840010b83c0c0010303840e810701c2c62440d011602400c40f02e07440d18030700c80903a135024110000c0c0040101800c180891501ca200c05a1101070060568030341528000840340d190005100444204c0d0707006040c4585000d0030840c09a03800540c8540240c00fa00e00400b080100081c010024840c421005107481d0005080e40201500082100300303d5408441c108500440403210f4250503100700c0342c00da8141c21600c0144601d00111001c01d400714002d180c0082d06603503140700344103032010071b0b04900b014680c080108401c0205c07005907884002c24120001e0b007401c0c071940010356990081641e144031461820005080e90f00d03a6071041d01c40717100040c0640c081e030905041694008001c120014002d018180010403100f0740e05685404813940180008006482408100c818a1004d42440b03c01d058400080100032881c0c0e01070b60040d20803101850341c461461040160092121a0a90146040c030440e100504600f03486141101c0d2030b1900d500000040c107040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393988642 1250 393987392 393987397
    0x901081b01090b040306150b030405120313050106090e0c0604080705090a09050a060c03150819030201020c0d120c110a0f020103020d020f04050a05060405030604060902030106150503070306050604060c17 89
    0x400d080d80d4040303130000c14806a600110358065491515030074040d00e035517503000ca0703102c115000782c8642c0c013003565808207903000303030085d5448400320302c0b40085826255202400e64005502000c6007580703c0c954500c5409041c4a9440300d80d40807564039140c6032902d01c41c0c41c0c5588280c86060f1090f0901d2000810a660380d4018107007495005080c1c1e11000c80d68645131005000c0505001c002a2a065002c441d01502d144020b0a582d92903005001401d040441e402185162050031030465400784000c0e00490401c015000e800c1c14103813030318281e00d004d00e440e080031110840900b1040204090200319009030208804008581003d030b5822038540d00c1c00164040d10803000c40300221880002d50001d030120f20f00140046d0b038800c440d84218256a0b0042000d180901d02400f907040d003040001c600007511039444140700c00e10140012415a5403000c0c1813450038082540300c400b061000040100f070607814460807001e01030803100310f418942860401040a405084010100c410141454101917218400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393989892 1250 393988642 393988649
    0x108160e0a030b0708061c06110c0a03080106111c05070309030b0a1e0603020603070825030519061a1e0403080c2e1812110c0901081b0109 61
    0xc61400d20b549140030502c8420440700c003000101e09401041580c5411400303d82c00d44410440080e510501d034031440001d1074030303a10300700e144501001a06042c007018080a1941802030319544101d40c5804005007402880307025000e0641c20141100b681c0406602444c480c00885203841030b285d214610701550035004540001c1d1030308040310200014610301c1d400000104142d035030b20052201d9451400000c0e6140c80c00300960182082c000103040034810b00c001a0b00c80200c0c032030103050240000c02c48500444003540180000d443d001004490b402400f0744071882c4190840400c0100e14000004080c0312a140030b00c8820324000402c81042207250128086003098450800c2d5110340c0d034076040525900504203c02c10740180100c2200105c2201ea008445480c802405c42030360910b4407041d002001100700940b0016941500b0a000c103490381158644c000107a141c08446d600b503641c4003072401d80006801c40c0700304c4082c00184802a004035a52103520b84c070350a01a45c191680c00142c90310340c803540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393991142 1250 393989892 393989899
    0x30c020f03071502100207080a08071e05030a05010b090d03050a03020903190326160302161115071e06060b130f090902060714010f0e1506030604020108160e 69
    0x2440440c1200c0e00300b40fa280340c00740784c0d022507011850304044c08060380141900640801818040307040100d0103074400d254001e20520300600310924094a44050819038040d050000e4030100170048000760074880c540c0502180c0541c10708105010340000c070041260b04000341001030209035078200c80d000b9010b98041c0780008081ea41498690900a051807030291001c2e40007800851a8060224038100c800f9096840b009052003a03a031521b40700b20129100120342010540d00300300da106021041c885800c0b81900c1240f40e22000b81c550307400c00c03003141d200019404154404001400004a1007100c3d00d0a00b2045440fa00a0301c0e6103081010062025a2111100400004da505034203002e036500c040c256485180c80201e520b071600014000c845c20a1303002500010100801408a0400da62151150160790004110f9003804288070701a612543d4010b0140e50014546000c42c02117105526400b403006c1c0d0042625161540008003031803409002100541d03027030345a002400344a2500511101c4c03015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393992392 1250 393991142 393991153
    0x30904110c0a032627070e070e040609060b09091b0c0307050d02010501050607020409060e0f100b09060f060705010608060f0906070807050f0a051b010605150f0304030c020f03 77
    0x2410060401c5101018025081180f44409070605203592070903401010204501d44942108401c1c54242c29003c0104801a00c51140001200c8001f40c80d818403c8a603540c91300310340e200c0d22007840142d030441e4114449031170404d07100380701c40c0740c004060300d01c03908044601c11120303111948803544400c00c40190103840040001c0d2072081d0744000000340011886a411200c100303d1200c0c0032800c0300e00c00c0c0030b1143d112400f000a0f01c0589480d070064043c0358000d0400041002c281c0c4c1180d890309181070303c6d000144e0043c00150441d04864411000c41c607070142c0c2c00191074500080040e0b000c0d20302403480d602c100f6010881405000e001d600c0b80e00504078520442d011400d000c0d000c903085640445a00c0542d00c11800018084c502c80c0c10094051040f03500c0d00350a29120b510441c04a07040a0320060400805004180b03090a1410a20507090100310000500f41d041c03405100d40001510080c100ca14020440280440c0c06401141d500c2605450b142088800c1c600c0094a0f085249840590610a5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393993642 1250 393992392 393992413
    0x504080a200a0308070908030408100504060b0910060216050d1b030609060510080118030f0e0a0e15060c121608120603010c020a050303150303070b0403020d08010f0503030904110c 79
    0x54a60341c0204819100c140041e0740d1254072907907909c654003914242c0d42101d80d00346800b500390340106801c03034428a00410030100110200d0024a011202e80701c0100b2000340400046405000c0d542c084807480340006160390611010aa01200909008145000c104608038002c0e0000d95028007441e41305409010222081c03c0000c0a454292198104084800c0c400110500148120b000d96034040c5541c2c8020800394405640c00d130100c616903000d0050f0310112150f035a85260341d10b400b1302040c4240707032042c0c10040c1d920005940d2100b04d55005240810000c060300314000f034040f0340c1c2480f64034601d41e80c40c42e2004403500084403a100034090355011034050f0100313a10007922846070380c09800030400c44d402030004a9984d000400041c18680041000c01d484901d44400021494005002c40e440c0c40800e5580d00d139000c41c1103c1c00e0380141c010710701c0e24680d5680803008900600c0714440d40d21004d800c000000707449204d82e100b61b0b40326540c1d85030200c904c0803018041d81d0f400307911003080d44e090203034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393994892 1250 393993642 393993647
    0x31504230601240503040f0f06020d0608032508040909061e02090108060603060f0405060301141608010506190305100512150f0f01030f11131e0504080a200a03 70
    0xf03180c6404480300f412041150226407103002038920454003c901c1441001c0203440740080d400c40070800340c0f80d0503001c205030310310709803a030140320010080d400007184c2d03684019614014608401c5001c0d951901151038810200318000c0c11340e4241c44091f000025030032007600d4410020010090192899503035400d42c60301d8658168023401510320700ba214070303580703503503050400989100840c0c448d41d0040209100000c0c40c106035101c107500400207400080e00009500d07034410201801c95240c4042d031070010750a0a04d039403003104540100020340e241820300110641450b0408e55020080c0105588c41001a2007201c03211204c1c00244005000e240420301d0a080946e2180442c040c410521750003c008143c032440b026001ca481035030091102015a400c5981e1455414203407001075522500488103500aa0364800d290b45106800410010fa660340709030851000d82c10080800c0c0e601481c0c00100400300e0000d008880d0001c1c1c0d185450b40c04c20a07095000c0c40304000704a40040c2d28811007064004254 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393996142 1250 393994892 393994919
    0x602151329070905010503070c0503040902070f1b0e040b070e0d03051b031e03040302101404020a06030b09011401050c0303010b09011107140409030504090e0a03030b031504230601 79
    0x1505031440704007a646628098411510520900780050010400100f20901c100c4070381c1203081c49001503030300e09603541c582d000680e0004541580c1380541c4403000010400c03c3c4030002c071800000840d40200510300000b50105100080c4050203843c681d000040b1000c2c0b095210b002c0703400e0003e068162100036400c00070819000030310341310030301d01003810301c1242d056000007524200165401e02500441d0904403c40003504003410490942c81040250300c0d0840e8140920340c0b9a845100c04a21240381c02d00401488007070a51010701410f1030154021000d84401041e14195403001c600c602c1040c001000403500752007041c44010031400040004650317816840b00410ba401800d9070f40301e035102010740b01c0741d40b12156442600003292009801420906140d00720803040c0b8000d0801a00702551040044107a030828001000203070400c00398182055058820500b05000680040003c803002c030a61640a100190025086203501c00b541802004541c55140088540505031040d03941e441c0803041d40761 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393997392 1250 393996142 393996203
    0xc03020603130606081f0f020f0a03020903010c3b060d09050609060c1b010b0a0303080402100302041a03090c0315151806011101091407031b06021513 66
    0x18100304c0005460705000400901035201c01d201c00392006c00f00d030000030081c00c0c12030b0000c51050f000d120162200516902030440b10b036623506d01580d1121040c0825086580003000c00050001000081c000d01c0e011602c0710300d140509800b0028070080600c100030075180c14141290307106400213040141d079201ca812064070f1a20803000c441311515800c000319240c920444211090a00c20f100c60707502004200214400d2210b11000040d5803280c45c8003082c840c9810b504143c001c80d40c40c2082c00218140311000b0100142a490214101400d1a142c481c0030381540b10101080c8101001040c44880c0900c41e0940e061801000ca48811464881072400c1c02c00480341c40d00f1408040c0c070001c0d0981041101c0414540185070402240c0e40c0707040054819540c100080c13079080d1341e01c040450014907051200502541e00e0001021040d24500c3c1c050391024260750075180090464004000d610b800003803600c440b001d81550b68565075540040031040007510440649801c0d50068100b40b120000c1054840c01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393998642 1250 393997392 393997403
    0xe01120b060619050a170a0219021c0507080f03012903060f220c0e030d020114040b0402010c0507060e1e0d0b100b0c0f0c030f03040608040c0302060313 67
    0x1503641e060108845409043c4810b03901e4150460300345120361045001703103505c0c1318a00340406180c440f031810b03103d00c8000f15000845c0e5540084d030080c0c1c0208043c03e00c0644481440204006c9045401c41c60b48101c1031000d9a040c0880443e50408111101040c2c507050348a452025480750b9540001032050b085841c1000c1070311107000c0c2c41c05401c0010404891190a02505007481c2c0c114000501c000700d0000d20031810142c0c1600c519141e400c2141c0a0076035800e219545030101c400382e0b4406c05040c040c0c241c3d210010f580c5440034840d0705040150303610b6401904820b0071500c0b65254001038a079505800c038000d01034001d0301c40201d10345400c070171805060074007075410f01c0d02d01c070560f42f0b501e00400d101400d041d0700c80113040105000a0411614941c05201c00c1090a807290340c40c2d020b505680c000706c25142c0a80c00004045540300b000304280415800203c00804002004081540c2c03a88524007c2e8810070145500207406d01020202105c0110350107052103990340740c15481d40070361488403a81104d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393999892 1250 393998642 393998663
    0xf040603060b04060c0b070c051e07080a02131a150c0709180b18030c33072a050a0c080c36070807090605040b09010c06060e0112 57
    0x1a031403480c00940f07003511074503118841c48103a180c4400f001850001e011008003e1a4604c0100240d0240107101040d5600004102400d209100c900c0c20a43c80e40c00c802c0300c5034840350203400076039100c4402030f8003800d88000c00602c1c0700000080c01198060600516000781542019642d9119150000d0160080380d80944041e15250b540a46c20340d07404042503c03002c071000c2000c13030200c0c1910402c187c008840d2050041c80040c0c00c02854216002000751141c950440d416011544c2546101c03600c003a50044403a41c0c440c203104402501d1820081d00f40010070031508800041d8016251030305014403d1070715104a6903000e4540160349c5c01190004030b9100050b01000200c0d5400010b40b6005044000d020040700301c00c1c091003400da0319008410301c001201c4070030020514058a01018092050755403801c03454030b001e12001e01f42c003c0c60f07400441000303001c12080251086050540c0c841c00024a131064000001e424607502400c03c13504244a01270321f00000040002c404242c078500c05119055050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394001142 1250 393999892 393999899
    0xa03150501051c030f03060f0b0c0105130317070e030105010e16022a04020d060b030103031403040c12080c010606110f0610050105030612010c02030307032d020f0f0f04060306 77
    0x2400f000320b241c5500d00c0081d00c0142c4000a8001e20144c0e080c40c849240004041d603849041c1d0b00040110b0f400031910007000580d07403110143c20f01034647e008607040362010070f285c001e5038004d0072580240021400d4441c80b00c04140e50314860b00c811542100010002d0100b940c6800c0c8030108460141c1e018024100d000d84218040c074004a0841031400d4400f00c01c043c20910465540011809078061f2648168200040c000b2241300d48a19000740c070a450345c240e125070441c41d000d080210309444106d5032240c280104800621410220000d496074800d45800c185103501c0c0c001400d00608501d1480c0f0350a0643c04561164882c54008189801e0000c9841c42603090381c1e06500d40704151108a2904100e1343c040c0401d5005800a640200002c1d115929941c2140c908030700311041e00d10f000b401070700b0010601c108590325005003c0c00f200351011072032081142c00e05100320485a0104000c1145c0c000c0340f0b0701540f000740c00640c1d1610025114040e9107402d0300345100c655501034010113000c00e142c000e010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394002392 1250 394001142 394001149
    0x30608060f07030c09081c022e0f09140a1b03150b0f0a06020a1a0c0306010f02071208070501110405091311040f1a01020d0219020d020a0315050105 65
    0x6000354407501c442080703519200303012409010361855100a02c581103400141880741002142d02054901909070854103c41800a0a010b031802d00549002d2001083d0030144004154804516003861000034181c01440c20400c080c1c42c589201510000c0c00307007684180004003081070045a40b0868a09100056910a0b0420340175540400360001c0385900301c2c041d440101c2c1d0b000ca201c00c1c00082c0f40321125120760b00014164941c68228000580000340107800b0891100405021541c1145007107409107403004070403905000060206041107090100081c07140d009120704809411452102c2c6103652840c1003d4a15601c03040003102c1da586072103800803a1901d0102542e05950000709401c015844a1050010035011804c054603c070080a800341c4035560f60380301c1d01031619a904400300301c0e508502001c2080070504c1503241c0c150b421012442c42920b60120709410800c1014203000584a9580046003c4003207500000303400880c078060100601c4000c054032218402d40030401d01081c0e8985092 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394003642 1250 394002392 394002403
    0x100f1e09240f0f0e0d1404051f080106030221180303010b04030b10030c05010c06020c0d030f0f0b100c0f1401020c160302030703021e0301051f0603021206092205010c030608 76
    0x3941c030382e178010030b1110120910400364907111304202001682420303118000076101d0214200c1da5031b00c4103514448070888940024060b030041005040c2182400c2c4003103004420704505010b50030203201c1e0200082c0c401040c00000002c2c0107480d10490b6200c2d81c40700c1604900da8800d0005607245182e4000069480300c0e0061003d041d0f0b98014010341a181c07401c2c00548030440084000c44034180c0a011040c441d040c100050130a6a440e6900841d140c0d160081d04003c88012090460b889410140e4842c07441d1180307001c00821800c2440c01c400d0340c2086040403c0c0c160014500144804c51402c150303c0d00c00015000741400070f080c43c0070307201030381000108407003440190321000390940c001910400251900808002c103402c1d640440d50415a424000642140d40403903812419805001c0b0101c0380650355811417014260509086150800341004041c2c10700000302240c2c410044580001c0c0c01307880c075502080030070305071105d4406102658030784580a090000050b20010345801000a0a21000103d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394004892 1250 394003642 394003661
    0x40801150b0a0806060f0a0f0f05180907020106050303070804030c12050d03020a0519080108010c0f09140117070908100204060804020108060111070602100f1e09240f0f 74
    0x1007481c81c20040b1402074a144500500c2e40d0390200c401e00048102c82c00040041c90311050035900d100900c0c04110000d02085000e108503004c00c681402000518003031400d0074902c2030f000301d4001b0300d0741d078031302400301d0140100d908440c0c0c1502011611104001e0000040c2c001d481c03180050701207050b01c440810095040c148000b0f03245500080031048000e00031303801070482903c14074244d480c05410b4a61280a58050082d42c1c4c00074170024010000c0030340a20800f0000301701d80c508002e07521510300e80100840d01c2401100c0c20840041100c01c091780c0a001c00b10003034204104902001d29120700040d140401e00e20619950380035002a001d40b1591f2442140d00b42d400c15120010280c0700ca0b001101e60010007407600341400bc00c07522061500790b080000f02c0003440140d0040481620510f400802c1e503804a1007500e081c3d003004070460a07c2d040c000c0c98180713030b130040b140017403022054281146128107009030308102400542003c0c647d034000c1c0d0001680c111851205221085541620304129000c169 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394006142 1250 394004892 394004909
    0x12150c0a0503040b0a09060207030e1201021911010905150a1802131d12070317090604080c030910030c02060708010e18030d020a050a1b050a150914010204080115 71
    0x2c0010001841096982c0d044030b40c1d0140011040800d6903414126440008158007189182113421010310303090b80a15104150007000750b04080c4611540030900301f00241c000309101d90000c40c0c04542d402507012146280e007003422266082d4400c06c0032860041c2c2130354800304540c01e00e00a6182100c050346450038550b40034180003034080f460784802c4d00400981c205060040b2040c455200340704410001c0120202c16510b000780d03501518600645240f07451840c01c2c02c203140c07400030032840c4d690209055921a800030702c0242e071003920744040350543c0700c0d8070180d40e4880d03c003241440d0601d41c10380c00a00765400c0798003155030036114220b041e100044e09104101c1c107008440d0001d00c055541004020682128508803400d10b5489007070700c400c1e82c2204000d500040d0703021030800c2103940d010825140c90341000300c5500840072161a41500c1e500b030410003505503a9204010501c081881d4000598560000080340000e00f07030201c1c1c14040d50052050000d01e42c240b08081d0310050200c441d03a01110000d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394007392 1250 394006142 394006147
    0x3050c0a030b060d060e0106030e010506060412050709060617071b110112090605041a01030305070b1003051905010f0b061602010e28090b0105070f1112150c0a05 71
    0x6103000c90140078046519600a10305001e2404000018069000504041e5002c01c90365810941c00504a0700c5404914040313038141350600030030313481e0001181c0c1a5045081c466004100f181000c40c0781603c00d0b8071204841e03140590005d0b149a1214030180b144d042c200d400b000c5611790304070440c0c0c1a8880c0d50303400c2210314405a01c40000b25054260401c011060501c0c0505400050340c00d0210783c1c900c3c105842c01600d41d8104001c0101001c141c0d031215060300d03000c070615419624010014014210000d0000b40c45a010480701d41080060380b000755440802c580c1c0b40a24840e0081900c00b1003101200e5541c203100d5044855212401600e44103440030308002e041400c1f400401c0c01b0f054901405034107100c112402d00c802c40d00d41500030000d03610020700403820f1111402480d4019441903010b070034624507003102c0c0c00540c1e81c090300306d4800980110040081358440cac1001d043d00f006070900340340d0212508542028100010030080c440342c0c060000b140d43c82d59042010b6013688244070746c1c1000a1000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394008642 1250 394007392 394007407
    0x302030a03110607030603050c0d0201210219050c03070b0903070f05010c11010507021218030307030c0b0a0603020616030201111602090906010e240406141c0b0a020703120204060c03020d03050c 85
    0x540848042034bc0145403900002c41f01c41c0014440160a403050310f0800c1d000100f031720b090070340800000c000d00031619041e460000450050381d1030b401248001040348043c040865030b4240d0170016900000d070465103601410800b4076000d8002c000702d0300202c010a00b000181035100030706101f03003441005550050003071800240c28884241e800140c9015402c4450701d82032020752010005445114441d44030500c0070040360800b82511b41c002061640410700303011050005850782d01c04d4803401100389044442d010704034a030903405071200403944c070b800c0b04022818000000e40c00042000c2c0900079590714103152581600a80c0741c1009000d0070b102c0c1c51010300032520068014400014050341004444408142ca400203801d890b1b5a40c055401111415501c4203a40713840503034000c0400c11440d030428142c885903101c08011000910550400358080780000c1498007425a1240002c24480c04655442e2130b0342016140724080351094006200b0031380d50700042400ba104032030081102051507410404c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394009892 1250 394008642 394008649
    0x3140702030912150408070b01150507060207030509180109140103020907050310030c080619091203020903030d02030108030a140f041a0c010e01050f06010302090a0e07090302030a03110607030603050c 88
    0x880c0d1820401c5201301040c1038480820561400d015030b1003489059615805030a20040518060f0000c2e6000068180c84013140ca070054101d81e10a903000dc00035032200d20f1801c00b1b590b58098168a40d40003600c261003e0660341012031524103a480d8040d080294180f00f45c07900c2c815502c2408000d400c03103105008a91a0380c050b0010b503904c9100007080c400880e41326501c040200102d5400719059510500502c0744545a074008041c3c1410f80381e004100100c12030700c4480c581c0c1103090f010f01c14540c0c00142c00b8100c1c2c90500071148541e600940955503540d4480c00d00c0e0366035210107160b0001038081009010780022203001c5810a01030b48042c1c074105400c3c41d079916031f40749261192a501e10401c1020818200080c0515000c0d1023514000044078074050882c1507005c40000c0003241010310401441d030080c0d40d1080740c0300590b015210009515610030034143d840380550340001e50302d84603106c4035008260384002e0b25164a0747d0302c03003940e0700c60301c5105d02581a59207a000041054100942070b890506 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394011142 1250 394009892 394009909
    0x20106080a150f0605060c150f090307022b2301091a19090f020f0109050a06030e2410050d0c2c07030e1606080c0d1e0c031407020309 59
    0x80b0000041c0b04c3e6940e10010b0500c2c1d000000344e0700160032200e4142c013400d040440241c1d1107070750324000c2c0c5018900306550030340701c0c814108000e105509484103280303021190390004007450300a4280444600300c5042400d1000d00325a510b11030520840e0b51114803d0040c01960541580504207050700c80140c440714428450003000b030b4402140360301d4810f203448941c0c01007484403401843c80d903031034803000d00602501c0c01500c120f442c14040303065000c1100d62680020401110902c0c9800641c2e82220720307045003041480c4041c02c0321122898900850300000d40c04290040180403016101c1070b5035402032081015040201500419250204010032100240380080c1c550503010b00310381446824444650703d80d405da68040019655145d183c00d0042d003040042c16079486803600d001c0c1546422802081c1032030041145031009800300f01c00c04a601280c0101600420713080c8840e001014034002d0200411009014000290400b071a01301c810300c948a0f480d0098401d0342c05180f0b030001c400103009000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394012392 1250 394011142 394011161
    0x501020705010c05010905010921030506032505031213090c02030a08041a01140a050409470a0b0103020c15060604090504060c030c0521062e020106080a15 68
    0x5548410006c1c0c00200e0038842c40810754450240c2129001498042c04201b203800030b0500181882e19052004540d40050300d0710405c3c660710240004024001d034040b421240551245415214501810154100002c080c00000b0800d200c0707800c1030b955616807101650100510800075820401ca0314444c140f00e43c2c0c0550348140a98105110f417100d6101901e41c0d01002d0b480624200f0005040060b40d1801910590050404071002c2c40141c54070345500c80100d1420101100c081c200a5000d0106528569840e0030210610200c442944540d44003600001d03045845204c168a0818240380944c00f0f84280c0d42e011004000801c00a908484000703158580500219803040e820b000029080d51755002d0103224601c54500402c5c925000306001e81541c144001140500009004501044245120104010f0101454080c0c140ca50802050080c03289130300100c0c001c111000d03629074000307803001110441c881c070354020844541e560401c1600c460141034010180071503034915041d17500040c0c001c041d98 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394013642 1250 394012392 394012403
    0x1407080a050f0304030e040f060f0e04030228020f0907080415112206050403051513060203070c02090610140d060b160b0a090206030a331a040501020705010c 69
    0x92182c0c0c0300444080380c20480c0c0840001d140025040521700301802001c80748140c0843c2030002134100100c14685240c10300869501c00c1a0400003030a0610803c1800ea00300041020008510b11a15030000c0326a003e80003170b4002c1400c01ca040005081c5102d04610a40b502e0fa05e00059469560f111055a850701c202d802d40b00b40c03107a0100305801900d8000f07141601e01210b40c0c117501d404c41c607070400c08410950300000c2448024001040402c40100c0c05101400e42524551459910380134000410060310f080a0030783d5101008010b032050304104001c1d1230f1130007141d01c5041551040100580b01c0701c46120200041c950040d072448030750001020308040c014405001ca001c075100c803811181a00109c0f8030400643e4403807007200500010707000c1c664100c035081d6002e00c40c0c0c2d1869004203059101c040c0006401d1503440984003d0505003c00c802c03130801000651421080302003404007914890790140100440309011230300002124507089804032541a000b4141180c030303040c01540d41503030081c8103691 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394014892 1250 394013642 394013647
    0x15020703031508070602060f101503061802030f130c1401210506010f091a0706020d0903080910090203062205120711011d090c0c0f0c101407080a05 65
    0x5880b021001d2000e058514000c00104d072608100074a4448094001c030340e58103050007842440d04d9891403905c2039171180381c10250b052101d444c04800130034207540410020401c2a0a00b8912516a001103010722821200c149042c0c556001e40403070040101c50082c0900c0d40f030308080241c907400801c0c0c880701c100c0505000060100f540306024141e050144480401ea903220100043c41d030308020606802c030640d00e4014486c6003850100b0040704452803400740c020a021031060f00b0440150100c0344600c0e00c054041c84084044d15010745040400c0d201600c540c001d602100040110b070b88075140000750014003d203450744990f81d4007404060980c141c4d4510301c0d07001842d035003c940104010701c2d038a000b00e02d100340e40300d140f801c10308402052510490304100305103c0400ba4282904071500700800304031040152503e8103810b0190034480c031018907001d40039140c0c0644200002060080d4507400940e442107400d07580550465800c0322034480b41c4201ca0050010300c0c00b2801040c080d12010b140c5041c001c3c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394016142 1250 394014892 394014911
    0x6051816021510031208040807110d12020d0305150303040302060307020a05030a020705091e0703050c0c2e050402060406050304050307020d120207092d02120103080c0705030a1502070303 82
    0x2c05940880d402080fa14a05208004000c1c8207950032070300315400d02e400e68060070250303030f2810144114030380502a14019030140300982e80e040042c0c0465070f40f000921109070f500d0080603449100f02441900071a142c440010550007002a40151164004001c0e5140905690030000c9680000c0d01c100f04500c0348400000010b20108020100d0004075001005140d1070001007200c4118020101100c3d00464081103807000c000b441c5036904510103042c049069035440b20301c034046024032031000c800c43c410300c141c03040c5c1d0400c0c40f45444241c1e0704285100d04503807080d02c82070f01520000c0c1ca0007500300b04100030400c2407603c910007071504144101d00352480d00e41290000fa8401d50310680a465000409081c0013840c1d404208402c01004510414030065420621040003021a004403501102c910b0240c0d120080349a411101e5409101090600550b108e080c181d00640141000c0400341c46040c0340480c50346000216801c40d140d201141d4400110320a9a40c40603400090084007031544038480301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394017392 1250 394016142 394016173
    0x50a06050c10060f090f0b0f100e0a0b04080111040308090d0f08070602121602070b0d0f05100518190e03090301060b3006060304081303080406030605181602 69
    0x85004140007001504090b082140754000c8a140c5039045441a11f03252200321503840d0000c50003500c038000c4444800f0700082c0c00040d2402c100d070707043c26540400f0a050200e05000c502004d0019030f21514000c000411038100e110754580f0aa01001d40311030014000c500c00c0f07150183c04041002e208480d039000c0c03502e0550f50704955401c401405c4410b01c2d00440c4482d20800207600e482d506c141400d03429140d212204a000e51504110302520922900000f10403100340c03020f4001c601c1644505100f0010b600d804100d4500c90161806014400d5044a824407000301450130f0041c023401c20700d100c0348051844003441c0c10040000f45400484c60000b0300c5100c0450390281306810003015604032040e503c2106003040401502e40c0c41241e414060705001c01559040045584c0364000429200283d5075203460504c030549000710384400e10f01b01c0d9184404010810345102802c01c440e0151024010030361514200400a10350002d00c041042c00c2000090080d04e9404003400f00070481d00548210b5007a900d00d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394018642 1250 394017392 394017401
    0x90303270405070e0a050108180f01050906010e0c04060e0a0308160c0b04060206040b091504082212150b060d0b10020a080a0320070b180601050a06050c10 68
    0x20081280090148035450406001e0700342d00440a2612913110143e04002692040385030141d94108040e050025040740c0c20301d020079200c0a503103012512030a501c21a8980600821982000305000d07840000400d5145d403001c1070302074047e2011090030541000000c0303841c480025403859110314100c000002003200e42005008180070010000c420708442e04200c071950280380c0c00060040800c0200704010366006c00d0103130304294031502c020581c0e2150841d840c0386c02282c801000070106030806020401a0103c020041c11185202080d4101d000c071402ca800100395201c0e120704480d11882c50400030352906c5c208540d241213014000707034000c3c0c0c10010a030700d17030090720348084410b90329081c0a60914154280c80c81c07045a92004080c259056581e0315120300404034000245074035264261100d5440b02c203031410101112204607210300103410600e5400070280d81c0d00034040b82035224020103503800310700b0304c0c10b0b10b02c058041e140803071500030115840e511900308400c01d03000301200c0904c110054004d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394019892 1250 394018642 394018687
    0x305060a030b15010807020708030f09040b03070b030702150708060f01020a170703030b060c0d08040f1e02040b032b05040509040507050a060f0905090a0e01050a06060908030301031502090303 84
    0x400c059a20980f60014101460251185066501010341003040460020450300300100d181c2e54903446e140b01c43c1c0400c000c1c0500070b00607035041c0541400072134800c2c074040c06507204854036800c640f009014900010503c0e0805d5610100181c1450000b9401d418a08550f2a588a041c07048a10450b52070b100e04580c04100c012088a2010026002c0306055241c0119901c064085a4091604804c460000c4e616074011112009000507070340050180300b10a1801041d0300d42040c9014844202c1070b5940d040042c03510400c0348103034076000c1ea0b54030f2800c002450340039682c14805480e40044465004103141c070f03000b00d116010080100004521074503000051030080c0c0c403840041c040503046c00104564204150050410003421080341ea405a911098004c1200c1d015214850161602c80406001d041d4082c0c4000c01076003000280300340c1c100c059100c00122155941c0e1a990107813a448420b40383d01c420b11003d029841c080b1140c2e0503091b010b41c001c3c41c100358004c1c22203150541006210003031204195 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394021142 1250 394019892 394019911
    0x9060901120f0c020f010e07120f20150711010809010f06030c17030c0a1e023a0206070602090d15020703020106050108070f030f0b330702100305060a030b 68
    0xc2220010f1601004042c1c0380610a40c001d102000c02c0c40c5440e0f40d60000c81c400d156821030907a25100c113110305000c1c1f81021603000ba159400390500400920340610315240c5481c00340d0901507078100180703481c200351124107500050f03000301301c0080401100c001001030082c0b0615503807000c0361a042d03c3c1038812040194410018014000e14100c607040440202e8624070071160010443e484107440007252651045038099a858400d8400c01e0140411528174400250041d1005076a002282403405c00e440b121403a20b01041107003140307420450507640410000941050013488a08001102d039000b0704a01e9a001d84031252241c52a120601c540411094000034154001280c3d81415030a0180307401600c1b0a080450305400c1c003203030040a90b2081e114800405540c0c4008080c490641d421201e422039009001c1903c000555400c03601e000340ca840c04070b52010340900860314402150040d2141c4039001411444883c101c0700050780640380041144d60302485c4032102000040741400c4041c02501600c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394022392 1250 394021142 394021151
    0x9091b25020f040b0a0e0405070906080615011b0825080d0b0306010e010509150a080c09010905040b01030b0c04050d0303020903010b0a080d0e040f1b0912020609060901120f 76
    0xd0051041c0100310740c0c0b0482c010703420b10000611949462010300111340e583c00c002d044994440c107000f03041a10300c0e007000399603074180040003940e054000b030002e000310005c2c6118452400d40c05e0040d6103140c07002181c411810a203100035004140b94001520a000e21100d40540311010404c0720300b8944072186080700c9030340000c039240062941c0ea01c18009103c0d4260002c103219414a03886008140b414030170781c0c0c0310340071410010300b000014100d8150701c280b02803d04e060041c0c403008050388503a1002c04241c011b41d0107800000b00004036000d21070081e90040c00cac1c41c0710359085489a6140700c4009005401034001080000f0302c031344608006500040c003a0794016110340c206402c046c00c3d00d19041a051103032002c2d580501c441100030800c0031000c003190520700c08001101000c2000b078007021207060070803440d00d03640f18212902806880c580e40b1941e80d03813815440c1c41d201d08010347e04182d0350194000c4402e0043c520203003050b070300802e03030410141880c1c04444040d14900007610703031b0003000300c01a0761036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394023642 1250 394022392 394022467
    0x503070b0f090105010320041503240501050607030f020f12040e010b0a0e040b01020f0312040302070816050409080f071b080c061e090612010509060609091b 69
    0x80203441d402c00000c60080c000e80d450f5032505001100700302185001080c1030412140a9a43e41c0e0040d881d82002041d81140d9a80c2d900340700c0302d00460b0300c134854100001c181d444040e50f005031003094107a441c000e14042c01c080d25514102d41001900c1e202c40c00758131460962810200c420428600d0740581800020f603164205800440340f4201030380000380011042c09000d1541d0b4100e4100ea10b01401030302c0004d1804110300c0101d14180c8903900684050000040304040000d0041c10b13244954001c4d002c42d010b1903500e40c80165280a100340d40321540b84c158005115a19058000f03d501c40e0145d0400da007001801200c0100030350258000b25500c006416121000d1040d04400c840188503c001030300b241030801c0c000c211244990400b042e9440180c094501c00c048030760003550301124015003015250503001200000c81d000078003a081c0700c3c1c2e1a00001030804d1411404880462034041c107003441c581c41c1c1c09101502c0911100d840304104205102d0648182014403514481080f4420040e04c0780c0358 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394024892 1250 394023642 394023661
    0x1701020d0b0a03030c06110d0e0f15060315040812071d060310030b0c0f030c0a140a091e030501020a030b0405010509011406030a0f0203070801080f06010810020708070503070b 77
    0x204507440501805003442d04101094100d10b03102c04081d04a0740108626400c240d00d00028814140c4204545103802541400c4003400514805905080000c64807021f000c4000c5614600d0205c0f403c42d41507211200c1c5a010041039402950030034403480d5054204085000e400e003c001d0101e500d03100059a4070035400418003400c0c004462000d0a4540078a9410030018101c0902c402c0c1c080582854500e1010480b40f0030b4070412680c51192680086440c0c0c1030008201000d907000c42950700004030090100045802c2e0a0111032800304103440d13445c80140760045001200a070700c4208503103810003e03800404980207000810061520795800100780000c0820030040302d02c180c0010b4001c005560040c0007446001014600c0844200d40203a00c83da0342e60140409800d404910b000054001f2081c424015000f41005050310500d10554020304403440003d07644120900c5085103641c024802c3d0b20545426a0040590900a003005840c105c01a00c9252440e840380e6000c85410202d80200034901a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394026142 1250 394024892 394024901
    0x9050a0b04050d1403060d02030c0a0b04030c0602010632120706090e10171204092028120e0c1c050307060b010504090c020f0d110604110a1701020d 65
    0x5801c1c8600103084d4106140710030b010003442a0300840751001d4070019550108004a0301500080c41d4080141d1152011041c42d04948000ca40060300580049465401070103104190356250391407401c544040b04100d6a4214843c5c01c0740101c5000c3c0d020001c140e151840480c10013220708004101d09444c09200810b90000341d8007180711240a441880043da18908044086800041c0f28100707220303c41e44500c0c1440d88261000030106000100015500c0050700130728410103a01d00d0301d6507144403030058400c2d28800c080b200d581112100d1a6080300e4a80850500c0180754a46481d1a01c1c4242c41400801c855503444102d185601100601440349044440507614442c80081c003000000b240d510306580c0d0080caa00104000c4e101c2d41c161760035910503401e51300200b1400009100e140701141019445400c00075070213445026000c60324403028050700c01040c45001d81030040441d41c0c4c070380c0c841400848121240d1548540b072500300003403041031040d0030502c0c4081c1c032000594030703402060750b4400c64 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394027392 1250 394026142 394026163
    0x80f032a0c091e180c190b07031b0c05010201060b040621020f0c030712050a02030403150b060d020a031104050d11210616031e0c020717153709050a0b0405 68
    0x251907402c04c51032400580106d6008560f0042c1e64503448030307403030310301503401000c1c190030a030741080709030003c00a204441103d10b04030340003a0000c010103612280201403034400d03405032801081407800403100141e0102c20303980d02d02924080040c1001c40d01120f4400c00d074416685020300d0f0b4008242d15090006070340c00d9015409003030602c285403902028020f034403401b0328440075001c5440a410202c511806410924517400000c0c0007554903c8040d641500a400103152440040e142800d10540e4000220445042d18402440e900e0303002080d07500d00603100311104641360400661401c804060050a0400305040351301130203800340c0c1c074150b040c9841c00e44007800e0400c01c0500340b8000c0040080c25000d02442c4000d1003c01007551321007100240e02e86045075002d02085003621044814031100428035101001c40b5200920541d25540d0040481041e100f18440d00d0100f41c86548810402545100c046040400c0010030031202a481e481d050031182e550075109890401c08200070084203008003e9907 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394028642 1250 394027392 394027399
    0x106030609140438040804061e02100b010203041a0901020d020c18090a1a100911040509040f050307050c0114030f061306080f032a0c091e180c 63
    0x8a2074a921101d01089283c000c00e40a2021000200e65103092031644401e401090100d2003480d082070b20745000309607c42d00c2410000740c0b0403984c1c40c6080c0907080303c40d03201d40c10383e90060175410502420316004002d80b108090540c0300420000840010110641d10000085541640c44509080004e4100440c000403035003190001d0208081540e03460b90f81040503c0c0f100c03000000707560364030400c03450310501040252040c8040c0391074404081200240600c141601c94a0201b0250703070781d491030150341c1c8030f05d0a24660101844244954180f0900301d0340d1146c01743c2c10b11a0320400e103440d6242103038480c03035099805820980780030340b0550300b000300c03000e0603203020140c2031561a08503460b10f00194003400180c451405c0d001341083d07149140c3c1108015042d07040a50304007402e96607507941d40740e006540150a200905030401c440e10781910598a5030143c80e0098805448501c003040001e0398010030a4041c2100c404110b10381d91b904601642c030a0031907064101c08841c520341d181d45403c6001400910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394029892 1250 394028642 394028681
    0x1140a09050f240601030b0603090a0201030e120f030c04030f0b070207060c051504081902060f06010206040b07030e03070605010305010b090109020a0905060310151722031110050106030609 83
    0x559541c0c01107250074a00c0c4281a10700b10303841c0c4c8001200039003214408964024404418032175914004580e00800d00e100740c03001c121410003603403095254040c01c0c02c009241745c002d20800304201e403c04000e41e4000c038030151040c94aa203d030f40d000a048113140c01034441b039254030100603903540c04000c21000380c145403c011410080558031665140304500c560894007814401040c01c00c411003040c0c0d059210200030b502d0303074218084002075644c601100c80240c0b21b1001008520340d940045003d90040740c204d03200e00701550320120141c018081280881c0c2c0640b108210303501c0454854807a03140030310720901c00407503030a51403001c001040b035045c1c002c500301c0c03441009810b000c0390b00501c28a04403003064540903201c1c1c0e94440408000142d56100c502111060480900c1b00f9520a4020700b0400c0d0601d0259056118070903020810300c42028103090032035510040b403011034060b00d0314840b003480d520100c402c844134154100c0140c820030703840000030948945007400558002c0c00b03403440c01242d00c5420038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394031142 1250 394029892 394029913
    0x1b0a0506010308120105151c0609060803090a0b07050309090705090301050c04171209010323040809281a1306050c010605040b060d1503060e1612020a1701140a09050f 73
    0x184c90b03c01c07405230002d04896406d40c0c1010800540103140107100810b020030070aa80c0d403010641702d50140840c54811144214086804800700c401d403500d503904140250308045000040c0480c034400540440d06000007408680e00a03030b403d000d103510400c5c9410000e81c640e4038200302c180251100d100844500d8000303a1030b00058481010980d0303106402460080341c200d0346402d480003841c00070650100880c03518030801c014441540c004104d1030106848a81480b0b19114010b014001c42605a0300755940c192000c100c071301e104a98601001c1d49211040745480504100b54403100d206130f2110300820740118034544c2e004c000f03104400062106072403d1010802580001c1e680c0e03c5102884000180d032404c9181310241c6210000010310742c821b4040104c01c0d00321809a55401c44460000810001d07880007103035103001e04000f0080503031b000d01822605820020440800007113140040c0b0559615103004010302480300e103441c01498204000a8140303028100700d03007003484018000695921105511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394032392 1250 394031142 394031179
    0x9060509090d08070c05010e0c031515090a1e05010501020712031e02010612051b0a030506060d0204240f0e0702100b0f0d08030610141b0a0506010308120105 69
    0x6090761043c034260311180d483c040b06403448421410041d1075907117419070b00315090400223000454000200e044407100c08000f1840c0310201c0301161180c94003651440222840d040c440c1d4250b41101c440540490040450f00d600401d11350810131000745180c981004000b03030358052041c0005096000d03080d9241031069100500744043c1d0396071000d40c0301540004243c400d071003075004034084e00000e8881d4020400d9810302c00e40d51419071200070348503028090000d0309440c0103d003c5048a503c4009000b0310350390030041260107941503109030781251302c0714102c0c0d0354560103d001c02c83d0341803d0000c0b54951030406480e11501442e5400c103130b010003c2c80d014810803940008c9c140c040d61140d6a0003042c01d500403400310351745039481e14000c4c0e04690b110b2201020022004042c5104140507110b400d220b9046200403255901040c2d0742c011140e508204460903501e040d0075000c0f01d200c2c640225114034850f40e039450300c1c05000b680700f61380446000c25541d1021202810017401040210f401010b8500821100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394033642 1250 394032392 394032403
    0xe03060919051204060f0201050915040f030311130e0609040f0f060207121e03050c040b0f09060706140f0412080702010f060303020106061101061202090709031b0906050909 76
    0x101181c001c4246849070411508005910380b52031622032840c0c40384e03900d21015140130b11260fa008055400d040c000354652000050313001c0f039081840840400340c0c6076a1540c0b80390903002c00d4203404054440f055111580701c600b000b001c01c80c1d41582455125441c1002f48030949030058441881202e0b064140070100d4074105211144981000b800c140f070a61a20f40400244100b110043c540030035081e0112a05401800148010f4040c02c2c45600c0441040400c40c100c0d007084400b989491418001806841e03514230161440c141c40c04207007468810402c00140d1540c00c002c0045800c01c1c0c4405211076500f0320403071000d401000010f03d43c50380703081583d1b542d00c0d004403070110340c400c2002d03000000f51514801d40181c2008002580f0800c8869102e0030001d018100034000c0c034002ca40351f20301121546c10144140c004454200d1035002ea071544581c204802d9150203846401080700b5007002102050142d04078030094403032103044400c00c9207480c1594081d260369901c80ea00c81c0c103456042000b20403001c1007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394034892 1250 394033642 394033663
    0x6080f190c0e43020102032e080109060207022d091504090312050c090609060705070509010e041a010b07020d0203010e10020d050f0603030d0b1804050d0e030609 71
    0x2942074160380c1d0f000ea212070400c103440c1c02500c24030318420000c0d2403180004003002503412030000400e0038010788410f07400c1c1c3c8019aa4074001d0b0b0780e00c24103014502c1e40c1000150b04502c00c1500f43c1d00c0c0d0350361011800d085d40e08444040c2c543c0da900140120461508070300070f1070f040002d0b5403400c45264060301824400d14914000398040d5802c03100050302212a0700b604002d650004000300210030040c2001403500040741d034031f45c007180e1801c0045509084c2c51425203c040c8001002e42e80781188060074001035401c424821505480f940724045120342d00d400200740a0907c0b0300e0b502d4500d2401d41010780c068001c0528098174840300c2e0b0010b00805980f0001c072240a601900c00103078021151001c01d00610b2410501049400b801100d203003410701e150000e040904e1010400c0c0082d460b42c4e800110040340c1504d04e03c1c0e060b441000114101400c0d40c0100f202180001c1130702c2c4c1054550130105640d00c200b1641100c0580140400f541d14607001030000a01a0381613006001a2a0032210181d070f82490b00d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394036142 1250 394034892 394034909
    0xb0d062103030506011b0809040f0203011a07020d0507061e03060e0112020d020a23031c140f1303020306070206071d0f030307260901051c0f06080f190c 67
    0x80c070990140d0a64070b03032254000041b181049240c10b001e0519080515082d10682c140207101d22a1551402504d0603214441c011442d090115541a1b83c0740d800a1000c0381c0143c1c0041d41100419070611513140102903548403503481e68401070400400340108815074042c14a0420103000e01c01e12102254152038460034506400344050000600c0036864042c000e511480055010450304201401225030b40f1043d190320305050703001030825440305550000f44e01c03400c0c80f0346000d1202601c200c690545070135600d0300e15460084840400e4090780c0c8407440c5050148820081001141400c0051396885100c038409402581000311006240601c011a0f003d00035141d0b117000a00e03550340158100003110018200c85c5e44001d940742815101c20b0401681607507406203400c51008601c85c1c422152003030f0050b9501850107003001c884550f1241c0030500e10801a644401008850710280706510190aa07440100803200d0554083d928211658904242d0200407941c1a00040e41036031810b4113039900b80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394037392 1250 394036142 394036151
    0x6031312170a050a1b05090a120b04060203060a030605090c1503160f03140a06090e061608070e0d0c08060c1303060b01031401030606080c1f08040213060b0d06210303 73
    0x100c4e0385405440100e5070040220300381c034003080c903031078120000b0f00b080e05d400d0351005130096941030352040c001d017207203c0a8030148a00c00080c0005055070b0046131301090080800320f101d91640c60740d20444604880d140c50036484060402d4a07131078188140d141000d0b500041900c1c514041e254880c4010508000f5800d00c402c0e80c008950090198212104802120110803098508515990040d04092250300c040d180350199580414002107803543c403900c0e21160007074102c070b0484401c480030030008020404018070b80a1501c0281c0e610240640064040c0c0e420504450500001c1030500d800175020b0301e540b030700030480320001c2540041e402003220341000000907110203c2d0010307000f80404100e64101c04c00502c00110812000d07070f12203003c0d1000a030445000362180424030a02100101c4510410802051000c010b82d203e116110741c0030307101a020300204025010000c09841041d040b10845800115810301803a0062141c40c00400021503070088071000d07022400403441500d000901055240c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394038642 1250 394037392 394037401
    0x10302090c0406234303050301181401030b0405070806060d0204020d020c06250203030105090c0d060905160e18040b13020a090506100e0a051e06031312170a05 70
    0xb00026a240420720050210f510282492031040c0100240071000845d01c069044000d1800c00c1006203080c02d45c1a100c107031840c4d0900312500c0d4412860101d2a201d5900c459070581804001d80c1d40e5802148943d40402d1f075400c0615044d41090069009002c02c0d80c810000c00910795a012010000035406490059540d907107072214101901c2803001c407404a10030b813002c0c00200f180702e0341d550103c41104040000d040c051030100303d031244800e205450340685048040780402a04500901c50b82c08502400a00581e5031744a64003518000c40340700a40402112100281c190000080d00584004841a61102402610841c00180b0213080581001d803030500050700c83c1c5000d000307550f00503001410b10400c242c0e9201002c0c0640001c0b00d6584c0144141d000390403070307503001d0445001980303070040c00000913505010500c4940d6040050700c460310341003101d4424a03902c4501c011400352003140c0c0c0d186e10881640c2013018405064810741c10801415100900c1d40740300035446641c102c02101c001140c4c0d51a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394039892 1250 394038642 394038707
    0x5060f091504090c0f0303020f15010b180a090f180f030e0d0f0f110103050403020703061806141b07151e0525020d090306020a0302040b12010302090c0406 68
    0x20f0780b001400f000050b0310201d0f0302d4a420326a002140d00c6071b42210390700a280360b01e458070360380100c07074111000c401400140b10658810001c0d1141803040d041450301c40c8032004c0004e41d000034035406240341c0d560301c840081c0186c05502590031506480d00c2c20101d24071544d42d0300002d21042c1c5401404015480200d40b100daa90303407000c401c0e5103402403526180060b050400c0591540c80f040300301d90100000c400301403554085d020b0180704a07050b070080e1051901c2e60b2030f808003408001070b07510b44089104421000064091081040b6240760010b400803c0c500b4000c08450700411440029801000340402c0d40003442e01c0c0b1040c60f201d040f00c07030003007403001805400c500001d186010b003c3d81c0c0740c204402c110141c500c124511a0800480b0115903040d00b01c0c440a9031102089a11b2000191050505001080981c0c000308481d44651034014a8075640300002c445c0c68004600107000318002c08010401d6103031204039250044810741030302d454149050009400042400d42e04c070490f18840c418440c2240c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394041142 1250 394039892 394039901
    0x40209040603080a110d030c020303060919020a091502120d020f0403060507020d031104050a0608180d170c1603030e0f0d0f090905011401050d1806090605060f091504 73
    0x60340000c200ea113070340e100c0c4c0c40038201c0d0401c0c2d107210103070f07220b1228107806003842400707290f146001c2ea802440c5141c903a1020f012002030002c0100c103040310303442f65150724244c1c90f01c000e18010110360b4400c03c640d400e2480c2511f0300000d400c040000c40d4425417104000003c1c400440340740f4041900d006950351000c0b0034001060059500107001d00b80b9040c20049080d0700454056038005047c0e07420014003d00c01c01b8941c10780158010390b5006008100d0903c00240540203142c0c2180c441d41c80d82035841c406d04840ca1420207000c01c1d482c00500c80200c0c0c66501c441190440703070060558805142071141c144c980201e40010018060100740e114060170513480d009014240f11901c40b0070a4a424400080020b41210030413040034000038880b007000a40c4e07044512130b041c142c2c1c1d81e00034090003c1c0c0265004460b00d070040c000440c0c5855441c1310040400b032054140410b514410180030800d10f205007848411100000c0c20b07980503c8210121450796500c0a030899840082c02d0440075506110401240080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394042392 1250 394041142 394041149
    0x70b071104110306040c081b0a020c060a030e070605030105030a080d09020a170c2d012006010f05061305150403080315040509030c0d081b0d05070e0a03030804020402090406 76
    0x1481e2002c2d01d00d00200900003035100d80d2042c1c0e0240702c1c0110b00c0700300311004802201e40b145c610482c0c0c4440d030500407402000f00800d024520488816400c1c0800040a540c80340043c800801e1f80c85d070000107106c1e41401150700920450404c24119850000440c0d03c501c1e9240e00206071240c0041c0c101c0c480c0519600c2090101d4001c1c10301d00442d0384909038001d00448854046129208040140c0154a004200c0c0d06003400c0700c00c65902c0003010170041c9603100001c80080c505122202c105041d0103c00202d480404280100044c00700d03500d040000e1340b00007000d400c00380c01204200481100302143c07810590803030b002618050035001e0070440609242c022a0402030400a0000612041081c001240d80088000f101c08000c3d5859102840780c1c1c910520300024087c2c0c0084030071054050042c64a00d50102050020000850080410400d260700450041c03405030b039a90248070120354040844520a00281c840700c000b2402d40e1000742101c08010070081c451a0005941c171101d44440e041400107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394043642 1250 394042392 394042399
    0x1a07020102010c0c082b0e012016060902041e02030a142e08070e040209060405130f0503130602010e0606090c0d09080706060303050304061503030c03120e0708070302010206010f08070b0711 83
    0x101c4190a1024040c00f000c0f122643d20031161601c227800400310178108c581c18080b25400086400641c1c0d261405050380280580e405540c80c5c0861103151442a10f21080d24140d0130700603541d29010b0342200450b0001d0201542481840d810002d071240f00074200154400190342c51894035803024440010a40903070420342050254060004401d0031a520440c0181d00c203d4001c00c082d554402840110b500c21200140781160050f410404940504680011a4021000d40e440e040f082c06241c02110320300e50011005039900c2140301da01040500103d608205c0498a884440c2403003920a4000d014890f920100e003035496000008110fa00411910040da201c0400e0001660342e05014185800c104c80c241c1d43c0a080c00c2c0000c51b007030b45020803a800d80354103880ba00b9400b469520b040310054542d6009054540d9140d0344a400e21104108050050100c000200728440c11403000904003601070348402c0f110300420000740b10350103001c00c80100b81c40c901c3d0f0429803520900d003400d0240034104510141c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394044892 1250 394043642 394043651
    0x15050313050f07230d021c1a0a14040320030405040f020318120418090b09011b0e0a0e060a1809021804050a02011101061a07020102010c0c082b 63
    0x2c81e02004110383d0210307121021900420f04a14801d040d481c80142d6549030301040030405e1000502e0900788541001c2c0701260036000c41041c60780d0701d000000260420b445001a803100300002000f1500800ca0760011303601295441d41007641d4003509100f2042000c0560182d00c0d41c001840c500c0810a8500800c4010018404e02c00110000002507100342c59400e644000c0800740c0d600044000340c14201d22031112420341c03a00e850a140345910750211004103e600f601c4060441c00700c1c021000392800b42c211031000142440311201001e201c96100c2c5603c20a000401d00c8011250343c65280c40e41c202c9001c24920009030703071031900242c0b50f410a5003150b946050500420344600310113500c200c40c401d200390380c9000b00d090002d04c52000c84104030b80042461b03006002003001940b0030105810b4017150900040345003612a400301190013408082d01d0011000840c44000355a42401121800c43e06401d040d4540d02042c2c850540ba8841e8190306807807005040b205510f48001000c1644424620450400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394046142 1250 394044892 394044913
    0x3090b0a02030601090e07050a1b02030a0501060e0105010c020315060303070b01270504050c2404060c0b0a02040503060f040813080a0201090906082e020f221505031305 74
    0x38000e41080e18240d0000301400d0022450250300020305000d200d82d5107955042061011080b9947d2004849030f0001c212034034540c0b00140c400300401000144910700100e00d5608040794001d20b5801644071604005940320944056140490300300300f08148450908030a540e4640402e14521808000805507241c400001a0078010306004200c2800b008450448020890102038281e0b94162409001a0860040360307106103403848075a4982e580006e09184812802c00311011150842c0c0d21400100700d03054410010810340407c007a82c0030031149130450505040c840800d9480000900c0724083c0d140060100b01407003480820388051403500070b0002c070415226203410f51107403001c01d01207000c14079880000c10965014042d20f02540c1000e0024200300f12565000074080c14845c0c2c0706000520411041d13103256803103000038079004041400c0d40b81c0d524154007941942c508401010b042c04c110180341400440341c00010700e00300c1c01e628500243c0b00d84502c3d10240c11001c9200008110f80308003031520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394047392 1250 394046142 394046161
    0x70602041d04141c0e0a0503010c110c030714100e0a0303030207020102010e0a0314070c032102071703030a0b0f0a2601060f0b0304050709050a020d050a0902010c0b060103090b 77
    0x4500c260f01c1030450501c0d104154444540c2d60f10303c8106070b40d110711422184e200c040c1c0714003c8150308200040580d80740a54400100b8211006003005500040305595110740200082203111540b203002d400034580c940c0f5040e15900c40340c2e01504c101d482000f0600180751003601c41e80c800d03040001e00420a4075020b40c1d0f841c01800941c002c020032030143d400d00c0701500c3c2900d000300e803105806800d0740761180800104910707a0503030380c440d040441e00d10015a4004c07012031602c52000700b184605004982c1c164132200000703450240c2e02d610201c0c0d662560000707040b40200100035650402807910021514158440024107142904140b00741c01004501c40042d101d81912040e4040e038401d54141c644000e0b002062900f44d86580c05400d814818000c41000701c81480b500556105002d001502c1d000c5807500c4d2500c00b50f402c15215280001d0300450360b0480f00d8140d1051680054000c40100420103e50380040c00c620b04080c0d001e80074811140025096900a4000e90502680701104070b80780e10700103025 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394048642 1250 394047392 394047449
    0x403120c030e0d0f06020c0a0804150e0619030902130c0207060908070501090e040f020d050601030209070504080a02010c0204020f071a01050a1d040f1a09010b030309130207060204 79
    0x10380001c1c1108031002801c0c2003e0841d405401d41100c04010184d00985405000e5030000024001e0b9215040c0e2040c04141120003030300c09052002100f44000340c504400070030700080c0006141c4621010410302e019030b20711480b0060141400e05002ca001c4480f40001100461519000072405003061486241c10764045807480c259686900c2e014451500c07100515526281c900a29011501d002024002040c1c100d039040d5100e031082d01001d034a448164041400341c07040781d00880e601d5000340014030452900340100f551104c1d152401c50b082514000c203550340c401c0e1112020f410b02880c5015501551101e8040300c00c07605608064070743e01d000900c0c0c421620321104001d02c0381580c03814004202450410009011900009199460403801407072802086401900031038440c0426404030000412140020100480c010030644141c640300c0d50340d40c00d540c407000010340302e40c104002e008503655035900b0507600264481d50050715680280340950091040d50000b9444401c40c0703482c1c06200014400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394049892 1250 394048642 394048667
    0x60905030417010213091104050405061203070804061106040b160201290a0b19110a1a242110020313020a060906090308030604090f0503210c0a050a05040312 69
    0x4017024880d910140c3e0000caa0a020648030442410042040107180941000e030b000f940081968611645054490380307107610450f01210309400c0422308000c0d5580114524013030000c018040e1826150680e11944100c2e002840c20410006030401140e203c0c6c400d43c040c041708614079010707602c1445040c0e0081d25000144080910901d030208000ca121110201074401140b907141d01c5401c00090041c06840210b0030303c0c00c003000391240881d100081a1200341c07082e4000c3d0b00c02c4000d45542082c981e0781405140780c0f00101d0304100b41c0c104507405519440d01c112124a0706c90003001219850401c1c003800c0130f443d0031a6003169130002c01803000c0d006466441d03403050361003101e0807031002d545c42c4030a0300d82c0b2900d84240307400303d078100000b0000714100000466114400400c000381034035042d5120401c1609101081c3d403142d00c00306051240d105030050310030020140e44d500044030320301007294643d10b104044100c410441c0201d2160071a902035410349000c1e550040020b80118030000004049000c200c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394051142 1250 394049892 394049917
    0x17040c0f05040e03090f150304080d060b180105030c09041505010323011202010302161b0803071707051e0f0d08071d0102160f050909190609050304170102 68
    0x150001d4549040e101d07042c83c1400d031030055410302c182c0700108041d8440a480d040e412214004031100190750200040d44518402c888050b116401455058102c565039040b000c1400d0081090a181d4403e000d0409200070782481c0840e6640d941c82d998030340c1d6001c0c0c8561250441e06040e02e410401a410903c0000e54031700b07030f800b0009103020001031014905c0602050740c07100311400c0103206c56902000240c00107401030501515061005c4003080f10490320078415221854005d035440707115840c3e60702180007005481d0003036041412580321841c035400058540300042800140076010401d081c03009494200e28210800f403000700c0c15601c00e071562100e5000d04410b00a145400c01e455003d680858080c3d0025501d600141d440000007500c40710400100b0fa065100d660380d6520100c03480c04505029080304140792050760702e01014031110034000341c181001070700910f0140308601c1181283e8000709070000390102c3c0c84c0c20182003080c1180f1881d00310130041c0f216400307110304c0e005d015002000c035040d40c417 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394052392 1250 394051142 394051169
    0x302010e0c03070f0b03090313080604120206090309010804060905010207080a081015050a110303130501050105030c091308040b0a050909090c0a0b0a0908010c0903032006041217040c 80
    0xd01c10540c4558503070284002d11400e814003400040c20f40006581d1014400c4100c03072822146040d064849405a030102070720b548841c0420007001040340c46d070000840c150000703054074104040d004c1d44900941101038104491000000d0a0015139004400c06541000c021540c07000c09040898080e03001c1d4440701c0100310308501041c001e603480d001480445007150038110f44118542c9003107645030301c44112141008005041e8003001e00c1e0601c000d5000d11103c01c46041842664a085825035005034030240c403c0d008070003030500c551140d15205601000e040c86c00d0b070142c003803450020b070366000b65040540240d801040004000e1342220040440031801c6031b01446941c0d40c0c100003580c45800010700350300300c01004001c0000601840281400d0151400c2a41e40248c8514240e400c485005d40d0134400554404420424142c1102c080190105520800589600c44403c110b03502c1c0b502130001881c1b500f18400d80c403c0c07140306080c403034041481e038650720140d401e05040100212605000d12300251000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394053642 1250 394052392 394052413
    0x903050933070b070804060b0a0e060a0815060f0d050610031a150f010c080f0316050a05040513061d0901050702010216140f030406120f0606050d0c0909090302010e 72
    0x38070041d030b0b000d182d200051050584e51210201d0b50001c2c0030b00110f84690316200c0c154503659480e81140701902841d244005c103498904204030107414242e009607000d8005891102c0c00e02c5510000e1a03200e1800d540c41c4040000700c40101c1c1000100030b02c06000c42c05080705019113801d41c0c0951a00300c1740034035808808030341040004e0744c841d681a61400d42044100c1c0c4c000c010385c28804c1c501c4618450505200b150803004e6111002c16074880c15440448440010400c546103400d110301c106004e603107145c0282880248113029219200c0c90007424894995035451060000440d000000601a0710849035209124098540311481c4140c8280e034455003001d000689083c414425606480940303100c8019690071a02c0b25860020302d5940d40c0c2043c060013900403200307601000200010304071681d81e1241075242c2125801201c09145100b0740c030506002c07003008041d6008040c0c464a5040710780014030102c14000654105559500c62000e15091400c1241415011b520140d00300022509032402900ca = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394054892 1250 394053642 394053739
    0x7170d0302030618040809030703060e190209071202090a03061b0212120907080616030608030a080103140c040e0a050c0a030f03110109060213080c0316050409030509 73
    0xb08a441a030442560b040c81d0840810481401c0c5d0864021098545040c80da60042030904ca4580c1081c0c883d07903151900c10814200811400202c1d0100c0c0041031044940e0b0750025031841e10282c0000100039074210b80002600c00c130340c125050b11100501d14421580d5910f80b0794003520b007450942e0f0148069440e10032569001146210140000e03072079072854411030392100e18443e2405809207030b03280701d00c00021a80c4003007000310301e01840712030704049401c0a14240c02800c0c0c4115801c542200c1e0030034840720200e603800003015070540707501c249500c003030311003d00382c4500e4a0314a0480581c01401e00d030f03da004550010035414000c5000e1010786500011140130712000c05a20310008103201c0b00c400d18880030a21900f90f140398540110000f1507004210b8031f03210242d0b00310b1428417146010386041080494802c1007092250207069000e00340140341d40f8120152102140f14960207291545401c01c10507100e68100d6030081d1008200164004d040010b248025402108400f8041c1800b0281d501102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394056142 1250 394054892 394054897
    0x41406060108011203031b0e190302010e0108041e0c09061202060f030709270c0f120b0105071704090b0102030418200a0c020114040320011107170d0302 67
    0x20685071108180d1070603080d1080c081e20220207a00f050340d9031401004006c0200038407002d0b20100d503034400e401030302302c010865003990140d5036028900c9044002c00050360005291356007503400b400d016190b5900e604244540c0c4000285417010701c1c80060010b404c0008803031855054035407642c010007040791504070141206218000c040e511910600c4400851440d140056038099501d18004140c40d54904400110303001d920458505641e400c0d90002d55400e052080c071426412501c1c120b50144440000680000d040600e070710704d07150721807608180690081c07007154101c0351b200b0001c3c9080c4000d64420805604039008011038607040101310350042d88004240c900b81c1d00c40101000e5100d100c40700c103000500000c0880c010400c107024046000c21002005445a03240a448520844043e88001030001c001c41140d00b81117101417000b0f00204811444001071172000018140c4840f074800016120b4080d410a1a0030f1880b030410081040080350030300c619330099900c221600740343d072500140d05a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394057392 1250 394056142 394056151
    0x21110a030803061e030d05070302061501050714010b060c010603110111120c070306060618061412091603031d010302030106080c1317031210060906050d0b0901030b041406 75
    0x5002d01c04070301c0510b4144000382c546110700e1405121502908086030602c000d5910a03008503102007410824150140480396010003111208202e0542200010b41a400741e40300292012440b4a008040304901354810600708500414040d1140c04440b05107010305150b00045810244d2511000d101d940100840450014041e01500146c4607500070a00150414007240c96031b07220709030300000401d00328400c0201800e440d80d1074900c1c044003402d900c07100f55501e130301020400c001d907681e2200c0100710b2010303500c0085042112540a481710348486140c000403024116080b10454400010150004d41d4000d441716602ca1400e0756290180055040380824800c440101c0d0145000507225100308000303003c0c4140c106084a103c40d100d81d120004e0550f403c4490350107030b100050141951007000c1016520a00c4211501481d904001005000791032510840040c8076022440f000b4511068100e401910300140001c1c029687d03070300f081800800280d905481419201131500100b25010a040d4880c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394058642 1250 394057392 394057403
    0xd0603052109120a0215070303050714041202041d0c091f0306090203100504030503060a0503010207120e13020a090303030518060105010f2001020301050a0b070b0406051021110a03 79
    0x103000c0342c1028030400c420071200304566401881c00d0000180e85980000120260443c0c1d06900c6032214503001e0704466010f86004107001d06090000d0072900b8540c11907080c2e50034500c68420104551021802400d0003149004d40324a000d4005134507074600003441780303111100701c6030714002e5201ca0310b1200c0201c00418840b60704100d01038040c0007240c01a00b08603440c601c05021900300d100000700f207a0803a001590110b00142001060009518105110744040c19049000b1441d2000356a038070024030b040c0b10080e40500400d03042440d0681d0707a0305155040800b4082c010b555420300340c1001464040540030850109140c10081011b8035802c0034006800d4140400034042d5034240310055985014811142c0c0811a84503a0b00030000c00405000f526130170700038000744c1c6950400781048520405034008680c45c110a01007500450b02c4924255000764004c2c0000035103440340e011503c04d8080c0c03500700c40211103401d140c83c48170000c641007400381c030360140e00c0b00c80301d00101e0000c011400c115444080c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394059892 1250 394058642 394058647
    0x30c015f091c2a0f0f030b06010302070503040303120f091112010f061706060102011e02090609040908070b060f06090f0612010e0106030c020d1d04060306020d06030521 74
    0x16642407010408040402540014040512568501007100c0340c0c1c1082c40e8100d80c4140f100d6810103100c9081601511031290707450311407414aa1800e810041c00d2002070030491118000c26080c1e40240c0c1120800e0360800160b990300c90b12424050521244428551031007803038103a98245024152080c40d008039884500000403281c000204401200c000810440c155a18065100c05a10728417903100200b00030303812040004010782a150406d20010912410741e4100003059804541c4a80040202a40002e0044c0c5032070000300810329900802e501550014640600c600c00e110303100c400703080f20610aa04800e06581c42d8010b10034440501600a50070100620152244d031405000403042100007601c0203040003c090320a040c290003c4c0d121040540d081401031140d15854094807101105500080c09007541d0042c000b0509000e03032405c0c200100f0890a6402103980e103802020040d50170000554a82c2114010302005201c039200444407841203103e09203d1442c00915205800c40e118400c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394061142 1250 394059892 394059907
    0x41121010f211b18050906040b0403080408120103080d050a0b032e0501060e0306070915051c0f0501080705030a020a090203090f06010e040c050f030c015f 68
    0x6405080b81c2110800041c00820b0801050056464014424020040c4040d00e0101c6900c044a03030192210303a8681190040001080400d400b60b134000d54189061441c075aa2820185581d0050f1900384030851070000000051117140d0010701142588110104082d44030103409030121260005582e03010f4000340b00c010b822904070090304124a800240c00b10001e690506440d0454500743c0084010170020308032030745281000c02601d0b43c05100c0d401d15225080c148109220300300c012030f403070320100b050000d09000c1c0d6204181035a0542c004005044c410b0b40300680c0c105d4050b00742400340c2e0543d0321580a0004003031500007240d200090300a00401081030a1a006a02a40c0001c00d40707950b52042d00f41550110b0002c201c028000c4c01c420180004a05042c03820071284802a40281d101d20341102c98011139690105010501b5913003420071003003000c00322100740e00d00360303031082440400c5494038005d200140c0b03c04071440700200841110700200301500200300406082808042064a040c032501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394062392 1250 394061142 394061189
    0x7091e0e0919050a0303061a0306060306011209030c050d02031e031b030702070302041a0f0d050c0301090309030221030d0207210302090316050d060902041121010f 72
    0x15004260740c0190380d001e80c0c1c1c12400c40d000004426084515501221030203040c5a451310032400600340310382d040404010131102600300341c04080c181d076100309400800b041041e8022603031070100d4908880c0500800600d8180640034070180c610a94141c040c0c2503100c05901c0c4084110b50740080d511186001040d13240c00c0004d10364000030030503001c6d85030031055598290b01d45006548114900d03130040c2605030551040c00141e651010841c80c100510134481d05041d034800180c1000c210342a1034100c00741c17102c0e040c1140341a240b43d201c1c82d0194a00614201450b40c040685030079039000392403103d219508890b1400340301c540600189921382050001414000c25a00140080c80c040d2042c83d0103401180100340f520b46120b40f250340401e600007105040c508050000029009804111014444c0b418010a8031610541c1000301015907841d4103408550380d40c1c6c0404481c80c4143d00b4651120188009107a00154a00301c246161903070b13500000c0d0a900c405458400d40344a03840314201d850641256 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394063642 1250 394062392 394062419
    0x50d0b0604031707021807230c0307050f07060e0a060c0f02100323091c051c050405150402030d052203050a02091303050d0c11010e1606030501050f0f010c061407091e 73
    0x4d08c80c03002001c228030303e00b20718208003824030a80200043d041da981d0385e0107014500000b5900c04801c0c004404d0305c429845d511500c0c01000c90f13020f4141844034000038a0080400c032500f52000303501074200c1c2c540e030030101e0781a80b0a0200407069520030241d401c900a41001c00d08040711880754035400b98581010700000c451030b440304441c6030f08081d81000c40a6801104208041003c0a44150b5800c100000c2c00400c110f02c03002c18000d4410b03d102d0341030903004a41c551011088040171320800103004d0b2b400b000c40000034008407280c6414071800b55203a1600c07586400520300d06912803802200410394a4851114404c14581d0607107900d1315109a11a840002c3d1040303407807140520500b001e1510a0820a0080b035042e1800e21000d08050200703107002c504c2c41140c81e0000000c1525100042c455034840300048803410408880308003041004000490746505089002040d06040c45151900114060266401908035440300080b440e11401070b05000f0700101100b050041c0d9184041042e8100e8100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394064748 1106 394063642 394063697
    0x51b0304031403070c020a030b0403080603060f010905040317041a09030f07060e030405190807090c081f2111010807050d0b0604031707021807 63
    0x14018149282406420041d00d800004070b4040303405a045e00c00e41560060210305655180d150200e0400420384085003c40c1260000c2080d0b8034000c21700e14410380d125941c4801030f80c42c01d81980090b0002030010b40512000300c20145801c4030800d880c134803490007010704c2ea80c00c80690011181014000b0324052030394005003d8410324082501c00c450341d450704010049023035980680c1c001e046204a03441558403ea0018000d0501801c24500404840302032081d12982030b514650802039419400545001815000018030302403c0d80f003492144142d0b140c0441c0c0713110340b036010034101c1c0d6079445c40f44120000c104117413504100101c41d110071101c3e800c1c038080c42d45040043e00900a40644e01e9100d4036140c8030001c04802c1e86817001590001d5800076150703420704110748000ca1031580000f40603405602e4240d404e40320707440341c1000c05005a03015620001c81902801241c00740c400c0350350 = true := by decide +kernel

theorem cover : BRFrame.Cov 393884892 394064748 := by
  have h0 := BRFrame.cov_init 393884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 393884892 ≤ n) (h2 : n < 394064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
