-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0985
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:39:24.422745+00:00
-- url     : https://prove2.me/submissions/7ed352af-b817-46a3-afd3-76d7ea6e1517

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176978417 ≤ n < 177158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176979667 1250 176978417 176978419
    0xf05041a041d10151e090f2301090b030a02030601170405011e0501080a112808012f090a030212010b0a1406090907090801050103080403030e03070f0512010b 69
    0x390356140c15240c45140140743c0300c1c110311207030342a001d521140c00109415001c001030002c2007401c0c40c0f120b001d86190110200380c94440c80c0c9988031555900525150502590141074001c81c4402d8801001c0f0042d13640410341e500071301b01080c080d454506134101c5840006e201e54021503011020520aa2040c2c055901c101c4000759105560b00301401c056000700001e092882401d014010424440f401501a0604a034074000c0a80302100164507640e01510403882401e60206000e031440b4026920007000a0f4410f5101c44400031003400c000c801402c50f000728414070021028101900c045800c21072002803501c620b040c140c0d4840e034491002c05c54040c42600000e52001d0411450103400c0340545c49041011412035800b405241c7d10412808100450140960001000c02c61402c544c10704080301c54000d00e1525116160703ea445041900319042a082240c11800015040041c942e103c410404052801c42c054120903144c03450740c09040b141445200d0040200100c443c1c0d09442c29407042515400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176980917 1250 176979667 176979689
    0x1902030f0a031e0e0c0f0f04020307030615020a0503090f0402121f0e060f01270602030706110307090303030f1e06050a0609031e020d050d0801030308070f05041a04 72
    0x30003000060042d00141100200c0d07040d0940789400c00002c1802040c114600134405080182c003010148020403505800c40c0b500b10780c2051103d9000c0c3c68500c004c500c5a10613980c002102e50034181d800c22052414104003003150322807502180481c40210489562420849000615482800c0480d029004840f0b00c01c080c956070404000340303481c44002c072510710f60194000942064443c0e2002c40240b80660700d2a800c090880401280755000380e802c0759044001c03200c0b0440711039604041400510054200c40010f80010070441c003008594042d18140d1150098181d05518003500020024a003a10000d000c05440e0250007903603071105e5104d00c40305c2090140312032a210015291501800a502c101400b55420410008050b4400d20240b03059a600c9038454604c14a00242c040301c8200c01c441c2a40c2c001c00a01805000a5040160081250b21502c0c0d004d400c0d895410090900c2c207000304a0001c0c0030070030606803641035103c0111400d50713080d94680d81000090f102055583d0045400181c01d0038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176982167 1250 176980917 176980927
    0x13020a0902030a052205060c0d1401060f030507030b031c210603021002030702030a060f020909010e09070602070b040e0a0608011e0506040b06030606070f1502121b1902030f 76
    0x3c07407604213a1244800701040354680c44e022046040c0f5015201c40600550402c0e0040354031900080000c002003068640c01141144c0304692000420000780d0081c400b0502c0301c008440c0064041c010194041e0f05802d00b04a00125200400d40b5003001c0c11040980c03440484020030b04c10b0140e05140c6200a401c0b05040340403200a40749001840700f400203a00c103052015a0b0711156100000711210158094050078400d603196950381d000d0705544200080c0e458007408152407544540d000d103402410000c5c400c032001d00303000b0300c3e10381400d04640100086403c580e00078030012000204580441d214001020b501e50f0b0340d400000c0051843d038008240030350a044100701008400e0607035180e18003101d80c0c100505c1d1a40b00c2000700702d0b02c6400449401407011710028555260082c064102507020b84403801e60140e4555070301d602035009407500742d00c8a9000c00e00840c40103042000030b0384010b04a1000420003500340c40041c00c0d0003a181c20101c201781103900452281c2c424002d0382c02c0514040640c54541d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176983417 1250 176982167 176982181
    0x20607140613051002040b12040807020904060c1b0201090611030d180c0e071d0f04050c0c070906180b2e140901090605090d0b190e0a080313020a090203 67
    0xb5160746000e880610a03090380341900002d80c0301302d8085a1449a440f480d1900302051480b2042c4020001c0d11b42420074000b050240e1121169140700382e02c103c2000515411204000d4030300e942d031200c03044000c20b0903182c00340107036040440b0740155031641c18054640c00307035032105520318401c90100300c40407402e0050801181800d851400c10080c0f0500e0220441501c5100780e01d018030040310f030107000030080114555151344462010850039405020341c107070518a24046800c0e135600f500e039800303a0000001c0b4450011000e0008030b001d801c504006001f2180b070110140b5982090854484240342d40d550b19030581e0340d40310010900022203c0e40d0110b00c00b05074aa0340c1c50b07016041c2c001c0000c9081c547c6003c00503d441d108580610341c05841e0a60058240700e000c640541281c0d81107a0410702050310b120218510b400c3c00c07441030a5001880d034001307441c40ea1070010740c0c0b2100da20341310540c071901412000a0700d503000c0d04d610200d901071021220900d8000a0625000c95020b9104944000180300d14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176984667 1250 176983417 176983441
    0x7050a06090b160c0305160b09060106020d05070203030301050405090304080d03020c1618050a0e1e011506080a0e1009050631060509030408010c02100b0a030f0206071406 75
    0xb4018402c94800d9940d0120702840d01e052440000300061a000c89540002d005c0c40113070207000e0704900c0c801814007441d604c7d00c1030781300141c403107400951144004014040d410042d00c03221010300d2928034240f080550201e0380d00c0c0018050716118581b62400a00082c00070000d40b0001c2c00000c0c00c5a450964498016009600000b0044502d00408807501c4810650a6203103007142c12418401034512100c0c09070742d004020240014071525111455003c50002c10000d861043d000c0c1d401c4010070010b04500d0b18215400d000f062200c00c8542d0b8020454035800805442e8804100c42002c20120403841c03160b03041503600d80c01d0101d21840c03c01e041081c04000551248206001003c80c681c484030315904644d0a012500d03000780c81c10380c00300710f540050b045410141d0030906d501d04880c20039440b100c00d02e00307540941945000680c4580070480b441c001350300462401140540d8015074441c20b64544041c4c41601d050040d01a0000050080401c4068440a2486442d8809984c10340c1041250508 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176985917 1250 176984667 176984681
    0x90a0b07170a09020121090b091e0105070e010c080c030403030905040b18071b140d08010e090a021017090105012619050a1205030117010b030703020405060607050a06 73
    0x1105410401c00220b00101610604000365016114108031100c0b0000754110340113032030030b16600280c076048000c0001c0c000200b824060b4400c64040c00750201071280003010020f00d01c0c2c0c82400c0703a04103420320900c15006807144810802c00e1910707141088139801c200c2d007584501c50003c0780d03034400018004145940202c00c0403d1352000c031000c1c031043e6519000c1207001c62042c0c00f0030013100b2010001c120290f001d50061880002030341c600d0303083d510040e120280c07524941d580304210b540041014950880d0300c0008580981301440e104401800d1049040d40d84070120700000f40100300c46100d270b442290151900c10341102c034142070b500407490065a0355000e40000e220300e5a1020800d02105202c0d648103500e9040c0e8074090005000500b200100c02c50180201901920940141000b03d004900215030b815072650031501d03401e54039494142810303854529100c41f941c199140007440801954042032517011a50110b501040f0b5454290008810b445156401020362280714800810041c0030b80040f8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176987167 1250 176985917 176985947
    0x1206060904170c030a0f1116140a0f09021207020607080118020d021801030c02010207020d0210090305060f06010e0a0602031b03090d0f020406090603021023030708090d050c0c09090a0b07 82
    0x87d41500802519640c1c0c85403441c603028072101040f01400141d41903072818642440092820042c96601d1064851034804c941002d091903400299958500c802406081d401c20713200d01c0201981c0c42c200d003006025030b1060160540d440b001603100d00c000704258041e00d0380b0b00c484400443d958000c40081105404003880c5142c0882e04041c0c00120700750040c42507820264000d0108800d40050707900700204007584000043c280000800b02001140d801c004941c8188100096043c1d1030506800140201c200c80c20543c3c859140c01e802031165035804010742c9e030401100f856201c9000c0f40e00c0c0b4030383d056006849032280c210000700c0004081c0202000000d01c16802a101001081e0301c80c5a682d040c2c1d032150102075007080f0700d071450f0744845100d0200c40d0002c20f0700480c40200d0280031028950700354015100d420000e001801845104070041c800c80410500314102149840800303000c580e140e14080000074861b48604c0c002581d084030034402040c0880d0700420084482c90250b1000c1c085544020ba00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176988417 1250 176987167 176987177
    0x509030304230d030f0212100306060905130f030e101724090901090b0f01030209070c2003030d020403060c0f020304030b06090406020c0601141206060904170c030a0f 73
    0x103000c1d85104400c0b0700055805070805040c20194404080e805440040142001945c1c200410342040c040c2d401c440d4061301e404080d080700b081c91401c001c1d01380c820307070b800500c40507103031005011090719101d85200b441030b4400618445040907080c142c41d48405550305a400c80103100907031290750b902080207181300e58005400c0310700352207549000a103400d80c882074600e051801100c6003050318044001c01e81c0800d846d00007040a800315550361601d81d000351111454586242c00500071490840c085c9540492286000088005144c4500d96482303059044102000e0301258042c6a0751814811141e460101000955640390b49180400040000e80a810005000f00300c038403040d00d20100032907003107039008502c1c0f004940b01ca000b000305500340a8803ca07100380d8200806285810144901d50003854201c191704845a4000203210b1000c41c1d041c8818015081401002482d54030281d0380c84d0095084004081c05031380560403d01c46206040782a503591001044032124142c1c48040c0705090310300740da10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176989667 1250 176988417 176988443
    0x106053106033e0c07150302070c06020c0a0e060d02061b01140103050607050310050d0f0605060103020f0712030b06070c03300e01020309060d060e10050a03060506040605040509030304 81
    0x3e840d00c0c914075072182100c4040302d4a05040e8140c40e90303000c0d040040b01e80c01a503002d01d668207907001ea03090307501c0c402c980443c0e0003044600c00c1c01540e0352541e008000780c1c00034002202004001841500303141c010301104003080b1000c12920740720751041c411030581c042e203600d9803000c0410411050011428044601c1e40c02d004109060350120a05a4100c0e43e205c0010720264890a6080d44c003900028584503000301d60f5003001545580324007406188138080e9115448151003400d040d003d0b904010f08113410300d4010055100c40c7c00850084a161036048603450b00205604c2a084001d441421f0100380d11110114022040c401c0400c08e5000300d910400421441030682c0452680f10446880d14407244002440c560400314025041d00660744414410740b0f20388100740300001e1181c7c200a51600310540c2d106418001803294501c610f40000d842441746600606d0f0a0000700d04901ca0f001c000d00e059250808100651500c4d0400d401030440144107202038a41422001e540360400c4400340e034189601a2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176990917 1250 176989667 176989721
    0x1060306090c09020f180118030f050f06130f1115030a1b0e010e03100606020c03070b07020a05060d06030501180b070903020102120c0a06020c01091a010605310603 72
    0x108640711751003031075038a5003050064a99070303204440d1200b1142c144030005066000a10360b244489001d90311510703201d03003980300c00d003841e91030600340b0800d9603d5a0300c03001c1408006404080910302031a403008511001a808c0c2c0f8084110a04041c409900074540e14490a400c03080c50707007c5c0d440356200e6501040307598a10400c81010011200091000c0748003210704d8172642d442510040c0341e20001600300da6104182c120302030101c2e05180d218400603088031240d00035601d0203002d0b500041807942e08442c00c00405800050101400340b203800d03c2600000b9440d1951f61b003640002c002150024020004807280040b03810b11301004840803a900703048400000c285900894012080c0d80c1c043e40204001078800c000715030305901c50f09400c6114030a8241c1c0b0703000240d60380018441c02944c1000440c101140749401d1059403c044450564650000014000c1d42c1d4081e043c2c82009080b03149182c1d80c0c0040c0d4a009006c1c0300458011b04140c00c0e00800443c1c525015003004201c081c601c40d6103445420840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176992167 1250 176990917 176990921
    0x2040b131e0b0301170a1202031e070c271104090b040e060406021806071406070f0f0807050412030f08010f030215030c160b0103051204081e01020c01060306090c09 72
    0x20140164407031050006120080310005402450341e1481c08882d0f0946d0251564101c043c4030410000050b80006403c2d0282c0f00c0340124080360301d401d40704e458202139041d515050020160f000e0b0541101228001846031081403150300c0400403502c504101c4100001c03c03407160355000c2c1c0240786c143d0b410701e880080141018400c003181110194087c1c0110703211556200080c0d40403090b100c000380c40503039821400d590356034010b01d60544203025141a018152a400e420460300414103028013102449403154141c00000c0c0e05402c1c2d02030700d007c2c003d950700c0e40d40664442c0102d81003401c400c829440e0140805400c007001c650305071071503110070600c0c0e079071002e41c4a013845660000a4001c4c0c10320484101645c0c2a001464004012070001c6040c2041c0182a400038081d00000b80e070030480c050b004100b031080510100c584400e41e041040d241505050134103175035903200c1030b41d0114030320704501580304c80000398140d43d80904100c009102990f92030807d400904a54441910901c600081c00190f4045074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176993417 1250 176992167 176992169
    0xc0603020705161206050403090b1308060906040201080f2706060306010b0a0203070206091503040f11011e050a030e06090703061802010e0d110904060903080906091e0102040b131e 79
    0x307401804044a21031703407402d0103448050301c2103041c0501e2036404a00c01300e980000c1c0c08a082030f000f407841c4041c036101c400e030300c1c000d4050f00c50348050f080102031102503640181001d80c4000014140180c5859061440d40d01090091b01c0e10050404d00342c44520002e00491501d002c0c0c1c2c400c50484250366280c1513440305920410f618400942d10400010005050203009400d8504000382101e0052075031a100a2255208842c04c55a9008118001c001c00c071b0500380c0c80382c00030420701e00646c8541d500c3c110044c1c0320100207a02003d0000110300d00040b00c3c1700313802102c68100104180c8041d4109400d00395580d42c0680401c60702a401e2a841601640c100b480c0d0010080e01607503030102d903c001100348640908203c0c1c00f601d29590021608540d1b0301e8a00a4500644c07103004001000c0c4949d0030001c0100c0d801505000c502d030440010f120400100241c00c1141d00d41100c4480500c0b80d48030381907402446140c0c407040003410086910b400b140310a850001c101c545070306580e1100148160444819489 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176994667 1250 176993417 176993429
    0x121e150a14010e1c0c0902120705160c08061009050c0301062f07180912030f0b04050c040608070f0507030f11010203040b0402120c090f070207030c060302070516 71
    0x10100401500515119110700c484040c14440510328068010403101600408000d00c0340703c1000141c01013040c542c0d200c400805912404508002c40f250f080e0301d40344000780001c0100400499041a12025003000c00495a441040841095613a504042d2035003c1190603000310140024001200c5140d80601c61259115018052550307003080c109440341d42047c0000490011404410002c0d80703804e04400b460385000400401601b0311348898008017894441c42628094141020400098264101014101030506021440344641d00f07414000741480c440c1c1a0780a0705100905c64000c806800034410740da83d6030b81328411503440c040c0c1510f4074480c021100002910801c55070007c0380c403807500050a00b849140c140c000e905034040c207a0a90b0825182601c0701c2c0c8586050004514200103a1072103048208007503e400c0c1e081200050030140002c0000041c03500b440b00203200e243c428810135001d03542c403903000c541141e140c0800030002e41103140d04441c103216250307070b8035030f404c0f080502e80d012501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176995917 1250 176994667 176994679
    0x10e0303091903080a081902040803030a050a0e030a0509040b0105040e0103080702031f1508120a110a020d1202060109050f06010302071b12020f04050723121e15 71
    0x4119002e002c03061100d01e06240d44410046404000510040010240b032001640d514800d41420483c84039101030f001003070744440344100700812401101000707495001c100040300060564030100c0140150100c104140002d000018011030810b8200c0081e00e2205d1056404010310103e190055906200341c1c05000b01040604004200160516008028081c805030954001d2544803004028035101c12082140e200d031540c100107180b85040d2040d0004025520042440032030b01e41455a43d48682ca9452042100400400c0241141084186e45d86603010b0036a1083c450107041491101020442100040c000c400c00062920300c0c7d80202030149100d982805000d454a40040d0000d61008d00200c486803464240540103180254000008080d403e1032404c4925462040219040d0f204020710712451501c014007a85590050171841b007c444e01990080450a825542d4001c0c020346807041c3c1d00800080410bd5505141010345111000d03031210b61201b915100400c1d0301c1c0d044102c3c9004e81190b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176997167 1250 176995917 176995927
    0xf0614040b0916021203010306050405060f040c1701090c1d09061605030a0e072402010519020a051905041406070201080c0d0e0307080a0906091508040c050429010e0303 74
    0x41d141551006025144e004968010050400900503074009a03c1a142d00d940c800030401404410b00026510601c02d0783d2903410741c0b40c50b680c1e400800d042030141c10405459040105a40c4800b54003201c2c4554202c41c0c0e20100c0707035a6840803e403c8100c0e542500710b5542d0000815a07820001502500891400c18030708681c402c1404200d03900e400040400da03405807200380f022306003407061025001809108010b100038034201407181c045098040b000c002160314200c108802259139211912040640d4007000da03072524030481c116901d000ea01d22320040b0300384d840100088540c01c403006108803540090b031000000809410015140148007002c0d000c903000c50000340b1044018401003415640e08040000e03403480c8600f4541c6150054a0308030388032800011184d020319041b4540e140180410310700780010754100020415044c1070582040180301d950340202e4104400f0200b5400649406002000313000305800403030b00000429052224202031030b2400719070551052161211088020b002140380c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176998417 1250 176997167 176997181
    0x403050d0305040204060e0702010509010b0303071106030a11030112050c0904020108072a050307060609060303020a0b0405030d0c02100c030b011704170c06070905030c210a05010f0614040b09 84
    0x140000400132a0b00640e02c03540462480724507a08280589400c0c2c1c000942460310141e11f82c00c54003a0012944071381d0090101d4400188001f280000c014000e42e1026220748880351000d010b0040041c0d0403000304408000858050070382d22a203010f41e03014208586482e002c00003031003070b0b003e0180c0d00070303001903440000101c9581c003a0115078482c1c007100201a80381d4103544c034403040f0901990707021290b640000401909020090040034050000f860040181038076650740a59541e0280d54002d00002d00c503c009018004140243d50582e520103c0034020350ba07200c0002034564035818081c05a0f2450109509450340c82481039990366241a104c3c4040001070718021484401c0c01081214085025002a0040e030200d0010b4882c003003214000741103d04101a029003048003d81103607000f64002d0b1803001d00d55032141005d1894600c6c14000300110800c031030510303080104806000c0c0c415030808815180c50001a4401c0080350101204110842d0a00e070401c000d80302d40c8010340313601808402c040341c2d803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176999667 1250 176998417 176998421
    0x31a161d0a080102041412191205190c05150705180d0807030c0c090216080a02010b030601030320010e030f130f0e04060e010c091505070510020301090b060403050d03 73
    0x440e08014902103045555440c00d50030780e0321503000348400b080004042c0380181044507480c011201c8000c0038020381940c0035910850802904005400685c190000010b603e0084048401d112180e00000c0b601400802000d4410041d40501302c1e418481e10541d600103601c125055800780d082907499604d80b0b1544210803003508154030141e03a201418603001e0000440040003010b1080c400d481e070b41d2010724030b03040c80c1034620708590041410303071300410a00300c42c00d000446111b642a840f0746e409445110400c0e040703006040c5540e006415101e003000100505130443c82d4100010015031300c601d894841c800b0030030300360780a00840000c5517000388030389600c0f00e0940307014108004180c110f08640961310f61103000245010b0744000c000161020a110070f01c510307800f60381c40101c503c00c02880003c0c814031006001e00d8480c4210040008400f81d101c08143c803d4044544107504101101c0d010000c4003c41c0c002540203104000d9080c1c50190140154100842030b101105e07000000740c00d45c074040c8001940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177000917 1250 176999667 176999717
    0x61603080901060b03010807300813030203011805010c0908060f0403030b1f090b0702011d0f1509041a0d0803071b080c010c1d2101020301031a16 64
    0x441d075500c640b0040344000e5580f010714000d011400081000c03624100b00180001c3d4010705640460b003045c60300740c050181440c4030f1201c0e81c2e40914030960347c242941140c1504505504025815401c1c843c80360411042540c00c111040e000300000c102104103104217844181c040e2144a0158000384001039019201c0b640c101d0b03001c0d018dc100400d5030401040024500140c05c8103400c44a002031403104030071940150f006000d0162560114a0248949c00103440c0c00c101d006601c0c04600000c0b035144136600e0305075410301d0a200180500592800e541401605074011041e076500551401780c4107415040082e0480361495400f90410031802c03040e4880c13002a601c024042c105000128016002064002c2d0002c84011300030740c1a142c580c50105005400d42c1e40703403c1298104400900801e155011524800150300fa007110040c4409070b90412003044200e2640c4650070b031f544044000424456840f41035040c22460030031840c2e0350740d1140d440c02010102c0b100103100207001e41d0300d000b84071004854484 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177002167 1250 177000917 177000931
    0x20a120f0e070f030309060906120207140d0c1103281118012904120302120706020c070602030c100902030c040f0e010c020f031608040902070b06090606160308 70
    0x810340d5500c103600340c2c0c5010410f03840f460030715183c1c2c0c1040090642c03000c10b0002a28041c900316410519142006202c5140c0d80c0d807040e40325034000780c0c890130842044d2040b43c900c0c0b03030002595040d160021010f012031004000540d441e400204117291946408586d201800e054158501643c200480d0000740000c440101140c0044d0b000c02401c0b2180e0302e80401c104a800348442403422903041a0301c115001d080002c8500d1841c0450512022420a51043d1000d03503500c040000c41100290070104d00c2c1c03006550340e01c13070886000541141440744ea500102000148281140e0320036035a10001c9a03a44030781c5103041032a402640c00d410410360745030801c0d40c04600081c00c4034040104040000c0c200c500c0c081c10000c00300da03204115080017a0a02503195268124000340c045050103801c0d0130344910691030040001c06612030604200700c4d60300140c1b0007038010004215192803452800030b00e44e20090301c0c11031280c410000014038a1a00004442212600740c60840c09810741ea64280d5108501609a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177003417 1250 177002167 177002171
    0x18050a09050c0705070b0d0c03090302060a1112090321070e1e0306090706020714010903060f021e030901140c0901030b01051b0106050a0501030c140304050106030212010504060f020a120f 82
    0xf01c1c0450410400c48028000b50b071141a44d48024a4200d0100c2c0c21502c1740d082490b04060403180800d8010460940c0311000f0000860780c60f0109680c0c0d20188514800c14005e24509006e11001580c0000648540484007010b4010b4110101c0c8008030034000321451400503815110035501414484c000e08403022034802c90a44404041c80040d04201048030b48010300d600403031042090f00e034104a100001d003011040c40d40034079061030009114001c980800f410303464803401d8105507840340b641200c08040c10100c030706103800308001170b49145a0040c1c071020025820400381c060301204085580d80038200501d1514a0402c80b400150003401030540810305200c0148900407a81201e00940038242104100006415040c1420068a5501608442d041618100303a80c8807c681140380e0b4010701c5110b40407151207948500d017082c00341030b154000940040c0640941d9074048015040f05001c0c611940040c0019000c01e00c41d14100c1c007400f01848009259020a80c00311445513020103003004c1d440d040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177004667 1250 177003417 177003427
    0x120d051005060714010908040909020f040c05090108061c0302030403050c0919050a1508070323060105010c0f060903111b01140a12051303020d0c020a0b09011e08010618050a09050c 79
    0x50384147d60003e074000d050032030701e4a45c1d950842c41c154040c10001c0030101e804020350040c2010041a5000c1e810465060119620115040b5580e1220651403410149580342d030f0107402e803400a44a4205101c2102c032886031211a041514241e40e006d407155405600707040300302d205500c51401912000e811401901c0c2d03600d171201c0449050080c940c0203400e0050007084c25910310320300307200c1113455103242031056141d030401880c080e0800705400e07044074000d2a088602c445036042000c11060f8400780100480c2c40c0c24208400c16802c032040c2d001c40d542c3c031003d030342c0c7d40d1050384940240c4080d0b606140e40098944002c0c3e04a001081010704040101450110340300401010100c1c115041030f2107240003c1812a00d03c0b0400d1b90400c11241082c0d21490880c1282e41651b000c40c803292410b00840c50600008115080e250344078943d0800000001c0c0314048101c9001752015102610130f018070400240d004203803010712a0342907265401c48901a004001c80741c90131010900030400605500c0724844100300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177005917 1250 177004667 177004673
    0x81c050304061503120f0302070b0103170f03040303050402010809030306130c02031e0301090b060403050c09040305070803160809070b030a0b011b0605010501030b0a23030c03120d0510050607140109 87
    0x403e42000d03500c0b0700728001c00e0713084400015001c19002c550020406004210150000b17204900250440346d1010a200c071170320340c1c404000c18500030030851805000303011007048103041c0c0c141c206034043e50003a03c906401d0b8075450941a200d2000300e40d0160408200d08a005200384103038043c0f10f000d442441074a040500180305815904000d24002000040110052001200ca48911006150304803105c1d841d080c13460303842c161500c0f07210540c00d1003041000c0004051500800894040c56400902c00399240f4246880d86464200000c880b000150524000f80d024500001c00f502a80c0c43d410115041d07a845500507000b5100015a0340d04010741c408130700d01c040311001303603001c01c092041e1804a50356042000040c01c40d03105110091140f9074100c010003031401140020282421004072040c0e42c0e00102002c2441d04000700b91240e01481982c1c880b011500345403001e840c8400003250240450b45030403d00c0c84c510308280c09441d80c000e04c1001039500140948407001d6042c030f40403001207040390242d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177007167 1250 177005917 177005951
    0x2150624071703071b03020c060f0d060e060f22110d15050a0308090414010906090e01020705060106081009140403110a11040905030c190507081c05030406 68
    0x12418036040e0004214201000060180002000c0808510b141035141100d40240030048456003400d501010040d8402494800d000101c0c220703c1c09450190303140c1034000ca1400c1d0358424100b6000892901c0d4012880901c21101c0a0141d0b03030003070113412888046800c0001d50b080080c90b918043c04e82c0c140b51513601446002c0d00e444c0c4827200180b540c8503000c02034480e065522041700410100031001050240d07588003111030099a4025052649951030840490300400f010714100803440d90b068000190f03440690800b10641306500418010070103401d030454280d0107821001406c0c0e4010310700611000740b15910360b6600c864000c200680956031030b00c0400c00c54000441d0f40990b21400d004100074550007080a020151906000306081c141c40d40740d0307460884000034118070a61b192024042802070804c241c0b506110800c09994581a140001034441882c00c0400c070340c140200040000c0900000c00c41c4c6040701d049094240b40e00300b92107400c8440e030f80014400c4030010b64914504080344029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177008417 1250 177007167 177007219
    0x9021c0b030d0e3717030a090303032c061006090503070303050c0a1a0f06010f12020c012003060411070506040213020d09050c0a08030c0717071a13050f01021506 71
    0x660180341c0f82418250172041100048a4800455104110428510303034000408000c0700d8043c0381c0066070600100140403914640c1602c1504412011800b03030000d10f000c05c24074000d80d004084078080942e40c07131081c1d9150392a031041c0760b850f170028034041012034011402080262000e2050383e0301c10402da42c0c2c3c004444000781c4441c0020b4010001c02011004c1c115240da00144242095814202408401003084200044066134142c000c1049000c01409404c40c541d1510324002038242c040014004425039003044418500c254141840110710051000c1100c6005800030040c04c40c4c2c4e039940d02400315842d095804410b180754200460401014144604c00358188103001410245001a00700013582095400c0250b454004012410300001c00251a800b00c0d40d140551002a06450140f5410041d0302d40c0107000c0b01300c178050008d401940750b60061800c1d04261001070603990300d03141480790070113141000c6800340c0e01c00001c01c48098442080d06501880080c5075801144a17048141151598 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177009667 1250 177008417 177008509
    0x102003120a0506030604063b0105010501141e040302040203010b1b190b25020a030f1b03120b04020d090c0e040210080a0609021c0b030d0e 61
    0x204a2600c403100031614141c105940384024030032802c00e10002030710340c403000c0c0c0b0090000e0785d00d0701e41e00300380403000741d07108c0c8803003020300903214030700d115140003010f01c1a0a00f0000040d46004000715032580108049450389195052a50904040054103504c0c000704014070407011406102c0040165a0b03800110302802ca0030803141e460ba15260450b001043c1080042501500480e4201442c011034100d8a41d034560081c855061a481e0400341541d014041180d140016001d2689071003d60703000942c02000078402c0e6a415900c400ca00000c440030a400440c01800419401100f40400d100305034582c083d00703000f00005004411790340050201d1748101650307620a40c80b81040b03414019441341400041c181d42d8100011850590300103010154331480b4401032000b00e42c00714100440690002001d805103040447d5201c101e003800d0212286c4d00c0700e00c07021207800d280c007604c071307034140410607001c90382c020f480354842580780340d041000410910a444c2c5030004c0480100598184005140ca00121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177010917 1250 177009667 177009673
    0xf13210201020c0d050c1309020d050717030408060f091014010f050d0203030307030504050a17031006030209090402060c010e030f030f06060301080c13092f010c0f021020 75
    0x21510019003804500326010780f2840c11080000042200818005002c41048a00108455421188100070080c0c0c181c0a5001074294a03030074104000051030005845138800071012002104002c65034030f2149010300c0d05943c120714042050f90b10000c4003c2e40102c021000c0e03403162041c0302154801c507050019401c1216004000400c100320040e0100006494240d0720060010f02c2500400e03501c1c03001800c2d0404060351400064180803052251941c040c2c1d00c0590b0a019044008014a00381c000342c42c11030b01408074090000d4494001c0c401c07507040c900094904003075540c1d69000c2104039040442003d201b55200ca503e204504d40a02c02020903000d002d40035034981c2000c42c0d038a4200c0400809060052504000600071000700203141d840c0302c43c0450312070019403c4410200007509031540c0052461191001d51407944002d1816015800c010010b21042e00305031400445540d06036203c06440c4a52881e1440050f0412545000c0d410003d41080705000200a10088041e4034403400c888d1560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177012167 1250 177010917 177010979
    0x90301021801180b180d150504030f0e09060112020f0a08090d110709020906071203050601020f16030b100f18050703140f070903020402030c0a1103040b0f13 69
    0x50f07008003010072402940c0c00d42005607030504181120a01c2030400015050a4031940c49603070340d0f9010351105c000c03540401051041c0030302803001c4000e401c0c1a00c1c00c602207400b82c0200302c0e045204800e445882800284421601e07200c610040d03c04419950b0310500447d02045001007030403021004001d000b03225038a140c258540003078030300c0c200840146036104101c1420071515400c6000554001515140580180e44050010000d44c16208000300107100a01726041c84180d5038060b0b00c40c3d44122070a0b025914005200c046107900c0c1c124903200d2441c0c0c80843e0030140041404c0e420030941c03100704c190415030340c81d0702c5403150741683d0301951110141c00d18000382c5140820040c0100c9070442101d041c00e00000000c110019003046000303012408207a00200014581c41c400c280c1807004503005401150f4908028001d035038a640b01314150390109045c50b0740000050340010468084502002c10b050602c44800e08194180d803200380481c8081712032300390100d41d9981241140580400b661a0785801d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177013417 1250 177012167 177012169
    0x204231302031509070501080a02040f14040b030616030c03090c170f060c070206070602071709030c06070f02010807090f060801061407020a17010f14040c1208041a0903010218 77
    0x790f08a21005100000a081c003034000c0001400c1016188242400d000075940c020000d4002d0240ea849090201d1130b0400028041140c20b6400d00c500c1400d8500340840d408180600d0b940c0da406680d0101002152401c01003101e11075441014001024035004c10802c0b51b40d1a614217046868010070a603241485458590b060b04100b0003c411a1401c06005145024009540c032805000e0010717014a4002802404004190f4100d414141c0e2003445550300819103118010540c0214044138001d1040421204181c9070000903980d1866011002104644499004465590000d0001d200b4881522008503140380c0124144025040c03540e505082d03907140c00303801048110309010020f0007502c1048420050703141c56a0000c1981d0852105040010400f12a603006164200d202d290307203407502daa000401e000d6062070038000c50081f0003078101d00d80c0301c80780d90342d084d548108020600203003080204800d62030007224080c0b0001c12400c20341010a0303480072900307903400251115a000290301810f90a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177014667 1250 177013417 177013423
    0x51201080d0f02070608070f0c1a0a1503020a090207060e0f01020c150412210905030c060615030a050a0f020c010f1103091e100c0203040e07031503020423130203 71
    0x500b007424402042c0d8075142210150881c44080c018404000e4001006030b0039a0160041d04c2116510521140c40c000a00440d00120402a62060302d0a41801c0b202c01c513174042c0101340420b507030b0001c01c103e050515041e440b038025442020304032107140e20b490302d000a5182c2031002ca015444400000b6948403402c0300400c0c00d0060403441030b00c42c0b0482c00c080c400803e8040b482140c2c01d0304d0605014800c00100d00b074040114601d41000c80b040741c10440032104114010001d40b103601007407403c031034087d01d95108102840d40800604034005805100052801c2c00d00d80110341c00003502200003458418001d81d00b0b0582c2e0040100081a80d16150310805440c0c151003841249400032060714254145040b05940718030102191003564613002040c4034200c074060044035216046100c04200b001d0315114040c0d241e400c54440c40c6000c0103507900140c0c010f0f01900a0807094251404040041e0b41580e0130407004000304c0f10341000c1110304040202c00c3c0c1680040b80d901a000c240d01c0002c7c100740600c10585 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177015917 1250 177014667 177014687
    0x501021603080a060b0708070201020a14031209150c0f0d15080d02070e0a0e1603031107060507020d1e0c030606050a1e150516060b130e0703030e01051201080d 70
    0x601c03e244c5001005101401c00640303406903800840c49980388a0f50004074940340d43c200015029002d64219121540000070041c406041603105414250380d03000c00b8151540d0548122070f02ca480c41c00005424207105500600c2d2280303880b9065410a554010381e941114500b48951092000080c0244100d0008006440004103284000d000c0c460070040070b038103584ca000d070a0b03032811a110340000894400034007058581c5040c0003049607100303030380f4180106aa031840400400f140190380d000300b00c0da4440c0c811a400c1030380180c40480302050542e100300000e030641402c801c50007400d0364124001a070150f5204002d50044401150a40c01c00042100121680d8068202062001031360f44001140e2a1620229419001c6400c03683d80400000c0c1e51521402c504160300a4107d58440c080000e40c0d40aa000d00f01c0980d0428400f41035402c80c00201c031a5071400b60f2032075211020810000c2d1054003004504001807601a0600d202410a801c17110800c2c3c0041c19142c00c152040300d82076600c400c10b14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177017167 1250 177015917 177015931
    0x105070906030b0d0f110604180207020f03060c0405010c06140901061403161a04081606170618090115030b01030b060f0618010e090f090706050a0e0904020409050102160308 76
    0x800311002d552100f1aaa0b070001000740481000f00c500000c5e0b40e94881698001c000d802820f010b449c0c0d054010900961141c0d04c200d1041c02003000034003060400042107480b805500009529240c2403000648184001400450700d40d51a05400f0b0a501403200410340682c400c1000460014100381c0c106012100660031030340260301515961043d1021410448111500011001000202c0042c402d60038400c6801812685c0710b00910400861018040c20b000c0750801e40d5014511010120280c0c4108801c2c0c43c5164445d09549400e00821302c1c85e008550800c4003000009240101c0d40303000c4007803001030350064940920700e000410520210114499028404803a40300d07000c40d111002401038045d05841c40a400841c034910515640a55610125520010180c1c1d0701e900d44104c103007122600481e501c29242c0a101000100a8003540656801100c9601c4090400100d8400c0c00b03001c2e040107009030380c415150750351400803c10070b2004016544820030714500c1c404450070080c108400c090820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177018417 1250 177017167 177017179
    0xb041e0c03150603020705030405030106030311120708070b0907081e0c04060503030f030a090206030406020d0b1f0309030c02190e010602031617120a0506040c02060f0105060c0703050105070906030b 87
    0x42c9500d046941c1054080e1a40d5040041c2c9400207818081e00e903001d581c1107586c144d03280c49008018035800680c0b1094850400c2e003115039204800c42c941c40b85014481000b4203100f01130001e000001c1800010640c0030440c64222240503941c2e60b80c291405812240840c0c84251180701c40c84070b00c0040c4510300d0603803400e580c1801424980300210303503030780700701043e031401e102c004808240160040e410602085270010300b6140c80e820b050601c0c000070340c0b0003050007841a01e000d020740c6403070501034282c0c0b6058104014a50486140b604140d001e00b4030200201e00300301c600301c00d450043c1d8811070242c400f0b52120101d2001a404c1a091440c030b56410380140c030965000b84100c198080110f842d112040f503001e21004030700d08040c0c001c00418020110111b0740c0e482480200003468130b084e84618800d280c01c44051010760700c41030090761503620030740b9074020b400303a010010f1009050801c01046000d034024220303160142d680c0c4419003181c0d41507a4080008512400810400364036025907124140c0c00c07114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177019667 1250 177018417 177018431
    0x1306050a03060e01080a082d12060d11040b040e120a020f0f0304060e0a15110c0a03020a050d02030c09040b040c1505030604150906060c02130501080a080304060b041e0c03 75
    0x5120703901d001c50035000344000c20000d9070600103241e45c64655a05c07800311242103100310320348100c0740c030a800c080c54100030011942700107009031030180d400d60441a0880025030010b40c042051002500c142d00b500c542058a98000fa801d00d80c4c00c200c0c500b41441a5103c5984500c1c88420003424001c0c001034001041d401442030b00b9030ad03400481281c003101d00600303100410048101c0810116910760b40309031a0b84c4a150400071074550011103084013a105034080c0e41c03103640042d040009036442800040d40003555007078280607a0074031404480100c0d0009040701d254100c0d40300001d00046003200c00b211291080001d1000b0028080a050080e00d086080c0b028100880a4000c016000003400700f03100725160a240095280da0b140010041c001c03010051003010744455010b008070481a100300d00900b9103540c1340132040103921a0a0503161620007038415a10389446500c807580010b0825113440d6a03c40c0342000640e80c034841d04d55000a010528076406080d01c51a00448a0b5071915205050030482 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177020917 1250 177019667 177019679
    0x24020a03050a050901031d0a0b0106020105072102040929030307081204020a0503030c0124060804080708040503030d050a0e061b490b180c1306050a03060e01 69
    0x2a18030960b16482c0c403d4503580418012405031403ca40d01c4600914042c1d0040c05001e000700306080c1141c05481030600d141d91b101012401ca801c2103541c01e0010360340c468001c8a01c49084000b0f01c40c07100001c0050708082c0c036a840401256258140e16803601c00b14000100381400c3e00d20020071f000c0d0210302450403e0519190440381c1d204200c04440404c100e4400a0215038441d001400a0700000d07049a441d0501203000740d00804c1241031400c0034103820000307611280d46010741c10b001d4030b065560360b09040e01c0d140e907449180c4d00403000031100c0132400c1c80080b46689080014201c1d110003030f070000c1501c0c10086425002c4464401c010710303868010b001007242051032840c603016465000000c1f5655130041842a202c0c1100c451000344115603101403100202c40803090054082a074158000044420205440304845400d91150b0b04400741c03810540e40340340003880550384141e5100c0a54908580640c00da04c09032826003007803001c0f40f004200d0389820765151080d000908410300521140f07504000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177022167 1250 177020917 177020927
    0x130504020a0b09030f06040c2904030602030907080f030a0f0e0d0308070c08120f070518040f11070b0a0e0a0b0f07031b0c02011d010f0c020a0b0424020a03 68
    0xc02094080000010483d0031a24204070f000b116100c0c02056500f24107103884c01d005104164801e1312002102650f111116100e058180c40b103c080301d030032151400703240d5034408002e1f420060091000f4000c90304001811082440211a018600c602542d560110240d001d85488800a20706041101d81d81e42c4500341d454010a904d4080d0b0903041c501c2c800c0d641c1c200d00705c2d0006142e075001810b0070004268a8001d000b407160203801440e00d0310485200d43e83c1d15404640303078014020412007400799200d00c04903600700366110361003d581c0350f803010270a9a800074000d600c0c0c1d4005402180c91030103580c02c00c54005400e220f031410b1a010710000c6c00040b1f034561611000c06034068a05800a181c03003021030a854002d07880061b842007070006003804071181a0000e009010414002e90204403e9103c000300c0f80c159002400548405840b8181e5100e0000d01c102c58010482c04200d80110b1860b00c04500c000403100034100401c02e40910101d504254100f500c5007406501d070140655000032a00000283c0203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177023417 1250 177022167 177022169
    0x151c0e012912030d0f06171005040507121412090a030b070c020d0b07031b050d02130f030812070201091a100806010b07050114040302070e1b041203031821050c010e0a02130504020a 79
    0x2390000c295522182062400c00c441030b80009202240b45c0307800020055484000ca04071440c50041d6810000412800840c40c440d441c003895008000d940d0900c0050452200c4581095940c41c1c801042c04481d808240080140c0c1d8050b40d5107011402005001f6506000d013901881c9034000d48000111601c1003c1c2088c040c42c02c8038500300303402080200c122041501d201c802485c41100410b00c659503800c00c0d02080d4007029000c0206202480003804c1c46005010f45c00c41e299004047c2c60003c0035590021603c2e107005840d52102100d201c03000110847d0401c4070328080c041603e8520b1381d07140c0034503001d800c54080084800e000030340242048003080d0040743b001e088031000d40002469590390000035030020078603c914400c6c0c0703502080100d124113401e000c4e0403400c0e209031010441000e5a4025904000d11034000502e0101e444022250b4100c444e540c6904400b1181800350400000302c51850030b41d464641095400d910001e0301c1c4096146c141d5800605840a03141003025080c40d8001c902041c0c91 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177024667 1250 177023417 177023443
    0x703050d0f02032502091803030402010c0302010e0708390904050703060f051005060c10020a0309020d11040c1106040809151c0e012912030d0f0617 65
    0x30008a00207864000c0c412200b91110a0302c604013602c200b05040360780408a000d040e4010000900041c09880c18400c2111514031150011820750740e40340e0046807001011142101155214107c10000d40001c0001c0c1029100500160018103c494400b505060105156907050040041300951445c03d08880b050400b134166030340f41880d901c40c10103c4c504546a4001130000f1319201000781d01d40c0071544030fa0b020310124086840203990b02d50400204e8043d4008000840e0011411042604041e6005001c032241030704000ca2807103940d800242041281034401c2c0e906582d0741030102201c0c81e2510803025080d07030500341325854501181100340d40d00ca00502c010a031210008601c000c60350b841c4020b0a0307030f2444008017035032107100c25003104000790480000b2140c10700380b41c150b12104106008041240c0a1000b03020020b60b18170b4811900543d1810301550420b5600401100f8290240010500c007000d07400046071340807003c0040800c40d0440d50003810703040704c00490b0188620001c50002a07007a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177025917 1250 177024667 177024677
    0x20c0c090610050304110627010f0f0e010c11030a0f02130207050a0312090804080c040e03040506071506090203010e10081209040213051f0306050306040b010b0307020a08070f0203060601020703050d 87
    0x1a086e0110b6280c0c881c0c1f0318a004101d00c1d10060b03d07013602d8a98100c4034102c1081c0e8540801c45003600c4169030001600c1c440c031000c2409201d110126500c82c504100e00300e402401c030008030000920100b820700c9031a080030b50314026111611410740c108070005000418668604515045581d2549900c4060034003008041000c00b20444c140070305260405010107400c0450555581e82c0c2d90707220350756440c183c0c081501540c1080304200d9240030105c162000c8810150241e07180100590b02c079121b410402004460390340d500d035404904041c040c4042d40c0600b2200641c02454103200c140030036040c03241c7c0d000d450617038050592401e03505507000c107030b42030f00c0000d540242c0c44071001001100c88511a42115070000e85000010325500c0040010980e040c1107918100515507d640c24944c1303650003250054012485480108070341040d20b8029a80401d4610560b40c5c16061552400748607404080e068514079854205401507240c02d009054000c00e0900007071a0702d61460765010b4136a130020016005000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177027167 1250 177025917 177025943
    0x1306050a020c0a0f03021305100605130e040602030f0c090d02060a0c050a030203030105040e03130501231309110c06071b05070305100c0c0f0222020c0c090610050304 73
    0x241c001c110215100344002e08032000c07140c681c1e0821001c0c0c109440164420050f402d80304213070360300310b1150a014401c1582c00d41f400030f0915030b0640303042c3d0044d00c4a20b040300b070407880040c0c48818001d0050141e84140344c0581d403401d00c0b02e001d016800c005440c141d801d040030000d02c00c0703654488120405641d81030b14000c0e15100c110318103440b000303c02d0070042e00034003030072a512041580c04001141640c10481c0c08221000109001c1903a0b40122080d100645d001030702c042c0415801800c520190548610300b008601505401e0781406400c04030744800f00d4440c0b06d0080c020b1602c3d40c00798106d030b0002c205503141001d48143c049a03032200050100b0381400700c0e020b02064a4245012041c81c03183d000411030f2280c46e640c0c0b41c0f01e66640d080c5407503507110a00d041c15030749540d4803510030020340036000b001d440e10550913602000155184401801500d2a20800042c9802c6290010b84201c0718403c002d0305e9414004424802c42c81c00041046209008149886140ea500038041d00c3e0065007054151b0b40340c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177028417 1250 177027167 177027187
    0x121009060204030501051003140309011b26030402040c05030f0411040b2101050f040201080106030c02030d0504080a080f011208090a0b070c0911030106090303030b0a05060d0905060c130605 83
    0x20300c030b60b41014210f9400c0500b0401c01c00407111361001200e200350301c0070b50080c141044003134a0f809100c035854002086040040001034451146aa40c82d000f804c01c0b4014000e40c2000201403220070704101100c082c00701c02c000c04d615151007500080d40007400d056185103088858403400103c0108001d010440c501920307079150300c41c0d03448607400340c034003400686800740444c1c8034407501e91141540315441d60030100081c410741c1000c541c0c103006640c181c40c1e10103c0d90901005402800181504004510003448072501180b030302d00a50b8003ca0207129a56954080300300010304165000303085000c108001c4004015001031664855001900909956100d110181c001402e0708a558445404c52130b01103030074002e2001201301c03c0c045070144982080904460342e00c856590000f40f20f038000cc10064102080880c1c044e4000702050880200700c1c0303d10545800004200b134200b0340400081c55943d0700b48100b080010001e041e00880c64100a0f810b100d07154141030b030b07110002c0c003420040007004a030f84038072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177029667 1250 177028417 177028421
    0x60c160f0602030705040906080304050108061201150609030302101104090207020301020706020a05030603100608030702040f090b0a05100609030512090a030605010b070b010e04150c0504030b0405011a12100906 92
    0x5540d070300601c19950703410128401445504035010355a00a4036040f000a039045002003120110380f0180c5442903c0e03076514007001501c601c2d000701c06420b552111600c003075900c180b4600501074022522000805415424020301c0c0100410300e080c18140381c040c1704401c1d4036030401a01e04550042d140903030ba5000c240302007400782c01005801040d550011400e604065041030155100e0350080c0c2c11109200c0050880c042614190310815040e90030411000c0f0160525070801c1491855141c00032490700c50f00d07516110500001c1340d82003005640c41043c050008140c05084006045d00d00c1d041e0f070b04c80d086443d00341e04c0f0f203d400710460503032900007252400754455040c03000003990010003c004640c3e4803002404140c2c0109000c46151100c08000302e2400e02529009004941014150090350002502000204140034603201408401d03c0b0000c0015403054140c0c1c41a442240085005003400a4025590010101c1c841c400c100d0081040e812072400a584035036003806041c04104e1054900b00040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177030917 1250 177029667 177029693
    0x60e0609010c1b0e090f19030c1509240f09020303220503030d020403060501051e0f010234120b0403030c140a0e1009150311130f17060c16 61
    0x20010444104000c440c1001080e00712140c0114801c0c1c583c1094121a0545030501f942801030201d89200b01c44408140806800c9440000d001000115480c00d0380352030840b49141100b800b1000e1000d0000c208040850141e020000100801800800302c00d44c00a0780764011407a40340b8a003010f600140b1103040f00340001c07000604016065a56034070501a2a60195009000035a070803030601000261904152559852454604500e10100a58a4104003032140b03100c42a070704510514800801c902e40c49100385044000b5400e01c0d10040783c0c04c070084030035480076134883c44408041c1005800400c40026003681c1c02585443e00040d10b101e0b858041c1e46480c80307010400c4072141c020030a0940350380c01c03002c814a03982d021541540040d102a000300c90000950064140c5912003011202559000b40c220000035200c00c08040d040c04041c4004455000e0240d0041e03048a09411003009207400c5103199181d88810034015040c18542100c101c0503510820f4062043c1c1101140c41405020890031254 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177032167 1250 177030917 177030929
    0xc08031b0d02030904110d0c0801031a0105060901051b1209040b040902010c080d0e0601120b091b040f09060f021b0606180705160318060504030b0a090c080102070606060e0609010c1b 80
    0x41023001a10005141ca2024042290580038105002c514050010046070485600602e100e1600c0d417028011561074100d1048a036034031005c200c2d42c0c0e442c00c00c28040001140181350440e5200c01c0313080c0030070058030345c0c000d01c80340118a4a0034500c0540d0340540408203c07508a80c039076076244c4901c40010028208a02002c05c103028000004c030344208e54001c0c50400314081c000c1c11400303031150303504140c40303000d100d001160250a80703c00da086410300740c06c08800030450410020f031014594682d10155000c000303150200ca41c0c001400416842403004030041140e014005080a03d081c1000c00c01e40e1341040c0016480700b29500004400a11074000c6860b048619866234403c12401d240c060304420f844c003400c0c200009030450208600e881401603904403508042452002c6d11aa15a64010190240d00f0f8450b810350800c01b0666880900007026001e00ca104000f0303145190100091901400c079070502d101d90000c0024007442c0c0e0340001c00300c000c43e411107030344180d403002e002c03c20704031190991200d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177033417 1250 177032167 177032171
    0x90501050c0a060509150a1b031506180e01090902090702070b1e040909050f07080a0b041509020a0308030f061234032901061407030306030c08031b0d02030904110d 72
    0x4001d422030323a0083c4100f41c04156221400b81104a016030540300c20084440c503800051004000d180d10518620070f0410704d90900d4419691034056100d80c580090304030f900e003da1a540c20104505116448035802421880500441303418034260441e944a80d081080c401c00307080680041d0000200b00f254000e18100e141000000d815160240e00c1d08460764032441540100c2d100000e6040b804a600e84206500c681880100c0c2d8550741d0b00c001060011412101403941c5100300702c01600c03030354010000303136000b0814951a8a409009001d400e18000d040701c0c09500724120804424000013070151440e0008081e040300d01451850348208401070144c100d004140e008000400c1c42411403158801c10030040d2107442c82c070031280b981c00d0f2803082840ba03d40095100b0b00345000102402c800b410303600713100e072a0200d5004e0340d9032504404164240c100c0c018541002800c02c1413914641e4200d051044290003411006540d100041e49a02500001a00958a0340c400030b180c4d00f000c030110703a083d51300c050017 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177034667 1250 177033417 177033421
    0xa170d0e0609040f09061416050c010b180f0603010902011d191202010e0d080901080702070b03070915020d090b1e18090f012103021c050901090501050c0a06050915 72
    0x100d401a002c50a000e4171b10902c0c0248101c04480000540d61140d2401c80c0255240c51101c01c023140d90b40d011102c10701403950384420324107481c5c0d241d4211202d0121405070550706418211a80d2680b0403010702114800c1c1e14104c400d50050342c208500c412401610400da125004071840410070704d054011480c05128040720001c504200b15060a03001c20f4006c0e80c0d07001d010f04c6000c1c00d021006811440c003400c0e000c01441700d800780798412801c0c04e51000c0584159800d46a80304800c0d0040d130810307103000c0045544040180443e05035560190140700c118401860a80650310011b01082304d40c5c0980c003c0d100002812101c618250301c81d101e2902102040c159440102d10421003d05150514461003000c0c00d0001c6030240303944e01d0005043e2007100c0d1404501c9509050301103040101c1803800c078154051000348104c5d03c0b101d11079502840b046500d03030517907514103200010454112a005127040c070209100504400ea0005150060541d2010300000c2c65110700100701d203000010302c03503035560300b400b181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177035917 1250 177034667 177034691
    0x8070e0d0311070e01051302030601090317090f01020c0901090e010e07080706030b1f030519050a05040c090c091403030c030309032101030b0a0b040e0a0305090a170d0e060904 77
    0x80c1c840103000004054614603134480c858034541000a200d40f644c040c0f08080c407078a85200031350040d030b00040c050410300c0049070f1b60b540f98007070f645c1e4007140321006840110380c1004074144040d0102a015092000e41416841d40f000500e0914040c02046509541c0384801070320f502c0d0960246521029040032694000d50398510f090742d840c40d9001c0d000020742040504006400c000400000306054000804d61820900c0c0703007103006200040100790301030a0706000442c0541c142c404c15001d403900f0703100468185031604113010703081803683c00501072518000b00107001641c40f90144054681c0403010a515107694400039240d03006030840ba08041c040001803081091002004000c000004100300d00c40d24455400300d5501c0e1002d00c07011b410900d40f0400140201074503031001041e802e0052002072070400d180d6a00e454140d641100f00e01080c0c00080340b860919107075444d00020800c0c04500c0900d60707000300c203031501c80503164810300c01d020907c0030040c251340d5000f040c0e8400c6080034100f0064190400707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177037167 1250 177035917 177035927
    0x1202130905121b0d111509031209060601020c100c0b04020f04020a080a050c04050d0b1009020c07080609010501030317070909020d240509061203040306060b0a171608070e0d03 77
    0x34801d1080f500c0341c004c4003038045000d00092142c4281c3d140c0940116441d181e8840308412000b440c00380c2d5404100207080c01d8400c000c0c08180948001070040c04546040000a80b07003940c072070380a9101e00100c0003510246035000d64903c800c6540030340100c44076111480030402080c0a00b040c9a4060300220324005403581c070902c05841840f002000f0b10141e2541c4280001a200301e01449400000c3c0b0010a00468030714124140c02450700000030901e143d4441c034660882c0c0109200c3d40443d0094101008080c20030440b007500311147c50004c211551540c0e9014100da1100e59140314810690400a1407041c0104a440000c118441c0155552007030f081c4003000038003900702d100000783e1099180d8070000c00c0820401d0280c401c0900143c540351200003c10410390b900c00a501d000703100030070002c400034403a4000c601c02030121880c010780314198020060300c0020042c40009400310841c2c01c001000614401041044615007042406500c2e4000101c84002e100b41b01e1170b400c13142400d04041056401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177038417 1250 177037167 177037207
    0x90506011d0c03130203010e100609020f1e0f04030528121407020a031505010e070c0308060f1002101518020a020c090408040e01120213090512 63
    0x15006491080e038035081c51041c00741c1c841000c040c400032080001044240b40c0c00055800010082c2d07110041101603000a00307403080180c0c03041c041c2d0411112800e1100c0c1c540210700242c03440410560406d581c082606025010300740034004401c3c82e601d0b8034005061000d040728140300311085e0f200c0c0c2d00c03512424450f5980003100301400040031b01000f11502c0e401d00070b008201c002c2d0701980c2c1e00d41c00400329004131000c1d44a25503000c0700c00010002100143c1e00c000d07440c00114458184446500074a5a2403c100c4105074003450240341e01c04200071550303900c0302c0c281c100aa4903041801454a9a4020408240240341d109821030401d00d2410002c0303030000381040c1d124501c2c1100b803040310140304441e242000d40344122048490002910a078011303c03074000e840311924910484440c1010980080c14a000603038040d12181c0c0000750030f002d40b22100c200700c0d000d000d2a5401c402d43e0040390f40072840313119820352141d85840d51500d400e0100503081c4111051070901495440d12031041101c1d03502e103040c40d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177039667 1250 177038417 177038423
    0x3080309030a12090827030703060b030c030c010903080a0912080d0c0e030d20010c08100b07030507060b0a09020c0d200303061e15071209030c0510020c0405090109 72
    0x100b03c07a10725007240f58000e0144240d4400b542038101078980d908034203038440003210900c1514000c0f9510100703032000c01440300110300500f00810100000c40070305041c201890310050180d0064214820a83d030031210ba07504403a0300c40b004990b00d00800c001142d0309101da811070700c2091410000e4206003c2c440d8041d000000221908001d83c3d00c4c45a003da842e0103030320b801c107a010703007240000e400114001c1152001000b1105462000001010b84040c00c603002001118003207102034050140c800d03880c1a20b0350103480f00c01005031400210351800f41c010b0003203c00c000d04142d00c40380014100e488004901c001003640d078801395250584040e10944420241e2418400201a8003010039050b50700700c030815810030300714003462660312090188072601b8154200c0003046840d1202074502a2107948040900ca06c0c2d5001c026121281464008191440361080004105c201c03941031022407001c9040e8022501d0446c0c88143c40c003905081a42060300000200394002e240c8170401c1203040f0190003424450384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177040917 1250 177039667 177039677
    0x601120510120503090409051509010e0c040c11060405060105130615030e03070b0c03011a0c0d0e01090b03010f0305160e0c090a180905010b040908071b03080309030a 73
    0x5800216808a8000711818140000c60400821605681007070750070110f4050410380341340040500118040d14980031084400354001000c009002c0b01e0803240c00c0d00248903200034400c00482c03800881c0c0c1c4400c4008000e1150b580e0740b548190150140b045c1700314032010304003034070850301d440c0c10000e8039207100340300305805840300f41c0c00c902c0d42e020b13584a60b4060b12194048165000c40001085000b48003032958100c1c903100c10030a00c40440c2d20000250b00c9030003540da81650b01e41c1400309001e82c000c014824540f00c43d00c20b0000c280c0c040c4000c20011481c60607850504802c44c2c0c1400101e5213503034550f12003807400308008000306480880c1e0a81c0026a4060307c01c0b106581101400c0a465910314401d481100d601d640124012035101c82c000c1024640081081813403030303160100c0348801c002c140e2180c000e0341d0751295440d00b0401c0c00c1c020320a00341c404032001c01408219031038650b034500c24004000e10703a807003200d0003910b000c101580790406560441d42668403483e2400510317599a22140740b0b200032903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177042167 1250 177040917 177040937
    0x1270c0f090b070f1e02031002040302010f08041a04080f04080f07050109050901030f11060a0e0909160302040203091c050406030b1507080c01060b0a020109061b020a080d02090a0308030601 83
    0x800b10300e0846416940c0807001d032040c49030315224200c21141d902200954810501c1512025a5080054103d40b40180c040160f40d280345100142200480c4030000043c820384404003c04200102908040d0204807281082030ba640d6160240c1d451290706010011010040f801103080c0000090380b09003924a44110b030440b40d01c580c01074801c00254428164001a104010b1000848100050488620505c201c003000c001070750008416030010900480001d01605184103e854111003141d0001401c40241100c04004040d0804504c1c0c1c502000e805107400001151000745c040200c05589140030b104021403203c160001000742d403040c440d510000b400c01040303480d24503049034085051058000c0251070002c1c1a80c03026000e4110407001d10711950f80e114001600100c3e20010081d041c0d0036030000a41c42c6840c6441800c681c10100c5000700b5035001d4100c81070140d0002103109400342c0028500e603c036002e460b692030192007400c11150300541000800070420003401d0245000d050300741ca031400d0301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177043417 1250 177042167 177042179
    0x90c0a092705070b0a11030304030e04360507030203060108060906010f05060415050d0c120e06040203030d05250903030f02030306030d081e04050a020a060c05030301270c0f09 77
    0x140c0780000c080c142e50000300c420440180b40c04001c19440340c241c200f0088405080707141a0664000712019004142143c0c9440402d00c1c051050200210744d101640f880005a064500a070000c802d00c1c1c004521514074051043c08010007003c402035900a040b15000d685803040151900d01c01d03030384a0b007c0d12620002082c00c07030351482040c003a40ca0240601d803d0a1505000c1c4035007540080c880030510100b0001c0c12510f180a0081200030104c03032301e41400300e420390100c8200312200000e82207043d4008005200040e5004822903c180c92032100110341900c440340d510189048041002c4441c9030795114904c000ca41003000c030b504880c065151008800203c20041c1d80300e100440302c41e03525400c58a426442c580c003941d91250801010402c0c1d010100382000c2c48200c5070720540c1d00342c4042d8021041c1508500e07000103210082c044074a0b251100304156600d060b42c0b0b00041c050300c450b8030901ca206214518010809800c07800315801c0074040510299005403051041044c00400500c039000c01081c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177044667 1250 177043417 177043481
    0x6100503010c2c06120901050411190e061908011401060f050910051b030403020f010516060e0c0904060b190602030418020c1c0207050a030f060203090c0a09 69
    0x3902c1c04040f085075005840d1611031401100c05008182c0c0a401800b00404040703e00e5012031095400000009080c28141845100d070300c0c00354840d611891454000041f9144c0e0745142d0780072900700100c40e8000d41c0300c24000541148a40c800178000d282c18903000a680ca00542207041800072610040d80350782d0301e4203000c541102d907881d064008900d041001c2e5009060101104003404818a8a2420060480038041081d203000280d400c26500c0801c06000350301d40209400b1404009003085403520454011160b0074040b9030902408450340d43da52103c18102c00d01c4208440302c1d00a24081480c03404c0e180c4030005210511289008021f1250342c5600c201c40f40c0c1889040c0d43c1c2d1a001503040919025540040c040b201008003080d9800340310041403820204211404208280e050106100884000030301d014415070015110b00c2090104202040c1d90400409005400c01005030b900c4c2d58a5881500c1d110080d00c001d40c005101002c00030b88554650b00098081242301004c0c171300082400f4032061 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177045917 1250 177044667 177044687
    0x7060e03010207021507020316060203040608090705010c02010f0201090f030c12031a0402070606120507060f0302030c07060b0f120606010201200a03090f06020d02040f1203020a110a0806100503010c 87
    0x5000b0150060240540510401800d0411f1008044035100b500450b500c031491750036540587c015901c0414207100076500042d02691040281000b82451458400020309258400501a06000540b00704a2046101f9002713004d00d5a080101441c081e180d0b071034014840a006e920035590255641e55010b0030501c6030043c0406100703a0ba5006003a2040b80d4200030080d1302c8403504a42c010f503181c1001514105003000000914099005403100c203141c84406440c2c182e01d520000201481042000007030805c510a48a070356401081c0042c3d080d00c1100442c148425015160360710507000711000030a6a0001a102e200344800c3c2e00031301050046149010300c1144c05c041b0a00c0720482131014102c00b81c403d5000c51299030181c9000f440d08009511040100e0384030000707582e050b43d00001c0503c1184662044000244801c86259660180f00d440c0292201c4403c04010603450f480c1814040030740d0781040711000f030484107068400c6410000022041d448481c484e0501039400d0170090b9110074010700b0020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177047167 1250 177045917 177045919
    0xf030105060a03140a0204230f070807050703030605030604050106050103060b090616060617101407080a050a0608010e160605070c15030216050609060a0c0e090604090b040507060e0301020702 84
    0x40803141943c0e9180c013541191103203c4480c0c4901d800c20000f46e503442c007401901c144480405c14464a4098500480f0803000300315501d0310704050240071016501900c960340c095a03514069441e20b0040c981200608611f5014a500d071155005020500806602c89c0c0700f120390980b0204130260f5514240b4a250040c40410791740710b001440003015085030800300c20000d620503c400541c0da83c42c0d05106883c0c045003044d868140e44100b0b0a80c162016130b20a0707215030f245c4070b43c50214a15000344000c100e010000c0c4420107840e20354000c15050030443d04080c014210002c02800948a014a8256159074407034400162201c1c0500020350b0b85c1c09401241c2140750005030408140307046c000c2a07020b1003440c1d80c0000415a080102040314080b15070b003209190300c520090082c9040c03406405141900180c0302001562801d100c4002280d00048003241006c020380c3c2c40ca401c1da030703040001001011041800782501c50000c0403c4108140442d041040d03404e252076413030b0441e50340b50600d070807170003150402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177048417 1250 177047167 177047179
    0x20d021204120c05040212090105010b030103020f01050a180902070c1a07120c061a03210a0309020303040306060605040810020c03040302040506040b0d03200a0b04020907050f0a08060f03010506 85
    0x380315180140000382080c6008900340c4000c01c4c0d4500100e4204c0e070080c83c00841c14440042401400340c0280519401002c0c40c1d040503042d1f50440c0c000071065096074840f28180b1100280416686000d00c040c000080d9425450101c850741c0c41010348040e5110b5041120460412000800e41c008480e403800301f41c10700d80a184d400d12125a5600300c00c208080031a08c1800715001190300043e0710b9014142c1c080d10100c50290340750711030400b8540342940e001500001e101165035031030110003102007920040c110528012400030301c1c60010a095200d55040540603038100400410010740280051049500800484a04169200319401240161514864140c01c20007003000540344ca5000706030071803802000001c10034044030004400c110846811000300e14541707544409148040e0000d4405000080a03010034030680d80d80400c024001400203100318440c1012986540c480c034182d90308170103040042a6903207050070010309021401c40c5c5803845032442c5c040101c1130741018021240151809401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177049667 1250 177048417 177048419
    0x90f0c0a12260301090b0a050d03120c031103130c061704030f110d0f021e06060904050c1903022419140d150e060109060302030a09120f020d021204 65
    0x144080b401e035001e07a03406440c00340c41c0c1401c4401002d10010341c020a40582c000921a100e1020b00c40381d80300980c8030074410460f03a401b100200c4d07001003214001407120840000d0306604060260010004040502402c0e5404000c00c1100103000d1030500600c0d000703101c07004e40309903500d0741140c000340080c1191602d04040c0c0041000070b40180d0660494a065040403841c0c1030784544040e1170080c0000c5400700180b02d441e5024000c640510840403d0422804001c405241c05a8816610000500701602400c80c4d640000e050100601810405000061040850084040c4c0c080c080502c1400141e1280c460b04012172200b5201c1c502024402e045508440e007801c199050100c0101c250320645014049094140b000c03030a10b035001000d0404482000081c804800c0d100348112a903a83c000c03508012801c0c003400616078002040303400300c0e162483d000d6541e50b1803507010b10103446846002446185040064000039400c0080f00b00c24004035402c94264620035171040341d6800d8401a40103c022003004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177050917 1250 177049667 177049673
    0x509031614120703030c0e01180b1e070803090d0513050103180b010801020a12020403020a180e19020405070e0f060a050c07080d0f09030201080604051509090f0c0a12 73
    0x70551140401d00040c0e031a800001d405114140d8009142200003990301c0640f82c0c00682c10941c0140741c00320a1030244428880c140600446440380e0092a404860100342001d14000c450310009440400c0000030392140c213945805c405541080e0340388080390280a02d61401203114509690360254140e40d0301412918000064000300100d9006a05415035040050003098140b40075074001c0c800d1200059a0f00c10f0010300034030b1980b41005540040b0700410042000d070740d0f4411140d00f92000180300b05041c03543c2c0482c0700c000700019045040c040c003c041180014030052602ca4040500a49090245541e004001c844140c030720300c000d551200d00c0308480c518505141703000e42405105828040d141088560400345803050a5102030510741c03003110041e440d194460300484244203603003000d001140c190750020301002d0340208030f140203a940b0800291240c030221240f460307204019003484007600b00645c032700d0b403117a0012514441c2841036031103922041c142444001c00b00c2e03020003049180404159 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177052167 1250 177050917 177050933
    0x41203351602031204200307050303180109150e0103051305060a050a020c070e060f0a14060f07210305011508010e09031908040b07080f042d0303060905090316 70
    0x101601c0118030041c4840c0d000d004a4201103401a0300406902000c201c0c2c80b2484a00c0c8011400c2c0a8042c1e040240c0c00c104c03d443c000181e0f007220000110391304c02c90711542c00403507018840c0e51000070408280c45400c2d80b615003000c5d4100b0f00a1003030703906210035a0f0303440c00a0211035411200a0455001000040d41c6a849511003074110160200141c0380000025415141100300d8122520034903025080c041d01d03181c80104203c400301c0545054000f1450212010700c2d841140e284140109000581203209403a46030449000e968004142c900000b074110307031000c1808030702c2c012070086840d100000c912020030644c9d106e501076060356105040da0a0400d0001d0005c0d014005119030311041c415071040741a00c105c850f000e001c1c241d9a6021516040c2032480c18000003a100d00240407c540c05d000507482c01d184080d5000c0d8000003a02c4911103480a0580740340d5594000b880ba68030340c0010b0074100340d81504180d04130740c4400c1007400b95031101400e9035200c2c8100c0a4000a5030016035a46000450360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177053417 1250 177052167 177052201
    0x2706090d051905060a0501060305060319050c1206070908010623040209060a1e0f08011502070b0307030e010b03010612020909030403020402031320030d0c0804120335 73
    0x1e80252941c0c62070400e0102020034070540304940542050081062480e481c0c842c2900400051600707000d6401d065020035140c2108a00341c4115030032040641c01400f100b000b0405402c000034160b44001002d241d4042c2e161102a2031010020b1100b000c0040c048005000d648142c582d0b071209500050040754008244121032415150401d80910050110b0350b12100588101d20852f1101407044a59000d407403614000023102c10140400d41074400e81c0994800025419a000343c0d0401d1448809900300f6480c242c140c0e44102c56002001080200e00b0f41d158000c1d50364640781d00028014100000201401c1e00c5d2240100341e02420006103c202628103071100f25000b03411070f01901d1409459402003420b99002300c0c2c0d803500d8800c01c49581010000c6801c078403040d104c0401401184020042e0002c3e0f140d2540d24803900800c0345c0300c103840041c0601c6400f101c006085414540852070880c2c0b8020b003040d4140e510070305070001c0c1e40702609221603003948541c51500070910703181110340c0c42d02c030400814090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177054667 1250 177053417 177053423
    0x40807052104061707050a030b0d020d060b01181d070201090501050414240604051305060c130905130b0702031b060105030609060f0103150603081b0d02071d130203060c2706090d 78
    0x320300b1280984c660b440d0104331980100340120360401d034200094140a602c15194000a05541c01000300307013100c5d41420242c5141888150240d160510124050070344400e02404075480c010500003088080d00707641822048210580e240302c80750140e580129030361044611a02c2ea44071000a000780707000e80c8144d0b0b00880c03c0070075014004160315440d10b0700200f11200364203084005060000101d085014030f000f041544030501c85407800c2c1ca0070301d00c41091144024641801c3d00d011552660080c030590f4029821604580782100d0300d4540150744140c20301c12030340240202c1022072601c180209469200e901400305007141c0384d103507690341d4464090002c1e40721002552814040b00007008140181340c811408440e06c02402900c1107098105010001c0d4101950f1000c0b1040010400e912254920780b1540f10120049554424010483c1001c0000095140c0240d4080001143c0c1a8000c0c00080c00c0c080f2848480c0041a42030f40590318140902c6036001a01340034242041c0361881694068900c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177055917 1250 177054667 177054679
    0x10b0102010e060f060a030b0403030501080c0d050307110619230306011413090e03090102120408100e010b0307030311150103021c05280b0a060e040807052104061707050a030b 77
    0x9920780b00c00e508c213031080d641100043d403900c00411101d10200a4240400d000321000c0d50329001c195100c503528803038258001c090014890100d0802e50b96441500c81501c4140800b80c0030405080c2c0082000c0340443e5446080f0043d02d41c01c007040300904090741e00c01e41060b11440240c0040012855103a08641000c210200c2d0602c000309401020303000d44c1050101d840000c5d502d0709200380000e403c0601024060721080400d01080061110020701c11800c8410450006000d07034004445501511240e10b0844d01840340c2000082010713403202243c00d40c0010711080d1030045110102e00f6000b0344c02844040d40c40110141c4034040d90100f0041d51040a2249044644035020140e801e010b0700d040b11160740541c11600100028840950002070b800502950304220050412105036020940980040c0c9901400705032141003000070002c0b110b0301c0c81c115081050b03031041a00c4500c41030740140203c60001d41c0409103031701701030b103402c2420b030107440c03980c643d24200710510404800070b212420403564020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177057167 1250 177055917 177055919
    0xd1e201b0d09050f0108090d120902102f0607120905012f16060b06040b03011211040b090601030e012a020d0c0c030305090a0905090d02010b0102010e060f060a 70
    0xc0c0d410024000d0424154550030141440e1404000089007103521950500045908100c0041c802042201c03081c2d00b00d0414000e0b061003025000c004003c810310007500440c412402d0f0303460640044294450030301500030454956044d4500d0700000481710342c89041c80e88200c01183c00300d03014004201512107070010000f501032268640900b0f4501c0340c600062075041c003902642420703080700c003c20320600210080030701d4441c0b00094581003a81c295005072000740d5404024010b55078440c00c4800921000c0034860320795859044880c1e10b10648107080b991000141c526004a04103401503581490b8010140f40469456030019030103000c911103160000c0d580c9030440c00b07545410070700040d86450342d00406021852483c40181c6003807a410600d40c00d100540010a001480450040b8152641481c080c0d89420014022406582054214241c07007410b1108000f0f0312400010750282c0100380b540207010048288006a088503040c0c050ba0486802c50f0700066040100d03040c6c2160803c2c000b4025030742c20303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177058417 1250 177057167 177057217
    0x305150d0c030314070c1a070c060503070e010905010c1401020c19050607030501030206040303030e0c0607030e150a051615050c030a140106090e09070b0d1e20 70
    0xe400e4a600403618140110340500038194000018100d40540941c15841c3c9180b13512a01c442d02c83c0c601c503034280010307032402c030340c9084011030280da410301c4c0d00110001940c4e4491001801503002200e001000680c1e96010311119803190881038110360040c1c56000d10080c8944402c1e40d500b11440c11502199001c0003484440303101001032062207815008014554021464481c1c20904040c1403942054108001400035907280000c50b002c817030345420001006684014094101003403001c0d41a03002c500828050281a085503141000e604101e65584d403440001620082074090300c205400010818001000c10100740030070203580074000c103000080100d900c4404426030340121004403400d0408011720881e4001070003400409804c0c0b09808100750b040c45401441d188080c45444050003200340421403480041c45403101070041c0110403640ca607290300300b02c0003400d166280c0d01410b8201e4500f02d00307074106c41d100303030f6440000d00040b480012101c1c0103014000e801c0001105c84045000001400d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177059667 1250 177058417 177058429
    0x18040207060608160e0105030f121803071d0f0702060106050d0b0604031b120302032a061f0512100902060d0f0906060e040b0402090c070501020f0c0d0f08010303030515 74
    0x7407030035201c511300c13031990401c1c8202503024010b138841806036000c002c4c8003000707000c0494200212100504001c2c2c544d41c404039520190a085c000050f01805142c1010500e2070b140340402c0700c070032498015048151a400c054464040007210540300681001d001803200c1032040000307140c0300402d40004901d200368200007a6040c1d209a0044400d81e5a41d0441c620740c9035146801c03030042c000ca044041c40300e140b64030003a403a403051442100010281800c030b41c2c0313010101d2504114512000084038464a0551494640c1400a481e6112940d940c500700007400d1500d000c01c1010b005c02c1801410b90a070640104501520100b031003281c3c0800140700c0b10a1006080c03141e030342d5044042a010440c0803507400c209040f28080d4011810b03601b4498200000719402c401080d812a6040d0303400300899035510079820090284400041965000013100d1000c5140440582420300c8181c003507030580c11501405840c014000d0250a020034004401000407a009074000d80e0b11541c00240e09060010301000196 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177060917 1250 177059667 177059683
    0x100308040e06040b030d0219020a03061419110909070e091303030522020f060904090803010e06030a020a0b0d060b040602060411120c0d020f060a08011401030218040207060608 77
    0x480c03141c041d080295034a4103008000d2a03480a41c0035000d02c50490700000d448078645654120410703110130541d41107481d00442e01c80210b41003002040381c40c540c00400b0823414016901124500900000b0000340c500c0d40c8688180c1003100080305e031411400000380107107050020052002e000950f050100d503501c230000340764405c80ca0350f550340b4078003040c514014040f034034080d105c16a11801040003d0342d808034900058801601103455000103076031500090315910402c2e10098004d070030411500100600800030f18160382040650404913950181855a40c0369911000795010611660810541c800c410090041ca52241c0012030510303101c040c1d0034500e92140c1e05c00c40c010b030306c210100400c0c80b00549101182040031202d81243c0080d0100380c1740c0d5040460803507841101016148411036941d10700d4050b070004050003c54031042c1405004e09200000d00c1400d50148074a6100c42066101c1d100f00c814903513610072450a041c0440040c003009422265084032415524040803800003800c100c102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177062167 1250 177060917 177060929
    0x2360f0a091e060f060801090914071403060a02090312070507030210050a020c010207050f040c03020d050f0403110a0213110c0703110a050103090b06010804020d0602030a021207021b060310030804 86
    0x39600d501d00302c180b0202e9540d03502039401c0e0b1084000922045610001c0e49044a00c08900400c0010702400c2440c0c014280140b00080da100b4040002002410550440c1d900341d400c4068480580d10109190280e103d84000143c0c0340e0003440303030715003020500c501504440340104125080c164495002ca4585068404202d002c207d010482c0101503904110702480c08800b071003d030002501c0c14012940340e00d0f60004281c03207951544031b100b030310380e01c01d9040d03404440a8039014041e41c1080041b110120384155401d60008220090101c0d15140010344c0e03880066026100e50000d03643c1e200c001d001481541949a06428100b282184c07400c000c005d8007024502031425001c030050448200406e8a00e15400a0b0502d810040352a004c51160031003250310000c20f0030013405580da507100188501c000881c0007081ca91000c001c1c00300111407940a0014000c1c01855034140e6100c8010030303651401414403441c5e0a40c480a91032030f1908007100a5600f102510707507100b582ca6185d9490840f01c1c0c1050700300b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177063417 1250 177062167 177062201
    0x13052203020319020114010303030c1b0602090f0a180504020f0607052a030a060b04060506070303150b0c1009031103040801140c0705060a05070509040203010902360f0a09 75
    0x40c41c6034060a9500040f0104580000c0100314004c4806034102e070f0b0144405418560b480040000b52402955040c100c0b0101d004000d200740c80b40c1c94100002e401503c030721130207900c2c68201c070300c0c59060020390324099410080c0d400c00d4100119030391304064080140700726080000c45848003100d0b200c0700064104a40f04030003510701850301012800181d00d154589900074a17200146002e16200420071100003508001e01141d0741d081c20012402421003a8005c9030021f200017014010b055041e400315174006600e07080c05905543d508805090b5001c3c91400d0080b40c0c108a4114889a11030350011501900c00d04100c0201159180b005003590444e5014003060303516105200ca084000503001980700b003c00003028103154542d2240c540c1d46000800312041581d40310007244d003940c014020f8400b6960000e000b9966580c440070000041c0d0450140d0901200c180e4903c0c01c1645040c1422014000f40f038a443c0001465007010410004c50300e10980340c001c0c0d6080000301310303030060f4026609600054108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177064667 1250 177063417 177063427
    0x121502120403081e071718032a01060609150905040f0204030501060b0a0806090709080a08091f020309040b12160e0a0b090103030c150e0f0f030306130522030203 71
    0x2841010070000b03100b2044075030031130080080c8035821040320b0b4800302c0107a820756416030341c5081c08841d407c1d036074a03411035510020880603002c0c03014508100410540ca03640c40d40c140481c82ca0103003641c02d1801540041030441009100d030784501180100c3c000c031285003080d41141e944020504071a5000c13030804003181c00140500600600340101d1000b0b10398110b4042c50301032000d00c020000d54000d0700c070318828801c0001160300144501c0d11000507001c20401e444101c0e0051800c900b55600120069014100c040c1200d10020401a89601040945c4d000341d85420040000c000c001c2c0248060a6070142485080444503841008105c0200c0b031007140075988141491b01c40891400018411026181417001c503540d25141d6100302030441e5454200400700310800c0c80d100d4003100100070307140700007841d004100c0010100041c09410240510302035030040c0080e00c0c0c01685a1001310703802034105402c40d01e004000394043d4081c1c0e61019480c61a42d02c00030b8402c010709184410054250011b03800410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177065917 1250 177064667 177064681
    0x140103030509010e060310170a120e21060115110a060b1c081204111e0f03160e06010314070309020a0509091b01030204050a0b0d060b0412150212040308 67
    0x780550b00100b049480509600e03202000403c6c585c268014840a0300d404c920b0081e2540c0104070461352280e20a03940144007121b00002001d02c6420000e882c818468032044a401d44cc00850251200c004480035006581c01e082ca20701c4102d000e00c450004001c20480e490110900501c45a10b41c2e6100d4000810f0396003500e410010b080c007061034410240300d0100c543e2000a400501120014015400c3c001c580781d5550502101c084414480c40c1c0e0001485540c2c80c0004c4040310300c0400c144d801311000c5030a5a004000c0c55a40c5030401c0c040781100b0f890000900c4807090780283c50303920840c14174001c5448035100c154010521402c1d00c4000101e0384a025400c00c500d07055120700301820301940c11102502d8000b140503a5035048418040c003801c4400300030303595640b2030b070100c501810015101100c1941e890f030406045900044841e61803510b002404260348101c10111001c03a044c0b815001d00a81043e250704259141007200c44c1131042e0b00b009a00510340c0380c03c40b0709110300d004c0d440300700c010304d0005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177067167 1250 177065917 177065927
    0xc05010605030303010f03030305100306051608010b03060a140307090615080105060901080c180603010f0602010e010504261c05041202010b21010609090803070f080114060d14010303050901 83
    0x24001d90b01c030707800520050080f004140c00e501e04803509450040307200d454400d1100381885050b00060309603802c0030100031824020340c45840d80e41e40f113a03648101c1070f0390358800c81540c1d00040da641640486045c2c0d042000d02443c0c000b4030003c40c1d00400b594041070392801900304480555200c0845da5440b000a041c503690866101801000281d525610b031040d1500024400c2c0c400134072103641041c000c20300311034042c5515845c042000700074080d07070742d603586481d00703a46000c150784603101c010341c00c0558045131000d042c080ea81c00307640e001c3c50844e2802412805201408070076502c60403c1a01888070168405004000441800070700f10006018102824025030060305206100d0540e81081c070382c00c8103034850b0300e0700500306010300060b102c240013a44507040c01761820f43c4c803148210381485035030814050318000940c00b860194a88040c040c11034002501d4500003445407100c40d504030700003101075040000c000c044601d0303140800606200300540000c9000e8080e001500007031000704050b11079517044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177068417 1250 177067167 177067169
    0xa030b0405040c0e070507050a03080a0e0706030e01060f050d0f0f080a1809050f0c0a030b0301050a0203060117040305030f0403050d0c120608010b0d0f03020a0503040315060e01080a0318150c050106 87
    0x1486d010f4584145901c946955aa41520040400042ca000070302210503d51140110b070b01d05506840d102591410000d01800034070485041c1946401c40c000340c0a143d034000c0c0011a403000d0a1542540c03030a4503045511080182c05403450a51901481c0c005071824004020100c8103407210b003900308803080c400b021a05180c0021111a01c2c2505006012020504131640900c08114a90740c1b10440d5030124050f2001c4c200e1641c06600341410702c800c0d444030390099842604280e0f1401030024010001c2888041e003a20040c000c0b40d410400700b50498800c0102a5000b402411300c6441c00300700039070100890320380070601c8000418414400301088068000c0c88010004807009002c0c010f0356a000542c070010f4200001e00d450101c0e000c6108250003440300b40c2da4290440300781c90702c4d0703641c9061100340460110400e06800d4945103011450b0280075141c03a06899050000b48140a0780c1c1d0340c01c0c0c8503484100e01d0208004405000010301c06402401800c0003c2a5920072558560600d0842c0c00e42e816 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177069667 1250 177068417 177068431
    0x9070305061501020c120309030a0605012d06030507050f160201030b03010213120f120203030702010c0906080c0c0a060c0201020c0f010e12030a060806010f0302190b0d020a030b0405040c0e 83
    0x1034600c03094010f0fa0300284103682400201c0e000075a4848400100d49503105011080380c00d03019402001061002c15032010b41210700d40c6941518104400c100d4a43c141c080c1854030840c03490000c010701c1807034860790041d60f1012003401d04034949484030007c00c800d0380111200c8240703080758204134811542d06002d043c072900816802036003003403085c1c5045c0000c005c5134040c0d1004a4112034055090182d00b00c05041c00ea0341100344446100140d84d0006d44950007101c200c0059801c1900741c0720080c0c0700f04c08400890b009a0f4134411181c441d01d040c062036a00004c1a8140b074400c4e00302100100381f40c1d12031292030307621036000140d07180f2141c4449828a2080000b509859250041c212418840454100c116926940907295a80d913540b4580c8000c0007aa00000498030030f0400100d00034121304668810780340211000c01e07190600c03504071403c9101600440000540c1481165001c0040e6005040c80c45414140401c1c940d05100118084070021102a1828108110108401107110712a6030304004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177070917 1250 177069667 177069691
    0x1e050d1802040b040b030606040c021216030f050c06191b2102030105030601030b062b0209092a0a0518040618030f0c0c0b1216030603020a030f0c05090907030506 71
    0x285c1c00001381d101d01c002000540100c3d254011a00454828000d0010001000f55455280d1861600900e85001810b5007100841e800c480c030340103504d0080d000d90b0309404480000301001c0e512043c0c0300745c03075098003140701e144a520382180080210b5920400c4040401d075503115207000e04514512020061081054002644100010711050301c001c91000d0659400101c059070039100d000200340041443c116a41c6000c4800c40a0700c0849840c11501007814001c4511010750344401000e140c0b91032141c00744441905581480c1c88000706a1800c480c400d40c402065104545c0e51180030032029080c03001c3c4202c400700352200704020013800b4806d011814860003020403a024660b540680000da0704062903040c41340d008030074030800c2040c81d100d1000c4c2076007440c0c05445006900100c52400e0080e1000c0385405090345c0c544807521301c00c1c400d5008032038006001003206031075078503440001c03a4211410f840c492000080401c45480b64000c06005249110041c8040351440c20450b050100151035010008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177072167 1250 177070917 177070931
    0x5070b1f0902190f0e010c06020901050c03030c0702030d050a0c020907030608030d0b040f09030507030c0c030c08100e0d0203041a040902070309140303310509180606101e050d1802040b04 82
    0x3c7d070300800ca94121588000e005035103050050043e5607a0044c0c8001e442c0502c000001c1004a00c030890107010564800e40489a800c400d240040d03c0f54010200c100c1c0000709401c089001500e0900c64054001c102801d0000302e40c0c0e01d88005030304540c404401d60352056103500a442c07407400d042c8240903504031a40004c100c1c0d1545690000c0580c0300348100071f0104480350b48d00400744940000141c000710f0380221010641940c601100d503d40b420004a0b60303030507180440c80754882601040c10000501d240c1e01a6143c14149031000484103504013492080003030500c0b000c03e02c804544014410309000b601c44001c81480c2c403065000011000104902903042401404132201030381200300d04c0e00c034512a4415110318400380001c40405250301c0f1507886507030f02040c0400b02601c15903200351101c100707064580380e0369a841404481150500d03d4400290700e40302049980a41e08103208204026142c046c1c5044940c0703a40701e0654245071100980011001d0114045103014400c04050481c1928184260 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177073417 1250 177072167 177072169
    0x10609090b0a06151107120b04110a03050d030e0a020a143307081c1b1d060901180305060f06010305070e01230d090b0705070b1f0902190f0e 62
    0x2d400c04d2455074050101000503000510018408140641501e00ca44006a00340c2d04201c0242c8809071800e64030743c0e02d81000c1400c0c0e41091200c0c0d0050b00e1304007004210030301c240ba0089005200e074681c4003d0700e015610403c0c006a9541d400381c0f00408070200880d1290340104104000c02c01c5203400c0240c3c1d240c00813240340ca0300409124100c01d281c1e0520680c5c1d01c58100f402d0000542c4568440000020b07441d000c20301c1c40b41c0044d07100c1800c51603007103046c8010103914481030f00d80c110100e4014412103c41e40e80c821480c0390820003400349085c11f140000e0b110460b51424400e60b03405820480305908030100b0810101c5100c520164085c0c130919050080f03042240d400303000c5991039800c0c1810020840040c2d5200c000c000d580d002c10b0341e0607c4060340e03100e0b00a007404c802041c05010485030070460701e001c034496902c1003064500103070700440c2e0f846098481e000f41d10701030340010840340004492810000b4200da502d101501003001000c1452000b01c40d41c00004000c080309500640600040145524103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177074667 1250 177073417 177073439
    0xa140304050d0f0c060213030c1a041202030a0c08010f0c0c020931050a060e01060506121302040c031508030316030203092d0c060906030f0711010609090b0a06 70
    0x10703a01050410540241d5051002c9138649010f1001038800c034000240c942e60f10700c1710254602100c0c0120004030000381c481020800720f0300706110440d8420f4091100307005229081c50320003000c610050803141c03a002641e035820128003442e4001d420780c1c2d66a101e10601a146c5004951401c5440c0c900b800c528040c40e0300064901101524a05446043c054000800c0c0c004e10301034042050343c0408440c144030303945412650382247c000e04645440c185603202c0b8188105004600c140d440c020541e03420040308000454104e070009064009107035802c0b40341c00150711356100306840740701c181cbd6020035440340c03140f9019492102548036011380d92040003001003500d9482e207140c01442603494056030300e8492040b031616017207610000404180428103140445500fa0b81820300c00300c404c4080ea10503071808010404a4040e243c44660842010400155882d8408078107907404005400c0c2041003c1040344887d0841c1c00c16080034495564868010040c420341c02c041c00d84c440200d28003030040f14180300180ca1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177075917 1250 177074667 177074683
    0xa0c0506041a0307200c0a0f0803031306020d18050c0906090c0a090b0f03010f0603020301050a051c06091202150408040e0711060406020306040b1206010501140904060b0a14030405 79
    0x7608100210200c0c082030322621111001d00000b46840303075207000c500303040360700c41c41c6c0e0f80126849952940f0001521001c0032044100b101c00305000703181190307949080001016000e80d41180c80035030800005102c5000e5119820307040d010f503081480b01c105039203046445d140b41008401e224500c4c504c00c000503a40e50001e060340c00643d055070709803901c442d00c4003a54001104d8003e60f0850314046442e041140c40c120240d41219104000d0406150392404194220b120a02600c0e4100c003070010144030a0806403c003040d03002541d038508020f0100c1c4e0300d8031811a80c5004040301e9011111080c3c01000e907042100c50348240c482e2440caa402d0900355200300941c420381c480c0c511444500000201071310300038034101040c480030300309481451603d450444001d5200b212080d115034906415201c5e1030400d094020200f5010790014040b990a00005484e40900401981c0202da4200b010b425591658041c1200402d400c2d400aa00d8011000c800341100d0344024440750451000e00400c400314000045c055 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177077167 1250 177075917 177075959
    0x604020c03040308030c070309060807020a020922050a0201080610170411181e040201050706051503030a020606030613050d050f070c0e070e030d05040e060a05120a0c050604 76
    0x5a451903005400c40c1180243d6002414203c000300812a00084480003459614466603404042980301c0b1015101c8603010b892400040e48004550300c0181855203906800c84c0d06981900244012000e03282200710f00d2020840e45904140124030465070040c40003a003203801120181088070708607000601e052135400c402030000c0c8198021806100540192182c1148068000c580c154510081d03c8020f000a42d01c1666007a0403030040d10140b00308174401d9004d90b6050f540c0c030b40740070140d07102e540181001a0008590b10070000c0d89140950742007005000b140440e8015040c00c0c0f402c8400c02d401e0100041003024200c0d0030710040e4000a00215000201da10307542001c0d41c58000c40007012a10b030290420050410848480200d01480d42402162041c0300719541c15044425003024561904c032200711502c041507007817106000c1a031080090540c068400341882074025501c41c0003800d6111216180e0b001908489284003c0c8001408100d0281800399503030b40c80c052901c3c404120100e4500012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177078417 1250 177077167 177077171
    0xc0c0402070606080102031003050d0914090405010627050f04080a0c0305070b1e060f100311070209040602130603060f0302090c0c07090f0e0c03120c030705070f0501090806040203060604 82
    0x1c01001043d5002d00c1c0a002658021500c030710f004000e48045411900050314144142c02145070518482c103080b405441802545080300c4d1214014081d032a00050000c644035503d0346408101850700c150140070001181000315180d8035080c510100300c0d60090b140804502d581c004002c0030504100c11156400c0140c40c155030136440b5418100c406005110b8000d0005080c10709200d62948440e020320407030900520010610b445000800c03240d2416480c545030001d0300d81e100003000c14000c2d4031190560349007003c2c03a840d10751243c0c00180803001c115012258a40c1c007040c0322100102c40702c0100c0241c10303070b4101006503d08000c407184030740045200086c81103002d40000795010151606440340c01044001f00c80310951203091510142c80c04040c0c0e030516500d811501c0410104c005a6100848005805850703207030030a04c4070035510f80c490740c140092444200010b01c0040d000708250f8008246071410440e4030340c1000001040541c0790361040000354800028000560703804103540e80c006e60100d41c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177079667 1250 177078417 177078427
    0x50c0a35100b0309070905010902120103120c0f06020c0d020601080a080310050d0c0e0a06030c0e130f030201050603060c121303090f18050603030a080c130323120c0c0402 75
    0x3a1600081c000e0300b00ea004500040240644808001045410344513480c0f002d1107170341c0c0c03502c40071012401128030403005258244010808100c015080303d0400712149441d90842c06103480700c4500c0b5110740703012600b60380c0c00a188851308105101c034100042c0d0710301c0500495407504551698403007072a140070701000000000f042c148140c004c01c6100400000c0d14040c050085418041d107141c07080d1003912010450724001580c0c4030b419100e240152039000000c85140790601c00c2c0b0008010005040c1c20542c00c51282c1a030108281034041d4448920075400400d10780307040f2090509051000d06144841030044c000bd14040a20303203401ca6028903842c2d5801c42580c07250800b142d00072900d6103c0c028400708050301003114a2000354002103084c00301c0041c003c9890f60030506590f072050141410005105001252a003252000202110402c03410140101503c035121003005050b01d101c0c01c4010707480300d500e10340c0b061000e024070018040940b000c1340c2000010b20751aa1100d01c4040c02620490340016 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177080917 1250 177079667 177079681
    0x30e0a0305090406030b090a0b06060a09030b1b22081b090702070f170c0f09040f170a050406110d1e050f0d020a020f0106120305070f0204050c0a35 65
    0x10004000f11b40020408441c0e080400b100c0ea1103005044c41aa04c500604001a2580c1082c6048034034020450355401400ea2454441c076141c03540141000030790b0000410b110b0034041911014160304510350301c01075403110701c1040a102c403c10399803110302613400628042e06000000e02e241006190103807502c221941d82c0342412410724400d40c00400ca482c40c0364cc4040780592800c881030080786100f8040700c03040d9586104105400e0350144003680d0000050740018000350240c03001ca680c1e40c1c4214034030030340050740d00c04802041d00b1004903000007072400b00f402c002080e44142600b800e400e2550260064001d00d041c02081a01e03e10000801d1310040f081c04580382d4440e40c221521800d20011142c0c9944840192202943c404909130005104d10481620b013181c0c10710036074049565189060f1602501d568059034250080c00c0d00b555017014865404000d80c44600900e0b00c940c0b101a01a40d40300741d813074030107021070f00040302003100350b110103030040130400b850300001016420006480240e80c3e14a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177082167 1250 177080917 177080921
    0x110a060e0609090406020d050a0b150921120403080a2a02090603031c0c0801050102030408030412080c010c02100501080c0a170a0f0305030604050705030c161403040609080c01030e0a03050904 84
    0x404040c00813850230042080d825042e07030040c182e880c1c1c02c91300e095402681c1505404207015117041c8030750046440075001e030004c03130700d00418040c40c07809010784403460100c0c140b10705c16400c960300a03103501c0c400240d20403001c0d03807000d0380c2164071049080c0039415010300c0c2041400003035800402070044085001040700b5540c04c000ba180102c94000004040e194143e000e6009046100302410200746240c001003025800401a1000e071981079000f107050900c2e00b020ba0480c00c8144c1c00560700484100041d03000c180c802e00400201303c020783c009160010b00b82d1001c1c0304503038059121440781d80142c2c02c0e5411550328041e1480072911000440c000c0058915107040c100088548000c281c5200c0142e20790400d9008009503103e81d0781110b0410266035903443c10740d8030384011501c142c0411000c011040ba00f038130301d42011001038000e02d00b400c080040021080d20356030041d00100042100840104500001004a500311040c01e10b002e00c5110011894140d580110320f50050038068081102c041c0364940e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177083417 1250 177082167 177082177
    0x4020604050406320904030c0f060614030c0109060903061d1507080f0402090105130e06010b25030503071209020a0e090f0703020f10110109110a060e060909040602 72
    0x5000b0015551381e8018211040d00111000e01ca01c1e007100700b0740301540b01c0180c01c1c01c0f4100018107503448940e03032654122440b0610180032580300d15001048004902c540c030414014040001d8040b06601c1c138001010310f89100101c800381040b0b0390407400d10125511412000441354084004100000c80680e0600c240040078007020340d6103c0c0e107506854100a10303418070f00624003601c0360002600e9026540c070500b039003103401039044107480004104d00e0502d1110900d090305050f800142e01e803602d04490781820741c00e901c40703082c0c6030000c00c0743c02246100d40d1051380804c41c0515005100c5040c0c1e40c01401c60b000050240040c48044444142241c02c03507040a00c296500518050209071209807a400a10058513480e0040c818501e92286080000501205591300202000c00040d00390b41001030340c2c1380c040b030908100700040d44000e40e038400c00d0086001040c810501080551416000d20a4002e0303640d03c44d10030003000409c41003041d00c60400316041600c003601c4d803820076074070350034240068850 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177084667 1250 177083417 177083419
    0xd08221208090a0605160b06060c1b0f06180d03090b040605031b07050a110621010503011407090513090b10090f090305030a09171314040203041a0402060405 69
    0x4081024030030410268010301d40608115594040c6540315202200c1328091300881d540140742c0090b140d00400d8041307110a0344050014030301840c051301c404500c1d090030002c80040c480b15401040844040c6031403100c0c0d00c1003100596170241002a8400450600c0c003424501e035018400c598164006c2c503100c2c0103036002600805207040c0d501d0366583d00091695100301c8601c0e040045214604e910118a501100d00c1240c200c402000310f0545910703034842c164070054005511000400500c00000103200c1c82c0e4a0124201c10400d031698540024142920a061081e140c0d1546c0da00400034819006100030083c0c8500b85e440705003132030005218000419000002400d07034001c1030108200000c1546400c002c0e035118081c11b102441a08106600382c0e4040e90000b004180c0900024180494551019805e680030300316490f010107594025406992042003240482d2802c45d00c240602d50891000104c0100b064404515624207502d4040d0b250301c0030f60200c064800400080707015551403a0a0324042d00b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177085917 1250 177084667 177084689
    0x9020f070f020a12260c030706110c010f06090e0f1f020d06120606050901052103120c03100608010302100c03020f0607020d1d010e10032007020102010b0d0822 70
    0x21030511a1045c0c048a0003085405001040d4240c40b11004007600c00d6145034600850422030b00303030f6441c0c0c05015040d210700c244603010f1201040c2440240200111283c40080c001a02c42c00c08200d907042d11000321034201d06900c40e03028103421740e20002d48540310207103401206d0103200801300080081c0c4240840310750054104100810780d2001004030a88480c41030000f00600d950b0303542800120807091040d035038000032045c00c1040443c0c010116580f821100002d403842c0440c1c0070101c801688058602500d0f00740007100300014800c00031107400142c82c840c1456800b5615550010315002c441035216410049902d9844042500070084040c5002030f020541e400b43c50030080003036842d031080300b80e40c0005411210240f041c01010a060f0103111042e500c118400d182c0d0f00600030154005125207040550b2007620100300d80001c1544540d80b20341c10025659a13249000080c2034601c2174602601c80e06c4a00d0b200306c00582c40c5000c80340c0007009010310300c107103044441008010703a010364000c02c0e42da4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177087167 1250 177085917 177085949
    0x61c06020714060601020105010b0301060e01050904060e1f03020f06090301021b0c03010f0b0307051005071b05090114130b0406052701120c09090204090f1b09020f070f020a 76
    0x4882d80c114070310040c01c40070444560707544100c012070a96600b0700c16040d807054208014402c1600c1500d802c03c16038418140f240c642180b00f00410100c411943c8100b801c4080b40082c400305490019920b121482401540740f01d150658001034017515007503490300d1050030009544211910290103640200007131407104801d17651040d810b90303100d40c42c0705000740c4a5403a02802e04075000310303071180840582000e0002c1843c0c81c145001e000703d1140ba801c100051007003d1200b440010240d00081c0401e01004488080c043e2038042800002d980681081c1c4038000c0303944483e411030b104c404000b556000742a41c04500c03040a440400d00410154010035040b104102c0100d81402c0c01c4608141c20312034404451500c0e86e61169a00500e140030040100382d2507006100304650300503604084102d034002000090458400c0d62076081002142004035400803030300e0030403510041d070b1040c0780c801003220180030b41c60405035038200006403040501c028500c40d0400e803800207541ba101040707006040c19900c03c940720 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177088417 1250 177087167 177087173
    0x1031d0d0c0302010c0309050a1202160b0a0e0907082e03140706020c15030411131a22020d021b06040501050c040e010e1b0f0d060506040e061c060207 66
    0x100641c24250055070900030b140c0002446407040000076604180075004181c0355981d45c525081191200a085100e500b0070302600c3d081d00910386005001c0b0690302070343d44045c41d5004c0c02c001280412580304d048001c00b0090125000080d441d84450b000f00001d400444903585504214404c0404240c05c142c00c84e004810821144024106840300600f103809580d5180d0301240c3e64042041302c01d4200171000b50400c45071f5550340103160451703c44c5007212540310710403002c2004004207090051840741c03148001801c1105804100e9452641601c80c9004031140321505482c0324201c0c0e00d030700c4000313a0018000c4104c40040e81680c0c0a00049a20390324540d0a909501c1d507134072415181683c1070f510304004291202a140c007240d0855503a107a00301810780c603201480b55644402003030002921101d074407500f0b8102d181401001103a083c4120561034480c81c101c180300310340d455004140034482c00c0109100c100310f19a24954025011100d1624045403042011001300420340e006080303c0c0049031080030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177089667 1250 177088417 177088427
    0xe0612120a022b090501080406090605151002060603060606071103030d0207120c170309010e0609030a090504061202040b150c010504060f0207030c1103070b0c0f011b0e01031d0d 78
    0x400c404aa0198200c8143c0c0c5800f003612114101880001c83c030020350410095003c5c0521962090151400180304032041e103500040d603004903400b01e02541c030000703511031516043c090884070444500c01060301d4907000b03010a6071150003400a81c418400454850b0170440100403a02c1e40d52005800e8a80b11000b08100c840a0b401c081400c450040111800d450b40c1c5102e45141c65100307030043c2c0035038089040d8200c19030b029800501548529501c80c0e150f00c42404040200340d0048001000459440c4030b890380c02004000242c110340d00c16400c00d4004c10200d410035403090111a011a00043c455041d02c0c0014240070780c1c00c3c0d140c28a00d9011030720030403004066000e54482c80c040d010074061003c03698014000c074401c1c0d00c03000780862150104200855010034100d025590081c007180c40107520b549801d6584c1e04511320b03d6141d40c1c404130314021007000038043c0c260191b0201c810342c80340010320000078080d44442c000f03880c100350340c5134000160311103d80d040c07080c0f40000d003080c0c4442010600d0004c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177090917 1250 177089667 177089683
    0x30c0c1207060b090f0103020d140307150b01110304030215120403050901030f11030411060405040f0504051c021507031b030c081b0403020123041d01060503010e0612120a02 76
    0x194040c58000000101d007000300b00c1905c2007a0741e020311405682184e08000790350b41c03a24010303604100034824800412404000070000c40380501c625a5644c4560b4803070f0740035251207906250410606105101d90003000200355401d6940c1110714515607120a45210003a02070010207905850b9058284028542c01c01b004100900003a45c0a0141d0380000c5046000d81e00d0b015024454034a0402c0082c02149030114040310f40074000b40f011b0f00d0599070b0380009098400f0702841605050380d0780c0038002045010480e00c87c0603041841c00d03480b0b40340703020b6010351201048000402200c04040001d4035140c42544526a041c0d0140701c00c600310300100304020003e003110704001d804100080d02142010159000c414070000b03840c18180d28003415580111100c09120118104650300d020780100c031007000030040c00c040e10102c284144140702c0e42840400c028010f900c5001030104c00c000610010120000c060740c04030040ea1071010340818090142d10304074400b400400000000b180800d0620740c00f1030500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177092167 1250 177090917 177090923
    0xa02010606020304060c060e01242303030a0c0309050603100303020c01141b01112209020c030702041d1501080d020102210403090f0306020d0c0f0206010b030c0c1207 73
    0x102540d00c40c0002c1e079491040b4000d07400800c0400d07407103400040040d04034082183ca0100040b550f06412080c040f00740907050341907031002d81050801d00403030300b003100c4d481d00c420704401c43c1040750503a0a0110340c81344200405c040401280f40c03010024540241d032844001c1001409007a174a10300315221401400c82d9020860043c0078850610146610582e04028500e020040789450300c041c5041c216000040d040c0010055501e0314110346035030780010040e181241e4059501340c004c1041d421800c220b00860741140141c2481802140c400c9140001600c86a0303605440024001c060440c100c1c1c0c004124801081003803191036108078410040402e0141290f00c0c80013102e10300e00720450241e00341e016214803039070103842140103007114440070030360175800500a041c46442d441e00c5011108210589070402c4d9503213a0009010415503039944034007a044002d034604410b01001000c402034481c14188500c14002d600800410803101e002170480390301c2040c1004031a0b1224503210391036200d4006040c15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177093417 1250 177092167 177092171
    0x301030209180f030306100e0906040c0e060304060e0d1d091b0a0c020301060f0513050c07020a030303020415030501322106010f03032709020c060f10060c0609260a0201 74
    0x10181f0f10740030700b1900980038401003801206076124824440100500d10380b04042003a24040d00e006a1240c0c4001e5000d45c1c015500414814031400207689041d1200c20390724208141017000c1d100881c000400003140100454807c80e15444100860900e01c001c604124100040041c0f4455104e4000d007119055600c01d4000740170030382e503070640074202ca6500e100343d80e040300305100c81f180c29803420ba02590f417107110b505025050034025004584180a250401c8001c00e80c0000e040c08605100c1220306c0842c485481d041c000f545c10130501211240303c10706d005035003440440b140c00c85802c04025400300044040c040343c0d611007074003e41425100f100e510307030100c0780a040000f055860307040c3d000b002a260551604082250101c10958402d04c600c003440c1184400000c000c961080940000c26241d0b58420081c091030070840f40300b45100070060260201541c040301c0400403560000c5041003242c1c2c0001000072a065030781087c844110208144d0340d0700d0400700041400c004c070454098040c2a50690003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177094667 1250 177093417 177093439
    0x1050d050f1501020318091e0702060108010e0c01090e0601140c0318060a17100e0c0a11070315150b04061707030b09060f1914030f0703080301030209180f030306 71
    0x1685c803407048a50081c15505030441161444c01c211000580056010400140030640040300c0c0f680868243c4030880181c01501c01080750319002d00450300d241c0c1e0001c001d0700d04c0700801c10000e40100a03500c00d40c11002008400981c05078000c1d07102240e0000c060300342175a1904040107840d2680c1c060314508003201080d01010b0b103241040d9007980c1c0071481a80703c44203001040d421011901c00002d0185c110344040000c04100d032030202c489180a03070782c1711054a84640c0c800c08050000807418050041507484100d0030004966074210300c070b0b80d0194120000a0b4000d51070b050544a0415821058040fa4001800150305602c080450b04846c0010320554180e1070b0603000b04c050703584000080342d000f500301d404600310789010400e0442040004042c0521100b00c01c8c1841040e14099000c00307070600c070f200522001d9003401d1150440328409100541030990039941c85030510701040c04064040c030f04c04400107998a981d92560303031401600030120b03110940c0c00c022031581d07540201c07812801001b001607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177095917 1250 177094667 177094669
    0x10e0f01061a0921071a030a0501050607050d110307080708040812031b0f22050909070e01090509030903070f0302040f020a021c09050411031812040303030b01050d050f15 75
    0x800d07100c000c48010000503080384400300605000140700010713010f602910300d0004a0700d60301e4020008512251000945038603101140000b01d41b016403100b4040c1c0410000a000102c002c10790010240103400d002d550141c00d120100d02d10f0150303400040c00c511002403d06e050003240301c090012150b5103002c485440c4882c0c1e03203081d000e0000b500d1110301d80d41d040ea0035103034001070b45000c0d15200c611484d01e6401c02248460040c042d44519a9103040c200300340006202c2402e24140451b40845c81400400440e80b42a41e211445041442492401562030340440c1e40840140222402c0c0280207046401c89a1a08495548400c6520040b8440c51401c0f41c1c10100154500a5031400c10700c4d034018040c58450854a015010360f0070b0010340c1081400c0c1c03400b1800b42d80d40d2050380031050745503019940301d20304011008600b4420100c0b03120150300483c100042690024101c5003583d0b0304d440c010580700031880060b5054051980507a000d80c7c10070041013401d4440c14422031040500e0000303250141d400c18 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177097167 1250 177095917 177095969
    0x3030f01050103060f0614090604090218010806360c0301080d031103010302060a090801020301060c0b090f070315090602030703051905040804050103020c0703120807020d0f020604060905010e0f0106 87
    0x7100c1d401e002d0712080401c001b454020382d035821480b00e4004400b450140e040d0002041ca0327005030081503241e94003141030350b83d051906407407280c0420203003000460b40c2042400a507616402a0b01034402d0903c0707a50000300061006c507019403804610705040c107075041079481241c45070000d00508a01d48207815681040b540303c1c0c0592042856000d2a0a01e1a400c613000d00200381c0c020350780101801601140000c01440900c010b6000f001d8696969107100100d10300340e00103a0000c1c018111070350018020410241010078000100c0e60700c208020032040135592004040e111442014042070320220421035441e030036070026445083c414011440b20340d181d0309200111034042c0c0b80904103180c1408140030302d501a60061085428032030841c0d80c9143c1da56141605003481c0080390b00020240310070b02c10b150b50100070301000ca2050341003484114050503802503948800520191030715490340641c105214080d40459500c03402c1505072001d11050b11092800781c6a0752140030a21800000d450013024000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177098417 1250 177097167 177097169
    0x9111e0304030915051308010b040606110d0c02031005070201091122020a02070f030f0209010806040b0606031909050f0f070e19020f03190c050703050a030e071703030f0105010306 79
    0x1501e541d0126400d04c0d502070035807010101500d0030700008001d0340360344c0c0e210018a04000c0c0741010001c61400d0f0303600103000945d01c80d0761000c400e20003444043e0b0617201020a41c0d0070395090b280f918881c10440760002078602000c42e113502480c0c5107402c003401006541900310402c0d681c061790000181040704810310181101300005544503010401603d40c00c10340c15001010000032520440b00419101e00050036a0364407940b0403900f0303860003544a401c50901c0740c21180108514005450302e403034140c95002c07040700c0c020400d40c41020000001513242c02524000045003c01e2241007000c0e0f00a032810a9559143c000da808031881445504005090001019002d0f00c40400300410551158588240344a5000c90441c0849030284194034404c10060040c40c400c51380740c144c03004080d01007854641260704c0b41d5111410080c04010850129400608a500748603843c90002901605031486500b408880c0d00040380f840c000158548107020b00002950180400b40740c45a856681c42d0015012103e0b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177099667 1250 177098417 177098423
    0x10503070519091a0d05011508041b09140f182d011b0306050102011512140318130b0904030513120c03050c09040305030c07060609111e0304 62
    0x100b0405038160802d80080114941c82070f0074848401074681840c007000360fa0000720740341055404510031001503c18010a401000490006040e00c145d061005183d8040140f01400c0c59100201d40c410803902c202c031450003003006040400405248a06c001d482c0c6d00706035888000f42d5208004224084041ca2055000440400003041c00d8521740c0504c001c2e00c0314610303211003035220700710280d8038a03002030003620380400099200581c0a18811005030498410f50403081c11685020400d0131040180c0f5121001d4803114081c0960450f01440d020400081080c03141c017090001040051030580d90101e103404080d01180d00102e05040301c4035000448110648a99201c1e02c248007003030201e0300540c014a0070b407c10044140c005070702d90a58400d01c203500b02d02119012900c100410500c68103002c0c00203889400c0318400d400d42000e840042160001400d2240c100b100041e44070200131680d8048130003002404001c0c0000c4441c1d0700042c00580100310800081040880e400c3e01520711401181d10407a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 177100917 1250 177099667 177099677
    0x60903111203032a04030b072d050c0c1302250210030507110105090706080906060901150c0204050a09050115120b150303070c03060f06050609060304050a0219050103050601050307 79
    0x9241d102500c5030a040c40040380e00d84000c40920241d0b078510304c0090000d1809185640402d00700181c00518418168500c00c01110980090350b80c6004504030090f200310721840c0c0b894844001d040c10340c0c01c01120700411544184034040c058400040f0f0340241400c5104280e80c030015a486458551000140341402507101d603c200812841502a501030340d0403d000c0e142c00903401200140d402e0031104207a03901101c0d540600c0781008074540c0014079540c0100e41e0340113022641404004544252010b00402d51000508641c04420511400740e00c45025001003003031141c0d0521101040003820b009409542a500381a120b40c40c3d01014141a42184c0101104221520150b260100c0d4440054a01454485070b1001e2208903a400c0000d80f0020340900d00306020140356240803c2180c2c403a15203000c1b0703141003040411840c0d0b02c9000351141c01d0402d4505079565030341c9103807033390412840180003036104070314820b18a50140141e612106560302a00e0421407038840d0001074443e8001150100d00040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 177102167 1250 177100917 177100921
    0x615010801050904060902030d0302070b06060405010f080613020406050702190f0b0309010902060309150124031a0d12030608010915020a0903120e01080615030c030903070c06090311120303 83
    0x1003000c43c1042d0744103005410008083c04282d002906081441c03a107080081d0f0003223080780c00e00401e00d008036001841214114542403618001902c250003807030780b0100f807003044400507525448e00702d81010552404402107689603116103010301503400042d01a40030b041d00742c455070081101c1c1c542c008e0503900c1340754a0060540c9080807040e6290710080c030105041d500c40000c034005071200005180540c40b80f8015004d04040e92880c800d400605a03c5018000301a00e85c48022100c9181c400501150b10718021505500150503082d412000a030030315044202c400c584418046200340242c2c100c00c90382e500b80b00c0c0711b640301d403140d09a81e101803000d0941c1a2075840c3c0b1402081ea035004240791080750404000c8241e41b41ca403041c69141d01e00054000c07510250980580c0e6030310182255203e441158280c0d0804281500320169000003002c3c1e00e0303000b100101041d0015020025140020f6109000c0d5074010b4840c400208840c143e41f008540c40030380300c0103494652500b8198402e121003950000c40c216 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 177103417 1250 177102167 177102169
    0xb03010b1605120d052a071406040809151201090c020a05070f08010b0409080313020307121217150609010302040b0f04050306090d020a031d0d0501060503061501080105 74
    0xc1e60060340e2880c09524803040810000340140700302c9851a5120b06016151110298404280c9500030f0603203003045140d886082c5403150082454950050312601282c6501007894620500d0301c086012803a01d1117a90204030400603e800240102401900c400001550351000c160721801001c004035030403e60b100040c061800341d03138050701002d074242c0304032002400703582c0710075040802940144040a000004c14002d03800c007401400c01c402800e80b0704003c820440d803101151030001810914150826072203400941d502040440c0143c0b0076540c1e01d10b4202d401e0300c1e001c94100421907032000401d25200c4407045445160010910034040e500d0194002d03180d020420540754070080409060581c20f12011071010307580406032451007c044043d039a2141407408140c1b604000612100c21680310032025162035501244440c0125030504205c8119012020010306900500c903486800c81c2c5145160303001d010054012604850058099031b4107900c59901d032100d6807194641c41408150b0401c010025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 177104667 1250 177103417 177103439
    0x218040f0816120306142202090d120e0306060d020303090103090c08030706060915030305041503091223092d06070b0f071b2913030207050a0b0301 65
    0x45000002d410310151000d9035510190010a000e528000959032441409000f01c50b50002510401c01c030f400d440304005100036030b915030102e042d9007400346401082158440d1101800f0080699120902c10011040101c00420001d09060958424130411000c0349260903e0742000540b550054055450a00c01c2001940a4500c2081c02c5078000600b10002400b0300c401e0018180582c494071001c10810301d401034800c15a050409141041115100c041000079007040481d07041781d91420075845000c90032141580208106038000d401005510300b689542640110024040b0b00703c0d2041c0c02007041d1120658807180941036601e50083c1031103411600c182e65030740c0701c402c4105010704040201407241011641c25001190101c40c001e00083c24005035a81503040e29034001c84a10b0642040c800840c0807820b0f060205002800c40e010a030f150942d5652120340078042080c0801c406405414092100d0741102c40805065005000e00200403545d40f03410012102203800c10400903003140d081141c1c0c404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 177105917 1250 177104667 177104677
    0xb0a0501080403030b0a030c120311060907050d0c030206040b04080105070206060f0d020f15130e09070e07170f01080f011104030201080c0d11040e0a140c0307050405090c070218040f08 81
    0xc6d0011404400100090b4a6441c05020f40815140502c000e105c514015203e4141da0144c20741c030303070400010840307484400070740ca00440781d0856011411130068202141ca041d4190000317504524005000300e03c80400c8070080c070403034a01000800442e96444022601c1e00c80a0352601e510610f07401c011321242c9025800c1ca60b00500007006050f04005113400109402001c0c2d02c011031a034004141490140c010001500043c884441c0780300403480c0c03600030180c0721112270007544407007480383c00410f140611600c0800e100b0030f591681c0c07915a040068505101d05400d1044c0b00b41803142001d045481e0384180a1400081412440c0504040c1160b0040d140d038200241800c502107001d0002040d5444c00d400ba0f900700d50410445240e41c1c03801c000c40c0604443c03006240d02805424400d00341c1c1c6102c144501c1560103200f95020a4403501c070a0741c12142d07032080b5817010f5400180d4606004005884030002c2c160305108030380300c03000c68154910344800200211409800c1c119511305d514041040280148 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 177107167 1250 177105917 177105919
    0x90b030f01030b2d1609030506010b0f0903010c02070302130209090402045006060304170c0f06100905130f06020d090609050f1605010c0503040512030a030b0a0501080403030b 77
    0x81d1000c2c4441546000d03584110020480c0315080344c0074401c00d07408003600c0030135540b06407601441704c03411929520390700e14043c0b050301c0040c1d0001842c0e00b000d0303542005460408000400910140d403825800175035130f49440c0404e03072040313040c940418000062403003100c0e05c00030080d0041d4140ea03200e4003000f004103804494003130445417402c102c0030f44400d6101142d014091400c00e41400c2e102d010720103424418030303083c0d868a441c203003018400780e650b4004c02d4a6000d03a0100302c540d01c02d00301600c5025240102c3c0700d4400d652141811248010001044040c0708940d000c00102c0203965864241c01601c01c142ca11034840d10f10900b10700049100c02031844080390003400058680115521004101d803c07107001910160760b0380715a00e04000c802c2c0310450421107800000c0c503607125100ba0800240d00c1c144515810301c2200000781042190920594008040c000c24024044c07101c0394800b900c075440403682074006032505004440500d44500d015081d00c1c01a556815560758654040d0001c2581e40030312 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 177108417 1250 177107167 177107191
    0x80a0611070b10090507020c0d0b060414010b0711030a080405091e040b090c0f060301091d011104050306070f02030406050706020d05010b0a030c020102040e0c07151b090b030f01030b 80
    0x9580441e24048016014985480d50f032841207251010748403c80d48058200c00454115001c401c40310b544081040c40c6203038114022084e0354035980009002400356404a12024540034000102e101c10280500b504502441681c10006c500000300350700d85120f448010650307403041c80240010305080803800d500c280d81031400c100844094100410100b0211012a11402c0100c1000b80580d0244008103d81c01c050314a40140c6a1403800180e190005001c0c0884055440c41012400030344c01c160301c029098968020040d21341c034180800c0d00756000d405601d0107880703031201140c902403180102010b085096400b03141028103010044030507510221054510540078441c41801d1041d5128044c001c04805102c0c50351840210800303019280c04080d900296441400104542c9601c2103426500c506081e088a40e512524608070002c40bd20034a000817461500411140307403422184001f00da5101a00c0e14586140d86804501052108807081d40d408005a00100001a1249802a007040e451209 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 177109667 1250 177108417 177108427
    0x41205030c06041506060e2101020f030a1505010203121902071e020102010510050307170321011d092e14041703100e0604090f03080a0e010501080a0611 67
    0x89500c2c010007990140c840300c1c00f12205600411517840340c04010203843c1000c6210744410300c0003c1c80031008090881e01c4411888031070305114820b604450240c081c0480c81078a904110700518000c1503e030038240c11686400c0004505580004151030f0f0000040c0c80702c041641d0f80e600100d24503031206011881103a0280405c1e000111034143c10105591310340c400e10380850b001d0000a0230f40f403028145a01c0890845401c2c00710340c9000c0b850301d054a80100c2c054085a0507030307580314a18440ca1041c00006a090003000016060381c0707400783c1c101c0b501410260a001d0050b604200e8040096501c0383c102d40c404038150000c261a20020040c190544280455403141901c0745c0703007070307804640c0b405110a034100700b00420010a003207805185280860105d0951401c100c0d642000d1559003c0c19225003903000c00246555140c0c0c0154680c01ea0103020318030a041d50385401f42148505851100400c0e080c00303a44c96804d0030510940741225240e00c024282c101c802d49980c4002c0010b100001c000b10400c004d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 177110917 1250 177109667 177109687
    0x702030a020a0305253b390301150903060e0709050a0c05070f0c0503100b1c0c050d0f06140403140301050105120603030702150a1b0804120503 63
    0xc2d80900440c0104058200c61081c0d0048403000980343e0404002d2500051041c44454092001050313079807007500c444400c1051035810601c43c007903640d9803031144d49881c00070400009064400040010540c001a00800348442019040381e203140c2d00c41600c1c41e2051004004801c03007100940352078943d50500c0c20140c0d0710b80d203c550a8800100b80186a03602c04041004000010b118080c0d21840c41780c0200322503a00136800a00900ca00080071340425418944c0c0700a00945108110041070b0007422103400301d2017040000f0241000c058500d2181e98060020000c10ac81259413480302a0301ca0980c81c1d20a0602c010130201c030541d003209460344101c203130300702c40000c0580c4905a600f1007424000242443d05160042c420707041e0300d000c0c01e69070390f0602c010004da1760032009884010603186541842ea9071540c0c042407450080c02c901952203442a40001010031013507000301416040741d9980421203041c4202144c0e03601001c0001030005c1800c2000304038819020b400200e0803031190054038a00203d101d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 177112167 1250 177110917 177110929
    0x3031b020304140d0507090e030c01090c05040b06360603090f0c0a0303120b040e0303070903020906040e060606091f021f0e06060d02011b0c0e01060302030610050702030a02 76
    0x951040564400202400400c21565020100c0d41c0c08560700e03501c205042e900c0030703250300d00703489140c0c000c544559200840c0c0105105442507600090300804c5082140e007403031050441a03200381c0d03000c0c030f142c641c060100d800c103c012a0a000703641640c6910040318049218038401341031404124a580780c5600c000c8650359440154006c4c04400000d0500c080d2382c0392800d0522401e20000c51240d0442681000040d4101441321040e9090010015426a035540410b0203440500d00c0e07100680000401c001c245034100327580c841904c0c0240d50b2406075030ba41005000403940042210442a4014400030707842d0300c1c05800a00d040c040160004600605a41d000031680c1d60251041026811044800522031522201c200703801456001c00e028004040340d4040e2139075005400580101c1515a020382564000c1034800805045240c10848040f42c60805024440d06030080b6102643e40600028500c1d21138001c1d01c2c002e00c402080c0d000c0c1e00d40800c00944080e4800d1000b285c00d80980007418025030360720 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 177113417 1250 177112167 177112211
    0x20d1d0d0b04110105091305071808030a090f0b0d0b0d080309282001020120040303030609020309030901180506040b0309060f07090501050f1605010606141204020603040303 76
    0x2096200c015042a03e09000440b40218000d4108207081c0000440c61b030b00c0d121000000080d065000035651505d00040b00c19010034600c0c4003040d0303503c0030700285100e1700000400c0c0c01c00407a559440b07090f488402c810913901031842542440d0006000120a00c296a032028003606001001007032040030316030b00c40c61150000c640801540c1c10016410350500294101003000e208030480d141d1b1b81c800d40351f903800c491b980c640707404070070028a134441c0141d164001d6000c0101070900c04240100c05a00d101307014155880741c042100000e00303187c80010070b1080303402500e00a00c3e2180240d410492950300440c0c40d03400c0311000c5406003050110004954513601e0040c00070342440740390326950f4034000f82c0040c580440540b540400c030612608200d801070344240050260307502407801540e1268000c1e0308030880c1c01040d0580c030700f0440b0304502c04100a815032000e412500c0548440b0300d2000d6a880c981158040ea88454101d441c11000007030041c580b890003140d005202c0d0500058281c40c003002d180401e869 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 177114667 1250 177113417 177113423
    0x25050f041502030c10020306031c0c0b010e0709060206010b090405040215120a0b1002060105060309070e0c070302070821090d1a15100c1b030203030a02071a0901020d1d0d 75
    0xf0002c3c030700e03c450743c0034060510040a001c07801e51070b50a204c2d0201e682e4141001401c2c00300d10b030b10400c85103d9441000f9801034540c001600c802c0c0d5503100e00c40020582c40980703c40c6c1c04a00f0503480000c900e40003140490495203105003080c2000c191900348006400010022a4440703245040c104640505001a00c0700c141e0a5402c11001c1c5011202241140c4550280900c981055035210100e1680000d0701815034400780d440e079440e1f80716100e01034941109a00700d00c1d1500300c003000700320070b00d032804002e0080503002e54222052142d942440c40d48450312080840360003007184600b540c20310080c070000c00c091600605003a0100c0707000d403506000c3e03d2000b42da04070050055002e0103141d0b4000340c1e82100380f0b0401c17a41500f014401040c090300303100c03101c0c0005066840c000c0c46104d0640200c40200025034024007525078a10100c00001e456030f90601940d0600b01e0400d208801d821541c0098890324041a0011320041d94001c0c4150b0340c1d0920a501c000260149403005941d035105c0d0028990400e01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 177115917 1250 177114667 177114673
    0x21021203070b07032906070f0c05060a02281e02010c06060b0d0b01030606020c120709020403051005010609060f03020c070b0a03021b0d1704081210050925050f041502 73
    0x503001c817a05502120030081c4c204501c141e01145440c540c3c82c5403c40703090f594040d881e00c20300c503854904240703d52251f520107640000046142814541c010402d05010b900c24014544a210f03e89040c0e5100d002d03442001c0c5c040e24400390740701c00d081c45819007503c080b401414410350703002d043c0d0354100683e400e0303030400b1508202c08070310030b21005000e0050300c030001e8013400c090054a0504070020b50f075052200c64148602100f0300300050501c41842032102908040307100399600ca0722801c25a54620009400d07448252414000207482e504ca00042400c0d541c1d6a135454206000004044000e50090b240e01d046d90300070f65200041001140d070080107090b20544002d40c40c2d880c400202c102620044039100c0c00f5800403140c803000c0c00d0f0b000e040c07400700041100c45854503480d00c4c10702102034010b8100d44d50941800c10207100310100d54042e003500302c1d841190400b101e507480e070380c21080f1100c410b15400105501310100e00034013070080010744507005600603081d040c541c1d1801c4800055000c5501030025030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 177117167 1250 177115917 177115931
    0x80a031e0603050f1b0114090301050906010f080105010305100507050d0501140a080303090a12020a080403200f031c0201111c110309070902090612040c060921021203070b0703 77
    0x141c00e0000303040313450050014081c80c2001010180c03000c3c80d00e5040700e0400c21180d00d9466003511401c1501c0c410040540200a20b14004004c00ea4420007806020003020a00000217100141400b4944c1a00ea01c030f40a00030388480a0341403400340c000501010148030301408401d000307843c10f21030302e802881c01050007688407001c4030034040078481c1500801c0301600308000700142d801c0001180c030442d907071040480710b441011810880c1813940c81074009085890004001003030109010b009a10324400c4207900b040c0c01c07080790411080e46030744100d841d05034100b02c0004407103d0846184051050540c0008141d840c0d503c1051240381d07006c0c0d40070390450b40103040b01420380c2c84603224240d10041034054142c80c42c2407400613650348403076a01c20503c0c0c00d600003450030a03c0e1030b040b00341c031280610481c03071622500303140c0b6040390b28040794011640081e0307403080d0004001c4010b0b041c00402101650000d4406180c94081c06242950b022102000d848108141400101c0c0c0c016800e2051b909070368005404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 177118417 1250 177117167 177117173
    0x213030b0411101817010608070801060503010c03090b0601210608060415050106050f030403120513051605011209060603050d05040e010e041a090c03070f0303090f12080a031e0603 79
    0x40503c4a40201c10840b071180c48500101c803005106094460302100140413942042039a4094001c0360410507040c0514a00001c03c41c0054201c80306540d400c50092213640130085088044030403c10010f41340b8115000031642c036500910400540700b076024604914080c50030440015a0402d901500d0b0326849041040244507540003140030580b05c0c01030034444c5514ec003000500314010a4110f60302540c0003c0843c08150040d01400d000c001c04041c244840d151461940400c1e00000360305990038001c4148403541003038086290002e90740140c54213a003400021680c040104903542003100c0c155980c00010000c168100010304009000e03941d01940c1ea030404074130050a1704103911100b0341e0034090b001d01002a0250340703a001c015107915400925540c800700d50500d48003500001a41500400d07030041050440080104280e0707001c2d03180c0c2010b2590790803d0b010050354070301c144d0440d0b101d4034402c6000640008000d1403064114940842c00065138000403400900340c0d510140f6095803030200b0420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 177119667 1250 177118417 177118429
    0x3010515011e080601200a030507051b09240301062d080a030806030c09010905090c030601050d03030b03030706050c030f0105030c031c090b04030605100816090213030b0411 76
    0x10ba105405100c0b40360764441d1001038034241010700300505000d840c450f484100751201c142c0d200702d000a0310880b01014814100902503606c80d240584050040b0031000a8442c0d0315003601c040600302030075007021075580c13a100740024483c1d00b01c82c0101e0554504c00c2d50701a5402d00894025002c000400c0c0040c41042003080c3d2140700c43c00c02101070501030802005000400701d100d490540e09801d144041da038440e000241040301000442c1e51000d084000440c071181039500403845945418115020301c0b414500f0107546020900c65950300c00c64410480c00003912a401c004012031000d41101c1c00c1513036560b158001d90b00202d8506100f80310100410401900f100ea000340100030a0f8064440102c01e280401c1d00c0d8207540c0714240b0716514505450364460b00c100c401d00000e042140959403030755280c6ca030040c080c180544010786004a61300c4007144000c00406d0348242041182d040340103140c503141040b00603412550506200c248885800000b1906c1e24075100c0c45540710740b603d1800b01c6401420041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 177120917 1250 177119667 177119687
    0x30803100f06080f0c0904020904020a030509060601090807030f0507080a050c04050105090402060d0c0915020c0f060906180301061d0405120906040b03040510060e190213090b030c0301051501 84
    0x801c00852005000c902c0d1120b000d04c9800c80d40c15190959100c0d00400070070064810711544ca6001403000803500c402c01d515903c0785014141c100c040d20354035140c91004540c241264007806020f40c00001c410000100c03288954412540301d00b046d500e941e0fa5030f40b00c55090400b507038002d131080d401c00c1081d00c071a884e182c4216805014120b41d07860003410300e5008129980940280701c1407a6554050707000d075640c003da540c0401440310306a4000701e050302540c025210341d0441c0020b4042c030000b0b00c0034403952134050207841103d0b0000d044541004036034400000384203070142216415550720307c00424500e041c0c4c2504034080a04845041c507034105032070320500c1c006800c030280724412424421100141e91b160300301c0c1c0844101c40c0310705440b40c640d41481130401200100d00740c40c4600c0d02d00000362a903540c0c43c4092013102d03900710400d081e0a050000c0016403040c42c00c60201c0800d408400e001e107401a40c031540d043c18004e001c60700030900743d4002c00d003141c00907598030440400c0c0015200d800c1d03900840ca22 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 177122167 1250 177120917 177120929
    0x21c051918030807030c05160204060312170f0f04020d140a0605010e1302010e12280309080a053c100c090302091b070c03030e01030b0301020304022404030803100f 72
    0xa00480071b0081850240071000d14468508007240300c29076071550441c201550308a541000402d5110714082c203492041443c203c40016800c0009400c0c941105842c1d12071400c50f2035a45044e03942d036081041440c0c540d41d04603038410040d03034824445001089034210f4188107030000a0705506100d80c0c95501c08004010049802415829400503640b02c00c040d04070038411348030254a00c0c26800042d04151410721040c60030b90081410b40c55002d11613110101c07060007612500c400949410056445547c604406827056000008000010001030350790a01c502e01103800a01e0700a400d190b591011241c4868a80c0c1607100c01e01c030508080a5118001c450b03071039810401e1205145501050580d10014040e150b4486c448081000d8600114101c45000364001e03d41c0c0074164603850090444082e10642d140020f1504079114800e0605208482c041d540042000c4840c184482d00304515441103444084a074030180000030020722400040c3d40103216580f485800c190a10078420240551076102d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 177123417 1250 177122167 177122171
    0x3120e1e0d0204110c0f010b1009060c0210030e011b030501050a05010801090c09170102030406050a0207050a140f07060e120102070312020306061902060406060801021c05191803080703 81
    0x800d0352962685212101c003641910085001c8000740d5540c10140503c161141d4503000c3c404440290300c0c0c042d4880f01da20582145c4505d103203910700d10116240d001901890002c035400c00760100261401a45811407000a440c011540525290001c1e0948003050200d62880700d80c01c141050060b00343c003c140c0505015104416003602d01800201040c0041c072a10015654039034421010390310900c075174006031442400c01d00140820304001d034001e5004a40549038545030502090744800b41d4021078202541000c001c2c1450422903d400d82841d03c42d030300c00c0c62031740b1807409180003c5d6824005003008002c0c640740e20f1001e6640c417050040301c078510000c40399664810007003200000d0f003200800c0300d030000c4904010380ba647c0303030004901c0c10f1280c0c2d613550504980c8000d81e41c4440d45e000030480c1c896031003403005100762550745144501742c0c0550f40c1c1c18a0134042000401109060a50129900003540c4000f11400b40940310098100e900403040d40d4007aa04664030b19003490340125007150419450300d02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 177124667 1250 177123417 177123469
    0xa050702030f03160206030406060b030f041a060d0212011d010c02010f050603150408090d12020123070309111003021b07050d030818150115050c030a0c020a03120e 72
    0x104058407464a04c0c0248107110100c00b080502040c1c1c2e211101500c2c040c42829030b00d0402601c41120050f089504075071240d8100048810100013440403030040700054084901010305e9070130070800b06c1e0f205200303070b6483d0f59402e1200d28038140b6002701c011540c6150000990024111002420745517401c206210322030030a418800c0c1514000340d00801c111a00000203072a460307510f009410340c8075031140716038000d600320003030b20901091a140c00000c8002e90000c102066105201001c141403104560741d04000d030703100080242c5d001ea001400c0c4544035040e103283c852000b10000340c0900000c0503100000c1c1d40810849807011002105004c18581c20f03000b00501e915002c009040c0314058403005041210040101d501003000a40352002c0c43c0404c001e40b01c0a80702c020003000c10850074071599400500a01180c0d88040c01401112440c16190014518100e1a09410333280354044200c101c1e00f06940102c0017001c120a0044411b030103686ea038078038011042c0d0b00d040001808542c004400b44450701d80d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 177125917 1250 177124667 177124687
    0xd1229120c240705030d0501050f0108061302030604020d060b070b1b0702130b060a031e0c020c0915060705030d060905060607120504090c0804020a30080f0a050702030f03 75
    0x6010041003100c0382c03402041540d000700c070341c818050410700400c1c030710012030180210080764200718180c80d400c0d40d245100e0041100111034450701510300c15082050b110100c800b403802c80c0c008550001d4050005450015200b04080485940381d20588030315001007844070402000414454002d003400d060368071003041c0c150600300940b00301e40c0001d108130101600003000404035002290099002003d15031102c0104401401a010780032180181030400c1d111031001d101c076886818451401075008141320400c0303100344084480301070020049402d02d150b031200c07956104e400501c50280300c0e034061503c0d0d442c40011401550750a80000746c0700c82c10081004107a440b1801680d5046070024061210641d140505075202e200d9604050449400c0044030300681d6049081207000301d02c03c2c1c8001405940d03420842d40703000c92051880b41080e0b01480e60480c44444111080c0c0320074021808a440c00e41c4214910459a00142d10480450001715844055281c107010031031148910101440c502001d610b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 177127167 1250 177125917 177125929
    0xc020303060312070204060f090209040506040510030605060a2402060907060c121403070f02150412140408030d0522032705090f040b0907080d1229120c 67
    0x80f031100c0305090046420350a540c0c40d600950024001d507428540d2940e20761507030001951001440c0340c0541d04060102d4030909040c4180e601c00c0c0003600b0384501242c1141c1d070f0030000d08005014142e00c10074045000c0394005124000481121880420560030104194040d081c800000e015410642043c2e10803c8403540100422218a511002c107800100c200700c0705680d112015603080302c030039502104010210750018103c40078400c450302100e06c000c0820104400d030030f80c11900201550060803520251900400f420304601500304521420300da25000400d00d150881c003101040a500c03041407201382e03114104d902c1850b607906100031500f0281a05c1c054881c21001050301010925803550a16135440310540002401000305000b8483c10800c51901b007208050302d05031030143c614804076814003400180c0740100d5103402e020303000c9035029040a40d8513260001024200030745403048542c030443e240001c42203a001c0c1daa95a004400e2000600c0301c07030001d001c0303d000903030f00c58401901c940c1e41e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 177128417 1250 177127167 177127183
    0x20a06030203070c0507031410050603031806071b031202030315220e01090c050a06080703050709030609030c061a0618040e06041416180507020c03100f0c0203030603 73
    0x50030056940e8485440c120b45440500402401a0090641c088100503a80004051b8003101008440c4040c1ca911101d0301180c41c191100c9a045e4820418003615400200045103100401010503017800400d440d03c888140300303401204e40c01889441705200301f14006d2100c80c40c4040920040d419490300100200070389002007070305480ec0c1c441007a103070020220f074081c0f07048251101e503050108110b1070b0708041c080c21201c2422107021480000c0802c0c1070034240c480b1403c0f28071540d00d102c826101c140064000b000b0113451441086090340010021850074091801c017240b0a540760080c03070845041a00c126541152203d032034a180c3d5000013241c1d0381d4442691212421640c1146c80c0010360000940213114401a100e9a0701030b500c1044180541c1320009083c060403241550700b50000408520503044c4140945582190190284000001c42d540700990110b00d0b401100d000310300240000389000f0504031031002c81600c4104d28401128140104c610b5002c00740011030031802e01500003502c600306 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 177129667 1250 177128417 177128429
    0xc020c090c0d0c05130603090201050403060c030f0903020c09150f090903040e010f0f06050306060a0e0a05031b04060e0c0708030a110f090306070206040c0b070f0512040f08030403020a 81
    0x30000100e1880969076040701d0b80c0702d030071003001c00100b80c005401812940104000044008410030300061807070080c011041c8055050f03440f02e2038681180e6544005050391016001016034405018100d00c5072440360881d00750083e0010280c800e02c1d00104403070480006d280745600000c2d510385840503225050213040c1c10400700c42207007690341c034014a94a0340c05070741d009404031060100001010701003050b688098440002c03668582035245c00059a0034441034603401d8120600304481c100e428807441c1028054400240b5513203145e41e4500c0002c1c603042941c1c501c90030310f0300020005505440d040c800d0200801c0182c00e80c00051030807100c07506060003224400350070400000000382c184c1e69a0340c040c080945005010985400941d40e014007a600400000c42c0030340700303c1c0c0205d407401d8000140c061007258400070303c40d90307241003041c1008581c00000c0c080320b003c0f8000c20894000341051081904090704e090803d030b00d45150001e81d04100c1d42c664029481900100024000350719000a00000c0c0c0e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 177130917 1250 177129667 177129679
    0xf05100605031b0d05060a060f150503010611150115030e0109050a06050408120705030a0c020610090b040207240b0d080d090c03050a03110601051005070b091f050f07030c020c 77
    0x60381e001240d802c404c540f400a01070b010b40e504019400380f0981c0400f003512410342150860343d4403a040000304900060021002c210b0910040200c02d1080e04078924035103103502a1071540c054240001e4501100303810120782050080d2000b581030750f1511403152400c0041c0700920130240141c030307102d032141e0381c42c000604450340300d030001028080540300301d462242c80d40c0107801852400300070003051500151034921500e0304104410403118030004029026031480d01c180c00d180d515000b01c040c000c010060081d60002d800f800042c2c042000c0c58907403501e0f1031300d9900120400308210515401c941c003016149104a40460300080402c02e00401e40d25203500160700060a007005040c841c00207032090740000c00f1407107407070744c2c0c807040682c00320798540641c6025040b204180d89420402040501074520980028403d1140d6000b04600340c142c1c03030f0400100e80903611060309501400f03101007900c07084101030640f00d0083c0444000c00066940d40000c203890300700a0003400c440004d40703c1042ca00d4041c07042c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 177132167 1250 177130917 177130963
    0x150b0d0504020609150a14090913170a020c03120406020a0f0611030910050a0e0a0303020d110c03130e010605120601020715030609060b040e0c0c0c030a0f0510060503 73
    0x515203408403000004010581980c0305481c0445d282d0a510450049000a038260303c0a144070303040d0020b40c0d0003101700828843c23040c1d842e1610450090f41542050303424032003880c0010700884a034001040c40b00d45550140021644040038149071001210100d010000100010807100d40e0210315007822560085100810380c085040a41c09884400c1b0092003a410000c1804000b150020745015103061542c2c0601030b541d1071309104000c451605e48510304d07030f40180300c0800010340b0a5004201c0201c030b0b0080054154054000303200c20346c206111066031584000750814520140c144604001e010100d1028055030502c40003c00c00d000d89010121500603007804241e40d43e000307102000c05091070b00380c0c1351004041500010098009841388000c9940703001c50202d105101d1400321802c1d9104d0345984100c58460810424440e030045550310341c240501e1500c2081580d061100d5200c5500411108a4080143c101141002d10b003c0d1080e040520340941001a520045011008041600640c100203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 177133417 1250 177132167 177132169
    0xc011106010303021e030706140411030714190f0803040e010b09060f0a0c05010f021902061b0903071509031a10050613030c1806080a3c15150b0d050402 67
    0x141c01404001001c081c20308544034602e800f500d849c1c5216900480e40f44052030a048141900c5803a68007c500c0c0e0020724010800c00c030308040b000d416111903051801d0035607540d03030b130f40304800c950182d00200d08642000508100c3d15003a1a44180900f0030f07611051b1410172074400090180c070800043d040e00d890040741d003010460144580325040d6802030b0080c07202241d1600d12070001d52200c00241070342d010349444000340a00c0018600e1007107041c01805641c5103240e03c0b24090f41c0d00281105507040c801c021002c95144582c0c405148a03030a20b8554400e140d007540f4040c1540590307041020b80d00c810b04020408805040c82001e41200c5003500c0c41030360740074400203112030320700e00760809051240c8007400001c001e100040c010410415072441005030f1a190600c0544a1070300d00c201818000b07410000781c40d0782c50740c00c4042c0384103944080c039031a4404c0200070208003815001c4084d00e201c070075900c11040760142d81c080d0103c400808400780e1015070800352058654003c05101e00c102d2030381c500001c1c1c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 177134667 1250 177133417 177133423
    0xf0f060412052701031a01090b0904020403050d030b010305070309080910030b0411040305010b0406030c090f140c0d060503160e06040b1807140415030b0d060e0c011106010303021e 79
    0x10222440b15200740c0c000d8402104030310011002c204500203484c1c00100c051841c0c01e01e06c1035080180507515001140c2c500544080c3c9a040f00e000300764850360800c800000143e040110100c0c103c4036403404070700d40c0900c00000d0120384004207003e0600d82862204400540f5060803200b028404441c40c0c0d0b01c0c0d902c09002280103000e100b01040c0c02c00d10305261000700c2441c600150080b40e101d04000e04ca604989001e110588503544001043c0c01c003201824000310300240c1060003050050000084c0b600000c200341c0e040e901c0f080c0c4040740040d50014202c0216001d43c0140c50160805500800c002d150445840e00c41c09807a2007980080d248131408511280d5964010340418040105494a550402c10b204001d0100990340d04011035600000d8101071401c06066400701d941c400800b40401e403662005070f000d00412041a540541040c04900c0020b94521550319042c207800c00803c0c1c075400500014081d41003440c8881c169902407801080001d90016844401d64813a038006e0801d0041890070a107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 177135917 1250 177134667 177134677
    0xe07020a0231020a020601030807030c020613032105030604021b0d020d08010906080a020d0203030d09060614030a05071a070506010929090106200109140f0f06041205 73
    0x54040400042c1e0300030007558400921491141c04040481e04110546142c201e00c0350200711005608203800400100d100707071020381030040c06420180030200340c6034002001c40d03000402e2070300444207003603080c000d10609903003041048102074000c0c001104401009411400000d00c041d20036500001c8091400100050559480e608201100c40382810040040d440344c4000c403000001030540c10000a90000a008903411a07800700090f08402515030280541420300c1c41c7c00b40c1e003500c41040700c00c2519405106000055008035400901c1c1410841404500094117240500c65030050619202181021460310101c62030b00c2e80c0e0002040c030f030020310582c500846101401c0380c0910000001c8a950341d0700800d4982d01d0003216001c88a1100050f210510000d01400381c0003514407005124550003140c0800e207250000070148040c000c3c43c184542980d1030031070115108014031030607500000e410805035000e00131040103030021458032020ac50384d442000300b000d05003001791a0111021401082194 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 177137167 1250 177135917 177135919
    0x3080609310b060306040b1b0c061003050607020c01053a02091005070302030703180906080a0203102a030207020604080105040b1609090209041404030206010e10030b010e07020a02 79
    0x54440c0d4400d400295145405082511010042c00c000390041c600452040e114550020340410191116070034182d56507220508005141c03820060001d032035608003c00c511422480290000640c118035020b402c0c403502500300300665120707a500c0d0120303a8201d01660a42c00003034aaa2130ba00329a0124545003e40507002400150388101440d905100550014004400241d40300031400340652000c9840c1c0c4280500540183c10600c81c800019205034242002071200006040d0a0703a00c4904c450111101940224003030350050410408500307080c03180e40c4860506840400500da5520041c020f00d50340ca450750a44981e00803525002c031406541036603003840d0058001621203441d001540d0091100365010ba4080000000040c2049251b00060010032859038840090341d00d81200c6901a40000311329542c06500c40ca010f80080d03402444962159000381d004000c1545040c4101c7c1d040b000250000c10b910101130f03c00d03c00301d0b00c500405411688281d04003481a81d803502d049051000100c1c0007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 177138417 1250 177137167 177137221
    0x2280204150807080a02060306010e0a0b0301080a0c1707120f0f0f050c030105041e0312020f12010902040f12060f050907090b06131401110303071d090403080609 71
    0x101055150a072507500540b0b0161040310311241d11522019520030a00c0c000039445102040041c01652041041c2c00d07070704034068445820584c803403246107042e030802d0f040701c00c0e140d0080d1981424024900c6281c001005a6040c7d4002c0c05110107a494841640b030240c070080b00008a43c0d40c040044210740301400503040008009050751501c1c08a0701021810426a4144200510a071452a042c842c89001e80d178450366120511b5624800c1043c0e0201200041d0103100541c900d403200c00b107542c0010030055098070503069a84030000300c61594000c0680010920345d2040c003091044955202014003a5036a040d07917210703280b03254035007034024200d0020011006400c140c203100d60138030700007203c13815158845014003001c0d0030181405010b00550090400040c00240e0401030030710320400080b0101e9040c906841c50300490400300c0e1840c0d00c1501d26000042c03100c1040001c00500300741c8003148200440382422a4105a140241701041c09482107125200c18004101d031220400c0e86c82a8072804000c80e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 177139667 1250 177138417 177138431
    0x515100906060302270109080102030f0402030d181e08100c020106050f182203080402030d08070f110309030a0c030c090b0a03060c02150906190b0102280204 69
    0x2604400484600c6080041820000040b6a0764040c4c0203680307140e0180f2020500300101c00d095801040000e1004c0b81c14084005c4000c64421400c2c0011441840081a5410310b400d184c4145803130700303107507003003000401c454020715400240181040c201110550000c550000d5400341c0555900241c551200350f40e031098980b400417100080c3c000c8807180440f40c00810119990b2801d000801000408280d80120325080110000030a0076280ba04156010114580c040e800c4800f02c500780c00d0000b0030790124421030200001c614081040392010340745071900098a04114101808480e01300e2444018008880300c0080c4c800303410010354035030100050803101044668101541060070b2408103540c0c0e1000d03c0004202c1c0381017800342d0044100060001c51500d4070f0740d11020003c011400d2818118000e0070b084400401041003a5801003904001402081c1414820311804c150140007131074181c1e0421030034040320381e000700c0c42c60f03044442c0c40802e0b05a413540180300c5c4045d46c02c102c40254010b10700b00c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 177140917 1250 177139667 177139681
    0x20c1003050a0501090b10030e0a0f08031603020f04050915040606121a0a06080a060b0403061a01230c0708070f06110a1106070819080916050303040e040515 69
    0x618000d02c40c402c02040140d032207084000540c1c2901100071b4000c00c035034030711240700e500ca64400a021240311094a00e40f01899444040c0c107510380792709881c0c0110100a0010083c200704103816695841e0404601d441031282942140b40210305c101171242401c10300054144d007002d810b080c0d40c41c10045c410028203849100241a90000804a25045207000c0940b0b6003982640c10450700d491000f0418040d0f940751a0080310700c01e03c02889003100075101c0000080e4030b481c0340050710103544070b102e01040c9210701401040050042624090410440408880601c0385410b030403850705908924a0703a2380c032148502d951034514640d0080e01c1c6481801c1e00041c80c108001c90240c10750b40d407030fa00e21034250300d9001284e644402e1000050007940445010b1036052400e44020082948100b4001c0d003040e0b11050030b0401c03003203060100c4010540d51802c000041000303004015941c08546505e036001130810001c05d030380c0d010303034001c0d10603c25004010909010f4100706203005049115401d41040c0340c116 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 177142167 1250 177140917 177140921
    0x80103210c02032b02030705030318031c0b09130b0711010b060d060e071103032215060e0a02070b0f090313030f0b0106030c0f0c0c05060d020301080606180f0403020c1003 75
    0x503e900c8104d50980d245029051010003103500d038a030040000c40c1103494000074007202ca0815500254984010000341c094803100c40c1c1c6891321004c14080028000103070006222650500901d07581d201c2607aa041c4500141180007020b030003820a1801c04507108560302c1d8140100340610f081a402540418040703102d0455030405000e51701c5400700d002203a141d00c0029181049041c10a072540c1e0400c0c000148951142048218507041c0b1556550b16440c140d100c4901e082260604000c038651110014400540f403001400d0300710281d90f4046240010701e840780d02c13501502801500c002c00100c00841e1400c001001626000c4a594815141490740c0385001c003900240001c08850242e502c2e0000540c880c000c0c0f0400e40452040d850340542c205110400f01c49040d00070b40119180c4a082c000403645403604005030030012030308400140d07654108484149400c000500300e601c9610480d11111400703e0100c449904078550f2810524192035601e000e9040c4100c103a100358004520090b1140225415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 177143417 1250 177142167 177142213
    0x1f09120506060f0907080a09050304090c031d0705010c11040b040c05030403020c0405070c0b07180b07050f01020315011d030303041110020606030d1d03030d060e07080103210c0203 79
    0x1160000703a682c030f840c824008619811207418010401040000d044083d0b1604144070301485130301981c0c40c00742c4032101001201c541c140410b000903a00c201c1c5c402410841d00c503400c0e54002800045c96030600e0680002d00400140c0c00040c0815020117840500e61541d801c503500d003c5000f0b00030700a202ca0b0b0742000340150000c0b00c0c1070300140b042e18006140d074223061042c0360048d4001d0792525144203580d100c4002441c80a1b100d03808210102d0031026201050340300706030184c81552915503942075a41030041c581401c40305070a070640d1042051080030801d0282e07140c0c41e0707002030a007074140c481c3c13210701e120415140a03801501804000200b104105803095071b0904980211800196080008401c80c2d40711000c50f8002d405901a880610f80303d406a01407155075914408035400c001042c001190a6030404400898500c0d01c2d01c800f8000c20003944c100303903442a5140781600e590345c5503448400c8008507001c4c0440d03402e100e540f010501d4612440540c1e41d040d401408031235054040f222004401212 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 177144667 1250 177143417 177143419
    0x1509020304031404080c1e1806030f120a030b0307090e012315010e0a05030115081e060606070204110a0903110103020a050f09011713110f1f0912050606 67
    0x1020f2003c0036103516000c00c0d1402d454000f00140f901800080a12854901c2071180b0205842040442c00081d0fa60100d1049170058054070392146003400e0044c0745c60101201c04108007604a900402d0101d403044007650401c00035450701003a400b207118080780c200011600100d503258206103c0c2d2010000540242e0110149101ca800c1613840d070b10700240c0c5900c8241c40c1c602c2d450342e46405005075584107050f40207214000030005c00210703958030300217400c4402c00c0d449024141d134020350400000c03e007807000800c40f000c1c0d50705220a4002008042d40c46060041c28940b0a8802003021019911680e2080c1542c03803009190513601d4200c2e0350003500340a46844201c0751502c00d5000368409511034000d540d915002501c5d19800c04c0d011410075803542c1c00a401c246e042000b1031440300346c0c0c9601600c1d01e5000d40580080240c02100a003040c0310705101907020b0341d000d61001c00d001c0d0125121040b0455006910303110103002c0c2d80084030121501410ba500c002440c1002041c02c000b400408202d040c01410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 177145917 1250 177144667 177144677
    0x30203070b0a1409090a0c0915020a050c0d0b01030f0c03080a030209030f010b031b0301090602071505060102070506040b0304140304080c041a1507060603060c0804021e060d0b010201150902030403 86
    0x40d0340009003d151150940b500d400c0700c103031804285001410703041001064590b0070a041000d4030750398131100400c4c000207051f0041e80710952100600c46c003400102c42c010f801fa602004030b00003135101c8103c9401c0611006020034843e100c040c042c4000c8070380c800003030f55201c020259501030680005029410032061144039004861808504000c1480b80700100000940900000e140301c0840d01e4485d00030034120354043d52900080c000040342e0744000c0800900c81c9a442a12030114030468003103e1005081700e05550000c5400c3c06169600c000707440894a4001d90503960381e0f128034200300d0424030044070041c14800881e0200d0700743c01c0032581c0281c004054500700020118250801e510040c0d11080350b812443c4c0c551418601095407008150b414020800810381c140c2d42ea0310042200d004860010001b060042404114a00f00082c8030002507c8490316244500c0c03840000c0c8a4801c0d022102c0c05655140030750001e5034000c0d004a401d4042c0080050182070f502e88150019520403a0101c0c0011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 177147167 1250 177145917 177145937
    0x20a0905030606030d09060e15040b03011e08060c030408121005041415102c0a170c1309080706020a090b0c030a08100314070e13021810030203070b0a 66
    0x41400030341d00c86511900d0f50303403c910f80d1800c0d10980f423010300d0308000381e0001c0c4001d0b0103400d40742425000348010081c201c005a42c1c0d601d00300801040050b84d04007003018140301b039010410700900294a5411044c03200c0d01c1075403a1228074054800d4450001d140c0040d5101c2010403010614a01d0414110b072810355040c001541d55403101c000410b0219950b100000010705c0154150400d19603c004e486e202d0f040215030805140440d881d1450000c2c08a0541c12250f29a0852400c0440f0110006d20b064040203000e0b206a021454690700c91041e0707640100d00901070400c40141940100504a8024101d5540c2e00c51b40c0c1400f6019512940c004000701c0d090810014641104404849410075850050350814002c1c0e001200c040d2000f40c071081c1141321625010000c070314010f0008410524500042005518181e54450132460051000e2654858800340901503120700e06000001c0710080800200765560a94194881b000c41e00b02075010701c00c050380442d4062079240100b115043d0340d121141d100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 177148417 1250 177147167 177147169
    0x402090703020703090308030621010603030e0a050907081f0b220303080c2b090201121e18050f071e060c060b030106090c02030a0801140f130f020a0905030606 70
    0x43e00c6512801400905003503010070105041102454000d0001080c0c03c0000f150200150f41600041840003840d07551202d0800416401180e64a901c03107040c0c8103600304518000010b891840000c102000b07100f42040000d001502d500611400a4612000480740d2a200d200d15801074010064503501c0d41741c25106045840c1c80c00c504401241e0b815543c042c0341d551400100549504652907110103500141008000755452034140900f12201a0b000203080b1030b0f900004000e1007800f0450021149407031860003c0001031500d0a5803038195050114001c4036940c8140541d5140b0003000e040382c01180786a41301600c1c0410000c3c100c80d845000398000000340f4441051081d4144280c4d00481c01c1401d00a001070520740000c00030210040002468503518940341c020396104807102c000581000451003101e94200140c81e000d803042580c1d40c540007090101046400d10294a03881c031a140f1002c1003241d070300e0305030451811001c0000065450300704110016155014602445210f4060400000c6113 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 177149667 1250 177148417 177148421
    0x803300108030306061303020d12120605030309040b0f0301020301060302030f0114010e09131401020301060f090302060a081b040803120703050915060f0a08150105150715091a0402090703 82
    0x5072404200a5840d68443d10204502da134004080d00039214458074002025a40e14594405c0f0329014804010700490302d858014105c2183c9044181c62500d072000130320007034a000041d15803001058400107001b0600800190903104a00802a495800000042503480d4141c0165004001076482004140d8079110a107101900da81101c80c00625000000e11a524000e604a40c112400c00c00031280d1365590385418088200303440001074140e4000004004144c1e0082e00100141360340e19240c1581401d603400204c8134898180c03088200000d120119840a908404000484010660595440796100310058903a0440340c000d003000c1c0d810700000b402070f0303019001e01c0f80301d104100e0103000108813001042134044005040241c1007a03451035a25420348038078910300050211a8010a91000d500090081100058000c42d000700d0f00c42c0394882524a1030400e0b070b01282e5000d4a50089601400710310002081e804001400d170605501c803003240c07210100d41d208c3c0514000c2d220000b40d69183c800641c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 177150917 1250 177149667 177149669
    0xb010903170f040b16030e0d050303040f050c060304030903020312030609190b15030603070b090618030c220f0e0712020409140f160b0f1308033001 65
    0x1201801c041000e4807503200e884010054000590003650505407158071007503803500014180101540000c0d1140185034004d12040c6011604446403402c0741d00d1a0b890b1500c0380806803006183ca403444020b5401c00c83d044c402c240c412807000c0d100644a14150500900003402884203134080d00598083d0000703182800c0803644200c5004c0c00b403403a03503220b003010300e004603184109a08009a607055112582c1c0e4803014003409100c071021000d070f200d0801404240c2025181c2d408100b083c82300b0443c1482d55125034003a14001c1142d0300005200721320030b078082401c003140c100c0e0150340500c0c1148500518195003512120500c9480020040c040c000420403003161414511203030a40c0c040c01e800c12201c040301500030412480a000400e01408941d606002084900c40e040c0351500018000d00120100708030f41c03c032034250784c0c18071241549401058070003441000c2c050140e00100140e942d079810200b040c000014100601203035962024600d8039040540d031842d071500f0810b4079010700c1380075800e88481d8038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 177152167 1250 177150917 177150923
    0x303030e160b070311030f1308240405070b03040305041707080c0d020f0d08031b0a0509040b0d0c03110307060908060606030612010f0c0e09090d050f040e13060b010903 74
    0x403509080480c1d202c0150071004048040100c800c1005104807402c0c40a004643d02c04280140c4130086011060102e01c0d0075000071481da0720403403143c4e44019082c1e6090340049078040000620361183d042640c108041600910f480c010004240420994004010300899621118101c0c0010000b613071641c03504100c1c81104225440480303031284d54513020007001035951006182c003011012000100d03c24000702102a00e031920040b0030404082c407050406404400c90388843e51804000c0003001d4a24000c510406000d103980b000074500c951211110481040d070132a0f0302d24401540c900e01291040a00724590780030340200c00b00061064005c8080b4070136140f8840107040b050781c0d075405004040c0c0000740030590000049504000d200c0c020301c04c10780e4071170f5060300c007241a4400c080042d0a000d803290759680540324130300422002120105a090860f100d03440c0c61a070b11040307050070200314000d036084010b0300541d440c01e00c0040604503c0d4a00c20900c07a00c014041103011400544208000348000703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 177153417 1250 177152167 177152203
    0x801051005090a151503050105060307141b06041b0803090a090c0203040312051908040f06110904140103051501031205030402031c03020d140c0417030909100303030e 73
    0x140007625010546540c0f004006030700103040d083c1c0b02c2e548480015141c3c08030031948021010003143c182d250240b00c0c09080d050341c00514500f00894001c200c84400c4100c4681c03400007041c10560300d10602c00807211711202100701d0f0100e09240c203000c2c06c5005041d42c003d909040c0d030709000920b404040240c50124800a010780b071828a0405100085d080115800b82107000401010001503888245203410790401d03591030fa20f58411810b8031000c403510151f82c1c1c06108103401004002862103012002095011502042c190110030343d2621600500394050b512901f0701d0018811040402c4901d41281d000744221aa1052000040c0703181d118280000707800c0244110034142ca01d070040c0025900188058202c5911341408000540050701d103400e8200000d400181084040d6014010400c001c7e4008000c5401800d107020750364010f2040c0d210345c45a9641c20545801c09010510548411f018060300404051905c4042514042c4460000b100480d280060b00c6541c850002803800c04181c041d101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 177154667 1250 177153417 177153419
    0x3070501020d03091e1202060702010b130c12020c0c1806010504030f0302030403020d1a0a060810090f0b07030b09100509040f0204090c0b0c0706020c151c180c08010510 74
    0x842c00340101d42020303201001712103000e4800c2070b42003540b00040740c01010390740f00803080c480d0000c4c204000500207004580c1411070f480040d0340c0b8805140c0c44060003880010b9101409002071700c94550000a4464140c400b1980580b41440481c0c0704001a8003119034000b80f80f1031141400d40540140c41d1180000c40030f10052000452040e10701c07180e00d0090040300d0800b0b642c0c2c0d0018807241c80c100e908a55a44a11a4155a0300d5501030300c5d54004007201c5c42401400e040c4082c0c0e80c0d55120602c0c03510120b0f80c5850400c02444011200c103840d540d0001e10304a41454200406030241c102c209000b07020780035a03000540815440000c2070140c0380000c01181c21500e03252903207211315400080c1a03038040d5848500300c0000d50b03d0a140402891001007540e2a070640040e00b03414414580d0107a03042d90032025800e03106503140d403a8544072202c03a00c5403a4441607000d241003001c1190701e00c085001e620b4203002c441e11005484140307612a120710b000000180c1c032422464203951042d54513036200078000e40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177155917 1250 177154667 177154693
    0x603051c18090504020303040e0405160e13080a0c05030d0501030b0f0405030a0f03020d0516110a0b0a050a09050a030302091e0f040504050c040617010f0c05041e050a06030b03010b0307050102 84
    0x2103034000d8001401c880c18603071200769481d4480d0040e102210550f0cc0010011148401d00c111400200040302c0301081e2803420080680980350140c3e0002c01d007040010314020a10b0249140608881c0c0240071030303807a800c0784234408004045c00c0c04280c540340e0302d003030024045d4004000c4d50342c403c507408400395080000c0e100040d80c3e2031050f82448014107400b413049410140c114480c1500c201c03c152000441c040079442e001e010551138105409541d005490f901d004941d040c0b000580220104600040759914a03400c0402001d440300010050f00410f65040f05046e85a000744c81e0b0603108481101015604540d015240031034a4296908140000d040b40307118900f41d17000a41c4140584152103071401d00b00002400c03210b158004003510740105400180000091050148404001c101004121340180014140b8048c3e0310070030034640700d0800050f411343c8096542c003004000142c108243c3c6a1260009805040d81c40c0409001e50719219800700a86000103038041120700c1a0050211900906 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 177157167 1250 177155917 177155921
    0x1c0b150f0315120c0a060e060405090417030c120604090213021804020f04060324050d05010905030f0c0f0d0906030b04060b03070201140702070f0b0d0b03010603051c1809 75
    0x30620600c0b040e07248103141040e2035500d84003600714980000741620b00c407668100440d00380c003a0803060401c603d00d803a10360b240d201c0c03408540c140e690071110445559101e00d030941e0100c800c2c00c110b030384241001c0284501141640e001d0016002d002d00d40c1c803202e60780c0000303000c201c400d07084000c0e500204003449041014595401403d00640102c0c04100451303403180401d00f40d901030f10052032149800a003c00c440d03a80340c8600c200c008441c4011806a16815040c0381d100c60b40f03405858482c440c012081c60030004258481c400240e4000190380d02c8840c542a40704898004948510300c90044003c01c6448603804902c0b0102404140c0f1645503240c286501240109812500d0541003030303583c0c4010510419002c055403103544940e001083c840c813660500d03c05144060560320a66200c108103001c0c1060343c2c0034440c1520303243e100d241d851344501c00c018009400c41e10802900355180c40307400300030b01c8000310310074045031070244240c09828603050044070355251190594040c200c5100c014022440301e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 177158273 1106 177157167 177157171
    0x904090804091118040b0316080c0a15120b011701090b010e09010e010306050618041a160203030105130e060a320601080a111c0b150f03 60
    0x24003070001c11600306000c4e90380300760348401c1c0d103545540b000c01000c0c07003a070316100035000d405a1b9103001a88848440f041d450281d00c0c0b4500100e6941c905075285203030742109030748802040e0000d4003100000c0c04010105c6041004000890010171984001035003e00441100062401c4414001404820502034118007035180f2000401007034000107a0141141d40011001c1802e03a5040c000541116103a0303400c020b0a641c12042c4001e000c250f0b58030050350303486103107206125200c8034528800301e400101040c005900c1000140140e0030b00400304210582000000314948801140035814070b1001c444420500e0f50300c500404100c0040b44801541102c00250100303150a0606020100b440c010006414055150041421003080798880320150f407503003040503200c0d00c0c91480794030a20000500305240034185464201d4610301042c40c0061545401c2456141c4803290082e10216000 = true := by decide +kernel

theorem cover : BRFrame.Cov 176978417 177158273 := by
  have h0 := BRFrame.cov_init 176978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176978417 ≤ n) (h2 : n < 177158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
