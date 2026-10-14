-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1912
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:00.948741+00:00
-- url     : https://prove2.me/submissions/1fcda567-aca9-4a53-8b98-b09c933309ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 343705035 ≤ n < 343884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 343706285 1250 343705035 343705111
    0x5031c0b15070b09071706040204050c0f0d0b120a0b0105040b01020706080f2d0601020c2d03030408060112030e01020c0108070e030f0f03070501271401061a12 70
    0x410344d58066015140080c15031003642c92440504d0a09918040030030464001e6000742c4050240d0340d528403055410303228100c007191030070070704005150881c61143d21126074140000c01071f41482d0080001d1500e4108024016214801c080004010502d03040c07250b45940102800605001840c10901038103034080207244e40c4280301e07003100007620000b0800d01c481e1044143c43d03500100708101e140388410715a00704d404501510405a8090451510182e0740a00340707101d0030900f040400c0c0044c1c240031031a51241c00c41d01440240404030300090203021040c064140e05c0c40c1b4038003030045414010665111014518190742001c0c42c4110281d030b001044541c41007a070b060095802803483c1c04203160090b8000000a103001d00900000c903a40080014a0780364021002408413180c08500d252404803005040f100740b601c0c08940c403000901000d1781d030400d07403402400010b5082c3c1d10a02425004d8151244661003103000500000c0f8614617040d040e0050014a4403010303031032040c0b8003024070002e0840906 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 343707535 1250 343706285 343706303
    0x90506030f1c0507150209101110020c0309040504060b010f050a02150402030a021806040f050c1905210105130c1202090402090a03060905191110030905031c0b1507 72
    0xb00c001c2d02820031654030540c403c404e60800e0161414150003034100140083c8184050407249a0a5201e25030045c1c2e0402590302030001d0002e0070802800035484000341d04400d00040c0802141a9901d00c50340c0d2203076000e507074040340c4000288001800032001c0010079003400000e0108100c0d140d0b000901c0f120b80100c0000c021625140c500000385003482e1500003c0d80010a0480d0078440001d0300082402898241c40034000841e2158411040d036808444445628400340b18031210300e490401d144410f6042ca08190b40f0749149401014162078072601041d40d01d050a0004002c81e09200c00303208482c1048034020020084980402007803a08296140c4101d540c01251400003595150304542c9112802480c00c1e85250b50b80c40c00001502c5000c03003d440c0c41c01611300c96100b0707800044600541c2036000707511503150214103003040303008e00d40c040300341040540d10114000002c00400003480d103189407044042d071044804150000303031040c0c28460f5002c0c5108007084180d001c0e01505803041c5640c400106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 343708785 1250 343707535 343707583
    0xe0105042a0e0a05030f010e01060f06051204020f0306040305120c03070804021009081b030d11070605031e01140a06030e4306080105090408040302040911090a06090506030f 76
    0x3680d90f89480e00300660600413403074884000c400561000c8454115800248407055545010341d130140700520952002c98810480c510500c0300000b04103501c030384002d24943c5c54010103800300b0320302030046508070042840003c0c618050002c058120754003440610b403043c034501d05490000d0a880002d4402402107100840c00c0d07004078010902c081c083c2c03420700229808605085401300c81d0303282c0e0b20861400b0340101c060002d0300394440c000941c80d501c10300c0011300b01a8070300b04044465500041c8000c0c0b10040040035803c94801d201e60041c02070602030340c1910340c0700300c1700108020016598019424589002e0300201c44c80d5010424900c0b01103030700c80444000840a81c2c0780800003000c001035684040c400b0100303442020005a81080e2117080c1e6445203241e07252820720100142c161005006003505120410041c64203401c190209440340e8408418500050041000c035241a1220f445654844400b4807400605106850f4400c404400800840a900c9551070310780300e00e16418903659170742c2011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 343710035 1250 343708785 343708789
    0x1140a030f022e0908010203041a04030210020703090617040b060f0111070f1a03090723040f021c02090f01050a20010207120804171809010e0105042a0e 67
    0x40040d01441c0500d0f50381c1000c10195000121002d403100000b00e440304d180418800414401e07030340b18903803180d2004220010001140090480100103c0c00c501c41e0a4038804240380c00d0000c5e0003114071a44402e141030b801c21101408881c2c01c0410440d841007140c00308004650400002c5401c4403041d81e0541d804042000101d13048034a0810620b150321079184002842c03129801d480c1c0441d00c800010f034141c03080202002d6000d20080d1510035069015590070f0244035010f40000450070750b18030f10070950052040c08107065400b61403c100c03885501107040d0380c1401c000500360352441c10f0320008618000f161000540c03900b03d55000070741001000315000e02414083d801c01c9001003d02c0c603245024062511203c0d000c8d51110004580300001e545032030301e01d107000e028883d000f6540080b22286001c00c0c503d501d03010343c20180100707007140b40d00c622403c3d0585400ad44c55010f04603480c1c40344a00d6051034140010b5a07400b400803104800d400200c000304550304030603c0c02d100e51a1410220388102c0c500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 343711285 1250 343710035 343710049
    0xd0204030c08030304060b060c0d08070c050f0604050f010b0d080306061201090b030d2d1e110c010804031e0504180203040311071508060a0b070302060702010501140a030f02 76
    0x80205030070708403000801d070b410000015603c50b070300c2540c09010038504101800301d43e01130004008041d61001c2450707580240507160300703540402c0500e402d400c0c144d01070300e0303841c1380061038a0203400c6500603006102c2070150074800d00041d226500000e0007605090b0021a0000c0d011940180c0052400300c04182240c2d00e00c0221482d010880600d220b0f20350715403100c2002407440505080c420b100d44000b1040303041c0509a900c40408440020b0100300400034808002d0104400004003040042e400152000c1e09040f803c00700da10443d600e20000c2e800e041912450008881c020b1030521211a04100c0065803080350b445625032201c1890b61500d02410342034541e8001c1e500111805084080084c0119050354003a600c120300940d24481c5282d19a404941c5408160203044800e04006000b0b0b050f007070081884c03e030070010140c41c403070201d80d036200d45c0006a089102c085005030854814810741c00c0d8240a410b000d48000060010043d030000e00040800e01135201c01448000c0c0c40003002c0656541c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 343712535 1250 343711285 343711289
    0x9040509010b10051206041b050912250b090604121103070611010c030b2d030a08030415050c04090c0203160c1505190c08071a010905010909050c04020d0204 69
    0x1500d800c483c0540b803980642141c1204500701108400080052118905405941415445800350105002c45024100d8842e8031540b0616089400114401400e10f000c104000f07e200c000880c41503d40300201c90030001454617070107440e100009100076003059403120200d070b0889048a0900b00b42942034039141f00071000c410281c5505006952000400c10740100c010300441500d0300007048030851054050f801c444070880320a1700088090a0707241000940d1710041c01418a540440b0080c0e080000006d1070907001c0041202d08100c04000c1c80100071100d4092403c00030051828045c51810021440b00c074010f83c45812880340d140e00003004203030b000b88103c0e00300002c854810000c107403240c01e09800440b0280306220030314030700b1019140709512680c29104d01101ea01405001c268007a0000c86980f5101f90040d100b0060070408800024014414011902c0b014540e00080e07602d0b040a22080b114164000000300d403c015201000403c0820000d070030510032900180c96200000f120b800071701440d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 343713785 1250 343712535 343712539
    0x812030709080d030c0306210204020c01290406050312030a09150c03090b060a031e0507180606021207020607061104090f052a0d0e1912120c0509040509010b 69
    0x2c0f03005107030144d041e00f1080e0852800c0c0c42c10301c021039031103180084210803074004219050080300c1060040c80e01c0c2c2c00803c1740642403000403805112500c140c1c48032404101c42c0211807442c000e00b25600d400c080c0a400f000b464224040c1240e5250740641d456a031000920b105031542d6292861800c0001681e40c00071410000360382002201d410742c01c00b8008000315107050b5404d94849001a02919080b4620750980341d0021a43d01028041081510044e42d2281c01b01c4040c05401c0380440c0c0070942d82000d1036a000c0600d00411800d01e40030020f401d200218402c04e811100400c694405a00c9010480340b00760740c0214000380f03201074072028085d40c0c000c0b50440203105082c40c614031011045034224a01401c000300d90050340755505182e00b416620201d0f48840801e00501208100108a6004c54051b0b10320005690381c1006203448243c03060755204007150826400000401c0c85548501031480b02145000100402e11310904081c040380640300c80d0070710840d146c20005407410000e42004a2817040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 343715035 1250 343713785 343713793
    0xf040b12180d0f02072c0109020c0c01050d090b0f010e060906090f040201020703050d180e060d080a05090904150b030f03180a05030d0e01081302011b082b0b010207081203070908 78
    0x106c82402e0b802141006c0e10544815044000421203c10030300c200d68029480d580104803642e1590019125a003080d9000e00829503a40e07800e001054507929240e11900b8944000202581003000000700c514010308024090100c1344200051a01d8410b6401e4102c040c031914401d143e540e51004030f10708a0550030003800c0e80503840642c003080d07070401002034182610002c822200790310303410010f01c111800c03540b0a0b44400b244407094040741101004140d00c0c911454050328003000200864101c0c074003901c046421000d402880c20b01c0546511500701a40f804a02411078170b0b9101c180036a80340030b004003904410101c1009602c840e607078200000d00416024041e1600c59601803005000103104c60181808103200100048102000c010f11100c100d90584440d07484000300c2404c20106002e85900f2102002d081120624140f200c2141102c240820701405400c4184007828105540041c060181550b0040701c2c180082c150105844610f4800c45003400e46a42e11854110743c150304540c014009405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 343716285 1250 343715035 343715069
    0x140708091c0206060a09050f01032d080403020f010503060f0f01120905070501080115080c0d1116110406140402070218092503051906020f040b12180d0f0207 69
    0x2e008070303805100e0304045440a0900341e9400da590290796088615483c0810030100510016070282507500320b02101c15a940d040303204132031080ca4050800f29043d681c1100128007082149807a040d0208184421b1800c80c0c00d5081c071001280394003400b80c0c4090f00c1445e4039a2490440d0b4401c191600041d40407030001d0101d884281012a150710b418050140090300ea07800205040f101034a42051768107a43d0b580b400e0f20703a1201034001580c3c100c406000102901c80d01d91007103500d2804d0290076004001000d0701004001490309030400303107a2114040c0254101581080321907444020141c0d40d00c401d40b000352303540d04144000782041d1003d0103808841803400040c0900c0742c500040011488c42000080c174070244032445401c0144141e444024401d078003112403a540c1b41c80d10b8403403001b100d20850300941007000c5109044001d4009411a0f1108000410307482c401c2041c010303000c0d80200e1400d1a5107840c16400260f40d8458501e1140d031010b220f030046001800d0751082020100401140c41c0d0f07406900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 343717535 1250 343716285 343716287
    0xb01030e160806180a08090a0506070303020a080609070e04200c06010801050a0504120f11120a0915020606011b0b0f0708061e0d050102040e130213140708091c 70
    0x10005002d8141144642c0380081c2d40c62840345a5000c1501d140d00040240e081035654040069000c188900c0d001606168001070503124840608900c900c039031030150f01d6900144004010280040203d40700f0040c4109102401e5040381911310034240c250b03004601c1c100d00e034210035074a80d095011400403500004003030854840200b0501d0686413194024401611490800c1065450958002d070402d286948030f403d1450080254480700503090801c042103100712232803203040405076080d12104c0c400005100b00055440644040500b008005801e24445203042c000c1d5907100040c84241841030000c000d05010034010703d900c0ea855404100000310746412920490407032170690705207000c41e0108005c540146440c110f00001801c0101c00082e250104408000d40482c41c510f064a5039517003003002003007028400c5586c81c0b00d0310380c0c11840c02c6005824030500c80d0005400400e0f41c101442c0c03551180e41c0840680c10b285d040a00b6140c44081a222015494200003103c042e8030452207821003441d01c1c50b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 343718785 1250 343717535 343717573
    0x6010509040f0c061214160518121509120d02030405150f0115020a05070b090a081906060605360301090c0503160803040608040c2c0919060207030201020c0d08090d11100b01030e 78
    0x190b05581d482c2f032544980d0209580e03102c9140300c2c1010800c5c01e02084c903512959a01442e4024014421514103108122182d01c410b5803c2e40c00c05000b01400c40188030910304403414400c034000d180b00030048a60152a45511444a801851b540e0b41c000500c42c9010350343c1e20340c0d88002d0007000c41903403015040046030042d558030390307041140d02c81c0c1002800114940032740113131036041076055203008081038180d01300352101480e051022414203852009d040c842d2401d02c1640151ba10a0110085260404080500d011035080505105420f2103105001c010404000e40c0c044812604007005d041d291031070180013001454103e000c416006005004e161404428811550041b0322940c043e0394071005843c0d0341b0b0f10032401c0380c040607100005040000030174690040c900b05019200050078401203003034060400048a00d2070780019012420300003144801d02404c21020004d00b0304400301d0945016440d26084039110310b41c00d6541c0c5800940f0399174001d400c09000302034840700740c6d40c0040d080661500e07a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 343720035 1250 343718785 343718803
    0x703020a09051509011101020d02070507051c05070608070e060a0201021e042304060306020328050f0708071206090c02190506010509040f0c06121416051812 69
    0x78180390400100c50401001c50748812002c88035041c5003102000c01900c00c4010056005443c0d9420000c800c2401d05900c01b03041e82520070805044458900006c101140000f003804200c00da011803070a60026400140e110115881070074520719691f6411000d45200341c20851150308040c001a20310406681135000708691000c612903a003516401180c0504140114044d00104124070310b898401ea081c0c000c1c44d42c902220003000402c1d295204d55440d820303604141c4082c0b400100c42140c00e020032802501040003070400c11000c00051405003504401158090580c4060052480100750403500c0303a942c003000030900a00c00e2104556403202000100b51003840034006001d1010500d00907907008400e40c2405401000400d00c41c0d0070101008900075010304201c850b621002000000103001c000320710000d21351074072080d01c07a0760382c0b0307240078140c2c0d5000741d212002842d00350400007080620f00b071032554909145803545d01c6504013a0341d103071000c82da10000c5a122208918402540b4000125402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 343721285 1250 343720035 343720037
    0x4120314060a180f09060203010312050304050307080a180609050a0b041d1305011112010b07021e27040c270209010912030e150705060c090d02090703020a 68
    0x4a10100041020340e9106981d8140e000c085010100711840d070b03100456910300d079107450000e00b0403415604602256000001101c401d5000b1004005100700500300843c0030a560900924528045d0381d00c584034415030400038916880410b0000845105544002004c5400389043c5007442e00c85078050b06081c100d05c503440c480e854190001ca400c026030001d40d0126154a46000071103042295040003444004009404104107075030404040390090050520b0340c40411003186d562034000c440040c5800c07058000760640241080520700580b1422661950320024001e04c00c0c0201c034040000301d2418003901141d00310aa01940d8030340d805c3c0520402402503200702680001c045d520004203000d41e65070701c030034078545150a110362000300c4582c004115100c0c051500c905441d4580903030307020107100c0c0300f0290000750044007007d02904040f40d80e584c0b60b82e104030035242030032481d550302d9545010040461005e120049841180354488114091f206a80140f00c0721036843c002c0c9000b0002c0d003004203854 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 343722535 1250 343721285 343721291
    0x50601081212061528090506210a1d060f130c060e04230702010b0f0d020f030304050622050d0f0303020304030216090f0e030a09030b150603041203 65
    0x12000400c1c1504807214030601059142e016a62001008441c590010941d00000c0b010400c40d0041411024807042d1511016142c13280360512940041c80c1884a0b0440350140707004022184040b21500f640151b00030040440d000d05640e1318000134054106a600c0e40f400034146800c01200c0500440e40e1071162034029182035072030380c0da4103454028180082d1301801d4101c2c25001401454402d1411781c20742040984080742c031841a4240907180f4030312611800130300683d5014000e20f158207000b001c00c5071a0403181ca103020181500060b8801e080756100038420300101c01d03010540c1d1024000c0d20000e004c001c080c2030300c3c0d245840c18165551110400e0544d1080071b101e000c0f4661070b00701841c1030f00d1a00f003024079206401e55235068000f5130003d8000c1d810b501c00c8001000c0641c0d40800c000015250000c80072662403030080854055403480c24810005030400e01484e590a5401040d031402c40741c010040103c03980311403119036a502c0e040d03030078241c12030f00020410090140c3c08030300b0605021240c4e410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 343723785 1250 343722535 343722553
    0x306050906060301030b060d050312010e0610090b0a03022802010914060c0a08070e101227031b2a080a020d03081005090108011d0d090b13030f05060108 67
    0x40769900c003d0000a01b607a1189011880394140f80c07401c07104140c496030480e8034068010741c2540d60000309905c00400444803108008031420008040d070444038030341c1810151513041403100703500c0717000392030700202050342c04160030340c0310b40f4000546181403841303141040128039003030402030180455200941e510302d186102c1c20719a810000741039124000c001260741c10100c000008a078060400b620000801504013500e060943c1c414012207865003c548440541c03c00c010440020b48070301d040f858203068800e44200c6040000206120b954962500d81b4100d0100301e0481c2c6522110392040c054908491031301c555051000c1c240f84001c126100844002c8496035a8141c140d440402003002504450000e201400181c011440380ea08442e1500310101d01070b07213030004a80781a900764000f030003d031b4562940a0803044101c140041141e01d210161040000b88900030b80a0680c501c101ca03007102e00044c0b005249040316440f07038061a4000c0c10701d00513429a0a205540300030078094140030b80100303008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 343725035 1250 343723785 343723789
    0xd02010b01141c09050f0609010c02010b0a0e040c08031306091502030a18080a0302060a060e010e040f0501180302030a021006050f0f040e0f071d13230106060306050906 74
    0x140c094400d100032000c1c5807440c001c000d031115030b03c0403034414011a150084c813000141e090044181e40e1583d640101364900e020507407182500e110080403015645172651511281d200c0a0403d07041d154140e0708403205840324500303140c00c8481c1e17130b00000c818080820081600140c40c1d265900b140e040d9a03d81c0c40302900c4e0700540361406050101300300503034030800c0480c102c0d60051000f0780c00250180406100556240e40e19420410403000c1140142c0101c802c202c0b6030b403003e01c59100070b40460b40c602c1382190b041080c030101c0200301601c043c1501090780b2000f020021309400480085142c095902c209445515010303590303130050351207030b07015000b80c00c01060b154035184503031030807210024040b200c00c803414414814212400402660440c0d00c2d150702038000b040400001c403040000c1d1004007003161a007600d2080700005188150300303481030314040c441c10f03001e00800c54110f50f400c9401480c1960520560140d840906d400000320755081040000d01c0343e82560103901101c0c801c0d14140c541d0751312001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 343726285 1250 343725035 343725047
    0x507020d140a170315540103050d080c07060606080117120d020c0c18060a060e01020c0f01020115150905010206090d0c080d050a09140a0b04021203040e090d02010b01 73
    0x780d1014007503011101c2c05c0240f52095a002120001c11601d29612008958a643d07459001940400300c403113040124454a4103c2138100070301042500c9091154150303501d81d512450513a0702a03003040041c2001c514001040d2040b59082e56100c00308000380340e51400040c1054800b446641710441c0342d585121501100890346c0c90004080d14141460240c005031160b000317412002180c01075108031041c0d81c0f030680301c0303130b243c00140c03003c280c100c0c819880d1907010000940d8143c3c211340100b10260180c01082d9070002a00780f40c00d075040313640008441c039110040780145044003483c0000300e08a60000340c0805411a06003498100e5503030313030000ba500c6000590350340f8400d444100345603010380141464148102a020201d0380b24038103d82c60f03d5146500324064400a40b180c04046940e54050310810020803000c440403040301e4050064822a80c442c1145110000e0010380241070055021500200034011a00030781440302c0884c095041c280c4159a445140c180d02d84090340c60038000044940c0195 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 343727535 1250 343726285 343726291
    0x1a0f0c070302150c07031e0b0c0405190803030406090809130c0207060311070258020d20190e0f0402060d0b01050706240e090705010507020d140a1703 66
    0x413000300a241e146a03103d102040c20303804034002181c0082d084200040c100045940504284540b8030b84541c1440200441201c0200900b07101e10b01001040185050220a4940c042d030860000a078413249401c1c85203080c80741c0003600752704c40c000000c00d072441405940000300f040101e508950b41030b6120b100a404442c40c0e59882e01c5082002d128020052802880c0c00c40c000f8020030145141035117141850020076482c110301c16901c5140c4058138020b8064006818400200c0e40c8010307013080042c1c000ca6641110400003038004d00b0031035188100380b502c000704c503a10007401030079040317102740480c81460091000b40942c46e04011002e021402c801607955116003d150001c00403485c12480940882c02400d0540c50710f03050203001d11510b0b000c20381c80d10800c80a403803480ba0345404407100200242e40f00d209078010a840c2c0c5240030600c50f48034400954038050360401e082c40341d40c0d6003240c00000c40307000c8a50740040500d5400407c5c010716610100c1d5003a02a4480d1030202200307040707850039135020f010403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 343728785 1250 343727535 343727557
    0x314160609020301020c01110705010f1e0902120d0c02130507080609041b0b0301030302060603060103200a0b07080406021509060403030c120c0201050613090b011a0f0c07030215 78
    0x9409408540300e80e1001100742d20080006141450b03260a860950300e9220042c4420b48000ca82002409020302940b17840b81616081040144400c5441e02a00c0c808130b904804a141e0b11515007045480301c3c024414134103144002ca512000c40500000c2c04c1c0510315400300e016000e240c2012551905900a060045000b501c9041107613071404144084104000c009484c02d6810103d4003052410b2003c0c444050300d6140e04103030303485d0305604000e890400090955070081d40108010004070b0f0140f40803194400c0260740da14801d20080002507040d0350f0b03980207542000d400051910400000030010000c80d034040d001d41d090441211324484482008641700402c0e5040680000c0002e44039600c40150b540e02410805001c03201c509620b02121140604100942e41d071f1400c0c044680342c028440b620700c140748401840042155640c410040710103110340d840c03040184901c50a0a124001944d0510418007030458540a480001c9942d0701c41034803090f40110802c2c1003061400c80e4a40c100c0780c40c0060b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 343730035 1250 343728785 343728817
    0xa060f0210052d31060603050c040e0a0f150623010e091009110c01090309080708070602030f03071b0b07090512030304121206060201050906060315012112020a0314 72
    0x1003e00441e1000501c540350410404d100c1011000500c1901ca0075003d10701440042c254149000d06200c11911144081801907101c2421440043d44800480601030350100e00b00c1c400035160314096000d06100d82121161070701c1000804620228550080c1c191842645c40c04080c041a40070b00410700b00a44d01c081c5000c2d980c080601c151031154100482000d13915901c01e02c0d282501c11300b01d00316003045204800013140300360100191601085484060b0880798082d185641c9400303030107580ca11910391200403054012001442c4107000f4030b01d0440351000545002072480c035601e002c411403c1c0403500000407070031800c800320302414006030b50318200110360020f41c695121070b2942020325074210804810000914a944100c3c445401481d000785010740002caa1030420500c01810018002d186078080c0d8007848408006180b0400030300d044445010a4148007044c0c00c495821005402a01415083c201107050b03030315131381c00075052880c680030741d4840a00d8503802d00b8051441c40340ca0481c40040745 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 343731285 1250 343730035 343730071
    0xc0706183f0f060506040605120309012006040f05061b0901050c0709020c0a0308061c0b1b030106050a0813022d04060303020606100302090a060f0210052d 68
    0x284141500c480c0c10321284090310803003850341d4022030b004504104a40c00342d02d4209100541c10b02d4001d0002900c0300700d035030104210b2440e005907a80d010382c4031414100a4041c41c041c04042a8922100140c41003505446152804e4141b81000071180d00c4102c81500c110400507007070b64005034460129820281000703181080010044901384c11141001d03030107001d00c07180020140003a00c000c01144010f04040c010512980c200500b06000080965006404480c4e8040e503641308000d40d03d00032940304503060100d40785ca81c03850090703600314039412001c01d60000010130000e40080180282c100301d03641701e56050740d50000a0310a40d1101c14020341014204401150f02400562209840c1c004251181e4516641d00c0014040e40e840340e10070b4000d03030000c8042c42101d00b8082c013481680702441c01c0951422082c003021480c0042c2ca0700c10507040042d48100d07510500d20a100c044c040380d030500b0084c0700e1410041c08540110030a00980100c005180503074a00d070880040c041403003820707444034071a0520 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 343732535 1250 343731285 343731359
    0x101a01030903030e0a1b08030304020904020d05030d020313290a050a09050304090c020105180606040906020f12150406180504030201021605060403090b0306090604110c070618 77
    0x1000a541c100c060648a0140340c450a10401050101074020104400f04940e111408440403c5903004000b0b981c004000300070240c1c944160f4981c0240d0305459108140c0454100755045000b120070040a640c000018494034400351003040c011240102400228400741b5002140c80c50204042c5881e00c81d1040c0004420b02015800140d002580080c08181e9950f07039541c031815603125400208107140d4400030041c540b9424864103500c00520b6600b8180c80010003501655840300400032486142c890740044104209034060f43c40303c9010525181d10350441e0280b100c0b032160100c40ca4140c840f1514002c00041ca0035010700d0f01200d051200301001082800b9014002d400010030a600f0366408102d54070300002095150013116001d03c3c05040da9040901e801081000541c1c003ca140560a0050121507a40d801051b81c200e90200d40000d031100905083c0728890041900c1110baa00601c140082c42d0380d04298101c40541e556100081c0381c0f07880d0302c0c11401013041019409000711148040540b11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 343733785 1250 343732535 343732541
    0x20703080a0c0e10030f060803040305150402030c1509011e0504140d020a030b0106140702010503060402180402030702070501112103041a28050405030306040b060408030c010e101a0103 81
    0x400c1d418a00108895041404610800c0103408a0304c002980c40c0c0c00554442010b1040502600260002d185000c1c0345031901662580e107030072842034038516540814219941080610100d040240410780000e190341091891034019266036800700300f5400d403071040c5400010703058218113000d03140d8034100343c109614118503101520541d90000c0700900c0c24030241c0d44d14011140150300c2803504030410341c1404002007280648030703000d07407503c1300a019100041c0e030090306403680b040c5d0545005840ea4081005201d000f045454002c0d001362001041c4003c1aa010514800f991400c2e210285030009940c1d07810394514405803540500d820750710800421800390030045400c1400361a0b00014840100070120b041c20b0152040c03c0303600c1c251805082e100301c0d40300303010070b020400703103410002841c2a840d110749038030004000c6846180d650320311115640d03c1e10165006490440100c944030104982424000d2400c8820303190688604054074008503014022115021003403e1100c2100745100015405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 343735035 1250 343733785 343733801
    0x606011719091403040503070e01030320160801061508010f0e0601120501060903030e010206040302070e19020f0304060605060406050406031503050a05060f1806011203141b010b0103020703080a 85
    0x101c6502d516194020403482c040e0312070014a107a010310b135590301e0982018a0880a6400300006080040040020075081000c3c0422008018203640030042d017083c0c030a0a24201c42d81000900001d00804510703088154454400e48456400803c407080180c0010303204034000348100502c0c0c81b81c58006120207800e0058894000e1018100a4041852000b141d0140c8009030080400140c031510f007001131661008050307500700401c0c0050890350402d034034004d444090314048d00c0170b0002c141011075613207000c95442401495040a046446030f00c03850741402e050384241c0d030566100c1d0030214041810b01d410012903080350390a071200c034905803034000b05401500c43e1954001040c00840000000300788180a100d040c20700c80c1d0041d08103807415500220351841d018082c41e82d6600880c3c11480d1004000a9440c15a80c5207007001d1410725032440c084420480d02c6101003060900410320800c8059001d90340c0c00ca403044c83c030091042047c01c10044040303000d0440c0c0980044e0100001c14a40c0d80c0a50015030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 343736285 1250 343735035 343735081
    0xd0909061406090d080d020a0807080601020a0f080913020903060108010b0d0303180b0c2701020d0c170a0801060207080303040209012102060a11010e010c020d0809190c050306060117 80
    0x408608584174102c0e15004038502d0071394203030000f480c0d1900a6001d503401e544080107041820b502d043c6180000c0d500c02a100b8020030000401070f250042c05820130a560806a00521740c3c0d003039400c000340310f4001e9080842c82c28000c0c81380030000300b0340ca03030306000e400102c0c00302408500103443d250301d0031000340281201e0001aa2880d49000000c40c550303e85e41803048000310700851380c80b480d001c01d01e000600d4005201030700c48c02e4000b0014180c0c0c0d0100e400c0000340103034a00b03101c0300c03600750603d9010704003180c250351644240010803191294100038610b0407108190251609590340c1c6083d075440744022100294404e80090042c082c03401c21981c81030800c0d1001680c1e40310000a580800c01541c082880307000401e0600c1d42074a4190300174083c1c0d850038107440c0000e0210800c24003002e5038408a01b0106001d00c50740c4e02c0000c03185103041084118031920110422400c18541c1032068101d80c56000b400c2c02401048001456540961a42070303d90451402a400988e18152003c00941481d10025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 343737535 1250 343736285 343736299
    0x150f0c02030a0c0e0f01030803130302030f07030233060105071103070e060f0418060b060c06040f0201033e09061305100f14090d0209090d090906140609 67
    0x50307103081088074020b9100e03442071642d080c2001d800880c2810001c3c60b015420003100010700005500400381c0c2c0d002400d007441e02d007200541c0c1ca4180d045000e02d1b00751a0104030003056040604d0760004070107041003503406803071030b5044003944906a0041100d00c103620300550400030030311075403040c2d0061402501a4648607008050030001070b04021660380001c02d004003010601800e46800c00030101c10f0001220100410031704144180e8540c0e400070000b070035641d60b81d0b041c903606403100002c440500703000101782c4041d0311300792901c071610404400702a40080d2808501e5a441503074a02c141581c00000d0450142c2201c001d072210130740542c0c0444800000b40d00744610040e585912000d4014010070604500000e8148028000041da00c040128100251501c280c000356803c4804005030b0040b4500c0303903984070303203c0000c10807030f070f034182070082d0041c0c10801004004140850ba601c40c0c24481c5d03541720715880d698190101520b020b07015141c40700c5101244c0d403490307240400080540b5000030b0010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 343738785 1250 343737535 343737557
    0x30a050a05060d0c052209050105180a020f06160503070c083c01060b0c06090c01050f041e0e0901020d0c090510080a150308120703061412100c050c060f01150f 70
    0x580071f440c0030042c101d0362a91a0740070f00124210b501d0f48a403814585c50000d14083c0c2154001541d19240c00d900c40c0c1c0512000200c03000c0003518104290805500300080b255100c0e081e02e0304942e980c205116160f41400b691507040d010071522014200082613864800750003103078001c0003031a10b880c14203020f40f0719943c4540010385500214098080300d00c150002c0d0140d4034180d1211801c01c9000d03d2002c6c10000c0410a5245400d000f03015202550035041e0341c3e0300d240c000c1141c042424403a54218541c00302d1000204501014150010020401e015030180030711f5001140c00d84400119015890b4080d406c03041000640b44200700465101c00104004903020030181e41c035081241081d007080d07980c0000002d20000003540312244076081b481c1e81c6810041c051612103480c1c01c1e1f24460f01780e207210340c1d04100003840c5000100700c244842600c0441c104130411444034060410340c006110405240191030000c3c410f60520380005040304c91801046010b659614411650103040c100c075a01442101e03101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 343740035 1250 343738785 343738849
    0x509180112020a0902070c15020a020301020f1b070b0318011d1c05040b030105010f020a0209011403070602010e120703210507030f05100e07050906030a050a05060d0c05 74
    0x12140c000c00c1c1c880c09540714041e06005000502e000ea4001c601503a0041000000058003005800304694044001496000342d004049050807643d490184d131540c004110042c1c03442c0910010062640c481c10031624841410344190f80f00d45041c8680150040107100103030b4512511541005da4080e8800005141107080c2d51605944100890900351a403094240c13000e8030982820302111000d01c3c3c14018207041ca0300d003823000359200500842d8100003003600500c40082c005c202c40e5014036030040603840341d036031607250702c541c9420f075000c03114030901c1340c001c002134614010304c5090720201c19400545541c040c8144040166071002d0b00032010880c000c1c1c25400b45d101c8943c40f0505c003280940d0b02095600384114001c080d07c0c202c0d1404081c5501c0c200605c406034a00c0c1c240281100c1642c5520802e40ea6002c005a0b09401240986a04a2400420800481481c0d07100034400c1484040801042d1036900a100c0729440e4500001c02070304e1503240a00080c54085401402d02d028a203620082d1160301107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 343741285 1250 343740035 343740079
    0xf010f3c03080309030c0f1c0c0c150315050402090604030204110403050304090209010201050a05091c02160b1b03090913021c0807030e01020c1020010c090f061407030509 75
    0x9980c44981c002150380c0b4000d1a09021501c04500e0350402400c00c8112505904000008411100240710009c02c404080140041c40d20380140242c0e10340101020404001401602d18510403208092540720042001d103001c3c401c2d18404400500400c3c01d081c1142e080c000240400403280103062030130301c030010001d401000140301920301420090388070921f61002a0944101510010030981813a080044407200010034151880c841c0d0803d50a195411405038207010081038102401c54004501040f40d1500300d00500403540721510800c81d03114800c0c078080d1203000700e0a189a0104811000c60042000082001d100c00d00003021a2000324401c1030940c442c2c1340f061012109028081542c00906820100c1d004524000307002500c404454080000c5000c041c0d180240d00340001d08a00c0c3c43d030031100042d84c4003600e0b1401c0c000c0184080e00600a00401d60a1040d032400d40142c0d00e01180e102e20410303400007030000001000d82002c1140c1d034142c0e841d4000410315908140015040b000e2084215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 343742535 1250 343741285 343741291
    0x7050301110403110a05010f180e010807050315060904031d0904150b0406053f030309061f0306020a02031e030117030309100e03070b0f010f3c030803 66
    0x80c81482e5198658908102841c100581081c81001422000c0101c1e03600600030516195840c5042d03c066094071200142007080f84d00050b400403ca0340001c25103000018032201910f40071001c9400c5500084880c90458000700d44140c0c00000000100f0000780c01107540b070541845c0c0b0501d0410a0901c000440d00034a400c031010303181c2200f1805012901d42481c8200240304400703032410300206081002040804a5601c2d002404802c16a0340010240c000d1000c071540c4501c0074403440f06500c1004102e039a07500b058807400d5160040c800410340c4184070313400b4070080c803c8c1d41c400440168030315101c510081d00941d05800a5010800c2030b101201c20346240a0904209034114035242e5041001004107010024100c8659900800500102c200001401204a880550081044032410f601c440c15809100c41c001c2c06003147ea020700c0b5000c40441c1405043c1c580b460071207104a03a0b00e981c951110380c07000341ca900f5501c043c220000304c185550840329154001006807100b240c0d035203950301c0650340e00031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 343743785 1250 343742535 343742561
    0x5090111010603050c0d1505090d0e010219140a05100b040501050315040609031403130302010516120509030910050304030806150a0e01031107151d1c030b0a091b0503070f080907050301 81
    0x125062000c00d4bc20405910044100f031000306110f400960040b80034000e42c80014103140e00031700c4800c242d903a00b0010301c00c501c0d40c003905032511100c5030100c90024201c2124142d1003a404d0000101d901d0400040381d0fa2042c03214040110346841d40d407a400000c2140301029001c02c49190707038040388078440e40029805080141d8100252444c1414001c0c21075002400a130200e14020821904841e40810350324040d41150f0341c00507854a03551083c9155119a40c02c054003c40f10004194000da00f103005148190b010b03403602c8034075581d00c00c00c000740742681c26449221010203011300c00c01907101c0d0001c0241e051040c180080c00040094004c07040b80c01100c4100c1e4115140c2c080041903000c80d000d803d200e0b4181150b581002000413444a4492070900500f2050030040c00d032000116205e42c204601c4d50300050b0102580719214490709002d00307e000c0b038901c9004007100d688502c0601c04d4044074854045c0b40d450032014200003100301c0f040f100c098150f03585445222800706865400b0301c21070001350f0803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 343745035 1250 343743785 343743793
    0xa090203070e01170d0201150b1b0d08010f06090506070b1f09090606050406050109050907022e140c03070f1106160216031502091201090305090111010603050c0d150509 74
    0xc00f540d0b0f62030400020300c00011641032a440c2c0c45030510648c1c01400b030b01c0e49512410745440e01140300b50002440100005058800c0c8a0100d841d5504040c1c00c038107843c1044142e01c0c0c1c640e15448141c0d400307443e5101e059000700c420003450f0081180d07a001141c102d43c0c4c90340400e44103008400001804071194116408481d6200c031514100080f81c03149000514082e1818000c43d460803001810a1145208250081000c10001200706100340099291890409101c000d0011001030503510a8034604030400142e2509003040c81d901c00302da001d20f10a800c0c038482e051441d902e400b001c5910400220b6000280801503026480c00ea10034000c040c412403000800c03152941d00c00500134500303920781543c0319001945032400d0003c900d8a400744203442c0c02d140b40150355240c1201c082018100401041707007807940391080b00000c1513405401010142000d036070340c059607042c0994603800c0364803601c001041640b2030310550301c4038100707404603818803030141ca269000702e07855003c005c050300c400301c07540004c60b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 343746285 1250 343745035 343745069
    0x9030c0d05012f0f1309050705070b0c03130210201606090f031211030a020c010810120f06021306081e09061b13030807060e060705030a090203070e01 66
    0x12602607801121109490241644064552411080c4c4141005504600800620820208000030305803008201501c0200803c2c646840001d0560f08920301c00c4030310b050f0000c04502041c0a080540c0d00035035081f00403c017207038001c1e400c0203001d440c0464184203000c081b10803000040403606001c00c04461040142c00f07142d4a00e03865400b0b261450b04441e0500450010038000000001058010f86c1d0740602b4a5450003510102600c18102d58035103280036100010300a50480c3d804505201e03014801e8a0301c060944640b500752007905224010f90301689008a00400483d055407050803075180180b000514200d4240c80c4080c0084894102c1320200d5681014408a41021500402c64103406001b1400300c0c2080c41c0c6903515017001504882600c0303d02201c8903040d90054040710f500c2210424140d1149a4a00d000ea10f0303a04602c5080e203d19240180ca2910346d540454098460061a134545145507103c01003000180b425400c10b0741c05106147c00816050b16040c0413601030003049499a1480e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 343747535 1250 343746285 343746311
    0x509041a060a0c1707120507060617030705280b040804030c03201c12120203011d010b070305041a0412060f0f06080c0d0303020f13060f0f0c060209030c0d0501 70
    0x141c5a01300030180031000c2000c5e9000c18110448240b003400345181659540f0030038104600a080150002c9281203205540680701c4400013006124042c491402e41c0c500442c200788414480c10b8202410001c2041c045061000404441c0205e501030720901200e400c1a031240c5480d25400e440790000c031740d11103840280c01001e03074522000324403001080314031520981c04000501e29802c03400303100604403503c55015440060003070003180c040d5503c607281151a5a5140d802040c80c4803a0740050b40c03503c00340d034000300f12400100c080302c0401e03405488583c0307458942200450030840300ca842c2c1d100004280004910304010001103000a4000c1002003824200700c2c00000880354010103000f841868200200416400880d0010280804940806649940b401c0c240d001e03104410000100d00c4000a1040440c00c548407200700307940013030382c822484e400440c0c420b4900709038000070341b008540c4004204000030369580082001c880040e050b208031511030720109180340a910f904941f10794449200b80c480d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 343748785 1250 343747535 343747553
    0x2071b0b0714010b060d022d25020307060f0203071e12031a0609040f021308070e0106020709050c0f0304151104030206070f03020a0212160b04060509041a060a0c 71
    0x1465114000304091300e0318000083d01441b40c0000b4200d195004150301c0b10741000001010078840e80245442858444601100c410354481e1101c0d920200004107581c100c07020101d26031241c5580034009010315802d00e0f105442c020301000001c800c42c4020043c0b103000605101c01d064080081581d000100c607218601079140000c041c001004041c03800c544150040100e60203010400c2c0700340c0303080d6600c0b5000000315019180c040b091b02121400002d1003851104003200c01e100301c031a0501601c4075641c41c2c290500d02c0d15028440c603801030303100f29814804071140394070040d0000350805e540c80ca409000c01490005800859080d07c6061000480194042550040c0108034081010b00741c6460b0843c0e0010300c55004080000d4a0301c04142000c004142c000c004d00011940c00800d882d04000c0502c181d95640c410019141109000803032000032040076602c1910140d500a4036a82d04000c026400c1c0b000510041040d10007564149540c10003e132541c80040901c00051364230401c0c0324005007041020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 343750035 1250 343748785 343748813
    0x170a0c051b010f030c050f0403050c0310050402060d0b010509100305090f0718020306131e0b03060105150306011709030915090d020d060b040204060807080603060408030a02071b0b07 80
    0x190405005107003000d0b030340030b080c1025810407810005140e680220049405004220400e520f2460000d4003209220b07000981161104e0105c040340c8030b00000400c19410b840c025140290031000c14004848100700c19040a1640360042c0342a904086642000901200e4030920745004240c1c0c0d41d041c41102c4009002001c03000540000030003010b441c01580342070030044021f81384a103540c08008100d459507043c0030751103204001402400403c0000401c1060f140d840c0c400f4804d0746143c000b1203030031803c0100744607040745c8004080c1032800309424800c1c51554030003042581000007004d08241d03502e09004206000e00c1300c241c000d544508240c0c040c411104011001199001c40c148290142541e682207108803035541075480b4201a1324501d410303400f900140f254558418004a00414075a0f40f00c0c5019100e880c281d6201d131541d88451083c50749480013602d000c0d28040c2c0070400601a40700980041607003902c590079440c440d01105168030f29070210758024150001c00000c40c0820303c945458820310f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 343751285 1250 343750035 343750063
    0x60d0915020711030f060c091f030605011206270b041515020109050d0302090307090207111503061f12060807061709030a0f030e031204060c030b0d0f170a0c05 70
    0xb807600d080781746041d0b40703a2004200d401c8400300047d002d441c43d16803d5510003540e0b001205d480802e900e0140107000380c15a40940c40c001400c1200104008009004290458031a00c1084c2512510031000040e0b04d1b111418044080362100c62004091f16588100c003a2014222483d880b502c2c2426080215903007104d01c1c860845e8100030060010400100b030300e0003000c105080050345c0b40c0c480c0380481d0804210b6881b02c510b10340702003005000d0058103000d50b0100f00c4202d40032042d001e242d03400c01c0c0039401b090365410740000064594200c4101142050001511641413140819050602034001d03609180c110f00e000c1d400103901040601d400c00254161081905404038071850241042039590040032808400c110030b454031a0100d078060380c4020240001e00c0140c82c1e4501141d526840070305800d03601140c0302c2d490074040d920132510920580c070207407100814169028181c2d0326030841616080e00143e400307400b44940d00700c0e0340b1091401044407a13015240c8411224090502608000c1290f10500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 343752535 1250 343751285 343751293
    0x1090b06030d080a0504110a031101030507050f070201080613020a0c0212070e0408090409080406020102090a06020105060d14030f0c1f05060a030f03110d020309032406060d091502071103 82
    0x41c24542003101c0d40d6005440d070b03400061580c0c9a060081d1041f00040c0300d20b4014404030004005d100c0480ea22072400f03c0203032000c0c4080e03103641c2c0080b503051207a001d1070500c0460034003800c40107600c201d002c00d170071020081c44131161001c00c42030391081340e2004241c04007040781128000210308010941d9054030580101400d60b40303107071140c03501c0380c0c090041000701488800955150b1316038490b0720038408a6080400c3e652110748032a0068001d41c040300300c072171041402190000b401c0c1d105004842c81001e028012801e0044642e031290000c210701c4520403106c0c0000c1c80041d0410341014041c0100005400040503224500424180c021400700030b1541440d09000400030380e503c07a8040341382200d030f000720640031040c054102110006004510038005024040001c1d0006600002a0000e100102c09903041e4040041105984001044c450300141144800180042c502a4090186c4032050000843d004102c0c2e0740e00c40c543d0402c00c0c0141d00095021840f5000c0c0440e0450300d070441c1c1010350042c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 343753785 1250 343752535 343752553
    0x190e0607050304050622031103161a0a05090613180c020303070809030d050c0c1525020316060501031e020d020906011b1203050c070804030615051201090b0603 70
    0x59103c0c4228003401d40102c0300051080b541901e2040c403540a41900d80b8034101068403440d1030101c0040c1640403e1180c405e96071316102070000c1400800c200c803644881043d00032002075800310309411400800342801402d00ca204c4250321500300801d080310320402500728203410700d00c001051407124050701c2c60403882c100d826061240c00204980c4c21418504054550741c2d82c0c5240f462551003215001c1c03445e81d00f00024440d070700003182c01402d1081c070503c050f1600c3d16044c9006102e8020115114500100c0c0214002c40320042d0200e0044038441d24410f03245400d0102c194030101c8004620700b141c98580e580010070a100400c1a60344041112106180c8049016000107920020700900030784205462800b04000340e000b010703c02e100c0e180d040d810107011880380c11f048501640131840c02011a084c400022407580c5000100c41507a41d01c84a480c0c1090700b151910801020785540d003100740a01680c02180d10303681c00204066100c415800406d20285501c0c0c083c40d21003001d071240340a540a0048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 343755035 1250 343753785 343753793
    0x80a03020604031b15050a050604090c140a080601080706030f02030115111e10140c072418151806020c010f02030c0406020601060e0d2402190e0607 65
    0xc01ca40154061070300604c104c1d503640303108091840c10b0f840109051703841c3d019654041e034507801c258032480e40c81204201030f9031503074140701c150f650341e060044c01c0940e1007005002020b001449500c0c4030740045c02c9041600d88a0008500d4043c0a130048241503100c09010041c551341400b61007009450b01006500707651412040c0591a40c3e00744015007800480134401c404c1c240200401621000300308104880f1012000300c6548588508030111949030030315600580d10401c051030640201c03005505207251000c40d440c0d684d1490503240b040418848807401c4401c01610743d0091070010546000000d90243d601d00d00007082c040c3c0011484141400c1041100f2484940410054800d800c402c0c00742c3c2d02c0c403a82c2d54560051001340b003d07910440c804010f0092943e0140e001d04150b6615800310f5a490741c0381d640a03111941c403458520740c400000c4c00d500c0005000070030010f010f9001c0d240100100b050030040c02090f07030862003d0003481c0f620407110f00e10071503200c0409101d1081c01d6804524201b0f890325 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 343756285 1250 343755035 343755043
    0x60414060103180203012c0a0803070c05030405041b030e07060e0d08130f0f0906080309100c21021005090d0c0f0b130b160e0405060a090203040803010807080a0302 72
    0xc9905141e91a1410000b11001400d440700960340100200b0102c0020304d43e43d41d401400b004403820300ca080b69a542c4201c100000c0380001c19801140003420743c2c1c0d856100b15032000c0c0c0507004840c140414040015640c8540c002c80401200c81030b034444e03400d1801200181110041124620076511481c002c0081c0c0350440c00c032124510068a1103000f00081d0b0034900500d01c505e12001c05955140303040024803869600e010780a0740c850400c40303d07001e82d03624030031400e035006800391010700c0c2c10401481c42c0e030b840d0902d1175603c05450b6040241c40c08034035403a41001c0241c42c0c45c40c0d03020b01c00c031440b0342c064807981840040751301d0400d414104443d0405980e05941d40600b080c242c0140710805840c0c0d4203000c40382d0075803001c95078800140070044c90004c0381c1443c42d0390902c01c2203d0240b03034000400c0241442d81e8980c681515190b9448040352020030400c0041c020107042c01b82c00114a01020550b65001d00065100c2d0380100c2e1019a203514003001140351606d180d01140740c640000540c000021381c041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 343757535 1250 343756285 343756291
    0x60304030e13020c0303101d09060703090c030503310b0301090e0309030d0903062702040504020103060909031e050304030507080d0204050a090902090723030a02160317060414 77
    0x5a880204401001c580320020320502164013032920010007042040846800c000044d903c3d00160012408286941c8c55460342d0181c0d040402c0d5000580003a400703c0c401da0052104900880305140015665180e0074219800544c0703c4540c24440003c000c13071945219904050085513041c0500c2007031900005205038001030041c810160b454903160181e8080030025a03e071008000c0540b00300c0c0d00721000c050048001803000b1a10030f41425050340115031104000c032140780d03443c00c0342101d82f402d40d42000001d2400610803814560ba81c600070440d034409110f0030039900d00c00d840d400c9000c0002c2500e40200104521200c080010400800000a5000042e03800c160ba11290964980785004d102030302a00841e0421a084450b441000508200c00c1e004080070034002d4075200e440f40c03a003860440d25601000744201c0b080040d0701c1c58182e038a1048004580c440b1500400605000f07540e40c1d00113400300b4900c005d030009540c0400d8030150515242c1010f0700600d0469080007030104040440883d00402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 343758785 1250 343757535 343757539
    0xc0a050406081302030f061807061e09090c03020c0114010501021f0b090406061806080309011b080f0c10050f060f030a0501050103081306030b03060a0b010c051c0e060304030e 77
    0x40d0201d070f0380841c0c2c10080f099166000702603551001a03502480d81e0341d001141c2070340641d01031070703820021910007040800540d100c590301c8400d01c4021a50041040c0050682d40c1d080140c01c1d080001c07244158418100054001e81c0c02581c1d502cec5a070425800c0d220101c40314110a010000101304581e0000b4400340e0500346100c401c500207132401e01c694000c001c1b41c1d0080da000b001e41410441080304990000041c3c0302c0401003400030701d00b042c2101c001c9405500401c4217a620030003c2020a601a07c22031050600c1032140001d5420b8941d1107032510341050041c200d0507000414181c0c3c4441044c40b0800344030a04400801c0680781c500da82e000c0060000e0320706c3d4025403c0428400485d00e0074400070164980041c028810365035286024002580030403604003d6100340f07400420628480d000318108820000c0c0181000c0e211a0081002024000c4509050292140c2d03140300162084c00f0f80390800d580200c141442804000f40a007000c005980440d2061508004000c0026003080031109810740c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 343760035 1250 343758785 343758797
    0xf0501110a0b1b070f200f09090c0d0807060606050f09040c05160c151b060e031b0105010e01060309021e210106031e0302070b0f1201060e04050c0a050406 68
    0x26072007102c0d80401e400c1448861000d40000d5413024041e5000241070514802e07001c02291140311265400e0340380b883d2500a80c0020840c80c3c1c42c0341440c2584402c0e8100c4900002c0d0340c060345001b4005503c03824807400441d030412010400b10207001d0140300b018000c180c0c0341081272900c60000301d8961244290541280b1407a5900310305c0c40c01d54415029100700d440703072520300c00c041001070402c041ca81c9642d100e0300240141491120000c18031483d5101d103140c3c2e80010240030303220503541f004081d10840a984010b40b200748001f40e02c98070f44c1e81401c4074082d03e0100010300c1d541403400c0041c1d50030050300520b043c5802c06048070f0050300c5007181504441d0200c00c404401d0464203002540c0010203000c0000300c82600d00001c3d8440e64103500102c112481050012411500080e02c40b510b844506400340150300000310400c0413170701c2040100700315145481c003249003040c903000a0326096000e030082c100107500681c0003413490074948110342d044252907110300d00f810103508000741640b246000303010070065 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 343761285 1250 343760035 343760041
    0x610020d0c140c0a0e341101111201090f05060a06180b130512010c091703120a0605030c12030d1d0106150f0905010c020f0303120708010f0501110a0b 66
    0x105010030f203032000c0c008050204240d500c04010301c4488054511220300090000205100c0341c2000340d107010000300e034010041d020f00003d400c0e00c400f101040740922554881c024801043d10420040000f0a0210038846246d41031080880454886004040000349001e003400140d0f6950303150b0300211034603071402184084040c100340904001a03030041130307a03007400b0a04080381121140c2c010160f51007a900401d06180015466082c0e410000511b80031901d010001d1049155030604a060002804116407800c9454505031440b0442101c140300e80346c0e507a0a080c0064074040c48110b0702c00e07004071103403010354210103104c5440380f00b1003448000099807000c80803005814202900c00080d4070000030060340c1d03a05c40c140420f21104d44070000000c0d50014400c04040d01901c802010340b40107130f5440044090a83c28410401c1d2000c40169041c801400000c7c0100380c4001d41a1195486540b900302551400e218480d80901d03a40000d810b01041e260048040500001d40303442640d080482e08200307071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 343762535 1250 343761285 343761323
    0x31502030403050c07080102040824160c080304060b0109080309090106111207060203040204050606070503030a1806090c05010e010c03080606130b07300c020d0201020f01140610020d0c 81
    0x200c1000c04c4030110b400b4804001550803019400b0700100c0b9802c0d41981c14800c9807010714015410055400029284100081100290f0300b49400130801c00d141801c1d4a41d28240d221250fa9400031102110b0541d1980480007665901242c00301c000e01c42c903030095003003040c1c0100086110300305001c0c80d8100600c040a80400240800245403500c100343c49190707440c0e4581c2850380180d030044406a02a5041101084941c01e01004a131901a01304c0084c1d42140c803480b600f030740a0040c4001d0480940001703038a40c404111184950b0f0130042c80380540888441c900400940642203076489903041c81802400f52001c81e4000151030b03032101c2d007194982e5030303600000788504401019400445280502107803460820510341c00f5076150802081c00001c4000e042101428940e400242c807000240305030f91b03403500508240600c1c00181c0d20500589000c2d07600350314104d084804040e04659041020001e1140d1030408001c998180300245c406020541101e0030054010455610002c0048041020301c00181e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 343763785 1250 343762535 343762537
    0x50f0303191e05040f08070302030d0f0507020a0b0c1002090d030e0a0b1b010501050427020109031707020411040305060f0408040b0310030629060c070914040b070903150203040305 79
    0x4840d000300b8068400090000244641c0040c090035241c103200c0700010480040004441d02180e600130010049100000781c1100c220304111001014044140000350050781c88010040240c80481c075078946400043d28400d182c04070495581d0004d40c8100a49682c64403040072501c0e81540600384118070400200c0422a05a4154410100020045241100403820542d0f040b000d005110007032060b40d80314403c000480d155a522064411042d0890003a44001c2d2004681054014142403d8860342c03a12809908d00c09281400040000000c1c0301c0214981407003000309103000400d2180c10907017503543e62980c802021340780d40340000101001030104003042c01154090216901255120308002e50380c10408105400b048600e1400c00103180d0508943e070012416205c030b48000000025408001d21116030301003100d01400c2c0c01410004241ca410314000e8103500c06140404040301e14180c102801d030508064003003030800c07550300e10400100c0d03210281140c0c12205c6200043c1d5070384031880c0648003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 343765035 1250 343763785 343763807
    0x5011409012705010801060f051c02130e070201180203060106031d030d0902010e0612060907050d0501140f180708100e070e01080106020c090a0b040e0a0c030606050f030319 76
    0x4081021034040c4035a000b07060358002115001e80f13601e2400e90721140c054138036140d0348482e01d0000340c091100000441c400c20010300e4242c104100146403100e2261307920420b051981000001c0d4a520003032062031582407007110141e20118019a01d198516800680c40e004c040c4601c100705615000c410b49080711130403c60180700005d0301240e07030b194004035201014041d0b0138000d902259000c6410000c504000080340e404400341c6038803d8540e07982104015080e40081c0c4641e003040b005100f8144042c070180329090281080c000600c800d001240704001c0413035202d00015002d003403414101d50b040050880c810760040c00e50306000705640c0d103d00303844511000d5075200d054020075030b505000640350040d81d08451411b0a0380d81c18204d80c0c940800340d0340d450a181800303800207801c0000522400c0c6961010070203100043c00803c5070b10b1040c24003441c0420f000d0742a104988015020810010a44180e40044c6400d4881401c4190080006a1207004020030b142c00100200001e0071854494010408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 343766285 1250 343765035 343765067
    0x806160905091f0f060906030b1f0212070311010f0b10080601030f02031501140a0c0b0406060f08100e0703030801031113050a0e150c0a050f13030f02190501140901 72
    0x43c0703544001e15100c05080340f00d0800858041c0c040800e00c0d40c8a030140070400100034203214108141441021903c2841100890441c0a8a200181944007450081640707500a40d20b10601001489095085608001012118130700d004171040207500e40d959008020010350034503116035030303a03800141c024201c0c980036410003500c000104034000c55907070b5445244910a07600c1440c42070300c0c0f04444655204074403502c00443c026401000024a500f90a00d5105204000215040c1c0e5070b003035207900321800760304012000d810141e11504e62005910405601c1205040108011480c42c1c4010708040301c10302028140220300c420000c401d0300c800b044205030441c0050108614a0b200344108020481802c00541e2030050903c00301c0b425240072070060040c1038031500140382c070f04042d801b640c059101f09181c01c1d0022040c0510009105480000b4008500590300d88047c220688100b1003412581e40904056182c80241808a41d81c048484950491001d907160b41e00c00c0072900694240ba0400d144e08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 343767535 1250 343766285 343766341
    0xa02190302030412080c09060903010209030609010b120d0e0103051e01090209010e04110a080603070801060b0301050a080607120c050c060a0f050c0f070f02042301080616090509 78
    0x4804035450360003144603600402a00d00080200e4404a030000029110301300c12640610050300d4915200000f01402e150090005140c81c0500d030202e400d00030201c801c85032603590b824160382141441010b036400d00c0704440140580c1001940c028111129481e0540d04140da9680050751a25020040c9540081c40702e241e6185981e407000b440010707611070220039002403040321b03540c0c1c480c1c20a07000720250000151b40742800c100004c030045a44038801440d80f85e040c825440c0c0041c0c0c80b5400c1c801c5101410400400e00c0c1d03070358109414840c000f2401da1000080341d10001c20022903a600801030003800e0705510010a001c81c103100201d41d580a403800045c540c0c0280310520880c002c4a81c800d40800c80c004130b09101540c0c0d02e0307014036854054845c060288407810405a00012514031310a42114801080050881c3c9601050702c03024010510001e002c40000c4018044504100b040c181d20041c2c5001c0820f030040390840040414031640305403070091030b500740424540c0e6141d403081140000304050034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 343768785 1250 343767535 343767577
    0x8060405152e18020405030a060504060204050a1815150e060409060905090c04060f140409080a0c020a05040b03030901110c09042109050105033d0303080610020a0b0a02 74
    0x1a03035010240f03114200c003011242c03d01030386034196030007070b01c007218001070107040c2d0401c05031a0b5001400c0c0042c805c540e541c4e802c00010495689080c21040a13040b51070900384141c1d6035034100c00880e405045104010503565404100301f0f4a00c211360340c40c0c0006850594a0306045101240d410300807900210307421420010b011810701540da202c0c912500c9080b04998801000100380f100304d40080c040c80300f817011107090a20030a01c10282c00c03801c801c0b01500004007464580c0b903550864110b012510b00049078120f81c1001d624080c0c1c241800b13854120b44c104241c2c034074500000c0c1d8070b104941145045c1714200412540301542402005020344003c1c04502c070f03d02d414500b40a014440300480c42c084040031555007030301403107040c2c0401900c20684803107145490301c8a55503c404414a600c0000c10052071241c511080700740d41c1024078038205010648442e040d0b1030b01409440c1c0c020000c80c01200101c0701c48407015800200d01c0307507a0b9082005a00c2270717199200d0400103071040c507100401013500e404103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 343770035 1250 343768785 343768861
    0x40f090f1b031a100905060c0703121706030c0303030a0b010903020307080609060a0203010509010b0d0e0d091a160b040203120a12060e040f06150f03050106030c0806040515 76
    0x2142000c54040741e5501c440c110750104000c0d081300103982c0b010001d01c1405051019090110044c40c1c4a000c1504490400d5079035900c4440c0402c8100901c00013a0090302c038000d035840c0b000610b80e040b58084010340445000a40441c2d90782c040200352000c410f8036003000c01040e0b4000ca10203000f440d0058180c1d02c00c0b03611910215940d0105a42c40c0c40f0601c5407800003442c072076591080d00c3c1070702d000815995441c2d00c0c2a00981d129004240081f054541e10300c6084a8078104101c6020700581540b01c07600d500d072808100d1203050180c90008800d02d401040700f0211600248014560345601008a030b1039a1120300210340303040001d031480d24004000080800e20030b0b170842c0e2041140c082110b0184105612200c0c1c010b4800d00599009154800132035201001490903000681706d8008104d50000250761192000c1138410194425910b81e59a90010310a00c1005c0c00303164007030641000104401d040950b162a07480c00f040c0c0a440107040c01602185000d105a129055041001031006002200c5450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 343771285 1250 343770035 343770041
    0x20d060e010e090607020607020a02010507061b08010302031002160b0411030a03020102030a05361009060f0e030a1409030307020607062c250f0e01060311040f090f1b03 74
    0x1030542c0b2138420344001903081c03440041c0c414400d034020350140c2502811030307005551036001404200d48240d16021010078840403d280541409003a9a8032038481d45140181410540043e030700174000d41c0104011040390580a0a0510640c0c0c4201c00000d45c0d52103007460380b0b1000d80b8094141d81030240204407024541e05402650090183c06d208118544410303686500001100e010b56262860000c0c01600c142068806d43c03480d01070841c251000c3ca107102c07500d10304803040c1c1342048036159034a544a01c1601194418071040503c2c1400070b6142440c044001b5014405c04042c1e4601c3c00c0c40010030100548081c0292120558050440c1c5e0710341074680782030030241c8442c815107000f011a0180e0700320000b01c07200700489a10b2460b00035006075189000303541074050103404820511a802c8100042d030300800030807040208101c1490360099410a1401000d8800040c8079600300710007800180410045194094202c40a07804001a011010b20b5154060810044203800303602411740042140c2d07805030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 343772535 1250 343771285 343771291
    0x40b070f061e060b0703080601080a0605150c0616081f031514090c090604020903070b0d09030909020705280f0503030a0b0d0c0302010f090803030106050a1202120703020d060e010e 79
    0x414203102c40703502c1d4003444c44180115400600082d005030045a00c550041180310f410081a01000c682c5d1510340c404558500300c0340030b8032081c21800181c2121700140520807540c00c210f080c04a19400c0204d0240184000005411151100511130260740d0088041c03000f9001194085071103a1540d0b03c804c2c103000200416840c6090074116500061403190011410348100f000090508038241c68101c01d00009400c0b50384c0b000c1d01403082c902c001c02c112a40c00d0160500c03108824010803019124503000b40010301a5210100362401408104002400400e682c20f00010513908400f012284048070b8041d80608440a0a08030704a003500713090143c084011071050001800078010320b2004800d0002400ca01d2801400100c640c413018030056210310000004c4604c9841c0c45582180c403442d03c18215842039200ae004100f0020700e00804d1501300d622030a0300c0c40701c0341c3d0450804050010b1188000d40081c011420194002191003a00409501041c0900340e0191000c0385580c4481ba4900d0802d03041e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 343773785 1250 343772535 343772591
    0x1704080f0d030b0105030f01031704090f020a2c01051e0310030302070f0b070f032a11060307120f020c121c051e25020606090108060c040b070f06 64
    0x4400f049a581d4003840480340900300c0010355414581c41c5407190410501c42035048148642d0800c030002d12101c0718001c01c040e0f51b6522400581d511541c50010b03242c106403600358084a2580c58481084107540b4100031102042824003a9541c04c1c00c150007000500c1103d032040004901000b403207040c140000800098a203c0d400312100541c03a016242001d10507440390503643d4804020707101c006140d5400d1416001e1081c01d0200b1105400c000b500b9038030300d03255038182903503c144200348144490700c40e01040c05041170350842d02c0c500309004002c040c0e450314060041c20f02d8a490384603051100540c1110480f00d141c500f50348155200f1194040d19920101c00825291a0682c0107180c0d02e0407441014020349140c03004403914000030080d101040740041036a0814010300301440d805010200d01c803850310480e580070740303018981042080340c00c0d94181c10589050b4401c0c002c12100303d1001c811201566140c1c025503884422624180305011040d19006003114241511030000b140752500c41003004080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 343775035 1250 343773785 343773791
    0x70803060103020412140f030421050c0901031a060114070228060c05060a0c09170c040216120f09050d050c1003060512010c050a0507020d0f12180e01031704080f0d03 73
    0x3c9615008d03600d002c1c9004a80c4025110442042002e40342103110008a114009860031b46000800043c9800c00907401a200d400300e5071012078280c00140e0006034044424284410944500d002c0c0650500903c40000c1c001c02007810040200a000c9004034031b156120301103c0181ca8a40c0d03801000c900340302b241101c0350300c60300020a160860340c0c01031500c6011070350b6a1324130311454420700241150082ea0050100d0040b4106110b980e151030000b809040b940800c90800d0744547c0c5011801d041d6544003500c10803c5902008100326402034030601250000c0740c182c103004071302c1c0c104542000b2076207a035940d100d0321181c18451000d4054108004440c0d0172150002e101c1d00d6540c03020300307984200103140e0000f0000c010f044038141c001c40260031a41d00250610703d2180e02a6650641c02c88010020b403a004658036000e075007a03601180e1888110f004035000c800c1c0701d14005590031000b806000046c0f54805000081c0f0502c6003203025a0010284130044800074507144040644030400420300c6800241 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 343776285 1250 343775035 343775053
    0x50106080f2404060c050d02032401080f19020c0115050102070608010b0a030c050906070605150d050a0609030201020c0312011d1e090319120e0105010b07080306010302041214 77
    0x261010b81e10000ea60b00b088030003940da59540d0f807001031141d201c508007401418000707184510700310710143d07100341002c1c0b0400c15006d221003005941d4440c0412102d0402ca01e00080040c811080e228150f002008040542c842e40a441c9250019005481c6d20074401d628203818108031080ca81707800012203200782c00760307078036951540030480d03004409000e10008a1130070026040040d200360321030710381e60030079151a508000486e40007640952001c0415aa429110018005c01d0340c150303079603031481c0c1404807a640c2e111416551400d48801c1b8401d000303018280e44401000506000b901105e0070000482d050720358400c94032200844c007010078002d0768200101d07803c00c00c0d608184522024040d20b08000c2c4031290710310944100c10000d2008050700c0360781c081403003912604914480300344030030711a54403440070f444503070030350101115080c1c01c0c0a00c0c96030400f0010003000c04424210b400301ca400c060155517075511000142c02030700c581d601c03c1004000307401e003003401d01c6441c420380d0910100440036165505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 343777535 1250 343776285 343776313
    0xa080315010503010e070e030a020d06141f0308071106190206010b0a08010522020f1c270c03050a030503010e07080f07110a06050a200a09060e0d050106080f 69
    0xf001c24021a00d10004402c0400c000c0d0f0b00604004a07200d0b0b0041c1142d0310648154045401c009114404880c1c040c0c0b80d034480b0a55000385022284d010100c4009211810440b0540f410140342a10001d8200f420006411082c441d0b0b06c40d0f00c0a45603005003245685000c0b0175081805c4454002c40d0b03900500170040049802e5984200304c500c130b131040c4e58984510b6400d0104008003010261840e42e42078040e0150940440f50314001303803c403260030340038440c1c680f0684024010f1403240042a018033b18502040100344080141000600490b03200304803806000600c0d00ea0103082440c1c20182a44c811100403c0415610000950503603218801c00845611499802c2c1d514001c1640c42e0030031a20400000341c90315200300d954600c004241c3c0120361407407000b52500030032510182c03034030803a081d101e0b101c0c040e09041c0d0803400844054114026894020107100080045447e0b020342020080740700c00d403200907501c071325020000d560000020007259941d210999501c01d00c00041c00c6140c0148000e03081c0c4c80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 343778785 1250 343777535 343777537
    0x4030c0c0902070f0210030e1c0f0504150e0a080f0703060c0513060f0509130504030e01020304060f0e13020c0c150903150c070b0103080d050a020301050d1704080a0803150105 77
    0x10384d20a1502c81403500780da007080b501c11483d4900404240d03079501180d40524040150b00c8112111b000d182c607a0b500ca00d04014481e0701c0300e00006081c03000c00c00c8108501800c00e03100c078550f4501807030025500c004010000d001c4040540c04480c1134442c1008010030b881001c02c440085a00c14070b410001c04036400d038107460b60300540f005080c0049104204110345800b500b007103040d0003081d16289181281c101c0c000307040c07030443c3c51954140c50390b01d200700810140c101603101c2c9464001d000850a10345404c8001340f40100b0721241804028010b0b0710440c10352103060450307503110b80a010540d241c02c02203c80550300e500c0d48103854810000050711403d4180000300310f401030305000d00940310f0800201c240302d840180140c0060034010041208802041480c4050b074083c5110f410020781d6080800040801d03200c001d080c011150344108010000340d600c07480d200054a9010120214100e02c048605204e8010b0b9801040103004041120b020030007140025885440001d82030f80b40081d1207001101d40d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 343780035 1250 343778785 343778797
    0x30a0c06080f07051c110d1a0301020f030112020612010b0d0b01030b0a05061b0703081803010614090901240303030e0f030a050d09060219020f06090715021504030c0c0902 75
    0x415005c20031622103811800800e000c01004841c00b0900340d032030008072030060340b01343c10740700303c150703503041d140340c0d10100380c442c100241108400a6003401c0034000302041c40d21040c440c030841c080c3e981c0080403c544402050780c16803501980c44145540c1d582c150400c143d8070001003401c1d5185800c8078a480c0307600a200d0a8070301c40010b00004105030501c8240006603000d4140c42d0312401c00c228601c17100000030080440590f2040c0c4540340c0780c039640d07220340400b02c2c0c079101c4940c42a41000f01c180001503840c185c180e07076000102d070860241d49802d00704a004010300041a1140c0724556240320300313007640403006020ac070b00c00d5030200a4085403103485522481b010703030402141e4004102e81a0315501c00c1000e03190707040b03800300300280440c0039a03200d10481e8081c9580d00810f190000200050700e805201c5440d800c282400982850300d0007480075504d40c4004c0c000e08054403080300e48030184a100708607080340407240b105010100d080c41c0c2800350403c038500204854404d5510b0010490545500940f91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 343781285 1250 343780035 343780037
    0xf18060403050d020a020a1b03021c1106070201120c03050610050f030604111303050c1507050d0525111011031903020702030604030305060a0b0423030a02030a0c06080f07 75
    0x1040c140d922903148040c0d8080828001140325102e81070300403688448c2c280590181807100400d14501d98410b20000315140b29a00001c0c2c0f541e4016803010590040312400015800c94449031388071042c3c401030700c170410000702c101022841c0441e480c2240790503900103402070400310b5003c1120251000e044a041c80740100707800b0605020301c04101c040c205070308180000340c000c0702014108180d2401e4505405140d030300030383d0154044002e001e0907081c4212a012548060702c052880c0034665207800b80d599200c440c3d01820070600181200a01c0503010940d03c0a070700c5800403c40d9426070f42000100110a030060500c141090802d51854600600c50061242603400196007003442c5040300180c00d1018a82c140181502002840c0040e0340c2030100e40d00c1948207480c00201400c04505110315004242c000b040e41000400041c80b0011409107005120003035a080c0b012007007086408a402c0044c000700003901445052060b000300f080c2400d03000141d80c0c60f03680c0e0416075038819144600d01d0300c056440e80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 343782535 1250 343781285 343781287
    0x901030f02030907082e1a0907090e13080702090718030510151203050c0a15090302010b0411160206131502010e070b041e0b040b0901020105090303041a1306050f1806040305 76
    0x103114003503070031804501c5940313003030342000d040f1081c04188840004c6502d03000090218009100000d28031440c2f940041c41a419103a18a0255482084502c642c0304007a104a04a80014040c50b10030040441500c0e4400300c1c80840980e01d241c110b64500a415120141e03034200351100b1461000070702c040d822076500c41c04152901c48251410b42e01907009401d0a803250240e805d4140209880406000d00720b00364080009408800d402c000b42160f1400e496140300340c0c10213040342603070004402551408010b00980c0d44c0842050310006510307210741c0030090b0039030303098010024040c84c0788091f01403690786640080c0480b0045615813901d55480740032b201c50728041400f05100d04890700300380d10703c1c58210740d10840015840c0d26500c4110382290f8040b5180c0d6000052603002541d080c05100d4210010300c0045003541002c0d070b0740e80907076801e040e010101c4c0d1241100084a040d40d15106524440d0001c608000343d040900025040c5942100c1d1718607842c8007809410b1440b880014024071031901f5a44417 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 343783785 1250 343782535 343782613
    0x8070902190c0f06021201051003051b0c0f1c080109020903120a03020c070f0518090607180306061e120302060606090a0803030108160605040311060901030f0203090708 74
    0x41e250700011190079959081c3c00303584034000032014402000b2151130f852103480c082d0f00d01000c01c24800f007002c1c1e10000705801c020034400901d080c2803c0d61048001c07006401e84030f0007001040c1c1c0c41c003040b81c1d003400361038071510148444440300b540c040340d40021559140c541580c1c0b1041007034160721882a0140d0141d02030310031221100e0507000074101481e054a0301600d01084070001e18503086d040d030007600d4211802d820402c4145084c040d070440c0090307400c81c2554203141c00403006807248001400401480604d03245490303130000300ca88007006140d100604200f19515a810307085130f0300d8030504251480303c0b500c60129a46406003041c1900a915500902c41d40e43c03184148202031300110030680d004450740d80e000c0b40622041c00514040d008041c000e004110318003860000f00d46c100d40c40442400303000c0006101003841840c402d404003070166540c0781d0311400c1000480007007400b0030421000d80d20100c1845070390500480d242d41204c00a408491485401c040521101c0b201c0d050b009131810760031011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 343785035 1250 343783785 343783787
    0x1030b030304060912110904051b0d030c0813080d080714030919023610050a091104050a0305010c020115050a17010207080708040e1012030813020301150807090219 72
    0x40b002d1148a0522000e400b848080030504800c801c1c2d07012102a045146c0300c02b01c100e01c0300d041240a5408550000404142d510081d01c2e00660b4140076040ea080055000156006451041300420324501200c0c0323980750f12203000b042c0d61800c1e03c5610010702c10a881c4824103502c2400e9074001d40884010f0104004001411403140c2c4105500701d0b0040c0c041c8455441e40c4145103011804510300c0070400d42c907903a00103045c0007000001400c064075440300a0040c012a03ea801010b4190744e42d005001800780240c07007001c480c6008507400300e41c0c0200c0c090310100401c03d041d00500b95609242d002403103c8541e250f5003e003041c910b03019494201c80c6400e001c004a603240000030a1410044000620308181c0751507891955005910a0340e03215070010302000114480e41c05075510210002103040d23118203240e8220300c00300380440081e080106040c007003041407081ea0842d4455030f50003002040240390407407501190110610441d1401e000c0c013400003c90103e540201c3e2035a8a1840c102c41d0b080e25a580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 343786285 1250 343785035 343785059
    0x4060209031518160620010c050711180402090709030609031e090e13020402040911091509011d010e0d05010e0c0306090d03023004020405090c030714030c0301020d05010501030b0303040609 83
    0x2514100c170284603100541b68000030310410035400040e0b9100e558565160902c000c45041c5020300302d0164100c2d2000c441c54624040025810990403034418140c2e840700c0c982150080320700e40019142c0d0780350044440800d6000f198501007614030410303070042c440e51000300b03690100061090202034040d40b000110a00c02e05940c001c02c80d032004000509050310703809110b00300c8100149000620b4000114000c0d945040c1405016490104103d1071034180b031100001c00c0014881004a140e10f10361605041c2a0b0107620340c40031000024016540308405414414040e00b07203081200b9103800b03944e029407903508020030302c1803103243c140001704186949660218001d6000c521141c0c0000305811000110036401e000140d800da144007420201402c01d401008102c50b001b4060222641c04284219101c0d140802c814080f510820802c1c00b00030441030210f0305224500b10769941c194030010380c070a002201980444d050b90300a0b0f80800c000e080710414103940740304500406010688503c010000c41c4c848003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 343787535 1250 343786285 343786307
    0xc020a02060d021209071a0f070305070204020903010c02100609060b030c03090c090403030219090311150d1404120207050307180f0c110c1e0603040602090315181606 73
    0xb240062400d8a250501c00c0203040030f8580328001d801801c0c0030401c00d8019a611814000c1c18480c003894000c51402101c032a01c10350b4801800d22001162210a65447d43c0c143c0b000803c010b002030000b0810484000e442d9050b40c3d030303212000381c5094004144240e5922034001a100406812451910303503003904081364000510411480c0315050b402c041030780710b00300ca65005d54401c1d1005030301c808009082c4810141405488e40c100b02c122407040000c540b02200f050302e284003c4d600c0301e130001403c2e1543c03200340c0300340003a10000f1030508101e03014212010462a10550013542c4003070308200c07001e500f246c03124450300c661a810750000344180441a0395540b03115504011050001d00104012842d0702a683c0d40c200000108060307102041300b401c0c09202d055590300c000c4844e032480c1c42c420984814907108251280740507100c0480010104000355044035001140182140c59082e8444c0000d001d0341c804440c8041151140070803c402884c0001c0d180d0304101c49441481192401c11300c0c2140c95a00355 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 343788785 1250 343787535 343787557
    0x60c03111b061b1203041416090902030a05011508070f0506191119030f1814031f0608100504120804020607020d110312090d0b13050304090203060f040c020a0206 71
    0x310880006120404c0308100b101c0740201072a450b0703d0300c2e040c260707800412244400c10302c0d0003080003d02c0078940040d505050352042d0038005008100360000c0387c50046155801400c40d0720741441d8442c1601246042c404440070341041301c0256495600001131a41144a1250010802c0c85441a02034031041c44000e41503451504078038019094481c0c61508000000d16000c1561441c0850141a8012803884211074035040c642081e4882c0040700102c0c007503601c107100080b003004102500a580501130100030f280e00c00c81001840101504c840c008040d02e00c20350500744501c01003100d50b04da003809681d01c143d40003003441110071404681503401c000018400c82e4406070800100700140c2d07170b009500352518082c40c44101040c1c06103050502e000c3d910120f0f03080182d07041c01022019a43e0420b00c4d40090741c0310740505650340700c0300714400b00f40b11130305001421030002280c041040e110700e43c0039610030542102da48104048150074001100c0700c2a0140c070041c3c1140c0650405803c00d41c0040180a0f01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 343790035 1250 343788785 343788817
    0x100207150203040f03170f04120201020f2a070f1202060403140105010608090c030604151e020c0c04020324030322030c0801020c03030703090c050a060c03111b06 71
    0x10140038049a0040740c040710881d002c84808000c1c075901c541150003000201e642c0a000c3d040000c80080b144000510081046505042c000b0805100790160303500308480400858030303804240c8100003408010a4090114240c1002807180c40d0000541182142c2e0301409056810f03040484c00c26502d02c0e240e00c2a138108200b08000000192032103840c000c00c01004000140130350411000512100d0b000e0903040540e070040b4901c0704540c3d0042901038110350301c2402c400700c0c900703000e20841c003900c078a84600000180110701040c1e0312840760002c0009102c172409030b4030310f03884841c06c0004900007501c80104182c5008540c44900390150310301140c3c00710040c11a4100b40e02000c407040b8009458032881c2c0820f21a04c170800030090400100405441030100943c2480340071443e441c0d503030200600950030181c41c3c206040c2442015414a009440301070000f481c0b0b942c407202c010307018054040003100040c10074031390140416800f05841b42400203c6a060032281c030342c0b0381001003940004401c111558030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 343791285 1250 343790035 343790063
    0x60506030714040f0e1501020c0112050901090803070512070f14070f0b0a020c0f010c0c1b0308040608061f09120c09050103030c14150601050f0d05010b03090709020c100207 76
    0xd403072010740d00034603140408a42c1c42c58000070303851201e0210801b2074150350007620151340c2680c009016264084038040002116512100c0240c0500003d5001612240f400401e01403480d030b00034010124130720198201607085d269114100e070000c1c034076070144002482c1c0c280544641d445d0040100710090140350021840102a107a05030042d2003660b210030300b2940002c207040c1001061000c45809010503000300b00d0250011405024000e041c07500410030603481d103200c1034846030741c241d4501940e002440d040d140c9848860141c600442924140e2003525034410000719144040c1508140c04210f03a41e203a50a0f00c0d180e00701c503102c3c2e03a080c1c0855012006020105803201c140c03040a0086000c1c0d61054449015820400700319101c50240c40d03143c4e003010600c0c050b810b0350110070b503400407420b20f010b5680d01c80041400780140660036030808414289000080d00800500180d4041e0444406483d0442d546106100c22485005d01134507190700031101c60600d00b281d03503000e0441c041c020320101e43c0d20a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 343792535 1250 343791285 343791299
    0x507030e03070b0a020c01260907090f020a08060904020d0b06150d0203060108060604120b0c09040e01090b10060e0d02010c0b01090504150b0315040519051005090106050603071404 79
    0x40e50b40e0300300c194030f0400480c41e000c2d515070400070010064000c0c00c011609030568514440c07510310b00e00305440c0040e0448040f447c2800100245401000170003001c005c220080f505810280d808007450100059606020615070f2905070201801254014110709c2e0761801551a0103480708002d0040b0791000f82d070020b010b1030452035002440c00716076400740141e592900c130002500300c1001900280c004c0314203102c10300101c0c401e4880140115004460103c4030340da00170700b1402c01d21404420b5900070381407990121400b0015008090150b2003200c15115550b1641604429015540b10b1400040c40503814110281822421b0707c0746903006150800300600b0b03c2e2610b0a6200c400c2c0d20050206070b65400704010b1000ca46503c07000703601001c100340410300910380001c0d91390303504298074140704100b038011a0400070304000c1d02d44080c2441c100b41c1008485420030a880d0b030000d070541075800b03080c0b40c0000c01001040c4034540c00d84400406e264115103c0c5402151051003001071000119000c00001c80c0c92 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 343793785 1250 343792535 343792543
    0x50303070c140a08031c060816150525080d02121603020306010207060c1b061205090106030804210b0a0204060215091905030c0102030a0e0f0d05040b0706090803011428060507030e03 80
    0x589c0d1a8005811401e251000c100c00103940c250b08881044001d01204c08078041030701c41d01c50320f104401800c0e44c0041c1c40e4103140d83c0c18843c900c40302003603520009400411103d0620070314850182480f060301070b500c00b0b100550603840100d550340d00580000000f0700485001d0494502c2003405140e0200b20071540405500e00c855298200d1004101005100c80c0410b059000310703075010841d54024096146581d0b26885203000740d004802c0341e00c1000707000046840d0344100414807150482080c044c5401d001260b04000c2d0300a014100050240b60302100e140190485000d000d000781400074038069910103030880201d50044406c90f0140030400c0000b821a0f402d0001d54002d11184d04000741e064400b04145103885180e04043c2d20350340220300c0d15500290801d007924100c1d8030316840b0b00d50791000340c58007400807d6481c0c8018031040001c800800c8a001c0070b450710100300384c150380c54190400c8849206c46d024000001d14001d000f00030206101c401d2103000500b0003244a8140741881c005600002030030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 343795035 1250 343793785 343793803
    0x1060b070303020304140f0307081b0a03031b0809032506020a091814060f0d0206031f0b04030b0103020607110915040f02040f031b050303070c140a08031c0608 70
    0x20f9000310501090100c602c3c0b00600a4091400070001d108012003100e0b180d008a040240c401c010218110780656480c0c4c07007440904580009036800b01d00705240c0034000302544000c0517500824102c0009a05000b18041c3d40141d0000340190b0422010301615005011154110b506416070f0f290200d00041460002c0c0080d83c15a4444082e06420050340c54001c6c2400304c001c240302424038440d40b0404280c034641d15040328040e5441c21034002c20743c02150f101c000079070000f03412150020030400145125404114001404031202c81890f64444100c00d80340034500010b007075580d80b0702c01000103240c10030082440314800c800c0031030560804400921070803011980e24a200c83d50046543c1540351610030f04091b40899a801c50406042c081916011615400001c06c41d00c03031035200403001900c6564410080100604595664107285010311400d04144115180031444000b802d80d24544820b4500030340d200b1400440c106007151203003100c80c0341f19454041580760754100c0416200b40900003014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 343796285 1250 343795035 343795037
    0x10201060522230405010c08070e09091c0302190e0a0e041b0801140f071b0204021b030406030e060105060a0c110a06050702030705031903050703050405130f0b011409060c01060b0703 80
    0xf07203460681407960035115009507480400c00607508010b8115041b10106005503001d0f2112082c6a4070192030500e441031002440d08a00392010140220300c0e0305400038102003541c0032602c4804c8400500c29100142d4070001a5400b11156209000c260225000c1c13640c0315008075000b0494195140b03544a07013510300e4004032603594555a6515150311200180c0c4e4111207140a602c689240602009000a0400d440c4003041d04108000724250b50726501540c2d20004020001071421851680c4a81d40c0e501c144180b0020908101000420800c0840d4090403202c020f00350a2401c1c59000c011a403004140c1001c40d6030012005a560480d200c000c2104042e0140303403510b0340d0325403c600415146c04104d0340f10b1446a840859100001220210394000b5180d06040284c1c54010626068415024503003141d50420340381618a407101249401150001602c403c04100001ca0600112440100f480d01e104400104010050b820300f040c000401083c010302000098003602c400a030040c60b40840c006074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 343797535 1250 343796285 343796351
    0x21612150908072f0a05040906150e010302100804080d0207051e010b010306080c030a110a0e0c070308010b0a08010311010e0405040f021c120806040b032406010201060522 75
    0x13224402134120fa0a502000c840c21a04802d4448000403d05500c0b0700866003d10307102c403e4002000200d4100c800c0c50200502c003c0713a07035525104002072071502403100744e02c2400c012140500c0a0b00646089001e030b42c000c020603140070348108050f00030394081982203800344500f0a2a07448030700e51000306000348001c00300100b000b26a01c0e0004060368400c0c2c00c42c1119801c0142104e5407071381e0011741c82c4e1f41d890380310001c01d60b600c0242c0000380350b80403a50310111000c0c0030201042100b030404c40041034414801d48031000103988441002e5480c0c0540020f40c004500b4610042c0046003e070300c00c00c029203c0501d070440301841104049400d550f02a9800c032001c20303c26081d07008524001180c2c1401e040340f81c4982c501c000381c075102c080035403088808007400c2c4005e56012440d01c0d251034200e0b9020503405402c569039182140060b003094001d80091910f80b40070395011038055803060141c60100c0e08010042c6005404c2201c0e5005030741480d40850424503034070b481001c2741000d0341003620136665607c5002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 343798785 1250 343797535 343797563
    0x150f070b1e151509180a09020a0303080402031009020d14100234031b020616050a06060e0c070b1005030a12080a0b010c14280302161215090807 63
    0x3200c10202e0520309140f0f07012003401001903540312401022143c0c84009805601c9440c0c01e2481c0c00203041201010b50494070a4901105054000424074000c6100354100d84030380b00116000000c0b40c0085000a501c409010070000c00b0030300c0c41c0d651000d07000a040954019011410920040381c2c40081000c940c00c80720700085042040c071071244c140881745c3c80c010b000905a56a0003d15002d205144411a820710f280d00c1c00a64039404256420424121802c51421080d801c1a90f52806004012281281080030100d01e0070200c1d402e0138041d228003115a410022a6583d290074160002d044801e041d0280030b0006450358104445000340d40075844920f2101c14081e0010a8075a0003480c040c1028180201c807890360f43c0c07280d10880039036082a1040c103406059500581404203540218411030840b03500740c0190301c1404410600b03a8800e8013103400080500c94540f8910300288100110f03482d1040b40000415030005000070100b450460015084145554405c156003165406445c810000124 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 343800035 1250 343798785 343798789
    0x4230303070201061805010602030a05130b04030c23060406030c051e0901110102090310020c0c1905040608061303050a02150112060b0916050a090b040803030402150f070b1e15 77
    0xe170040443c010003d03c240e60400d10043d64074424200d0120030448009032807100f512500c0c0041010b0030752819105e42d00d40c1d03642080a070141c143e001c0d401014240d034440c00c000b000b661801904001f405800d4508081c60540150001c00c050310580c018080100a04000756254046804200c0d01c000742c0c4503140c03a4800001083c4200c3d03c0c0721100300381e204200d0410240d44c005178461041b2201d041c0540d8501054881ca8208001603c1d81904000e0303188a00d0301d501c0d801512501503400546040002c1940e800b0200e030fa07a8004c4c1c540640442d18041c01c6000319200d100108002c20f4140100c600d0300324101c0b200203c1e00b500744d2120560b207070ba41181c8402c0024a01681d2001c5504961462041c00c04000d440c1641c02e03c140b011040c072900040c122803683c050111940200006070005440300d5440c454651242d1003250308a1040100f13800142100c607640d03040e655010341c111041030401c0700540e00c201c10b4240140802091340c5909088080486861800034803602c0e20031403940d400700d05641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 343801285 1250 343800035 343800059
    0x51c020f3004081b060901050106180e18031902150a050403020c0d03030e1b04060b0f03010b0f07150e0606030304080d0305060a1502030310050d0b0423030307020106 73
    0x4424030200101c0320361a0004415981d010340090300b00c004642c2d18100722084500c10100001980c010340104420451540c01c1980f0140c100c60302038030b0b520b41900311b00400284172981d83c011440010207c801040240c41c9000003a148400442e0440740390081c56030501000e094465a0b004c0184d1062030b880c443c00304840446a00030241c10810300050600d075a01079100c8100740e807403a0145036001505820f2500c00c1c0c1024080101c010141c030780c40e0003507401c00e103004000340542e640900d00b000c0e000100016030904031410455011005c2e81103909145511220303078030075400e020303c0c4002448103601044041c624600c0344081c025001601d00c0c040e2800e1401d1540080909201c0c1e0000e000070451410302050800811080b4030300015203603104400540c60007000d8101030390740c1006407a07610625400100440c0500046071040e16500d98840c100030700c0031618070004000000c1d1102050008250422101905101324103460050812643e040d140d40c008032842c10040c0c0d100d20007048000d070401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 343802535 1250 343801285 343801327
    0x32401090b0301090803071d0916080906010e061909020a03020d0b0f0618120303090102070b011203090504020702130908031915030209040201180609150e030a03051c020f 75
    0x50b00030720801c0c0158643c500d943c00300070040700a1000b0100484d0903959003500d40d01d80140000d0030004142000711010604201c0030082c1404628150b001c15014080058560f040341d481c25080e40b6541e58840a05c01d000181b00703801800403030f4000021415a48500203090041823550300140c45001d804004402d84a40481850140000c4600b200ca591544022125024040e498442142d02c1100100c0c8204201d00c99081c06400f001c400e1080c1c40c1019001403030140d0058034000c11698841070307030742c2845040d44030083c085144200108010704181c3c01a00005000400f4104188104e1056009551001501700c4508000004001889144049040740d0002104081041000c41017210711345032800e002c06032140e4081c00005007160f125840c000040103841440651050f82d07040081c0444665001d00a8501e0100307095104407442101d4050b01d1440003001843d1902c1c03261400d0300e95a0202e003426150391a02c09030b004d2902580c4c0010121500180f030316540e00c000080d02c50140762240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 343803785 1250 343802535 343802539
    0x18030e0d020307170a050709090318080709150503030c0109050d0203070c0b0c0f10090203070e0603030d0b0f060c10060609081b030316030c0b0f10090b032401090b 72
    0x800000c00240c1c40000d680ca0036200d80c8025216040c81c1c001e02c0710f1900184520041292058080108129000d90404540c2c1403203a00e40c015640e4480d01c111546011601a820f06035000b0041000800140d8100354080000007002c9070116880d080401e04643c4040000c1446070f441d00103000420600700000c03400d94a40e072024500300700b200e1351a401d106038548182c1640304804070340c0190014091085400c042c950758102c451080000c174401e00a0841c0441c01d0384a401084000030b41e4110301c030002d900c6480c0040c041c0d450803080c0b9202e00010b000c1012010b4100d4001901c91405403a44402001c0082aa000510140840d0300d045019924150858410803500b44020012407000090045905454441241030108058007003461401942c403040743d448603c01000d0203040c1c100f0408500d482c000c2181070815034031000006440c41040c1d9007042100d900c3c03c801c1140d0489607010440c5132000800740c50600e0307905031281c06501c00e001144d45c9c041a54000401110704544910343c0e01e0101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 343805035 1250 343803785 343803799
    0x230d020f01150b1c0c1205070e06070b07030603020604060504031b050f060304031b0b0103121d0f0d060603050606130b010f0c110a0608180705030a020d08070618030e 73
    0x84000354202d815000d220710700c9807101c04214021400030b80b0804080c03810385142c4c1084840d0b00801c000b040d01618081e90001a0f00e4800440c09583c40b030440c1c1c40130410003502d8a07103444059586c440301035500400110800d036407144040f00680c0d600009100410302643d03080d0b1030307d0650402c85100a00300c0c1c0b207281102c490000c100200d0300d5456445050a40442e03d090300c03541d031802c09507030b2851001d0000084032002030780c42080141d0200681d058034000c00d800128009078400c20303141c0d01c1859170405030805043c0440100c61030443d0001c4a009400760101e0301062560340c81d10103807407140d042102c050700310744204401e0f03003050100006902a4081e0901a41c03500d00300290074a40300084402c1004a89150041030243c4c80c20040c00900b005001d04450540d6900f0080402c0016102910f107003e80c01900c072902d07400000d4400988100401078414009242d0800400000781c210440e0100000e0110901041042c0b103a205d640001c0c260004400102c0c0c50b0040401030100744481c42581 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 343806285 1250 343805035 343805051
    0xf06090d090f050904080a09090c09061101020a0c1101090302041514090c030109181a0a110c100225030f020601090504030e010807230706060e04080d0504230d020f01 73
    0x911310141e5074101d80c01030300403a80c82400700011180e101c11a00301c03003c102c0c186010300340095031140751401151b1456990140080030406428280e100e442985c00028500310035000225503040d40b0310f18201340505008255503520f0303000c64161400180303c0421009030001c20410523034a50f61925400c0000c580f0030000d46050030b5000f500380010701601c64100d035241510b40c200f400c020300c501541c07074001c10100c1d4407044901d0450b20040d0102c5150300c00c039042c144010b1292002105031010b0380341c140054811380205540400007900051000060105410710b44060146074140da400801c0c02651030400b2403148090280c0390240c1070b8400e1514510301000c20020035840420001c060304240f0701041309454140e0102c945403039a0860801c03115034000ca08043e400468020305440e07220b048240700541d903030003160070240d908890280c801e0310100405c00e1405042d612444d0300511801d00c508605004148030305007200840451415648102e420340115501001040c01c0030703243c031000740f000b04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 343807535 1250 343806285 343806289
    0xb0603010b031303021f0203090c06040b070f020a05040e030705070e060d0f02150a0905130e06010b030705040e0a020306090a06150e03010e010c0309030f1b02120f06090d090f05 78
    0x8403005103d00301c408088508841050700c2407101c1d05000d40e41c40004440380c5e00d402d600c07100079030081d14030042c1c42c86092102120340c2880d0059a0460b00560603441c01c0544545503464020020300303040781e00c0174172204046141e58840c4a0261103201b103100860f124281403403c14a084081d0704040c0041c0c0c204005c00c0308035500d400205500e643d00100c58001d502c51391010030003210303003400700c1000042e011498040c0c4a51200c240001c450701102d80384440d11403403401c001150440240d1801c0c9801480c010701112042e4402160046840c0c40d095103000e644a260b02902d0b60150b55840005070004280591071074032502e40b50300044c176102c0070801689044590862030801c18452400d0005031110a11103540a6002d01c0c00326030304600034016070b210500d00900800001c2d0301100490803642b443c1110b20301c40d0130382000900d440c041c0042002665002c0114891640c05a06803030712542c0c020b00e0980c0810712101d4000c000c560000d104880200b0070107083c140701600015078581c5810340402180d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 343808785 1250 343807535 343807537
    0x307150b090415090210080901061202060a0e030f01110304120e092205250f031a040606050d050c13090201080a0e0309090114010f030c0f0e011806120b0603010b 71
    0x2c10340c00340c245624203000580e043c001d04200e00c40654060398803040e074000c25801a908038459403029000300100c81c0c40d00721a1041400c1d20070040e41111041c0144410380b80182d1030f00b841b0a400904031000d04003004000d50a5944ca000d08601f0800c000c8240410801a07c4c0e0003c3d81c6011360401010a102400100729094801004601281c40032500040c80d014010a080062030300001914105404c200348407449002c03c00035600c0c0010800c90010340e0035800034400003660f0340100c0d42c0030705601d005222044c00c1009071003a55825590368000070955201c0300d0212402d4420740160000d03031011401c000032010350310b040e400c14604004103440140c1e030100c6007581c00f00c0d8090001843c1e000120003140755004140b0780c650044001d41c008902e0420540015031109026070b40c0b06003102201c001141642c082e00f4020340800d21030040d8250b854010440a20600c0040c94014010742c50308043c030200c00000d0344010081040041d1980d104100ca0044480315001901e5061655240080c0d902d07003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 343810035 1250 343808785 343808791
    0x3021e0a1b1104090f02030c0f0a030f031e1d01030221190606050d0b061206010503041a0106030207141507050c1f05071101060303020d031d06090307150b09 69
    0x741610108000408020504030725001d802002618101d15080d000d03c40188400c2c0d102e0301c1821104811860403001500880f040500700e8550940b07141e0b40c1d00b2098055500c01c6041c070000c120400040041003040325a0800507583d0207000303012500300d101c0a03100c1550a0ba0415004010f1100016551110921000030700840d610040d507404100d040e10901b10ae412480481c100200040c2180c3e0100140c001200c081000300f004906003401c1007128469030380800060700c103510000b86550302880143d6400b50152410301e03190315420b05043e03c905400d8000201003640415480306004081c486441c442201ea4024224000403942600e0a820b000780b804040000019110351259000d0003050f4004114460514081e10811040005000111819000994180c50342e0703800f440140100300c00c89070150058078840c2c07200c010440c09031003e007651101d0342a200341d10170540b5500704801c61088107003101668a81d0741c02d15000a0280003e00e94400d11801d01c41d0125480e5214210f40d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 343811285 1250 343810035 343810067
    0x1030e0604170c0109051c08070e0f0f040f1b020d02030c06060603180a030c11040b0d1101020c1801060f0f090504020a03060902030a06080105060307060e0d02040e03070303021e0a 79
    0x14661107810303e0103005d4610410700402c01d014a030142c0b0484c58001c24005188001d981b03030385265548542c01110b000f000b0320a4150f0100c500c450720045410010b1224502d420003500c04140803030384007102030607508507008010004446d6081004140d40c180400e03001102b00e44007440c41d0803102991590703201030181c50144a41c1001012a4802042d0984030600141c82420385403d40201c1c01e02030a11100c14000356400b100c049201003462500b440703404501000140003a1190600e034540170b10409400b40307010306600c2502c0c480300469640d202d2221181564030007280d15581081c000504540b40130b0f0700c2c4400d018600c08c00303150680d0084111825210159030068585417a10011000b8201c030750300c10114184004240421140c0f560803007001d5425000c001d1010791038071828166034001620800c1d0004204076101c0000d07280800c0444450740c001400454100081c0c01c090341190701002c411400300387d0006065140022031302c5400d00f102002c190540c2400c002030070240041c24900c284030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 343812535 1250 343811285 343811287
    0x1b08150609070504080f01020301081011030a0b0604080a05032205010c030f090905010b03090f06070203070209040213051815040c050405040303140910050108010c0e120a0b0f010501030e060417 85
    0xd81c0c42d44104242c0300144140300884410440b00c0f44114001d601c2800350000d18000c805244024000900980c5511460a20b140380f842e1b6880100000403c0c60360029940840204400140d1070380070030000944901444c055aa50140d0b03010321564030142c22404001e000e0100001c00070b6030382200f0302440d09609418404002d1610080c2110020f0f2180c00404000d89040d001107111001c20001e180b00e8042c40b0100d038142548801555502c041c200c1c1d072030006920802142006040551511346c019102070329490007811101d04103000e82d9411a000281f035908040c110384884400c0290803821641006480d15a00b00b07500c40c3d084115013405414042c0d500e60000c902010b10039803011403044a441c001000750708003e4405c0c0e40740c2001014100017141130400124014406104041c550a02601c4550348580e60343d050005008041e400f03400907020382180350012842030074140d44500a0706540511960500c1c001504480340d03c400503035154001c20410001403140014002109170002e00c1c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 343813785 1250 343812535 343812541
    0x603040311030a08061c0507170a0204020a230a0806060702240a0201150b0409090503070b0103060f050a18110f0a0b040305060c0c070614161b08150609 67
    0x541e0150038450207408a44800107000d1910b552120003680035000c1120764000000903014125900d40080902070510340082000b009081485171035403820b113081200365403882d2465000201260131405114003c5000550030302d802c4000c40501c07181b00a0800c070101e00b0013842010040403000014002c40c0140d100142100c103540c1c0b0300c00d11940318802280050000f022031007980b45603812410492005d98201190003080700c800c542e95000743c030740c1c0b180300504061a0a0a400240c139100b401a075140c0001c12001740483d042c07086c0c09010f10f01810307011858084a594420854038003e20307002929141c10523240c0c49070203e0b04601105508407035212401044240090288041b4441301a400488903070300103442e01000000d801200c0c060710903030f400ca0303130b5546510300a4401c114407803520790810320040c020180158461910000d0300c1081c0c41c1031200064408585004d00c4201740c600300c82200d0b05400002882000c44054110b03107015200072f185030700f8000808840a050540700340044000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 343815035 1250 343813785 343813787
    0x80a050403020d0c03020108062b08040305030c060412030b030312060303090d2003150a020309030904090609060c0228050a02030d11071a07080a02010f020f13090509030906030403 79
    0x103503806550000c01403010004585080304560703195110490220b032030381d4002401440d002441c0c1844e8114600c2e4036500303c00e070701c5820380540b80050045540d24014440803002c12400c2002d0659400490b00030301c41410309081801c04c1d1000d80501300205030404915150a48020003a5050001940410b9000742c4991001074114024000e080303412424201c0001e00b80400c4c131000c242d010b5410302d514060407140700103040e12445840340e0300d0704581e40368000c2a40356103258010341d0f01441d124192400c1c8142c0c2400a800d07104190701c15202280c0ba011074000740442c42c0b01da005203512900041c16440c0c0410020340a2503401c0500100107003208040f00c051103014048203281903401803d40f401d102c2035080c05007821a0115010410348642000420b001d040410321420300b03014482ca050402c0615035a5080326846003001c0b1045549409180c0094001ca0025107224001e110000d0780355988001a103142e15482e13407007100e201741000140807201d5404001c0300c083c40000e13100c0310f58aa40d10300b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 343816285 1250 343815035 343815037
    0x219030b01030e101a09010b16030302070c0e1e01051516020603010f1509030218060418050d0e01030203250c0b09030714010902030d110a05011a0418030c080a05 71
    0x164090503010f5913000c808002d0aa901c2400303403070b111500000442c1d01a00510018030400d0140b0307605240100305030320802030702c00140050f8034400e1802618081c295070f1180d945c04941d51100ca482c00c0c41c1c030240a003040340030303c1a400711a0350117640081c544c074120000390707002840400d900f040100000d0000c4034114400d0b280b20140c2e0083c000c4c40ea40e5030745401d4414010503501c5201c86400b8440d181100051003554980b04a03034000306103012119804504151004d0003801c0160701640c0d51544010107260740d100a400140150b010b4044080210f0010301003640f080010303070401d0300c10000c00c008408040c0801003000e4154035400390604e07072084240c1d4052850117000e07008110300000c2110244000004180c0941f050b03504021514074601e40354269006031000035456001300b108540c00324410544c0d907110700d4a140884d07848130401c0d1586801c68181c803480f80c05070b0202c0541a01c581c1024010394901c013541e1080f450700b0144a032001050000c101400030248640042e0396030a10348a14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 343817535 1250 343816285 343816301
    0x306090c0904020f180406120f08131508040506100e010e1503102a120c03060911040f1d04110a1503020a020105070801121403070b0f0117010219030b0103 68
    0xb131541da6201841441c2d811031111a020003132180b42400c0c00031031260300c0d00100c011180d501101a03052064595030340b0b01c82d0b810900b2008440310014100080101000c0003412203460706032140c0d0018101400d08030306100000703028244c2d80c000e2100401c410006550114112140445181c0c480d403680c061100038640710b80d07986d6034144610500c0d4541d40a00350300089140004124210703600d11103480c06001400d4204660006ca22820941064010b02e45c0107000c40c1502e40c41c00107030b01d5841c0d8921030225240c0300f02020032804041410300100007813036000400b4042c03c000c41c0c1034a215410000d149070100030300040c1401c42c4c0480c00c070f05603101c041c0003002501e42d1030100000312003100ca0040c02904502114801907007420049082903004000d124183c80c540340000404220170744809040e68070111401c011480204180c801041c5031128081c02218402d80056555160401c040b00d8607001030322a0040340d2041214107600545240c02250394501400d02141e2038540070016030060003d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 343818785 1250 343817535 343817557
    0x24050a06081b13240807081207030f090e0112170c0c0d0318060c110a03021e0105070602030903040501020f060c030a0b011110021c060f03081b0714010e060306090c090402 75
    0xc101400c2e886030103200b002511174040840e4607a0f40e0790002d40744e40c0c2c45199004105071108004000220f03100d100034100786901030808841c42562415800c4413004240e03c80148c0c848481900000c0004010181c0350328500c0401440c00d01120b40d040c0c80c2c44032030f00c0540910411145107400101401211700f403101005071342d071803d065691a0009000c0d40e06041b400c0307070700070b21401094500d86000200c0d4000ea0b90081d04051a1103921032401204001c4199020706115080c8441c0e80061501d000a600c240303000c3c0d0246482e5031074500060b141100c0000541c02c19000f0710f08003c0c00c40102d20690740d00150340e4001080310000c000040c1e480c40c8030b0358140549402042412282d40401d030b00206030315000440e40000c0d107881c4100c140112070860050348640c0d00c49c00d00404c00b1514101c06040e01811594400ca1400c561100b000d1130a40240d00000000c0320075000c0601c15070f003100604c811500f059840c10700c1c45c501400041e42d00c443c01400303004038072004031307011541d40c0b540d506540030300404c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 343820035 1250 343818785 343818821
    0xa020a050d17030906040b01060f02070b0f04090908130509010308090f0d080c0606101107030b180703030801090501172a030f1c03090305030c0724050a06081b13 71
    0x61300c11151103540c2190191480d407619800002c089104580c0c000380c03540b13a9405008401d08013100c0101c4d41c1e114441e0f514900009000202e400380a42c403400485501c01c2680035612480b4034200c003100c00f607a9020038840c08103400100b011a60107030483c1c00300f00c0201c6610000880e40c000040f0081030022000c0c12040d40880d00f14040c05001480e42c1c003590b02214852590686070004864500c1c0c0d03e400441030340c2003400104000380101c03800c0380c2c108000c2d00903034420b01015071000d890802140c3c815800a880351004021440003449200d0243c46862440c3e40030b02800ca042503618155680102c120000407821440b5000a000b250400003900030281c0c0c1d41808001c20031941d031501144048621000c1841c03d4240602a20800c2c2e13406a06440d52800c543e2032010b10704258000f080c007940c00071510364900c0100101c403004400004c18038500011241420030314a4103d86039a000a16694421151802001200490b1040e9107104881d00d8403003c0c0303902d0800f009414070314040180494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 343821285 1250 343820035 343820041
    0xe01020a0f11040f0c1202091c1511030103080f0903011508010e010515030703022b032705090c090402090d05010509060c0712080601020a051b10020a020a050d1703 72
    0x45150000c100b50030115024000445198169002c40e40e00030000350224460a40000011401750042c00344080e008140050702960348e2200c12480c0c083ca0000c4455081c00e07810481000303802d00c60801502408443c4600755811036440c140c561044151480d0b82341808030318644c107a9801d400111020261041c2604c20564842d911800382001a10847c915400c110000d10110201e020341510801e004004154840c80e580a006680c2c03290007181c250b10300c003c41e0303c02014800f640d031083c02502c20354804107048512105620201034041c085921004030f9003040000d513544a100a41082c1164002c0b82e80b4582c000015000303102d045c0d500c58200703104c0c04410f8180401940000d200c5c003041402d51b00340f075461190f004000d03c6400c4005040d040c04010008103d845a00a01c1d40000180111103c4460036203d01c0d18151107402c2a1105140d261000d14140c1002e60000c000031071700740000c03c1030148a0f0700041d2840818007070140a18520401b040c18080c01012402d90390000c610055a241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 343822535 1250 343821285 343821293
    0xc071203121e1b1d130e070312120b010804121202070203010608010209010f1106040809010c02031510060c0809040f09120f08010e010513050405010f110903010e150103030e01020a0f 80
    0x880c0d00044008100e0900e50854a144403801403c04004002c1c000e242c5d00100265410007400c4d04000f0034450301c52004003000040c80c2e0580c3c40440741700358590b8005480c0500e510000d623100880d00c981002007076424071000403807440c0d182c4006440c07410418410b0281c903641d20000d003d001c501950560904000007807a4406600410f131540c400c1e6641044d902c5021400d940d2400400e01d84011540503c0c0041c011405050150071307406814034018041404580009150000108440c90200c80c0001071041c2c003001000316500414403801d1132000440700351036040c860700510f104613000e2611111541e449044503400343c42990b42c8200302c80410964040300030111021132900c0800304030701c90700224483c00c01d4076040303040302c1009140341d80300d0310202070440107043c01910440f955034850f001000c2440642c0610718010562003042615603800d9001c25003914003c00d0907449580200030449550031600740d44905607a01410182c10344005400101c0c40c0c04000c0001400011407507001c10100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 343823785 1250 343822535 343822571
    0xc01030212062e090e06010c020303300405010b0a0812090118080609070f06030b090109020a03060b03130519030206071b06060f0501021c02250801020a03020c071203121e 75
    0xb0b24205e000180c116665100159007000c62a800030303603d41e00a20204d0007800e4004c074501100c010340c3d8500f20b003105045070f6001c800c180580e000c40b4a651650f0196100d401c0800b0070340300604241d8010400204810138014651080c04040e50400c4110b0020110039000c0c2031191008103a0002203d44601c2c000062076201d40042c0240e40c1290709806000546a1283c050041c45c6940204000c40b80d0f46071024440c0254080401c0300103140c0c0b41e00000844000410145224400305480c0443c0f400c11407500a0230502c3c3c1300c0501410307481d0340300380c40c01099000422690203515030a01020321071481a9540840040400041109040c041d000c501d045030a00300504a60003070b001c45009001c005c0f001c0030100c0c900c5054800580c0020f441c0303000c40c100305441c5444a0b1521503554150303030300d8210701820381c3d00c600d0400000c60b400041c1c00003003550401c218001800d000c10352800d5880c180c3e030000c040b040e0f100b80002106451762020a0070410348101389210700076500040041d000408180241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 343825035 1250 343823785 343823789
    0x90b150d082d0307051c0e160801060608040c0e04022d090c0304030f0e0a0506030c03010e100e0c1b01051e10050109031e02210c01030212062e09 64
    0x41050807099080b128205030580e805080e1541303519091044c0c1d104098103e48540103908209038448000c02c0502c0c2040c407501c071040d4100c00034890b5084c2030485007400e4464591040f82000503920030000400e41852540c0b00b600c52a000c04051901c0302d0000401c4441c9a0302c04511081e00c0140e039420b0010080c0c0f200301207541c151000a8196285140d90801703010448028000c200c240b40e81a2485106a900c50a20f0400402d400001138441001c070f1442d82003290758000c901c000200600c40581003101c2c0c00d90180c0300210703011415040c044801d103002c1016242c1e9020050214482480280310030203400e4148a41c40200b100b4a040c1d006c0954412030b0719a40744100350241c020410141c04070802000369501078540c80031f4540341da503a000b01c440da07001c0503900c843e86034503030b410040e960740074102c0030511032148400c100d07400d110000f41040c0071040f10701e042c544100881285081e445201c3c5070310540848403000400c0400d24224017240325110681c02040d20130502c03541071600407804000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 343826285 1250 343825035 343825087
    0x90d1b120521070204051009060b1e09010f050d0b04050403020309090c0a1b0206070813060915200c041b02011a0307030f03091505120a090b150d08 65
    0x24581441c007107448001407085032140b4040010494103000d42041e411040d001001401e00324a644d40d84c2c1c1449040700c5998020119000c0e0005100282488069848030000600d481952410241a001a103031b40084d450340d80600c030000c030b54010780108950103010301c5c09000c0d2082c8141d103414a0002e469601c84d02c0441d01c0341506801288400482606440141c003898941590b0000c842920f1010031110710001c0b64008810814600000d248078080d2440b002c40c4855031140d6030601c0000351010080d41c000e000390305040f41c980e0411940c44910908a43c00008000d0380680126034001e0401d40303449240d5070428144804040d1040c4203c40681502440354020044583e40d804841c04051001c80c8241d89540041c005001246000c80d80041d0f6078070901306000d00c60741ea42d060b903c80d008141d040728003095022491500a602d2403a01d9503020500e02d030100140f9081c2c3e5260841d28201402404000c24400e00d031055075150b019048401d01d800908990320340c41b103d00e100249101400c2601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 343827535 1250 343826285 343826293
    0x30b0316060f122d091106070516030501061a0328020d0c02030d180b040b06031501121202010c0206070e27090d081303050d060b0d050702010c1103090d1b1205 70
    0x11481c3c024511a003071708207a01001113404100d4000402120b90888001134a40c1d0080751801d51030515445090740065118200120f4814601500e844c20303200600c0720502c40b071008008201d84d146009074581d6940b42069510b42108c5283d5040d02d0003809410319144919140203c280e0010303030000094544030001342814803407044800c0c84810381640c2d0359001042d5512800106001070340340100244e0192014080b035200801c0007100028039107080c0d1100070300c2c0d4801d080400901c28840c400701d000300b0590000340100e00031741030020740d181002000b03082007200c0101ca6283c82d80e07900000d4100c0003030b92640210f00c11408401c0c814110000d54020340d1360304c924400480000e015144091141c02130780a1b1641d049081e0703e080ea880e50042c1c100040090380c80c540810b9032517440303000d81034507580d0610004151074500b0001e421220104160414400007802900c1e00a13400422120600016a155117041005207130108c0c0b00d414450000d8048641180e000c620301007840b04050000380128119 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 343828785 1250 343827535 343827611
    0x3080f070215010308030c0c1c080f061f05040b04081b040b03030a0e06040e0106030231031b05100f08060a06080c07020d05060907030201030b0316060f12 68
    0x3aa41c0e6503106800380c1c0382903a0600100089542040550b42c048034030b0211524084010030150700305480b109e03524400944550551515a5210302c0c00399000c1c07030450b10001d07181807a400182d201d28001c8006402120050b00811381c0c2403041080d20014075840890302d440e00d40f01d03014651100c0c030340e4030a0320306112109040c2c40c451616000fa04050040900558a031070300024080f6060104061103941208041000086280c15044050300170041c0d55001a143c0040d140c0422202c1a02541d509102014120841038110b50860f40300880f43e00201e0054500c00340c005014101c201e940c02950300c804065090007019410185100c01c22081d82e071459520380d80d401c1004400d94450054000183d15000010488000d180040c07410b1400107103144500b0b0110382d901407a00d881210244001c1d0020f00c400c00455070035000f542e8046c43e00700c01a01402e01032030b000041c100168460b013410402864020002e090040001d8001201c041c5030a00480004251040c0030403000000ca00740b4201010701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 343830035 1250 343828785 343828787
    0xc0316021e0106061106071b06060803070b15090601020303060d02280302030f01020408120a02030903010c0504080d0509090609060d051c0905040c020d0f020709060e01060905060310030210110a03080f07 89
    0x6c818441c3d001a00c070304040a900041d170041510500380708440072541d44078040b9481908001401401388180346884084c079003188818035022a042045000744006014060309a03000700985c0d038480381c00e850003465402140006418191103010180795541c540d1012610143d440c244441541e00070380c201d41144180e410410b08070f1050380b142c001160451000d0103140200306004042c00320040c07045030b082001c9900000c0c01c45003010081e9011034000036040000c00024403d042e05941ea07070a166050a039910f003c1208250300038400d074850a01240001c07056681d140075402c15503040001c89480d60050000c01c0401c0b044c1903448404246d50385000200d510f0039015140c1e2072a07160780030388010010090140c585041404021065006164002c80d400c007007445000c00415000c050800d8035450084064801720068100a004001c10820400e502415404000850b541903c1d84c48c4001c00201c401c0310542800741002d00720b4040d021840c400e066021714018024003100340221610340740e00c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 343831285 1250 343830035 343830043
    0x1051f05010e01030f020d0b120a030203030a050603031b0d0221090909031c0212060a0501090b0f2503200a060203090a06020705060f0705030c0316021e01060611 71
    0x1416214490405414400e9500c240c2000c20314100c103040200761000c0045040c01a80c1004c1150800c0d6036036040e07003254030710741710742c2c1c0c001007400e00d401411006401d510029202d100051610800c1030303d420100791151000c004940401d1b58941041d4034403541c0542050300c881404d155180144100041031140e0000e0403610b0130503079403010105250008850038088810b000030100f0607140424400028801d1000f984420501c2514800503a41d0100c205810380140300608818010002c2280601c6181d800803c0002543c18800c404c90f12100030a41c441c0061240800e845906003000c02011814040c625094007081d200c0d4995030040040e4000c802d10019200304044015403080c0803000102c0c40c2c5600841e0028001d1041d14000b62141d1964001d07a0301c0881c08907501d174481410416022100c00b60a608964070386802d501d1410034003c0e00c029400041d200d02e014650254144810301e00810060780841400076406031101000701005008000510900011580071445089125004a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 343832535 1250 343831285 343831321
    0x11217030708040201080601020c090c070203070b13050105130302032d062401090503030304120801080303070c0204020c190c081002070807060c17040b060109050609130c03140f090105 81
    0x1a41d600b01940c1c0e25001142c100102926642c154051480f20302407584504501c503208018280035281d4440707552061526160243e4406010344805009800d641d084060000080701d609181031516840780700c400200780229544000d40c07520499121a0030300f04942654120301440c0c004105164440c1d40310316480310400c07903483c0090a6190450160001140d0344030712054418584140c40356182d8001c02d1450b40255810741e20038500007203003407029074070100e10b81c00340c81244081d40c254101003201815181017528020300c0303290045100c043d03c5808000580c40d9240c9488141d40d0034149041690141c24140684481030180d01c900f150100901c4c001c40c0c0f103069105424601d0b004440d03c0341801000a00103d5081141070350002c2d038541030030200c0318000d43c041c3c81034984500b072480014264016903071025004000900002205135203c841140001004683c0410b00e59441d14044009000c5144081350f034912000500c81c09200c16080c0303610500d00140200002e0702c2c0c5414048500b0103031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 343833785 1250 343832535 343832537
    0x302090a06050d0905030304300206241f0e01091215090f0c05030c0d02060d1d010903170105180406021c0207050d0e043605060112170307 61
    0xc10080355120714010000b85944850001d03200ca240d940340d40c1180e1041c1c0d0705032141018401200c030182c4070348581e824a40720302c03041010030400e107030400f03512180c00425502a988580703851615072100710305c1c80c448000b0300612100c0b100e003000260f29070ba103040c640303040b000074030002c0100c441e0350050b00c185058a84210101c148003209035242800a021440e601544035104c042d035070005108040c0042c10184a01c60032012035040a060501d000703603151145200348207140302003015885250845940465414002c560003100c1c00001640610030704c0040d03240e40c609812481070581c01a4035142a072800c40b03d9000300d0340d03108100a018454900091100d4a0000104000500c1940108240d1444850529514404042c01c4080f038000c00415280c5402295503900c0441e0b0110304440050b1040341c0800107120800c5500c0040540b4607181441e6150b42c80c1809044001c201a01032551340c400101c403a03541c2c541811070040c003849502181d583c03075241004d0001c4010142940c1c414442c0b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 343835035 1250 343833785 343833799
    0xe0c0c1b010e06091c0305180306150904020a0f0b120a0c05040b0307022d0d0f0906031104090f06081b0d060203220606061d184201030209 61
    0x15040402203d940f20707941095101d0800035600c480c1c009a4186008040e001c0d0f00d03280c0c0c560405041101000170b1b501c034028803d03040702003042403a0032041c030718213214142510340c01015613031803011500101450300160720100c00d182000483e80300300702c001c180b000800c426903241921340700c0000003620902892080030980501050055034440c00145500120390b00c1111051140c2c4000b06000c40ca507142c00c1c451607260784074859180c4070200001c030744c0411715203048204040c40c0f5800404d4071000b400b075442050345a0b184004511801001c1d180540f050003030070010404800700404c000d0203d80b1541455014810220b413203404e10804540344208083d2501219011951b1400d00a6000a00c034011905070405800382102100e500011300c41d00c107c50000b0030340e040800180603511040407002444800441000e56501d51013448050300c2c0ca006031300a46502c1e1181c8843c0214841c0860021100e02c05a8619000541400090004840054113070140701e40c00011816071040a40c0380d42c010322 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 343836285 1250 343835035 343835057
    0xb1503100807033f050a0e0108060a03060e030405030f0606010806011e0806150a020c091005240702090403090f0501050c0d3002070c0803040f061101060e0c0c1b01 72
    0x81a00104600d40341d5245084c2c480503450410b210b4000b0312801c1c8200080c00807801c0d0548a070006000303072105100f400c0c07480c281d1401d240094281d1025000040c00c09407a4070000707503c8041007040e980503120003403d4aa00d4000c0340d150650390b02e0111016400180b45001107840d5501a105114004009581c0d0304021135120f44166002c002c00b03400d40ea0441d5424075003000b00030600c1c000e044221490360284c09265118000c0182816015000c000980d1b1902d80800c0160384501c1d180034002044008108048c0302031458003083c1c0507811000c0d400001520422041542c488034a1064446965070b000f8401c1d122401190300d8012207104250039400400c250660764040c2504070005800100e0040050081ca20340e0078014003d00080c40840d500032400704200403078505600e01900c40701000303500341840d0000f5034041400d90710408090100900240a5400c0c0c29040f00c0c025140c1c6414000c4c06007495201d1804c150b108001c1c1081c5401940582d41d5090f00061314040800016550052084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 343837535 1250 343836285 343836323
    0x8060a0509042a030f03120f0e0a0b04060b040203011d0106020109080423030318040506030a0f081c06030305090f010c030f14040f080c0a08010504020d060f0b150310080703 76
    0x410f40b200c1e40080841001d03000000070228241071881ca40b080e40c1c0c0e071a071401101145000d80d803400d14400c182d03504210200910600c00a0003c003402d410080205082d2114104600105655030380303035421600000002c904640703800c07811401c0398994486101c413a0f982e454103d0032078010f04001400030004102c02c010000488620500c2c9030091880d5120020300d22001a00e10340c0500c1c40c42c1c0c0d4076070081c50b140045207014890640c0c055804d0f0301901414880c0c2c2d40d011003014109078020320041020440c00116500142000c01c591007123a130803c49640c59040280c00394001d014014410b9894128908003035115046000d56268161510380b0003281c001c100b81d41c1d115406500501d180c1042c04001400180b104441008081110241000d88a14400d200c0d542d10950048101c5a0408040c8001038451000c5c0101d065080b100006410b01d01c000510f01802c0808106503019811a420306801880c0c0380046004010721b480350300007156500780c0b46131296040d100182c814481006090050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 343838785 1250 343837535 343837583
    0x303010b090d060b210c1c0b13050109050c1e0a031101050f040e1b040305030f1809040c051314010504051017060f1b07060b031c08060a050904 63
    0x5244115000f0403252a40004581c110308180700504410515403032000d2065004e01032080e031101e040c0c1e80d004c1050491f8404950003044600003e00c07070a40000061810780f002100c0c1c101503903105001b0300c402c003c90304003a9540c51072510414490500360303a04058503150030650b0201c178600030303204103011490350302c42101c58103c90500ca41404000c1040000c26100f60b40200040c290540713503a0450304200c880311036a10441851051164010007003400403610010a07104041e0001810556400b03210002e0f0700c040310b4501503103800011303010070704c0200503180702460181c42c0151058049c80002c1140c01050310311120240c42494602001400703e4101030b0006688030031481c0351500384503541c0782010700c03c04103c0c00b0507215070880320602100c0303410241c4d090b4104100c1d051010a44170380c00c40a94080c406d01800401a036600d410401c40d80c2c809010f546c1d00040018100224440c401401034a0700e0011a9068440c000114020030913252901c2402d01654102c2c0424184002e800c25402074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 343840035 1250 343838785 343838809
    0xe060f0103050606090d05010603120503310b071e050f090f21071a040510051326010f0e070b030901060806180d081b0a0905060403080405120303010b09 67
    0x2e0ba0821522002d03032038051218030305603c500300000d00d140c91800cbc4840c46040035800041084070800a0103840701c10300c0e8056604002e1411103030f040001c821200190160100030080885141600304905a03402007110300c45d01215090111081c1c1c5026001c032211320404080101c10380c41407020622508140100c41c0301a84040d0400c4000d91301c1074030039207070704840311407524055101c04e40c140005000e1400610000b061001070300d06081c1090300184203640c000d21400c04100e80480c5007900e80b00135041d600c000306003400751081161f00034032a0b0201e040790405030285541c00e080800c040b02c0a24401c01d0224001140644031035400d240e8120015480a07040f10300541d2a260042014032090104902070041080c00010040c01001c030175060074022040a014803108004028110070241c0c150144100119044c41c3d44004242041c1c0e03c8000d00e0308600d40000b8041804420080380800800560b101261446d003070107002000780341d6070701c400d014a460882d02400200080d041007010310035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 343841285 1250 343840035 343840039
    0x6030a030207060e040f020d0204051003050103080a050f070c060305011d1009021c05070306090608010b01080402090621100e07060c0206070809060711040f06080c06070c0515130e060f01030506 85
    0xd5806c1100c81d200d0903a0131031180145070a600040130042803500350240340001596050500c00c40d85161500c411501035042030000b44000066028000300b10002203440075640108400000768484078004d00512090040c004d540c00d0700401300301c1c1500068030a86c0b0030840e17100f0111320b690814a5400181d04070842400180c2c0030154080d030705000f21b00403d0f01c08d039500e5400040c50341c50b25401e4000c0c0c87d100c1c0e005134140c1c2d141c2884040c2d1a6841162035238002e405950300203c6403900300100e007614101da44c002c5803001c0c03100fa40c148801c0002c1040500103001c000240800d582411000b51911418800e40000c41e5502c1c082e00d006041c44000307840c03071501600c00d8030704151a00b80403502d2688030b00d0080b205c006502205166a1926102d00890074846503420060107081c1107810b0f070780780e000c030400522406000ca038036401c01c05d20305040c07805808090940341ca00b400102c405030080d040a48841000c0c40c00e020701040b00c5408034400c51041400904c241042c500d100e00540044c9005002c1c0340d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 343842535 1250 343841285 343841291
    0x61c0c0504050d1505060a0b0d1509020a03091407050102060712140a090317130305090a260105130b0105061c050115141204140a20040506030a030207060e04 69
    0x10b4a40e9852414040440c0a00c070404446580d001c0c0003c204c4d10010700d07030b42c40783c035900a05103c0454003109403401030300a40800a64000c10a03a5041c0c0c0341c1d401da02403105a03000060848072158160005d41400d4070403441a0803009064140686581d0a0700603a8010b030701c1400020080781c8a80303040392102c1828203002881c004109200c82030104200c07441601c0948404110b404c055020002c03c4c140d02c908421003501d4102039503448224801e11001400f00100410700400c00d84d030b42198440208040d03d0081c1c4041e402c040345500e901c0300106c003411654070346400601124411104032070119405441060180c0c01e1904001e0a0b401c2003101561848011030b2214559610344546400780200050440001d04411001810201d0451045922000501252801c0030388030b00900e400075802400040003e040c00015031501101c000701810705441e200f20702c001c0c00300721000c00c40ca905046c2c030300303020540c4c50000340750740d03141018002030040e409041e08210103407103081d0f41e240640d4000c0001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 343843785 1250 343842535 343842539
    0xe0f24090112030807090b0d09080c010222120506010909140d0801080115050609010e2d090112020d02040c0c020d060e071e030f03051b010f0b061c0c0504 68
    0x4036400340d60980020308092860000c0300305150b0061001d0340c2c170041078980545000d0500c0001422405070b0305c140b00c04241c42e580040108520117003038865401d01c0300000c5448849808074958402d13414a42d01d0000110341c0f0010501690300c0d26a010000d0300403004140d140d10703001245c001005401d2084c0c03001c0943c1076420390003d40c2801010007008080e6101401c1e541001107035403c54000300a6800fa104442070200860307100e090a4030034440c004d0070b1400c0880ea1650104030010b641612481d41d01105c0280c07001411144c1212a100d800181d40f00e004a80e240c0000380090111100082d6000229001c00b44c0145411781018543c0d0913589051403008440d0381c0400e09014032000215012625110440380740007081103142d004020101c40c0c1020b41031b2525480100701000c0c040600030350140c405410034580140212a41c42d08c042c0d020300e074860244200e190080c4070104402441134100312a4040700d145c09426115145413064408000c0350700c2c075010b180140211405841840818400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 343845035 1250 343843785 343843789
    0x17040506030403030605040e01020a081f08030c01060810090203030315120d110d03050c0d0507140f0d0e0102040f05060c0f0609100b010c0305040b0a0c120302130e0f24 74
    0x745002d14440d85010031200e0916080009403503105200d200c06a00c140300000c0495031088820790401d1210083c1c150150f90701d40007040d091100c2d00035940c503200002d402d000c503003415070101c402c5a182906490078042420003240548402c45400395042d40300f40041110050f5200541d0400040244030741340900402075010b0401e020f003001400409e800c450003503403d0000b07010800100c2ca040c9800c0060385401001c08210740114000184900c0d9100005917400b400755040050a0001054440d114800c511b00d81c802503100141c0540c005081006442001d0414001d5400751900401c10060180c101810b000d01500401740300c0005110380b84842c10218024800240111f4000340035101141c1c030344140c00140d980c0181c2080c1040200c420341000300c0d84c42401c5d101990304030301440b9070f10802690100d5100411030f80180002554003070303021400f40c16900030541025a0241c0c0b420450707803803000c040400400c480ca201948002e000045c0460352042121600017501210055282c0700040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 343846285 1250 343845035 343845037
    0x17121b1612030306170703080c0106050315040212010605030c040e0705060d0e0d0813060e160b1305040504020a05060c03040911040504050609090d080601170a0c0f0c0305030417040506 81
    0x8003500d41805820481000d0542c98081d10700500040a905d406119164044540c3c818a51002412000f008200041080700a42021000381401006c40c0c0e46c5c1600e1502510f202081035504a10406400e500c0d0720150708107000340000c0701c0d07005001d42100d0084200780800740c11090308904441c0241e84c004205079507544003419210381603480005c1c1c082d441d110003501c2e140740c40a600f014807100e0307810001c000c1c008041100c02c855012201040304200c1c1f5410b44e140c9070300c18440c46006d202c0840085402200007029012156404c08080e12841c0d5070030900084400640d030282d04150a550240180c0c104030000b84041da41c07900c200c074036141d07076a5001008c540d000343c0d10b01c1c182c00002504000d1440d0500803990401e03400c807182010380c20b00b100130599071683e05201d4010301010074001001c0d81c2c043ca0703001c10015896004041c0c14503060740ca904c014480d06000d1004592039900719030b0154490044010407641c151141c600c2e43d144d1b510745e02d0007091a4000186210710070480801c0917183c8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 343847535 1250 343846285 343846289
    0x1404050906070c1101111507141305061303140c092d1b03100603060e0c03130c18051e0c03040b060f0d2006030603030406080603030d1517121b16 64
    0x80e811050902303024400030300420301c4000d02c00640d00180001c40b408180503d00004940702110b840c1da40da80919860540c10002d0f90002c0c020070414000304914140c00324a0101079101201c4a0200350fa80409022109504030030039003001ca0f04038452032446102246440e000303840d0510010002c640d2183c4007a1a500440700141c40c00c12000d020044d00350140181c1c80940801c51501255140c1070741000f1081c0001050400b18400904008040c030159072400c4020703001c4909803c045251055031503003c0c0c103051320000854940072200203000d0070709100b4540100c541d00c2080f80b954945441e82c0130a10030207000c07180e0007644c9144d06a401c2d699104d0070601180314001005d000d40a002290040d107120306001400380200b001008102d0f0307008001c41d401e498090500b440543c40f40c0c404030b4618001c0781140b1005d0b0389407446100d140103c9441311000c44940c1e20f0024011010748241a0720f070301000c01c44951844c0180b200c2d03440705040400e594004295501101c902c40c0000f41d0420306820b0035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 343848785 1250 343847535 343847563
    0x7020604080708030408100209060a030207020a0504050106200a0b071101060b12071b120c03020a06181205070c17030d050a0c020f07030206070b1b03011404050906070c110111 77
    0x404121b000000e01010301810101c2004504101e44100031542d2440740341036043c10141d0001c0c440003195640e10018001d45400780c402c0041e580c5442c0040d28007008180300e40d0118041ca401080009000904a8101c50b8080d00303480c41501d80f07000030398004403c050f40c0c1c0c2080d5260354021807000041c001a0181c11718400c29292039081841001e000c0210904e10001860a40f8484901103401d000d199000680c940c030301041c2c5424282001c07410243d40802c000c044606103070550400403403241601e41041d002c0d2809142000e10700206940f51305c20b03504000c1081610b5881041252000f01d0010309103003d58091300d140c851a20b41c040d0440b982140c40703040361075481e100c4c1c01010741d0401040442c03000e40c900604025003940c001440074043c5070310040c09417904100103907440c441115215403007030700d12203a0b075240c0d40c444083c1001a0001c000c2107002d0b0349880b0024140210000340240a10005d80341d40d0178104183c2c480a40c01d0344800c2c61f003810b001d07942540600480080100d60442644 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 343850035 1250 343848785 343848787
    0x9020d0902010306210b33030c100c0f0602040e041506080a0807121419020105070c020f010c02011e031e2703020a060c0e0405011e05060702060408070803 68
    0x16200150072180c1325080f11920340d501c2c04188000c0b056800c000180b494118000c01c02641e05c42e41d80382180d141d8503020b894450088460904201c035440b43c001c42a00301241650008072042080c00700e694607118a074800613500c444200b0105540c0d0504500050041d40050315041c0c0365180104922000d8a0403582d103810048140310743e421900c030b2440545200c102a041d0500c00d9200c41c040b900510b00003800d642e084050301e20165001361903580602903820031791502c40710003072040a510b00341d0200e25005075003010300190600d48110485203000b0390080655912a11301c0c00112340c1040b8650049061000d1030104042800c607250004403039a007180e60104070301c90159035080503021100034010f0300904010801804500800742000902c1c2c0204102d030924000e030a08a18089088034007420b40c0c1d1900708134030302440e80030811040c01e1600365003e02069036114203030180c07950483c1050318405640350b000d00032868454001e05219000500071418035844000940c00c2c01d80d0395101141e070f41c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 343851285 1250 343850035 343850051
    0x32d0705071101020f49030b040506011215030605090c04110a0f11100906021902070f0519090f0606120506011d01030f1401140a0302030d110709020d 66
    0x364180102c0801007003840600100c0700d515040d0750751000001d080c2c0c2802c40181c1004140030b0901065450015800d00c91402083c0c8545604004000074540100000342803040c035409900b407034010b45002e40d00c10f940b60040540c111462000603c0c01109080c24415150340c0040440c40c68003501d400340141c1c0003d40a440084070402007221000d8210390740c2400300340310750106541c102109202402003800c008002d500b104c8102c504195008441222140c40c049a140a000c104e90183c0003800440c02480035070101d0003003c0c1d80e500b0b9284944160255004014082e80c00e060707090380c40600c407108850b100d60b602c454003402600d1608e41c000c0748540d0748040402c521507000b00071120300200d00a0811040c00d01d100020664582205900b1607045003900b4145145d220790310001000503051070800407900000d8030303102622020b100d17a40010b1f01d8420540701c1d51824400d05411070364002c0042124015810301070b641042e40100c0c0c211039006500001401c0c0042d07000a0000605624001034404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 343852535 1250 343851285 343851293
    0xf030e0d020c0310140105060901091a04150c12051614150c040e01050f060706020307020d020c010f0219080c0703050a0b1509040b0411030f16061103032d070507 71
    0x40c0c4c110040050604240c1007451038000400702d82c0c1918010b03220541e03101a46801aa06120a607110700c0d1603043d42e012106501c440c500280040e1032002070000c650224200c000c84100f54074040240000000c1c603e9000d44600441c02400c541d40790104e24484030205494940803402d41e251204a141c21407200071131aa00d105078265030040d4040c003028280307814290354900005050040c0303030103500d4000da4414280c2d9140196021560b01460641d44d84c40d10041c000e440e1008401e81c0c401604c03a402010141d50302440e0304890084040c0c0c001c100101d19607007503e4912143c10006d80f5212800c00c0387c2a121035040c0080b03006503000e40010602c5a006140100d0103800007003041000200361110311321161b4845030465000b54005100b010640c4072400e05480d02c11406000981c54403c64141c841040d20100d1890900341a20b510b038451603545400907294103803824055100c5400400000b58140070060009441d100d141034411605401c6030044081107009450070008030380c02080c140f00308 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 343853785 1250 343852535 343852543
    0x30a08090705010c120f03090b13140c010c0b0c0408031308060a0b090a090c08060118050c03010602190516060306080f07050f1e0913031d0607030f030e0d020c03 71
    0x4240c00c4c0f130b1042d00b01415440f0080301121440ca03400420528480c5e9045152181c0c000c010f07040d030420b03000c402608100c007095521403c4004210788843e00860180d16038900440c000f0300014068440102c0441599260340c02c454005208000c0040c00380070103c0c00e80c40405c0a040044100c2881c01c403c1c500b04100180740c04002084a00380030f01703200c102d40003500c5040b0900d800015000020038a52814130300148000c1039031700145d0040c402c6400000d821008000e045a080181c1c40c003c0015895410b01c2c080703144001d000d640d000d0380c40b604403068006004003a003181540264107480030720169190385140b6100f1035011600180c0c4808041c05001020711000d00070700400c000a241c401d150501103964003603e414918807800c1e07200150041100401c10f20300030510001c0641056103002c04041540001031981640010341c04041d00000b440e0b039120440002100401041c00c01281e9034044400500302400c000c101600c2c0c182033810040c003003000c081e0b201c070301c0d070060305500708250141854 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 343855035 1250 343853785 343853789
    0x150c03090601080a0f030f0e040f05100f1a03071205040303051b0a0f050309030c0f24190c031409070e101a070302160603020c0c04061d090c03030a080907 68
    0x3281d0040c00f02c131000103130840c0398000d01c2541814030104ea8490001d090b281071000d40b98041c0c20504000b400d006082c20707030780312a1080d0804018030f02030070b031240c012282d2584680a0030043c105c440c1d505841001d031030006940d000d0205d280a0000040040c0500d041c0c900c207650132004203888505010000c0c10102000c02d00759a5083c80c01e082108995005092040188409d0103220000012440364142401221004a404000c8a520820061800d540ea0840703407280880350b91480100340fa20910114414041c1c0d00e4001c1d030f440029034010071400140500c010042c18543e544410010710035081030301030321801f07000780030300f40070382c0340c0401d43e20060300042a031380007111044000d0040400c0d2001803600300781100e13510f070b848210302c0c6030591400801000e0000f400e20303180340015045500d9001002d00325442415a981a2a41c2c028030003650858041d1f401003402c25010f41e602421458916540005894200c441410050700880c6c210383c003c1c128080051080310401401d42020802040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 343856285 1250 343855035 343855049
    0x4050c1c050121080a0c05030d11030603070b07030c06180f050a050d020d090e0a022b0e19110d08030a020901110c010507020d0809031e300a02150c03090601 69
    0x1d0743c0c0000d0780c1d00c0c05688182c4900506202900500509101d81002a9071020040c1c40c1c0401c4a45c08402030800f89810854400f8400c1c494200007289450b524070a6a45156154881c5110480310b80d4450014248601040384e0030803080c480600450b491280601c07100e4003503c054481d0f140c0700e08280342800c00200d2103a00790743c4502d105200080d4050100c07412221796002c030385100d8a8806c42c41c0003904c02d1190824403005541003044402d98114105c3d0310ba500100010080c45601030900341d243d0b0240591034210740a82460900800c00344804403c400c1c10080005100420b90b9440034481d4100781c0768140308a030b0100342c6018658100c0e0118038005681d2000702074109502000034240c1c03241c428000c0c0100b00c1d80300c0480070812280c0a0b282c60070002010707250a0f500302c0c0c24003c01d501d1003501012091107000a142c10880020900003c448520b0000040c80060381c44c68800590144250400710b03c541010ba0360542e05c801c0c0e016016602d40d45002e33649052402c14240341200c1a08800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 343857535 1250 343856285 343856339
    0x1b0d051206152505010912020601090608070b030718030c0f0e160302210403080712020c060105190906120b061f0818061608010f0305070504050c1c0501 67
    0x5a42c4140c1e00c10b49100a02d40a02c400000b42c002000c0701d1103800090006201e50b003030155090800002000c0750004040603401c81e41c0b5a80d880030384c00c05942d40ca10031041c494000081c107110203188000116400400e5042212060500314044c0c03210320040c0e4020340d0000c1020206200b6100050720140091002600e04843c1e4104541d12540380805001c8820a041d40050500320014010800c541901242c1034a16401d240a042c041d103860b00858031500020b1041c1c04900080403180f081e00c8580425400034a10381e8204028007030300030300c40e0f03481c8440c1615417000003580311914013400b4040e00981c540c4802c50416417030480540b44002e06000d20a10300d800110300503024914604401403000e107800c000c961901d20402c0121002501e5000f00c60240030204080e4564101d03541031900c1c0340b6940c4016507a40c520300094691040e0200812541107680200084c2c5417a820a03500807840304ca02c145041c00409c3c450811000c0484902131494030340004212500c00c0c2e0b846002022101c01201d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 343858785 1250 343857535 343857559
    0x2060f180f010c030219170f0309010c0f27360209010c060b06070b07030c091a0405040509011419110901050304060903030e0102161118010b1b0d051206 67
    0x41d44402214103a0760072001d001030718409014801d80890307170011001d2000c9580304503230884030b1201d07442100c00009940c00e003c0012912489a400c000b1080610303500c0e141283d0340400c100d0030f080d4000f4668403480f111400080b03900020811000d1026480003402c4c030242d5200409051b1801c90401483c882e0741c418484003115980054217103a41550140001422141600c0010f00c0d5002d005400fa0280c4981c004002c0c1c0fa540544c000111a1400c0d1200c01049954550040030309903400802449844203000c00c1040f4101a04041e030000c1d0b41d0400844c0248008010043d91141181c00390a4000350720000c1600907070350b2155840e81c1a80c03079480d41c6401c4100c00060030500c0040e000400150b41ea010b104241440b0b0f50140f0a811181d200a565401034a01c40380341943c40800b082d9400d440001101c8041d00c0d0010000c02c039052964030b41605c40e171800341c074082507400032607000280038001d11404043c1c0c68140510a9480c0642c2c0320300c2e0302c8128203c0005020500204001c2c0583e036035003d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 343860035 1250 343858785 343858787
    0x1d0c0612060909030d02030103080306010e0906100e031903020a0209010f060f110a0209070816020f0a0303022803021819090e150a0204060f0f0507030c02060f180f010c03 75
    0x100c20707440201550090741a4451a001610b5403003110038060b590761000c40007200308140500218080d600036a501a447c1e44048100101854141d401e6940300072a5042c000055020b07112125001000070292a01141312801540d6026102123003140141c02070303d0100c0031450b00c81c0c2886e014007401d4000104030f500744200901120031030990b65050044030907084207102030400000544981c0070780b110600707080501c00644400b00503103054522820000382384060510000341c04114851007402410507051945050700290710241d000c41c00c080750010180c51010002c03283c4c0b0203d01e6a40e60061359080a248643c04041b0b44100e81b82c40b94400601c0915000c0b0001100026544694000600e02003501c140b10314001c22440e00815540ba58000c1010180313480e0702400859606440701042200a907804803810f2a49034041000303e1014807496002c0ba2250017618142440900a01e14008928060380d00f20342050702c0211580495901407441c600f001441002d03912006c0c00c02e5021084a41d034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 343861285 1250 343860035 343860067
    0x3230105130e010c030615020c030a06180819080a0902060a2708030409060501020d0c110d02060c06090d140d050912070b01152c040b041d0c06 63
    0x400c151080c50380456600c1c080c003255104900d0204070000801140000200290140c00369104105000031003442001c0c04034000304002140880081c0905165241340da2160020300d08007901c403400480c865110000501c407070340102076121000c030111880406011008040090081c2040e02440c140720303a10300144c540360291003c1030800c2c01c1c400528094071a0b10304401d03a441c9014401c00040800020f9842e001100038029504450300070321401ea299001a40d981c41c0e040206400a940301d0a40380100e005400c411540c0340005242590084082d00054081e8101e8400418581c000405000007400108000200341d541810a040e0042e489002d00c3d2260058031948045c254070b8400081c1100c40620a1109103d48140350703c1d2101058141903007410001d000700410300c1c00e1103da0b04141ca0092130342e01600c0c2c488820701404000f0741c051412440c2e00c030700040c5820a49942401130325590718000c040314156144c0040046d100c070000d0507032800348070b40c80b56402810f04008091102c00020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 343862535 1250 343861285 343861289
    0x10c09031529150c031e0f0a050316020c01020606060a0201060e04030c14071a0a2001020306030c060310090509070b0f040905150904060c1206090c032301 68
    0x1603803441d580c00d05401800c05420300318490405401d01e07641d0300c1101040c0414031022668242d8002c10850a01544620300303105541101901303500c20f00085400d000e0310300c0c000d0992203403004001c0c1025801c0e400646c3d90303000030070044085000801000081600c2840900d0f21a0540c402811094100344c0042e4403800701900607400b514000541301401e500035080f20004042070310401400345020b08000389855510601264168100004075050840004880054815515002c1190003001400240650142d40200184052170745600607000680e200a04604401d10015940f0300d080f504140c00c00300c91b0b1400341c1c41a1014014010203900c601c6030501503685150002550380c17602c0002518254159200b400422400a81c120b51601c001c2d000e04115481c1101c2801942c483d000c01000800050021540001d491000100032851035040f07a00e00116070b0500034aa22031034000a4207588030340e00b141120f0782c0c460782c120402a40c548220804a000008040c144044010015050102c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 343863785 1250 343862535 343862543
    0x8063102090316120302011d07050103050a0b060c010603060f02041206020a0903051f05010f080d1d031b0f01080108061513060801050702060703060b0f030a020c0303091509010c0903 80
    0x1050380c0780c240c0c500300544080c0d00070700b8583c0504a40d4a0015102c1c0c42c08455044005500b0f10240400c0c498440c0c030b5000c80c1e0f1f03c040020f420351908041c011001040010710390f88000780c0314100c045044d204d841c0140248052903001141460035400d00c1c03000d50741e1900c0000e403400d1040004200c90302400c034600002c550304c12000350307032101543d604031491003c1e031b00040d006000760845c3e50f50001c0070031251302e102081c0480a01981e84d90350504008503085101e001c5c400e800580f84a40030601c28004c0daa9041914010100c2507c03031140841d00c0d000801000040541c1c0010780c41c200761504c1840e60000c580c0034030300b001881d0b0605041e00d45400c80079011441c41d0b6280741182600381d803807044920302700c6d0340c443d01000103c0c4e40d4040c8070b019040c1074070014098000d03e00030a030030600c40d001e41d0301030b6010254031030b00c0c1c0007681c548000c0321b5200a20101a040e800d01911000140034801180039110a01c01840015200551103040c544003034140000f03a071401017603120030340c0c07c600402c0c12030340c00c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 343865035 1250 343863785 343863787
    0x30507020a08060c0301031704031101110f0303010927020a23220c020c0603070e12071410030e06010b0706140103050618010902091302180708063102 66
    0x215201145008481e41c00448950042008005010744403c01450480e80036050410b40c00111a5024109220324040a0702010311203660b142154002c0c040e56074502803000440310702030280c2c690281150003c1e00401c1c1943e071280c81311800074400d0706643d2002101200d204e48865103d40c00285c0d281018400c1c050030030744500790400003c0040711a02d00c0c592014100544160711070403e5401c07030340e0400c003a81c03a0314600000e6a500d2440041c0c80244500b020340954035507100d80f181036441e200350424181d440841800d1403403194000340101c80c02010034001c0098005501e138200030085010401500030145082800c0900c10000601d040c1103c0002048a55490303050601801604108005031417100c00200000100000054428451401a100f1005c5041001c01796801e031100041c029500c1909980404e103868041c01038281c400d44020408120307021034080f41840c0e902c048440c40003044003082001820304080740c80d445110540312509032003520140c40900351407035a028040680d58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 343866285 1250 343865035 343865047
    0x20d0e090412120603080729040b0a0f020c06011a1e0310050d050c090a0218102a1a0108060a0c111002030105120d020709020f070c030f03021203060303070305 70
    0xc000c0e1840d040f0501d10300360a0100a84908107032855504c440c008841d81c44840901c10b130039000b82d4440c050103011080703c0701e2464485403205c940360040904500e403101da0724800210142510f05c0240382020207400070b00300c0396150801c82c40000a80368015a030180701001060008419180500c252107101c00c1c07516100e0711200014003070300583d5041242c219818070304087c14082c00040800700180c088481e59501c0e0356240c02c907020790064420f9000310a500c1d1056544a00c1c001081600350451860100325106c20740304101401c4800da41c1641c2c141c0550f01e803140501c0710b240040000c420701110212107651400c0320315a502c03000140007884071552201ca040a9070700c1100d01400b00300d554400c81d0010511011204029030081c4a103a1084500541c000b0702c072040403a00020501c03581d0003908495207045036403006540540c101d1191484100403030400140e4a01e0914080c40c01246440c000c9185454080c0c6440707803076020400045001e1040020325900013084425103980f40c68465110b203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 343867535 1250 343866285 343866287
    0x70f0f020114040602120a020408070603051f0b1b0303220f0b07020c0301060f03080703080c0d060e070206060306090c220c020c031c020307020f0d060906050601020d0e090412 77
    0x44211a0325284401e80b0703005010a100035500030380390a11103403c50341e01984584203071404034410b5105a01041d001044200105402940304c941d10070b14041a1440c0b940c155104101016409d800c0700e8468640403660359003d50220300d4400d00e40c59400010340c61414043c0d8000c40d800d500d59550300d1804129181c2100300500c0c0902c00c400c02e40d1000304030410741030400002c2d40360250713404554025841c0a400040284158043c04102c0e6080b8000603c2c014581d1070449a000c0010040d8200c40d00404c890981da821511030728004020146480015042c505e400074107007000a00460702c01d078000000c1c0040d40074003041003000c03150111620301c02d40d00c10000610303100f0340200d81071040a10717241482068070f801050b42d10899070100c040e19214070319015a0010404507004102c01079005009590040c144424070030b03c01c2100406101d0b1400c031555030f031000c5d80c0c140001103820507218014000507503010400340a010102d401c1c880708606d64007010402c0c083c001130000d4142c640c0c00c0070303603100d007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 343868785 1250 343867535 343867541
    0x71d0609011701411303030c050c030705030301150e03061501020109021206040311030a1b0c090f090b060a0b0f0a0504120f021f1d280302040605030303070f0f0201 72
    0x143d0400041400b031445912491001400c44c0718012003021007007200c0780b694004019034107100702c940f060404007000264070114000d0082c42038070390500c00d0410400c2400074080000e003080c148103c0007107a0301d6040041c46030b4060001c1c2c032841d0901940448000041d038000c40c5c00b95018405511040340d41c2c4240700100e025101c00c030303406504100224000301540c4404141a03108074001e0300e51044110002c445250f50b4030809600c0c4000680340c0d82403900c0344000f401e0100c581400f03090720101450f140c00c4510211099079103880c5149540b488107a0402c0340020764264422000c6848105040c80c1c0208031510b48152660f132646200001628800c0ba400782054070040e0134101038401a13100146010030880003010700a0748102e400d9800703990440c0301d0803c1d4041d0760029945062042c40c09000c09401120a100d1140d4000703104013541e000071403109040d905e0a2a006a607018141c07071801848112401e40c0c04c09030081e0410820084101e0b00b0042a010b0f4003030a00c2c2074142070780d03030b114200c1c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 343870035 1250 343868785 343868801
    0x90f0f060d0204030b090708030a0c0618080a050901391e0b0406180c03082b0b1206040b070c1506170c010e1c1103010e071d0609011701 60
    0x40302e00c041000300500100d00402482280c140049410080d100c1059664030701a0003130030070001c0c1032080c0c10340c00104940c100034401001e01d0504015845180e88020641d0425940f142c00950086a00328480da448404c0300c45901c10880c412104420358282541140710310002011300081001040041103203000302e00900c8000c400040040403070f90b140140ca04002500d080d1403441c10b04000c2c28119100c103684040c1940d000e441c0c8440d207440c0d035680c51007a80000340b1030034083c107140d2590010020480c001207200c0c051940f001402d00d440e0010001c00ba14003001c100240da001f4820400081c0281210a400400d50304094180810520300540e55070f030b030240c062600c241410400a81d10395202011842682c421040e554190031881c01103031250026401035a02c03240c10f02d050780011214101190b860790213400303500100c010720000300c3d003501c0c43c03c00544581d9000d020208802c43e0314421252569032881e0101078941040c6001505141e030600a620900d4050b03030041d84421003d51180354 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 343871285 1250 343870035 343870057
    0x1c020715020c010f1107060e0609031506010f08010312050705031605011401080604030f050f070212060a050906160311040504090606170a1502180307090204090b06090f0f06 76
    0x20210354400025150031000c400180800e45030340d050000703540120806900c81c80709500501546213004000c648501c40200c1040d00700208100c0006030ba20203015034540c080c3c4014010010b4100700c0001021541e403085c0c1e420030804030700014400580b10410a080a194070315250741c40d18a40d00b007007419440740c1c00d00e45043c912000d0070300c0208181074005032658220801410704580c0d070380784c040761a44411500100004c41e02c480d00300015006401801913591403038105428543c1c031b275000c144880c2c030340300a19205034410010030a04030302a004003684440c40c10302400c8141031410b036448544445d014264185902ea50700c090113407851400307660091038010418408a4854107054004012602510b9500d07610701103581c0006000080c0004901d03404620800d0410b0040390b148000e4201c451724006420441040d01056941000304101401c0045401a6603520b0290182e0880c1c0710481c10a000700300510031041070703641719000262004019941d450191046a000800d681f150303a81402c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 343872535 1250 343871285 343871309
    0x120307060b011707030c021212060910050d0f05010f0b0306162a11060405130b04020c011b0801050a151101060513060609350c06030a090201030c09081c0207 69
    0x11504c0c0d50305401581070968641c09550141c1542004043c4c00d22071804446e140304128000f18040d07003041d2030380030b501c11b2615141044035511000010030070001440c2c10fa03201c0060031800305c14404284030300803044880c5e0004001218407800880c1d12100001d06800d044065201d00a80c854003940409030091340000784001200f010b0a0300104080020b00c05848a00e02c80440070020b0800344205d80640f6401002118201c1e2120030600180101035111500b0503000d00002c00152401d001d0b0000071144940100c05030300c1072100040103050140d0105200d040b2038003080042c120880401c49900c8902e19102038003103080040e15000d012540e0147c0c1c0c000c00c01c0c003403c8407081600d40c0002c003a128140c0c1c9152545d40da0b211100201c00c0000030041181a01c401081301e2507082c500e10503004c2c0c20000503070701d541100100240780ca40040f40c559511039110b680c440119070745441401143d1049041a060040c104240c45503140c400c0e40826180003003040302c01042a000704640c1004240540e0b40e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 343873785 1250 343872535 343872541
    0xf0605070908061b0412020607170715090b0f06030a0f03020c01111b01050a090e0411040b06360607050106090e1912030b06030906090705120307060b0117 68
    0x400c00c1e80c2621940195000303050209007001c0500c1c802100b481c41410741241480d080c0510350311620344d0240220303440b803001c116040c00500045200d02140764990040c60b11141c1c40d080c03860314075800d030801051ba1440c0980d61400681c0d43c0401540100d80301d44403080f0383d580c5d400031030315042c50707480f0281c61081c001d00d0f1101003550009007020b000c0c4003a03843c400c141c00c204201c1940c2c2ca90291115881b880c0b140c242031881c1d4403c0c4040c10720b81d101482d20400459031005c1c03200009405940640b6465030040c0d580480307040902600001c4401a0780c1c81d0728090317181e038805074404021010324080d07600101c002d46484240d1103180000a00c01040255074078030b10314080e070007413078140300f805245800e007035080c01a00340c045003181005048072408604c940741a62450208030038001a00d080c035540320f0b02d00c0c070540c641130081c5100780c10200c020303c0740d0f09017007420b07500d891016801548144000c204c0c0403a4540044203540c1c4050340a400480c1d11054075006a42e1150007580e0100011410020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 343875035 1250 343873785 343873787
    0x7170a030b0d24060b0313050d090501080c030601090b1306090608070e0111070b0d050a15052103160f020102010b06090112020d0e06090a0c0806010b03010e06010309051b13020301140603040f060507 87
    0x5c03401f0340d5880354040318201c0c10230080594844140e440380d203003c50f959900107101990b0720001154801014985030031202c0d12a0201420f9411480e41c18298421081d020701c615600100e90383c0140545040c01201c91800c00c4000b0065502d00c1c00d524100038943c0d104d041c0e10301080200e44040d00c0c500245540320286500200000e010440c0d04903660f03410403ea22154002480e030030002c0c1d50001e0072a05405c0001c2c60100030902401800d04210710003001110740400c0b0740c0b20108145c0d4480d945030400343d03060f400024251000302e26902d1140504201444403a80c00c0b00d1045c40e640340c540030160302c80c40c60010345801420503205c001e0060068400704113407008041000326045210300c0c064440f203901c85000a503109002d001c0e004200000b000107020760415a00c0c401d60181d814034001c0ac50003a035517100d60600060081820000228000c100d40914010302d001c02001c849010440c155031503c801643c030280340c2021240241c0d0008042410300c0f0030301000c03920f4550010030901c103038141a44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 343876285 1250 343875035 343875061
    0x203030c0a0303060b070206031b0403120e0126070c0303020c03040308040e0a0603050c040f0b0d050127050c040c020a0b0f0403030501080318040c0507170a030b0d24060b03 76
    0x1c04400080c54204080390001400054800264015129904554a0b00152000034805042c0c148010f030741808000002103032601c0d254480550790b81c903031b050320043d43c001400e04035a030364510748486506400421003800c00c2ca1311603809422031422243d0421241400d800901c207244007205680400a004014040d1700350080c4200c03280e0103001180ba903104503040013101c0860000034255000b200b41101140340603080f440900b0442040000c1100d150000a100f21135150411101ca9440b08101200c0c00e0000034481c41001c126000030310000300c4c1d541c4031a1140705100d08244165a2080303507c1400d482048580f020302d900601000d802d0514111400406004071030440c002401c03c400801c0d0108040107a840b2400c074624070090f800700c4503003000060000ea0454004020f81400300d8004a02c10000001c00e500241d40400c2d5903070846200103081e0750142c01414000c8400c6540c0c080000c0e0100c0310700c0015000703144e505000c4031640e22a5009001d10394854420307203a0110500401d00303040c0d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 343877535 1250 343876285 343876303
    0x2090609070c2f01020a0503090d150911031b011b1109040f020405070e011e120c090305070f0f0303030209010201150e0f060f06070201030f020d05010303091a070b220203030c 77
    0x83e0070154071054080049a443d03403070328001405c0d41c00034402030603103043c8014164503035442015441c001030312110346a0101c0351380c4c04043d40c40d9503a628100c040b42c11305000500301440d000d04a1181a0420000030381141c4022031002822103c4180d00001d01084070040300003001c0081c0126218141818480720310310b43d11009030720a078030f8a4049986640142142d80c2e0090040c3c480c4144070341810020356121400d44514024002d0b078640b1805105024440c4132800c80040d260200302e031b800c5080191071f00d4500d1b04034140f028001001400412180c0b10500c044941c1454056030710901c2c540100d000d8915880f06405164030740001080b0210301d034420604c14a040030b0402c40560300e4200700681c483d00350b80e00d180c00c20410000040903510a0300012407960407610054640100c80d0b0f00e41c0d0840d80e09900a40025420342000e20804001d54a900f42a9001d0803a0506205454507058000c54002c0c00360180b101d5803000d256000c0c0000180d21461030f4004081e00c1e118400009550b0311114a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 343878785 1250 343877535 343877603
    0x1503100801050112030c05071e080f073b0f0f06030120070606050d06150e060a0e04240c020c01050c0c040203130b0c07020108060d02090609070c 64
    0x51140031550120510640d4101c541e04407400800200d1911300b582c100c4444a4191403d0150403030104501043c4a0300e0900c40526810050b4100e14140c0000d0030700d510030000400d00d800c908010040301c9032021f401d003c0c20700c13028410354034140c00d041940703e071301c90001e684d41080446104002c2d41c08504030b0003900c202c1c056120f0300c0755582e40204150803a400c807540c0c0c0f1640c0d0b080c0320000300c000c15184040e01c0840d00c00c41d000500c0e19103a01c00101c21414601040302d10589070b803038000c160780070700381c0b0000180f031480c00468650030940006080e407a214041e400841e8003020004080c07200180b0b0000b102510716412080030300c4002070460240c083c0540c140003500c80c044c03440d0072030352003002107503660343c0100060020250440c040001a500207040c002ca003001c0214802c000c00c03070601a0a015441100d140350b9219500e20005d00301c04c4008008070700c240840702c10200542c070b130300c50480d80c08541220100c40302c0e614a101540d21020504002c1c1c0035018031001c42101408141c45c01c0690840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 343880035 1250 343878785 343878811
    0x9020906130902120a0912080921180a0e040f06110a0e010906170f2e06080604061206271a10030c09020a05040509090102120a05010501051c0b1503 65
    0x8070885c40e025030381c4005000300303602c04428840c02000c0c49401010b80045d960802c0c1c8400305881c01010082101c40506055900300004106c41204017641e500c118005056588178201450941004184070300240702420361a06100c42070200442903001840990444401e6610386041c00c80040200650104040c0402c41903103010070110700038090601b001ca510180b810166542d0841d0954620010f01644402159051001403048044052401201c8145038a0120602e0000c1c002c0540101404d010b0107540352201c14003190031540ca18140032600850042004160182207400d103d546036054400398210040c19003c00c070704c84401c0020300b14116400115510396a00c0300c0030307220062100400185015000300303ca201c01c1c2e00500322441250400f1400e10b542e074008a520031900f07c62048031654006139210300d410343d4503001170708030990031400c100c150304040003e000ca2040d0040e0440c0b45840341d1500d5003407001a00440301c1c0420290100d109407503501024889504103980516034812 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 343881285 1250 343880035 343880041
    0x120c150e0106051e042f030702070509130609052b031a03212b1a0f01031805010903081e0f010302130906111917010902090613090212 59
    0x15200030f025501a104102281c2c84552800801000f0301c521b07441d01d00ea90300350000d01800c01451407200009840c03c0c46400d0707900d05e020140242001703040d8000503c9100400b041c800321168070780c0500e41065000b4000121b080c11420214509280552000c83e0414105070151040c1880c4c3c0c0700e004a14001d032000d00650384017115450300182c0000c40240c15900464103440a481d044910f04d52222a0800880c50300e00c40038416440d01c008001250500e03940c401d14002e02124901c00c03010714402c0c502c4607844510040d000510400990010281059118100d4480544e0450300c00361500341d0100007000040b80501e409800c0781781c200d07a401240825260704548403102101c01078841c1d82c1e50045007445d40c0c250340c00c1054070a007040a0307a40c042e5990702e00d140056943e1245170b20b05000c90302c6c0d0701e440d03914001287d003021031000d428030704001a2000c015002c18104240c207040d50341d05000584c40b41c0b07264002c103100e40286501214107801045c2c000550b80f136030b9401030004030310401a1032210b903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 343882535 1250 343881285 343881289
    0x10b0607021e120d02060403080903121f05120d0206010b030907090c0c020306130c090c090b0903120703030f11071208101706091e0604120c150e010605 67
    0x10140040294000c0ca00b8080c0d0490011001e4400a00a900400c058500c02444492a00c0d2482e0707550f03503401507403141d020310003416004184281e01c0301b0400021840c007040034529659030140544010006200d11040f600100411600040034240150280010561401c40a9611840d400241001d03002d6240082056803025085070711039580c0310005c02c5810303d8100880000c0900307000c03030001c008800300303080010fa40610445000e40b260407141d603152001418050f00d809a2036000b003091500d060310000384160481d501000b00c42d616003c458841d02e6070004607082550031500b4820402c00050702604040e0943e000003280501718608204030414070400d00c065124101000d848500c0150f907294801d40f1426613a94000c0614072084403090343d40e284c40002003d8544000c4003600813008121440c4801c00c04020050340c1c0011036401800d90452094503040080c0002e8140300c5501d05000f0b80e10702400004425642c0499025104068010180010003108050025950810a0000c1c181c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 343883785 1250 343882535 343882537
    0x603011b03090b100f031707060203010b1201090b0a05270408030f010602030a09092301080d020c030a02240c120c1905120705010605090103060c091205120c030d060f08010b06 77
    0x5150041004a40503040da11020207007d100108544414401c00080300001d02c14000b40d030003008910b5000d5100c90342070b81d00e00318207101604001510f503d07100c24801c165944003424000c4480642d00d804071404260011204005091150400342865005000070440703030701c3c021403048801c0102c11000341d0700d80c0340c226240d1242040c00400140320600502c05003005d58800c0040e0b04100103400c030007004100c22102c9845090f4802280c0380c101e200c8a921441e014000324120078001c03009803a07445455400070711a100e10b10385259100d400c068485000c00780d284200d460000e403550032200c00d0003200410801580c0060b145042c98002c2c00801030034000801007a0a0b020741c000b014103003820ba100c0f60008550000c01d410b8031a50340700e02b40080c2d1070b16000b8600740a1400303018042140501900c000e4844000c46e48024039445035003003690040390f0085203000f520840540469a03c02054081c24690300440541d40d58051400c00001008284214810f0884810800a101c00c5110004000721 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 343884892 1107 343883785 343883789
    0xb1309080408070515030a110f04030c03021314011a04030f050a02090f0114040515120a0213021e0a05070c030807021e010509090603011b03090b10 65
    0x182c818811480035200a42d140a401584180040054070000303060180e200d650b2400019400c20043c110b652040360805010b444580307a050000d0301805504c4101d104590708000761403c98254001d88081044540007000c0581c03170001c1d03000710010180d601b850710503000c01000c0000317203000001c400564013482c01000d00e4030551060099010780501600342c0303110324500401c031400c04555106031807002540c0206460f1140b4868100c003101c0f14540507030003212495000c03c1008006005100640226840641c0c031000e59a800e0403889041100c4660105a801100b0782407911402045020f03140c1c03030128074120b1035031180550801d040d0800c4402c648005010025417600c0b20700c072a5074a1035403e40480070700c40040041c2044c03203401d5145002c1c0d08075070700007502e9a80c294011810500c5003203010148045c0c00200a0003070030790140485092080a0115140d04030604500b42 = true := by decide +kernel

theorem cover : BRFrame.Cov 343705035 343884892 := by
  have h0 := BRFrame.cov_init 343705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 343705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 343705035 ≤ n) (h2 : n < 343884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
