-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:00:46.073466+00:00
-- url     : https://prove2.me/submissions/eaf0b6a9-23eb-4acb-9c67-652b558c0e71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 986151079 ≤ n < 986330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 986152329 1250 986151079 986151107
    0x140c090c030a0b0a080d1e082701050a0902030d0f0804020607050f07080a05060609061e0406050a03140d03090515040c09021207090b090a270203090303011a071101 72
    0x500303c410a00014a00b508550203180c5a80c01520b03407801403580a2800e000382c883c1c0000d40c500d41c0c40100400b9015a000420201c0c030035150340d1864410602d219401401c050440c4020041c0e428096242c1c0c01400843c1800d078080c1c0315a02d0308144152146a1340c052152040c0e552620320f40f510390810415601c00c01050f50a40b0460444100d180001d1040ea03004081c80b40042c80d0000a0385482824440000c0c41d01c0c0c45071400c802000b6071512031910018014010700c01031341c80020300d000010300600030354204076000385400c6c20100c200031454880901079108034049078102c02c048082107003074850a81d0018101d400c00400604900120141e4640052041c04101d0790252202581b8040781c10511599440c081c42d40140f210b503030f402c080c448019148007100700c3d280002c1720011a094048510552a01000040000703083c042a030340c600c114010b680c0d20542d96414014030003581ea40003030148030481403d241168400d400e130042101c0903c3d9100d4080e2804030010001550305904024131 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 986153579 1250 986152329 986152331
    0x90102040b04081509010911060703020f070f0302040b090103020120030d0c0c02011806140921060402090f060d06020f0c01090303060617100905100f0303020a140c090c030a 76
    0x4110700e4048405800500754010041801d9102c1500c1020804400b808004603640740c050f820f80414a107085006a84d6000e076405980c840a61030100c0c07510300c03001e504817220b014104020034042014420311003100d00807174062101440b40410805025420320009004c5034050303a088400007180305d4940d0182c025801aa0b041800103100d86040d650499280800203140d420900115a00f0048014201074040038240e8401e0603e0405031420403061210349030711501042c29503081c3e54041c44955850030824194568540240c039207991940260340c103d02c20421000015501d1092902c050303c0bc00c0d005281c0c002422041d101c1c44000e5025000300394a0709801c0080d02d44251090207242c020a10039500002d025141080041100c001c900c00702c94460401004d001172240074002c403000340c603d5030f030f000a541e48600000300c1c20301c03131240d00102c3c001d040080d00006264000c641c800c0114051101c1001c00203039060543d4540c0d0b0300c102c0c42640028241d01080c2d10046c1040650f030700c0a05008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 986154829 1250 986153579 986153587
    0x315240909020d0f0605010914090d120e1204060e01210c0903020d051e1b28090e0d030e03070605041e060605030d020705030a0b0403030917070309080c0303040e090102 74
    0x484e611904201502520300546440040100f80c0007445142e40c603a10110403024541003c3c08281d8a07020148007070f004200040c03469030000d1456502c0351044c42d4111049410b1b00700b10203034802154009200300c0c0c2c04900146a0140954000c5000906c090504140031010b050599040d070002e11a120f85c42040081d400404001a01c500100d000d415028000800e80e00111040900c0704013010350031710034a50071420110002015007072080e1071080c01140c00580402c10160701c8511140c40a11004058000850009400415500c122035002d20710060300c2c40182050302c280d094401e10a015010b641c41040640d010500543c8401e801a01c42c44030040c4e586c0450041c170315a40caa42c0c1041d0340043e6917003020070044c07404114042203d0803d0000c2c116142c50714001944401501401805102e1880005070806210f54030115007198054501e485244140000c0840b98211950817004503d40000c0490101c0b8005034003410808001c006602d09800c116848030740f540c000e07003800d01c1c1d0340d0240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 986156079 1250 986154829 986154833
    0xd080c07111017071d2707081b0406050f09030a170a09051917100614030c04051006050a050c0109060506090c090a121a010315240909020d 61
    0x141525015885683c407209a071008075403201d10444080e282c2001d01c4081009a0003008070601e090341c034800708545044140c10200032002101c04d14180480c40d100445003000a420340242046009000c244010f26a04440030000c4c0114851801240d010030030602c603c15201080c1001010b60340c1c0050160750200c401a41d842480f40c02c2003416410182000c80c0900000307600c10351280091204540079066216026450320600120340610603440000005500100b401088255854540744d501002000c0d81e4014461031010340c0c040891180c05081c0c0312030b03040d1415015044c0140001c1c1003000d440c078508070342540c0c3e0754044e01c0c100050103018417050303003826000e200d0f14800c1c2d8016000072036a40707490003c01c00c1400d001442d10107130345400d1000c04243d840d2241d41038240c801c038816400030707584241440d0528840321030031100b48480101c0044100b003015400c0c00f6a080f46200f0030300902151000c05c805206148500c505100d405240410403411160000f034901400500b40c3d1922603459 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 986157329 1250 986156079 986156089
    0xb072111060a020a020f1c030504081b060a0e0f060f07020a0515010e070c120e06040b1602012604082b0510050d020609130f06091d0d080c0711 63
    0x4582c4082e00b2580071036440019501488020110780c02c0350302800800c1380c0740c00d02001c4801d01860220825a45800007000c004410044990440492071180162200c075400207035260701c211500c903c524103100e110060040d0011305a20310f50b0b8480042d098a5841c80c000c14541c9000402910440c0b0a80701e00b00041a0184030058070310000c2d990401e459070404507100d0205030040d00740c5041214400841c008182c0025000c41b03840e809242100d00850301d58001007040c0210f030444c4141c12000100c5210720314068503074540d414400c1c0c9840c49810202d201c0711a00003c1c900d0f9217084101d04800250003d00000b00608001c0010380503034039408100c4852000485800880f850300301d64032014449040891112003004207011100402046807a07404502c203030141400d600d000b4041d290100e5510200b98100307103200d0300c890708204629030392101c854010300780020800503402180713952000040f60125821407126200d881d80d4000b605c8141111506500482c4140d402c4850740c28481c40a035a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 986158579 1250 986157329 986157331
    0xd1401060519091a07020f0f030619021c0b0109060914060d230403020c03010c0509040b310e010902010f140d050c030a0f0e07060f05040b0703030e070b07211106 71
    0x1c001c50003a219a00c41c030500200300060743e01248074102c1c2e1000c0304880e0f9030026041cbd50080c10f5085280f2051412440030010f03010b040036100c48622001d01d004150140b6603c6403600d20000d80e00c110403991b0f1450143c2e80c8810718001c40e4000c410340155450582012002005001c14101000032036800d40c075155540401840d013a107840e00180c4040c4402d1590420600c20f108a0890003040780706050080a80640714101040303000e952680b0414001c1c0d0368860030540c8020384224981035444490108800c06504841c005980500c0c1c4411120044014841c29042070383c10384541d4241382c080801581d01c140b86d10111170f01c81a04000b0381e1550740260081c203001d0030714004883e8481c10030801c0181540c0015002c0d035070342d518201c541110320000003910070480b4035070308202c0b095110503001150948104e0b00703c01124080096180308165141e401710520802031019070f060245c845445940300d1082e480060505000101e41401010040c0c40c0ac2415074110306009105941100c40f003410440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 986159829 1250 986158579 986158619
    0x11060f070c12021003020f0405150c07030c05040f090c090506060d091a06011b0b130b1006020c0a12080f0d09141902030304030611040b0d020d140106051909 69
    0x40c6040440c00f1030601c00d251500701a200d040c00d50801021b42c10b00d020782e02461254901c079140b0030003100880b400340700c00c071400f104030502528101074407802c088001341c0151280d9802649000761441800c0c03081c0c491011465030141901d40c0b110700e8a81807e02404000d44656844a010031041110321840e1043c1078615208215654032030300003034000201800010001030510411032081451801d404942629a0358440700902503130325241304859090a4031140113211103e4a401c0c801c814005802c1c0c00211812503003128460011002409081d0844d48119468091174031070b91000108100042e002508228044505051003a41c0c11401e940340c031241030b241000750b00c80107101e1480a0126505088900302a4a90440d03194042a600d00c40d600c800b070182a5540514042c5803604411203008100300d055032902d03860800d000200960100c0720308110a442c0501c1031401340d4020203818121034550f114641810040065024044144402e18040114200c004034580569812960401c0707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 986161079 1250 986159829 986159849
    0x160522090f0501032f03010e010e0606121c0302120a0f0e03090a0e0a020c06010f0e07140702190504111b060124210c020c04050411060f070c 62
    0x145810300d4801252154510004881d0512005002003010520705210040b0091555103407011004444290181c1c1890000d905500308007504200403c150801460244100c060316415181c040421800b44d140c40c244680c0c580011500da1000c4410700b40c00210a01103050142c5001500005d04c03401d11004c94503c0d5046546107407e01c01003013203201c1c5117419006200154a40b0483d580007500800ca0742c41210102d454940000d524105203030151041a05040c040701e25558403400301112001540c0944814211040002403440c1d00c1441c0c0c1501e41440b0794801442c100d0f0903028401042203082220a01c04600107000815459034403a07611100c41c00d1601944031041003003502d1003c8000641028240d00c16001400340864201d43c0c8848401e841c034152001c81d0301c400c1c00341d82c0303125042d050034400758040d420703808440c05940007804606501d40c252442c007001d6404020890b0010707200505561220800003007981040702c0207080c500390310701040741130a00580d00d031071a800031034200003144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 986162329 1250 986161079 986161147
    0x303050924010b090a050a121403030f040b1e01081c05040f12050a06020a0f090e090c010320030a0b09010b181302040302040e070620061605 62
    0x10032000e1240041d1140c40011036030303995061003101280150107014290795000006200c031a160307244507001e8001c0801800da034003001d03622020007150802c640310a407480c4d0f0903110b15014048000c801c070ba210751040d9007482207540b103540380c10300460401080380007c0d940307035280004e400881600d150b0081c84188010581044c054880b01d014217071899401c014032400307002c2407203000100708803001506d043e4a0407201c07840403810414a0076100300000703080d0901c002040c1116540c458094401e5200301d40352040d00c150b40e018640071407002110300c5505500020a6002c1540c880d0700030440031107440d008800400340385110081c09620950f082401a45d1b915080a00c0e800c04181c1e107401032981c0c4090038101011184d1920204d40198061031013899000800701030040c0650548002d56009803003003054000e80d24501b951000e150241234081a6084001d09841c1c20320105118144a0400a04550f40340e011482810038580c8502400344142071040c080c1200024401442e1070741c07003051159007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 986163579 1250 986162329 986162341
    0x9040e06100b2106060403120503040201030501050a0e0a090c150207030515070f0c0510060909020307090c12020306040e03121909110d230a060b041406010c08040302030a030305 78
    0x5410220b900000c01018284071000304151001840c404020590316030203070310b544840c0080e07018483d81e00b000300600320a10070484903651003405148501c3c400c0c1c07070401260740ca44040110224140c0b25600e8803100300c1c1d00058244049070401d5036141c2c41005030701c910300e0319600d8044441c8c0c006401400181d000403410002d02408010070a008e0400075110300d003506045100404492070200303404240403001c00a10100701c002c00c86414001c1203040100685a1502c500d0806082c100005034442e1141203008140c900c0c10303101e0300c0b00c00340e5581c448403014070013540c4100c0030b50001800903034495601c1030030381e0b17210070144010a2184001c56a0310451300e450002041c81e030314034002c02140e01c1c0c40d00d403006001544030700d0507189900301102c40300c0c1c0b0f4840900c8c15080100d00c9a98182021550050000240d90001951139015115190600c9000c81640910003200c00d071501d1115000700030800324000e5402800c1a5030800e004926207481c0507244d0700402c1c50403c010404800003030f1740e4010000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 986164829 1250 986163579 986163601
    0x2106060f06052701020d1407120806010e0f0609012303090a0302150f191d010608012003060402131505070201080c130e060111120301080d1704150209040e06 69
    0xe00f8040310110164402410000f540c43d040040b12a09011780400207036824140c100c1070f100d0b6964800c032030241d80620000001c161000c180c1d04c59004c03881d0880c0114003890310459120407030401a00790f50801c0039880044800e400c404c903240c44050500001c4070390504620340151b1203061054000c0110101030302e802440d01c408501e400300c00e01c568100b444080c481103440981c01007480000380500140000c00c1c40020555442000240300100c04000c00150040d0803820403512808004c004050703000c12885d003010342103040300300c8000c0e007000011414a00399025055032462840c1c451610350322480194007401c0301d140310201045004c00c14100315a4032841d10b42c0d014200c112000c0c1841c00c00841407104c88144e0003000f0400220340001007907a4803441140d440a800101150980c00c2043c8038031450b54001c0c0100e950b14081d00c80705803e043e00039500788400040c840d884840e41d03a41c90302d901307102400c501c904414040c2c00700003090659885000710341c04507140a01a00060600d010101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 986166079 1250 986164829 986164867
    0x30c0405190e04081c1a1e0d020d06180b040209010504090305070605041b06080114030a020a09020f040b04080c0102100b0622050a03081209072106060f0605 69
    0x140941100141c103006180900001c0c541183c0d10009141d105c00c600340040c2d40003110500e49500c00340c03030144800d0800c031111003d0004c800050b58002641910509818122910b2140142c0c00c148186034000c014100242e4041c4c86a01400e00040d0051221040c00307070141b18003800350b6000482005210651801c80901030041404a40070000c480c0c1c166006410b40c05003100242c0030030758800010f02880100c0c50003415051210310001015030710303110040e05812003802500e00800d42081d0201c4141800207544440f150010501040d080c6001c040001a61003441d1b0200350b0f00c0103000000d01e05030040040c1000c1c1c4407000c058241183e10200080c584449264120400d82c10f128010501d9240c2204039505080c1c03401589015040000c1202c0c8044032035840a50401c46030380000052044d080302500400210039100301c500e8845220309650ba9800d4043d02200d07120401003040c044080007400c2401e036129080100c0d540340ea4100c40603084c03000352701200100303400084400c200300708010a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 986167329 1250 986166079 986166109
    0x812012c06090403030209130c0203070c090501051c140304030c05030f150a020703110d05030103140a1211011e0609150f151e180504092114030c0405 66
    0x900c0d454a000000180c007600c02900140602d940015142e003140c1700c55413901c60030000f000c1e060001d40e201c60002076613030388080800c0c0c075030364160b41c008249202d8a001d990f0490708000c1407001c0148001d00200c0741e0315000d6030200ca8084064107110076a107000d001500c000c0d0b002c1c4480f140011302e848245801c00d120043c0e038900c5500811441c4001000504646800c8000b000005032a40c44a140c00e4a04020841070b81201e4400c000f1020403860744000114142d03440f55000c907483ea04c0e200161562031604d0407004000b146a805a025404d1141811782d4112802500201c0d01515840c81c1114000b88080c60a240684986051001d6451400740c0060060495801c1c001c9034546480c0769000411070041d00d0341014078400e000c210501c200c4100300f00c06e044c400141c4d10005203a0010b00169000d040b80d0103444903038100000d85182034841e209400340c200804060306c1058007424050303610092008130600006106c0c149128850344040c5115092000c803455985041c401004500040a040c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 986168579 1250 986167329 986167409
    0x70807020105090706050a03060302040f09050d0906020606131b120b120304090b220b100f0c060b060415210908041a0913020a110601061b081201 64
    0x2e0062030f00000820008a442501e0003507150021500b048010b80440d510195015041069540440c5e501303500001d0300502c200121565021494020307a0102041c0c840d1102507081100011003c2c100082e0008003140401400a4ac07001c020303409100c1200b02d11060000140000c0c0d44070704103000c6100d40e0b652414100c42c0c40d00d070709448107901540e9220b58020407102d00c1d111000300c0c65a0701d80c680b8110410301209041100101c1d0105d458000305a0780b4540d5200300c403180c50000c046070054041d0303110301049645d014030f9618a40c44482c0507081901c0403541019080000045404044504101c025600d40d50025172254a4410a016141100012081e00d14041c64500081c0c07542048a08440c890040020414180c4100d003056000d03140005400982601e542d859200c0281d00903c03030001e00da103946004245e603500d41c40d0b0300c50f0240108400300307034ac9002a080819054034051032051260300391501e401e0f200008580350360400e90025405003085061a40c00018043c6a0808401680c031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 986169829 1250 986168579 986168581
    0x3200a20030d0810171c120c0e0d06020c0705060f09041a10080703060503010204061119020f0d060f18050d0503070e10031808031f08030936070807020105 68
    0x2480184c0320607204501003412141c80d0303030340310728405c3c0b01205c00d0074203640040c0c81039101100302804054903500407015031450a80c3d030f00f44103405049510300031500074004440c0044c055032940000c1d80203400d040f0907446003041c0002c007555400d005040034010b07d241c254031525820306100695064030316042e0007040c0002885107030b484005441201c0d40362803070180c2e0f01d030700c1e150000d40c003c28040d04500e801d54000600411610303003101250898103883c1c0102d54121100c01c00712481c3c243c000c140250300c1810322103502d000c3c0c9800161400c816009038400540b2003110310507042200d801203c8115908038a040c2075003403000600c070010100605081462561a060100a009040840c4010f1083e450035070a5031070184650301c034007006c150f400c140c045581c14070300301074105070811a02e41302030302c9a0440d032000d45203040c1d044404403420302d4021424420b240007000f00c01100c45428411849144400c11501c2018801c140708440c00510390b5422418507200041c421840200448156130500b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 986171079 1250 986169829 986169841
    0x20c0c10110c0d0f02042301030501050f011e05012703050a060501081b04150b07060f05090f0c0f011e03020d050a05070e130f020c1b0d03200a20030d08 67
    0xc15184d001c0c95044400184c540070960b040344090b10b64546114001c0300d82c070004400c20405511480c001c940f52010b410160ba030320905507260080707000304080400b1180004001d10350094030840b140e6140b121720750040314030042680c171000c180f46c2d2054646502c40144001403000901c1198054170852001c0e0850b10f81107500c01a08102980105001301d40d55001c50940403108846800900340310902e441da15809814250302810203401248130f868034020110700c40c0d010001e002504110110041e140704204841004806910501042d05008100c0075811003c04118440c3c08540507a440040c0c40f03145202c0b00b0380440d4001040515030500d40f0052164a0785c0000c2d064010b40000c8401000c482d15828268026141c4240b411b06040e0000c03d25401c00306002c1010b0301d0a5014000c2d600341c1745050410440760310101c21001d80800d0801309091404841c41290076442d20005c41143d402503010340c0c0f00300500702840702c0c011500c43c03603940403801454140a5241050706610704681d0b80d00f40300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 986172329 1250 986171079 986171093
    0x80d02071e02010315081903020c1005040320150310330809120c07080f1b0105090f0d020111063d0b0c0a0203030f0405041a0916020f0706090e0a0c0206010603020c0c10110c0d 77
    0x14400392507001d0340120014038144000d00948013c0c2140084a60101c01c224440120b60203040c001c0326211030314070101e055624801d009003441500000010070140760020031a036881c0c0d02401508040c6d001d81600071071501e008002c4101ca5100b800003c03c802500f100070003201c44501d03145070703040005c1084920a02d640701207154011540450340032102000034030058440824035014148a401010308101c0f40e400c14400f030948a80311204ca413403004800f41c0242c0903c0100d40c1c8003c81d40c0c040044c0500070104064050207041c8124000c44001c11015000646160441e54940074180ca000906019504003401180107000c03889481e00d031082004400200d0038400245000d0305200409004001030380f00300308903078040c050001a00c039003e443d000b0043c02980f650095450007010700c0301181c2012454801d81c401c0714000c1d40034000c03c1e420104100e01a40c4000a0f000940c030a8451408c029560070903003801d03610040e11032403030034060388070607038140310702c0d102481d101d0706c40b1600503030205000f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 986173579 1250 986172329 986172349
    0xc0f0f0902210a02130305030c0c040b0a0303080c0c03030c180f01020604150207060f1d1c12090b190f0c020a080d02071e02010315081903020c1005040320 68
    0x70110b07000030b490359000901c000030b01451054101c0c07030300c82c041e0000034080c3c0880140a04030340b8030282c0f0744802c105001d010039a83c070350a039243c00135564039040001c24400d031107081e041605295442d02d4018030030074852540e002900c60250404000658004204071034410344c030960400d4425622010080001070344510f80140090705c3d02d10142d05000005c50540c0c100c5d50030035402081004201c0d10744080400406040003409402aa000c1c1d031351101401c005805201c110381480500d143c0040100c0807200000480c6c1120307041e68440c0c900350000b84000c9030440c4608590407544520000c481e8070f0380d00742c0f81d03c0003136120528906801000704550204076542d03540c4d085410190754900703500403c070003032080c1c000140c028201c20f140c2080481009510503181c84c000d0340c040c0100da00c500603c010403100ca00c50541c0c2c03031703004240b018906004940c2032136003940079006440108403501c000c0380319030b80c0d100078103400034400090070b10402c4540a01e41c41f003400c00e5010304d1140c10300c2002243d40191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 986174829 1250 986173579 986173627
    0x605060403081e0d0b040c080f0a1109150403020907050405130f0f0e06060f01110d08132406050a050105040608040c031b03150204260304260f010506060913090c0f0f0902 75
    0x6100d4480b072100c0c2f44120204c070003010700607103010410041003248640e6604203000c200e21800d010408140000d218901352001e641e40103050f00600b000303a1144a0040994000a80c2c40e2030b101c404501070700400d8820300d0a5011510050146490f003081044038000d104801070381805400440390743d03142400562586080940e08002c07281c0c1c0c9600078105940d50300c0c83d03402030600d0580e40340038400c99001904d0b40c103146410034050051907110030401480091074060303103002407028881000524401d82180c3d4101e80140302040b080b41e140c6c9c441d1010b00c2d051082401010301e24400400c00c1001aa203420140101001d00b141414107224080c00806207200c4d1750303e9203e030380c1d110080d400e40d010b004460080c410308611a00c5814100130b048000402d50f41d1030461740c0500c0500612000c01801760b103115140081280d850681c29404000c0741c003c03400c1c2009070300d03a522915840090400c1c0600005484041d25904902d407908034401c0031101e840d001b031200d041c01030020b0810703d41c01f018120142c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 986176079 1250 986174829 986174831
    0x14070f051c09170709020c0309091302100c0201030207061104141c02120328030e1504170c060f090601081c0815101706040605060403081e0d0b040c080f0a 68
    0x1890f5105580780c030071a50004070440e840002d070101a040000010000c06400356882d0b20259103002030740741c014079806c001035044500d1011404a140c49002180103445c4141001414003425072681030132500300d072107041c4140303034005001d0201818040100400d008211103200050984480c3c40340310150046000340100b4160303441c2036008030140240c40c0b480b042c0e00d000700c00c0200111182a0704566140745200881c1c54010100c1c80e00401140009004000c100841d0281d00caa80da01024500100d080c0e110303803042803004854a40c014816a4010007883c24400b00c00d04080031514202941030f0302c052181d904c48032017001014140c18803c11913030f130b5030b080080d1550f032805186445c4403001420ba5500c81040643c075a0280d40280300c0c2c01650a8252141442c2d175038245c00d1100300d80144c040c6991054050004000054802004203010001220b545103544c0c0c80c004154600e400c19010420401c1e1621810f84041c281072192003813910300c0d403801200c0c508000348840d08030403001d08801226 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 986177329 1250 986176079 986176109
    0x1e030c080a022104060b060a1e0c210302130b030f01050a030506041401230415110d1e0207151401050105030c0306030114072c031c14070f051c09 64
    0x100c2595404100301c003030087d0000f6558210030f0402080c080260982580c4c41d0400801c003e800e0b842040c000405130f92091550001e036401c030502e08601c00c40041c10400701074003084641c42c1c034240c1c050f80304010030075035000c191603091200951400c5441600114059104440c04001040340011702541194000c8034550030b505d1503440c8940980308460b440d07a0102c00303022100d1100104c1c4894540704502074090b51440540d01642001030b2920303041c0306110400e05006145103240940e00000440f4105a01502c07000490038600c02a41c1108509855411030400c0c45081486a40034001c600b48040700203803410b46c109000603002d4000681501401f060200015015460035806541c0c05d21000400c100d0713514050a0041040300d020412118640c1c902c01a84c41c82c0690120060300040c0080180c800c021380c01030340c0103e119030041040b0801510644100003583c2140c0101541c90103418047c640040c1030802c00d140000d42c402c01d000b40d60041c0c54850100ea0300011181c2a255043c20b02c440d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 986178579 1250 986177329 986177333
    0x14010e150a0f08010c0e0a17070f06110714010504031709120606101803020904080f0f090f0306060d02040c2601030309060f020307121e030c080a022104 67
    0xc486544032486401c0841803402084003401c4414441c101c85000c402400b80c030032284c400f1a5040206204950059000202446010440f031070b119901c05410381124031007541c83c40003000c5240c6650085010502107180d8011080080c820f4030050f02c500c003107240740030802d400001c28911983c44060590186e8503901140401a0402c40f002080c00030b20740c82404c0145200f09444000c191080d51080e0a83c22018a41074010701c0007042c0302103416820420a80765800340300481d03800400c2114800703400c020140b1032017240c1c409450911006860941c5800d40c80342808454078034203410600c2503003da8100085541c0701c1108000c4254190b0340440c00c2e08071048140c520380e0350780301d6026207494021491079080810b005030341d04aa0085c1c0d504c2404590f5030074250381803c03001c044800107070030411680380410154a0240a042664604252000700d8a5010313000004414180000240c131119007031030f419440300320389410024580d821817410125207052071440d0700000e00328a401d1100000241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 986179829 1250 986178579 986178601
    0x5040807050922120306050411040509070e1809060c09032a0301020409090c09050408030c0a0c0b0a020a031b020316080d0905071a130e1902180a0914010e 68
    0x8065025560841441d801450203d84120103135140c603002914005c800211031502c0d01642c800002c0c10f15201b4989800c1c40b05000034604020300307900c02e00949484015032a1100d5080310344040b40340c0c0403440942044602e680c1406070103403140692150500100da200d03600464284040100f0315144600080500342600140c0c02040380254154804100043d0101c101e40006610601c140384c685401500d80d440c00c03045407001c1c1e0b400f601d40c1d082480001c05800c140c03402802e04c01c0301810b00d1001c180700c55951011070361003103d03aa4920354012500c580407640600460b1000510168400d0243c1030307800d0029604c1c05125106a042d8000506078010301c58031001300c884601e00d1400501030b0003035905080d980e61103603126501203000703408205040d124400054500b50781a4076104cc109503c2c00c1410000e0030030184c00c45260b0b4030745001c40b11100f18076200030900003100c1e00c0c01050440300c9408005000c2c0441e40030aa40d10f00700141403c5001c00404c106064030032048030130081da00c80440001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986181079 1250 986179829 986179861
    0xb2a280203070e10090f0507050412052a100903081e040909030c02100c0308060609040f240509040206040e10030c090f1d0c0105160519020a0501050408070509 70
    0x45685514414001e000c007a100b1013905032101100b051101411040851b01213810850710b620019005204c1440307205502d5109503482c80c0240c040b0f903102102d00b40311090300c10f50310340480d007074002c4030f01c80580a04096551844543c142e0406941d0a0703d940c40e90310841c07103000001070480c00090003503820417648406441c00741810b07660420680d0031515019040c2c5001c0981a071186220010024500b1300c078511404641768199244900c94691000340034654115070201a032290319203800084200301407041e1455404080c81200c641d928190011002c041c460b0000b80c0166062410040540ca030340c0c0450f011140c5a608004c42503940341001506041c1e9500014864080c12400150720b003070a4100e072104900704a410000083d02806214840004c0300314051039130003a200140c019801b4102a105801c001d01144d40c0c0320015658803420040203048480c1e0101d020401034007907092004120018101c2070800d54900f03402d20703682c25942c40d06440354900c50403420001994030700440400c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986182329 1250 986181079 986181089
    0x1030b011701170f0303241219021e030a0807060b0303040f0602010609020301080a1113060b0301141c300f0206150a031b0b2a28020307 60
    0x101c941c1e942c4505000800000440c50201c4610031039054a000710400f1045a0103107201043d580003a03418688141c010042d0b00b0b03030351a800510210240c040d0903050000240c0000030244101c000004c1e481001000d0100000c0c00300c400b84030540e0b070384254800054200e00d0541082d0031588800081c6442d101600400c1002c60301400013086c0000c5200c0c103400c2c1801940c0c0707150024009261140030a00481c0424812080240d00c0f0700001e0300403034500789000400400c007800c4c031402d0b052213208060a4808a038000e840740403002004001224420345a010074860888900d1142d03510b00303001c002c407150b607000064042c44000b0020420843c02c501400300f04070040381c0055a25035445000343c40c0365048102100580503000000c0d80c1c10207954010380400c0c00041101040728210380b12104201c01c0100300702410340700800701085140c0200054a140c0e010410030044445810401407080449840303d01c05a501651000c007203100c64031049038980002d08032260b0380c4021400001d142000742c0d801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986183579 1250 986182329 986182367
    0x1d041b0308030a0e0c010e0d0c05152d1215030a03080402041506120c0e060d15060309200402120108010606140f041203021213090b04090b0601030b01 66
    0x20010410880d0405148900e1202d8420402c4502c91118180c942404d00c00250028080e080411010702d005440039035040d001c0c0280b400940d840e000482d14401001c0c40c0001a03550206444c003200c12801d81c00081c200030340c000958141500c0510400d81e00400589100740030403000003500d101181200c800d4500b1000701203071500c4050f801c002d4002c441c00e5505a000b5810400710b0040c1401c210b0b0300170104c3d200d5a8030004c040c140092a68000d040c412224000c2009100c0c601c1c6840d9a444081c02e2449c02110000500100c1515148280e51490f4841c0c0301381420b040d5042d002c19203140720711107820400740c0703042e40040c0840005030080c40b41950f0003880c1c5171640d001080c42d140543c0080140c84841d11000540b0704410f40520084c01005c0402e0801c180422050188040b801002d00b1494072034011182d90880c0c0d94441645030f0861000c00008190200d0108007010250180c285180d00a580402940e26680c071307a04205540104118140b50700e80d0740d02c0c2030756485040b04004078412458 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986184829 1250 986183579 986183633
    0xe030a05010f0605210a02060a180306050a0b01020708100216150e0601080c0d060c140f03090d110c040507110a050601030506060f030d0c0302340f1d04 67
    0x3000348401e0094601903005c42154410f1117035034a01510010f040360000384918080e40e8200001503005074004c03005c102c0a42c0560101d1050100c01c0c1d03010354800d9002298614100d034280c0125001c1c051298115400520208800342010903500070b0b030380c9a03c0000d6a25031010042da10722004070700c1c0041c43c64036910301030711080382180d1055040b4050078007034400caa43c0e1a00a941d60b01d4540c0c401c1540640d41485400001b40349502074810f2002c282420001c0c1c0c150720401080302e4000740031002905100208108010000344012080540315092003c0000803003400303966a0000703880c00d580225130383c030007003020306010701c48a05024800c1000c4552452a525096480320000e01c001c031a607114820100355107251032100c0071441c0c08054020545c5c81d1240302d0071107110000303020584c00e501420300101480315804450100d000e80b035002c0a5600c8204c1005201840950b9112030b061006040c003e20000e440d940e0711440c101005031040d03d040d102e030b06021201c0000c445c04180d180305005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986186079 1250 986184829 986184851
    0x303110f0705060105061309090515040503041a0310181e0c17040503031909020603040b0105090603010504080d020d0f23010806010303020a0602070f02040e07181107030e030a0501 79
    0x190007403059034895401d0310240e903650820310085016483c170070144c10861a80034001c2c150280d0048011500075400c882c41006050010392120301d065506030340613040058207100c0c0700100c50110244140c9550010b1541c6080071240840d0340b0a07010340c00355848005540400914150403040203508400c80310444a070440800c04020080024203078049550410201000c80c010010140300d580c21102031440c541d500c00b500f910b041c240c1e032900690241d491094002580b40d8001541c49140310710402c0d42c0c47c0d4101010041180b2004100c00d100fa81401e0801002842e810252034210903100c2025031511100502c41002e84488511441c006281c0205000e6030043c140748480e41a54040c3c200400782d03250464161144030901002e00940d100014031400a01740354000c05501d0b02840014160340c460b680020180c0310302c40801007407544030103000d0010020400302d09444c4060301500300801d110389102c1c51414041c0500180c180041b2280308940360b1810f00c5031540050b0f110000f004680401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986187329 1250 986186079 986186107
    0x606090a240810060b19021005090606011215140604090e010f0c0c0c0501120207081602010f030212060f0301110d05160504290415120e0a0b040609030311 68
    0x10307200b000300c1440b4400400002034054402c450507100d1090b036542c50807aa442c21018003030000d070f85a0003148541150505c082040307118603401410254054802402d01500040c6040080310407440150b00d0002c21100100c0d8619282c422150140c0c403020040b01020009071090140c0d40c484c540141c10401c031121310380010362044030b081c2d01ca946e003009903c04541c0e0484004e8086600200100310000f8203104a40c014800c2c81c10243c2000405803402c0420390fa0044944c00501c0c941880510300340b4101d04540e040414083c0e116240d150450812030012403062920f0005441d4034000c1e050b011916036161002e4018401e000000821580d94200b0008014010402200c24040300d84a450025495034891002c40d411a00034810000030000e1280d610203c20b01d07c1c0740420084403042100080d140d070740c8000d0808101c200c0c0c4881c4d6100300419180800d4a81c140c607800f240d5001002414001040b40c103040b034005412000010304c05100345016001070100152002016102007101c1c0026404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986188579 1250 986187329 986187401
    0x90b220507020f1605031209010903170403021203030406061707030803040218090d3e010f05070302042903070f03093002060c1801050d0c080907060906020606090a 72
    0x25012586402d47c0a41c41078801c0c080c020303c2c0303800180b01500800c0803034405000340d030140d0580d409117481c060343c0303074009980c120094000b0042ca800101c20842070002900c60b810040c4a01425900d02c0032140c00340035100e098078000201501c0e13010001c2001e648803088881c1107202d5580e0b254407203040004c08165190780241c00c0c0000242304c911102290350340d0005000405480c81d045040d464103000c041819110501c080c20748a41d602c00410b0414002030156034001d1440303031401aa6507040c40c00d000224201e8124800380001c0c50704200300240c042c0d00c00c990b0b0061a926111813115021003044001d010595409000b48900f0150f42060703001605000006220401091102c0203e0705426a141e4a04a5485e109410b09000c03862904c3c9147c04111401801450680d2030410241e41d048211801014840002440c610070052100c2041012034050403e0341413400d00f00780b602e10029590711008011a024408034404114031a0380c41c0c004181100d40504d1040080c02400044401600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986189829 1250 986188579 986188589
    0x2072c010b07050d020102120406050c07060c081b0f0306040504031404060e090702062e0f08060a200a05090f090a0b01090510090b13170106090b220507020f16 70
    0xd003110780c0131040e0052003100e030900d142241c00140769540380c80303400040070000d0800c020203604011b1100040c03450b129030804007642e41c90700b80c1c0905000c501051411a02c0303c4c06800500c080040d480d00032281401e403039100c1780c1180d02184c070350b071107190480b041c00e241036880208101c08140480c0854005414529000007524001881d075038241c401c9903140000c0d2003280b43e21016607041014881e03414000011205040e2540d60402c0d540c1c42d20750003a94a550042d290798201d201030200122060064603500d40c0c0488003800b0f460403550680040e4807407203a240c1c0a210000440214070749451141c2d10481100410160940c98440e0046014042c4104c401e400038001c100c0210b0a840c15420741c0c2480e49051395410f0b26141000308502d125404400c954000c4040c81d0000075543c049a0714400342ca00c100350012454070303d000324503015a005504070034410311801825504049071408040110701d11000c003c14140c580070000d9080c003020348410b4640380110345801d007a01400300f45940440c2c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986191079 1250 986189829 986189833
    0x1a06070f110607110f040e0312090601060c051f0603080c0618071206110d052e061e0909051320181f0e01060807090602072c010b0705 59
    0xc030210100422071252100083c00240084203044041c01c0c00a103006070005d0190001135203180322005c0e076203140c101840c0104240c0b285410480002018008a030040c0800e04140c91011500c0d51240e80711558690b092a43c642c185000d95100b107003d81081c8001d503080340e443d580d40ea1981c009940c407242c0844041b01c040000304100500e00c20b0000d400d50498103260003c0e103042c0c0003540c0d42c5010300081c0c82e018000c1041071006440035141d510615000b24500f00000c01c5079460b081400d0090040b03065405100701c05040304021494005a0450340780751041d0042030010b014540641d80c1910a030001c2c80709519200420604003e40c80c020082c00c1d008205121b43c00e24000405040a50000d22998020700905c10204d1001046410160410749801032002c800d8848030011090700c0d82c66000707c2d81500884010025550480d0313290343c10000d42c0c82c080e200107080100103983c2c0c591501c981032000103001803040d01d10f0000d61000c13071140051580483c0c207507503541142c034060b04030303c40c180e480d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986192329 1250 986191079 986191103
    0x120f04080c01090f050f0105070804080303011a03010e15210c1c050309041e05090d1d220204170309030c180114120114071b020102060a1a06070f 64
    0x1d9030003100800e045540070100f20780d4007402c01c010b000b03c0001340b408903810b000040c030a030000242c0402c0a0006040004003e41e241d603d441c4071691078100104101070701a204100500817141c10110b055800110300d02d404600c4002000031a01100c0e00d01d60622549458a40e002c1103244045040c40081c6407c48108000070a5800c1d100e46200035410010141d030304c2000340c2a13150620380c014115020314101002000616207509505a410486004041d070b00300c0d4454070750301600004001c96004400c40301d90400100a008a40c82140d11054050403060000c40c010002c240340c2c0484005c0c00c08490104031115020401540e25003058903801d2003030107144025415820084401131b00500029424581c0341d29007810b0b400d0345070600200b180c0040000f07030513098000c005d00072410701032242c031750000c00c40c9000b03a001030208081444208002702c0a951410241c1e80c0007404581114450034001801c2544284443c0c40c0764142c1000ca81044c8045962400c1c0b10503511102200307800b0301503803140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986193579 1250 986192329 986192353
    0x10c140c130c09050d0305093307020907030b0a0812040504061d041202010609020f0c0c010801060c0b15030d08090c04050403090e090a0804090b010e0603040f02010c05120f0408 78
    0x81d107450b410308200180d9220001c00c0705141c4000045c0c45103001381011172512101801040740407032030b096225042c10403201201c20781700088a620482c80ba03101012400d000702640003034184400506103008140c0ca801c0d80844699405c2000401840c404044400424241c10010003541041c850785109502c0e00b0000500c00030b40003905005080c400444881c26503441e81c461100e00c41d101d41d41c204540d61140d01242416161006201a80d4100095515610b940742c40d07600d400c01d1641083e040164002c0104941c6400007000401198890300d00c3ca0709544030074480480900b046d0350190b040c403c1050962000390040c07451402200b80c001038607401d885000901c0f0507030700d0030780380180040c85480007040795920300d12809030003010b110191400d020203521800c081e508a03801081205035a13888140440d84c0100070070300454001d907109030442ca400d848000280240401c0a410700640c420f00c002000b405000400101c4140340c032481c0c81380c4407030500c2003841e0080d0140c90481d224400c81004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986194829 1250 986193579 986193581
    0x9150302010813030806190f06053106030902040b04140612010902010e122a040606080f13140a05030415020609060a020c01020903010e0a050127020906010c140c13 72
    0x40303030a80641701c141e403d841d25400e1150308140c1e080d0f407094043e403072080410782202c0c2c0d0314418002e100c0355903050303111031000008558202d07524110b1200800103400a80b10905904d501604403003481c03c0c0090000d81d9400441c000d801558800780d80b00d480c250300e0b201e0f1013000404441c091001a0f4045001c48061845ca81c200c0c2c00c034010103404221081407090035450441c007402180c02050b004e80c1e5961a40c0c1205500031800d240d00ba000e800300355070301181c260819200d40c0c0c0007440f0741d2411825034180ac2c4507400300900040e1131000c0e26021012020180150750000181c0b0303802c0001218000041d40c1005034582c1c104d8000c030901035800040c2d43c00040e00c00220350f40941080400f40080b5204c7c214118025407000c404040195000d00c030010351a5420b01c10580107082d988007070b000290040c500b441c02c44a90f038045100d9980340611410000204406c0480c400764151809036443d15603c006803111301c1000001007020703035503050108030300d1404100e024030070000385c81c542540140000004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986196079 1250 986194829 986194861
    0x312010b0d06050907020304051e0316051f0c060207060e0601030305030a060902390304060302040e1f06080709030204060b07030e0405070c0605100b07081e040e070513091503020108 80
    0x5c0c00503482400140500e00d0004c0c0f121600710b2006a9148501021401107130030700c5850f501c0080d1008003644c00f04070720701301580850321150300f00781a4a1511108140604010380c08000900000da000c02c0000400c40e01e544030048008140f8221402981d491070300a11035441110b45503203003810f20200046102640c000c0c0c1d0366003002c5a9013036443d01140c2d02c035406903080d02220a8161828240c00d03114945081c402040a80f6140c0c2e400b59030b1f81d0410341464108200541038000002c10312184803252660b0202150a07201907207001401340e1100002101d110210b070700040c6d1300c68984040042d50040343d50051002d9403081e01c50b4038940d1503036000c102c12a501160b1071070104020500140000304039600003940072407158004450907803244c800750b03021f400c040c03411550540001102500312001ca80c41c4010948822042c0d45000d04007001100d600c0c00241c5103805000000c1a00c1200360841e2401c0806452084030801980501240101b0b2215041c4000da002c40c90307900200d9101d0010307403c94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986197329 1250 986196079 986196091
    0x90801020910120623041808031305010b0423070306030b130c1809051605030307120318030905040c08010f03080a020a0c080a1721090312010b0d060509 67
    0x30064040300703426a0f0300e54a50812222180e034515000c03403c44008a0140c0c0360031100300120500303040f004203200843e0300c00707120503011400c104611000140c0740021260b001d00e051460b9040380340907203031507400741c038102d084103602c18103102c40d0400740c0b5004e10000c00407001d050410100c82e26244020760498401c2c1c000601707951201c000080c022a007419031100504e1040c5801d06c2c249aa500c404032401c03400c004032040312522040010705005080094561510001801e003209900e00320003c4d5481c03180c1c03200107000d1428840030780c4034140294081c2e8504038003006880312881c02860004c2004880d07010780c0d4883c84c5028000710b90a485811400d05842100c0c114901c00c50854540b454039400c4560140210711480c009940000c54614a0071300400030b002c003c1108601920709100504c5201e0401c03000e1510a001c1010303800e0b50000f5040c1c0c106000c8a03c01a0783d200c105095042d807240700f0f016040101e043c0700024102000c1001801c100d60007140030456103445034204090071a00381c0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986198579 1250 986197329 986197339
    0x8010b12010b13080102030a0617340302121507030c05070204090807020a0b090108160e010c02030c0324060402210a02070f06020304110f030d0503130b09030a0908010209 75
    0x610624811000805011050b03e024000c9030f9626071015003aa8021210303050150307201e00d0100040851983c1c40564101104058403c140524440001401c55a4640d0141581c4003a1520318403082665900181d41c02401140030302d41c81c00c801981c2c03500a075070000c1103c4070510024294510a2080c082482619074445180640c00e40800010b00441c0304140c658040030480c0000580d40e40c01041d005085500b1416144c011250001d028400d009102410140e01240d80780010b680c4100c20000005090800201070801400440c1c50400008112900b500c107580c0005d8030740c82e00355600d11014408000303044c1e1540d600001d000c02d0380203280d00c074072040020045210940c08141c0600e03602ca1b03c05c400c01400d0112945903101ca42600c0541514900e9000040c0000d000d62060074003003013041500c00d9a071503012403004c2a91914416106400c000010000c01c884003c007904000c440c030703080740d00c0150030305040219549a40c0000501070220361601000510f0f510180240c070032502d00141 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986199829 1250 986198579 986198581
    0x70f11120c0105030406020c03160309140f0409050f011d0c030c0907120e120a180b032e08070608101401030207031e020c0f09040203280b01060503060108010b12 71
    0x650f0542c001610445440d82c09000c501c03001c00c01000540300401d4901e080d6070940c8400c0c240607141d40460f401000c12004540f82278459510b40c0520385820719015100010f1010640c00c001d030a10061585100d41c5508210038642d4036005a0700028040381a141030707070b50380b01c400700070943c0d18100382e07080030b421458036400104890b0085542c1c3c01d801c0d5103800041401713800140c5443c207050303119000d103200d607502084035409a50300020100044107200c170b2046883d41001c0811166000c010400c8201c625282d061140c080c042c0c1c12070036242c1d80341d180d940840944403010303d625000c1500443c000100810700142003007091071403401c00c4498640c0494694040c130070044002c1d52045100354144841044c0110004203454010403800e0790710b6024107112414001002003040000440910424000c0180009a980840c150700e5140800300340e080254ac00d8400c4c070b005c01c1035005001e44000d00007000000e4440c1c109008603c10402603036100500ea0700d44a00207014000c090000c40340c003007035038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986201079 1250 986199829 986199853
    0x18150301320409051608060a050a0207050c1c2009160e24030907060305160905130e03070b01030317130308040305040906090603110405011a090d0206070f1112 70
    0x42d11209000780030704d06890b00f515100b402c00810b650346602045095004a04022031001c45109983d04050445000d602e0114903840e000d545142c00d541da5803182103520803a000b031801c902c850b2116540d000206c0c0f00d103442c0944880400c2051200700b00d00078480c1200103244080e101070328400c010129251001180c15900070b00c0040500100c0c0040e45000c1000c104500e2060344d009144210322681c001d014190400c076006056a2010381303800895500d40c1c1d0b0100943d900001681e082d100c1c240c851602e4a40c00c0f80648014007821008480607000005000041c0211480518180c9000b519100c400e0f01691100902ea0403080790f070041c2c801e82d818500000a4407503028141c019000345445810142c5502c00c12040700c1c2180d000040c40c2e503441e81c040040100c420b40d0320950b80c3c0708030f07010402076141c0703250b10403512000d1a02002c801000620303c4202c1e0342d040098803182e41c01400441d202c80d828234103030490101c4017100b034030040c20318942000035203000e00c841405056944007810418800e5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986202329 1250 986201079 986201081
    0x1a1c150203060d06050408030907050102070f090203090709060605040602150f010b030a09140106051306150c05010e0106060302092103040605070507030215030402120120181503013204 81
    0x42c0520b90f01c200b2211010000c100917015a9000c0d9006c0c424803a41d03410814031143ca0b02d40c2503400141950408001000b007002402a420211101c2413005079803980d48007807443c20842d407a00140e00ca640380c0b5001185140c0c3c0075000d0300c01e5034016005c64100944071003000002d42c0c02112304980003500e11005100c00c210140107150480120b10020130070b0041551003aa180d01c610581e49280d2390b4520042003245400c0203d00582c0300010010040c4500340b89607a007081e1981039105003071082e47c3d0292410072400350300015191060f24004c02042c0e840e480c00802079030080701040c4c401c014044401e00d41d01c042e01c00e2045545101e000a618043c5892802d541e1904103580550309802048000009a200d2103d04a14521203080c0c1170740c0c1e482d10b40b04006492820802c03441d85a89002004182d208231106c0051a080180a0b01030710f074100800648400940c0d210003e400c521000c80880240203040c000e54182c0310800d42c400302c00310034401c04044400c01e03a19017894810a81d44030207218106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986203579 1250 986202329 986202331
    0x1805030a0609020d020d060e010c0c11040c0507060203071e030e0706030c12020403061d0304030b040f061d01050103110d17030c040305120a0f1403160908011a1c150203 74
    0x3011380b401a000c4003a0700014a401c40c200820745003e83c0301c0920812868003032082e40101040d40c02c001c0641c034a162101c1d400aa100c1ca01280034568601300b858805d809081606c0d5119800744007559240303060200182001c0004030303200c03200040400321080384c2d80030b401201106080e0900500a0921b404401ca0103081d01c9a160b80c280003142030207040b02c1e10240020006903004850114202781c000c440d0203000520011100c81ca504144014400296149201c580240c1c2200103d09204107a0904000a107102e2920310104824154482012079042d00301504a07400b822101406401d5041440f0559000d55402000f920410040c10b118074a86006550006075480d003c030304107a00ca98030140b50081c014541501002c0128040e202d0350b9018401c0e56400300c01e4a0b15403a032120410802040780400762441006680401810015034801d00080e8002c1105800038000c801c00c816544800c517619440c1e5038080c3c900c09504a81c806104001c00d04d560f40d2102d65880c5c030400e0200d800c002500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986204829 1250 986203579 986203583
    0x603021005070b06101707030b03010903020f0c0f030327060403031706060307051e0706061e1e060f021006290906030402120705091005030c041e2301060f1805030a0609 74
    0x10789e6002d1640640c400740309850040744240c0007040b00741110b080c010314060302c90305598418004241e450001d6180070050b901c00c044914110440303940d00a85800ca802c126440703054000001080000500d64080c505c00040a4610074400464440c036051015a00c0200c074030601040003009010104140011240444083c0034a214140b408a540d04c4058501d00d503c00c820b991426560b540301d881840c3c2c074000c0144944c21980342c40184020750b104540042e80314000600c45010b007800c000c07a00a000315100c0c14640f5804200c0544c407076142c00412216002c010201030410755a04c0345003c0c5040c2203960000004001508603551907003000719803209010610741e41e0040d0b00c4009202d4980ca24407074010450009010b80740e030309080915142240d500c0100384a6030a002841602c04107030060302c9111400b5101c0420103c170385c00800d1507040d41c00c0182d40c0c1e0403d15200002406079004c2030721018010a079440000b03005c400000c2e01c0744141d10340582c139495005a80c3c01800600d0a60040071464 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986206079 1250 986204829 986204831
    0x20010215161209111c0b0604110d0e0706022514060c06070504150f210209030a2108010f090f0b040509010c02010e01090b040b07030603021005070b0610170703 70
    0x89440d1050b03000703503180508111a030340b0303220000007214507100c2d214229a81c02c003841001501910303152801c0b0a14050a4180180e0b66407000030380010304c9501b200c0207502c0301c00041c80041846000560340300070501c941e60050154140300500d01d11000d1004100402d0616084d0661342030418016080d2105c06401c2c2e8400010000013882c02401d1003614840c0c5100d0b00c402340c59a2501060800d103100e50b68003001080341c04600c01c54080d0f080b14103d6004409103126002111002100c00c009120711070080e58544214401c00c81001450521014002c000100010380b55040940a6400c40d1080c000c0e00e83c56100b2a03400e00001c3d07400c0d4409a0403c0d6900c00100308282c107103010408580c4240c0d1150b90030794550100900c843d03024041c0180a10b50500204580542c1392076807182a0009040200b101005102042d500c0c3e100390410800355030018403c20f03030359600c2180500b0b145c0c80079000300c0d460303d400e40001b541840d00740f00381c4e8082d10280c0c554408a132488042d102e80504000c002e10149 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986207329 1250 986206079 986206097
    0xd031404060b030a0f060c09150f0e03031314120d0815040612030c12080903090f06130b030907120f020909011409070602060a0c1704060204050d2001021516 69
    0x1117030a00d40403815181c082c2100041c2c8048800c0002c2030f40242d41c0100b0540313004403503021100c03a80000b100f003000303100b03241143d01ba40800000900794803036803d401061801d07181c00419101509030130401c0400e42111842009140414045d860b8504502c2c5400032602010020b0342c491705c04c1c3d210306207400e8002d2001605507241e4120300b0340200d0040c4141c00280c90300620404204080014145100807418841d4462074000d404070345d40d11405024501038402078140d501c0603200c041c20388100280b0410707500c02c2c1d103450f9440c0a58580088404c2c00440c8501080052085924140501c403241c0010040110f82c8290f02400a90440542611229980c0b001064081410070006c6802035245001802c25a840c012b00245001405403d40401500d040403a07200c441e0407508081210803240600b0342c6a65503803c28500034003c50784200e030824401c0982e94100b10800d28220300b40c0392282203c002c800c4004004a80d40d0301051440060101404085030180c003071801c80c0b03104000f00c1e10b803070003c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986208579 1250 986207329 986207333
    0x10606050f2503030b040507030b1507141c0f0c030e01031a03060f06030705040501050609040504030219111503131b17031b030f040e0601260106020d031404060b030a 73
    0x200b0107600000f9800240d548105003010714181c064990004500d1800303000707104003c00040e044600c0840301146038040020b941c4108a02c2c500d01031030700c002c0b24060701d25601c600d0090708012a022000c403000030354805661414075000d1803520440b80e800d070342c030700030554100320043d0001d155150b100d481d850140c00041d84103030b50401c2414841c200b08503c80c04a82044020306140204a8102c1c1d445035080c4001840306484150503240018011900400d503a15103060036410b04081c4100021038a429440d104180a5141411080c0385020303211040c49a11000d6003105a000540d450b00101e0101142c0401041d8150144551900c0c141c0402004607a02c01102c02d4804841c90302048603040820800e1204410b10885110014160040c514203031003009c40c0101c600c80d60060010540340e580110b0340503403051004100d80030300072100c660000d07006181d0034490542445511300600c5085400d8003014442d004000c90468140c80800d6075031100c0d81c8141c040e10100028a416200790449200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986209829 1250 986208579 986208637
    0x5030a0e0a03030618091a0c070b010605041a090102060a0e0715031d010207050604141203070215090714010507170f030a140c0a0c0c0b030108100608010606050f 71
    0x181c0144207441c001802868007074180c001c5418001d104c0c030390b285070001c0200411541a002d0507c030702c0320a01c10403240d0340c0c0201600c0c14064140c010700003001940021400ea84c10400410070b8951410507600440c03500c8030076a41d00e1080d00c680d00e0046e0071070804100d00c080c26411951240052400382c0340c000740c881e8251107a022a010442e0006610340004000da04a580a140340041f4900003c2d0b25103d055158550380344409403000b0592078107844510213030007040c400c0d4241c0000c000140303984c81c01c00c03050080d0b423454030350b44150700850b02001180b0010320000720780c030850384966401940440034100540703d40c1c100c0c0c1800e0b00d103c0200d07580c1d003080d1130201c3c2c0148694440c002a80c2c0e16814441a100119082c01c015010503090540900048150550696940074020f00d0065118600e40c0b400506040c0d082d80055160746010001059401010841c0755040c01243e20802031a55034458550036603407540300d0840801c0c0201310b4820180520710082403503c5a04241c410b2032a01515030344 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986211079 1250 986209829 986209843
    0x5090a0f2316031406090717120d020c0606221109060301030507080708060403053c0901111c0e19060c200a090b271f0b040605030a0e 59
    0x841184490500401803a64030343d8151880304c2d0020400e5103403581d90345680b1642c6004103009102001e920618260f02040740c400c010101034126030b15402c400741201c2c0690040c0c0030102081c081e000004071035041c0346814910b48080112190f034050381081641000700030105c01c500d09080e04010350150394030745400035402144618006e00e2064035107200b0609042c0c3c150003892042c0c1195052101282d40141521142440310a24070700504155409110b411149072100c101090014503a803000461a006061074200030b8a0740400105594285501e64030002d55401c1000e2000c2c20049585200c0c04c0c141e101c200005d014a4a14202c1c80b900d0304420600c2d5100000165200703156804001b80c1c6042000da0482c44c0b403080403c806100006860012a4091000e000c0c0d5149404010340d0364051008040c24001703041c9803c2c4ea054400c0604407500100c0ea01d451409125010404081900c0d2412040340c408180443c107140c1004404c94065001800716030580303840c1d0711540b4003003c1c18081c1c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986212329 1250 986211079 986211103
    0x1050c07080d08250e0f040c030506030d090503030712031d16050a03020609100909060b0301080607020606060726040b0910021c050919060801030605090a0f23 70
    0x600b8080b200d5000104100300043c5036442103e01c491080828030384d0100d00354200d95007410500016041305001c01d040c00703108000c1941c40b41c02d10600c3c46074903401d580064001e100603003d0350f400c203c0042c0b065030030003168450542c06910400041020501e00e000c491441c5030217241c00b280010052031050174449a4044415054018541c0d07400c81941c84021240102001c0c1d6940e20010b01d1030300003403064015110030500a00c460459800418031490700f00d0b0143c8560041007000784e403a140f0449160704240500c3e60144501e4003c01c07070180c000600c50b40700c0d00004055516103040303a680c016200118440c020358410b000c0d030400701d4010040020300054030468201a4841c501001004100b1201070420000d540140c4480301107241d000000d02464481c9040550350350b0f61100220305402c0594244c0810200e85410100d480d69000f41180e040700d004403000d0141d91a014007080d26a80c6401c4001d041c1e405084001002503000040d020b611549658280001508012441d04201c4d6260039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986213579 1250 986212329 986212333
    0x170c0a0b030a050f01030b07120b12010204030605011a070f080c0d05030601030513020321160303151a0414190e0117010e0d050c0f0d121b020a030e01050c0708 70
    0x4115151080b0f128080d0700c1005880700410310b5145880715804894003904401c00c0040c089604c031407a245c540c20054452001821189002c140000780343c1c000d40080c0012210103003008000034004000302d4031203914a80300f4030542d10300710b2a652642c54840c011002107035108400d01c205010b290080c415212014042c0e12030036944d15198000608403180148403800d08080c800020006d40c50004135030400000f000558001d2141184c010f68584c044d07440800395880301a064081050740c10b42001c603101d1003a44003946190385075400380c403a103c0c0c504460100708505100400070740002d8011600111005003028944000c0c41c00071005140d116040310507030780c1d403400041200070005000d03100c1e142c44000081060342003890311103495660030790f0f5103400c01c4000304040e01211001d201c1003216401c10304c226483d001c2c081c8000781421030000c0c0d560131000e26003001d22280c0a0200560718284040da800f81c86048043c2d074050740d4600000e90301c1307810040144030703114003035a0801500001e00340c4400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986214829 1250 986213579 986213581
    0x201005011508040b0f0601091730090105090a050d0f050c12030d0b0a0f060e090a1e0c21060302100216062d36170c0a0b03 54
    0x51402180c0c5403281108004201c0c0030403020900b5140b0880d0012050381d1780c40c869403150f000480c0c0b50185500b003003507a00300c0c4c0c00003030001c143c002030105500b2140d0001d411010205411102000a0680d116090400204003c9000e580329400030181124001c2c0801c4ca51030301e81d0302080345883c081000300d440140002003141031140410000110300301c01c407100701d49c01503001c0005413a40250181402c8550b21529a0314642e51f5945828010f0002d02c031551000030380c1d50b08010030b40a12182c0301c134010039611020481c9143d050003a05041d0001e07641000e520041c0a410100500c11034024004101240c4040484c1220004541241030803190000ca01c1e03500f1401040254409036505070199480004500c6c3c80b030041c040c0310802c60381c10703060207410f85250684072006a8100b0392420314a80d5200b8010f12095040b8040c104002e60b441e040d440b1107040c405161070510600200e900c80500e020400b008041d041007000040f03081580d0943d40c3d20012800480c2055085802c8100072400c084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986216079 1250 986214829 986214839
    0xe0c090a0b09010e0d0204060801050403170c03010506040b160c081b0d0507230301020d1d0a210201090c0f051305040816030c3305150120100501 64
    0x3840400034290803100c96241c03080da040060410400c0b0100640600e6a1094110035903030b440c0e020038002c02000c2c00074001072a192500030000c00300c80c1c644e28204000440400c1c054152312090728142c6030f000c1c1c60180f070039003011244802d50b04101c20401e040c82e050080c400010f031440020070020b01c420001011081501e182e6513565582082003140120940401c040200e000001c5001c11242402c5c0501741c4010003110381c1c0c4142d01c20382c2e070660300b40d0700004403030390b03051016130009207400c0e100d0402c17802c5449541c0340a5105c0c2440a4007038140d044100d002e4221280c03c203143c4c041d4074210300001030f4a4482d07985442107582c01d5442648071104980c0101304070308040c188541d5080f202c100811180c613190792000d0203409140d02010351000340141c08002c00d40111700d01e01050f504103c8250400302d46084070500929a2103154000300b42000a41015041600815000d00913413940e81c1a04040b8000440d00310341410780720030f08501204522110210280403441c5030403040c03440461158101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986217329 1250 986216079 986216089
    0x5010b0d081b06150103051b13060e0405070f08070216080f0c030312160e03060a050a0c1d130213080c03160b0d1d01020c0a050601050102060405030307050a090e0c09 73
    0x28840321030f600a070003046541180e280984c80408030034240021140c0302c1880c0e814804000080207480d2081c005904001c20680041140480d0b40036640c1140b00c1265a0520082e80d400780e03090004248099880303c0c000340507030301a540c002c155104680b400e02c09413001c4010440e050b40001a10b403c10489021072560500c4814000203054004500c0c1202c1c00200d2445810000c040800b40e002214a070620284624045601500024119210b9051400c00e1800526003a83c007400f0003403400b500d02007440d009250f0790040c0c503a848000b01c52602c6400603c44214441640f005a180d0b080206c800c1c002c602c803080901412504000302901d0640c081810b242001100040140c80c032164006c00c150100c4208171106071804110100b000381c0d080300c0c2c0d03004071448002c5c440103650001c281c14000c2000014000c0c06507014108891059070f85500598484a080e200905680c20070070001e0b002601441c010111401e0600c1c1040103242c0e1b40790f20742000e40c010b071068180d00400090314a840c0c600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986218579 1250 986217329 986217367
    0x1090507050a1e120e0105070909060b04090f02071e14030723120d090209010b04060206010608090304050d0f301209080d0603020909010e0a0f05010b0d08 68
    0xe80d0810526244040c40054038159110701100c000d0f44100c0d8440000c00c1c404c00d00700c9010300150300b0510a048030405014041e00c003c95020000498001002507401c109024200407a00b000400303a24050410080601410100740c25140c100c0e02009140b0001b0707000d100c0c0ca907010b031a0040e645991025843c11201d00915000d4030716036948107001c45404a00c01400902d04000c0e03002000491045220701e00d420880c4118250440800100b07009200f415107130040080a4420ac46200407030b80c9070b45508a0500a90041c1c00040c0e01020044c000d803401107101d07503000440501101d0a00f0b81c0e85000985c503140c040011030740c400003801144100301e450f405407a220022007000240c0c45221801203100b840b51010796004204507028801101c41c503650259071800d41101c0d60701e035150100d505000c0940101d02c07089000f00c0e8020300240031510188038080c0d906281a0103400d66042d0351319a800618031210040d0742c255611040e014050752600070200e0498401c00344147c98480d26a0790b1600c0c0d40c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986219829 1250 986218579 986218591
    0x31a061608360612091005040b1009060305060402090727090c0507050c0603060a030501050a020702240f09130212040c08010c02064b060117061e0303070b010905 71
    0x42c00c402c19610559030f06056400b55510084400c04036682c582030940380c0a00d001d044034449103800140424840808a079912400ac0b04905140036a510351140048401c1840007500c1e47d0000340200300180303840305100d5000051072802348920380030b404840600b6000d400340c0c0e480011b0040810404884180107e601141160400f1800d02280380c0715292111541b40c040b9103d8900040001c09940c1c2e102680c002640d0008020001c178038020300310b90020f60004a0503403080343c036a00070120110191181032055035007207210a04210351940c00c021300341c010317009155116a0001d59054040c40900c05410302d092108450680d034101420680c05082c02d580026410ba410294000001c82c0c00007086600210002c5080310f42c0c6100304203601c0d03940a02c1903803110b04d42245918807450010740d846a5500d4007020008062910b4001c01582c0040c04451030180d038020040016100340380c090781c01c8a644402e580303140c401401d840c1c0041d05590000c2c804864a0104800500a040892042e01d60002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986221079 1250 986219829 986219917
    0x1050301050106110a030c0303020d060815010b03011505030a14070e0a140d020f0a0f0f080111160809010233060a0605120a200703020d031a061608 65
    0xd450b20364013988455160f28041d05000e04400510100341c8a58111109500740120410009803140781b41074580802041803598100b9841c004900e01480c0804c50341201d4410155201c040c180c1402603a03184c1004001c00b03031007a9900050062030001c0b1683c50310410385035540490b80d002c4401085907010b20f6400c039103501a18002a5603583e1207444130f42d000301d901250100b00d04840003000445d2002030b0303040100070f28840e40b00003030fa00c14070f592100c081e101030200074040d80c1025001352040d8001c10a40044404080c0c4200c4042540d03400201036020061041e28504604c4081000d440c6c1007041d00c103d0385c04405518030b070031021100c045c2070300003100f01c3c2d480c5900b600c1c11000800b0b5014000074014141124004070711016201d034480f0004102540e5114401c040500c2481241e8100d8482900903006400a10001c81d109100e4502d614400520140d4000c051400780941c41e001a15008040360528500801250400300a031100c11401c082d201d81c056000119003201081c2c0d040303030340300203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986222329 1250 986221079 986221097
    0xc0203122206140f041706070f02060402010e330309070902040e151f0224060a0e150d0501060f0f0605030417040b030403020d031a0d170f0a050301050301050106 71
    0x40d83c0d1040f0110700c0841c51110b080c4d103074101c04284e1405841213030710000c200010707441c860f85941404142030748580010f44418800403503c08081ea00c407841114000e0006032110f103851014a000d021206c100000f14015681c070b8001c11740152034081000021110104011040050303002d01003100f00701a08580505508080c6482ca660f618058054602c4504e10507001d14420142c072280341d0070f800d1400c100c2c1c1d100c6610090a9019403601c004191440001009083c001040340c60084481d018007000742c800d402292414500d10001e030006800700505455010b45903080d80c0ea1541280e414074083e4000195a034507003d1164450036095000740300907188502d0400809400c04240d80d4400e8228603502c1c0142d000c0b180ca10030034071684d044078903c100044180010700d640021184c0301c00304152002c2144000c00224001d502c114040200c0c3e1040c020007159002030f6040494030406005000c2450500041c4007242d002c1c4c2e00b01c0c01e103a40014001000402c000d180c00d01919004002c07608094100c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986223579 1250 986222329 986222339
    0x40602071e15060b0d0b190626060d230a0b0105130b03071401090f060302030603060f011a0903010605032506140d0c0e0915010329100c02031222 64
    0x10300171503901002156650300c0d03840c21510342c1c0c601d900c4544000c0040c044030645801000d404840505003000e44008402c100c0f190000c0322030300d800c5c054500100320b4140754000d55519100b0f0b0403c0031044140c200d46204000321542c080000d4852940b044c07413004501e41c10803060211603c0c259a01121031410826014110b8902050000907200894184682907200c50010707100403c07164000301d0400091000051810380c554061401020f040341078440d07545960341d201c0710302d9130280034880a5040c02008040b400c0c0114004101c6e440002c1c001081c400c0e900d00001e42412094003030741224010801c5200b0220a813840424044c00040c05c00c0185070a001c00700c4103990140d448404103807541c40f800381405138003454484034105030043c1500c10500d012510311401001c00004140881e0400e1001a1200c5a900c000356241d03413042e0006005003090b20030054200111010002400007605256015071024040f00c210942604415070790340965400d005007110307408007040c011007078000003484 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986224829 1250 986223579 986223599
    0xe101d150a1d0303121f1d16090305030f0d0b03010c0f1b0b06040c0201150f1a07080304020d08160c060e030610090e0c040e06150a0e04020108040602071e1506 70
    0x1e0464595202c54540c420f0340709511025000503004010390103103a5501490000c2040e038103502c00d400e81c0c41d0820f8a908c0d0544151a41c0b07015000c020b00c103400a02820710402d401801410039102c044c1404110301e2507180111742111002100200061407a032081040140c001041d8036a9464000040350750085d540c1316440c6044000d45140e2045440d80c40d48001c1900c05d40080c2c020300e0b2100c000980443e42c030070281c103082c00d05128400d60741890051010b0991a50300980b80082e80100d05140f4660b20b680c01c011f00094501c2d02216500c0c4103001001c44905080200c2280610509040380018144000030f0030300f01200400700e01c01c1e880081040200f80d1820441c03001c880c00c00740c0210364039400480d103d0900d04072500c00c40d006413600e032200c203030701030000b0750705000314a402d1140e6090910441841405401781c000d05c01d0b03444017040450010751103801b8007913020740601c40c01414209159a030f00c041070a02070105481d4060084064140600100148003c1d144080708109151030522004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986226079 1250 986224829 986224831
    0xf0507140c0622150f11130501030903030b09090a0510020901021e0a08072901050609010c020102120c0303010f06020307030903031202040b030f0406050a0510060c02060d15060e101d150a1d030312 86
    0x41e040ad6102e440c940200740c0645c001181110b0b005103c0a1140342000300d403542c542001609840ca44140c40317443d98801c080d442181d18400c41070703000d006100c00c0741400b07803000015054a010944a03a09a0802041110024103059481000b0346a850085202c011000c0c0010a0146400c0850b480c010001c40e0348603411039000c40c000707007420f940340784044c00180d0400761003104803001c61000103501c990740c0d10302200550585190486248046440348412a56809155002000700740c03003070320030f0000c80d00400500294a00f051005440c203074070341403850402d8109030307400003000c5401000d100410400c1c0c0500343e4003800120041060b46044040080000d00794410001070118012400c0103644a580464222403500e080500c0000300070f0540059000c1c4c3c85c490480003621400d809042803600c0c0c8041c11050405030341d030500340e02c080340c2802c412581603035180d68004010480740722064108070161030000c01ba81c40b044a2980803440307e10300b25244440c0c4500c2074104000c052a610b40020100b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986227329 1250 986226079 986226089
    0x60e03030324040b090703020702280e18010906091a0c090d050705043902031207031b02030c10060b0304030503060d05010f0507140c0622150f1113 65
    0xc080140d000c00100d07005001306512241c0081c0482c0420180701d0b0590014040d05209481d42101480d03440d008074100903000810842c4029800c1c010016502c0d4401c1441d040407054420b100341d001d0540c0d20908407200300008035149900d83c8521400c0c0309102c003604101c0424031040715007610300036103002d01c83e20900c94003c0c0700e141408a00000d01c001008070201501c3e002d041008462a451001c00800750360200100c0501c05100c158110040c1c0c0e40b41c155010440c503001181801440840480440c000901d800201075a80030311201100d10710b0b40c8504681030a0b00913640d078512008105042c0700c4074014031080c0340d04001c0d041040d01c204078100d03a84a42c00d8906242c40740c0b680c0000500741c0d1a2588054000d60810005507116400755000c94095600b0340c42d8288180000e003944041070040030820381403070704500d002421407a4000c040c04582d16441682d804100310b6a039840e00b00d460414860302085a0740c94240c2c0c0c03e0752482c45507240c038006e079503051804c0003400a1860004000c41c056 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986228579 1250 986227329 986227381
    0x8122802280203130906090e0d0215040201030e060a09060b010207060c080918102615040201141c18080a0e06040306090b04020f0604060c140a1209060e030303 70
    0x6104076a442401070390f400f030f800000212811540e821240c40500081d00508803070601e00805408a001c00040703c400326106034000d0302d80540400c44560040c80002c0080c1d041c5525150b0f000f000c084180141407040c0f005240c00142150360381892400c440001e0340b1541903500211003031000c0c40c0c00400d150603840e0700400841c0c0d1140f4a0000c42c0e080491042c2240d1180401418001500003c407070404c04d44013a0340014029000c64880c51034014048481d80c4640d81041c071aa450b0810556100c82d44180181000382c1400403031543c0210a92150030400790b03000304202e01102c1c01d4054010b42c0d0103142000c01700700c0323013078000c3d152220309200700c8940c03009002c00c4205c2a401c1d6100c200a90f001107070018020800e00c105c3d400d1110a112040341d0891090345080c1c00c0c20f06078500007050350705980c00fa95801240c10320650316031080e00030703402013502580b003080440b00c00660703031001d40c41c0342c150665943d072a89031520201814074416085128840e41007842000302e001010000070440d920040300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986229829 1250 986228579 986228647
    0xe030105060d020409080c030417191110022b0305102d0305070b040e0604050108070501270603090308130b0a09020d0f0605011e0308040b0708122802 66
    0x9009941d80c03044001f00d041074000802c0000e0325402951106144c11908002c2d1280465a04524109028003620051006089240325081410144031a2200c0300301401204c041000504455440340c81c071180820079014000615000329034140249070b007292100c42c0c8000194100091030711041042c07202c228051a4800d4060101c1d242203240300d00864120044d103042e40d403500800041c0368040d0107980801040c6d00040380300e03402c00b44034180c101c0d16603901074201141007600440f0401541c172501da2066604105181028941190041c01402c0307980b03000070003001c1840c002c0c0046400030601c1481003224183d000108400c4854031f42d110540c00c40c0041c03900b190b480064003981c0e04520160043c5000040d0301d007000030a901c4641641d078484800c0c484584104040e10503600a400001d10fa4441400104075501d0420050800b40c0d11070003a0f281080e0003445840001c010841d07007084001d1444409403000b11380c2038012104528807540039454050341090f00b0143c20002c42c08924800e210071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986231079 1250 986229829 986229833
    0x20f090a0f170f03070609030207180903030b09070e01030b030c0901080a0209060607030503041b03060e0706110f030d0f110f180f0906280902031902030402100c11060d05070e030105060d020409 85
    0x2b001c11400f1f03050605180c000c903140c4051283c01003071010004ca011034504040c0080c589088071984d03110b420560f6414100041d484011406024100d02c540d405102d02c00f01a1001c0da10b0350441400381000400400c1040f855004102c818400548158001e0030200101c2020070350003001c81e64002e130028105003a550b10040c070782d015042c2c50360028200b41c1c904100d260320300d140441c4030401c5a04545c0c80541501e04410420784803180351016802d15842045000d541c0300c030310f80280304a5090040005076001d2101d0611040703070b011402d010007a14000984880e9126000b62000c600c0b070003aa0701624489001d00443c42c00d0a02800307482c8a92801d5144280d00810703404903014203c0b103100c01c3d28009580c0c40815001c1d4000f0384080440710090a050240d5140368420f0368070a80d001032132030b0140340050350255100582e80c8010380d1020703d0004216219101c4100038552a03008900015051400b03580c004c14205940192034806e9041c5810700c030031036031041031510f40070750111400030b20b000e0340c0c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986232329 1250 986231079 986231083
    0xd0c080d0e030f0a120c14041e0e090f01050903030601050a12111204060f05100e042109060206061e0910080d120506030f1f1d030901080f19020f090a0f170f030706090302 75
    0x283e2b000d100710900003020010801004145000c08985510080c04075172200b410054407800103e484a00040f01400880c3e61580309610072034607403000e82000036410300301e020650381981c0a50380010002410106000c10000e05d440395094141340c1c04d02c100000d0800f00701c0920451503504c44c1c0502400454041418042060140720f0742d403003020004071b00e851090307101030f1482c1c0b0f8604c074950141c004d2200113074090034416240c450410052080503c40d00c6074000704a03c0c54070203400248002c01d4068081140541048080d075840c06070348810407190721001c03c00c0e00751140100114000d800a000d81e007540342000408482c00d0398058104090060a0030240006007052501c05860001070380903030040140200090247c1e90082c0e035030424079920205000c0a1400031382d2580106d00c055101070002c400240d014000c0c0e6010503913403528119105000800c0103056800022645400c42e00030080101c004c3d40344a0390255078000b4043c0c030602c40190645034003545074040c004545484e00e0504062003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986233579 1250 986232329 986232389
    0x31203180b060117040209041b0b030a0b040c020309030c060d0b1504090b010801080a020f04330f0317130b0a020f0d0c080d0e030f0a120c1404 63
    0x18880031a118100c040c00c2010640c40240e60740c03800704003008001184029005041c0344500d070003604c921542e490315500d0b6450b07041640c2100d402904240c0c030100d019000c2e0b1000398010224508017090103101c032410032088891411010040d544100129110360320702051000e0705640488242e9103070075103181c44070064005c00b10301a0348520040729080c078035400200a8000d07a1000a420492032a00f58019612040280074020b1503074801010b404c01464580341101c28140041e01c0800e02c201c105a0362214484040f25010051580d40c4040355882103041c03081000301980610305d0f60240c40d580b07644d280322502200d0407500120005401d080e00f0300d0f80b6241da009200d0680099903d05a040009441d07207200c0c44002101d000d000301d804c280c10301c150201c041d159040b9652a18104030007008400610403c0d079960317101d000c01d200c284c2c1114540c20103414003581540f0f03034481c0b445403000c03010201e48070134442c5803c0c4000010002a1421038209550a031101260302c002803081d02506000d103084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986234829 1250 986233579 986233601
    0x3030c1401020d021b010c080417070f0605011d0702061e0603161206060b040513150f080f0f070b070f03020109020406270b090a150e0702030a1103070c031203 70
    0x40001041205030b4000c501a103160b17008a4020450005401001c9034804026140504076002b070b0320f807100c45c2c2d800e40001414424442e04190580b50000d81e0760100b9901c09a0150034120414010319054030904a006a40801a071002e0122823601ea01085014244c1c0d101002c82e6211610005056840c104017007a607a00b00441c500d00f4195072603038030000000080c20111601810800c000a54042880030303501501e070000c0c603c0480000f0900300c20010020042c1c4101e0025002c04002103800c243c7d0440809440400c0140920305030002c5564a025901c04a01900364007034070082221a05480a580c5030741d600c5840d9000d10740803410100d01528100c0c04c06903119250510000304901c41c0313048a41e0710310b00068209075040f42c100c40c10b4101d0b1602c108444d000300643d0001507039011a90300402002d440402d44008482d140e5880005c851812030b011f00250b40001014889250414001149906003030001c600e4950b103541e50000c18003917480005d01c50b0b0b180c0800d0744010f0b1301079008810120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986236079 1250 986234829 986234831
    0x150c0611030709240309020d06110d1113030b06010512130c05030309010210020c01060906140a15021504030923041505091302030321011e03030c1401020d 68
    0x4020310445201680c0261007090100f030704108001416824800034881c050112941c80d20380c6840e00000303401420b03040c1e4003203030b000c90710040c80b4000800030311400942c02529a5160340340e48102114100710b494007003c2c0c0c1500324040c499542a00481d4034008252540140d1115260b00c03460300580303c07401540a0f4200c0b051004081107010010350402c1800980104d10042205588800b410b80300e210701c58070a40186c10108040d2a10144c2ea0000c0005c03d45c000d000007886952a41d0307103000c40301c4030b401c054080050910181c3c5d06207000500c0d04003070042c0c0c0300b80040351101c040b0b01968450301711920300703042d101035130001d0241409689000000c1c40300540141c15040144013401e080614104402d04c22071409010104645507030b0500c02c1655009810203e164071008854140401d02040407a03061004012010703030f02180700388660034062940b00c13000c00c1e54141038400d0a00608031418500641007800300b04046517004910000c019040504020080412610503019100e03215801e4481 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986237329 1250 986236079 986236091
    0x304120807020310150e090c0f0102160e040209060a051c02010528031b09180f060e0f090604021509010c0c081b04090201140a0203070615031101020a02030601150c06 73
    0x10240b070b400c17419800d10040b0000320100c0e118545d21101200688060340198003040300303258241801d00400c91040c405004984600d003207101641c408aa154000200c20701d124428041103080401844e90404000c8807000e040900b030802141c01095030312031090401034007410140039640200129a4810301c20071940c1e920320b048560140340c00b107101420b0400a40303001c0da56480d003510342031191460700c5140c0e80c503208a8074003150102030804000c0103074407143d9036140b2020303011307904d1042d000280b140b001d00610f0b924060015000602d0010948905a00101d04000042c1d0b2001e4071002d084180b0201c6503201c0c1d84040040758900281c00f0001c040c4080180040b825840001c1c2c0b4034030700c21006045140e01c1c10b03204103100503200c0c0e0f00e1340207020076400ca07520016005d0318409810002c0003403040ba820004281c6400054039044030f450300070500790140c180103000d40c50461a0701c2d05000e0008102c050100e901081e0364a50500c03403403506006e10141a208180701d0248116040c0d0002810720074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986238579 1250 986237329 986237353
    0x1c0b041401050c030415090b0c07080408012430050312040305190905181b0706090c12030e21061005010912260f0a1809020c03041208070203 62
    0x8654805e44007581c0117090280003d0180c01240200035045c2d512507050012625903100511081c2c12940301100c030b41c2005e11000c201c0c07500034480c9600320801260703013603100007104024000d203a90740e800501d480c08165102d0075003550f00348031511440e4000c0480401110040c00d160307045029810540a92101c860306102c00c0c103502501504d181900c01544500c25540207200382c0d050380e05803184a4100ca40001030300007604440b40303015400080141440c0c02c00c10000701403401e5521003d802c8035019034420310706090021520701d1364003a1824501c3c0042400c02610050f1a0311f001070034242c8550101c06404c6012036800e070000100d900c402c0c4c110340060904032002e1224001c0c90050a0000e07107441c900040b500112100c2202c0544c001c0061a207103501c0420545d6081d0424a9528407600200040742c403c1c03c00304000e04c2034510070744d250704401040d2001c0d140d03540c2c865032040c1081401400080c0207002e012040320102c070001540c5600900191408003030502442c10003a626001d1580200030b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986239829 1250 986238579 986238601
    0xa050103031d011704030306080f0601060201050109110912011506030f051e0718050616050c03030322151805060603031c0b010905030304080c03010b1c0b04140105 72
    0x2058a129441d5101e944004610041036000459180c50002d5031020140d61010154410260442c0c02413401003002a11540b185160000c454104d00e0b0f264845001005171990a200d201d024191840061064a64180600f00745000d03c028251203001c1c8110040410300b07096000c8401c84402c03503100c80d2010764030304001c0c00900040000040311414a800240d00c41d07659503521071081c50b00815141c00d9100c1000451701804540c0d01d0f80c02d92440c49a01052950b0352001510504400294200e105016490004d0804203402c00080c000d90003401800030006003c05078442580074540022078041c0d0a003013144c1d8a45142040d0000249002c40b25401000801d1440711010700a0301119016115801072643c1c07807048120900d807100048108000742c00b11504514410841498500c0c241d03911940005c0c01c40d445980000c000f03605c0701b24010741c1401d080c0940c20800d0812103e110024881c41510130880c3d190b00d500800003070140303000600b001811a0b4001140803982d0082045e4584140740c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986241079 1250 986239829 986239831
    0x605090c03010f060b070f050a08030a0c1704050c0d110d03020109120e01140307260a0e0313060305250504061704050a0809040e010504201008160311030a05 69
    0xd8001d50a06082030b207182c2c420701400d0308031a0f001144515140041e1a1140720300c944401c1260b80b8054400c9803404200c444c40a1800790719803050001e03441c0c031070f204050060109011425000e1a080d010840461004070700d004000c0700c19250484801e9681c0341050414402c03203080d9601070358401c079100038960b05500c51031f881403150340000088841440c0a0300c0c0c10116a5440c0e0009040340e00102030611114082c6420080c681400020401090464400c0c2502603131507801510301c00003040003041283c003492040b01440e03005145000d0b4032000d20601c0b0304480c0185c01c24151244003041f01e501e101100782d0a05844180c5180440300c3c81d07103000302164000d104800c00151140740b40c41e07001040c4164140543e900000421308a03a242d99200030350b80216004540c0180d43e103c00c51404030003030150f03500c42c601c00c6030301402c42140902ea030303284009900300050103149020b905510301504044000e4108a0040c40c80c0900240c8540c22805441c003d402036000728004000d0142c1c20f102c41d0015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986242329 1250 986241079 986241103
    0xd20072c0c120127092a05090c0304020109050d060501060f1e0c1511190503090303010918020a0803120117150a0617071508010f051c060509 62
    0x34a501e4144a004141c01841c03101c0742d0341010480100480700542c184100300384002000403950b001003101c140c0c100e5542c54800e41c1c9021001103d120462154560034a001262881c8242d1981c103040c04a084100c000344400c110400006c00300d401e5a0003441040000c1100400c8035a038078555161000c0a04028402c450102c0d03040c4000d000b13190b0160300c00004064094004244146048100316500304e4000801d41d000314a103020700d07a24511500800780b2181040000568903400c1050510703800c00c3d450009010007400b4002e01a600302d011003200c0c1115020140070800000d0300c0d81c2d1103040c1415042c000e610040301500000d1030080440900014061076604940680c4e03640d28540c030310040406d0001c00ca40040d8800146c541400c4142a040346a8200c0060103a85840360035a09080c501026070240d406003100b040400640b11880c2c8508982c0d103003006a40d450810301c60004c0e259030140b18810070020340e54145503128ac034550422960001d80c1072207030703061000800d51211400003032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986243579 1250 986242329 986242409
    0x20717070f0b06030a03050d0207111f081609170102121305011401051311161406010f180902011806031509020f030f07050d05010308090109080d2007 66
    0x1205440c0225400d0350701605907e50518050480121000a610425084410300c0320040301000545440307003110240300c0060314104440440c00c00260170b22500030814259040002d1181d07040c1580310801d5800c449402804442445100c5a02400b9028200c1c0b005151010b01d01005010015100402500c82c000d20003007090350701e0124040f4003483c3c24001d20703802a910b0301403030300092190f600c031160750400707170000b14100101e9002034074400d180c00c130041e909443d5000074100c0b900414403545004152031031040015034600a14841980e0000714008421942c6106400c00e40e40610b0555182c095041c6084c980140c032010090000d1131141c2d01d07000c3c4014000b80200e07e25406200f2a05442c4502842906681d9149644c940001005000508000060100401d2a0094050140078510401c20940c5916146d0300041488043c3c0d8400310356940200990790529410210400b80a103003c14010f001d1540c20309014545030b0550300c1085604400343c4030512000400c81c00b1a440a0000b80d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986244829 1250 986243579 986243581
    0x90607080a0503060913050631080c070e04170d18061b0527150a08070810180504030e10020106090b01021c0c0302070308031f05091504020717070f0b 66
    0x2281c0d1102e524000061188e4030480c045207240351140c018101c80740481421031441c9400c0e4039001a05048110121580480800e40800d0030038184441005052400701c03000076468103450f030a5013440401c2d442e1291440000e0038580f01c0050f80c1181c48126602d0760310f012800b40e0351600a00610030843d034a0015845550480c038440c1c4500b0132143c05815411104500b0504803000e0941a800d400540c2c0e440784680480c46d0003841141c02402c00e2091031f031240211031421003006800010b0003030400701100600c100600442d80c81e2000d12410380c901503400a81f0303907200e140640d07d0300d0b020800749070300c00c01c500b2186e42111b50540000d81900c10383d2605010217079400c0c006a03a44da01300070200802c1c42600011420040c800d0200700c01e680c0c000d05c100e602d580d41d66241c4003003a90050341c205800e00c0615880c1021044021500f0009200989003034032a4030300304400585c00d070211103003a8880c0d40c00142c1c041c103004c841d030b0034400a10704200155944000300d103404419400da090086400c921220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986246079 1250 986244829 986244841
    0x92206060203040b091e09070203030108160510120905030408100605150702120319031a010804050316030c05070602010c20070b070521031f05060708090607080a05030609 75
    0x2c000d450840c3c400f209258100030240702081031040c042c2040084a0040080340d001d182d5a0300001802040150042c41e0750b541003151321030514007100b80b0440c000400315810000f94944010100851150b0b01c1e03c0490400780310041000b8244844000c0c4c128400403a002c66580408503200c2c903960103110040005941c1d500a001d00d5050641550f074820005210b01c50140c2071510081014002403402d5910b03111410b011124180c1482d400c10303001940c0c03200710303a1814030307816001240c455003400e02480b45c1c6407a41c1c60f00d640303100c0c2101010340c2e00688802c820070140030312401455070741d0100541c3c43c05921050024024030105e00b40c040015180001a1017000340300160344030380c400b0a409000706a007421040c440c01c1c0d00c8100100c03960312805008429140c0b441d40c0c082510107540d17400a0340c7c2d04021072000da01c002d0702813001141e49003040e0304201940d6007030110b4000c103910803240350f02c0d403500b000003812034000d00c20041c1007883c0c0020609004c80c1d20200462058108856542c0c85454070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986247329 1250 986246079 986246083
    0x6050a030b0d12050304020307030605101d090607030c0207030209010b0c1e030306013e1e06040b1003050f0c13060803030417040b0706050f0105151b030922060602 72
    0x202070300c0300f00049550b00c5014031503402144d0060000d812a0300156695480c0380407940b0403980c800f03100346200d8007030141e100b4400c188c601cac03828175004140c640d0038015a5240c41e060b01400071028190360b0508881180d000b07001c0d4000558005141110300d41e925024600140e02c05801c44046005000c40b200004548503110300e00110220010760a503545c040064813070344081100007103001c190700b1100c940b648440582d80001d5284510301c00c900440b160116190418081d40e1404030f0070310580ba02c04203000050929031194024580032800e032604182c0031044011034102402a00514048c600c50f5080054800341e1203100341ea1400000c8500e0b090a422a400c44c02030f40d85070b070405c0020402040d00c600000c5c00b103800000f06107150179668856804150700900084400a844004205018400244860050105550b40c45001b94010b40007080c500c100c030301c03041c84170000340d5518104006c1041079415003000609841804003214403080758403451070030f42050711400d01401041a501c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986248579 1250 986247329 986247349
    0x50408010506060c15091903021f1a0103110d02040e1e0103080a0309020111070f09110408030712110a240c050306040b0105160809120a0209060402160c06050a030b 72
    0x4c50009052400318224000d40b07404400341c506189445480da9041d000e001f495084440039200360014245140c1103504038000050300d48000e4501840c00301c01c202110b2040c161071034103020034a0000341d00842d89142070040e0080e0700c40d4104641c80480c000c111aa04182041d0040c1c11610b81d10a01c8000b1442000030550240802446250180a000f0516000f50450301401d40705041240000e02445103081c0703006155807001100381d1224804120b00b103058840c0f5550310300801e00369072909040c40c400656070321400c5001080c121000614034080e501c60346e840c036251880c04050b250001d41c503040810740446046200b14800400d070606c0012145c481c0708680360014180c176101c0c21070f540c6c1020000240900409641441010400350341e120140d20600388410b44140e9000b9111140070050042d2550f20400d2804a640310035165005a42c0700c1032420b900100403280541e4460491040c6d0071014501040100700b04c4074020080b810507041005041109400da6040112000030401c000c07001c16 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986249829 1250 986248579 986248597
    0xe09010b0a0608131b0f08071520030d020403032006010b0a05130b0705010b0303070b01030f061b02060a0507030c27170f060c1809060a0b0a05040801050606 69
    0x215890100705450080351030300c2c2d0204107039000b081d44500785c1d1660807200018205e42d424500070140144414080c12a2042c00741c001d10000785101400d20200c42d60394511104030314103100a404200d42000c405490160140e15a038069035141c3c80b580e40c1640107504107020441c041b86003007008806c05032000148038032240500c1c00070001030f40b074070b2415041940400040030130007a00704400502c283c0c800c96200300034809460047c1d51180f0a084ca6402c40b06036484591183d08208086400f25030100172090542e60016940d03224030310f031440c10358010001d400c440c076200c00c1000754203144c1c1c0f40c004c42d0301c03841503213103000c241328581ea2028100c040b1004a100c0340f0100e10404c00c1c0c4048444000c404ca40b4081007913910700050740e12200c103d00204088103081249600021650782000c0d41170040a03000030502c2c00f40390030a942c10003044881c3c214032500d58014000392002424030780d6580860070041c0341c5250b00c0c980c0c440742b0310310080c003540c85401100d10350343c00e000105020b420024120b0b81011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986251079 1250 986249829 986249839
    0x3060209040b01050c1509030f07050f070b040605180123030f090303190b240318060123010921060506150906030703060f0902070506061f0e0414040c0e09010b 70
    0x11b4030a01c00000000024004454911040c0505882401d4003c01040114060402040c20110040c2c01529124541e00400c01c044c0c4107100c1001242e802c0b4090710b00e5010658015900024060700489400d6260740c1110002084000c1001646604030020350207000401c140c05010340c0d0f05140da80c2c0d61710080e05c905448c40c406000c0081180074540c07044200900040c1600c10800c0d000806000488040c9844c50111900005001e80141c0426001c0c90711071003180038021943c9024404411591660071140030001c103c2c0784020a82e100702034402c05040076540079443c0d90b690302224416159004400c60789586003402040d030a14040118022500c1e0f10300e03c1600e4444c500c4c0c107000d020b40001d403018060544590700070a0354040c01248034041d010101d001030301c0304440d0501c40d1415001030b0055025801c0301d110180120900808a55091402e0501041580501011a0041140100c0c00d13a51040020030301c002c120b1702030b1540b0100c0350709040c40c40d026280c0c548000e00325582c18144c0c0d40e001d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986252329 1250 986251079 986251093
    0x150d020603130609020904030525030f2d02030a0905030c063004030201050402040f0c2003040b0c07080d0504270605221805061b1303060209040b01050c 67
    0x80c0b214074108505503102d003038046079031300d02d84e4082640e02d8010b5608a0103e02c0210b10141441c003044030a405041072807512000c01107942e10f01a007010003100155041100a29181d02c0e26034600c10040c90301782e11003021101a198246009440390440341001c0c000503503c01d0006000c0c0f1700043c581000300d00c014040d51400c1c2810340508840201c180c60308015010310003070801a1520340c111a803043d4040d80011451b450035204100c00c0b078016800500074240b50085103100e09502003040442c40001e076003c60100402803e40710701e107019070b03402005400000100e645559502082c0300d4220307047c40c0d04991040c6032040043d90b040c02580141d0a00c014a00d00c201d040035607040c10460311801000c4000b4600e03403124049484ca102440020b01b80e0841da1006d04241a0984034851185184250072a40800e1030b0ba16a40c03a00005802500402d0074400b55202e5000103400311007155070040562184180c0d0b82c608940a5000348154521840c0741a4841c0400e50044003142c4c40700003024068401b03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986253579 1250 986252329 986252341
    0x504060b040e0414030408071a0f070204240308040f0e0c19030b0901060c050d020607020a0f020f0904140c040606140307020c041109030105010816061b06060905150d020603 76
    0x42e00c00000e00584132100700c142d0384441240c3c244000c0020345284006440c1c52801d200c814100c0b4103e545e40403807071000c10004884080f20f02d6003904c00342e41c0d04845c04942c0240300d540c42ca00919840444000d00081c030940001000031207070003481103400444412910981c0d9001d40585000c0445689080400c02c01c2040c9503528156043d44421800b42000285880f254012403582d5900f40c00c1140800e000e56010003d10104112115030908184020301c1c46180030301000f5100d02c1510402019806051740f034400315601d640507444120b10240c02d8041d240340c10308080c90202c0c0e81700860082d9029034094a803c81c2083d001e00f5017541d6132078913450480c8108070358003034490b03000902110840c02114000c42d0f00d80e545004440e030b8403070306000458407400381b18101421650107901c41c508070b50008642c13070041410107201208540c0181800e0000b02d80941c80c40d0f244d10325000000b4180c1e464201c0229809550350302041c00f642101500650011090302400041c00e980d2070060750001040c00010a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986254829 1250 986253579 986253599
    0x1030209011518150e0f0f0d0f140c0108100302062a0a061a030a0c170f060a0203041e0c170c040e0106080d05031b0708070f0303060e010504060b04 65
    0x94412654030306403e144911981090424080b0b0708100b07200c2141d51a0760511541c0322840910040c03040314600b851000c0580004c00d14030320551103034010100c69030800c0602070300341c0500e1812a04424150001c4240b803020940b14070751002802e0105100401040040001d000400180d031340c0504034524011841e0702e00d0468051400101c4130114404100222500c024800001203911406000c51001802d040c0300c80da803941d031051640254001c0c0c41600204800000c00000c50310000220100e4080e0407031000d0400700d818101c100c0130700c18081882030045482e0b0085205a0040c0030003d500d807001d201d9020620004040648100400c650901a00c1d044000803400e6007003603001c980b250f40740740001c40c00f90f8210408991941e5562103042103a032209100c2a135803e1010702d80b0601c0c525040030305080103a078400c44840038001c0482c4440c10000300100b1030b40196088446c01090003c0780c076008014022900808142190800c00000c8509243c05407805aa0440c0340032030603d4104202c043d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986256079 1250 986254829 986254859
    0x715180b010b0f041d041202030c060c1602101805060405060910033306080601140f09040921111005041e12020607090b030106050912070603020a020f060103020901 72
    0x41004410080060000b030800d8496070071803142410000c0c0d0f4601407c20ba030041030100240d1003950010411402d140101140c920b6000040d0501541c4904403444250140300c0e20300c80007500720031820140c0540a4102d8411080040d008403024016600ca805129150084e8400d80360040014800001240b40072001e015001c0a207280018510b0300d518986101140c0900d034080c40c1c1c1c54070000a000d869212540100070348410300b040007103400c00c440028010500551034641c0302c040400c1410719120980e04480b010040100306208496250400c86038400d10744201100001444c40b011002c14003030203000510100c01e5010b0810300d200042c240024000c010800c132065494410007130b03900721895440d5403505024075030b0f000d80c1001c0e0013030291910710054170040600c07007400c0c010001c102c51201101e064443c00d182032a1078240c2c0001050312001100f032401014080e4503004102c0560503400b400605a6680c03c81ea6401d034403c4c100c0e03403110020301002c0d40005800005100c4c0140c002029 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986257329 1250 986256079 986256097
    0xe06030705160b0c070201031d060c181009060f02010504021c1106030703060503070f0f1502030c010f020d0c1130030420061903051801020715180b010b 67
    0x100d00b044040da0341c50710701c000102e405000e0710101241c0c100565034940301d80c0e01c04c071080c42031201c480c07038100d81c1140e80c07003000034001c2070340c010001903040000600055800390010060300c00c0d00d00000c0107102a0032900e441c003903007001803110b00806070101c0c41401840d00440c0c000d070501d10701d1050b1214811142c01e07076a10070b03503c030088244e540070300e0b880384801103104003016a0005001400c00c8101400d005040e4031102160448200903c12019000030100071a1294a480200742d03008620070303070031030080141100700c9510b030103d090010075a680043c0050710721030380304202926001d06e040d00c0a60130129004035551204030101403211000c04070f410804000040c4058554201e01c450002d680205c0d011540c001450038080d00036030074404605a205400c841c0142030142c10701c0c1208018287c40d01d41c408060f00c840c04034004183c1d105100291044080080d9a210302604008070f000704c0030031500300c00902d090300a5660801c4200210030f400da110610014a928100c10b80c11039030458041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986258579 1250 986257329 986257357
    0x50d060803040909020901080307080d090c0e090618070b0d0e0102120c071e0317070e0a0e180c090103150609020a0c12021b090423030301030c060e06030705 69
    0x404035011030100080d100410b04842d0110b0002000d1042c13046540b41a88110241e501c1032140d440011480c406a0700e40c005491710014200b0003034240044425510f622104481340c074441480310a22000c200741d4410300c440025000d42440c0751041640d52030f098801c1850a000501c000d1500c0e00443c2c100103c0354045400140c2042d0504040c0482480c1c240e41d91482e09400007036050411412902180901840c84081071803004c417610050030004085a88048001c15000046c1c0d04c1e034050388444508009c082e1128103034544490741e003209407009880100c3c06072000040d52a9100c000101d07110241c0b0003808100040e482d5642e400101c4a4001c00d001c0703a203846080c04241c00b5001d01c06001c3e412160f03a00d44282e5845030604039001082500c0c09011034010410341180000360b01003000100c04141c1c6d88030703400e07038950900e5126001a80201302440c3c5440c103661444c148001702442c1030324040d014828402d60360f05d505031140900c118810760841d0341480040c0b4082e00441c050000f82c842420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986259829 1250 986258579 986258591
    0x5030601150c1106211605040b0c0708010c2006060303040314030f34170d110a08010807090507170408120702100605090421090e100518060a06050d 65
    0x560315812503000b103595103450610041103040400c480e06d0700500100c0400d14400c0b03041000a10a1140780140c115042c4006840080720034100039990042504c0802001920603c0a0003010005890105c103010320501000c0c0c1c0f0102d0010030340d24001d1200800841c0341a107160340380110068440015000c50009001306075403d1a40c20043c40d0003030708a0341204c1c0248500d02d14175100d296560406000090f66040c050006104800d0605903903065003000740c46080d40155039001c0d1541d16550f03e45400c000c54140740c000d40002000c0e040e17958070801d45003070076120307140c500c121201102c4a100107010000740320f02518142000f15001400703080a01e140c8510064a04500c03c0b0603141100168090301c03552004145501c0361a014150403103c84601d41000e468240805455202110003031541400c41285107002d180c5207001402a044040442e00d01a000041391811a10407140900d209440002007600340e65041c41c46600002d10051030350b03007000c40444142d00a800f41c05c040c650703502 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986261079 1250 986259829 986259863
    0xb181e09060109150804060f091505060607080c0106050333131406060405090109030207050f01030902130b030c010504050d032106091b050a0801030b06030c0405070309020a05030601150c 82
    0x1c41e1190380b440713039407505010307410b003490150129071183d86200c807a10f1070460b10200068803071354411456050150041400c2d12080c0010348284030300c2000419594000401400e0a481900900300700c2e00101c0544404001485031401c40310700e2440b000741c8028440101504148551a4058100a03091580d030003e9400f036803814210521300e100b0741a0340d880081040754a00d803078066290f02001c11030003402524815039010b1766503516809040d10403407080d0100d00c81c3d42d200381e0210321744580040944501100755605c0500400e464007001c1c3c080d0103080c0340c8010a50003841100c08507180070301132551b08001a1000c54074440351036400c0582c00903da812941c65900d40c041d0324040e00b411200020b01c0400c80046a81c80812170000c2d505200c428002404900d82010886044035046802c0c00e1840d52040700007400e00e04480305103039016141400b4810320039403603030141d10001c1c0f00703031941c01d442626041015035440091050400b110106103103104041d201d1800181d00500c65004001c100d007080e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986262329 1250 986261079 986261099
    0x10180f0309030803090606030609070f0b0306030a02150a1403060a0509040f060f0c0e0405040809130204030503030106090303111203061002010f0e06040c0b130605071406010b181e09060109 83
    0xe6490b481c0703d1b40244180000d80c5414000240c00004650040c10454901100704806204a1240c41d028142c04400100540c609018034440305d81e00910803e18808402c901d01c0c2030345c00843d811000504101c400032200199401228011480202140e00389454901001410a40104111594003c0c0c040c02d000203202d40c0501c0c6101d402d410b40c00b040c5507100d40c40042000c141440f26034412800c0c201880301003010b810885100403002c2c1e8846c80cbc50014182150007900c00c541c0000c0240c0310010000070466440180c2c54152840380d9181c240c0c0c40c8400501a988107110580c00300000010001300d0907524110916180c50800f070300011031042581c440d00d40407030f40003030840c10f12508140b0802040081c1304000340050701c883c90383c59041a600b28901004601c01c0d029503010311000003004818004071a01c500e20f24400d490468480e5030b11084000060342024440c04808844c3c1c003c414014681103070202e40d03041001189030b800702c0b07440c1c003005086000500800e05010525001285a80c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986263579 1250 986262329 986262331
    0x3050703080c1608070501120b0a090506120a0317010504020a08150109031505040302061e011208041509050f031b13061d06010e090702100f110a090810180f0309030803 74
    0xb079480500031745403516002400381c01314800c1d20448289070050503190303961400c105109a0340368a0000420f992070f070300805c0720110040c4101d039151145510a604055004100200c40817000c101300001e41d13a100c041c072050380980b8100c200403c1c0600300064018680030050b0480c01030525203202856941d44555142c92501c0390340441c03440e1650104424190100107094000220f04007902840105003c074800958043c010049040358030500881445158001c0e14041c02e950304900e11045e0f030040d40503254503010b108603030154100d01070500e141d02c2c0210722001c1d0000b040500800c40c0266804011b004021080c40040381a55041c001c00c11a681c00380c801d98507c2c01c981030240c10f0800318009041c45100c01105880765243ea020441019408071b000402004803180100f0071701d900d401d820010b08400420440d5400001c640e404803503074005024030880b0070703110540c1c0769220401d503401c01341c0381c03501042c20310940800f140703000260113030340091041d40c0240352106400340c595940304900d603c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986264829 1250 986263579 986263589
    0x712080f37060f060c05071203140c060f01091e110f0307021f0b0112090c1e1a03220f0c03062a270b03040b100e0103050703080c16 58
    0x2a50302d6040c0580c103541a80c5801400a505103003096624a940e555030710102030291070b52001070842c0900415006003103211940b040084116282c108403501d003955150304617003205900881d000002041c0c0c142c2e00c20b121020b5440d20098400600003450b50303020341010034a5135801c1008019000f00e100c08403028500450741035014008030b00c51203607000b40f030010034420010040d1804021036020fa0f004170f03032240f803054034020100e4508060b0901d5420003090794010a01014140c20700f480c40c1444007104010b8462025982070b0349516010010983d0004562441000409002c0f103d54881264139121140d17106d0700680140104030780d6651354100c0d4540c000c8950b1900c5000c114035242001d1103c20024500035405108500c1d113280003442141d0504103064040e0359030050000f004904030300320000d80007a200701c0b0703540d08182c80c00f220394042c200c0741014044481d00011840ea180715000f00d04a80e04900240520fa00355200c0c101260320041110301c1c0b905c00c486022030b058414a02401c002d00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986266079 1250 986264829 986264831
    0x18070909021908061f0b03070c02060c1e15010302030604020f19090209120a0b041e08031302040c08010b03270f100c0c021318170712080f37 62
    0x818110341d0100f05e070360483d046800705990401e0500401441800742c0703a000383d9914014038010b0381d03400415150b11490703200b41418080c043e640c0540c006180c02032290800a081203a40c0c1620456600d8120030b02808020b51681000c80402c0151411101041001d400280081d203401c3e0301d071806110800080d4840304241c0d802003412180c0f40f0301000b81c0e03810884c0c60005480c12540954aa1100c204001d00050105481e0409850304c0703e07000300c401030060391010707100b43e40e41001c41401c05054982c0d5000c034841d070308000110403c203200741074407030480d600000b105003940c440b8021240d0210301040459135058460480158600702000940010307903850015090608441d12200280c48207210104107210304661210016150071440324082d1a10950000d089980c1400c07400a50b21015030292518420780021b411901a150007000041d2251001c0c420700450840c007603440c5582100d04003034405c11280050172400c480100e00d01d05441c0c0032422502843d01c410440f80c00030180401d58142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986267329 1250 986266079 986266081
    0x40623150a092c180c15030a0e01090b0711190807050f060c0702010c080921010c030b0d0b060414010906030c1208040303180b0d0203060102061807090902190806 71
    0x2c03226092140180d800944a041ca0100d8502c445940b4020b0150071000131014a044030f8803540000d0100c600e862400030200f010725540030710260403580007a10b2200100e440d00c1007401d8440014890201d40c681e025181c3c1d0306560b42d050301500c030700202d0081c022642c081c042d01842c802e98030740c0408650078407442c0e0280e1119101d05110b490100120164080703a4030482c11301c00c80354108005c0e40c0c03890f9424070b041050b150301403803c0050b80c003841c1c0d402c64110500d03013116048171921b5420210b4404c961002080040c0307582c2c00c1102650f5010740000e8000b015001070b900030511060000d0340c00203001d00081001e07107042d0032420030920701744e0015040360b40d070700414810414004240380041030300303038180308421602d5214803840c0e00c40c0b884020280710082003415044d55090108170300416080b0800341e240c480c0c0100001c040d500842c5c0c0c4131700600460f40007070010301071506e4007102141c40500400640f0f0600b60032900824070b40c40140d03031081807501551522440002103038050f210090141c912 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986268579 1250 986267329 986267339
    0x40b04030b01170c01091e0315060303021b060a0806040b030607051b070b0307032403030509010f020d090b03150d120e0907020d0e0a091d0c040623150a09 68
    0x30b122000d00e00c0003101d130004a040c2c500750384c0c0080003c00744c2d5807020399410b0011803603812101944d155803005080c180442030501000c01640e203c0f0088900a409552105503260111084040c8400301641d21000620580c1d04051248032a00d07403102e406400041d4040b120390010b8940070741204c80f05c0003e48001201405900c40c84600300c4480f80c1c20000f00006c40c109000b103e401d0100a103940e0070190f84035425070b05002c1c4623950f06045010101d041e054146c0b2401e000b4030341c0d80040790081c041600d02480441d12172000034042e448001d9940c94030f118508020810340560310140080ea02065180c0001966a441a60000e4841c0c8544444a002c488005015003a030000741413540c8240031000401c4071454010404a2086045142c1503101c84011000107200c1d5500745c10020310140b4155828880b40d440401814014440304101e41540c24158100010b48034103014942169a0021004000b0740c00400c8003200078070000c0000381f182e90400d44d00f42c40c5800a440080001d6121001080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986269829 1250 986268579 986268599
    0x3020a080c090a050c0702193212010f02040e1f051804170c0303040302010b15040506090d1b060f0305041e05120c160b181302040b04030b01 62
    0x802800000081c00000e0888030006814901c01807000083c541c440e000640b2402c2000e08580f04582c0c02420151251034001c6800620b0602c3d01661500304a00110011148500e4010104d6010312303070121580044502e060021201b0002c0c4440001d41d2039216030702d0030348010300180024103144d441c0c0d0703074031464184142e01d40e416101c0c105107030030744036440180304640f18108116802d01c80351407075038803640707403031a01e080d02c044c1c803860384c41c640d04006c210481c210b48044021401356000f0350080c040a8410003c0000c140d0703540c001d100b1121020482000b050401d1800782806140c020324014481c038090311003a00300802250303030300b00c46030091800703000030342e000514881d22a205140400c01442d1507070720039400e690001005840080300c07031840d1080000802508541c51000d0b80601e0b25400060715296480c4048014614020506000492001003c6050f80d10710b9111504a4060060001c1030082141a0799039190100c0d03020803020070b0620601c0d000f8801144112008490341d850150500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986271079 1250 986269829 986269849
    0xa080307051e0306010225121101080906070801091e0501060504061403070539010b03011d03030103060b013c0c051b0418060518161e1d010302 63
    0x40e02c1c800090080c003121740d0b40050b9000c80242042804c001d62030908044090b40c03080d0744d00481035499100700000c104001110b0030f022041d400e0701c43c441141c860303c6d2030365150390302101d0190004401c40c00422081c41c09801c00c50130340c581d1801240014400241c040d05440307090b088140440c81c0082d0822007176038401d5507500c542c60099461425420b0100c0020028880c2146000400344107041c940e02074030004c10510700c03e00c44070704502005042c90062901910007603488500c40e52801180e200b00c1c440d1211021440c10340300004d98616030031540c42c1402004564806810441c090700c040015020066814840001c211800400c0072010400850085e4107603a00741d00700602e0080700c0002038000100c0103013440d103881900902405183c041001030504601d044941d4210041300020f110791588600d005a010801c460001c21921003a590749030003c08041c003011040a8081240300079100900d60082c00e03080c0e00982180d0780f94900075686403921340c10784440c0c0c1d001e070041003117182c4035002c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986272329 1250 986271079 986271127
    0xf050a0203030a09060b0301020d060e06220207050109080a080a0c03060b120a0f11040302030d0e2107230909010e100b0607051f05070e0a15020a08030705 68
    0x54901240000025103070b0201800305240f4544034070003c001c0020f190040c0101b0107000c1c000315119510110f592020b440346105804a9071200c0001c5800f6007804640c450940c0e440b02c1301c0036000c90b00740b9186c4d030085d44000d000362241d551b521140b030300040101c40145003840da00d40d680c070038600f8244000f4044803c40c11045061500d855010080507800740c00381d600c000700d030510400c81907940a11980c05401d11100c60010a486c0441d04a003400c0140c0c05403040d0307402602200d2084218a00c29103001d52640c9440303a00803404449410b4441140a07401207401000d41503400c8103a443d0448610b1401c10481e210210440c05035924282c1854840fa55000c0c1c40c100007407046001030110561220b00c1450000000ca8071001000520b8582c00308403881d150340310084078100100880030b10401c01120908005003420a00400c45051180420041401009085051803480c012030713040c140c221414076900354003561503110003103090040614451400c41d280c039640c0340c1c4281c0c41d000c0380274118504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986273579 1250 986272329 986272337
    0x3140a0b0106170403120f021323090c1305031204090510050604060509030f0f010618090b0f060f042912151305010603050c0f0d03301b0f 61
    0x32003850400d20f40003031074002e034250501c0d1458071680c1d0004005804450306900c005400001d007001f40704d0381032102604845200810400c10300c4140e00c50400c101c22200301950200b6000007040d109401d001c002c191105880c40312041e5550344002107414042e40081080c268080418100f284003080d000d00c55000074442c0c0c0c988040ea00304400100300e4051805050100040803075990300580701007103500101000e08040351202020902881e0181602d8081c0ea0307070b2092210b2072002d00d0b4240d0b0103603400c4264005a5a0443e41da0300342040c0105100170311542d408800c03d403400c019070311144105014140700310010203402c400b4003211030104910001043c05900105101c1c1d041400c003040602010440300300a6003152500c2580340b0140e0003040010303009500e8640000100900015000035024040c1c5240070f003440640204265039400041c0a40440c0c0c01e0340c10320000300610541580484803d5403600b45482c0fa2110307002c00c66140301c031080c06520340014554841074010344c1710a442001f07450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986274829 1250 986273579 986273597
    0x10806190c18031401110708040e06041416111501150c0b01090b0a0906030b0f2502010f0e03031e270c0f04023103140a0b0106 56
    0x10902050240040008069940d003405071180351003124015010300305801919089612400c02201c461954180c1420640c42d0107280c1d03040e00110400c1c0c9540c2500102c546d414146050003a40303503d0802481d0652103940c032100d01d90450804108540030b50b0101d184145540016840601003103680e44101c01719511005419041000b5440d40505440c030220340d80d44128400c24060700c85502c1c0b4000140890104800450494500c0d03120b102d25a0040701c0101b02155980100000c90348540800351642d82c2840000c0c10410000388096008401c4844131301e0490f0b601000e03c8031404e20710b10000010b035141d50b4159640500e03070080340f0744001110065403a60030800300c15501500d0610001400c0c6000100060040403008031110501100810850a009108107016201c841c140c24480c8a8451034031010a2401c081c802e07140c105440c0c5200050445200c81070016000c02c0b000000c0e5490a103550100000c0e4004c0700304501501c0c50001400841c91524002c1c01d1200160050400c11440391 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986276079 1250 986274829 986274841
    0x10e0114060a170a0602070302031e03010b070602131a0403110402030f160302070b010608070f030c0e1504051005300114030307020301051603110336070f030b010806 73
    0x1180d508a60816201100603005070340b500d0300b041d44c0040c0180841344082600001d154010000b400511401d0a80d900608040c3c0c080d00710501003805401d4a0b01d005001c0030001610a5008112031040681703100c0755a5031300c08411000340c10503041e140b04c0001c042401c03c20404c03e505202030340002220298107510307181400809030b001c010100310721141041048094103000782e044401458018141c140d056031030354000380042200380d484c280011090340b03007100c0c124803d200710110001542c7c2c410315207500140404c61084130884501032121010040003680d42c0e03445001c4c1c00981180d0701c44030f0b2100001c03015200c41181c1d40000301c5a0421074070055000741580c0c0c80b42c0d41580e4200c1c406140c056001008070b0f28500484c13034025055803070403003030081004099000202c03400e00c03640d091002110003a1070f51813900042e604805100c03010303000304400016840300d2003481c5090b807000b007103402003604849181c00f150754004194022400003e00038440612100c0c0c0c0035140590081c11181803030303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986277329 1250 986276079 986276089
    0x9020118081b0306130620040f03020a0503010e07151808010b0f100807081005130b090c0c0a0b040512030a061503050c073008061c0201140a090f08010e011406 70
    0x4842c028481a42c501103001c50505804001c40207c2030a070720386455a896161400340b524090005a10445140d100003e803480c05024007801c00780b0900160a1251425103455103048514040f0030500140111222401740f003080c4100c014608140080b900490040c10710025199003d0458080c0040381b084d0381e5103582110043e500316000d807030020301c0e6940c0c04800500c0c5030b000707402c00340e80148819201c10a400042c0c02040b00740c141141d100500d07440c0c00c0c44184175403244800c5210380d900040e040c100030400c51101c1c10303413040c011410340e000c1150304110001913600480c0c9607401d990307541c8001d1040e0407104c10030040400d8141810015810454100503181c080d00707000030020000070350340402d007560010790056100340d203200010494008241c081d22050046130418010070f01c41c0780c06c290005001c070014003003030f806071101c42d8000c120452528465202045120a004030b1100c0003c8644070003480d0402031000c40000201c8054403810303142911904540020f01c0b00d0341c44148940755542d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986278579 1250 986277329 986277361
    0xf1602091f03080d11040e040b0c0c0d051b0601031410110405040209040b040c0f1103070309060f0201090b040f0506090705150d181a010f0b0a0309020118081b0306 72
    0x410f00c1501c80312480306a4018244103102d64420840100c1c0c0002c1d041b50606c0c1c1c160156102e00d03802c02c407279a5840c500b1412400745081c48040c5074004410815064064801400000070001c400320030f0000c2064a14600002030341300300c030844440c11041d1b2070f091051043c1c6441c3e44403250140400c8001d190f940700d480c01b4600606210303590008030300350319550300d60200743d04003000b80091160340708241d409003042d207140040b0004500080e081c104404404000c5411450340350300c50060050a00108965070031011514200303540d41e800c1c9080c00309459130a054420791040c200010b481e80346141c2241041c001600300d09450b44508001e00c841c0d5112200d0484080803405850744a100003500503000c4e2500b01340f103645041b98000d02c5424814a80851041340e541039007100000e1341d99a0b0210f864040c14440c0600c1c416045c00401c025038482d030410100d8a00501d001a000c110090184440e6500340e03020856592100c001e081140000d0300d0710f4042c1350300c110003800381c518113034520480842c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986279829 1250 986278579 986278583
    0x20c060d180203010f2c280b040506060f04020702091b0d0608010515090420180703050405070501030908030a150e041407091109040b01050f1602091f03 67
    0x81c4401c0801c03241c4046034540c4000e150014000d000007080c4181040c010400e40d680c054207026100c1d0545840c680300c050611b9241a0480105042d040c070101c2d641111521140c0d00381090822404280480c0124a2450095003d0703c041c02e228103024007004174680d1954200c0b8002c9006000020140e9950300e1041d0344502c402e002056820461012201507100e00030b510302406142490120309001c0543c8030600c9001c1c1003100116000041c81007081425048400409401c180c50803440c0214459003251a0010041e0111b1014021403114400c0d40303030210348004c002a601c10801080c4882045400700509007800e04004030781007522a440b40d807200410f401100d50b2034503000c00315070700c544141300c000b0500381d04085068285441c040071040030040207001d05210b0000e01040c2c5440c140b003082500c4103c2d1007807910b0090410103100180003110840ca043c0a018002844c84201d010014800b1068001583d10b4098281c030401210400c00b03030910040e002c0491080d04c2d140c1a000080c2c3c290783e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 986281079 1250 986279829 986279831
    0x712110f1f090806090f03031302040609020a08040303110c070608060a030c0f081507051b010b10091e0b0a050c0a0c0b0a0f080601050f0705010f020f09010f020c060d 73
    0x2403034240031448804595403129103403512140700c0d40c10381d5031051107036080c1e40324081544c030240c80d005a403982d18101d140a40685410410101e0000c03862100d100180301d201400118071183d8070807807041203811481150740840d40d008100402c059041c862294100300301c1c3c2810b810800d013840c04c1a03542581d4040c0400f0f0000705004270724160f4076844128004d5a024000450080d161071803e04008058810007040b80714104605c422880304080403440b4980560300c036030403d04400b542802d55914041d00c0c4031107568580c9003a089440700400f12a1074411a11107400c483d01d0003103100341403040780485c021000c1540030b0921103c94500110340d0011401d10307105480e00c520258803400c00c00c100000504201000c88000760840303c480182010450640302c038481c9000784102a105100300310780d00c2c0d000440400070111644016005052014054000006d050301c00480d81e008980c4140300c0c42e4241c1902244400c00d96034445122074581c501d0344080e2004010250105495019001c1c00380d02107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 986282329 1250 986281079 986281099
    0x7080c0d030e030601090b030f01061508040201170f1602010207020901030f15060303080f0a0912081807080f0c03161215050406061e03080316020c1809071211 70
    0x105124010b1400c9400008081c3c8001c2d5940303001d0000280a540b21840c00707401200301c41c0d050140184514001c49107050b902c0c0c1c829844c1c0c41d0040300c480300000d2040341800324ad14480031549a04462561207400201e04d00701090401094440802c20040b4002c011a030042108030300680300e15415604480c2e0003a07440c046185140380c5413401540a002d400001c52500200005040e8081072107801032050f4105081e00d41c0711100c0c140c0c155a440103000d0a00010500029205031040c1d00c400c0d8000c940c81400c0c1e6004c1c01d074003800b6080484590241e02558010000b000480e00d003448400585041140142008980121008141c0420b03204084849903940c0c90281070143360f50211200725003000c400c014601e064500f0000505007401500b081410004100752009600c0100b035003680c3d0451140c0b42140e954140c9100d4080034910184114040c000c407219442c2c40c0c241d5082c207500c28001c0e812400f45000069285020821350295201e4484071101c4c20103d2007100700307400036a805031034928035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 986283579 1250 986282329 986282333
    0x1306021803060112051c170702030904050c070803190f06170708010b150708160f120302041a0313020604151806122f0c100213120311010515040e07080c0d 68
    0xf1f01200c40600d0650245904208001c4540c040000c00f84c0010442d81000291102c0c3c084449134020f0030741c000e11001041000c1140425190016600040d2044000c60550341d4400c450342540c0e16a403110b40c821480031205006400c09000400161030640000c105540004c4000f4208100d9800c645080580009080c1c09004040d4115172803207140a60401ea00b2686190100d00b090900c82c0c01d0f540d86103002c1c0f8001c41c0030311900880d400c030b4108480126215007110001c045070b82c4050105d03c01380a4890300030300145c49000140c00141515026240b070b25440f900060417031140720f022900244c047d80418001c0c0e41d041403d88400c12040c5074002241e82007007140c3e0031512951140b141c180d1510800410b44080b1060081c00d08c3c4070900705482c0020ba03100001c00030f9026050000525542551050008200c00c3c0c071134102040c041d2802c034036094030041210b0b003156819036044225a80820840303010381041e0203425003e1924070000c0503140c0c034181000d0b4139040d0f0203050b2072013641080c6039101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 986284829 1250 986283579 986283587
    0x1230403080c0d0c0522030305090f030309030703082a120309150103050106140109050a03110a1d16110d030b01181205010b0a0f0504051306021803060112051c 70
    0x140f046560401001014044100908140c0010078001003810044107400c036507140000040d01107030f46c541c07203460a01c2c45070003c00c102000c210401c01c1d003510040c0199991540d00300203080080d8020400c0540d52110002000d43c01810036021318003601e5113900040300300400150b1500d6000b1005100b40e01c079211819083c0c1040e00700108001c1070054200040180001036010b08115007482c03002400f10042d5000640341d2040d54814144c1c0821072040030008214410400801010000c01440391075489000100311100d090f12100c107004010301c2001100b00200034801c0300b2110b50b090415803c0c0030f4401d41641c0303402404050f403c26454010300005079001340d01a0806a40030721150110a1b05d503a07121769a20705800d0b003a00c140d805d0607851501400e00040b4603040d900c03641100c0d4080c90070402800003a14010380181400d0403803442603800300d2000d01c0138120a0211640c40540803103081d017014640003040e04541c084071425036040700099030004449040044503045074400b0520900155 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 986286079 1250 986284829 986284837
    0x17030f03060405070c0b041202061b07110f060708130b09030613020f0d050f1c0c060e0c062b110d1104050d0c090e031602060706090c060c0501230403080c 68
    0x40540c40d1406c00d00082045400341d6130318401d002c2d42250115943c081d42e20702c1360031900352695010807082000c4404030f0034407820340082e1a0301411000408407040007003a80741d440103000f0340b2508800318401c42594580c506060081c52001e42d11401c0400307490010345c0301e4101a200003d06100d8081c08400c44d1560804240c00090003410326080c10001d0800c15296252582d4513100c0d40980c40c242841848182c0a508210aa42c1d407680c00c121619640c2400402100003e1003080c860303031152103019656100106856490b01186c1c200b03e0908990240c10100d079402640b08080c01c0a221450851506090705c04405251001117080000000d040c0003034407407030300681c2e0070801c5401f1b6a010f01081d229500122031038103004200b0302c5203e0021383d40b40c0c003c44c0c101200d0300907030010020140c54807002800409004007000a41c2040b40e0b510980f01e03120725807140000c6422071103220103100302031060030340c0104c80d07041d0002c144e18015021402c2c2440204020180018500441c030641c0c40d807800e072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 986287329 1250 986286079 986286083
    0x6120a05100b0306181504031202031303021606050d0b01050403080307030207021206010b0d1122050117090a060c0c0f0605390f090402031017030f03060405070c 71
    0x3407100c0c0d40d901110940980808408280680308400c041041c44040d00800c2c0c0c1044002000741100700d003518440404204054001c1d42003000c0180402072a1070140b0085003d0150100300000301815880c01900301200d44c42c01d0140300302840340402c1420f411404032501d0100c00d10b4009082c14040c00182d800e80100c1e0406441c500c80402000700b59070b05070303004007107040c000c80e0710f03a4185040840f4199101c10074018113040340340c21b00114401110342d4100001002d2414002c50034841c9000e50010262203182c0342101c0340800e45d404012558104012149100d591204103400d490400115940e8a04d100c8000b08000d035500482d00341c1511400120b05070035800380d090031500320079003400c0e0007801c0c09641d0510104e6020300440105a045400202e020303525803990701c2103a0300d0222803d41f84d0000c4178000c0d5201c5c410130810f24650383c1d5100a43c458541260711203445401d101d0107450988440c540708103144d0007001a0300c0607800b02c0007500e60060003140c000c6142e41d034003401151604030700c1c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 986288579 1250 986287329 986287333
    0x105060a0302120c070c0f120b101503050f090a08040e04020105090a0e070e0d11010809120a031a0f0d06020d0906050421090f0608040503070c0e151806120a05 70
    0x92119034130078140281402c074050010f81c1003844e00d0ba650221100388610a07010951003100e41d880c0022001b1100550104c544440c844c401661185251000c1d000040710900082d81d032800c00c21201034500c285500416801d0060050303180f243e40e00e03143c034400c5000b06c0584041c1e0200081c11a8881c2d41111b442c1c48024025049165540e86070b00c0d0300c51819207602000c20042c07a080c464a040c6000c80e121901d4004bc449412090000c006581101c3c0240003141180914140c1c4005809054011704483d40c2a90700000d036080287c0c0404a1001781c246158405c0d00907a006580c1d5175101501c003c42c1e50303001000165248001c014450080c02c2c1400300500850138030041005100340c01d070000c1103e0b0182010710580036418041110071a0b11b81c041c8201d4070040240a2104c18800c620090b40244500c00300c80c60300046407030700e501e40e6042d81c0c0804052800307602008584440c4203041140c00701c003698040c407800004504411640c1c0002e1a040c0105480b40502440c501c08020008495402c501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 986289829 1250 986288579 986288581
    0x901110c030d0513060c0309090b0d050d09050f0315010303140903011b08071707050703180f260c010e040209090106030b040e19060c530105060a030212 67
    0x801030084d81204003800d82116901c500020702c40e00410003642600d0381542c401c0c1500e400c1658000003403040c01545604840c0080c8000c0c00a0020012441018000d484445109240100b04041040031450340b500070341007802d048504d215080703007072819a40c2c1818000400580702800412034014545a651316600380003400104082c03400354000e00e04030650707071100542e6440c0e0f001d94000d0354100c00c5d0055800384170f002404d800d1084000e41312061103442c2280d098030321030040019114158103c0b4100d1070300c00c1030030004056850b80e120480d0301d5400001601c07224404401751101446084a810b000f0708031113203003d0f669594100c0e107103000010000c7c43c1c2941c490900600500c40e080201b40658640340d90a8065140040c005001102c0b600d1a0400503505540c0d00028095061002c001c0c0604121059060f4000c200e0b0440350342441100304000c0380d003001010340045406107003000d0f1400305503482d42104610303140e01d6040d11802ea403d956035106424086000344100f108a558440e0048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 986291079 1250 986289829 986289853
    0x30405120a1e0c020102070312020a080c0609070e162003030423030c0601091104050a080c030d051810230c010c0906050d1e050405010209010f140901110c03 69
    0x208210395030070b12494040280c0c90310000165000145070501038056408903800304001034218126a070121041c0c03058072001d1090b135859810b5a00410b04c0e00d0700b550480d40410a1080040200f000140803040b40e100a070b0411032812a4103001c840101f10401a5000c0c845601e05a0001c4c80c03040034804034116548e0341f52905100b145070102c10318401184410100710700e0f180800106541595026002400036a441d01100c3e400070410380b107058130b140e00c0031f01c00040c007680c550700d8020042c50b0400151040c036017400d01301418148100341443c02e01c14240036103805004400c865503507800701510060300d1408071075403e49580d100e4680a2000c6025010345ca07040440e15800f030100260607070024800a0b182580c241d4000c00e56014040000d1030501588c00d03800c01c1c98102c01920744806140a500c4d9088c0303010101a60740444050311203179000039200702107580c0480c843c1201482e51070030000318100e00003221004d10402403484d0401c910300000d0b400c0b000b81489000d0401384028100d4680070101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 986292329 1250 986291079 986291087
    0x209090f0f0609071d0d08040b0406092907150e07050a1514180d08070201081605090411041e0608070e030601170a05150105130605090a02030405120a 66
    0x44076502484030031440400c400c0e003807080b6034501681c560344076161314408495030030000d1202095407550044c48040088049880f45008002424000d04110354803410a840a00501241da1201086003c01c1110101c0007a0301800100c1d00b940a000150340e0b0003d40c100106214043d10000c1207042c07500300342c002d1202c400505c00d8200d40f030944540045903075504100c40c0060800b0054004a15030205c40a29100d00000034400300c064103d070f0101142000700401c040d5550040c0484180310b00107501e03c00d540e0032504583c1c0c802104080010300c003001c064010301038010b40c484075009603218100c04c400b2400304003c0e0380141509040090f2403001c0e0910540302d02d00140f1440004c10310b414007003194a4854a408010014050000e022691030949001d004003540f0b60311504500400502d01c001490500041e000d1141154a46400d541817404005a10110940b04440c4500c4c0040070001a260084543ea00850f012401602ca036aa0b0415034204400455200e000c0900095800100303500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 986293579 1250 986292329 986292331
    0xa02030a030b0d0b1617090d0c0203150106030204170102090123040b131418061507060e0c100e010215040203070308030711010609110714070b07060f05060402040303140306040209090f 81
    0x10681d1006010000300c515840100c6d000c2e107941d105504001441710f80300b8019a0007181c1c0c3e0784042d0864150180905401c0b901d420282c102200203900090100600d9400d44150000d07080803c2c021490190343c100080d205c4281d07040081010544540001e0709028043c007500c0003040600506581d903d40001c0c607060b0b014440c00b074095001e180030a090914285160381540e044c12044400312251130314410048540c160316069081100100400b00010700f145c05011007480c000c1000740810800e07102005250050161080c003040b4011052400d40d81e8002035020041101c80d95500190310380e400400d003403485070b410282074420000184080303940e00ca40c00c0000b40000d4002006030f240c0b02c044031000d50b41180e40d001142070003403008030080b0368107000181804c00d0540846940740c2c4d861507085010b4024050039284948d559821a03209401e6001c0c4030350003101250114135050031664081e040e070907100700140c0808008000070791552207550403603481000c010b160404a06c0c060310400c08402c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 986294829 1250 986293579 986293621
    0x21e0d060b27061e03030708071112010b0f01050f1804020909090601061b0c03140a06113115170c07021c03120c0903020904051c02030a02030a030b0d0b 67
    0x40360071342d014015080c0ba8881140440c004001d1480c1814680701c41109401501003651b1703080074000c03c0c411568030201d664843d081124004540741003200c081003080c02c801c0c1529070610004111000004621400700c4450107405c24046030280415008500280034551040350410440d0f030034005510000500300d4100e418903a20301c030340030814103503018a0717000740300c0010310110044105200003001e2902001e2101400400c0b9030500c100303034070341000369410040e285015a100245110303103144207502126003c4200b40c002c60b120701a100c0056451405882542c3c0a4050350000345c0380e85105050222820001400b13101940c00d01702d40521b010760002004a11401080b4096845507030321100d003003242901078a9405a5451100081005d401462018020801428004001a40e1ba0301c225802940030304018510304000381f110706141c400c200c18400030340d481440b075191407075800001c40b06448070300e260110f244100a004210301c1c004205005050362519030801c46504185085824000c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 986296079 1250 986294829 986294839
    0x50f0a0c15090e01060306150c0c09020a030b03011508011103100b0306120f010225020109060305190e10050106021906021b010e010e1c080606130302090a0207021e0d060b2706 77
    0x40090350039503410103200b800804a03cae81036070801c4612120360246c01595140d050206504100c2c400003400c541c2800e8144200300d041d00001d110300c000901c030b022584054420081d186081c44480801141c0e0b4500c1943e00703084000000801644501000ca044c170075092044078814215400c449000c0c0d00818554101084200308281f03224100821144903150181c49541c40f0740d0a10000b140608402482c1c00c0601284040c0703c4002c0704244030b062540240c0b000540b00040143c5180010390710183c5c03200c411035201841d81141119400c140128071079125100503a80c48040d000a00c032401c800e803501243e5460003181c1e01024a064110040340000322080d5840c039800c0100d0720b0004484064800c0010f2980000281e0a05000000345003065212460900c040e60f13940c00152804000c0311601c01c0c00d43c010a0440071400c01d501c814500d420f020079207060042030b4001042030f180e09108003034401501d501034000340303071582643c0140d42040000313801200501911288090f001c251a814010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 986297329 1250 986296079 986296109
    0x2032101031b1508042301050a140906130c1a0c0607021902011202160f0501050a18021e03030c010e0708030910050c0115030f050f0a0c15090e01060306 67
    0xc0003110b15240c00d0301e5024988003020003c0c40340407035540714000c2044404a0780301441e04d0141034030b052040e540e2012400042003600d413030200c4500f9501c6130080c0c2d8004d11062414009510008210294803d8000c450060040d040c0d08001c0c0b01d81040b070f0b001070348103000c49040e800c99803080c0006140c10030b5184115051a101c8003001caa98501480d002d103800c0701d007210a10019031050303844c90003542c060440542400180c1c0c40b1558512041001190080c0307004c0442000c02c407080c003426a01c00140c800030406003640b89248040032412610007841441c103181c00000001404400c08191b98014003144e44900ca803811081c001d10340680c44025500c1507072000500300c0e034008119403c80e60040c040c0d4403c65030fa03903020b844a4119103440d91442d521135080c800074031391800404000b18006c2c0d0101094a0712414003034280241c030420b0b2240794100000b29004607003c01c40300402ca0305a9528502c1e4902c2c0e074007003299040815080002040e40c0b140001a449038150440760644030326040200e51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 986298579 1250 986297329 986297363
    0x6030109050f061008011406070b07020610060206060a060c05030d051f050d0c1a12070e01081f0524070f03181220131a0114190203210103 61
    0x400c000c0c2044c090005000740c0040c840109040764074407a62401400d180c0c1080002e9607640704142007100d45400507800007003040022084008181d004100c6400903101c0d505000c070105011100e280540f4060042e440e81e041c040000170030440e1501608803004100a041171100a10301301150f801d413104502c04803102190f185001951140400c0c2d01c40008104145004110902c5961202455000460038060302d19903060706011180300341c0183c0c0d10305203840110f00001d820b41d5070103001c0d1595980d59941410151092403290420340e04111110110311041e8000c0f004076004505031044080c4010803c4410001e0303500c00c422050b88640c403040705c0c0000f84031000280c42040d2041001c2d4030241c070b65141c00b050100701d0071101886220b92541111455002107080d0000454506c2080c5598940c011480103c01e0100700303a2400c03d00c3e00412a11074800b1500007800b903103a02211085080d440460030500030411901c0055400000e0081d40308014100b90350b00c01c0900c400d8420411411114503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 986299829 1250 986298579 986298589
    0xa020432070c0b0f0604150b0a0e031204170106062f240a0f150b13050d1a1303050d0e15180f0c0a0302011d06030109050f06 55
    0x15a01891014400d00c200d118000c681080016010205014084600b503022804020125106010aa95280280c20b098052000301c44941ea480344a20a48010520034001100201c9403040d4151502c2c604d0210400006030407d0460091b801c00c0030f40001c0e000920385a00c480384400020b6040c0200000c1d0380c1d90000ba64506076040142c0c40c80910005000440802d61414810070740d81d101c212407051003000d4800e24180c110071262882c901c8150704201d84420207014005400040c01814442c0071001600030982d0105802198400d20380850110100382d81c0001d048001d2600400c030184070300942c00d00300c211840c0000b42c14501c07036003a0002989106100c00350044540d040e903a15191059034416500140005803c0795101e0149004140301c9945002c0a140103281c0c0d11001e0004558105c5542d25118030070301c444486410406950790301d60f554100c03842c200e0340c080c28100d0558150401c2540c52a0b0741300001030740128080300104040b04140d11040c41421610400801611140100b003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 986301079 1250 986299829 986299871
    0xf060403050601060c0f063b030306010c032703140303040c05151c060f06090b04170304090905011406060304020f04020a02030906030a090b070807051204030c140a0204 74
    0x35180d50301030001001a40d02c109179941a140c020801021850f009a80303034810740701a86000c0131544240d0030602e541c1118400301405850000b180c07030818041000c80305460740002000349050180140e455014035018559500412a20022448442800503400660f0500c14082565110240401001d0001e000822a80526000200204003a02d08010400c0300c0482e0b00800d110807405004c0080c2c21300c01e0081c10000d04091440104180d810300482440445003a40f00604000b80c0050400c08a0f4000b001c1368242c2d4450950204602c110a20041c41c502ca10b50152074090710b030070034040900c1010b5100e4008545900c000400ba9100c1108118075408107a070041c1d482001c0503189000ea02d440d0380201200000303401030303905220142c000160359030400c851084495071034501d05420005402080c503402102420700075601c0c10498001841c50041000c06a0014100c8001c60f00341350040c02152489603122003840b03c00c5080d241616164541032808900490070402c180001c02e00c035510312 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 986302329 1250 986301079 986301083
    0x2303030c0702040b131406030a03120e0f060a050f0f010b09010809071a07020a0b0c030307082212030e0304140d15050103030c1401060f03080304170a09050f060403 72
    0x4605644561845110507803044100701ea21694940150031152500d04102c814109004000203c12060051b050800d0400800e505c2c82a000198004c000a8201081c0c0650028807040000e044503240e01c19482c00d40e00c844019110700c119401c0013000013041d04420300c2006008503039816500c3c0e40d001031860a800f8007034a0905901402240815482040d000358071100d15002c94a41c241c0d503142c0c0c0d01d0386a1813440c0c8980c09440004200c0c055041c041000e8008060805085140c4074062480d1512408050421000c01c0103040100310204150940380c90890701d1590350000c3c0311101c0c501045400c40030a914004a03080c403d103640021404415102194020309d11034003201150307010032030350000004003100e00c2240b1081040c04903038503100c0c0b175020710301c81c0d11620400a0141030000510b2501c0c1710900c400c1e810705d4401d022a81c1000180c1f02203c1e8040e403229107d465519006090422083d00c8010261020650050095002107000129041a1801ca16100e200c3c0c081c080d40380b00302c1c000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 986303579 1250 986302329 986302333
    0x130f06050f1e04080708010b0603130f061e06060206090a02210115030f020a0e10060305070509030a052104031e0c0b040603050103020f0d03081b09030f0a23 69
    0x410241960841c00400007841514903a400d41c484600ca00c0303600c0d40207608590942d9002c94014864107109100300e00d00c401c000c88036a400e52601007084005c81a200c040281540c4407074880000b0440c0507000b081c0d181e8100105500101c4440c1002c0006000034404c140062213050b020a0030010301140c102e0075140c0281a03d01914040403200c4505051080c28589070741d0f0f18140c1c2004030309089004405184620b001d0b40880055004000801c0100d42020740314400402c20700c0740502040381c00b801115558107000c900750f82c610b001596140540f80585070140128403108042000c0030822900b00321490700411201d00c0c51b030b0600350750390049000041061400711240c509007100c0c0051170a041c0c0c03041071050a000d031110200c12040d0096404500402d40724401402145042c8c82c4d07807860544281c420989800b09600c0041081d800a040c0c048800600c1d51404c0c110b0010608846c0920000740481e404444041f03107460342d94507604020740701000804c10514007800c0c0240349000106420340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 986304829 1250 986303579 986303587
    0x10603140f060109121b0b0c030a120b190e0a0e0c0f0a0503070906210503030402011404170f0d02030a02071701020d0c0503040201090509010b0a080405070902030c130f0605 76
    0x35000719010024003070505002090b100060313180f40c2444410f5500344501c02d400e03100d0b150074a013100808035540041d59140014000c0a00402000041c2d449a50303807860140104086c0199050041074074040340c0d2b4010041400c1840c0b80040300700310008540b4151003102140d651104080e04450007001c2c15900d5411000e900c502c1d52800d4008400350400c000c0080d01131a643d100040d14101c0c0c03a0348000c84140e100c2408110451191006401c181c82c841c2c030000380300815a90b9142c076031000500c02810f1101303403401a0300d966016400c0c0d5019081118001d0800c000e2800c0140d0343c6e0b400150751301300910030103101c140c10034804000e84c0c10703024164004103c0c042c1000f001000c4030000701c010600d5594280500d940e50700e40c500540c0f50104050b12510364a08040c000107085000302d406c040d00400d4207000402c580b9018800322003c1040e41e00d0001b1403915103240c507508044c1694004c3c1c04440c004000d00586100403801400219001c0b1100b13407607030384c1d111400c9905003e14840e410105800340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 986306079 1250 986304829 986304841
    0x50601092304080408010c08150102030406050714100c11060109060533030103060b090a06060203160201050706230f01060503070f03090b150102011103090c10020f1f0501060314 78
    0x84000c0b50000d204024050034a516007140c5400c40da24006604001099041800b00416041380f0b844800c030428400b8600c1c003810140e0240c0a88128980140308500d4800a800984814084101d901012510030301401c2c0121100601499841280c406140a94000003070401c0c600c0c170a40c0300b15000680291640240c90214200c0900059855002d000c180094400700992460045001e58820752000030040054010b001810f5001001c000805103001c000744582c9070008140d0b42c09680807a9081c034400018401203030680290403001b0600f40c20081e103005488551072203030150719082e9035401c280d075490552003d80c001082c410040802c42c2080030405a910540c081450000c0710f060129801e030403580c4210403070340e08840e03c1d660048406065901c1e5030b42800344a05040c070b070980d00c40c01d605010604d5611001c10040c03c80c400c405070054408454000c3c811220b691007450192412180b05e0418007400107120107542c0500c40c50500041901800f038401c003d180115002518072a641d05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 986307329 1250 986306079 986306141
    0xd0e0102032e0b0f0a09050f09011502030c07090e0f0d0f030203040201090e07030c02010e0a1709010216080a03020c091e06040b0d050f01050906010e0f10051c05060109 74
    0x42d400040380394200c0021400300e415000030031400b00252440ca40c3c600f0011001030002c3c0054010a01c070707690b01070849074035980c0c8074103007419104131204421000f00c000e5810f80c51440b076207039150480d003e5104000745c030304020f9000b2824020f0310b01c10f552500741407151440c4c940c0b000c8150000400c035000222088a4840d03070156500502c181003490b0f58a455102200e4070420442c3d10701d0001c4e46400b100ca400704da081c003a602020b1238a9000f080d800860741e6030b0b40d26045086e0240c15803018080f80e41d6125a00c02c0220808103d4124440040300e17465a41003a1188803107030043d80544a41140070300342e805c04602d12403003110203d15104100144004009c0b000340d02038030403644280c503081c1c601134a6960720030090f955031040d030041c5200080c00c1c80c2c180c25514003c0c00820a078002170b00420281d0a0750410903807140d015443c039540c1ea03aa10b69286e440d02174507042282c000a0340682c0460b01e02341c0d0904d24141c1802103046031584c4ea41c9094000036103038590001050000d40d200d5640d4440e0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 986308579 1250 986307329 986307391
    0x2012090a20040b21070506041a030a180b0411010503010e06010804050c0a0602030d06230904050307051605040e120d090f080a091d060102060621120d0e010203 70
    0x1440400e0041078500058040c1860082c01c0a0130540760907585003070705003000150020308081c0c2e00340c1d051625002d0425407510100301c119650304000400110b540b5590340c088900b0121103201d031101017029041141c0001d1003190100e4002c1041580c0d010315600400640e030407a401c05860151668402c801100e0b08a00a4011900f91040000501d056501d040ba0a0702400b110b600540e110420712040005032000c550080400d80c80f84011100b040713406c0044400f0800e8290703a2451503440c0c80c0741140c90752040c0034010f80180140c5940501150f00c881d80101107078401c450903c460700b00b0b5098241c5030014a6000c0a4007041085440102035041c0c1001c5101c80c05a034440c40020480d0311110400d511100798900014141001482a208052081e00060072181c140880301d00c0c060300044e6491310302801161186080494080c0e40810554a100d0000b03240380036224200c1c5419182c40303140e00b101d0840100b45040c01c0a10500c41c81c14401d40744100580540070100f90b0280c0750744000d03409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 986309829 1250 986308579 986308643
    0x30f0a0510090b060d240f03171b10020a03050609090c13090c0b09010906050403032f0f0c0a2114070b130519272012090a 54
    0x2001d04c1608200c17070b19803103184000290a085c803844120380c1e10b01d1b0200820345401040d200080b0050a10201342410821010076558450090765840c20802c4a1240c10030800319520034880c040e83c0d00c0d8920a550098010380b090340c1c60602c01603d07003004028490300101c5680300160300900c0c0300c10345864400040305c031070441c00b6000203041f109a00c0d503009008054000403e60300700010042071a5034404600002810640b4200d42400d0030b5550041c1000e164090305082003043ca0343c061400c40d0100c96400c10b111070002101c0d420308642003e25190000544202c3c0308440300d060002c0e840c00d141044403125022140c1701401d03a8803e50b03d10f1003501d44540d0b416501c0c4900c5070040f88400101000788011002c3c148002c5181c2d140c0700030040d40d4211902958085190028104091000c2800140001081d101001c0101215040100c0106014084901d54444503d900800d11114000071701e1070a1140c85840c16590300c07401d020387c1e9682c0ba10740080c000401c25402620851586a040345021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 986311079 1250 986309829 986309839
    0x901081b040b040c090806010501090e0c07080424030e0304180905010b030604140f0d0801151206090b0909011b1101061a0c010e0c010f0f120e03030f0a0510090b 71
    0x2c440300c04202261801e8081101042c00c1d03100501941004100460052500f481e02030111400c180c0d8805980202800703071000d406020232520308024420040c3ca024100060f5100140c1c0170311000200c400003101120800f181c5001000749100340b02104076070641c3e002d1400b070201c204282407854014040c103d4140e425540e0350071444180d80c1c0a1141c580504d003d2060f289409079a41c4a0354204030307a40c0d80c50751251740440607131301010303400820140c1101d180d04078800c40d2100140b0280c41983d00c0307011101c40b03985803000103d4420299440740c080c200c4103030340c1042696500c85606003240c03043d2010000a110300c45101d181c55104101c09241c44560400110741a681d03003400f22072100710055050140c4002140000d4690360902c11004400c001c4401441c0006d0640000303000f08018141c1c940c200040c40e411304048034040c03402c0b0f1419100f401c800700404808214081d841e0742081d20a030b10068860b90100d040d81d003485c0120340c0108124510a440300d4034000546008090b0100003035041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 986312329 1250 986311079 986311091
    0x3030a050a050d0207030905010f0e0f010804020d12020d030e0f062206060e180606090a020309071a0c011503031e1416030917060117070b0a050c0c0901081b04 70
    0x20f100c0c0043d040b664440c1d100d0343c040904200c00541103c4014000b24100455008100d40399559007448600030b160a00300b00d411502c55001007201aa440c0700c1c041c04081c01c2d0004002000ea000a8a103280480b80d038080140d117641520007522420506020300d00340e80070001203441000c144a40445c0384050180d4004000e00c20703650a000d68070315502c0b50f20300320b03151410000308a204040940c01c48101c1c4010300303e145440750014110140152001c0ea01507804400100148810804d220144c00080c0c00d55031075040c09070940d00158850720f80341449508096184101989040440066a500d919009900241032111240c50582e441c6080700300100c4441c01080401c40c00d0040c40c0300300c90040100d14500160402a064058992200d0443d4213119041c80907840040764580c1544d40354003814480304109003105140c40c001d608010a43c2e0344c009481c814003a0440024120b9200000036580030152080410000d00f50034840c104040c1c00c40002041824002d6600c4080706e40000c00020704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 986313579 1250 986312329 986312347
    0x705030708121b06150405010902040b181903080d06150c06091a0106050309010b03030f0708070204061502030301092019120e0c0306130f0b04030504050d0602030a180203030a050a05 80
    0x5813020a840384000c1110081051020f42024005e80340500a0039900350301c2d092800b071503c0361510850784440d00300704c3e1012034072606642340c0e42c00c20840390034145450303d0162a0309010209900c07003000a5441d52030301500143c210202c1c000c1003004c00c1c0c16101c0b003507020856181e8030098180b0213412500155414000c9030403911081341d4601900003640ca01382c4900d000d107022821900c110500b50311940c020700004030040c1d8000202e0300c40c0d0342d0108003180c07514240d00c0441c001e081c15810006038102c0b03100c1e0040c1c3c4c0990010166048403012801400540703443c07408074000d0386510303840184c48076040061b1000301c664194201d500c00400e1409490740d80d540901d1f1001c503072004c03004029035040190800a545000c000d070a8110320004407209500110b650307000d4182020103002041c2e010490005010306005e20151001020301402000000460349030034002580200c41040b1054544958180c0c0c44501c04410302d05941e000d4015450410800d10030b40746034002c0b00744101003000c10448554 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 986314829 1250 986313579 986313583
    0x2150c12030a020301080c0a0807050420070f020a140a03231006050420070b0c040e0a1b11070905060613090203100b07151a0418050705030708121b 65
    0x403044078070b904010303165414042c0701400c012a1a404c1ca01c1090140070030300400c00042002c00c112001120000340c481281c00044100c1010720441c1540c154010a03c00e0901c400610520410f40c0f08684135220a92074402c0d007581c4a21007020f0342d0704001c18140c2480055200e031181c103120007101003455610b10043c0011403038003441c07603411111a500c80780c0c1000f2508142c09045c04030f405102d22014040380310384c005c4006004115000c2e00c00d032201408103154440460448010300013821301c060076490924440b802400131801010741075603040594444003881081c2c0060030301481806000b590f0f20f01010500a441d0140c03010340d000c00700b0024800600704031500f00f002003010060141c0c8901d490003030315854041e40d920080400b9000c004000c0051484030310b8807614042040300261000940941c000c5085040c1d040c83e4000303103811811400000c012511070503803407064086400040e181e90500d91034005500c070383c1c1c115038490382101802190744800742080a40c0d00301540c0ca0310243d000824 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 986316079 1250 986314829 986314831
    0x206090d05070e10060c021516140706030513020f01020c03030d1e05040218040303060e01030b04050c01020c0102280203011d16031a1b0d0c1b02150c1203 68
    0x1100780e4014a01042030f582c40e0034419a101c200d009000745298904078001d45616910381c00280b2840c4400f5040203070305003100540c1e40030f540301c0c1441034011182d0300e404090080c01020200051060307072000507030203100307008642c440c8501100740b26000710298284a14002505a428154007131188081030700d45081014110440705c1c0c890115103006076a008000d001e0320150504000b40c01c0c2020800540c0725480403c01c50362083c01041503560f40c0341400c030001d21480c4c0081e11284003003000041402000c240441c000c1d4012019155044451801640d031040707003c1199015800008000b01c00c040c0400403805070003100d205106c80c1306407950001e801c440f80000c02d402c000280349410210602c081201d140b01c0b900c0c1582c604616419500c032246009000e5641400310082d120001d00b2860b208840c00100620703143e07865486800f6502c0c00030250a03000002d8000616401d143d90035440650034081d2301c25008bd000500e888105c6403641c0e615403041c09889103510841074001400c42c4918025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 986317329 1250 986316079 986316083
    0xa1e03121112090c1e0117010f170c03071503050901140604200a080f090d02060a05091603030905030c04021e030429060a05060c100b0d063201080a0f0206090d 70
    0x10020b50101500141480b40c540c20207c0e184944d80300140410395001c0500700c15201809181d41c0051030410030a440c211440c01c8064040c00b41c09000542070211205030f02c0640950344060116940f40442c0790f00721030f04031034551164000031020804a00300742c2e00001000c042c1d107151030901c0c0c040e42c40031296680400d2035100040d4020b402c100c040503202c0e12040c3c000d810480509041d8000f400007d64581002e001040720f030340d4940200c0e20a00b1f0803c40c801d00c0e44001054072a445035203080103400101140704060283c010600c4c41c50040c5001d20894541c06604040c261101d590110b00041a0304000c004885041002120246404d0b0f150300101f01ba0803128040da44510702402801200b0a9603400140243d0042c001151080808600740c6e401c0d0309500d40c001400e0151000240d9180c00343d203c05032020f4034004080b0186c11160252040340c44000c4c00400b00a2030042a400420000340315001d55508941707a000e0025900c8426181590f00080480b810b2121450004500e14000903003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 986318579 1250 986317329 986317369
    0xe03030904090f11060f0304080d092109060c050a060e120c03030709050607110d020f3c01090905100b0d050f060306070c140a1e03121112090c 63
    0x1e20400c001c03004d645200510001d481003030801d1b51004900c00c1d0380c000903200601040c80810003640c07160141c1d02916900350000390305500c0d001910241c0b01181c4103040c2e00e40c00a41c820001003881401400100c0350b981d8081e000f828030031001e454400c020400d03244920500e00a8245180d1840c07a0b940107059a02c1405018603900e0034401d41c007915082056100c0c9000f810280f080d1400b088680000101160095641904114851002070b090300c00e54101240d01104411040e500c1c070b040c0c4981089020301c0050b842c41c80c011800c040291034a21602c00c1c500040c0000c00c140002a9982c2089401c11440c4070000440c41d120040703a60250043c03407008540ba035640081140c2e06103a0205141c00c00b000781d025111030f08204d000200701907c0d000d4054504401e420070128010003c000540001d5041400f544000d4014031005580340004142034000441409036031403105007501c01c11030080c0c1880c2c41d841c80e000001c0000d0003c140d00030103146481c055400b01100b40c3d1214600b404005601041d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 986319829 1250 986318579 986318603
    0x60e06091210110a090515030115030605120a050106050a0f03080d06080a110103050a05221b080f150f06130207060f06090f140c0f16050c012a030e0303090409 70
    0x90020074417122a81b190f03220b21f01d0050280da05d0b40705c850449042d2614960460541140e981050340070302465442560003d001c400e4010035010041000d0111a10500081c06011303030302c078100b12403c111801149007030f09902c441000000c13030020040104201e12580800c500303a40700c0c200e17411b020709624151804a003113000440f070366a01d40b18599020011441c00c00c11800c01034038010000703181d10703815055005034504a105000140d180c4480c51196001100203864850340c1c090f86650118503040b01d18420355075440d083d0b060741c2081034440c201052107110a03a079044100414004808000d5602c2a403c010301c2020507014001c250780f00d880d0800110b42c040c94090107104481856010b661214a07007817420108107484808141c120100c6501c0316111008d01e100c50303042c3d1182002d07e110107041400c1000802c078020501c150300d0300e0300340c07510780491003074151041e04801c00b860b4441440380444c9640b40000d00407100d00b105070300d001d021a420190340c40040b03821103880302d009941030f4000e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 986321079 1250 986319829 986319847
    0xf060f2b0f050f040c05120102040b0d090c080d082809050c0109090c1e0e0a0608010305060609091c051908010503011b2c0901090903020106060e0609121011 69
    0x200502e41c02c03651968a20226103002e80300c0349140035a5000b128440c031000420525698803d40550300501295480c6a5840d030303501d01038800a15802d00102c40320340c03000800265180010900302050910307510349810036a6000503882c150340c10700c50b001c0090007008912060b00b010907ca46110548548014101e5034110400984501e020ba801000d2030303400c0201180595512204803015800441c0980451100c8080140c0b01c1446860251703800001242000075601d502001c842c0c100e9014009882281e240d580901c501984201c403040c0c050f81c002c0b05000343c0c14204840085500d002450034905050080c41c0c2d0002c00c80d8000e10410000311160018001464203104141030b1441113a040c262909444401070107a540190010300901500f0900c0f4840d9604805c40c1d091050000344903440d9903869000e003000030300761003c2c01c1d0015840c10401103013050142d1501c170361058004044505108140d001c02c600e01880780300305078850003400820746413100d16000340d04403840100610307500c410b182 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 986322329 1250 986321079 986321081
    0x8070f0c0806011a0d0207050a0b010e0a02131401020f011b1103040608180307080f03010e1b0912011407020c030f010c050301062703110f0f060f2b0f 66
    0xd4000071100d40280300100014080712041c0308241e1000005203032203100718500b0900900030010302074250f00448000e07008010329495454140c0f4400d804000298540c0034441c4200c1c01000b41151000e59500300034005036200c07074400c0215610502c100c0d038001100740d800d5400d4a59542c40c001c00c1c0e40215034075200d180d40140c610014542e543e4019030809203008130040c1078040142c10440880e00e0070410a10021007802211181038000c542035030396031a4007130008405d41c024881c22030055955000b241c0000607440340e4541d8612a800c0319424149014104031410b419000c0f100025236135107074000b00c105003000c01c0300e00c14190b0303030050100d081c440c1e42890301b010b02250009138039914141400300d0303031600281500e0551380145004401c121194000c5403c000b5042d6a0155001b000d00000003001392103c5008180d2905a450708280c21409082c402d100303c010758000d60000f0244600e40003070500d80c018001100141c004a503500e06070260005a034443c3c20310b1400c820740c441851445203605 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 986323579 1250 986322329 986322353
    0xb270106151d0f0a0e040506070e040e0a0b130606090b040c1b0f020a03051501090f0b0102030403110312040803090306010e04030509240a030204030212010b011e05040308070f 77
    0x1030421089401c02461035645400c840002e0320721669668000f44000d8940c10000c01c041c21026054036940d04203801e084d13540310022901c1c1000a40f010300582143c1c00c01d0b0044000f11200c4030000e02e950281d5603602c4e1030b4040010903a604594001040b0804140c103401521300070526513200103003198522040c40f0a0b15052100d800074800003040320440d01000b4521104915000f4042501113843da100081d43c000303043c1d00181c154440d2203175282c4080c1d502050749049401c006000c01030418500840f41c20740b43e904899602507002884100003141c5a503003164041c3c1c0009040d1a101e4100606c0201c0e03981003500600b5441e400403603a10118203003003040501400b154500d020081c0342c140e82c024042d1103002c0240740074945401d44084003084060156429041c5060460344414102c5130040094110703100c260712a590705103102c8004403040c81100d584503010307910031240f18019201d04d07504030f82d00002e50b02080800c20001001c00c4440000d007000303a00c1030013401605440c0341041c2c0d150700c40c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 986324829 1250 986323579 986323619
    0x29090105010c05030324091f06140405060706020409050405030403111f03020d1b020f0616090611031903020301260c0f0a0e0106110d1b0b270106 64
    0x3040d25160010500000581e0781c8050700c6c1c0d03500c1da42031810811002c0340400300102d044c0c11110f220203110301d215015000c5495164002d90b5412055651001191019402d8030342d010107070070800060000c0d081580040c41032174003450015140655503105501100c00807501942c96030004101402000713010100d50492030070031a50b85c1009e500b401e07491010b5014070f56003581072580c0091018000e0403030740c2101d40840b4643c0c00c0510314002082019494444070301d41c8404501a1a0001d8800c0c0d4900a165051080b00d0740c52100841c200501940d000015030b10009580c1700c240168400c5404040c00d4110340ca4855402680303952404030403001d00e92203002203d041c0d06600007045044040080c60201c000300c115031592129190344089903814405800426032405040004103105401c49040f540f128840c1040700c22000403c4030445214228001d03008804426000c090003084042061603049090f4444812030494004108209051402c00006281c0d4480000700b05642ca0f08051000005c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 986326079 1250 986324829 986324837
    0x602010905060109020730030c090e18150108030720010c060b0d0b090d020c090c0316030f0f06090608070b0306060a0309120302090a050a0e0a0e012909010501 70
    0x103919a0788840e1100d20501035003c0302540442c001007400350003001d854000803600c1884c00701c170305190180c40c201c4000c001c2041c007090826941500c01d521030888002110440b40c114402a04c4d84030541010204803410445513100f2a03103240403c1814032a03560003030a4500041d540c4222520b005542c40a04814080307400c941c0b808050400e0740c10520081d2425402800007030545400000140028030b200800303090041480104030384400005450011000550200c3d030360b03504004100540365604543d031080040042c00815419007207000c401010454905002c100000c92114000c216503280b90742c00800c540301d0f0300402c08540720b8451a00640100f501426000742061002400c0b40700181c64a80110b5000444944030b521075407103806210b80c842146910344c41e50190040280d0410380015109880d90b400009480c81d00700500c80484500c400044c0346641c4482c0f0110013400071743d80c81c0c1d0180d5200c0b0714081c9076100d8030944c50403c000314070010900b010b181c02030182c1d040d01600128180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 986327329 1250 986326079 986326091
    0x612020703080a091707081201120c300308040b07080c1602031009030903050c061204030c02030705150c061303051c060506070b06040f050f0a0b06040b030901020a09060201 76
    0x1095001c80d00503846100c081d40450b4010251901e20b800c13960780041c85c1e480c200b011880000b00882103000300f482c514a4248034080f80d88480115607181c08119008060342c403140010070600d82e002040000c42c0502e8442c44046110103034203400d0500d41d001c0c2c120f00003030151003040200300307010107202c0d04444c0d540b800142d148ac0260604c0443c2c4103249100c6c01034841c030440002150f80412100040550702c1d0028008103009150141440742280400c907554041c2018417000d6083c0502900c1c4840c60800c0d281440340c503151801e40c0c0091180c101660540951280480d01d5145c10348460075005005440641da01802e131020b80c2450005000705030400d6008050802180d4400103031034024028401074012290700c2c0191100030710403a84095005500451810203000a440b1010300c5004155014401034403858500400c0b2801110358251002c2090f000c110250519404025440d0014141524180c1c0320b56051340d058204036100c0d2617503034000038001c6503590300c0725480c40106a0742c0024040707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 986328579 1250 986327329 986327333
    0x6051302130e21070812040210050313060e03090307060807020c041503030311130303050a0e010e150f0c15060109080319030c0e0607030f030c050408060406050c0712080106120207 79
    0x40b0308145841032448101403c00e5956880044100c031001c69100c0c0a20f176446a192214a4202100315001d0380324140084080101e030303000300100e91003120345001207881491280d45400003441103045044c12407000b4400ca40c09900c0411800000d0021a10f824440d8500464020b25080b20008028040d03814002c282e03450382400038804050b40c0e890700380400e40c0d1802072041303da14010111841400380790608000706168114000301400d5407290303284054598950015035840a6141032581c00c030a0510324021040c40343c40c0509641c06100111610300752034600124074001e583d40017210040d0203601441040c2d1381024034040104642e90286080140c00030030a205200110549400d140d107500942d010240300340001c0ca4007080080100d911001c07141401048403190011040c00700b031400d02150710b094040ca098808550300d14004003220750b20b03a03440170081c10018100807c465018450359000403000015408040000c3e03503001501d62401100a0080081000b00c3c2e00c124810000b13840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 986329829 1250 986328579 986328583
    0x10b4b04050d0602301e0106020d0c080d0c11010506090112060506010c080301080616020c030a020111010b0909060f01050103050f071d130f060f0b16080706051302130e 74
    0x4006038128400507124407048108172100607500040790600e040315158007601d031440d1022580030703450b40881c600c0c04071100c116803607001800b07018250140e8080740070089403034480e894a2042502c65141141407090740e0080c2c0c002e07114a02c62660114468810740a11440241320b8164030101c201c034402d8a5502d0003085000031200038801800682e26480041c00f583d00807920843e81320b0b40803410503a2985d40e0310f03c1c6a160081500c40c0d0800303070700384410720701594030000d007020440034000e001c0c1c01d030704c3c000740e006580f0400841c0b01c90026548440c4600007c3e615075002c81d01c44c92040020341102c0c5496648809982c0b030503085603051614000034410f803858036041f05988039556080c6590909150101e22090b514803030342030f1794010071491507101020055042090300400c40001481207603119a9201210850b42c0907402108105211108102c101c0c0c00004488500803034a661800307131035441e611706990007110041685151601020210b01780000c010002d02d090500c2088502c100c10312003a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 986330935 1106 986329829 986329849
    0x151219060f0b0901060212072a0602060109060f170102190e18060306040305090d120c150209100518041a1f08010b4b0405 54
    0x210b00341c100124014140c031040d07000b4202016542030075201c1c54005103001d032028544034109001401610880440c58a0745217001d041050500d44042d10748001030348005c001d0352400604000324944449100c0c01d890581d01c40342001c0e044d48034258064040da29003000e50883e03042803070a05a80140140c41007027016140289460201c0e0303120018003804540d1150950000f00c0003d0000384200d00a10764100002c4c0704194201d56902c03080302c804d0012020002082120391880180703c400c41c0280d10a00700a04103514207019040880c448685c030058210902c100400e0b1850343c0c164049540d0400140500104004d183c3c0310701c2001c003401c000008600030340644130541c03034004908030820424401c0f81c4481503140d1800303074082000e600095444140041d000f00180301440d0165240c0c1001c4956203642032030104114006503407240b07106030310b00c01f907004110400c5141c84008080d = true := by decide +kernel

theorem cover : BRFrame.Cov 986151079 986330935 := by
  have h0 := BRFrame.cov_init 986151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 986151079 ≤ n) (h2 : n < 986330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
