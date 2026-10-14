-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:03:44.211995+00:00
-- url     : https://prove2.me/submissions/bc8c6013-dc7d-491a-b273-f9afb0710b01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 261330935 ≤ n < 261510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 261332185 1250 261330935 261330943
    0x706020d060e06060711060a02010609060e07090e01030302030a0c02010903020418061d0c0609040209060403110301051303020a022e0504030b01090b03031213060207050c090c090609010e031617 85
    0x400251103545c5800706036252209000740010f02d061003a00b0008000100700d10030b42040c0014003e07a40188005610303241e491805160484404000500b40000090004200150981201c2d01034000e9480c1c030140030400c0f14036a1079072000b40c0c1071005140c40003005071524482c48202c520711800c2150168030f03d10303107481911828064800c1e07100da0201140c1030b507580400d03c282d104d54212507959880a24002140282c00340781041a0311900c00300340013061003603000c011a0703581d000704c00130006a80d81c81c20807070510b0904440074005a11103885040181040f00600aa890701d11129001061441c0c5400c03c010703002c6041440000d2001ca020810406422185030150024080c14840e0122100c0401d03601c0c0202c2d80581c15100203040070071200c050317020741c0580d07541d00010159524082400c02d6540c2d816604565401517a02400144800c0e20324026254121742c010705140c5041000c5004607000d010b540380c2260f15010360800d50141c42d00c000b03011001850600d86818414406050050070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 261333435 1250 261332185 261332191
    0x1e0b07050d05150a140a03080a021e03040b09010804170c0f071a070305180901030309060e01080606030a0b030709021201030c0b0c030d1e060f05041107050a02150706020d060e 77
    0xa0f01c082c1070309403242d40c2d01c1000c03070429100400064030140c2c4d400c000142141d0b1305640003400a400004509515607404120070355020b51030180329584000c0c441069540e0b10076803090710800c18040c000c03001d166101b00001c64005000e4142041c585901141029259000c192442c0165008480282c01f204007880584014542c66810310500d4940140009280c4507900c8001c0400c18005521040d0030802841c0c178101d10005003540002d5038507890080c048030100e006242c04124004203602481d0b00c14104188280c401400076411a2104039008000c1c009808049616010b02400459025003a00c09070500d50b80c40f03c0e8a110030352442c00d242a00c2800740d0850304801900f00080f642108000085802ca01e450740e80002c0c42d40044505039403911905911000c905003030040004591884040ca0019a50129420458986910910703c1c85105000340145141c2000200401510300455901d8040d0106030b4442e1070408290380c0c0303104076805000b100342550f1303842409202c0500300018150f4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 261334685 1250 261333435 261333451
    0x1f24180203041a010609051507170c0a0c08030406080f10150c05030f0304120203310e0f07110f0c04090602070c080706030b0f030c100504050a180c03090b01031e0b07050d05 76
    0x2c5040b08a452b110f501d8000d001e410740500c04002354891416004100d44408a0b8204500901c00d644450710320303850360f000b881580000359100340459a49030070071100c2e40c02001c950405004161920b040c0841000020031514140060409134201084047c001803816240341403442d56030b0302d000e244c802058044480c0d94000c641c001d10240100c07d1090213402d86403c49110401d010f101901000f403107415003074012000345841c80007030102402841c68200e0144115446003850150086000d03a0740b50408445c0c1d4805074010030240c0041d0a00d0340c002804203002c5c4002614001d02e0f500c5000c00001542e1140c1c0080d440040d042090700e5051241041522007122481052006100000c0d40c0c0d107010703a4114490030355900000c4810b40100c0440c2d00918000c0e001d00e02ca190b84100c002000480700e150400414242130060210714031a111354500b096000c0c20002c1c10340d08540396460862400583d0304103c4000603620789c04903054020342449602a640ca40b41d4640e403c03454841a11130113001c0003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 261335935 1250 261334685 261334687
    0x2304060b0d0f150f0e0405120a0f080a05070e01110c0406060c03030b010201090305030105041a031b090f04030203120c04091a01030b0d02060a050a021f24180203041a0106090515 78
    0x8003104400c2c107840740895040c251100010303203640c02c062303007403c40241e001001d142c00010150340c9103400060840302000180c8804009540d42044001034580450380300f0009817500c004805250f000312142c04c2000303a45800c4400c440c0b507501c0410300300c80840e0010004941c0c15000c8100701903141c0038400d404c000a100031300c041c01c204c0c1d03000b0b0300c0c50006000303840c41103480b007104408012404200080d22a0300400315804500c41940404501c40c401c01201e02540c0c414002405c040c0300c0a000602940d0b02d9402140f81400f241075021101c10050100901050700700000160b24460b401002171b0107008211000c41460b203a0005030450381100c8506004030300090000c0003503a15401030701c1220300141411690365080d00300032400c0c007030368014810b01400012a240c0c59170590b41e205008940ba1000055000c0e9601031110503c0705030352146090a441d8002c0101303110f40940c01568000303100350f680c03010031915513024506074a000d82044e400110044030400c444c1c64907281c1c100301c40140841503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 261337185 1250 261335935 261335939
    0x100e0c0906070809030a0b01170f0601051309020a0b0a0f171302010e0a1205030403020103111c180f120f0e09060f0f030703060501051005042304060b0d0f15 69
    0x4284607005160300504001c40104c2d108646032400e00c18142d500364416002d1318250b85800c0c0a0310400c5144480c105544501a0503042180000400506032400240082110031280301558080e10505038120707003051180000080c0d61081c0b10140c2141101c0784c4880302c1c002c803894401090001c21841c0d885541c144d82d814810b42c0010040150225602880e280b0892003510740400c0300c0c040c0300e5110102e4903280c5c551040500c480400503100743d89c400d82c0c09015649210070081c42030f00590b034040344c1001c000c10103c1c048800507805210882c0c900070000c2100f100d952184050b2850102d0700b5545000c19800081190798408030365504081c0904000240321001400b160708100700500041c0518003a902c1070055982e450114000040d004007115081c0b5100d180c810007400f400e100e0103001e010884261a9002d000d80309a509640c00c0c142c1e034412503003601d42c1180d051000b035035440790442d5447c070002c40c40e08902c90040c403004611010100b02040c40201800840e09080b0050800c21120401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 261338435 1250 261337185 261337189
    0x515040308190b0d110f0a030b0a020705011d061f08070e1005060f0a02060a090f12181413050c1b070f12111f0f03090605100e0c09 58
    0x2007030300a4040410000342c0c000c0544610020129050116071100303600346407000b045440c5d0040c1014003800e6921805101c0e40509020020110b8040240117950181c0050050291980a01440c60180e0004079006400358407615055684403845000340e0420002c2080503141c00003095001c070501541c44050600d418206510795903280941c030781c040a2a0049000b041e882d2440e00301030900144100e940c1d0909080c404680d41c0183c0420026000d094001901e65902d8840c044a20360042c504246503281551b84401580003406584188904030104001500007410100c1c054442c0d2004407201d04100004c00204008145000c1c6500341828100100d03c02403805680000c00300e88003180b00c10013940506401c0801ca50012070089841e250300080485260404054440c01405841e0782c0c01803590a010004661004201c0141140580c40070014031841d07070345003c4011450001206207580e5105000d9400030390702d4010103104c55009209082000d50000d800000c0400f68600c1d10103c140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 261339685 1250 261338435 261338447
    0x120c3903030e0d02011e0503180f151e01030507090e0303040f02010e130f02190f1d0f030a050102090f060a0806011b060203090601031704030305040b2505030705150403 74
    0x10a60f0040480d11420011039010f01e88040c070380c500e007020f82c482004604130001c3c820340080340e42503801080720301d0070720482c0030100d554101ca03551400030300300c1c41021062040310035202505910808020b420101c1002440e00040c60103076105001510200b494003c0d05825206c00c0781a140940c1c05c10400d0100065101d102d20702055420300b002000080c6443c002404007400341e000000040c00c1403c582060140d07a0700514140140c65940b03991845001d1301102c0070003049007403401164580500412418007481d2031400703040014441d5030380c00c2423030700032a04103050782c001104c0c00c1e90085418415443c095000172103481054440d02e05008400c0d6004094504c00341816040c00040c00007002c0040c001d41740240250703004201590f80e81841540259240024401a204140d0030421500ca0f0155030007158103d03901640d91a0a0900782a0300941e582e108200400d4a99030442403903d8208407001089452800382001e1500c0d014682452414410508503140600c00c440f000c000010750040703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 261340935 1250 261339685 261339707
    0x90e0f1b090a0f06080604050706140c520b070203190609120e0a0602071d15030706230a0c060e0c091008010f05060d120c390303 57
    0xb8000f050401907100d40200805068011000710f00901d0200400d202c0d00007245000c0396000e544200304814014454941805400c0494001c0d401c12a0400b80ba03164640b40003400b8030031252a0400c8001d8185100348007420402107402410f48050801c120b0b50000e1510b000401e06c0c103601d240742c50f0403640043e850300c00b0040d041007142c824000003424800540d2003000c0b519403110140e050004800c1001d81013a440c2140d40b44035041c690004200d0500c0480c0c40002c440100021180c0410b0604442001e1080244180d1b26011400303601d000598003003010b20020051900c2d803001201e6040410380c444003802c0b04030180d01c841001450201c0c0c0d805400310441942160000804004101c00c1a00b807404d412901c640c03015441c0300f0f1003810b0740c08440010840d40480c00070010400036001e08000d5a40031960154081c0c1c04811410110711b40d6040660f68140e545007008400f80560b0b0303221041d5100900c0030a81c8000b0300d21908242c0c20040452103010792010420300654903595002b000c2d640380d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 261342185 1250 261340935 261340951
    0xf0201050f0f040b0913090503030a09030c0c0611070609030b04030309030c0212030406020d1713030c0b070804020a1202031002090609221506020304060f09090e0f1b09 74
    0x10a00c0c00d9050141c00e4500b04900725010300d9a40c0e0755000c0b822210340004803254410040300c403a10000c2d0020340325940845912030095400c5a503500c0f00107006040d031504c00d0382071050301000480003419014500b4060410380d1264580940903120315450961143c1100e4103201858500b80003041d114214954000c0c0c0c0351a010a415825160484410702c0791200250400b042102444188a000c009402078508980c2211040303410800c0441c0c410384000c04900450f04580c0c0454100e13001c003c02403034201d0090606031200324440e41c4405100f50100c4104001883c0401803000f140785c800321000040c60182e044050505e003a40000351106030901c42d2810301940000d0a021544400f070a46d09006002019060117038080303441684420b148424082950b840c01b1604440501c502c2020f030281c0d01140c0c011410607044c503030f0581e80424a00c80281c10700034009070019005010703005540528003000e000d40b900c52072100c80d541c42c105400407641a9004011120030b01a1103403580a44d01c140c1c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 261343435 1250 261342185 261342187
    0x220e0f150c0319050604020906160203101503060903032703091203020c04050603011d060414190b06040b0a060e0a0806070509040911030a0c0312140304060504061409070905090a0f020105 82
    0x5e40c0c1c0080c009100b507d04080c0c000001140c22201d202050410300100c0e030003501039400070084811a442110304d84000c1c4201c0e210501818000b19013141cac004520380744039080000b840c0c0c0039400b4000f46030111001d400c03500c1444c186c00104059101e40b141c030092440b041d4000ba0055280d401940796151426480e004680e02c1001400c5590250031165483c4282c0e1781c040d810160007050103071610422036059640c010050000200e00e500000d030400c0c0c1107200d031b0040070b090a05907a8035160b180c005c0d008582c40303070b1611b030424820b0362003802040041801c1d84031040c1c1210b880d030900803110702c00d500425142e0490302c204980250010308481d122681110001510b01683c9060b20303001d148031440942601c1038806203400c00105074000802e903801005c460300d0003c811001220081e094030ad01000d11102800030400007045074200741d41040c07260b0340102c0c0c00700322039143c040580002c480050b80d43e48a000d042140d568a4820284c00400c4074000c1d0a100303041c5d0300c4801d0102e40c0303070100a0402c60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 261344685 1250 261343435 261343441
    0x5010302131520030a1b0b04020d06020c0102040b0301090510050102071214030a111b0f040b040f052502060c030403051b030a0f0905040b220e0f150c031905 69
    0x4401c8542620395070600c407105075210710f4095026900c0d040800315602040134016020f50414041c4918890254040c1c144c0c9803d580e141e0920441051f0402c0840e4115000d001d1101080802e00103000900410f60003d6140c0d0b240800002c281c0d44040d011a41c0c6100200050000340d0707010410700290344108602d10f1010300703103150501020b007031011100c4460002007140303050141d01905c001d44807010002142d00c0703901150000300d00a05841c2c550350340002a1000d0380e800d81130640081100b00c03c020000030b070b0048081140005d4034012120300325503040f240d04040030444256405091007080b440104064a4540103401c0d403840041c20140c1031002c04522400d6203284030352915003a0711188140d0b0307140d03c14075501400201114140c04049400541d000c00d407410203100d508184100240aa07000c50124030700e2250290b0a040c0612441c0d843d521106419901003241c0b6080c4400440104100d200b4589070002d403500207402a0102c0104209101d1540c030482031209524040c0c5000180e151 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 261345935 1250 261344685 261344687
    0x703121a01050f1c0c020c033007080307020601030308010f060503010515090d050304180b030309010f02160e0f2a03090106050a0e0f06030303090709021c150f050103021315 76
    0x7008104130f16108030041c082115035500b150f0441d04410415800b00c1d080700000780101900d0756001252010b82d40d049080542e1031b10500846401c9400440480703600e802500c2c0c503940c07055881240c0b0b241c0543d1040c00101b0815620501d554010f0000c012207000d0f4500303000e40204188018880c140c440d081120611940310044021102004002440040302c0146031902030380302d0b00a03115510101c002242014141d1035140a04078240100601441c41c201900c001507030161410001c1104500c00e4600013210101119528006408961000c54440c0780c1007070808601c94009164090146104070407414580600001110701d41c8240d1002d40c4a0b56005030240c010301c4103900c12680400b901100040c1d0310080c0c05028025403211103c54055070b41c60003410750701e100030754044960740d003d440c0800485043d0390180600f0503500b16110100030341030134500300303407429041c044900c05c00a000400c0441d04610fa00c200031b003000c0c2010340c240311805c690b2401d81c545511403050300a60002641142e5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 261347185 1250 261345935 261345937
    0xc06010b0405031f061d010305010c0c02010f0513091d011503020a0b030901110d0c020f151305010f051609090c0504030f0f0f110114120103171b030703121a01050f 72
    0x2d030140c0c40c0c480d81150350141b00c595911400f8402600c1c5175290008014400388179402180e603523030301038580f5503000252040845255000d0582c004102d08100004990460680103680d0050740328211122122080d418a90844020b151b0321255030300160410401a10303080e0508003114400e0391140d803680c0d03079558518050100e103d0044818040000c25072081c42c0c03035a0100b0300e840e01c158211401600540c0d442c50f914010101101d41c0100c13924006800d141c2c0010354400b007a44550000308030841c14022141c00c0e543d0965189034420700d10180c082d85160b01000010007800102c2040c480c10400c403001030014407c0e0300018081089124414040c4141a24000c1c6400d5001004804d140a03a00303200c0d516142802c030b03a9000a01000040d41c9480c2010180c80c4c2c20084a005010300c1e07480c6981d040141c03002d88400d0414110148803929196100d50030000e000d64490005d150f98030a2464001c007505407150803891620b10f40781e14007801c0602c001e84031203451400c1c203150742d940b000c100d0f0076105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 261348435 1250 261347185 261347189
    0xf26070504030c1e080f0c1003060f08060a050c0301060807050d0b19030b0702010c140c0c0319060506060711010309080405060714010b06030405060f1b0a0201020c06010b0405031f06 80
    0x200c80615030b00021010040807806a440d100d80410413030440e150a03110344c4501c8000011038465000200301817691801d03480000090003541400110165183c945000201055010710041d40001081104200e03103805403590081868000301d04d10341c14580060401140a80500104200440ca02941412a602c00391580000800043e40102c0c00424035000a0803400110340c1101004007041e4101d005010308600b00c07150f42c03200ca0440310781804000ca650841c2490310864840c0c0507030f4401d1501c0a10001444030103546140c80a4901401c112043d918080c1060b4001ca03003c03c10031020841610714100a07000910700400d41149504100c9064000c9400aa503c644006407030820000f0402401c2c8010140d80000e0280d8034038801008101d001c202c8002c2c00302e40048c000100c8001c1c000800d640d00c441c005e0708440411314100361112a03500210b54000c05070f9400150382c1c3e4082c0e130030040707180107240c50700203146002d0804011035111101d403000c06549502440b08e0000c400c03c41e41000c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 261349685 1250 261348435 261348443
    0x302030d0e0c010201140106020d0c15050c190e150c070f151101050402010c081b0a0f060528020a03060308130f09020c0a0308180f0d0f2607050403 65
    0x855601c01092070307922841c00c000194003641c60031458100c520b50861000381281c455802811000d14110b100f0340782030244d100200c0301e912300060424842001c5200782400341000c011801e80b80d020070004100901d082030300507814041d03015640101c0350b541c1d4441c0c01050000840c05070305c481d00640e44500d004003940200721400c0d0075130000300729490016815030316140c0341d0750344204410152004508a4100352400303400100c00c0e601d1a00454035142c0100851080400703141440c0c46071040d0281031080e8a50120743d0107148135140c1c42409440c0c02040d80044030080c5404001c9022901c2c1112200d14008410b035050300428045c600307501039448600116004011565514940c270700d03a06080d08a03004440f4441c8060340c0103d40c0d9011442902c080c5e070462030080c24040c20541f025624000006c104054049041c6030140c4908410f220007032112084c20000d00442000c042c01802c085282c2e030020040040c0c07202c0c031381c001e1800b810042d01d405d5040b042d551129140c0c050100c85610031508050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 261350935 1250 261349685 261349691
    0x110909011701150b03010b0c030c03040e010f090e0615120709020a14070c032d0c03021c1a1e040c09050c0412031206091508010e060708130302030d 65
    0x16560712000c0480709440700750000b0407903502c0380d080c01441940c1900030440fa458050005100b04104007000b00301140d41315040302d08111307200c1c0c1c0c01c07031450740590807009444010000411032201c004240b40017500c0e103210140407403116045c01c070760b46000007400c0520007218036030f64480c10785400c076400205134528016101d082c0d44500c01030380a940000f07a103500040c89070115440500d2210207035440c196002911100c0c0d28519110382c03007006040404158241c60048545266507c0c0e403483c01b60251260318140b014074514010030040100b0003010000e68000c440800b00040c103840e030f5100d000c103c402c680c0c42042d11412404c00702d0b07000203d910380203070842905100600000c00c0b404c4085840b00704041c03186503a22200040349000d40e104241150302d03840800c00019004180c032000030400c41e00d00103141e690b180c5041003a200140004c8251004111b001e0000395400c0c0a01c1c00380700b80b2200182414140180000c0256000400079100714411580c03600400d8402c0c8119004400610018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 261352185 1250 261350935 261350939
    0x20f0a0503010c0302030f0f101e050d0f020109090203100b0708211506040b03070f1107181404081903090206030703060e070306030305161a0a020703091205030d11090901 75
    0x58001d5100b0341c4c40b13100559000000408880201103e03d11580040140c030903c0c0c2d00e402070f003100c0c00c420350307410288050400201161544660701c1040f80140108dc0009020207540000340c910121600082c54890040081020708901841d04000b1101d08002190352003030b003800c11881600808880c20803581041c007036500200851000c0794080e0001c4101039161100c1001044030301d11442c4904d407040c840a00c00190154080d02000c0d0780f402542c10070700e212a150362410307030500b4559008a200804080b5030414110304511402c0c003c135000140782c0005013865103d2100c24040c004001007010302c000b140301074540c402d801c05444180d000c3c02c12905c0b8180040090050000d0780a07030f40c002000e002c001412a482402584200e0360584c40e21480d05e5800c44005905c80d0004e0019643e2501001c0f02d40121034102070718034811b00b0404001a1941303202c0ca801020300400e94020002000c800e51b042010400c040b0403162404806c00c40014040300c9014212024081d00685d11344c00a00b0f4800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 261353435 1250 261352185 261352187
    0x150e0d0c05030d02030301080c210a05010c0212030603101503060e010614010e0d110a0b0c1c1403070c110904030201062d181d0f1009030804020f0a0503010c 69
    0x32410680320704400b503560210742d00308101c4c1d80340002d21415401358041c80041120f41010400c10402818511510071965080c245440c5040e034541d1040391300303a41d18440000156810f100100170250b0004000f4030718284840040d94910000e145004440c1c2d0b2614038240c2c2701850b800c1640210f1b8098411f00c04402c800c00014000e00481c49001144840f0b050144000d40c031903080000c22600040c1b44a088081e262100340c40061010900e5821110b002d20104040803018090038000004600800ea10b00c1446040d540c010111a0400144915815400440910307502529400b00440c039001c6c00d101300c607043c40e4080702490f800050700551410140700a060313041d0032050981e043d10100d0ba41d100318141c0072902d04d07030289504420b040318106040c4007103050f071000c07104004200d58000c9040d11141c8401c210390f00034000c3c0c0d112282d11418100c08d1419040c40b081a00e211161410000401e80b614058520500100003d1003004004510705044d0795079005a009000c02038020081030b094014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 261354685 1250 261353435 261353453
    0xb0d0b07091814102603040513021b03040806040b13080406021621030305040f0203061e010501300f06060302041d1509040f0215031816150e0d 63
    0xc882e07034007800124002200c03040041605022149003128144d245468544903214400b03c0020100317543c0020040014107982d000c440b92860781c0c5480d00146e0303650786002d0101c141242002d00c0301c1380f0307001071000300b01400c13011a070f0540c02a00304403e281299070704116030280007664800200b400101007004114a81d000030b038003140c12010750078a46c40a8650b0041ca465030f1404002e6105043e80141080c0021f1203500603a400c6441915100c038104140c0d80000d041140460360103e0701013048035040804584401c03d03900519082c207187c40c0d0100b4086040e180c290880c040c0010313070340c114140180101320f030b42e00543c10488050001c00c00c7c2625040300501940c0f0511641ca0502d108079102100440c0e4140d8050040480504420055080d54107104940c0c1340104241c404040c1100407001607207a001f85c3d541d103051059515aa00d1070881400111550b10a5400700e26034400c210000d8a50541e10300042900d0f40500c4030308044a84220480756080803040080c1c126164911640c00c00000b08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 261355935 1250 261354685 261354701
    0x221030f07080412051303021f080c030606070f0219090b0f0312030f070c0b0f0106030f05040f020105030c040f08030702040e120d0b04020705010e060711010b0d0b070918 75
    0x5420030001d03107402204030740c02402594080c20707140740542d0b440e14881c0210010040100c601d901c1614469898001038880a205070b00007a0308040080c55001403a40202616440034400b1241e13401c4d420180c0204000c1e01904000a011a00081c48101595503101d01c0c0c0e10100b504160383c0180903240c1c010b0a000e003000355241c1e802010522a81c0100d480d02082800101ca001c242250442c0d680d003e00740c0019001a00703160a129030707010240007080c000030010344103041901d4590a00c1d4900500142200c80b20190707420514030304410b00000903030b01c10307041010070380920b00785840e5110180e40107001c3c0300e107620500204010399400a040200403015200c0c0301c4c000c4404011007031011071240d8035000703100d420b0750001c0c50400120b60015030540c01000a0034001c1c1c401810300c1c402d030791107500b1242004120340c080c4c0c0c031040401c2207540e405100c0300503900340350000f071024182e0100480c80c1804280340c000c2020b030242c400129903030320542d2154000d03d41c00c40b0350387d40c20031101200d00041020b5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 261357185 1250 261355935 261355951
    0x30b030610030b0903040308030a151e06090b0c03090d03120c0c02030f0102031012050703140307060b100c020f060c06040f0302060a050c2205031f05010e06010c0201050a022103 78
    0xb0f6400507808460100956044982120200e45543c0d107004450004040e022081894400caa450218001807034000170402103c00c07103440303440941000b4014004100c9a401088030b51000c101001d11202e0100a64060701420350702090f81c809685004c5d1b424890055480400500d003024280406034000703503c8a07014006d4080d00c4626a0000c5d0941c203038403049401200e00301c8084410480802d920069030344a034041c00503640002e0300d9a0751703031101107020120791350194008501a0140320700e600c0b03082c40f200320485500e444211f4202c40640001c4c5aa0300180c1318400180c100c161a807541003c581c2c5109007081940c6080c907062500d168040307008101030700140324000002d051b000d180d11400c0d0269250203541d900b0302c4c4040712000c403012904001c000c5002d41c074032400a2640c81c1003107454900c04440c0340b9100102641d071040c2c01181d00c143d108052030080d81d0207104050340c000c500c8032619034081ca401079803840c101c0000d0b4680860821881d01e00144085040e801c07146640c040d601840038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 261358435 1250 261357185 261357203
    0x309050a0636030e0907020309040f05060f01020c1003090c0e160212040f0b0a1106070305060f0405061507020315040b06010806030109030906230d020c0c010c21030b03061003 77
    0x341102c14590001d00050080c00301c0c0918858a4943c40c01c12001a4003842e284100c0c2d241c07014a0300400e0aa81310840200b003e42e03215002e1101600d4151721600815400b84001d02012440e0f400041a92184400050903d5643c580043c140050884100e024048000c00c050755420440e41181c1d440605016620043c00b07020180c918143c1d41404407400c40f00d240c4c1400702c5440c208410710342e241c0d22030300604042c880c071011080f811801c1803020341e1003400035850000d018588201031004181100b0b100c14030452a090803c00c440d514415021004258001c802e41c03165190b03c00300e440e14095043e003109103c1c01c102000100006880d031144114001e9944c079859440d200d0900d07003a034009a80040100b10344403014044640b0440d00d40302e0300c003240c28940310300315580c45500e88243c4c4042c1030341c40340030340014140f00906420052505031800030319080910081e00c1d160042000300c0b900140800320a1980c0c040c482a200ba044504044030040542e000e60070901c208001680782c5100803140b44803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 261359685 1250 261358435 261358511
    0x303090105010b0f03010b092107060207060525030c0b0903031e0c030a0c0e04090c0306151a0d0f050c030a1a06090d050a0f12080a150302010309050a06 67
    0x42160a84c0d20020340789540341c0c2142d007082c00707c0d90990054060160401401543e18501602d5451041642d0010101910f012400d0903030003420500c0ca90842d100307100007080f103000c0c0b50303003404000070382085040c1d48404618080d107030403122030001100c09003218030103405001c000c0201100075400380e6460f05518900300443c166400d4000c4049070032120b0300000340001103801005401000340700013186080104a0708030380c00281190250101078480582d0044103200308592031040d80503c401d41d07034000e20001d00e00725600650509a200480c04c1460200380c8000b840c8030780c1c02040241520200500280c60000c0c58442507800444501a1283c104000900315001c401c440d4402140f020300480d160101e510180100703144040001c881910580d0240000b1401017944101000d100700c1d8000702e1300f192210000e02800005d030103500c40c1460f15184000704030a4415220403a58203090101340390b89142401384c24501e00d980040d241508011030f002d044003900d0002c3d034400c0854480704e40450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261360935 1250 261359685 261359699
    0xf1c050303150a0e0103020402070f0501060b04090e070f0b0c010905030a030218040c05030a020903101803021b090406050c28021605130213080a03090311090702071a0c010905030309010501 83
    0xa4078074804c9145540300d0400620141c14503070010808030b8060340d07411041c2c6119595050031641550b020041c80000070a042c41f5080003800303a0075056680e040245410350400c024881007082c68819000401400140004250801c2d0400440c0c41e4000d400d8030740b81d403000032010f006075005031403011003012251807078200e910780380c03007000030601990b07541c0340c150350b00c00350f140d4000e500040c09540c5c54816400b101c0c035520101d00403035001c040500300e400364a20091130701a10707020100001040c10600f030701250351a5201c2070011036120303420250204103611008440480d61061000308035000c0540d401540d00e688078040010300c0511180c0c21603611403010001c4248021203401101ea03c410081e01e4041c035200c0700d401504802860741d550001240d0342d02491850040e94500440c0401c01c140000c00c14071862103442c54507000243d40703600003031420b0724000303440744080d01405841d1000f40002c00400040e038420369800c480170350001c10440c8081c1c105150b0b0f039002155011300c590300348000800c1036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261362185 1250 261360935 261360949
    0x60708070507030e1e03121e0408031801030902030f1c09121b050607060b093402070b070501060f08210a0e06030406050402010e0907020703020f1c05030315 69
    0x20f426550b0881002490341c00c000805858203e0343c440551014944d28031660103020844452101003442940da030102e2940b42c05d2800482120314407404244020428468007000301e41d552041349040010a40700100168020900710702c0c00380d090f22514200c80401e900019041c425960403c0e804003206a05110480380d9240d540034401c200445000d20000040c050720700f2044c0341544410340c01049880e240400c07a650011142a206603485541012a50414800769500001c0c40c004850483c5501401c852144802a01c070305261440d800c2400803442c400e0118001405280708a00d0f47d442c0c56051842c00b81190b40180100c080c3c54440c002100c140002e000b03a4403514407451890800c1c0d41c89426243c07604480804014420740c08a161440e545e0500154407840c420b140000b031900f000e000041c80e500c240000b503405801c2c0c070000c2c0680c440e000500ca4003141d0f4102c0d00541c1800007040400c0c0c0c42c4154501008084500c044890104100032002d14400c5541340d1000d462290040104801c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261363435 1250 261362185 261362197
    0x20a211505090a09080a020a060f060e06060903010e010203190609060e0c0711030a03200d050301090c0e040504030f020d02071d0c0c0a0c050f0108040515090f0f0607080705 76
    0x10410241600300800d04001c8a02c41d404030760311038001045021a102d941c80ca50000404c1e80041e0404c2c02c005081002c94031540700c50340c1e0209070402a150909182413041c40c40a0031080c0301e03003404501d444c4269025002885080300c50706c025510b078182504c0480b4104081403d910045041003401300c1c07a455940f203500116085c603051106640c90340041181d60b58080141920210881010660306440030002c5449042c840d0b80d48203112030104030b02c0581601000d001c4c0c0301e590004400c081c00e8541c410706581c191100d2481c0041c000080980c1a00c44000750700c1000c2d04282803500300000d054100d1034001c00c0070b01d0350b0203440c81c2c10100c0700120307110303800350040c90403030951404540041c041c4600441e500c520082c0701e89180100d5090b810745008804841216880000030040c0f01c1800c0100703012112950a00303000c031113800d00307641d40f54451080008901010790600001001140b04001a0071000590300941d010708600400f80c54440d94100e540380b01280c1c0000c00305000501c16421141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261364685 1250 261363435 261363461
    0x31014030703060902011b030509150a020c061b01091518170912100608010c020a03090905060604030b0103140615011b020303091503180307020d080f0d020a21 70
    0x1440c02c5507603100c0140500d260a80c1080100346811445520b10361900c000340d03010307884464480401104114a02000fa00090f62a41051211807101c0e900050000c0f1804c0f0201c454036220704980143c6c090301c0442c10002c0c2da4540c240300c0e0401c1440040522101716241004044c420a40080d01489100032450300042034001c415046062540301030f0080c241ca450001c040c4840480b44c1a20301d80307088010410104026074884c001c20001400348190b0f00707006641d00282403040f2042d10302038480381852003000308440d00d54001440994401d803c50b0302450344604800c481d940c40e41000101c25603201006009031103220086500043d88020b0352501d124140d48142d0141c0c080450526100c1c02201c08030b0300f506c0140086641e0b40d44009500103018800000d280d143c0c6841400c82d001070030180c60324011500108001c07405a00d803043c0400900c3e411050513982c407240c10b0082071041c80381a01c107043e17082c40440c04004003a802410040d403059800b070301d031300d12000d0b070502d1008940200c00881 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261365935 1250 261364685 261364693
    0x50306040203030703050711090a0c03050604201c02040b1201050913020d05010f0f0207050c150f0c0703050102160506060103050c0a1b0b090105070212030f192003101403 75
    0x800081c1c446e1000f0142d0390700c611010149a4800c85c0820001c0704141c03010b4000742e899140a4609a40c14842c66a1284d0111420b0003070341010740e090071080c3c1c100c482c80300100c0c1d0001000001e403aa42d0b54404068602c00504641d120707540c902240294000f5800c030700d41c2d40c144000000341440d1400205002d080340500d008107018050382001070010381800202c0301175484504c44904515035108008040da40e0b4000075a0369103161a00d42d00b081e00340d800251144142c40210820317044070300183c0380051000300250b5038401c50350118629241c03003a44004c0140d800001d844403071802101501d001d8510174400c0b100da503110700c0c0041d0250380742110403407c00c05041c0041c0c24007500c0b40081411414648102d0794284000ea00c40744121002154101c00e247c1d152401e003c152641003200290840420004a0550500840e122142d55014064880011007407084840107402503100c070519612100841252003e00c50b40382e0f8090308100c0ba41d0b642023891400010716291102002c80c200310004010b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261367185 1250 261365935 261365947
    0x6080a0b010f030b010219060e07270c17040f0627020f04020f070b010f08030313020d0c080f010c081302090f0c07080a03020702130e0c090a150b031005030604020303 73
    0x103c0040194480300390461003154101c00d07426500c402481c0085d8024480801c0c0c6e604094000d03482c00d0070351f501800783c0c1038000b00180400254042c03049a1000000c40c003068010300050304131044140d61501c840a0208038090004220315138680040c00307441140240310341d244000800102007000b0800c4916103000501d40300041c6404400b50150b00d200910042c01c101640c3e1507020f194102150071501c2104401c01400a0402807103410003e0003071b04015842c42c07504e0a040c078102c0c170304140c009001d1401480030808002c121103c0c0c41c00303030004c1d5040322041c000601403d03018001c03024035200800d000c107001c01c0c4003c26004420441d181c0150903840542c580d01804120740100070a00d0041c95010f004480000c3d180d42e00902e0007111a90780036031501d0303981c01080071000d11302041500007480c0c1480308410b02e42c04100c86455800440d40c0c44d94656900c441130014082d601704010b1000c4000b5030210345150f04901940c060054094800f00854581c824182e484000743c5000e941940300b4800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261368435 1250 261367185 261367187
    0x70e04061401020a0b0414240108070b070605091f020306010e0303340812011a07020a09330303020c060403030801051021020405040e0c0901090b04060e010f06080a0b010f 75
    0x10711a0001d201f20691449041801c106609010810101d8034640c06051900b64805900c040141d001d449520003810074980383c9440c0e1801c03807080d030400402d8a912040083c0141005008071414050b080441d44040050000c00341c0003944110703115408240c0e210440c0e12941000019940c0b071031603051340c02c84059030000719401c0501d1040c0c14001d41505403000440003450301350142020f0112580194841d50406d40c0402400700fa2440110000c841070100c4000741c1c0d25a04520100c8480320030008038542c000f403241c0c0540009500112180100440240740705080d49010303030071240a0b5003603420a40d42c113000c20845104911001d000a51080018000d601d4003031100c3c0c1d0381800b1810300c000d504c010200c981c004078150022540c01c0d20380c0441d0400260801340900c080151400011f0026500b0540010b480d001c4103002c1c4002c0142d41d11009080b03920386074000030243c1030403e4484081e42e035403030104030892001d02030a070024000c1808218444c2d4503016030842c500e03050311682895403c10754 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261369685 1250 261368435 261368453
    0x21002060106020d05161a09060a09030c200909100b010810050f0a15030f0506030c030714040b09190b030a21030906240f06021203090106030b070e04061401020a 71
    0x106d255000441100ca00000e5407a289809544c2142032221540c2ca040900282040e40003401c1159031403c2c03600b1000002e50120036888142d9104522080b00d24006031035070070107000728031003581080c1c0c03020900460142c0002c9000500324004400e00200d1618030045484403400c0e511041c100003092401d010724a4403628054600704058541040503039603441c000802d00e0310f0050b24001c0b96440030841d80441a600030140d0000b01038005040305000d03e40400e070b403103140388904180d42c24000b80c4000f0399a61500850b1111000030118036490804500c2a41000121915115040c5c07920300302103c10f0501141e5003010300e821070a0a5101d0011410b40c0b80c1400c0f032040c141c02059900c8400600052907845a9542c034210110805001e20107140d207800700403102d42082044042680c020801164001020318080d14860f02031500d0b07460312070600c0d0161066800c0108a41a030104110041e80c1c0416030040d106021102444039540e1880042070201e1a014040e0058128459101c08950410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261370935 1250 261369685 261369697
    0xa0b03060402161208070305130f031202040906030803090d090305060109020903010b0909010e0601050a0f052205070f090e010509040206070311061302010311121f0503070603020403021002060106020d05 89
    0x3903800c45048805507904d402c60007010301c003a000b00e0314071000d00c5102c0d07901d441040c0c1e203d40508100d601115036601d50a180c4412810300408006503601d001a1291854050307800078142c1c4c2c0c1003407082e42c1e202d01e00a81d040d001110840e040303208058004010307500c101189412650890302030810740c0d0a102e12400a58441c0e03007107e416640311030400441e0b4440f40c10742c500c20054640002100c00c600014542084810b074070462142d54010000e100c29442d00e2100000c8984c11a100c10064071040c1050011301c401d0601120018a46010070003259008005030300070710400e0b80c9000506403900c03103801c011031007130181030741210400c1e000600604101004203240c50081c00d00720180c11281407018070301300d4211080810003919009000440d40c1500560103200e012030060303814482081e420f880d4500700209402540f044034059003c12140d407100380c00207401c020381074402081e00c0360009000ba60261100320302500e8007170011900355102181080c140c80c01d41c0c1c00351800c402c403403000300c03060341101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261372185 1250 261370935 261370957
    0x50c03010501061e0c02180105040c030506030606040b1207030c05131820030f21040e13080f0a0503040c05030a020108040215040906031208071404050621090109060b0a0b03060402 79
    0x5c20100300260792281c8485508004210440809604000900090f100b03440429410701d410202070004075640480c03210b41c02401501d000400d200c00c440080e2141062000c07124541c01542004030500445140b49010390760140c82a141c5100101c0140e81102d000031404080004490046000181020400900e402c1038881c01c460500c42c10700040d00340404441031200c10ba100300c25000d8000d003080600f540640300c5000b0315041c149002c03490442104010400b40d44280c448200c08104145c2c40103940402280e01080758407101e12110140c40c6034003c1d03078151101140c0002c00074903890001002c02000c3e0341a0b40e4886661a079900340442c4641d07141c0c081c1680482808085411038145c840e2200460081c403152103002190701c8040c01c2810b0240c62941040a4080104550321551048504981d010380d5040c1d610680e41c200303a81e21160958141187c48403100c14024880c0054000c4a070a0f0b0264a00f0802c00410a00300304064090f44142c10349810b051000401038a0290f01500c0355440c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261373435 1250 261372185 261372197
    0x5070923060d18120e0f09090111040f030b0c03091b030106170102031005060406020604171b0a0c0807080a0318050315010e07050403020603040b0a090804080a050c03010501061e 78
    0x105105400541c2e000c1c0000c9041283c1c44030001013801140307800804181c0140c10102c10348510ba030042040d040d13165402e9401207100390046070351040c0c00d41c01241c01030816544241c496440f4640c0540c407018078801503035140c0208003c58840020001102e0084070228002c005001c5055070030855111082d049603810b540e034840001c0c40b1016003049110790600500016528541024602403903040d50300580d02412042c041400083c0d00003500715085030b000744007805200d00414001442d4400c1d061000c84040039000e28200403400000d00b41c40b0148140706440545480364a0180d8400803132040c2c2d10a90700c01d01500001c0381c005da90581c3d454080034400b0a01c8c40c1c44102080c034014032641c10990034264140104500c2000082480d0805660302e1701519240c81d50300062164003010340080d20340c0c0c000a0110384078907021b41c03100103400c3d8800d800380d0315143e5400400e82c6842c0103200c1540c942c0079040c0611030354074040c408c00703058035060b131074091050302d05909807032a0841907010b000a100c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261374685 1250 261373435 261373447
    0x2090712060b120c040317070804090915180b06100c080c03040611011814160801050603012a210e0c0109080a0f0209070e09090a05010507092306 64
    0x340c80c0902030140100d0a07955030b88014910519600e040000d289804410040c4018000240305200c080910002c0c100701607240c406a0500100600c42c035844000f40c6807905481600f0028401640380c05614062000c100d0848501400300041c00b090000410844074000042c078541b0f865034801d6403910040c90031840e24540c50f9243d4100c0e0380041c25144140d071004c1003c103e02076210660250410850000380524414410580800403200500030f200e11b8510b140800206000c02006444961481d5a080050307034403ca003600800050303a00c1070080d400c0c140402824181d00c0214200302000d0030003101d0245030f0300000c54912241030b40c050401409441c403000c0829603801440c6020521a000d44298040200050f1000030b0b194442c12030f0303811032800714002c01c1e43c0740100816903805440c004160b94402004581440b8106040c030340c4102d81405001516000260030110144504001c20568889000644140c0118419850189480400081e0b4501c0c2521100681c1d0006058641000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261375935 1250 261374685 261374717
    0x201051e040f05090924060105070b0f010302040b12030403300801052d280314190506240901080105070e0402130b0906090418051203070804020907 65
    0x7502503484001c458030492414895444c0445200341c2009001e001032911903191903020b901c01d5090048200003400800018506902900440d2440742d4845650604c92410841c1410402400e0005030b020302d1601c2c0c5407080f1818111804914001030200a6040c24a19940c90340c03045c2c0a5a13049010328134040a40d103281251042c0280703a195240c0360742c1178540c103160034080f01d911a401c030183c41109003541060300007480d64000f48072205c182c0703204020b5220255400c07180c03401d117900138280d0403281500009200d00158440d52500240041d25000101212400b0402000c558051310541048002c195001041942180c40f58101407a00c121090124005052403d0036030212405944690400c00803946c041c8000f041c0300012a030460400580c600701c0c840f502403900810b01008000552031400f81e0390b010039907645060003802400380ba031419008000942e0f508104481921a00700c3c0d04a030b42c00e07081d060341d00c074400941e180030705551250208580c00c80c02800200c00d0100c07401c5801070b48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261377185 1250 261375935 261375937
    0x50a1515080102040f140a0f0e1504051506160813090b12060106080a06090c0c050d0908030306060717030c190e0f04021b15180609032a0102120613180201051e 70
    0x8020880270b4145a1504040d1144904a6681190311540c545800c0040301c0700903041105084006031a42910392954052840700d610380281e005d040c680010501600101c00f031507aa40c02e0b40ea00c40f400388406c11594040c03140e10880c40194030142e40042d001409620b10404019a22644161001c56100d41e20041d11045810714a10000024600c50000d41480320800c01011030240130700e08284920303e0b1821054603400043c2c0103d00c22100002c40c1c9060001c8054240d180c800d61581441e40c13810701c2c50002c030943d405160b074680d02d032802d6400118054028401c1ea05a4140505a06404c1c00d0031402c01000358064513042d5110005994050952402003018000b16105180014030b2802c007080595140d0710141110940c59000301d081044100010003520702041140c81c070160f000820310703005c02102c04000400790081d840454000031f0800703444403840c0602c205844e034521180758803020341d081e070f034824103068a00c0c8c2d00a245540154810001007080445501c00c1105c0100d01103842403203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261378435 1250 261377185 261377189
    0x10c15090c030201031103070807030506030307052b181a041e0504050c0405031b01031b020102040f230910090e06090c1813050a1515080102040f140a0f 67
    0x1440e8030100d003031045503010311500406c6200c403c2c0e80c42c1145002c1e00e0060640100802070400c140d2114007003059900c04009a54299034001d05484000305c04111a8a03940030a070806504151000f50f0f800e00c590003041c5501541c0c00401c880a001403c18002007000b240c001e40302c10f1301c0e00f001c0100051504032141c0c03400c0401d440c1804242018a080704010903030b040605001d103040c40412080000e07903800240071701003410000744403c0d00780c005001a001042c001e200020740b960440010340c5426410741c02030086c1c801e00c5a12078401611744204146e16900b002020341541604030b0700081e40d25014140303c0d4000720b4080342e0304009445040440603a90f2821448090358001014011245000c0c0034030701501500390350650104030341ca00080e03045000609100c404c50046c0300c40009216050244000710368110440d0794400781000d040d6030061a04030300904110001d4003000c43c14640c10700071101200c800520307807001c440c00d1815015000040b14000b51744003803070801c0003d00c5c00480181c0700c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261379685 1250 261378435 261378443
    0x3120d02030615040b0702011214090a030305070f090b0706110a03091e0209010512070306021201030b07020c03030a0e010201020c1902032401060503060d02121f1a010c1509 76
    0x6100d0400e001400f0b0451600d005040d400328050209002d013200c04026604081e40902c0d0422650070b080001800400ca81001354681d032000c4010005401c1c1c000500e8107406209540030001c03032766255011102016014110340c00900701950130000382e0803907070240c44210f0103840000348031038192040d0f10455100c40100c002094880b43e841080c0100b184d84201202c11100380e113130311b1742c0c0c607640091005d0b2814003c040c0708107800e503080d14640c030041101a0265074000340455070740101e003640c0c04115009202c100c5819034231200261070144049008241c1800180c000d50808154100544040c0803044069045650a104050403400c040110b03210002c81c2c40c000c20b02e582d41e01c2c0180350401c02c004080c560300404512078078a2500c82d0020f0750341110750a150094483c1c943c01c000a0000d1111600030398042282011084841000315800c64413007144079402e4040240d0203041015240c900202065200c0c1f1410107426075400703002501c0509224010512910182e080c240301203a0070b2040c256 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261380935 1250 261379685 261379687
    0xc0402180306010303080901111207050714030f0702100f080a050a09021c030f0801060f050307050f120a0513032c0a1508070e030606010c0309050a170c0103180f0203120d02 76
    0x1210110a01c100310310081d271603081174038001c440304008401c5800509011b00300000051118140041e0b00060134218203042c007901e40d90000c0d440c1061203900b100205038880ca41c0c41e01c510647c00d0040c5041004416035856440e00c6546007400040108401007401d0140c41c0c031412001d0040e80c810100283c80c0183c0800034a0144c05814002d02003201c03144001c003404000030060003920f4005e222401910031501e8495980e5594800c01c80c0d0500a850540554000224292110b8282140700b24070a10b5004402c001a80e681c1c0c890440070500c0b80000307804181104000d40e61000403007000e109a000074811004041c0d62400411074001c190b0380006804903c00095040302c640c084007440d040b201030710b02030316100f41e0400066240c040117030a41d414018028905030405008000d400300510009058a03800f59803440d414482240141e03156500c2d010301d8600440560180c4a0602524489618131068206035681c4251200a00790140d038980705016080b8203c0c50040f0040081f03043b140005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261382185 1250 261380935 261380941
    0xf060306051f120b090c0d050309040e06130605130516030b07020a021503100f06020705090a02040305030304030503090a050a030c0510110a230703030605150703020c040218030601030308 82
    0x1040620351480400c600c482c050a03030400c0705024031070110302210703004080328049440d80e02d00710345013a050f021030940044008041409005000c0301414041009917018403030f107200d1500803030f22030780300701d805480b62841d003406040031501503885598085010f007030148013040e80e51103807440c00980c0c200000700030340c4100041c0300700910110400e400c401d690000f818068451740c0020100740301d542c40b070400090040700041181040410b40402000c00700c01d0f01070016100e0000035194a110b004081c010252800410110b840e1482103904490300640038500303503255036904590f02d80c0702503c0e000c240c0c403420946c0804618140720140000d03100c1e443d10240b10525103859800d00d140b0a030056003030384c5407c203e04045241d00c0704031202003071285003842081e2120034840140a554804a0300300c0c0c0b0b404074640c81016010343c09a401c0e54401c541500d14100001980442d5105840b001401a04a10040b40840c240f40d0040c1800c1070003c1c810b100e0003400940420300d0321100740d0050700054210414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261383435 1250 261382185 261382201
    0x4060f0305100203060117070309120302130f0302030c0402071a24040b0907030e0307050609010c03050105060a050405060d0618091103160e100f060f030c080112060b040f06030605 79
    0x902410254007035043d8110300d402e5001030501100030542100f041050400140003503c039502000c40c89501c0482e01c214084a004010000d41203160b00c2d8649a07204900401e030f000c6420082002c8990050007000b0400b210380a000c06508600c03400c6035402c1d4402500e542c003500074100301d44540c69501440076404401c1c1d070650f010300d200f0610240500d02d0b000030b405460700d618104507401100c9040c04200c0d1138428404920714491580042d0146c000e5809002ca05401904030310300003015035406001e01d903200c000300320940c8980503050020030400c10041011b42000c03405001040b1140c2800a6200c4d0340709040d030707030364140c6e030039207000356070396950100104035010203250030048094004001031000e509000400420134083d10406100030701c00a100c00c00740ca00147d001d018800625240c5580e9000c014112480048030207010030b0405000d03004007845860514100c5080c8080100610ba90b912024005c05181c02180d81064961080b5685801903000c3d0f0001180700d800c000409240140c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261384685 1250 261383435 261383443
    0x207050709050c0d090201140f0409150b07030e300d05030c0403060207110d0c0609050402030709090c09050301050c0a030506040b15031e0423010e191104060f0305 72
    0x11996039a0b01d00428498041504004d45006070014140010700c00c18030300040c0c9540203024602e1600110002da132480b10302c221400780c021100c98180500c56060f40d07001c0d040c5420998064030849400900c9000f001ca88a5500e22446540140c941c41d03144014040106490b042124a90b24852020f004543c0085042041d0300704400b29140036070450805001980d000d11841c0b0014110035008200001400b0302c901d0480d1121500404040a460040c540880e201d50315105000120b8401071b0000b0705800d00c0e00031a803062394996104068141015104001028049140c104000c200b04003c1090b4509100f5907000c0c5085140c0035441d5900280002c1c240d43d03004103264080c1d401c200704c50040d42c8074200550403031400543c405460341c3d10000c101002052522141907507103078001c1800700303014914030001f61591512008040c0c0900d801040e07820382e11303122010055503002c1c1c889100c901801010601c0018401d0351702d005164140000075003910359a4000000304104c0c41c00070401c00030200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261385935 1250 261384685 261384689
    0x20102250806011203020d0810290313020112050403050904050720010f06090204031a190c0e040c03020a09030219031406010503010b01020d080423030706051006020a080d090501020405030f0102070507 88
    0x125051008c0e140400c0d5480682c41c0500c00e041c00c4800c02c4c102c3e4140c0b003480003001001d034604a848540c50303161203000340b40344041c001020b9012030f02001e04200010300501819100b0b941540b1458980a0f101c011700001f8440100380004002c0a120849103c8510300010100301d0038060001c101c42c2c2102d0300c500300710b41e030310380c000d040300c43c07040104100140d00001b20000100700130b4900c803d9940d0b02c880d034941458490401d10319030781c40c1c5004202d80c03a4104d900f60b0400302040d5010810580f00b000107401b01d10903a8818804a0700001d010030041c60714a040801e0200c2726401c56485995175074a40901c1102800d8003c16034101200610260900344900481400c0034402450f161024081c054805040070707002410f08500d0449640c02640c04003241d01c41d00001342c0840796200c100d8100200180829140d424180da0740d0b82c0005141440000c034103609540241c0c006240000b10802c0d50700606e4003980444055400b0b010002d92960140b1481e0740b40d4960300005a6541e130640340c800e050a03070765 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261387185 1250 261385935 261385937
    0x302040e09010902310b040e161a0903060a0905030c0a0f05060a09080406030209030a0c091e0204150809070302030d0f02010608011b030c121104030605090a020102250806011203020d 80
    0x1800345e402040b00e0040003509010051100040c07401005000c980548141140c7c84594810811a51189480043c84c1070468541d2400c6000603070461072a580107100340b10380320794194484000705d0b0030003043c0e0740070098075171040d002c407071621114484060400b00e001314280ea4840744028840f051020610046601942e240340030881d0b8801556030402d00c0c001c50240a00300b650104d40315410751001c0004403080707034002103158a500d5562802e88080c0c8000c070304400441803c01103640d001d0200e4000d440548489078002001c144c1c600b203080b210719400030400d03c02485a000c000016840520402207070302c980d6556500201c000c404080d0940300c541d403000312540c0c50058448980e1440001c1d10348400003a10703010070b00f0b0446031012500080358907180b01020786007400e01400000901c0c0240210f034401e001c1070005568000c8d8041e00c4440e0000041e0141c0c00c0b041c0e54504c4d81070405c45241400050b2989100503940300e100d21031800c80260408116a0342814040051580400003482d02d5805 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261388435 1250 261387185 261387229
    0x1503030503060d1b0e0a0504032a0c14030d090b090618060408060f0907060e010c0f060f0c030c0e0603041b03140606120105040213150b0304080d050903031b03070302040e09010902 79
    0x13260742d004020300311441100002c1c0d07034884000310548040a04802b50ba0f500010400b0200f62103c003444031540482600911901c1034400d00c0010310301950007002203560b040743c054200640c8009010180c5c0c414095a0f89035070b2102a080d06903902c00020b04050580303507000f0469031a0101d4040c50140c006011a0082c1e48000410480790354401c482200300c5100b071801c04465045441c0c05034800c00c003040d00904641c20b10f45a0a500840c503444280c0340041682d00340591781da20807041d1001d0b1001d42186401010401c006408074031100324855000c40881c10403100e141da01e8413900c01d1038550f407040205c2600881c00b03101d0325140c08403002e0348050303228008100070304055000841a5413050128100c0c03c0d20b507864000513000d0406a2001002015a200d607640350034a0246032560002030300d107180038900404607003e0315000040e40d00c030b400c60b416054000d010b584660055504010214020503400f0400440c01d054a100542d0082c81800c1c00481d001d52148100302c004036551078407510403c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261389685 1250 261388435 261388441
    0x21503040309210f03030216050c010207050117010b03090a0803010806063d050d091103160b0703051c0c08040b070e010c021e060307080709091503030503060d1b0e0a05 74
    0x1c2c03180710fa030001079003c81029040460b510301500640030302004600e40c4d10308890303010148800480d1010b80c85000342c4c00c2c2c551503a110b200544c3d00241102114225900c3d010050245c01a2500255004240241122718020580e42d58641c00e40c0241c02c24841138002d002445000e0400100c90121304007000301d030341005084030301510116090031a0b0711300154603980d0603c0c00f0500410881c2c100094101d4144400c5445081840c403401c0705552044c06403242c0811168030400b02c4c001a400c0d0743d80050117a2030700d181c545044410360000d50540e242500050000c1c2c128400070320580c44031f100360b91940744480c80c003400c050400c0e6600414042c10b00c803080e03c3c0100d031681d005450801d1aa4119010626178403503a85000070384010240080d0403200000510100d103400411140c03284020350703208500389440f1044442550644620504040902c41091001034000d0002e1540404007400540001e066500d800d43c110550051080c1c0c14002c1881c180000790001000c594801013078501401582 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261390935 1250 261389685 261389729
    0x50f010f0c140702011713020909070e070f18060f0f0e031e07081002121503060f1f0609060306050312030408130b0a0801051008090a11040207021503040309 69
    0xb00ea2949411610030000b808004c5a00130048000000021680100d003464900900ca44002c40ba1009034822003000c00050009040010100f09899041801584a4a0b0800251400c80284950805000040c070001c0d4102c540c29051500038021542c030512400200c6c94090b0201d404061017400304140b200100f40726490004040000d00e100c1d2003221031480400007a01c1c1011801d0300715001c14015100004201030f1680c001d08420308000a14008035125900c050003039042d031510440e01034000c58009503650540010f0700341c0c04003420f00c886126854600c101d11219020b6005500440c2d2201c1044c00b80b154103215000141038190000d100708603d03414440b1060200030001002c0312000100c150548500f28114030003030a0700d10416807600506000a0710f036080c00d00481d0b018424000d56076500c0c510800c0c0003400360119501910f41251191034045421080c0312605030429000c10030310300107807244020a12029030740d00080d80c032410706140c001c03c0448158803174590325401300c50082c911 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261392185 1250 261390935 261390947
    0xc15090b01170708030408010222060801030b04030302070b100e01150c1217010b09031506060315010201060f03080c0d03022b0b04020d0b1f09050409050304030f050f010f0c 76
    0x2d12a25118800c150b11200a510b00e0301da0315400142441c00081800564000c0c150041e16415400d907280088039074108610b2030a00038075208810020308a0700040020402040c2400c1c2c1140c028a0003501c1d0541d00e44814030360031000d4543e0440001c26410800001c4000b510060161203a20150891030400202c000c0c6001d00391130010348000c03822000306015030b00031030001402001c0c03992107410940e5581040c4440d07400c10a0841d009000d205000203810059182c250301c0782800400843c2941c03500c0c010a240704001076a010705642d40c541011400801d4294501d000303511440911344e98007e1100010700349138001c0700d10400d250042c442c19104d842e480703070500b650007046808411001035002200c0c0c040d2207003240c0d582c4c1040c40000c004402020a80081d0403254043d80c00702d8207071a0b42c00d00c0303404d00f80881500f440000d00380e0100384500d151680242c0344042c058400c8070306190f11303074440044076498410701b1507a550002c0304a20030303420f00703014420000101100070040710b110700c0006011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261393435 1250 261392185 261392189
    0x70207050108180105010f14060a0935010b0111060108060610170103030c050615091303021c050406020f0f0604060203090f1f11180d02030312070c15090b01 69
    0x512001d03030b001541005062091040d116140b00081c0700319690b411b004442c80c03005000d0441c02c407203180c0b000141d609150b001c0310344280c11541d80c4641107281a840d1032090300c0141800803641d460f00000200403d040320602e840d542c2840c000150028000005040c0500c0340182240303a0f0030a0004000d41e003130100b40030f40d00a0b000c0c1d425950301c16001c90111032410910104000c1c3d070000c00c1c00801459406402100c5d03d0784a00d003111460b445030640300329500d080b01d44243d80183c2010000340d2800218192210840c468011200240441118864040758004081001440115007001110703410003c1440b2502402d000e040e08105003c181c80c0c4611006001420054001000c00d4241c07504102c1146007035040001c0e00d0300704000c004414640706135590207200103400c000d52a03d950b001c4000b00c0d501032080c031545d9071010340c1c00c1003400a40803031200c1c242da1500060102100311036135a06110b1088049940f44c0419010510303103200800c07a05141052a145000c4680300003e00340b03620130b41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261394685 1250 261393435 261393437
    0x61e0a1203110105010e040b0702010b1e0301020d02030a0906050709080a02010f0c080a0207140319020904030504051305160c02030613080c07090605040e0f030f090414071707080702070501 83
    0x3800c0606800c0c02e641e41026540c2203280c540c60800001030340310300f8200203406a0b10801294480d5150188202d00365004038a40c1a4000d5000c0c04820200803241d46194540102500141c00c02891003030003400c980007150050045501d5100b0802003002c203220700d551100c52402d08048640c1440c403a036070350303a50501c0300905008010050050b002d0007400c005804660142e0311607034415481c02c0003501e4214030300c41ca201500c1c000e18161441e15001c2140401080680c00b2182c0040d80e076000c205600c5030141003903050080c100400300d00c580b54510b012100e58107508000c10740f410400c501d0180609801007000c10080c003038a82400580e400b0605a4001d9410b000403981d404060030850201d00c141c005140703507481403400000300803400d07420010496070210b604000c6071980002c41d5441705c0342c11512001a4004100c0c2c5102c06c500e100c0034081c03c0d40d02800024005121007007082c851501990b950000c80c3c0700e0710b10110b0700701100c20a642c0c42101864400207900b070181020b980e0b0b1029014440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261395935 1250 261394685 261394709
    0x604030207060e0a03080a050a03060503120d050c0d051e1006080c09010e09090c03060f06031c03090503040306020309060709050f0d060f061401080a0c0e06090f09070305061e0a 78
    0x45544d41c58448010255420108041c0d0b654031083c4094401e86c0000301940200e410304000103034500e0003082c21180b04848644451901040c010010000d14000302101d141940c18055120b8000c02842403501c03914030203603941010740b40f084a5407589032000780819105102c5aa080c003407164800b092170f80102c03800c08900c0d2140b20070001030b580010500c0b00301c0d810803105400c2003c081c200143f42d101500098050314515107038041d47c03201510080b04d0854241c0d0001c065896200303040780d42014070128925001810b403642c0d64034035045502543c402c1c0c800b5500441400a16203051194541004140c24102c13005442e00001c108032002c1e580465200b903400440c04410b000c29900201406034818004019454841080742d00c85130380620410300080400c4000782a40e405445110021840c60315841c8141d13003e0410400303035600440d401c039040125002443c11645a01042e58020002c03600c000c030b00e5240034000e10000c40c40c04e410003819040d190340c04180d552a503021b21015180114a48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261397185 1250 261395935 261395957
    0xa08090111060a06090c05030c030606160516060306060507021305060120030c0f030a2f01140106030b0402040f0b0a090b16020f0607051504020a0f060504080d02060403020706 77
    0x5850745020440007200354002d0b2810491080f410340c2c0020207480c1080000c01c0380c00710a1800301c42500003213075100e0382008c00b013021610794075110001c0d01550341c0c000d4100b0800d680c19900c0c00d003008001003841030081c0a2200c05c0c0049901405100d0151003035103004c60601d1246c0e000a4049003940e41c14049036030f83c42c0d0206040c0d0b40315841180c07034548640c142e00c0d581c02c2c1a00040d99294044900000342c4d0103100e013985c503c0e000100480740340b807240740c0e81c00b1400810310015480825041c100c10540340c035001440380d0000000c0c0244c103518920707407001d041d9661400b000076050758981420540300d00d20400c030a0018000d15110f02051b2901d000c034a0740c45030030344101980c24410b00d800043d102080800e5052002c007400400d00d00b424800c1d110a12034508034400d0181a000d0010000c1544d00040781c0f101c4024002c80c1c1c4151b1080c0014445000140d0b100b40728065400c05030050300000310001001d0013004820000440d0b0802c643c8018081c1e841d040d18000d48900c4030380609001c00079100e8403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261398435 1250 261397185 261397187
    0x905040203100f021603020f010e121e120c07020f011e0311041703040303170c070609020301110301260601240309060c0c06050f0c1903060f0f080715020a080901 71
    0x503a185c40e0031300701c035443c42d822860401a41ea101c01809006080d030800c3c041e0001030a02103001388042c03c22114450130515000c01e028046105106400c4a016080c41000880d41403005014019601c0f1040559211918010b110750161021210307030601414a1034540f1460540d00728124079070f4945400922151f4984601c4c14911580d80301134000441c040420104100110091040300e04c00d0312200f80440301a0800720304140b0442e44448271081c140300d002d01003919900a460400e1004000142580d8031801d4400b503a0020b8002082042d5841605605180b003111241c00f0402844003c00d0035614242c02400c2c404421048099030380406441c0e00096400380d04490b800c00e034441010302c0050f10b021401810400c16080c1581c10030f0030140451031038900301a0090182a41d4a48a480c00111483c1852561840d40b0000d0405980390000074403003103a0b4020001500c3c881d540400c11031702d000d101500c4c1170000e800c280d2903143c85203900d02400d6000158644096400702100d0340f5183c030000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261399685 1250 261398435 261398437
    0x405060409080f1b07080f061308040605071e080408070503120406031d0105010b0a0f0e010e06180405040b040203010c09060f080402120f160b040308120a090206040e0601090905040203100f02 84
    0x4c805462445030840101e0103030004986a066000c0344000c5074019a10311a05480c2441d21010160003460100400c0c0584c2e44114000c200060082c0b43c9085104c0e43c090020001191000e020350b41184085030500031840144580c1707000707142c21030080180210399030520b4003c1c82182300340c0042c90703a15601510b102c05c0b01403010010440c000002c120030340c5e580c0658504e0341d0165072110000756190030005283ca0081c911140c42400680d24031191040742030130b0084662141c0c09107040b59021007501d509540d500d02420303114030320a1034030000a05040c8181800c1d40c451400340c030180001d910341401340c581c0c824400303000040c9a160844040c1c841c4d0000c281c0410301c040751421280103450b00c2c5410a00002103131440412100d400c1f8918903650300000f03040d40210b000041c9900002c02000f42901c016421a0750800d0402800280d541115030000d0201d40c002c0e40028030042c103000401c00c00f90707000407a00c801056072517010304c007a03c0c250307000070344450400b40c2d284401d030703651580e006810700180c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261400935 1250 261399685 261399727
    0xf04090e0705030f0106030506013809030a060f0f02160b040629010e0909100e010e06010f03060b0306100b0307021e0309090a0605090118020c03070803060405060409080f 75
    0x3c1c003a580c40d0741e420340c04c1c41d01030a61400191228400c0600000380c0403c074000c0b421050f051211880c849240b903036080c801c6450900401740b103001d014000c0c0031882e0b07030501c000c1c003485100700000161550103e480506550310001500e0045106000610481c3d000082c020351f0070390301c0300c180c117130a6460345408002806a8a010000300362189074000c0103462541c80205400ea090f22507003a04408142007101a08040300c0b40e00b1740f600700106880886041e504a598000000c20000c41e48c00c41d009045890080241d0000f42640c03592941041030007828401c40000c0c1c801580604401c3c5400e813a0949144e141d846000c0c01000c00100141c486442404a54420250b161070428000b2102090030f41e2038105201162141091001042e80c01400307201e5241119009040400640e2920032401c1400c0d1605006080c03498080000105640b000e1005003440c610601c0703800e80302d0810b0310030b100464200501a6002e40d2800004101203840c480c103480300c107c00340001695038801c00000c001d82c04504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261402185 1250 261400935 261400939
    0x10c02031603022e0e06060a120c0806091e03040506120717010e06010e0a03020f012708060103110102011802060c0102040b121f0315050711030712030c03020f04090e0705 75
    0x200c4130701d501042600c4803424111001e801c0a004c18242c4031129a119401500d105600c5000540108010721326014513203080c902500c0c040303015555613a000b03420300c4030071180e182168001034003040c07c40500e0300d5403c443c60501030045007400d0904012034154810303401560300500c0e41d4400070f1822445550a191142000c5680c14480e59440c05603c08500b801d485a0b4003144101c5242800c1d400c24401100840f900200b00d0310188401600543d0a6a07000c008d11a542c000360008000d0f00c2d01d800c1c801001050418000c148562441c01c002c542480100082c60444e414500410030ba1f440c0d0441c0e226040c0d4040351207076601ea0040900300c0c02403180398080c103140f4401007450b8080d0b506030042684a0a018041c04003c03214074240c510342400c4c0c41c0001000d40e41d900c15011b2210300c15602031a400101401d1400c50003201ca280c003031a5400490307003154280c29040002d00c506625014911001600c0d0505608212002c1a800c00078040d0f805400c220599a030a10082e0707130420881400107003c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261403435 1250 261402185 261402223
    0x303020d0f020c16050607050c0607080c0a0b01081501030506071223190b010203040605030601120617070602060c09040e0102071b14010f0c02060d0608030a030204080708010c0203160302 82
    0x480f4007551103003a202202c00c558140e851000840742003040440b440a80e100e4050030300844840b00304009070300030b5a4180e4100030248603110401c181040340480362030003181c01014541c9400c402e00e107040007180b03c00d907110a0480041000440004100e030708800c0c03d08000010300030000041c8010840c40c0d075801d00c0d03059403c800c039540c4d80442d00954041d100c96206c407440301003580b08a009842542007000d0050b03004100400c01e0030f1089001d1078101005142c10142c070f2507100d001400b9960207400c0310806518038600790303800c83d900300515001000540050034031490228130030070141c0100800c86005548540801000c6a021350445a00030b41c4054001e05000d840f643c0740800303100354001c54014441004c4070310029030080062a007041400d5446900745030040d428403510760403c6003018440e03500c910b00414001010b0010304164481542c0060f122407801e40320501d445402d07404040180d24002d01d0050040e40031088800c0882c204d040d0088000c0c00303150892410031021030300c15484a07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261404685 1250 261403435 261403447
    0xb07020f1e1009142b030c05010507050901030b010801061b02010207170a02151e070203030918060102100e0c220609150509070c0b13080705030a1107060c0303020d0f02 74
    0x42c1103503111007512003040b10b441c07607013420740b0030711200805111005800754406558050110100c200c0d003d41e480c42490140441c04280e5581400c2d40c00c16030784940443c001060001c110359040c030403c844480e0910303106109525291000d88000000c81e0103488120042c08a481564020008040200340002583c4041003890042036203851003450101c0c0b02d003202c0401c04990000000c00c0d20200610141d1210048154410701206a800740c0b4080307800d0b0105005105940d550003d61001c6288150000c18440c54004002400c0013510000c128400f45003d000b411103031000940314864100c00d944c85160702c54000304000c0c00b116143784140000c1d0600c0808201e40c04980c0101d03000354001850002225141d008112502004650401c0011002e440344c001040750900c0301074119034900c2c101c204003002c617240c00d4261342c080c80d0240c42c00da2001420240590348420300341c184070004c3c005040c400d420464014002e60141c0c0000d82099008148859408401c0e8064100003403d038a0456450b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261405935 1250 261404685 261404687
    0x150907020f0703051c1112090a051008040605090d050d0f0b190f06030e06060d03180618080102041a0307260708061c060f0609061205070b07020f1e10 66
    0x80e074410660b000284041d01007420060040003e2103221101b407010300008400e80c400c1c04400d0304441c1107540d120700344410010f51600c0e000c070b4a0b078048500740d0b80c1413007a14050408005645020f400b03d000c0380c0c006030345a032501e603024003074850300c40004c900455013540184e941005408107110312607010813503544010f01d040d0201c100b0f80072566070407440700c02507030b8a04080e0b0445440c80e9141c066908a440090b19624082c001c1178003492090901017903900d2a01000e03201c0d00080c0c1c02034400703e03010071220340c1280031034120507009065000003549000e0408040d112004940294034000c0c007004404144c0c154018146801500c0c3c40304040140e13009805404640d02005440e0341c8040351224020070304038100140308101404405288098002e050b0752914010071020b002480e182d0b84d98500442c61220601411000f41340744900c494034030034607041003401c00d00c20b940003126014040040c2e2005840780001c00611102c00c035066410448400c000300000b501c00d0061075442480003560807265 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261407185 1250 261405935 261405943
    0x1021b090406111c1109010815030f100b2805091005090a050a0b030109020a05060d0219020102070b0a0c08012c09010606110c030312060303130e04060c0305150907020f070305 77
    0x42c02c04c0c41014031500e1807202140d800792280b40d03880c50000e0310540004411451030110183e6446001e8110f949080e07079040d110381003603c6c010031412520346421800310740b450604840c21302504816204002200030400322000c0321403500c80c1c00e0007480300d000090004400e450040f00104001b42810905280090101e4001c000841d102c80101e4505003080c04141414461030000320b601800e04c0c05e0031824041040071540003070844441064007000f0340d0400607902200020388100c01d40000d038403000103103030050003114010030003c651031410080c1c8800302c0d030110000b0704480c4640010b4000040851044100c218807410102420701040c0512203103000543c4050200c40329039892010901c60b03010016150701c4c41c2c0b84050390590091010700c86184c1c08800c4a60007005c000c049900d84064404680c4d585101c40d480002da5140590800c010300c00c19002d0f80d01d100c00249410451440c22418000c4000c0c08554254065038441c03000564050007000a80d11017002201120200c60303813072800d1562 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261408435 1250 261407185 261407227
    0xa080111040e1501020a03030b04060801090503090103060621020d0b03030a0e0a090c08040809031f09060516020a12020c0d0809120303060a1e090207150b01021b09040611 75
    0x4290b04400004441c854554589010b00700c05034003800340500b541d1421000703080b600208540c802da56000000b4550001d01c0f5020b1180d00c1030f4040d584410038030f0005411904076a0084040c000385100366120608000f04040e01c429901d54010303107615455100c203004106c5000302035054840040c100c110b95070400e02d42d001c40c40013251040d01458481055405a0ba44e0044000c04511410049000117840e4400f0741520395001c0c08581c0140300b00044145100ac102003410240c0e642d030040441071010781d0194a0380400e00503031a02d1010713441d1800035502e00e01c00f81d000c0c0c02102c1035814001000c1c03080c041015100e40c0180203080403c00742c10051810f074411205648100e0950300b00d16040c1c1c10102c00c1d24400c01d001420b01580d14035000f0315500340c0c10702102e2132480f050032071004907074040b0510152400c5070040c071b11318000034200d07a12030048405540a0605642c0b102010046144400840001481c01a80c41c0c92a0b030b1641e18104001c2c1681180307646c400d00340442d21006c1541840c0e61110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261409685 1250 261408435 261408449
    0x7090f23040c0f0305090c040c05131a0a050a021006090b090105040908040308031503010c090602010c0804051e031303050d0810080606040203090a0501090c050f030601230a08011104 80
    0x414640c4800c0008071031080d00d001d000300340c111002400c0c0c2406a0302055000d401c0c02e090b00c0c2c80100160002e02240d407280b8804022071800720b0f074510500c1e200d040800140c1403174901d030030224012244410260144030494010801c00103800d11559209000031002401210000e00c0481c0c0c4032542c41e4080c00d94080402c6c080e800460002442d4074050044d56000c82d04014400d2070541561110450f42d031006004408426049241c00b5468800b4401c41450008950340caa80e4681851402804d503800000c12070200103607017007400b001c20400b1515090140c03140fa1007440802c8e41303200590540c040c00c00101c041c2d100480000060080204944020b01401e580d010800e95914182c03a00b10102e50160300d50f0740c0d003d0720000b1690706080d402150841041002c4500709000c40e0b40d20350a54a01c2c2100b03d499139030301c00e410016030420781c2040c01c500d0000c80152940c1c1d0304180d00346108140884800040c0c00781001c000700a5252020310b1400360890b680248410001c15039440500d078001c0c8038a030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261410935 1250 261409685 261409739
    0x5030d05101a040510050a1b03030b090105030606090f07020118060c0809030307020a11061c14090c1e15040f0e07140a14040b0d0905100b030604080307090f 69
    0x1000841842e412601580e10040c00703203d00498032007003210550087c18451080c04108903100c40d080320300504d000d03000d41c0301381d41c0441c140e4980700034440b044e4010303804180203a001700d007400b01035074848440d242e201c081d107040380900d6698030030b003240580036000d07034035216183c442c0c44142400104e4001d44010010b503110034080b5250a00380c00d690748000c0b1b4100005030016803042000909a20315a41c1d03101009011500b00022010019201c80420040c0e03290507a80d00100b2502c2540290050b50244000005e000000460300c003040c00c0305510f20b1840400601c203038074403007650345250f030706c42d120040c612120b911f071602c910100354441100d008541c481542c850000340013a100b891480d04440301d003903080b420001aa08256a02019810b800104600602c000300304002c1d098007074000c4a248503c0400c040b01c01d401e04604050001d00b0f03045455060094135078140d02c0014050ba002644400350958a80d00c6880459107094580c01c1003010b0f040f0707401c0010b0301c8034038500130002c2100d00340030305 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261412185 1250 261410935 261410969
    0x6190b030a0605030a050a06150f0602010f050c0310030f0501020c011107052509050702070b0a05040501090905090303040f08090a06081801140604020702060d11030f1b041205030d0510 81
    0x59176400b10004010300c1d070343c09058503400058031074000500311a60321024010454461410382c01002283d003202c0b005039034500110548a00d1401995000302564001c180365003400b040c10440d0300c80b03600015040000036a100c01c1000425030446403031900c51002040f10b510348001c200c0150f400403405858a21607007801454241c0c0c011200d8028004100300301c0c4106240c03c230f110001d0030000b0002419030003800c1000a010012100911785540e413640c6847c1c2e01e03410000054850749058011075980c0c1e00c0d02c0f003003150080001003103d80040e0016130f0303101c810f43d003454030329810321400c003140d900000000720024070b4903003164641d0b01070200261140c200b00e0100086908072801d02800341e000582910104801c7e0501c0e070300900c482030000d4181b0b454040141190801d85614503035018072501c00000300f203400c02000f42042e401031526102e40c03064046070920302007031340143e000c2c003880004162310032420820100308030b4006080f0703000c050116180c4800284a81000391007010b0000b0203083c0301d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261413435 1250 261412185 261412189
    0x61e0310051002070e16020a0203070816120206040b160f0501050105100203070302060609070c020d1a1617100905070e040c030b090c031e090706020c0d0809010806190b030a0605 78
    0xc9000e65405000305c08156603142d42d030b002c010030400302e02000d50041c0c1401c500035840c113001d404080d201400090211808003040c4107410070341c2c2da025400c0000c0d80b00640b00141c0d0340c0000c81e02110045010213841d03407403100d00f02000c1c0c05d2455005003498a0029860b04101c0d040d04403a048034001c81d0800d4603014494000e980342c0c0b0503072200400503008500000d0030351401e542900d4105515192212050080ba40400c048201080003038075641e0040ca15043c0b07003200c1c01201c990140080040c8005071029543c05007000345007101005c0c3c1000542c0c001044056541400310041440c0f40c028412800c090340c1c05002d8114400815014a00b0500e50044642c0030740280401c0401c040d010f4101552940c202c540710341c202800d00c00140550401c81247c2d0701d18601c8027030144690b003010b0060705107046406440c0c0340b134001601340078403008058200071403550381c00e03900d580c3c42c20300340103413a0360302e65000440854410b1044080d0190680001ca201011003010714407030701c0428410081d050301c40b41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261414685 1250 261413435 261413443
    0xe070b0703050730030203090f03070f0b130c031203050a02040b090909030702030a3f0503070215190e06060901051c02041a01021b030c061e0310051002 67
    0x80c000e00840c1e420000030700000c2202e001401d80006408580d0614101203100240d81c41d003030382824001a0b004018800c00d03030014004880c0d2954014021844c2140558412985402c1454041c000d504410000b1f0807000c2c006142c10b0825510400c00d0401903120324184032000140f00d084c00001c0d1600001030001441c603c01c0300e0a50305000049410b110114041002c4120010104041c1d80400d1244070010703141001291034052041a1b1a5501d9914000e50143c200c0c1c50031105240d454143d1090706420b5080d24403d004a20502d800c59480e40d13052016890100385110394602004885c0800c0341040c08480046481061484140100200104100c0d65903c0541d9100c0c3c0c410030385001009145000841c1c119014450801c49a40080c1c540010301100d440303254142e0400c0108c203c22400d50707418400324440600416207030200c00101c4000c2552940c00ca100c142c02000002501c01001e100d00800c0c845507080383e01640d0342e03031800090400d00c02d5058030500380980460500c076410280081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261415935 1250 261414685 261414697
    0x31d0a0302010e060f0708040b030105011d01081303110f030406090b0c07062003030906010312020102031e0703060b0c010b030d0206010b0a1d060c0d020c040c0509040c030e0a060e070b 81
    0x10359107040d0801c0f21410441035900c0440d402440280030041600080c1c40030340074000400c00c602e80b443d102c2d89480000b40011221240f050180f002c280404001603030041c48580c0c014040300003021035103546103420343c1c40a088240c060f20030700c1480c40f20211440004014401e840c6607a03a0403251982d030301f80100c9680601c0200c10442c3c1c200e0700d414445c01c1d202d505000038460a01c280640900b44000180e170466005031407001d07203030b045100180203000c001046080c403d003007840214594504540c0c40c05080c100c0c1032141c444880c0b41000b1a010b14400c2e0054805400d07200750f0305943d0440c110360503008120207980075000b0301401c21900c2c02c2600115103030741240c42407881288ac0c27402c0e4400440b018100d00c01c0e0340000661501c01440240c50341c10103030505400c01c1c401080506a00c480c061b240160b4448602e109034244010611500e80c4802607800440c416100820004903081e01a002b4008609000d80340b4410050720006100c03e13a000344020200c01e5040e949855150340c4a041c0b607110321 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261417185 1250 261415935 261415937
    0x60e0a0c0f05010519050f0a0305041a04050303180309060c061f0303080a0509101418030405060912010e0109050d08010e07140a030608060c070519112b031d0a030201 73
    0xa00014880b2005a202c00d00150f8041c500107240030404a0311f000560895100040026138032003c000401c1280e82c00a40c5281402046540c3d51a00b50703926603a81c40002c020890082000000c0300e19940104103403840c0c01c40c0209030f0780e120420380c0c6c0c407159901e00031503840c01c00309240004078000c000142116002d0f01d80503500e102496440c000f8020203000701804c0c0210611a030025120341900300d101ea0030b619070400041000c0307424042404e40e148042a0042602900200810403c9598080840e10048005d07103581c6071280980c4101801804003581d00f101315400c24200d01c041000104a5140040071501c82d1000c1c3c0c1d0302c4030100101c1070011541280402c40505211300b0703003110b042c06000004054a00850f0440c1c41e80ba250f070801c1803e4a982c41200d001240760410000c09100030000400c60344d044c10304041043d1900703041c11442c41e000d5405444a420b44560503002c603502041c0e0904111a945880345113441d00411584044100701d83d200403890410a9603e0544494001c070b80e01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261418435 1250 261417185 261417187
    0x2220b031506060703110a0609140606042711060f0702120705091305011b030608011103060a0902070c151805010305040b07051c0e01020406020111070317060a03060e0a0c0f050105 79
    0x581c1d5043c2c2c1daa06e507800000c1c18500c01c014421000820070b020b50313511170380710b03203c003101c40815003c16510b003040c0904090300c104c0c103090280c1035440180021080036940744100c0c00d0014080d04083d030303034400d00752440c9421402c0001c280c56002c1d403c100602c8a144207072440410842d885d02c9540e203607942400b0b41c5500c46c03824400301d1074554840601c400080d00800001604500201004141b1400040c011000c29200c1100b0030511071f0030b1003103044114030700384c4032031039464640c2c00600701d0985802121034030303030740820008180701c00e0032040005018800102c41c894820400041c00300150b0410a0048400c04540464194441d004e128001c942c880c040701d41c0c544411805407155004a60204000300c440b2080c0d41203c9214003809803403140d140001a925810060004d00b0341d44a015150202e035800c10441c0d000039400b81000324880d00039203041c101c0351a040c1c00a00e032610160b00c00b03030909080903104018580b01046840300f2911030603426421540d18214072a08020910a00f801b00d84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261419685 1250 261418435 261418447
    0x20a141c0c0b1b03071112010c02061902130905040b15032e060b0c0105010603050f01091505150d060609080309090402180123010801050d030c02220b03150606 70
    0x154900141a01c10448000c030030096583c007104600c0c41e0402d000030b440788801d100504c01d039800c0400780e070594003c0d4800244007040030200060741c0d031840648409038020407040040361800c1254140c0300d82c410ba66901900c1036540d40341400107000260340031740c0c404040b180490403081d905000c91140e400c001c0c0c00f070040c5040707500c0400001d0345d85040d044d2121220015100c0504610300c915005020040074058032603a1902d60035084810580241d01410300d00024880f80e8078140d030b074050464180c60380100e0600f1248810406c00e5606601c0207800c403c40341a403040b02414640644000004500100300080e92000d086600008a00c507404043d0820005002c1c01e080c00c64036141e12900184c180008401100300c1410b940c0303405d9200d40c41c0c0320070343d11204a400c92040070343c0382504000d00c0c14442135410304000440c12410307954024140300400d404803085485803034001c0d81f00070709600c0141549140f051307442d000d0104030342014820b0145101c0d00c1071401c01511160300031030028054600b0700c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261420935 1250 261419685 261419699
    0x3090905060a05040501151d0a05060f070b010605040501170c0f0903070803030403180e0705030a020304031b1103010f1811121b010e010c170307030207020a141c0c 72
    0x304010703000741d80000d01e001000c540ca48560256a00130f11040f091000034510b4580c0052a0b00710000b0500340b840000d021031400742e40c44201c7c81041e03c5084034170640d520101000000d4900c10040018000c110041c0001146a0400050300485600b030b04c502e003461481104084142d03400701c807044252070051051001e0410280003030090b0500240444105039140c1050b24078540003140c0440010740b660b540380b0002c43d20620300c00020300c0c02c5007101402c0d0400403800380103400028a44581c40d03901200280a052145c24103203544a401c1000307145c4400607017010a0118040d1a44500039800d00d050074050106a11a1501c6000c540703c0394003200e80103170750794041c60b44041c0499600c20b4800b0061042c00009001c02c6010110441c15210500031000000d09800c0403401418140120210107502140c1c121b907040090710b4a030652503039240d031080d0058009000d458400394214480c2d801c00310b4124100c0396000c441c0182120003010100102d44804080030a581c4d00030100081c5142c10040d03c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261422185 1250 261420935 261420941
    0x220312052701021906091a0f010b070602250318080a0f1a011212110a03032a050d05010e010303170411040e0a060c0f020a02010e0609040507021c030603030909 70
    0x1000c051054400700180c0009085220b0100c0030161a80c5d56144500c1e020400e000ca03581c440308041080e0120185420004030380010014841c42100b04070006e184000c118659040f2104500f40d00f009010448606081e20b04502d1065012030103c0c2280d20f01040140d41e030004001101d0084005094016155403400255032889004480d503400241c07950021500c00324280c2c3c041d0820780303440f01c401d00c843d050030f804504c0c01c003401c4000e001191824030003100300030400581c169098200800d00401a19903048580b00007682030003a806c9400e101c02030b6075803000040c001c0d006418028061030362541c01c0f4060341142880000c0100380250101c5065074003182144d03500c0740c02011141300c1300f01c607403000c14259000e6803501030180d00004001c0381007117a90301c40d40d501c4481928002102d2001c080d0003030f40e10b900e17850020f814011720000c00703001aa100c008503800c4150180c0103014600346440c000c1c2d604c8008807140040031001700d1610412a00c248103a0381242c0e0103130745810007140740000d50402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261423435 1250 261422185 261422257
    0x1401050307030f080f1209120901080109180215071b080a02211002070308090705090604090203011b080f011d04030305060301091a090705010302030f0103020603060622031205 77
    0x341c940a2080400c01221703040074000c0c00400100424807482c01d0b00c2010b0070010401741e91030904106005004c11039074020802419100c0010340040c00c0650001940000040041d00070343c1b0610304401d80c84140c1c8481c1c06803515601c10b40d818240c44081c8000c0041e40e14141c00b80d000c00c5e51003200901c0c05480c0c003a0f0b001300311903100008800d03501a5444001d04180b45d42e1038143c01e01e500000c48004255106454650044241024000c5942414001650302c0713405002c0a204a44441010056640a42c00240044080c3c41351054207008d0420140007a9000c407146030354800507000018003a9803201c088800002c111641410360358450398107400404d4081d082070381642d43c079500a0b00203908403281407040440300705508218a8034103461480c240d000d800c058101030050007800000842c40e9002d034190303079044550540f242d9454003c18205e00030303144000c0f8107030a581a18051403800c01080000d032805030003003400a881619040e90184a1021100c0d0303e81c440c03998145650410440390380f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261424685 1250 261423435 261423443
    0xe1503060d020a15080412080912130b12060306100b0a050313050609150714090405040219090e0d1d0108040c0f0b03060405150108070e01140c0604020102011401050307030f 76
    0x384813a180c140d0041010072070040369001c81c3e900d006100c20b2201c401c080300c030300a219180111203844c220f0350b80f5441e19848030f1700111030300c40401c1c0000c6000d038034034030300018000140f00f058960f1855000001e03404416103015020f030103031201140711171281d0011281036401d040103031403601c1c1031804211100c2d40024101040344240000b201d000883c04c0c04903a000f1841480141007441d0601c82040300240090f00e0502407001400d10a2441c400750400e8410b10385003218002240c2e030302c50001c512110b0715480300314550314500d100414250260f5221018104407101161120860580140d800b03014200d0400000c001000d01c01061750700c50400f40307900030301c551424500c0c281c0c2c805902c4094490354004c0302111a01108010742410148182a03000ad40b280f002c0031800c1007a00040c2901070090660400c0101140840b6916405910648900c0542540c9266070384240100c480c2c40e0101039070128019403c0c0015015030340081c02c105030589500901801c101480c50381d41c2c441151000404071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261425935 1250 261424685 261424699
    0x903070206030403050901020706020712030c0503090603180f0d050f0a020a1707031404030c0b031b0d02040e060109150f181205061605040e041b03030f0e1503060d02 73
    0x41c1c554402035405607220303445080c0c980143e0400682800c3c0a90464021940500c1c010040d450101c100e8007500341e050304151407040d420f4107019045200c1c5003030484c0c010b0070010601c480300c10417900c40412031500006648141d4504c120403511281a0304403500090014880481d94140d124010705400240d030044440001980da00c06011074115000082103680102d04c0380c080c180c01ca40c16900d441c810081e80c528103401c0d50780b0036803070390814004c0384004440400011200303508100001ca0b00102485503c0d1610401d904000195000d4090701d5000ca031b6003004520f041d401181e248003542c10940a9004081c0d400e43c00b110845030700301003a420050310304440301154816208850241a220312036080c0c800c0c0905249140403005040049a44064020210783c07076885000ea4043d60700010790030049482c1d500300350402031100808181030a80c0250000101900700000c520b102c0e482d501c599600d1003d020401030800b10200d0b11348503842c020000122a031904030071400c804c61004045c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261427185 1250 261425935 261425947
    0xc030c030127240609030203120304030c0c030f030f020102070c0905150a080309010212070b040b060604051201150603090503030a0f020f13060e27061f0206100504150303080903 78
    0xa0301503d060f041c0b40504503a211008004103200105000c2c007600440c10032180080c91580469030711030350a0000c00b02c040b400701c04034041502c1760180031905604004002c000780d8a82c03d00350b000c3c41002e1011004604007060340c07441355006000762050180c1003000c5a407100d24058000c2c019000082c07008032110410500038402d640d88202c0c5c0f9010b450002d00454030b07004d400c000685010100990503503001c2050100301d001444500300d569100d907020b1403652507521541c02042c0140210303089264410411059030101c0c001c15800b259001c00c02400748050030740e45010560840b504030308040d004d40c00c2000015130b41d0fa0319800500d19804103040051901030a13002115040d04a003036541e4400024803420001142c1c0502c000c440000200c40d1003103110801d0001d03101c100d002c90122150705916100058841d1b407000d0803035052082c20000d80140d0300424000a4072000d04442000c0480034803180414a41441c0c8600441c42080c00030301512103003503407800d03190351800420340c1100740310030001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261428435 1250 261427185 261427259
    0x90c05090918031309150e01030602091309030206040b060603010602120f0f0c0d08060f10030e0f010c110609071514070c0b2d0415020709060e0108060c030c0301 71
    0x205100c442c01c91507150340324140b5040705c1c195400f00c0b0108174200144079092041001505869044070341c0310f100141d88904501c046200c2d0a00d0748074100489252000c408103243d00480c81e43d200e64415185000d06590300c03002c1000c40e0100380900d00042e4013010186007802401801441c031590744200076401d207a160241c1c004640d0110b0030560941e005070040940b699000110b10307400603402c69038001144184400300f4108084100860b00f0152075400400880600b8403126500c003d2304002800200c07203003040030b0801c1c041d46801113400d2041c800092600500454184c013a684066424035410904440444903050503c8080e1060042000200001404078120b03400510300310030000e450316500c6092034a031030041099841c80e0718030f49601d0006117003c0c0d4112070a49d20b105210b60780301020808121315241c0350707070840b030001d84c60f0100c040380104100003070a040310004001c90700c681e903c0840465081c0411381c0c004881417403d100502c5144410302d004001010110007100c40c0c424a03080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261429685 1250 261428435 261428437
    0x2070b03070203040e0703050112110612040c1406032202060c030c010501090605040219140d050a1a0604080c060a1710091a010e121501060e010207090c0509091803 72
    0xa60240540c0c0000303020005c40c00c810b03407401c0e80440349080806c0950724004c0da0b40b000c071058502c002c1c00801003501034000b594580e8141d84030b400301d4146503100d500c1e2074904121840300c140100c51880c50031402c1140185421800ca922658003200c518030400504250151008091802264004000e00040715600b0080010b401c541d44a100085019403411982008858480e08858016801000501d011032148148082e480103545000b040c651814045840b26009102900319498145418000d2408160300101103090f4420840001c828000e01000002d20451080911a0b044100c1d484864035140d0007420468180d818481107548480b8107000040c04102c807004410792114100b84000314203485952035402011140070806503403600042c00c8900f55401c1c56100e002c00c075110852020042c400d080d05c401068182e8012540c54540c054413500c2540f030018018440c9000c0040c250120b0700440b041c044640d2140392400840d1002d02855110042406401441007000950b844030300b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261430935 1250 261429685 261429691
    0x70c1806180b041b0503070f090510031b090f0306020a030902040501030605070e0301060b120405010b030a0507140306060f010e04270b090d0806010c0501061a031503010e06130302070b03 82
    0x5540024120419020002124061522030196401300005492441d8209040300e4000d1000c0c208503110151182c2c3c201c411800640015402c8035410014801043d010b401465070440301c0100305040c0490f140c42122145264400d050000303040c0d22040002c1000741d1b0003000e00034124900818481440d8000c1401d484007a070080741c5141d40c8408001d440e40e4010703c01e002001c01207000703001d018030384086aa5a4064042c2c1d400c28910890085410081c0940c003074030b86100090155005031003107043c050340791841c2d03210f040a43c0c0700401d001c0c031b110b02d40840c170640324882c018100070f655080c650044403a10903000748240c01503550310f042001c245500c101520850507006000003400c0e0f45191111408401600c80d520301e50044101c4107005400c0303101035510400070320381940d5040792414084e02600140d8414166802e1000922050390519801180311f903003070004031002c406048050600300c0d400d0f0a80d845c03603a0805d03808a02800c1c194205140307070a0181c030495900c03d84884083d00198004c3d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261432185 1250 261430935 261430979
    0xf0812010f0e06030c0105030615090a030606080709090c090915050c0901110304030b04080702031606081005060c07031b0806090303040b1608040b04030908030d090b0c070c1806 78
    0xe400200302c8441c100d0105a40400c060b00a4400761743c035600040d1082c0405000d03d441565001d804030400d00d039a1068400b41c6400422403031b00c0554034240400104050300070010326000c3c00c100407403048002e00600d42e105503c109a1703c9034500c1e00d884d500040c01c40303034000c641c5401110101d00d041b400d60701038180210407007002c0c50317a40e401010001d000b0881602551450341c00070701081012030900581d02e0f610030307004289641d0b184841d10009041500107602ca650011034504c0200e511540020442d03c5800120b0502d01195224070800449019a043c601e403144e201c014180001101d40100d50758150030484041c00940d1a04042400d0010464508400e948080100700c148045c000207160080c0e00c07142100d0304c82d00c010000410712200240042c0c603040350f050120301050321034602180200420820740ea140c1450042d2900038040204007640e09000c103501080740005080121066aa8802401c4895510300140c0e031020311020441c1c40803540e510a03000506034241c100c000401544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261433435 1250 261432185 261432209
    0x30f0213081e150405010b060a0201060510030203012601150602011a040e0d0c1e0b0f1f1406120c03180304060c031d030d030f0b06090d0f081201 64
    0x1c10451902d040442c00b02a08000c20b040d00c41e2450440108415080800c2c1c20b50310b412503511814018058200c20700d0190700214001012080541e066000f802030360011503405e16008070b040c104034140d002c20701070350400c194031103807104008000201040c0d000e00544004103080800da04c0c4202c10440c540d020b4000350b51141440da50074011455100c00280701145c1c200417517020740d005541d454501038101006c0c044801040c4040c0708120740001e00d810340c0000524200c1c080d0f07151a0303110082c180d4180d1100010138010400e40d4400c13010146c03505035225a02c20080c1e00e0a640c8520210010461641000f002c210b42924600c90040807445000e40600c000e5803810000c800303546043c0c1000301d14041d90014081448015400000301d21f03001d806141c5030740300002100340c166400d1041041e00c1d07810300c80c00b15032140503505504041c0210007140002c129901c0840c082c402d0602c5042c140b10b5004200f000364034001105803540c4400c50f0b0081403204c3c1809408004107080040a03040704c00d078292 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261434685 1250 261433435 261433439
    0x9120f021c0e24031b0f0316120b01020607200706050c0d08150918010606020d0315030809041d06040302071517060f030a1e0c050102061303050901030f0213 69
    0x105205407040c14440920700c02440c3c03540d581c80f9201400050b2803000a49010880c5029424100c01511320383e44000401d5503590402603905007415130028080c101040564129203a0b4009034841e281180c1d00c183c01415195550703c4044070400151440c2c82d020003100e400c10310204800300500c2018120303580b1459668154041d400f403920803810285c004121900c020014070303034001800c1401078101901d03034070b80d9500e0380980c89083d8000c1c100000301380d628003400024946e60001d41c09802c0d14440c0c400b0080101c000c032420001200c00d01024061280030070a0032214201075000e01000d950018501c518080607441d01c60070860309643c158016481010184140c3c8441e50079001146034030304064101d010383e1078521080071402000e69105884003c16542240c130705201d00414150700c010801c2a0205030b00035417030b565200a000380ea8011300c00e88041415400000c85601900d40d140b554907908807140d40448056000c030250310b04040d1120503110780c441441c00a8418012030501c1c0c43c001c24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261435935 1250 261434685 261434689
    0xc100507080c0307020c0d080903060708060a09200705030915091503091b1306030606150305071218080415031b050703030506041103131101020109120f021c0e 70
    0x240c060b0a04410580400c03c0c400c0e010f40002c1e0f030f81c14000055130010726041d258101a49240181d0f424030b90180101c504214405030710182c05480782c001100c00340400750b1607200e03543c129208203214502ca1040b00210303902d2041d0420280c070640e40b080d4216842c1a9058000c220100b5646094640990011a8104403482c02042ca1003690000140090440c80e00040b0150365030303180f400941810000158085940d02c0310800c1c0f8615203541c07001070221a0340ca2400400411f0903100b81840b4050308d0112110300d84c840c3c0100ba0007501242ea9a10501951046da130005001d004540d1409501460300c0c600012032160141c030040061881105c0700320813400025050b02c2c0c1751222151071120341340c41d640610360007a0548891320740619000500d682e0700800305d001050a882c20b030480000200411a451252892a0380034a200e0150400b58480c0c180059003600c2d8000c800070402441d051180d030b10316200707801014243c2007071310454801c41d9541d203112030080291882c941c0000c0b8130b052040aa8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261437185 1250 261435935 261435947
    0x402070c141014130305011815020909072d03050a0b0328060b0310020403050f0705150703020c180720060c130f060906031404020a090b04020c100507 66
    0x8101c203840b2141ca206920b94010000d8410501681031180c0100703c1003408004000c444018581c8207008100f118400314500402807200c0c241225011695411b20424032918001e071495a0005020301c2c20030384580740c083c0c404944200d8000b0040c03d4402c500000d403000135030740d01200140b903240060b0508014182c482a40d1200181c80c0c02607001440300c1d020f4645182d04021034140e00310340240041ea19203080070140440c548400e0345031050119008203580960f00030400c60b4896030854007014000106651070380250b1007401d40c040c0c1c0c0c06012000c12002c1c0c1c0010806140300f40f064841410700c420002d12526008846d01e50f040301604108030900e5003006078040000000001010b080d4150280380f030f602d1200911388405164042042002d800d01d03125148040c00b80881c000081d50b0311000000c10a2181d48251000241010003490501d020708400070b008035000f07400b0540c2c035070400d6202c070003030600742c0318141e042a030800c03560114450612240100c01d0044601107038a082040c001088 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261438435 1250 261437185 261437219
    0x31e0f0c0105270115090f06121b0608011202010c1a15091e0402131404030c03030b06071a0403120204080309120f030a0309030507020405072d0e060304110402070c 72
    0x81307038542400351044605044041007103441000380410108001c0f071600d000b41001d540902010344002c441b1104010b440304403844c80400c40c4100c5012280d0303a0700300b1542d10b030f001c0c42800045001e060100026500c42c1e100c0b02400d90003118049009400d1080301301c40d81604650540306e4842c00d0301c101c841450310240e9160442413402910340c0c0441e90f030401c06040c080280000303216100240d955020307000150840d141107603006000680d58a05410040d140c2e4521282c00c9000a1800b107165002d89030030001d0324140d5400c261019a1682c4c152100342c02144040c0c000d07001c0c41405103000c06660464002400502088009142c4a240c3c14007408003c481040350400300d42c01050031652854000429140820240c0c9400b19003810603060a840e103114040000e0740003820501049410b0b90000218070200c1031010f01d40c0d074101c500d0450403094a00c2c40c0c207401c001640e40300d055180c070702c0c1400107103400a00410302103240744002c600180891b84140001c840343c403071001e0200400040c4980c0c00380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261439685 1250 261438435 261438511
    0x9050f030307091415120f090d090306020a2304030309080105060904020907051e041502070303020601150e031902031b210109020a080618031e0f0c0105 67
    0xc118286040043e1410086000c0c04a209010352142c103080d41e140c04015a41900c41c5044596480b1600789180b22884226951001100814041a000100062604403c001e2580c0d85a1000e080d641c40802a41c0024000003c1040300c0d2400c060304458420134503800a01c941c0c1c065600c62541c40c0252804009920810b402d901d0b00c0c0800040380c07a19040d4581c0b01e581143c441c1d580f40e940810650740341c042d00948070080c00075180b8854801d41604003c0040d6205002c8581078014000000c0f6500c4500b808014010380018004212200014210b80e48642d641d061240c0c0d103000703100c04285080990b40c54041c07030008075218901542001c0c00200000c81003003501002c42801c10300480c04074591525034045910034412010126602035110400d015401060010700a645a40d040e5131010b003614405501011100d1901c15403000104a800c1c8451440700e0342280c006025105038280c00a05e035040814000708075002040c4801e10980c0c0c4101003c8001180b4219240708848005600c01204c1d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261440935 1250 261439685 261439687
    0x8071806230307031538010e0102010b060d020a030c050406021c030f050405010e01050a27140d02031806040501120c0e0604060e0906010c0b15040204030804060309050f03 75
    0x480032100d03081101c0d03401c00c404082280304601c0c0501003882d00c00d8943c400740801480c08481a00c04500b40c004c0d0f0820410420781580c07945102e41d0903000b48484110b40e03c00c0309081c04d10440c0355400740d84a034544980500000420480800101c0c1d01988001c41114586600003209841c4a8041c810181d40800a00c0c1041c2000c1c103080010b581c0305108015501c880e14010b1801c1070051194000c0d0a404940c088140207a0805141603030103015461007101055007010006a22030800344100464800303400b00007210300c171044010700058104070a066603051011803c940411908000382a40c1050796801540e941d0403000760354000916038a2501e114440400c0200510381c2e2104d240c00c11202c0c0c0c12070000364040407601c10340300b1044020f080d907007168012600043c010381002d9014940340d4140c84414043c0d80b6180115030308a02c00d03a004140d50707942c1c0049410100c4802d41d030004d10030b01820041c40c0c90380b82d45818806030069400400040d440340c1c009e4080003814008072504030707a0700d4019 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261442185 1250 261440935 261440939
    0x90108010e10051906060c11040c140d0e0d050c060606040f06050306130c0203090306130b0f0a0902060d090302190c05190f1e0803030601050f030a02070203060108071806 75
    0xb03890b050350101c40c0c40c1e0710f603c950114052049519480800f2803000508008039a500c1601601c0c04100280980304000114490381150401d4000c01000804656404103c007613111004070164218109290040303558258515820501708000c0403030a20a886690302c0b030074003640b49458440001d140314000c003028003080012000d5900c0d0003040d04c003181445500c0b641c3c2c140110305c8a40c50b040c9060300c00750034003103400b254030b8010000b080d40ea401601a51100d903941d408012991101c12401000319a208000075510140c3d001e201c0d80040c0d0000700800d4050721a00010004e0700f2004054240c0369a644100d403c250f01040b80e410712842e50000e0011816140e240c10560700c10314030919008009039280c4c404414076501c80030001e490500389451485841d5900020001c24140d0150840440fa10021908040000c00d6900c501016900d035858489103a00000d0b060f04080c10300c160194003444007800613038040c45124081d0030950000c00c0440c0c5804056461010b0504c80684501c1ca401ea013 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261443435 1250 261442185 261442211
    0xf09090b0601030209030c03060c0d060803030613050c0d06030507090615022a0901080c0118030816030e032b1701030f02240301180209011205100b04120209010801 72
    0x26481e4000c07824200140c60300b15940c080b17070401046940c0c0039854001e500800c005030082e0740140c04a003103561000c02c929500c41808650300c6c44243c2e00151700c85070407407103000030001716000580d01008003c1c0d8281002030001c004025542c86400071030380c0ba00012070030301c02c80001d0710402c8011321104c8004501b04280820194541201c40d03004901801e090503481c040764912880000400009842c1c0c101940c0d41d80354564891640400580c0060b220780340e44c0600381d055404017029607070061040be160403084154141040010030045050021309690303441643d034148400c0090316012150118000301100c00c4211140802c1030142c1804a2001e0069808801007440b6043d00da11071400700d5040b00500000d13001c50b20782c2d0b403183c1e40d03051908000c41d59aa54030000c0c50480b807165550091044030b880d104820781c040c20a81500040042201c000706c2012a080346030084a043c0d841c000240d140c0a01203119030080d000340e144003070510b41d40300850400da0005801406120020003680c81030000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261444685 1250 261443435 261443453
    0x90604240c2301020910020c0a06020d02100f06090207050c0a05241e0310031704031a0411130b09010909122d0c0201020f0f121e04030c0f0909 63
    0x504040d02d24807881c00001c030400c254125014008010071001c82d14940310300c02540c41d202640c6d074a001ea584c0807400100035000188460030964250007034403089641010300402400180c0401e405a40c980c0070024a050142c401800c4d80e6000300042c028030007a0707009001a00c00319a00c1039000d900480c10740048103007841d22401c5074021100106030b5500800018203118801001a0044000c00005000009100000e00002c580c400c00103848810185426050103010714413018140b0052072031800945170360350312a00d622910036640d08203264204004612030f000602d990f08001c80c3d40b2030f1202c44070300d02070401c1c60040520841c01c0c000b20500b60340709a112480500703e8001e0008244070400700724842c04007200507030114128041d40c0000014028803031203104009a001d8002c50580b041c080201007800250541c0c0c5d0310041c40c4040c0346408400c01540540c0c2c0c0e450310a0480ca0058156000c003400170001580101422a611410075402c60014015603015550652a00c80203d00088090f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261445935 1250 261444685 261444713
    0x15090412030e010b090a0203010e0106020a1a0c12010b0a1d030c101e0c0215120103020603060102014101060905090a09080a030f0e0f070b0d02090604240c 68
    0x1140200d100c07842e1402042c0545541c4005a5115072150200070300d50146501840c1221814003604000b81d0b07a412003a601c441200902600c441078417a0002c41e0280403e05c900d0300f041044180504d40f402840103030410380000e03000103a0f070300c100054200034645d00001d40805c542486502451400d0103400003a078514503080c0310360185900503034403c02240120071143d0882f030000c280c000f030003d40c044000e00d01e45050104901c6865044c7c10404252990016200f0004000101001c00d9003107808110040e00002c002c14110341d00c030180c040c001240f800101c020300451901920181050700d01240c070b0711081d40c1100d41c01c040b1001c010880ca5500100c43c1d4111041510a240c0301e80b07500b00850090301a00340040c01d080d000140500c050384e40b40d44088140d2283c21400c04c010389244401c1601d80d0340c01e00d0220915803042030107001030001c0d08018405101c0e401c0c0014a01458900415072a41242e4040e454403a2031310600025010754035454145d803001e0b03207480285240d455a83c074803d00840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261447185 1250 261445935 261445937
    0x311030d02100c030209031609050f060303030402090a2306090108010c09090c030609111b07050d03030209030114040b07020f0c1c14121b12031303020c09070815090412 74
    0x3841500080c1c0b40250304486011b080034040d10b05a850016191102010b1031042072081850240040c200444044506000d400002e01070f6103162156000c0150302e01c4060100301025540b078406242a01c0c82004510005910368007500c142c1c0b41c074608001007144140e000708110303410700e182d550520f030b84105c188080c2c0f1a00360740040c0ca1308420310118024080c9420020202e03180001e41540c85059a028141410000c4140c0041c031030500400b0342c070b41c0d46a11078203401491401c440000a0302a401801601e54082e000064086401052101d6150240c40641d403800041003404a299418040f0510718103480b4003d201c107480d0880866850541c2c03c09204844420801030b504128211402c0e2903030100c61000c032801c0e9541c449030a00c20350711001381c0031f51034859041142c0340482c01242440306542d9100c1498210360f00ca0240b4084144104411021401045407680742e60b542c04101d00c6c004c4140365161005031808903c3c2c0c500c00344610358224420081c500070400000d1442018140304801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261448435 1250 261447185 261447191
    0xc1b040c0c0f0c0305030d05090c0a0302011e03020f1602090c03040f1502071401060501030b0910030323030106080a0c031820041107050105010f030b040210050c0d090311030d0210 79
    0x16820a0312a41003e81c10041c201c0c0000200304004000036080f03180a15410016107031040f41480400c803107110329200003400700310a1029402c0000140c40f240080a1803414058608000540f0002c4c0c136600814208503514680e21854046d4105040c1e00c550160007207a01626600f01500c0b100e04a45000324000c140000c018072034480c40300700c0d805070b903031456004000404204211240da80a80068040c03140000d2800204c1903481c034009882d03038020310b007000c0d0321500982140c40403580119000380d03502070201486584510f640200e00294020220399440340c130541401e010030411b407040c2c101c01e00c00701420601210368002004820304880b0740c1c0320b000078202c245024580e095812201c00159801807030048200c8280e480580140b050a105000030003490380ca409000070240050700018141d003061300c0005006060440400c011030703540e801c03e242441e0454841070301d41010290100c00182042c00108104044a1041c0310350307542c118083d006100071140025620200400403100c9561 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261449685 1250 261448435 261448463
    0xb18010b0319050703060305060a0908180f0a0909020112020c060612010f060b04030516080a06020a0903020607030c050105070f050d0b0f12070807060c0c05010809070b0c1b040c0c 79
    0x129180502c03088070410301c02c0c0010b00d80868040c00510729031009851501445000071035181480c46230b1440700350b000c42100d0400c00002e035400d15054210a50700d400c14415151007400d40e0700d1100b0040102200d90010844141c603100040008901c0c00c02c50f0442c0740107100214001801140b01c40d800f1070f01762a00760358400091001d83c0036200c070013090415940380c4100459802400790060050b2405042280c850101158020a940c1070500c2000595008440220002007075a0024103c1200342c0c900480c003180c4070f030001141d0354892802200410b1001c009942000001e00401e40d06c5812800c240c0740403404050090b149201d003000140c1d14960310701c050b2000e40d42e82c10794800074200140c0050a0280216000c0e652590b060080f000c10748030785140003601621407850382005075400090205203601d080d0041d9140a800b920303840180c06140c0007c10105200c0028000c4030384520002e00c040001642214210080042c4080c09581402402d401340382d00441c0b504200303030b072000c511640b0130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261450935 1250 261449685 261449701
    0x1c0201090509010b0a0305061f0503040f1a0601030b0d0201050414060d020409050709080a030507020111031b100b0f0a15110607021e1c0807020109020604180b18010b03 74
    0x3100e800c00e60344200240004100c0c141d5500241c44604600e80b003c000984545003040518425070071040b03181600180111034840c4558080e5800500c030b00c0c0d16401790155591804028440f800c581c40c1100c0390403007002446d690600a01903503105c01d0783d40c030b1511034141c0c00082c0316100d60f0040b00b001520000341080e494440004844c1d00c1c2150840454680761030b0700030000540400c3e180c00001602031000490245400304d8400c0105900d40c82d0700b458103480794010354403148806070a40302c50009010b240301400340700807260b007e040700d10041c100784030a180000c1c5c11204007040c00f602503c00100c55070720b50b4441d2081d0000380c810300940b1160044ae6030404a4405002840c1080540140d6080c0310a15400080b01010b0800c801b035850500c1c022104156aa05040442c0e4581c8283c00600c480110340540701c00380c0c100d007191001050002054000c0b4215500c25400501146060722000c004050544200c03580c08204031f03010b0101c204030031042c455920b01802440315281000021030558 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261452185 1250 261450935 261450947
    0x507050c06030714070807060b09071b0809040c1e020706140c070816090501120201121d03070503040f080105010f0b0f090a0e07080105011404060c11030a1b0909021c0201 75
    0x42c1d41c440c01341d40e5414076032414144640041c0d8003120000c1c01d241c00350215161090a00313100c3c8005075a044048202a03607460840d1003841d00903100100200114819034645004024410a042c1c482c4c0300000d122100e80a01c51b1701103c0000219002070308207003c0c0c2980555000c4100d02c000160310b48410070200d03264181041684481942c2c458403c40804480d0000c3c1c3d007004880322840c040010342e030798603c40150600c0041000340040c07100d445e0040050060b500022200c00000ca510741c4001e160320913945503034030241080e2a55400420100080744080015002500c3c2e4007000341f19551401c0500300340c0302154040c4440000010800e6050203540b801030311807000c40106407440d029920050010305c00c0c410f907042e1000480c940004605540a0710000300d032200100046c038646480e210f0300300d8100b0300d42c10302202c0310318042000c01c142daa020443c1c1e0000c940105034841c2d141b450640203505520465110b14015414000640056917540b04592480d071509030b0280d90100300b07440101c5007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261453435 1250 261452185 261452207
    0x60a051b0d020f0a08010303030f051509040c320a033c060e0c15031f08010e0706110606060f09030102190315090506030a06021c0e0d0f0507050c060307 67
    0x1c101000b241d4100303070343c0e1720508940c101d030300944040005060b030382407400507214203d460f6846010440c2829501e03050641c1c0c0158428028000010754503180c564403011030580c50100140c0c0030315228040c42240b400704a1000a90040300c020105e00d1440d0760345200d0145500b000c0b4000c4250f00c441c608489003000d680d070380c0722000d42104940b0510300d28005000f03281100f60341095101709401542c0500348034000b0001c078981c111019085555458106040c1c48200c1d4001240d5004090000341c0d5a0090007030b804000e240001030425142072038001865080ca41c90300501650003141400740c60b454401c103d13100b0040b41064944d80e5072031000070a0292041c013001c0c41c00813450104062545d50b041e4030420350348034102c0d070b4100000da4442e442001d07a44180c84450f4503801c0b045180c80010300c0c0340e004020307071400300700e10f910300350100300c400c4007124213200380c50700d0b1900640e240080055101c07280f50403030040c3e800d00c581400c07040d407030703103541c801200f9420f40c0100d10000c0400e0301e003400350319210a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261454685 1250 261453435 261453457
    0x902060c0d0c03110c0d150f05040c0305060c040e0703181509060501050103020a122007110a090218010c030e0312090405060109080a1707020a0b0309060a051b0d02 72
    0xc000601d007030001c15118544000b90006440740b0340b84c803942d035004118200360b03e000400d614520101a241c081d0b600e1781514850651540d00c41d90201181140c0c018a0710541c02101d81d40e00c000e00d10b0419504100c0014188050460208001c0c0724040030350f032505800c0348481c5030000c0e104052035001d8030600100761024050040b80b80c03400d00001600c2d081104c40501c111402d0101e0f07640c500040d17040c1d001d081580004140c940c080b2501280c0d40350300507000015806040e4030501c841c01003080503944000e0080d00d400a58140388030343c605025111000410402e4401c514000754068154110645440d0042c104440e4039009418548101e007600c448000003010f48001d00000540d5807015405005007600441c100703800a0381541c01984404221224a80604605000c0b50b031076404200035009042100c1c00e0902040e03000da01d82c44007403000f5003030300008950350f030601440f50342c5031190040180107444e050500700100c41141c00014011a541c05090f25200d003800134016003e4050229501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261455935 1250 261454685 261454693
    0x40b0702040b0a27061409091018030e010c08070f0f0602030c0d060f2603040b04060504030203010f051605071103060a0507080f010f0b22090501090f1e0902060c 71
    0xf04016402c41003191114101161900300c05404d5007116081e00c11920401c01300081d414000846414070018095201d801c11042c0da00c50140c04000108407042c400d00b220400182c10446c02c1052b070003154013a80c0000034281011041c10070342d141c00051255290080c6140248102e11082003055100340820540c800810b44d200e20b0300c1014105581c200d60042c901c0309003003075000600b5800b03840204050b1080c0240700364084816915070242d2010407181c0001a03c000c000000314514904054070141550365205a40c03140395004041c2034540c120000003c2c0740c83d01d01800310543d540103031460344141908003241c03224558100701d400c0d441203200b445e805002d02001c00c01501c40b641e101d144aa800f0ba101c0d18103d407150940d58840160901641506031040007041c410046820060407400c180351210040391030b5021403210035108180d2140d4110f94860b00180f10818075070051500e42c40050b082007050038041c100c1e0340319050003801d5500b60555a00a10000d41d203c1b40e04458101e0700d070b03808036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261457185 1250 261455935 261455939
    0x30304090c021e15061309020a0e0907090203040807030809121903141009050601020712060204060219030206130807210906050c06040b100e0907030b0709051f110f06011406030c040b0702040b0a 85
    0x50b014ac60012550304019010301310000c6403a40c49442a00d0246810100303003418003540d607501340c6100c02c0141092900b48229001c42c0218400390006140303500c0c0c9804c004460343c0704104068185d50303400d02c0d1004e09900480401012018942c044000c40d40c00030004901c54a54400507420b101181d000700c5018003500c210303901401240e40090088803840d03421600c95102e090358400e21420b8050009005070000404241c031a2002e13080e4480042c00b400d000b92a05000f60b5070401100426010749519206940010350516000b20f0040c004001c9030404034074001044c0241502c13800002c01c01841d030040d00c40030890640c10100d07034001800741c0c404c8181d10ba0410f200e80320b54860003480212001d41003100002d14580c03185644a04a07100a40307124038180100302d260b500300d5650002581040346101104d01c102004120040c0f0110f140e4002d00b200354101202104d00702c00310702040740071304c0301001403204604401d0222400c423001020350301c2d01c4030024070005000d4601201d00e150311000d40100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261458435 1250 261457185 261457199
    0xf020c030c0601050604030812060f1c0212070f0905270715091a0a0309020307120506010812090907030207050601060512060d080a050702030304090c021e15061309020a 74
    0x3000a140c16034216049613a03150200680c0d40300700d01005100f0941071101520700a0201c165680060008041c003000f00704030004a0301d0081401c015400450b40500c02c84194204103064140788109103000c1c0190504200c007410301c000481c4600100543e4481c00a0001584001102d0883c007042c070000c0040300038200d410750740c5c2850380907501d100001801c050381807600841c483e4040341ca510754040341140940d0041f01e81074000c84401d80a01d501d6440b40f10040c1d805005139405010300c81e124520301d8415040840c50000305070401c000c40ea211040d0003038500020b1050780c25000080380e4100307440c2da80030401c601038040d510008105106178000071a4803a08480070b00031b5501c0c01c9a0034103280c0c0d503040401c600341c0b88030940544020740400014000c40c1c801c200800240c0d0000d81104c1c0380651302c034400d0080380c001d4494080180c1050700e100b600c009140030306061200e002402817110711548040007070b9082c0040c0c156807180038002c0348580b01252a8100300354a5400400d255030b000d5460b81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261459685 1250 261458435 261458437
    0x501150308070c0e09121c0501080f0f0c03030304120219082503090510090302060d061707060807201e070f06050d0b030114191401050d0f060f020c03 66
    0x28200d5401683d4a07001c42c2903940c007000940f1442a5500402401000e03441c450700980c0020805c10003c2d07030741e06284540d605c29004050003803c0c5d1310010b140310000701000500b0012414190101074020703001080380c954000040c0c81c1c0040e0020b01860035244143c1c400d80c5450304480445000343c000707442c04424489840003501d0a41110131b03424a850340401390360303400395060040c0140840c0d0000c80900032810603854010a01110782803000280761244c000070444d4000e040c10840c115200d24007030042c00c0d00020302c000c50380407980041107080c0c1089400340c028940104204100704c045803004410300001c8070b14400c011a40e0054518401840048400641c15815090014490320070300140c100c440280b490202d450f150340d51824079000406140103040d0072440c155066484251640030401c1c0007101601400f003032901c0503007172902030b031501c801c1d103c1e889a19001c0050b03220040100d42c0301d4126801106a1000508e005c52807180f4041f001400d80c1c410030790005101180c24411004000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 261460935 1250 261459685 261459697
    0xa050703020427060c030e0f060109140c030703090f0606080d020c010503160e0a080d120b09060f06070f060e0309011d03120f0c01022b05150d0501150308 68
    0xa030701840104201c2e003224940c00001959120070f6038000c40c0c01004105182d021303003044419860007041703d4001c40f44a0b40307031103098007444015821140041001980034460000c01d20302c2e01c40a04030301e142080c84e0380c0480c0402481041071507143c4d00c0d440100490314200c942e000d540b0260400106441d40314040c2d4ac0e84903617118201522030b440b501102580600152442900000002508442d00c070000320b0b180c00340030491a4001c0d07200903004c00c40000601071444480b810b41da030b10030a42e1003103450300c09481e81030720401c0c000c03182c250621019880700b1521a014500c25144999100d000e4135109603c48c5582c1406003c66140c90004240d2080120040007107da003640c415142d0000005800c2c000d40a16035016030552008506803a10a106005800c034002810111030604003040d03070050036030740405005294024070b10340c1141205424490300e2801078108208201c14a024900d02880321007002d19984240c3c0c2c9905017500300b207825040f04031540101c201c0700b20031940e070749400c0e07500750401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 261462185 1250 261460935 261460939
    0xc03020f040515010f05070b0c1309021303320c13020310060e0310060b090a09050702060c2505010c020d170f150910080c0d020109031709030a05070302 67
    0x60324200c0901d040d0007001d0240141444100d4940d1514005540c0704418110b040144a001d000c25030216121581c418441c00e4a0203120390348801604079840401b2445c0c0211901e54411711580007080c18a031000c82c103503580018641300e0303030f200415201c0c1200c00d40407820010100001c05035003540b030041000c9130802c2003501c1049040e2001c4203210309900044888040c0410320010801000d8400c0d002d50002d40d8000e003c2e0b41c0c4807541c180a8506641181d0424101440c001075004120304041c0303013460040c4543e04e000c20203030400c0c44009403603000140c40420710440c00b003451a03103101c2c2c1208060058084508070440325a0502e40700c1d010700b84805948016015580b20301c0900da00842986400a42c1560740d540b1903980e5401c000d05d8800017030050003e4168201c42c1d11440c0d15440509409400c03000e0311042c51502c0c0c085000e18164032803400c030b40103100a000040050340c20000400580341c1c040c2c442d0121800881510b040342c054009039503410311810000c502881400f00c3c034401a203000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 261463435 1250 261462185 261462199
    0xd050a080906190c0b010911160206130311030601090c0807120209060703022b08070507030917030c070b04060207090b0f0301180c080304030809060a0207051504140f030a0b130605040c0302 83
    0x307541f140b44102c030b1410542159068040150b0207001c1070100780302c40b03a207200410355410720b501d03021011400c00041d0030844075000900c51041c0c051800304101c60043c41b00600500c902002c8410080814502400b000c050102d1609402104815901562030240c0060042d903147da04c02d05000703565041411000b800c0e07001201c6002c081c1000000a4588145240c1301c1040c83d0320b55100496084d0300108080e01000003001000c0f82d140a08181c60340992098001962110300c0c6a2015003414103960141c1c54aa10401080001c903801050074802c4405042c3c0028a01e0f002c203020a071007420341030702a50306519040c45803583c0808100d017a080039008000c1041d40c55110302d0200d03036038412800080e0034400244070041c0223140c10402010306141c1c82c1705860f480343e552004120f40c1c00c0c0038400524006000315090003510b05076224110700e40320403182142126075040c080307910f4605480d000390072084c503c000510400c0349440303600d1399503910007001c0140d45854104514101401c1c0030482c820301c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 261464685 1250 261463435 261463439
    0x7030e1c0e0a0801020f0a1404030521040503030a051801080907050609031f090c0e010b03042a0b0d0b011407061113060509120102030411120c13020702040b0d050a080906190c0b01 79
    0x23044159020340303a0000050900740c0c0c5881f40c1b501c18017100d14541c1101102004040b078562018009844042c0d500d88401e074580a554245040f040e05520601341040109401c00c6810600090040111901980c001c0d0b501c41d0300101203410152200156400010386e90f800308074110306940082c010b01d000c0c0d03401144951f00c40160800c00c2d1130a100e070040ca0030061011402288240b1181000040005840b104c1455602c008c1480c250b201d600c0002c1c000404100d4504a00300d83c00b68030315155003442d10710a108070503a000186800340180c09031245544401040b4a480c036034007120304080da81c11340e40300d202c1e0f074501c0020455441511440d00560070b01c4000c1c1302140050007924011a80300c1440a4488488010701141410050312040c0c40d20901c4034a110a444d1451b040d60311810b030003405641d45c10203005000590340958a8a801622400800d001169000c1143d0400d45d40c05103005c0c2e5142036010010340c15004901c2c074408510099500d40ba030464000384c910004c43e2041114100300da03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 261465935 1250 261464685 261464717
    0x3100614071203020d0902180426070813030203070e090106060801180903121104030b010806011211033903062802041d07030e1c0e0a0801020f0a 64
    0x700440800030302101c04801c5100000d030003074000d40302c0301d1040b40000402c5003464000496082e580e01a45006103d943d040c00300f40310401241520900d640c3e11080c40700c25941910441c58031651030080c189070700c0030945a2a91000720916001541c006040782c05084c2c58606e00c10035048203540c0d61507290318003000060b0103402014524100c500c058191203440ba42c0314100d0001d4204030300100e04104007841c05038040c940900c030b081c00c0d2800d241191500d4500b10300c3d1243c4940d4040c0c01c03150f03503039000d07400410000c021003010032446940148111003040090011924008070300c02d0220600752048515144034031440038a80107440c0340b01201d0b40601d40501407580700c0e60296890024101101e0001e100065100f5030034901d000e201c0d20061800d43e542c03001c2d400e802107a40d141d02e481f000703410a020696615000b03005400981a002e040001a15040c01d10036035200b80703803641807045850340c407450f0ba038a40007000c00400500c1c000b90b545255610040c41990b12510307150b40400c50003200d0306014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 261467185 1250 261465935 261465937
    0x2100c020d0c02090604060906080c030f01050c0405120a050304091b0e2d130c0906020102030105180601020a0501050a0225080d02090a03080c0703020a0501030b0f09190203100614 79
    0x1020042d20b9082108950742c080c42245800201019085602c8800004088c000f03032040c2d100500410014083c1d4403007410415003000441c0800c1001a0f0400c0107006100168100b00ca080300c000301c4141c484100d081144900300701c80b1a001801c5030002241c0040c031110141c00c0404821502e00e0000400400d0081c00d6403004141490b00d5006120282600340030041c59000403090a4241542c0c01401090400640c403140781d4802010f065845141070403113103400c1030f030403006084103000039404c0d50304281c00703ea005401d4400a24016449501083c1180d009000340142030760480e000b8407051900c8003544000e076102c41201818080700680c00f01c00e411165140c0122250701c940518506078100040c0d801035040303e0340c81a80191030102c0003000070743c007900525448040ea0003608d02149180100300541c0e060394002e906250400003521026514a0040c0c82101d00445089400740c9407050b84185c038412452a0101d154800010b02080b600c1e516214021150140c0d1140408030010340074101e2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 261468435 1250 261467185 261467203
    0x2040f1401050910090510030512030702030703051309050708090d051812120c150604020403021305040804092f0c03070605041b090f0e0d020c0112020f030702100c02 73
    0xe00c9000140719510380401d5042c3c10101d4039044104c99a10b5588940c00c03140705541860450b608181c1c20000c0000621000780700d4402440c00741d066241c1341d030019403207116610004040090000e070110a95280d0f94149002d01100380d01004180380900703003c2e0a2a9003a0350b00b40140c8240c0c02e82d070604c0d920480480d81e201e10060642c080c204500418001e0b034503c078060140040c000e95000f4640d50054101629506032240024030403c422112981c0040502420044c000d81c0100400e10158035940044607081c5842c600000c3d0b00d65940c203000e102800782d600020092070a0104051280842030307800f45200302209030f20911807420305551121f42c42031001441d07250f0001e111070707008a406580810350040c06032150040003c02c070203041500e1041c80d04030040841d601c003c103c50101042c400c0c1c012038001c1800800d20001031680207541c40c0040400a410030120041856003c020703030301600c203090100c41d40183c503420070f190b0194a0381c2904d218220b81034604202410072620014030585 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 261469685 1250 261468435 261468461
    0x2607031d03030406030f090b0c0307090e060603040f0611040f060315060819060503010c08090c0a0602100b030109060207030903021305041101030f0e0d1d03120f0705070308031302040f 81
    0x114184c030700b08041d00500080c10144044c203607204185000f02e41900c1400b0310488402c09201c0d81c9140412002d080382003250040a1000b0305d500410a00752107003400c60390841d4100c001a511440a4a04840500049440d01c01012000300c5e0010702d229075403408400f50b8285440074807108030312012441c19098188503280000702000007017034121a01400710112207595500100320346440f0004642560302c0c0f088000009240300d01005065601404148802c24048034800541d91030104001c1d1348030040c21040c15825602c004850b0300d0f80d001d6000207071041c0c1c048400e6444010904000d07003280401c0c4001d03800794519902400d5040d41d50b1103294866503000c0c55040303c0ba900b0340f004500400700c940d04a1070a5555074407411842d8810020703584d500c0c0e0141ea0b00d40031181c03c6402d0484c8154030041d40360003a0301511103040019005400e03a108040c400040300e40b9482e20f41002c924141d290343c8081c1c00e1110000a10640408680d0ba80400034001d440034040b404002110000312010300c0b01010b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 261470935 1250 261469685 261469687
    0x30307021212060d150203040c0e0105031c08060301090f0b100509130f020f06030a0905120a02030301030605040c0510030209031212070e041d010209040c050301030308132607031d0303 81
    0x1034810301c1e00020b40c1324110300910360640c2044580070284c08a03402502c1c00d44054042441c02c100f00746c54100604e000d007030309a0203881700d2514071101100502d1560599130502c800740d030000f5103d46003580840c003401d41118506a00081c075041491100906544c03004081c964240f01140034104018000c1c0a640f000005440107202a202c10050305d1024400b00d03070248001c902c10307085640b850040c3d8042c40009500044407011031501e240350403461040414800c10a101d006001a0080181d07411207800507408100340d0740380c0ca444420481160070080d070040780400d801c249071341c1c543c3c05403021480075412501d0900b41691118a14000c0c1008890a00b644200040c0d40905c2003d442119400c06000422241c103215031003040a500e01d4000c1156a50228200d2503515040c0941d80c004039880c10500c0c03865056450042000400134082d00a40b655010260104420003101860014070030204203547e50801c1a9900d0907844640243c0000b1400300790301c03550031859015220507110080c021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 261472185 1250 261470935 261470941
    0x11100c0c02041b0c060c050f030103031707080c0702061305210601080303010530030d090303230f0414070603050612070b03130809040606090f0911030a0203041112030307021212 78
    0x90b501402440d2041b0040080c1400240c0036501c0740ea0186002e144240c0b5020030107151051090345101009100000708030462051048403040d4030211a2840c1d016600155540b000350300303c01c010122a8480d80e00130208401c8070240c00078001150484c82a0441961400d90b6079509007a0350340020f005085e409016066480480c4980b24807850780c50b0a02d8141810003060340b036916095810103a20400b1060300d442021080583c5841594010190200c0701400d04080d03a035200e04003040104401c60075052000490144180403000324000d4110fa01100c0b42c49440c0d2000901500741920a0b6004400c846001c0c805400301042c145c00381c61580078241c0c10b46d03030795030003030070844601030419111940c0c10824001c49032558000c00000e4140350b2506c128151400300b030031205004a9004419291410000341d12400c81c14040702e8111800c507901588903180c9080c003420501c001c45501394400d407035041130007260740048082c610480c80780c3c0a07220502c4001c6425403191042100e8181e52075080000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 261473435 1250 261472185 261472193
    0x10b06090d0222020d1401030512070503070605010b0403110103050402010c110a03082a0a0506041704150815030f070e070504080609010614120303060111100c0c02041b0c 75
    0x1940c4915000400020f0f1802500e01941c000f4600e9054200c0901d40000750070803020fa103801b40c10402650288001c20030761650300c4864441810110045c0d10741070025242c01071090030030680da203440d000700b010072440d69103462030156a07116120898880500c11500c0b51958028490188200c0c2c06031541d5094511030b40c0d40c01c4419002180c1154011403060000c008134040c4070107450700c048500c04e144001c0040c0c140c40c0c09440c1200720f0003402c0c0d0303222241c52030014002060b1643c2240d030014060030400e078104500200c45c0159001034520001c040c04000304c05900c078400500840410180c0c14019482101381a101c40209005544a074001001000300b214000b210a6001c40e040c98000d04054844004604001e4103a4000c1c0c16a9100c1c4002c7c0801082e00a031060f14690803128441d10030780340480c02d0703201e010051040d4140b00c10b4800300c030f160000500c0b200381c4401448608001201240c6e00103450406008010ba00940c072b001c0210001c06500c00105c082890152541000c10030943d031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 261474685 1250 261473435 261473449
    0x90308030609101203080f132609040c0804020108060415030312090501050112050d181203030906020309011505060327070e01062c1e040905070b1308010b0609 70
    0x85922841a001000000e8001d810421135015920942d614100c5040c40e0f40001800d03840506803210050b40c1903e40c3c00002d005001034480c1c80c0e124039258121000c203107070484c41c60288100c81608107007040049290141c1c0855071034843da02c04d0301d030b0307400c03585076201440304840a680b020600440710242c00d10109000d030803079400300400b840000c1488440c2d56a16829140c00780d01c06c01c1413048910b00342081000500030500541d40f246400e10860038254170603031030348803648500010f00c0c52a001e128149403203a00518081e039080f100643d941d0070800c00e068001c1004000c0c40c0341141101d04082454075102040740d0045404e0100811249211341c0e001034100c107201800c000603c81e8850008900403001c403664000c000e6a1120240890302c0b0156411602104040564621180c0300000c440d648412550081031046850490340101103000300e801840c4014000e44240f103044800a02c6022070340c01804c03108254030f00307101c10f142d481110780c1c20f8952420030203074004810302c83c009690070158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 261475935 1250 261474685 261474691
    0xf1a0609060702060705030c1b030d0e030a02180105010905030a120503060105040e010f1403030306030a150e06011e060f0c060b060d020c010903110d08010b03070203040b0c150601090308030609 85
    0x2400740d07241200c0c50380001c009070f00c8035108541c190800300e29102031020a1100082d0890400e800b81001480440000c1c2c6030a442030940c0c003030014409845603140c800b0030640303800d03641c0581410a2080c403d07410b203030030030130900ca494005140d9000105241c1004580303406000e0b84280211415212000c0a0b0b41542005000c281000401c3c400004c8903402941468000e2400c0c1e0040701c1c41c68103280221036812140302541f1b020f80c4c41082400000e40f80002c0c1c1c045c220350888209126840315540500c00752440042d00c403414032440c03002086900b01c0002c8802e0300b461420000301590b540340c0003030307400191004001c00072035480b5540d280031400d5a00180342014005100c42d18003092080100103d801c070000303c0283d6950f5487c10750400d90001d0743e5a040140d08001411420405480144110414010840c500c0e00100c0401d0906000300140c5000d420f41d00000f9444800804100c3d64521242011204010112010465a501a40c11201641e8020200c40c3c0303559170361010321014002c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 261477185 1250 261475935 261475939
    0xf051206030109020a0b0d0f02030103151109041d0c10020601090c050403120503070e0f030a03051303020a031514070509040b0f03010c091814040b1b19030f1a0609 72
    0x3c15160005981c0c43d031003440a41102c051054580740710750380d8202211802141041894410001030020034401440115115a140404030b400b0024800040c2d0034084c555081d9007103403c24040c2880b0f5524050800a502582d0b01111103c407940c40801c084012071211007400341c1c01510043c4006642134008200e06031150034911b1811fa030325034405000b107141c00c07041c5000800100a2051390b907409881e514079618100d403402c000702d4150001945440003030324003d0030700500140ca4070400c0440040c0c40d0045400400c4024219940e0502d6100400300500741c0655a1810350f80300c500d400410075003401400e5641d038460828a40308103120040102d03d00503a8800182080c02d00155001d006644e0140c042d6600da250340da01d480c000c0d1000d04010030b04141d515013020004520051065105580302c0c0e00074466040070307111048034180c4d28038080505100c000002811469104030101a00220580f0395001c1180c55031503811007049580c595880a444180e0f000c0640b1030385000b0780601901500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 261478435 1250 261477185 261477191
    0x8061005040614070f0b091c0801060507110306070203091009030b06012706020d18030b060402131205010b090a0912050f0c0105090a112e05190306150f0512060301 72
    0x2e2601c41d8182c00017089022aa0035401c04104aa102014001c0c50b035030480d4070304078a00c4022004d90181c18460705008502c104180403072200240203004501c100152405000d03070710b640c10003c0c802503c0354004030005005402550400b485944039480b00c2c4103e94001c0300c65011500c0d2640116055252803030b000e4014034442e280e001d492080c04410708002d1134a0b400400e00006000750140095406081e1644250b14406041002c80c4884540c1684003c0484006a580c510f00141000c0700b0b405801c94078001000303000c16000c000d030550080c0384040007211700107a182c3d125010f240545814078401801c48094032145882e007402480a03208030001002d41909101c0b229090908651088500404581c020242d074030034003912a840e001d01d58015600d001e03020a18091610801c940101e4605400303010144005410307200b903064a024045441d06030f000c0c0c049254008003d030025000d200300f0010701480300c0c803107640104404c030301041d00c940344c050400d4091546100301d03000091040781c142d52 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 261479685 1250 261478435 261478447
    0x1060c0c210803070c1b0b040902031b0307051c2f160c031a070503010b07020a15031401140d0818061605010e210304051005090d08061005040614 64
    0x2103084041d62040300240e442442c1500d16050011006001119501b400400c5800034000110940121019594051005a0382c3d843d140c04c0340e003076200d0b80388104400d60804820300c19401d43c0100144030b803464081c05402000e400012080071915421452800c0c50b07400b101d2a80c404201c60080c0282c05200c400c510b0401000421890b603030b0040c401c0c221450101e034003060041104003a070900e80c1c0003400a05150b28500080042c10511040c0104003105002141c0c40f003c554522000381c1c040d203044500f1100760f852107213001e0090548a541c00c0350380303c0c90a001081640301c400296181001c001c0240d40e09000399100c941d01da901282c20b03018020b868121000302500c4040003003005007454640480c45281c0307030812a00b110410720303841401d504000e0000000940460381036010040340390b0b60655075110f62401c1e83c5400014095648c84508210811028480110300000051142c0c0c4a072001d0740d4030401000b2491a000c01048003088042c4402c2c04054030580541248039000081c1d10714080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 261480935 1250 261479685 261479693
    0x2090a0f05090705031506010f08040c150521040506130f050a0308070906090501140d0f090809040c2a0215031302120a050601170a171201060c0c21 65
    0x650102d48076207140d400a1030402683c24100150100d410b0b15018019184c02d007400020400b02e4007003a0300c810850341ca008902808040070410000b80350300b070001d450341020f0740e0303024126070041540c0034407981e2401d19585c42510a00d810034450707075200000e40600d03a50b03041c41c04a00d0300d02000030f0f258290000324000014404001014a031402503d84501c1c0d80b41484000304184402d801c03c0041003d0041e041046036000b0410740b001c07041900613107488110284000c030040040d02038100c0c1186c103210001d42400a50001840c3e10442520240600c00903043c040e50007400c003a083c040c00c2a12035242e0088818158030b071884041c0700070302c18800c0110000d240c0c885500203032a61000c550358041d44c00214075065007071800c0994880081d00010320710f6150103807201e030144551034050481e1200c82200b843c5c00c1c00340550141d841451440000751020410115820194940b4140000c410000c20075a00600741034000e80e034404010000c03503040501d01c038941880c0340d08a0003d9881c10203500700007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 261482185 1250 261480935 261480941
    0x20f01170a1d06010b09190311010c0f06090309030209090f07170703050a08030a0b040603050a0609170c01050a0f0905031801050d140702070510020706081005030307050f1c050702090a0f 82
    0xa04103c0c1180c2d407034201200c1044100c4054287c1031240210160003007002507403404803031030001000d00705814000250b04200d4540e401c21100141502c3c5030001607001c040e0841d0905040e64000d44044d600c170b07541c040e035240d0744031024409121550300c40320080080014409244055210090641c0e905070b03980d80d14a40b41c5102008207c4858901000b08801680c00c1d20520741c8201040f00c0c240310303031483d6841e2a81c440380e003810302500301600c40280009022a416119900c801c100c0c0f07184e41d864084024086c0200030030b9950460031400c0081101251801c0e0082050380c981102c046c521740701c0400316101158504243c180d05119003840b4030740b441c4c8020b105410075100d100c01c2103001ca20303010000a0500703020f50001803040d1003080c250b2035041d41c00154903081c0c403c6402d21030b40944442c0c40c1036160000c0e40d4003480c0e26110010344d03c0104180803441584040070b000072100d8180c41c42d0200c8210220b0551076000061045c48818094640301e013a8a8000c16031010005056031000b04103016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 261483435 1250 261482185 261482189
    0x201051003110303190f11030732190311060f0c130b0319140f180304080319020f0a02100807210c0f0801050d03050f130306050103020f01170a1d0601 66
    0x21584524401c0790260b017001010748180c02c1c020203940307030585036a21b15030203031045551202240e0340d02b01055010b905440048801e200494222118a448064000b03901c41110404800203048010fa60380484030006852740244001c82d101707001903031604004841070304075600b108a42085e0910005440c051903006601901002c40710605940901c580141a1241080c000c640c071740c0c9900070091014040700f001a00940c41c6c60308070b81040c042070304040c514050354010209a01000a11540800e0081003070010700445400780ca0069100c04041034591480902c080d4210005030450200d1703502c0f8164203035228541e820003201d0b1036800c00038180e0050007090208810b580d0b4a01414210740c10000d680302c000d025140c6000c6544c14100418407a00180800070284207010440d008004044402c4d118401d0807650700e403503072030781d2418003001929003803000382d0148850304280301e8039503c6410b50825654071614540442d85a13050704c2c90003001b00d0346555880ca1004e40091000079014000580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 261484685 1250 261483435 261483437
    0xf06050301030b15030a031206030c0b0405101e05090a1d09010501050a03150506010504030b09030a0311122a0a1d1008040b060d060612030f020105100311030319 71
    0x6101e6040d80b070101c8802502821041242e120028443c01582d00041c500000030750500e03080c0340c0d000d16142004043c1c0340940000300260540000492003500c500702a00c102c071000c8034043c40040c0c0302d400035558413070120305000400481c000b030f00c0541405a0001d0880700f4014215403915980d503038031005980300032141c00e100d409a080074850482024010940500002c50707401e640d280c0f030b69940b042d003400c2182c40040314507140e400280c103d84c00395040e200110340010f0310700b009240804140d80c03a41d01280b4950042854004040c0a030707220113090300c1408003030b6424614140c80b0344d2030490002c1205248011070420002c1003841d12030844003c0e02e48a04144c81e56032280c2402000c2e10b85d131808249040c2d00406000666010660340b04101c0c60304135400000b50103080e01c40780301094242c540000060500ba007024800520f030100c2c0111039100b103000b07a4844000b0324270903508030300f600d0b000d035071256402d2580b14051001c18282404a03c001c10000c08030707850301e050702448558031010300d0703650b01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 261485935 1250 261484685 261484687
    0x40204030602310504110f070302030a080a020313020603040203010902060c010b040e0d140a0903061b030c0c0506190b0d1a010b070c060809010e0f060601110109020303030f0903040f0605 82
    0x14005004200840c0030801e8400c415951590f034150b85000aa0345449200c2c407560b1150340c0340781d246110030200c6a070b0115012149a60b00864140603580780d00c070380154000079400400248410002d4402d6a010b00043d00c40c054006509030204116070b000580305980c995603c0c4461001652644020b0035032800c41710012032940094010001151458482e10301e84d41c110494501c8240d50101049a181c0030303003d280b03515240c01d2141103a800030a6080188410f03d000c0280c001e40708014000143c083c56a90240200e006044084034042c2410310b000b801c5501160115601c01c0c81100240390704464020005000d00c80d1b80002003500100c40c0302a140a000326001c1c0e583c0c402003803402801741c0ba24120390b03464a0003c0d96000c001002620450080100c40004078500b102e082d0002c0102e80760f031000301c4094140c09000380b500c0380720a9510a012800101707012a4681040c0102403543e0740080c00345040d42d4507403088544c01100100319503100d02007004082003800d070102c0ca4401600d415a946 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 261487185 1250 261485935 261485947
    0x3230420010302030c0d0c09080d02071a0a17090a0b0a02041a18040c0509031e011a0105030411120d0c0506130f030e0301020d020a0507060b01050301030218060609040204030602 78
    0xd940c00030141658241014010000c00000e15002000c50700d0450401c100000c1070104c4020440c0c00c803031aa00800003e0142d5102c448100e907001803c002a0340c64402c0758007040084141d500c24600c288145080440c2d030940c10401d14031501031300304d90700140040940b03075a910155500140d0201c101c1c0c54610040c5c4c0854213024503409050001c80340704d9215150341c07400340001002d44513409001c024600c100e071110313000300e02c2621440660381c00100182c101e924403c0654030406515807142c040c50b176907618080c14040c001c04c0499100c0041181078445030b2541d01d6645540318507440c1d00c3d0305180c115004680c106c8011808000c10100116660340700c2c000c0c486140b400d0742c200030014008001217840150b04034042007035401c80180055150030f05205022103034000ca03019000d5892140c942c984041084034146c0d40000041c510284160010060804010010340d00b600080c08040c0d0401106800c106600c503114084d107400080003443c49091503502c0300010280e034482d410403200d90340c0121302 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 261488435 1250 261487185 261487223
    0x509070909030203220e0103060903020c1302031e060a1701180c0905010e0c03060f0f040f0b0a091a090a09061503150501031226070203041701021801032304 69
    0x202c244117602121001e9216282c25900010b00c44180006003001e0340e2000030f081014003c000d180c43d0300c0000303081c003000098000d4030300d0000d4004480002c904078610401184021850300150311840c0c00600e4a5000c5051807550030b07850550b18040841d42d942e800c148010300500d11240b24982d8801c0c404850000d0800c103078407043d2801030744910704d00d2100b1001c0c0154070f891481542e9201c44151554980c0e185548002070301110807400c10b50700a40f40c408500007030a0190003401c103050f81522074030b00640e03880c080300044500d100c01d4409446c18002d5107040c186048104140c00c4404100f0104000502ea2120400c44180540b21801c9010940003001040980780303940d4074050807003000b00b0040d03240d5100d04990350302c510b0450041001020f9121011550402c1000c0c0c0c04e1482c9861903214640048080d40c1ea41c007500803400c03903111260f09503900c1c1f5014000c56280c821080030580304c5410b00001580685403690403c5034100140c900c01c114003110280540c4100d006441040c0c6850200c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 261489685 1250 261488435 261488467
    0x6030c0b0304150b060d05060f0406080313080a260f1306030501080a0f020609062104050f0714010e01050d0c120b0114040314160e09061006080601030509070909030203 74
    0x4040e5590800882c081c00c1c0d9190340941b40118481800802d19503140d4001848007011405c000f41c0c882e14006000c113800e000040504002c010728a05a5032054980bc46e1030341c2c0b05403032074008002c10140c0d1103112010101107245080c03098400040c604000300380205a0f510b40001c10801c1d000003615100304004e5501d40210341c01852001d000c0c011f0707001c1d246c0b2605521006050080d0040b000094010034a4641c042110041d40405c0c10380c9244628078034481340070380000e0301c3c00e4400d4422450412520310010500d50100c500c1c001406812030750300001596108092196030f814030100784000032035400c0038091403e000b410384c2c3c2e68001d00400400007004650741e004d030749810810282c80d500c252003030346011102900d03005407903003801c2243c1041d01840c1c01c0000b034601d07488550b1a400025000801d0700ca00c0d0248070320009440e042d40d1461604043c0103500e20036000001d484101158165010b81d11441e04101d8101c04d41d01290b440c1d0140005072217514038200d0050344000354804041c00614 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 261490935 1250 261489685 261489713
    0x1306060806070c06061710050603070503030d1e0b0603220606150f021b010e0307030215030106080606070c03030e0a05090c070515070f0f020a050604061e0c12020c0106030c0b0304 79
    0x1c880c406c0d1481010a4480c1e880300d000a280c080d259840c400310b03071555020801030001302070040850382e40d10300b003202050107400c565021441c020780903889403c840140d0b00514140a4028000701c2c10340d0b40e80c03141d000c900c078120304d240e821a0304902c2e60200400c5040c050750300078000032003440b12180081c02008142c410041c203107804540008080300e80103c00101025000701d800d1908501c007105150000e81441a1603100079440b20f00c8840358000441c801010754103c07034050303c072169160303038038030511070503100380000140401c1c3c00e0070381400064040d809040041e0805400091925155030106484040c1540c01c03100a04003c00c051040003000c02021108440c10815000b403824142c5014205441459500701400510f07100e51910500c20483c01c41d50300c0d04070040355414105424244005c202e45410141403080200d244200400c0305e000c0e034105c01c2e0060343d8811901300c440c0200300094001c20100c0301a55280d100008c04034090b080a000030344103507080d19540342428035181c00940d141c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 261492185 1250 261490935 261490949
    0x6060302090a090803060f06210108060112020619050705010c02071e080a0206210106120f0b15031005060c0102090306060d0b01030611040503030c0c01030605030102121306060806070c0606 83
    0x4180b00f200012551000d42ea04048159107550250a50f00005503950190742d1042d40c80d041e003441d101c6485211400e0886c101c4110100b59111170340ca074104084900011071010350407020400491041d2242804031144100b024500182058141d5070b480c0c3c203541c0034a050500603449400300380114280c01511381e9030501c00310180d220752407414024580300d4a8450004e4407401c404a5100242c011011229141001e0b251032903c1d80e603100c0e43c0240102c032403101d241d01860b00d81442e02d9050080f5104100115900030110301401c1c10540c4041c241d03520080c0b40206c0b0348409403000a82d900c2d80c0c0090030441a81e58009a10b13000000f090514106000305130b01d1003035190400490101d2050015141134942011010940e44110741c60b4419522482d8800303909071000190f14070b80c962001c91040030240b4266020311001e5600c1d8105400d0f400381c0c44c240c4043c1882d40001c0380c0b146007000c65400c203031351040c4004100540e0781d22065050850031140d01011802407030340c5104020701e40c4a460007411130 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 261493435 1250 261492185 261492191
    0x906010309171e0a0c11010309031d010509121014063607020a030809010203010510200a080409140f06010305072001020a0216050303071e02060706060302090a 70
    0x749031140d90600303080d190440c440d0040041d6040028400c4412400c41d46107008030555606031413000105070300d039503007010340b01032140c0000c0d07058070340c4640181c44ea42038260352480303040040b0b1180c0e1202d00020108690500c982044001c0254031010484100c0b03280e140b0180070b5a0610140c000d082d20240c0000b0322003c0803030300c20800150f60b2010000481c0c49040c10f41c5c1d15060100000e0782490010070090364600d0007540c2000456940001c1d0544850700c80d1b40e070400507481d41141c0c40c1c05e03408280912584040305958003180701c0d02c12250140d680c48014450101c0c070b00c00c030750030b28203000d012002510bc0d5280020305104200c0700340070b185040c1a80c00300715201842d007400801c40700b0340041c001c01d04064880c404640000e100b0070000b81901038030301d4906000c00c2807202c524002c0d4401c0248001600884102d134203020b10001e00d41d000c45001a0240d8504801940c40e40500c0d40e0003140325805c109801104000b60706d418014210a5104850000e0540d045004000c08900c0c0145400450b0341 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 261494685 1250 261493435 261493451
    0x708030c06070f090914090c0109150c02060d060f17070303050f0d2c100510030b09150702010f0e03090f0603071b080d0b06030c0a141b010b09060103 66
    0x1000190081d840100c0c0e2600882d5441503d030103ca02c00603d034442c0a08a06080c040c80c428240d40348070600509042d4220f441c007144183c0150740c043c102d403041c40241480c001c0485103050203240c002c40c48600c000c150915054071580c02274101c801035044401441e08208e800d10465417020000050003100d40010a0001e1465400070181e10802201546046c0e01048031a1078408039089010039052008120240368504404800c4140d042800d160152164030141407010081e803107014010080c0c0c00d80d00f55400e085803901c046c42da0000d00400800d12441c00035114030005400c10074021602c6034004501c5114a5906000303035298400c0d8108a41c1040100002c81e1b940c400c0001d108400696101d0385a41e00d008094803c024203500350844c02a162890100304600840207241401611304200030440100041c02894001102ca601d010402041500160380c0250ba080700c2d00c52503003c40790700c2e1020242035404010807040040c0c00c203139100d00d0786901c035240c2290346942c0490203203400c01c0010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 261495935 1250 261494685 261494707
    0x615010e151e0403021f09120309030b070908250e06010503041b08070f08060114030d0302181f080901020a050901051303021804050601080c010915110f01020c070803 73
    0x22140e0480d440303202011242c0300001560302800c2d1402150000c210505940e9900c4410380d212004040d40300001e540e404020074240c100c410000000d80e0150b039100c0080b0304640e590394840c4409030204081c4152000300052038601002003145038082503079151b8041480310414414400703144c2000c2100c120300c4042002030303644202034a900542120100118030308070b0304803142d01c2d000303030308112071500070031030086040507401c40302c202162003120494090f45c2e643c003071400038a210a007a5640c19086040d00b031040c1c91180e00034103c07070258120307104000c0307002e8000900c078602c201184403100d02141d09090b45440d000004076522400290095140070a4100010250f01c28a80400d05000020407011070854480c5a44800342d039029103002d20048060800b20041e0104940440d1507100303039030010903429004900d1807048031040c5c50b2070310110300301040031003d101071aa0440030004080c5001c107802100300070003e007041d5400001030340c0f040b01c00a0b05003485000d03040f64840e50f2040002b207002c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 261497185 1250 261495935 261495937
    0x30709090b101d0a0e0106020703050709050c1c0609020313020f091b0703030b0907051306020312040f030e0405040b0925150c05160906060315140102030c0615010e15 73
    0x83d440d003c0280042020b01c0040c0700e002c40d580003034543c0c0720350000104e00d603500042c5080507a4000c0301201e0b2416600c045083c00d03103204603120a03000740240046840681030b800c00380050400d0800204a50781c4554000080b82c00441780c00d0195820b643da50f0007542400070020844150903907079003019117801040b9035100411094034142c60040064940281403003030703100a80843d0014192003490801e01001850fa4100d24142003900510010004126000104588042521581c441c10a43c0c5644908040b1141c00b842a02404001107010049031f46520855114910540b00c2160354103107803a600f0f19001c00f41d01c0ca451813213014114001034401d2101210100d400c404141c3c044151024821a014007030120010040c0c0300d00201c100a0030f08003c00941581c1c0886400c0003501e070fa070b00048003690f0078840b11150302d1881e142c0a01c5420321a0303610700405141030040f01d1401d800f400c0070510702001205c00118a0144102c0080300d0b60340321038114951402140d09074201102c1b1000b141d80c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 261498435 1250 261497185 261497207
    0xc0e01080c07110f2707020f0706121d031b0f01020703020303040605040f0b01080a110604060509010c06230f070201090507060305071e051306020f190204060506030709090b10 77
    0xc1038204440707013510b40c0c4c1c611640035070150f00180642c03034000018608281d2200d0a5030140c0250240e05030440308260300181100c1141c0840e580c903800c8402c0d0032101c41c02030510000b05401e86101c5204111340c40801c20003044116117450207000d48080754a90903080030700c07083c0c203044164010031525011940c00000c3e250400c1d00550001030740d40b640e29000b9500c1c4c682a00c010074540c035074000011482c1002c589014203e0080c240c20175900300b14020080640b04900411000c110188040c5880c1d51059500c040064030031400003070b1100c282070803029805015038024540002400421110343d03418420141c103c0c0031070000380948034141d80c80d80d40320b81300c0e0f0155404165484000518140c0b0419030030f503001403124080c02e5460a2000024000e500ca00c02d0411342c4001c0756400202c851000400041d0403c0d450050034440580c6100c085000c0445441030740c3c07103a2120404199981e440d0001e601031b40e030355110a030942d40791000e00e1040d20405101980300d420460a000c400980040501781 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 261499685 1250 261498435 261498439
    0x9100612170705010504030503070305091609091a1503070504021e0d02160f0506060108070816030204090204060203030619080a08070302030c0f011508280201120c0e01080c0711 78
    0x181920070064414a40d010704140684203601308410b20040c10782040085004281540c0e0a1103259101d03460160b9401034048a0701d09003420342401c000d112044d071700400b4500d10513074000704c02d0f010310181903003114010f4513170307566103000709540781c40d0313403504220301801028266000d60514400c0b602c1c2c0c2d100c0d0018000c914480500002c1c070745001c40b00545c1220b00551000502c28a01d074800e0400c1c60b034040310010211014441c000c003103074003903005103003881c070800844d40c1c1d440050f514171000c0000070788900006800d0540a000101d500c091030700203000a004541d00840e144c0c90020204000c001000e081ea001d16420740304140030450000c5880c50303c65810040c0550345000a25040b4174500ca03030b411012003401043e5001400e4030040d00301c40405030305503031201d102948034001192541c180d040116042c1c0c2d4480007403c1244141c05e045103007140141400e56000b943c0b05102070603114030564440000d03088109100480d82c00c41e0449422403204410242000c41c183e5640510164040200e8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 261500935 1250 261499685 261499703
    0xe0708010e12072d06140705120a0f09020a030506041a040807022214011a0c030d0923030915070b070c0602190203090315060d0809010507061409100612 67
    0x15036011301880c86034100c048500d200380c06010705410545d00a1180c0d02201c1e031990341000100c0c0303041d403240065501c3e5840c0500701080945480314403200500c40d1203900544240c440c10b06801695906281c54002c501500140c201407404d8500306003150b049604a07400305a50000b4440422500c1c0103403861290305903803044c882e2041c038240c0fa140f0040010308189250900d95918a080040d03204141210003180784181400e034250101d1010b40900100310300c103607205005041500144d038100c0c140030f9000d000d55003c0041c4620b2100c0595284402019003580000b44030007090804400c1d1168440f111030340e8070b05003400e942c1d440d009101d001e0309050400c21980b2403030080c050aa03044803910141c03514030710345080b0301d01ca010351203410000c120b0b4428000c0c081c0070765031607112540103031081400510030416000d00795160709058108101d0350741000000c0c0004400600310b03101c1c1078004000800f00d825030345051400d051411000c844254140b50501d08104096070f8a021001c079500d0b8032070001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 261502185 1250 261500935 261500963
    0x1e09031219020f0901020d050f070b060402070203060709030323030f07140a26041e1106130e100e0a1a090a0203011703040b03070c060207060e0708010e1207 69
    0x7850700da00d0307008401c100c0e03035100049807855900200000c00041c6800e800703a501c00c180032001502c40340902d10301d015919500304600710000d03a589400f1030740210300030130040c10403410350040b078074010040758840301140040d24284207054204030034265182d80700700c540980d00c070008564001404040c0c0341c041410800300100308602c0c0507200026100105600e1192980000c06004103070310450080a000c5540f29220381e44880f14040e5146d00c0343d6041044411380c030304500c0584400c4c6101c1c140607203900c0d006035003249596468400401000545c009410000341c00c4c04000c4046000c0500004956081c0000030000c241000601540c081e103180d000144808151075404c5410b03d07403143c00c40d0300290030b0040002c850300c103a01a41c16503081c02d0b00d014100b5080501c1c15034900c03440c000c000d0300000900c00511414891039400820303e00c500c0d4054244407569030f8040641350145280145c9d81c00281060080200c01d01c110480c900c1c4400090401c1000c0d5404100306114126002c0c1944404000c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 261503435 1250 261502185 261502201
    0x144303021810031a030604050a0f05100f0b01030f020315010305060d0605040b0a180804031205120a09020f010c03170403022404050d0e100e0a08070b031e090312 71
    0x4084410405002002d0034048248024003c00c0c0588070521043c155000b00c100300d040018000388100d9025004021041c2107468101f0060354950080700d00d071140340c00c1260444914051142c0d0386126440101e000b81100001409480200a005060602c14800c0004048020702e03124100d04080c01c0015054860b10b01081c0c00d0081c0001c064041414074040c041041012100c0e58461102d035002044000d0f00c0c0343c02c40d80035a604081c0905190710030700080c13005c174450004005000c100703030400c14a8840b04c088503041c0000c0c121b03054245180e442e281c3d45c080d820000d401c415040c2091070139030495038040d60080c0c0000b80d080500b008100e110320000701010300801107410f25041840300602c020760b141c011151402403c440449250044208030041140603c0c240806494010031550030349108040c1110302a11031004294800f00c1084005400141441054050980c1800c569928607081e89413448400c484400038003c80300d290b04000e203030135020064594900e00c40001d0b060644441903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 261504685 1250 261503435 261503467
    0x20a08060f040b061c11090303071e140a06060e010f0603021b0303101a0a08010b0306010201060b041203111204050d150c121406010e01030207030314430302 69
    0x303c1ca07000b5400007154074072861164000c12404c004c41c0010301c0015a0b806e01c01d074a9018819100d0340545c0f0a100d9140051010030900c0361101040070240d54055164880326110380766100b48003580d4101040b8801808070a01030400500018a01c101c0d055140892184000c0a170340f01d0030301019404580c20144c854243e03003106040047d04100d035102d04041d100203880d62000e10411204166000b6181c00031070404003039903c0900143c40b082191f86c038140080340b0303a510081890f8115580d0301c60100d64002110701510140031001211029581c01d4074010300003000c1d1010003c40c580c003500c005800070261704d04036010740c0d806440c05010a10b8070300e041d8000296400e00c1e101a58140804107a44a41c40181074480980c140d42c00c0c820000c041c400e040d6881d10544944d800140d50f41c1d100312080d40240c004100c558824a00040d01c0340c0784070302256040105071256529403010720425540c202c01c2005c16650038400101100048221070004551860303220801401c0c50b4010900340c2400412013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 261505935 1250 261504685 261504701
    0x303050a030b0609122b0906260a0203240d1211030a0e1008060f06160c0f050411030903071106250c0f05060d0e07050a0f03030210020a08060f04 64
    0x5490f1080d4180c5c0e0311803107078444862070b81403c025800c44010169141135007008202c040440e0302c07845041800d0103000ca441d1180d107071203e10880390f01d2203649404000388500e00e20882002d5401a04d80c1072114242d680c4130540c6600d0001c241442c0390340710340ea030780394901d20201683c8800f142d1042c0c010803206503803100443c04800410300002c0368541e64144c001c0509030900d00101c410a241c40304400381525007a01c180c07a01d17904a41802220321050918400401da07041c0ea80b1045c034814032080d0350f0429800d81c1604243c0110306070200400c000c0c10203014110907104013146e600e0131490f0070300c0c0243c0d8034007a030790001e40f030800c1000100d6007607290b4900b140c5201c501e07001c5404221060303c6518800310400d42040700c48607000c0100080c0100380100d0740059441c000d06091400c04007030a500b0141005800300c3c1504e010365640003030f407036844d580410000c00c90390701c088003040d1840c14003134146010781c2102c500301c1d4010060440d40b80e9014070025030220084841b83c624817000c00100f4028102c203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 261507185 1250 261505935 261505939
    0x10510080714120703060b0a051518011107080a0b16050a180e0103050c130c050d020721020f01150f090f09060501060c02190302010c0f1b030326010303050a030b0609 73
    0x4c0700040305121071500300c60304521003660000000c654039403e121307004884902c00c46441e4428031409409001220a00301150014586440c0c401365504c0000c2c1002c1c81a07001042990003c0ca524003000920354240d540a03000c94a032940b120000c031006846440307405500c108121503c9589401e8066400d0390001038503543c440c803000c035a140d2070700c1c1e41d803543c0c038140c074521656056910b4444a401070040c290f000100f41d450720704088041d072019000e50046081114134a5a0340408105441c09601140ea201c08680c001c2108081c0c01c00c86508450709002c0c540020562040207101142c40400c8440c12941000c40c0080c0d210060f0382001e00402035030750000e181d141407000003d43c07180d00980d01e000c00e600132039030b1240e14001e4460003400e602480c0b000030301007140141c903180031508110f182d07070030704e4020032400c070810347c0010031014140101d4004402040d9250210001c9200b01035004c8001d2945000305907071941941c401402602500105404058a03000a0340f000e444a4094407450400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 261508435 1250 261507185 261507193
    0xd060b0c061f1509140f01020714010309140c0913170d090c06020c010905060306181b040303080f0702010c2001020418060515070305040905060a0b0a02070801051008071412 76
    0x3a4240c01040c0b13500612800900d41c07a8151110003516002185d01c0c25070301d0580040444030301e40440403d502c0500089107052660300c034030800118070440412441100603102401d460043d02e001c0003a503d001405c0c1079101000c0342c90000c0001c2d15240f040341d10502118650b5100d4015680c1c1e10050030240c0401000f6240044d00000c850ba00001c0c0304807601c000340c952a80c2603132945c0074042c05000444900354440000ba008001a5002c0d285407038200407562010100c002c0c0501d580d84041d44036900440014885a0030000354820840100303030040b45620090060308003007400140b20607070b00391200342c41401c510300310503000e007095048038003c0944400c441c400410701001030005005900c203c40c090203a044190a40e9440d4104480e0b01c540d00d900caa80c1000d0400c50700c480100300052a082d00039000520104a038030000b409800c0040c201e5000382491400c002c9035509407034000e08076840005440100f813004d4403003c90802d00765240401400700030191a000207101c40e00c0380c9100025402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 261509685 1250 261508435 261508469
    0x20d140f0a02101409190b0301060806040612020108280c080a0606090f29030f04060605150901030e07120b0108010c0c020d020f030705040608030d060b0c061f 70
    0x219806032014000c45082c40021581c8509031000c101550301c001140c90100200c0000c3d00c0c11001c220b00e8001c000311b515070030545030181c0c90700fa6842a04404081207440301000546c1c580b50046038080c1c07001e40300c0c0d424003014a0707002030500b140180030100c1010b011400542e0301089441c10403101c0c0c5010405000480014402518511041d22060b1210f42805404981a405090b044040f41d015051070b01c82c0500d0b16035018107100b20790b480324040c003403e265120760a8582c0c8010310b0203044000ba49141070306017440c10324119009079114078059a80805a6034500b5151820348000c100282004150000d40896082c20400aa0045689000070300244018400b0021001c1e05a85c0300710001c208203600c003802941ca68101410007035111110400141c01800e003050f80c201c0e8400f01804890120b6190700000741130b520681c006221991000c660140c04031054003072030004000d10441d00b4505111405459182d0070000d00786406140c0b2000c083d1407840c4008803480003410748041d0600b02c41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 261510791 1106 261509685 261509713
    0x906060705210a021c0906031a040c0201090201020d2109030509030601060e180c0f090a0b0f070b1509040b0603010e0115151407020d14 60
    0x40101ca0b01070500600c03085070802503110302600680c0303807010007800918080e8030080d03902d461320217070761078405050700701c0240025565546030100361049a540d100701c0040f4480461500305207040c201020250b41944103c1c5030718401da0a507030350640400000c841ca030070416800c40d00c540320203403d080800758644c460040d06200b81440c2d420b0252020002c4d0900e4800d80c0240e01150109000100a16040a0501c02c920345600107030b41d1410404590401e17409524100a0852000a0b0b18982c40e56800500c1c0c0040032040f00c1156035112104c2002c0c07542c0c001c8007041f1049074036080800d00d9181c40341b2242100c0038020300b420010b60341e25203800140c250042c01d4079806541e80e179420460170310f0038017401c4844081c01081e070344414901710840c0e600e640b41c03501072410404454820040c1006000032280e5164046490f400240124103044070400d5002010030480c2c0301d403130420300244e = true := by decide +kernel

theorem cover : BRFrame.Cov 261330935 261510791 := by
  have h0 := BRFrame.cov_init 261330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 261330935 ≤ n) (h2 : n < 261510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
