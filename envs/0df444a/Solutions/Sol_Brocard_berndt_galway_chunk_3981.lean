-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3981
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:10.435058+00:00
-- url     : https://prove2.me/submissions/e11e8bb0-798a-40c0-b24c-d46c96882a67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 715827338 ≤ n < 716007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 715828588 1250 715827338 715827401
    0x30b04060e0c03011503050f0c1302090a09020d0c1416030813060e07030b01120b01060e0120011a04020a090b16171b0d020c12010f0f1d01 61
    0x441c40c0d50a0070303607404882840c00030303081d90940080e4000d480a0340c00c0c10010024100030000380d0b0034200d009000700699010009600011102d81070543e2900000e0283d41540c440f0440030203484280011900d410700c038890f542c000d047c0c2c0e44150000c6074401510718104030f800419113114805902c508a10551a6a811600000c0103400c1c030700c0004442280c0800100a8002e0600707041260f0000c00c80303d0315605101e46501d0043e4405000d6070b9038000e4a1000c11204c50380a8195112401c6c180d0000d24401d0040b03946c68903007180044801c0c020980d9407403030803041d00885c101d00c0b1342d8403c402042d600603003004100e1040c8000da4010034125001004a00c50754000340c040302e808080340580e010000e85455061800302e5050f5000a02c0c0000d503060043c0c2046107140e01100c0301c1c0010010302015620195840310039019140c0b0901c40220b072540c0c5c54409411003071305801000002d1000200d510040300213000c0d2480384041300b001c994001145c0040505c500040d1201120759803500e105080001070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 715829838 1250 715828588 715828601
    0xc06050702010c0b0112050d0e01020601060e03250f1d0f060a090203010b0306040e0303100e090102041d06030712050d05090402160f020f0a0e01092406020a0516030b0406 75
    0x1c2c10300050048030340101d01070601c024000c100300503c41c203548803d4500b0345d0410350210394034400c1c028034580301d24683e640082c02c681500e0705801c08884010901000910b40000303148049218100e140024203440c00402c560400c41e07141c8880074420075110302034820703101c0c4c907009840c0c03913400b01e00001010044003a90540c4c1040000d00b100c00d00d2030312400c1c020180d900903001a4280280003041c0401420903120b0b82c1d19044159002c0c40c00c42c20082445004a1110f228007416012080c0c0800d11301d840139411500202517030b21889c05100d80201c160303100d032003048501a11a008090001075031a000f01403d1070041e602002410009000d1641500e084c0c0291012b00d030070941c01e100e498241c003000d1103d112442c0c06642003070b4a1041ea0310410065281a440243c05400e039510708200004000c0b65403410345d2100d6030b020402d420403a1100b46140c0040e1515488815801030000b542c0e600854011100307401241503426101000b4103c1e80041b20f1072000412651071000041c002c10790a50000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 715831088 1250 715829838 715829843
    0xb1c05060408180d030302030f01060c021305070e2d030a0312090302211305030f1905031e0712050901120216080d0618060e06130e03030c07050114040c060507 70
    0x2851116816004200703104c0e80e00c1c0302100826400401c1c4102c4140300b41c4828010040c91524100840003a40814241d100c41c1854656464480b030119080034000d180e0824206c401420901c071030b08c14080d4103540c0001c2d085c142c100c2c2d00809460490182800304859a800f80c0580b51b0400e0000740b24021001040e850384103500314003d403000c0300c0c0540e0021060441c121403195120b5103401d0803000c100d100381b1181d0701c141d03c2039010103c90003210101040c10750900303440c070100e20000e45507810700604512078049448030150a05000c041a90a450f003c1c0021a02416003d440454600005c2c6e94500c6003081c0716012600140e10b0321660202c0360001c21085121200300c1409000e0765940c81c034030360050398811200c40d072a23605c24026943d0301c01d42240c101d009200d041c49030502c1d100b14103c074520060400360051035071480c6100d849219400c681080c1002c10b048131742d40c1c40c0c00d6000b100e164001e00021249542442a0314040344030400c1703503901035500520410001441d1050986603607100c400d08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 715832338 1250 715831088 715831117
    0xc0c0b070e03150619030507060e0f040617120408060f0c1b010b01030e0111030402120f0a05010912021b060d0f0207061407080f0103121b060b1c05060408 68
    0x24041c0d01c0c1c505001e02c2860050102181c4450306040042101e0302c40200e1241400e140c0e00380f400c00c08075500182c0b010880d0b00a040500002da0500b000c54108410100c406070803504001d03000031400c0f01000703841c4204510a05407194503051209a80252090703100d040c03841d0b4400350200f9205000a0a13164101c007840043c545840203901059820484980c018030040e5514400c118071541c15009035000000318000800203c130f20070142804074040548064001c668207035980300310841c00c0000c1c2c020300084408481147d42d0343d107803003400f030b140c200b00131100c03410013144440c1e40c1800090645c080c45001400956030210000a11406401c040c6400301c180c0d41310901c00384643c003e44010f001c514081d201c08245006e504c03400c03880080c4041c1c111402c0001c1038007082101c000300c480083c1074a40c042d40010b19405950421200c20b2280c101c110703400325900c1c14800c100050b41e4000302440e00203030364000640c51b08079015540c615008202a0444e00302200060025003c20014078504400f03c12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 715833588 1250 715832338 715832357
    0x40e041b0803030103151b020714180f06031e031e03010509130219031a09061b090f0a0b1c02160305030603070e0c040305070b09010c0f2d14010c0c0b07 67
    0x11000041f00e14080005a00030320824094095100310b1940c002006954208052714541e100c0003008800030520003401210602090b681d40e802d000100502800c1e50320700e65041901c80c070341e40d100d40c4503400d801005150004280c1c40307441040140c82c12074100804158090303485c5006c0c42c8400308541c50403640301402034001c2200d02e80350122100a1405040e18100090a05074980302401015240c1c04281c0d11200402c4081204002d00120300b12284069a07118003019001c10010918070360b125520031080580460f4000c0c0e110050820a600c080144401c6801070100c001284125501049a1900c0e0100030000c00d000e44001d50301b1071809400c95480681d115117452a82c802680e5440c4041c200007001c0061080400200000d4103290324901d2606244100207480540c072401d00031f05000d20340e10114184418203042010440e046a0107049641008908588070217808504076100d200c48d250b048100c0d001441000c801d040c1079201c1007400340e12034503541203200c8000d01d01d0041007480380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 715834838 1250 715833588 715833611
    0x30f04092f2a0c040524060a1404060c15050108030f1e030a05100602070602030909150307060f030e030405061e040305030c030a09060c150c0306050303040e041b080303010315 77
    0x26a401001c039a00c03030160100d201e0200810041d15009032107803e44002052850750264103d480c42942084207e542503540c004410f0252800485002201e400c4080844c00181c1c16400c80d2094841e50f10902c2100c00c5550303020790490403a1800e00502c00301e54024080c0001403040708008040719032101c0000a807424007140600241e40c01205c00d004010b4880e401c0c091000312954020024049034000380403501d0a00d40000e5a900a0000c11841130b220744011a0301c513200c8080002249001038141d40c1015101c01002e0501c1255103001c00000b4500170568024140100035607051b034200910442c0b404941440f1a4104c11600502c066850020000040012003c000400d640c032441406540c0b80c020211780606259090742c481810f1040705a407000000e1134000101d504074400000020702d2070f002d4a070480042044d03402094140c480041c0c08524001c0c542113140c420741c4190004551103600840da0345144905105050141d030007070006000242403900b010641c420041f10000b5400f0070903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 715836088 1250 715834838 715834897
    0xf050a02100c180308070201081b0a032a0f0206100f140109051008060907110d1206150c14011b031112010b09090603010b03100e0c03030f04092f 64
    0x1039004481c0c5c400b0004400b011560400300083d80240e0b08400c201c44990034020305101842000d04803002c140c1d813082e15041580c80ca400c60322003c03001c014145128404d240016015000e42c4038901c02500c43e0b14009048060071009420582d00c40c100307001405071030003030004c80070000e0342441d5040c000c1040c8007094cd034585085542031020b4580d138142c11400c00b50280030080102038184c8042004109a0b0303110380d80b0004042402113440d181c8031162892040c00f000c000c12054015006101581d2180c00c16181c1c0802c1c01820030b03000c3c4200243e8028155205400c84240040c01882e450002d00325220290007a070051030800d43e0407958900e40488a0105840c03084240c0020220710000700b4080824105401d4140d131101c015002001200070700d10029690b086419208a500b40c1c49092481c840311052049240360a8041e00b120748458480c0c40005458100e8010290041c0c030b0001c40241c211417051900b035602c0854185049494100c5000c00503640c07090103560301c540210400f0880c0950003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 715837338 1250 715836088 715836137
    0xa08070510020c0619090803010302130b450c030a06090204030f0501051609150212120603061509010b0906090d06021e54010f050a02100c 61
    0x3c400c0500000e01d00301c0381c41410740c403480d040c0070718041c545009074002500001c2220305403501220000041c02c500443c6002a1002070075058000c43c4218440c1440912034104800c205d1034000060715645405503119009100820322440d05004040425000ba01a40096400c0a01c4880c0450340036103541c08141a030b80f1076481100c10860a00d04102031203005c0c442d9941051000015400004002c0f0f4001c1c0032002900800d4131104050f040419090700070401c0c840801c02c04080c1c281c450709521b1a1655000b0f04030b55160082c001c000024a5260451752240d60285009040300741c280d00303100a4201d15000301d00165003120041100d10303a9540c0f40d11030034054030f101d0207000d41d54540b000c0c010040704480092090180300280f291050104c42034000c2c4910380d40050100704800810320030048110100035405510b04800b41c81b140ea00f00c20b14604500222081e02c502c502d11500c4002143c0074882c0d14210001a005400c5201c03404010340c10102442a0526019040c40404080c00840303486 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 715838588 1250 715837338 715837357
    0x2151306090302040f020c0a0809040b04060b0903071a19170f0a0b030a020d060203040303060f0e0a06050609010219030509120c0f0f0607030c020d0b09010f1407020a0807051002 78
    0x70448041045242c075000d10b440e102c214131707400d60400e00050305159071102802001000349201044450040c6c49581c06154400e50042017408070554801582d2075507441040307001d00034010280081114441d6900c50b222400039800103518041540d100380740d1010205480008110505103d031105664459601d03000d040080313240881c070305046e250141212542d124540c000d030403240403000581e403600180503c0c140c1102c0c0269681d07035545012401440e5940009003004040580072480c0143c50310390a2003008180000c00485884108011040c02030704e0803d03005070f000455100500015107608800d06100f030a03d2030400403041300084072100d804200c140307154042d0740b07403071294503003014030717074803241c001d0300c100350a0700206001c10024458044040c040c0400054980219290344241030145034120559034250b08152590501915240074195078480c100946a00a10150010103000e11010f40040602c80b9099a074110030760001c07031058075140240d5a100c400b0a01c40d0005185114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 715839838 1250 715838588 715838597
    0x90c06120609090809010906020c0a290a020d080c18040216050f1011192106090f05100e1306090c030f050d0c0b010512030c1002090f03060c0702151306 67
    0x7417110001001900c81d980050115030103c902101c0f03944035190007000390391000e1a41440400061030301c400c1c1d24454825500300010010b0b00c040341c40d902152840d441c140e980da9030006600e441140e1595030285051049001c41b150460342494580381c1d004204004d11801000700c1c4140755140c0a051541013003801513a0b3700320301054100250244500300100e00c0c12501241410950384030390200c402405640d8003480070714080c50310b00e4140b18444225240759000e040c807440d0b03142c4010a0142c072980382d445d005141020b011503008592000c61074196076000c4035041c0c595031441c00d5485a45010756017a506940d0314120040800e40c41c148440c046d40c0101c030032004101407458590700c1c0420640d10b503410018020300482c0052300500e03030241110401c682c503236010b0390701c1000581103100300076203103405100c0c00420760081d20080d000342400b61400c807241d0280c141c1103018562580401c841720908003804106050042c43c11100c05088000003911b11824100035514044401105802c40400306 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 715841088 1250 715839838 715839847
    0x1050102150615091207290c0c010f020a122c0d0303180219170f0a060b0609190e070e01080415020c060403030b0405070314040312150e060a0603090c061206090908 72
    0x7500d00d0203440c07c0c0b00301800260300e8442e456140903265080c0c004050304000c0454408070740707184200300d04103001d500001204031001087d9006021189140490668900e0840c0b505801440b070851039000d440740600261545880380d5806c030010042c05410310700d140c151a4110000d078580103e88942030f040c0ea442c14682c5800e00b858214082c000301d00700e100540c0f06403000082c410002c00d66803992036204d0030105140640400245460142018481d041819540710100203086101c412041300c4e964600000c142d01c506104a5020220046050210340d082000c180020480c240010781c035003a1034401420300070300c11000d60170480152400d600180d16089401d52600d054412103400441c3c41c10200140c2d840d5403003810300c41c2c80060001e070034001c4402190400c180d10b504560b420a0740b803a00351400584070b1081909602054803400d000c0c901e009404240c2074007912522004603001400c10b440d070385c6400c00031200d48668408004199458001c0090281c9c2d55000d9040010b00c50b8840a845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 715842338 1250 715841088 715841129
    0xb0a02040f120b06040612060e0709050702060402090705040b1b2e0507080417211f050415050603150402070606090f060b0d0f02120c0301050102150615091207 70
    0x43c10060700ca41c1c0300f0ba140c00d800f0000c1040b2915070507001c03a40f00b01c0218401100c00406410a590b070b501041c1110708100820684503404100184594422568503100351196041101e8900544c0106190030300c08218062440201d0f092154840740b0310b8044480c0c100141c00c280281030408000041000300c0b8a030f41140c4418140501548119645040c41072032a00303803030300ca500a002200746001900700090b52026403490080c64851440c8001900145d81004502031000300f0103102000c80c0314208200c085841d2a040c003519040050f0712848807552410441040310f00d030301c00342c541c021461204000c400c258485001802c1d416000b040001106864008140c09441034201500e00b5036241c41c1050011400c19000c0e10803072044020700051039452042c24100034803940340c80c141c0c00500041007060b81071130b2100035070680380281d0030368002d840070340c105101401d81541c40650110410b150380c058590148080d014440e0001c040c050300710301c681c00c103070308080b22500700010b80301529420010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 715843588 1250 715842338 715842353
    0x3020a090615020307020a06050d1d0f010c11060703050c19020706080901020901081909020a23030a0c120227251209021f0c05010c030c0c0b0a02040f12 67
    0x10524014005140307428000e86c00a09070008500480080c0040414141d03092082644043e81d0305240b408500020142861950381d00d90b04c00d203003e0415801c0507007882109218902400e145101000180400c2e00d468005030041c142c02046602580030130700039810036190780319011181c040d480c2c001c0d040743c0c1c0c24a0401000d00a00414520a070fa0040004040990740700070410f9000180c1d2740b20504581c1c00c00000380140002c06800796024402c5440400d080c035403440e1800544400c4581c500340440e02e003040c5515058070000290000b803c0750002c0080225041c4660600352000340111807442c2c0440c7c030b01000c0c20759040d91007814400d003c1000040c6e20507008140c50039540030000c8203203600e000d40c003e02c1151030340c5405011603154588481151281340c400d080d0f00b00c17001c090f20217542d5503c00090400c040d000044e941c0c0d6082c0414031178124040d01c00c03860310629030345d80e003107681106407100001c1d000041d1000202d16801c00001031195480036444d409048500302d2034014490717a00740202c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 715844838 1250 715843588 715843619
    0x2060709030f0b09032b050a06080a03050a030f0c020a0c09050c25021503040317060a0b07020102071a1b0f0d0f0201060e270105060906041503020a0906 67
    0x20a1140200c030a01c0418600800c04414550185561000d0b82e0351451190660045c6045943c140601e591124254020440002080c28081c0001c10907582e4031040343c0e040d60b0892144054641040551a0120340300300010113110b00c84d400d000c00ca00c5d0491824008583ca8a008600160400d4981500700091040c1600007841ca103203092280f410891001c44040c03242c0d0030580c1940c3c00d540c07402d02c21591226105035016070001c0c0382c0304803c060b42c241031010398402c0360200c1c0060900c1140310b00202c00c8c0d8803010302031480a4280c115503810300d804d00c4000d0b07000110a0b4150b202c0c0007000914460074410052000f601041081d4135049400070340b0700c01d0035804122500c260026024840c500c0c2e030016460443c404140762800b180b1500000580c01801a5008940500340c1d450800850030903040250b0003600c1e082180031403000b01e012045007295000e484017940581c08c82c012482070f14064009070107503503e1034890700f00340350307a42d00040500304280d100c2150151604070400001504943d82d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 715846088 1250 715844838 715844851
    0x6020f011109040b01120f0c0807170105040f0e0a03030e0d0305010e1326040612020a0e220504052824020d02070c05040b01033e0a050301060206 64
    0x78480c10110810101150062819403800349a541d11079850580c490900d811020210368030030000c1c008018442c00c043c200c0da01e00003022481c15808226100d204c0c0c60801c0d134000000044030040e07400c0c00c040101a000d25502e070003c0c69169140348480791804c3c0700f06112940309880c00510b0b03120340f514880c2815040740021003450318020040200e1000c146010384d11035004d046a6405120510705501d0424081120ba42d80000d102688046030740090002c0041d0340094545480090002017041e0681c89000b040d08000750704001844210704012185040d90b144906540d07030701e001084501d01c2200d10440c0e050f611a48800501d04007030002211001005180c500300d41010724142d181d03e000c1e6072010781d013940340d40e0360504c5840081e111541030360311181d40d480007075640b020300e4180000c0300e04260180502c500e1901e1103421166000344540460701c0c1c1e500f4842540020500c1421010305030b4480d074944210203105c040151704001e04024101c83c14241c49040e00d07541071041c0203180c4503005003078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 715847338 1250 715846088 715846091
    0x109060309051c0c0506040b060a0b030103050c19080f03090a050d0b0106080406020d0c0c0b330402130608041a0c07080c070305160305060603030f251b06020f01 71
    0x30400418800705420091401002400e5483d03122450101c9030302c00c8900001d4054000c003070521040141043c0e8440c002d904c110703514580d1035107400c040c05803480f080c07000401c42d901c643c00d81c220f035040084410440802c420450050706940709105170803e04c0300c03003800305103030800902d403204e524007184807401811090318486500382c0581d4400b03903409018001c507800e000080000800300302d036a804981080e0220401403110101a02000c0e00c03001c95036408031840703441c0c0000100e1003c40503614441d040d15801c06120080410200d01c0101031b140340c1190742040d000c0240024021211801d24020241a528440e0710324050400e0720300b0540e1302d05918002c5ea050418803a111a040d41981d0000d13800420f13030350342d881240c034006242c9981c2da0302c010486c1c0196103d0f98103905c602e040160403280554140c03496552511300305030703c83c031038444008500f00003445024420000307081e600003103103004038135900da141081e02d50074840900c08415140b0061003a00900504d41e050102c8048003210f10300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 715848588 1250 715847338 715847351
    0x90504020d1b061d31090b04030206061e0609011101020c030a0f080105030703060f021e03090c03010605030d110f0f010b040b09132d120e0907020d030506040b061801090603 76
    0x552034905d0201640007142c050420300c2d0441215042460700d121000740308015013040c46c1b03800306414070112000e8002d0f009900016000d410089010071020701c0e128503800402500c0800c000841d000041400e04000000220340c401017000d20007080180c00c004010b40e255400c141000b0b20080519100c90100a44e1000420064800207100001c1e6680004041105002420018024040c0046407414891820b10880c8014000380003075024a00ca941507440c064411000d043c00d840032480389541540c000a02d140c101441440d02580c141ca0130000e80710200c1403010014a4000e40000c5800340342d548500c59506031034148288815603800780e42031642854030198030522500540380c09002c009044003d45a030031031545214a1048450038031410626090420900d00060325008101003034486006010b50300d410940b070780c41000c042e40102810500c00c00100c01400f8050310664000c2c0d161a20b01c01550380700005001c52180b410032000c102c0400d00c00040460b1141d9002000349403800300c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 715849838 1250 715848588 715848647
    0x6090b16050c03040e0a18030c02010e030c221409060915010b0304170c01021c0c0903080f07032d0917070b0c0a02091303021b01050301090504020d1b06 67
    0x1c1613a0803103600820505484c0d4850030309a01070041031070b810007181e1442c0c81036010142c010088410b43e5000b0b03a6402c071001d449038241560350803030003000c640c0f00e0010b22030411a0381040885503000c5880500100e026081c44039450742c03241c000d440c000d00320741010302000140c0c003040040246043c9101e0034146254541424282e0703a01c00680064080d001c010300394041d01110a00b00c80305018407400855071840110302c14503d00c40c0112240c0345e040c0c10448500e0f400380c8030300b07000c2060700c2d040b01c50240303001c242d00844e444550082d107085092106c2480e110000880c2c01070b01d0074804601e17514070b20103010a2200180648610f4000710041c00c07003c0b8a03c0140b080004565040c0e1388045031481d62036010350111071610240200081d40a448002009200c80140510030242c511940858401031000e049004000bc01c6100b901d0005034103000400400400307030040c80d0043e0014101e561a08103a0312405041143d038100e0b803100e501080000c0040a91000b820a0b1142002810405418550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 715851088 1250 715849838 715849843
    0x1060203120a2d1b0906170402090105120a02060406030c122c1e07060207080d080415090215031b03100905180d020607140c0604030305090a06090b16050c 68
    0x10200d400090342e0880c3d640601d502c43c3c2e4412403030741e030032800c51080c1014041001080f40c0c3ca940a0100028520918212000e02101400380602d500500104080e0700348014080c201807030303254003c0305200d01c884120260315804010708c0580b42e241c0d07011036454010b0002608070b0794001400b10380b071480c000c2ea170b0450300a2201603040e02c3c5082181a036007040301c0380490786854641d804040c80b80d00300300400c44102030f0008900d0308030f950070340a0310451543d030108175880b014081492004101040c00180c0000c4442c07541d030210302506e40e00000c42217030a401081c00d40051000349600d4500000520034442640314014070302c03180c0303407500500c0d51801182040b0001d426208002d4079940741c3c000311303100500010221006034100c1040f10450001c0c05002551281c0039109500400e000505949000381c0000444002c81c0c01c4c000244565115a503045008000043c0b2002040c010721940c400002c0c0a0300904606500410700100c0a041110703e0340000d255400e51001401010481d90700c2400d0007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 715852338 1250 715851088 715851131
    0xc1501080a0c090c0908010e060907150905040c030e03121f0308120601030612060207060506010507020d0212030d0f090b010801090c090e0726010c020c0f0409140601060203120a 78
    0xc0344004213080e415a002a10a580c2c16000040e42d54280309002da248100052414400c041104c2140c05850341ca070032405940070b000c0121301c00690114428001402e16800c8500d8258940c031780010190b0615032482c0c06c40d0094260032200400000500c0200ba0803154024400040700007041c0d40c8601d543d0b140720f5030b449a2084280000038003400118161b00a610620040c01da002c22040b01034410300c0c180c1e0096100f40001c85200d07203070074041000b6520034002d541c02c6682c041c0800424189075003c100300102400b010543d98402080340341c1c0e4070342e40ca008080c000410380c00c01045914107031510103c41c0c0c0c8140c100d00c0c02030f850a00c60358049011b000c000c804a924103e00062940d98440076136082444603009282c91803401507031104581e01404d0517104030541c500003040060540304c005c80c0c4808003283c3c1c0365071000406080c0f601b20724103030f88152841e510400c9000d02030492010340e14140345090b8004805a000810b4400001c0211104640c1c03225844108000e001440520580400324 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 715853588 1250 715852338 715852349
    0x110705010309140d05030901050a09030e0105070c1e030b0903070b040b0a2405010e0f010f0e0d0c06050309190506070509060c07141206091c0909020c1501080a0c 71
    0x11600904010f12030840d03445400c60044100b601d940e5002900e01400c203500603101203409600c2e003800240b0096103440b410840c1549552400d000080c61001141c0d1900310700000e07180c01c41e2081c000a11442c01c0c80301c04010410751440c01c501145541000520b1b040014150301454008200703010020b6010507140d42d12982c019405502c5840e1103806000810070300c8403880004006030301d0000300b40d2821003000d0403201c0c241d0700d800358810b882c1e00b40200751386c580740c460b40400d00b91102c2600582c00390341d04504965021702100c02150b680c2d180c40d484034442c3da0180c0c1c04620000180302c8402410712002d081c401b0118254042d00106981d450795458000744500c0802c0303030119046543c4da442c03d08803031902e45040c0494022540f00c003180e04d01d50302c0c58404203202e4046004107504201001c1542032060712284003510708400100c04c200800d00400a900c001c2140c01d80010400b44024805012003100d0040180540d801c021141d99400c9070603042030f0b199500904840000a0260055500b510b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 715854838 1250 715853588 715853591
    0x1b180b09130905030712050403121b060507020a1e05120a0f0503061804060b1002190b0c040e10060e0f030c040917040303360314100612030f1107050103 67
    0x109083c4207095000ea03660040c94032a50051003601030f5440b40180003076a0081c000041c4107410607100799800d40f1894090550481c2c030001c00d501140c0160b02440d8009150b005952240000e65501c0380c00046030f0841070707442d245040000e802c4c800100b0500b02d010b40d9011419141c0011107401030075007a1802054402c00100100040c2c080e204c00607144500c01100020041030300f064074148000e482c007860342c03602849000c0c0508050303510000e5008400d40300c0c042601d8001d07007103840708003100c00000c1441d0b4500c0010030001480c6852130014a110f0002c8540c9c1952990920034014a20740041041511414100c1e0352008640e1300412a6120b000382124006048516490f04800e0519840c4010030030120104000007410b802140500c1d12184590310b0780400082440306401d0303001c005880030880c1e0407031401400081d8240c400001c8240880c012140230390540c40303001046d00e400d0707004400c0d4402c012103880c0c1016040001196003022034204484058129055195507551602c44c503410503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 715856088 1250 715854838 715854851
    0x3030412030e0d0f03030e070b0d0b0d0209130c08060408190c06061e091103040f17030112140f0303060f0607021005130b041d0702011b180b0913 64
    0x501802c8180540c00010b4000c28104099003429180741a07826030903008a41400b03040d03e680100464800305032078546c0151400c26188000e410020603411030110742010580c80c007400942e644e100d100340b094580581d040d582035054948110300ca491a40301040651280d0240000590f142042d905110300400e50560601d0b03201e00101c0d019480a440a420145404000f0070720814000c8900c50000c4e440e408002016900c86a8000703e07a039500248248140c240302040002c0e90034000070500e6402505415404400384140300c0b90f0754000e900c002c240c2250040c106040107516170651000c807080d030026100b444e0080c00c0a5480e4400240190b1044031840e4011002d5030b0740c0c0007a901030b207030050043c12000c0c4501001901031742c06603d074000321007403410000900c08084011075091b6145150b1004103011480c0d081c040c84140504084195500d400603068134072104070400c01c42c03a0803996081c003140401c100310400000f494112300100c250400211a25031500d030417131406002c4100700090750 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 715857338 1250 715856088 715856093
    0xa0c0f21032a0c15090311040c200304050405070f09051215150f0307031203151206060e0603010606020601120305120a020c1b0d030e04020f0a020102030910050603030412 75
    0x6080032260b14840703000d80c0032000c0c0038040408405000d98903000510001c00c40d01c80b4083e01c03240c08074070004141403042c000f41c10385418107400080c13040d030032030030012111000c1c03186840710302c101c0903003051890340080340c204000e141c00e000b0183c00500c0c5091643c0c50310003802c4000c0c04d88981d406039500806421040818400c0108504891100703581001403441c1080c01030011203604000420744500f4501061800502d80826000203d031750007144e50040460301c29042d005811120030345201d200a98170001440200c1400941145104100018010341000001d00b801d010207400070b4085d03031404006229070f40d0001344190644040507103400e13100c6030614080315640f280502d030065070000702c401d01c4030316003a98018003000d04046d015150204148040703000340003284494035900000f952007040100780030380300040391a003006c1c0000d031801c4500c003842ca50960000901c0700040c0c0d40002001b401c4501440b41c8a40800010b8091107581410b00000e640c07401180142d0142540d5030300c41c1c008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 715858588 1250 715857338 715857377
    0x50c1e0412030207050405061f0e01090506040b07020a0b1e090301020702061204030f0203070c090c02010f2315060f0307022b110c0108160309050a0c0f2103 69
    0x40540141d0400d0700119031400a498100c3d92007064003c5041901141b0130307141150481c00709400d10600140954880942140c078a1801e01000d4180000841c0118854803000c00a0015069042100c0d40e20103041c818401510166408089080c80c00e020440040511994802003c101c200c4826111007003280000c1c0288500d101c001d6005030000341c000012184c0ba080d21384034038001d8035210200d8802d0340c0d059840c0d1003640e800400121140c50140401901a4441905c2c10424070000a1500030f0002c190b040724225011480a0001c000c00c050030121003d5840c0d90100071a1171080c0082d9452000c990640120000032000f4180400025010f503c00c1000c81c204d003603140c542000510078005004203606414048100142c500c090a00300c00b200051104916041a910201c1c3e81d5030b440700d01a401045001d61404141e00c410034000440e104004603e2540c0c09148004541864040701c981817011643c02141b6000720b0704240c400c03605648800c40400c03034060400903140100010442c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 715859838 1250 715858588 715858597
    0x150306050105090d050c28150905220c0e0f0d082a1b01030b0306060121110c070518040503030604021605030c100507020c09040611041809050d03050c1e 67
    0x40d04517015109600c410031f02d030124000d880020040f0900d481da03c60700d03401d5544a1b4105802e0106071502e000304014240012459000050440300d40c0680710401c1c0300105440201d45400c000400805400e88540340140da08d40489808130350040005100e0340c3c40601d04c2c0660701d42402c02070b001d6441c0700c118900b03030302103160346031900001e4602e401c00080740c2e00c0003150f0a4060304d000a02d088051007090034005003242c01440140c5031404081524035844604408030000204030540b130701c1030043c00c1c203a40405485400f00c24005000b8a43c10320f414005c840c0c10481ea1041321445000c14440850004001c46c1d80000b020780380540e40301d05804440c0404c4070642002000e6110000e4888a14800454684018002e0001c180001c2d160402c040740d54880007040190310001c03440c04140080c155a0007110b0004014503014113186d680d2088204c03482c00c00c40300115541d12450804100302081c08085035820705410200500c0c00c013040004030502400300f40b03030800302c411b80c01130001c62925420389 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 715861088 1250 715859838 715859863
    0x3120c02030705070801052d040b0603100f05041208100b03130c06051803070b0406030f0b0a0807060f031808091203040b0702091e13031710150306050105090d05 71
    0x1568000d6942c805c00b03008040c22500021041e022100789514901812a540035140c000340c140303040d90b2266100c03820103940144c115540b5124046081c001510b803805002c00c5030f54041400203c41c50a8203210320055110820101088107410030020200c2d54880c2e030105540c107250420f0385998508407240e00400352510041c150b900040c00011b800c0350700c0710041c45e005001c0c1c1c030800e40c801c41c0601810703510840c500998003220790520090001178413a0740429070800c40f00e800401d0035154080400d20b60b406039009480c89800c139140a00c2f03029040b80b0010a54161807030100490713405008502254a00c02000600c0030400164400071545e034803040d51040c3c0c0229003525550303580c5102c0300342198000001240140c5c800c07400507144e41d2502c7c03600c903280f50040103110501c2c1d8514580c5a980e010881d011828402002072240c918180c80241c03a1190324030600d07166078642800103000160688110034010141009002d0016076030000030ba508a0600751844d500c00881d61401078189207074034406 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 715862338 1250 715861088 715861093
    0x317040305101d0703050318010302071a010501020d1d12012c0c011b030521090c042406081b03040606060e060f0403080f04170d090602070303120c02030705 69
    0x8211580709182d1094082500046184182000080f0300b10384688041c40058620b070000d100b03041c2000305000b01c1c0c0b0904101494010301d013620540c0c4440d01c01c00e1a0800700c2c0f94040d510014840c07541c042000b00340c040c003107081c1008441c404d0446100c244113100c16160040100001c00c50140c4130940100880c0038150b080321888010f2040f400c10b81041c80c1c458410349201c1e5040c12100c95000f46154078071120f10b00540c030341c2c2c0800c1fa04d003075415510101420f407240340b02e030440c0d034109005c02c06030f64051400c0c0b1000e044608035070010482960100c070070100805259441c0346c800c4210211660003127962604201003c2c0d5104c48564802e10070103000c2c0d6250400000400041080c554004c105840700390f150310052b18640b400303100c8a03028189880d901400e003013206201103040c58000c0e1200b07112201e00140f6060311a299403441555044070080c5035801018010100c5420140c204040c101d907100400155155886c000c100fa035000c00c0c17130050789a072140d4220300c0e68424030407545200e81103001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 715863588 1250 715862338 715862353
    0x3080711040507030e071d0f0c0702060d060513051302010c2d1a01050312280302093f07270609050402010e0108070315080d081b03010317040305 64
    0x10140103860b1201e20a5454003811002191f40a6038040c0b2040f444600b0b0b060b41800e42d14250303074684029014040a0b5210b8040c0031100c0182c1d6504000d0182c41d07544000490a949804240901d03040c2460080c40d1345424241049044206400e518a2003502464605820103150600384420b28200340240706041804055000f4050a00b141d107504da0311410000c40c40744c1010141201050007030003102e074560003514500c04000c420101901654000e42021007408144040e046059084801c1d00800b0a0300414401928a0070141029190400102d822400f40020360340400518500307204484003000390391f020f1440701d820068240a00300d800041c080800340c80c03019140f01090080752000302c500300000803e20441a01400340030395410f84a101a2038800d00056806000c0107003440d0426990703001503a04840300510300070003000030f0000340091480614004007400c900502e85403e51356200720200450340d42078116411650006122100c00e40a0102d142c581c0c1704070f0340017424a115442 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 715864838 1250 715863588 715863601
    0x601170703230135061017010b01050901111204060203030405190305030c0703110115060f051c020304021309061b0c05120904060f0306020a08100f030807110405 71
    0x244890704518610340120b0849880c1100701d02c000009008440c41a08030032516032488080041002a4450109566040342e000c04585403602504840c114410300c2049801c01c201180f58441191040300328000b07001070f4000301c1c00038100b44181180141044151400c400342c2c20340c148825880301c0010920965520b5583c1c2000755260801d540c01c2d40c041c0500d44a10300c07402161484280d000d070341526642d040d0b0740c03045100d000c01c5d08100403d909000c2101d0360000c0000084c0704102d001c0c1c6c0180d030881070301410304000174903444d25014170b2020b00100300508111a01e10070305074658001c816101607274035a200d2001c01c0718101c00020004029040051040400c64160440d60b845881803007440f484a480c00c00441d00d400d842100074102c2d4000c0e801040b030070390000c0001c101070b080280000c5600c50351401d000c0e200d500395a10030fa0300c240c0c0c0031801401d0b6952103182035400401081d24916640d00380203012603100d2840c0b02c010607042d030003d10f031405c00440345183d001c0650300510030406460000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 715866088 1250 715864838 715864841
    0xc010606140301030f15090b13060c020c030606041505030d0903050c18060f120f07080114010f0e070201060e010816051509150403060207081305030109020112050601170703 76
    0x2409408040380c1e0100342103040001d180305607070480e0b0b017194150454801c1915031500d1840b4418402c880c0b03e440340052400704161442850003008a108030300c94028980c20301104484600403880110740058450420503600043c009800280841e000509030350150244008911a6030080c0c0d054003880d01d10502c80c0382c0041b100c2e001c481c0114103580702d201086c010019100b0425a91010194035134010603000e00309031020812048010700102d08045060103801e00c9d0104034000680d066110b840c040c4451403081c09243e500c5640e2000042142d4145001c02c41d110005001e200c59562042c00003407040c2d4400d400110080c0002d109001c095619001141d4076a02086811768000189041c00140c9081c05252900c0c14a80702d0002c6090580e42c4041000c4041a800c12616442d010321012010a680744014007006100e00121991000b0211071011a40342690086100764075025078580582d800c4072190351a4102c030340c40002e155a4403401030b1152484903011000c03031810b000c10801c129425 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 715867338 1250 715866088 715866101
    0x806180c0a09080705090117011104120606050f010905010507110a3b060607020a08010203070201021b0c090a020f1b07141e12030d0c08010509181b12030c01 69
    0x240e86040c0201c0c3c44100c1c9982d01c588a1081d15000501e90004208410403034103056200794040002040c0c03200400309042c40d98110380c000030128103480d031244040041a20400d0001c05003518602d1080c04208006009201c9500c95903051010009600d400c000b030742940c030514204018400790803a42c8800394441e402c2a00f80400049050f0312244100004001185400640c045480c1c00e40f595a008180203035601b0408089030442210040410030f02421300255100d02c505600047e2200368900b043e144412079840080d0094001600f00f4946485803012258400d54850025031b9544030840020340d42e21171015012a04014a95210b40c0344601099500890300340ba2000d507180550700003088602c0900c125418000c20f1f81681d58525810102640310101a844003a80d00f800d00c03c0350724000361410400000000342c1d0081c010301262820340c4123907030040108005900300480051009030307200700100c088203c1c0c007a165104006035030b8010401c1c010710060b1082e81d899070b01862000340030f840e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 715868588 1250 715867338 715867357
    0x46030509061219050c090d080901051215040b010c0f0b040f02060c07030302100204120b07021f090501110a0f0809070f09020910020a1a04210203180109060e010806180c 74
    0x411000c2007062114205403086e40300001e001c0078940f1030035558924a5400807800a05000c014000341203000b170007424480c4076451468140403034a2a41040204485610800c0c505001c1c6040600f0085104a56800d007000d502030300f4088503840d00c2c1808460b1030b140743d10007540064005171f51312102c01d0100c0c41900f202d1107500bc480400c050040f40c0d5003a80940d000d019540b80c03c10021a0200d95403240058011100307006645008003184011410700a66019940b1803e840d03104820411000f407041d5407014600003c1c90341814032a00c40140865450700c1c0ca141006080303c081001ca40003488000c00901000c0c00240c9000da032084004080e4225175509845000078140c240d080c1400469008007a41d4000c101c90341d00c1c3d02101c4200d800c950003410580e9908900b200790000c01c08040b904910b0120603800454079900701104640b41801d005030f080d410002450400c0054640182103513410140c2420119000c3d0b0391240483c0b420726003521418000e4200308184130100c2c2b0144020803030a003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 715869838 1250 715868588 715868591
    0xd0201050702120a260412170f0402040b030f03160b011a1218030f030412140f0c0a08131e080d140c46030509061219 52
    0xe58600d810390311921100e05a81c144070080101807100c43c440c1172004801818501d10444040b0921400c0c0400034040701d0483e101260004640d8005400804081c084c480203203a2074414606a2014030280c4405031000b401740782c640000744442d6070141b0200ca41000c4241c01c03030382c42d20100c4010350b94020a800d0241c41031003160700007050808030100e0039001480d15151280c600000c1c045c00040006004100c1180030704401c811030400001400104410840081e00236100d0034981813180d0500402030524083c400b07589208280b10f081141036588003c0d8000c20151078000030080c040c141a44c00200070000f0400113104480c00700c103d0088002c0c1d460901c2c0c26000620b60100502c21140303940503d15007680b00d07003601c6a940340b003058980c91140d8007840140c100405101060326046500513100c411921f1400440d02400d078100103048040c0d00140001005100700700c030400c1d1601c032a4000b0702008000101001203131075000c101d40c0c0c1c0c42000441201c092a000b0109000412105151404503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 715871088 1250 715869838 715869841
    0x91306140616031b08030c030f090105150f0103092906010804050307120e090f1602010216260c0f100204141018090501090f020703050409020c01090807050d020105 72
    0x5080c90419a150803481c0d25205100074002e48082e12220034800302180c801071340c3d00340c82000580c4d030005140154841480c0a451b810710281c2540c1c04000182003840c560301d00f13010469281c50040d034202c1e0a65043d50202d0f03000d401e10004801030300c492600500061080501c1144042646815541e007480407021100140c43e0600111a40708042d42c020340142e20a2104401003000520a000004014100050a40355100100b14840c0d4212010b0019203840010000840c400203603e0884540d0b40c0300071850200102c164091030007000c00c3c0644034241c0c0c190180e0717860f2014542d001c240555940002d4488601d61500e41d500c0361751407418081402112a0780b82e03840d05a000340d0341a070b4139089442e10028070b04e20030302049880024a800411134040981082010b0791407440e000342085400c007088035070400050800f60b40740782d00c5005040b403040101d070300403980c0041503605a407a0b0400143e0313101d004040d154050040c619028080e00c500156030420450002403400141d925500240001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 715872338 1250 715871088 715871129
    0x606050a03050715020d0c15021e0904050f10030303020f1b071a070b1306090c06020a020306010b18060d0b0604061d0405160e0303040801060f0305060c030105030d030f02091306 78
    0x449411b4901007000c15001078107880000d44443c002c00416089110050402480c0300b005130960240c4990300403002e100041e0b2002504190040320f501950790003000d88141406032440310410305610002e4200b44e80802d000d01e040b00200d044403449420403003180c8400c5010380320b050321518580b10742445940c0300144022000340c190700350345085400440502d110750b6a60b80700511814522030884404da62894940001608140d04c480a000b444e0b00600030607901b40305242c985035040e04100740205080c04a6203242c1e05400da50400c003031050310043e841e4038075054074001070510000320540c410030104c0c5c08a602540030b46c81d80207500c40d07210304c40407103480740701030104480c000e0342c0740c0c0341c00303070100001844880c041c0f95104c02c0720780003404403841c10f56034403507150844000342c04c1410540c4480c0410002d1040400c4655045103401038924599450000025640d00d070081c3c00906054581a001d00301c42c41c1d690542d001510050b20300c02c014407403165004001c00084c0540ea285000d801d110341e030b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 715873588 1250 715872338 715872343
    0x90213090c09171504050606010906050f160f080f0a080a021314011101140f060109080615130507120609110403080c0703120201022a03160606050a0305071502 70
    0x98032451510b070030710042d08003c154003040da40030040700c005100b81c03011103021002000c0d043d44981d0044010709040c0c18031f00c0004040411503808801040004c2c0442d075055030130807048817542c4034015051061503c5518081306070800b402005440c240020808998494a540c020604402190b403040c44035074811480b1002c0380140e03203544a0341208002c06000040d508045200d0f5548141000180c5043c07100782e050944001a40280c161a0076100740014410b1201c81a038200c003003408c00c040c440c0d080507001030340ca0700000c00300c00c82941e01c440300624540703d010004055044400090110b842d1141c0080c058011403005512014505a80061903141c644a0302800e80c04a8920078076080c5941c45000705504803d060140500038020b0000028207030341110100f80e07119800158130f03407041c02091180d045259804c0c030f03c0c42c005000360604605010048a64920f96001489030116003400d0880041c2555000550821070702d040101c00d001300010203108541121401d424000c0444400300d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 715874838 1250 715873588 715873601
    0x5031509210a080a0b041a03070504060302030d030203130f050d0f090b0a0815121f0903050405040c020a0606080705210c06220b03041a0105061606060503060109021309 74
    0x90000000348a1040e50070f02c92103030303c0d410036070002022520307030b68002c0080c0440c6c2060504421003039006094209506080c02054000e04041390200409895074011076168210310000404042d0b0000c005008541823910800041d50801c2c10641c0784455403414540e00c414403989800413440300d0f81c0c0001028821042001074070400c120301c03801c082541906460024014101083c0035203446d40002950b151501c8050084e00700c0070061100c0025458203100001045c08460704403410400c03a4404650000210b4040359401e8500144600401c00100d0401c1000c05004001d2420068001000940055040c0554108980d40d031100b5414090b151290a0b02810202c0d01c0e030840c00440c81280352010103048000c031a00310040d183c0f20007029090213000b9517000340c10588004000c0c003040c0041481400d05500c1d001a000885505110016403107005504003400704028490651040041c980c2001c001424007030111140d03940c41700002006900010800c0002080000c4005901c0030580102e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 715876088 1250 715874838 715874893
    0x5010f0b010f0c0c05030f01051b070b060f04090605040b07030b013e060f1b120c160c1d06090f04122109020a0801140606070c05031509 60
    0xb800d00c1d0a0880d415075280c101d48500350350500703003200c000599442c24030140f5490004600001a503150400300e84520500818400400520034403011001031002810250031070021103038488a2048640010f011700303074414006045030b00301028802004845a003903030044007507072410320903582410011a07150440003d060720341c02002c900d0f01510320b0300324403000300030360101e80380c4c1d00350500c3c0c1d0503941c50194240e41c00c4840c0800142041150046104540d2a0032030881a09284c0410400703d10907814001d06800805040011580c6201c0003082c1c07446801d69001d0394014620707555030080d2a0800c0f010300d01018003030704040013410900e80000c1451090842d0103a010701e6881c0c544402001008290003030052008042c0807802c0142c944d1b14600c940400f101010991034a07600c1402410705a031340c0800380d240e040c11001c880380180307030200e994810010344141c0d86070328035410200590b0000341c1c059034050180380c0501e001c2140040d00302d4480c0f0841e404595850703404400c1f00d0002c01404064 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 715877338 1250 715876088 715876097
    0x31c111201050904030314011e0608040803061315031a09070617090102070f080316020d1b0f0c0f170304140d0611191d0f0d0804180905010f0b01 64
    0x50100d40b800ca0f0f00d01c0d0b0071a00030324000407201c580c811007102000082c0c10420158103400c030300d103441d0744029261001030301080c41d00d12444c0c00c040c0d84851850002a10680c42560007402030342c42c01d034031580040320030301074807290f60981c03980c034103024283c4642140c107540b884000200180d006000000c642c1c044036250f070340f031118448002c59401e1030782c0c41c040c000850300c0d50200b101c0e20200f8a44e80380451024014412a60340303060200d48a000188a0410141550401c21034501c0d03440c2c201883c0031070f6008402042c0c511020b81c0c82c103200e000000c0710008040c21901000440d60601207200841030315181501e40c005507800f8140d0035071320300a61013051141c1c409104298094105817a02c0d41c2003e218a0f00401d401c002880500c140b50050780350f801340800324240c0c40010661202c0080070480c2e000e0300da00010085280464040b002401506008a038800e00c107004108110782242c0081007015030440000300d400410b50050b16196034181c5196081078118802d104452080c14910f910503140d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 715878588 1250 715877338 715877341
    0xa1712070f0212271219030903020a0e09010b04150611031209011506030b030a021c0b16120b060307080907090501030606090c050901300906150f080601030b18031c1112 74
    0x410030703411b4825011401c0204060b070000040c1c551010000c0070b000002d030440043e290840001e804c441410f03c034180b01c1c2d0b0501018102ea9008010908207448481c0b1703010626812034800031b455445000380c00350b1051040710170013442480660200c101d40511941c080b60381651a2030031800e0303c020420043d8542c0100c000e500041c03800402882d1a03455002032491002642d4607510980c00b41112481d0781c0c1c110411403203ea45602ca800849038503810a0204601c410020104550340402001042885440303400726502c00020070268006204c0c100092025607100c2c80c1000c0030308040c0c400e98400394205451011480c0c000e60543e440c80324103a584d88101c04020b043e220800186070448140050030034020246080070703001d48015035018060126584541030013400840103280d2210001c0e080c171180030b000e800d40c0031030158116508066903150765212400c04250020080902c00395510001809103103004041c00300503800c0340800010010704104005803043c03071140c0c00640d00214803a20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 715879838 1250 715878588 715878613
    0x11401080a0c060302031003050f0a030e03030a0903140f0a0530160c050402040909021305070c2d03080703060b04080705131d0a1712070f02122712 65
    0xa001d941c0c1f11140c02401e0305965900d4407514103011a2948a0131150401c4203604249504480080d41e082c20503802903240c444100001010b8a1031030000502103c0700d1232640c1c41000301040803000303d000c080282d5101108904d001c95075540851203c000310340300420075402e07114002260080b1041e080b80c02c5444c000950002401ca0a4490404c0b1060350111300c0209880c0c83c2c1e88058400382508210002e0703140d0f07071801042002400100000c078900e040208010044d03070701100c08188240d01800d484a00d003001442070805004003800200184d005209070000d059000ca07880e070040b1240c0d1420004251581d41080c03040c800d0703005034056076101c0701d0700308014100004408911045601c00084110300808445014070745281d82c115694811205042404102c01c0030101c6c903c81641c107039240c1090b40c142d814100ca80140701000f440b9034031081d1400c1034001c1c00b0311003031114010900c0341e07a5036201608424611030441c0d06440b0b4448845650303d00d00b031544035a50030800b02001400c4980782d41d0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 715881088 1250 715879838 715879841
    0x81510060c080a0c0606080f010b090618101d0712050c03070f0504050d03090512010603020108310b101403100b0a08030a020a03120504200607080c011401080a0c0603 73
    0x8480360804c18408200340104440c0e01c9404050941480500303400c071281a040f600b90b600b1052101e1040e088042400296510a00e420142024000d00c5140d02c3da40c40e00c00c10407598296100302d660720b00301c082c1c001c440b2042a401c00e201c0c040c10b44a459250081c030040c001181e10486441c0103d003030800c041144613000c0c2c000c0384000755035072034074a14280c2c6601c04583c1e400c41000b0120042800d0b0300040c0180e16003214200000c11000d8020480985140c000038404000900030119046404896020303e100c4904402d000d20407580c0c448480c0740c65031a1400814a048882c00b1040000ca036000c01d147c8429050703a2450f400040042ca00e02d01e90b0804003000340980d112169100d450300c940080c54420a0010786584810ba030080c001c00b80c0e40b030401400c90808902401140b80c0b0f40300401c00050218081d0840c1c103241c01c1c05940c1d00622090120f125849445405040b0040c080780c1000c03581d005401038101c98550100d040b1b0f4a076626034400b56960303018400140fa85890303250034031a030b501c0be = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 715882338 1250 715881088 715881097
    0x70905010b21060f040e030910051c11221a0708030408210f090607090303020d030c0216080c0a0e160309030e130b2e03180c081510060c08 61
    0x10860b5099001401c00201146d070132690402240e00007094412480c03401c180c541400701b42d01c1c1091407400002600196101862600030042c40e5030310490212641100340a8811441c001c0c110307207902d11744540b00b41031242d0517442030340030800203100c07038104c2c0460207020f4484065000a40906603115a41c4040040e000941d4001c21914421030314442c90050380035030b034000c05c016140c102c191b0600134612030a141b4028003040901010210410010303a00041210581d20149000a602410700100702c0c10f0880c64120201141003220002c00e81c0349010074403062107801281e51181240d950410194184030496000410214801090400f41d001e50411444c80b4031a25101503402590400034120005a02d040b61a80c0da48070504145420030503090300035003140b184110702006a284c11040000366140101040588030190055130602c80541e12030b00603400755200c000c458440300c007150342c0c080c0004c0900c103040c003032008605452076030003d0006480c4160b0713500d4a05421901c42180c039611 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 715883588 1250 715882338 715882351
    0x21f05060301020c0d0f0f170420060d4802010b13050a05130503030c0d02040b07060506191503110c100507020c221e060305070905010b21 61
    0x1001c20800d040c0c0c2e2418404149840b17983e032902011403039035031002400b6600c4074044c0814802c0f50240d070300442410f000364030340c080e0344244d901c0c81c5024a04070001d03038420302e075000c560040d0000c02c1490340c401c404d41001070001070000b042d1807072841070600080e1400d562b000c02c440c40c000080c00900c07005002c0104840300401c600000c2292080b580214075411104207a040071240c1e5032040c030a00c01030900682d07410500010b071070304012802e40c84040d12888060701200b4007140c0001d44a5440301203806446c01009824800b58488019040c1400a01002c44c2c8040c841c0b007188118030700800004204200380d0712540c1c41c46d051480503040a400410311544001c507980018800003210180402184850b9403280101144a0818450291410a400c0c550921610301d404400003c1d45e0310301000e00020881c6407000c00d0f2550324040c00c8107908610008030161509144003c000d1204c0000d48070101c408550003000940c0c0c2e6258100030500a0301c1c40507024400da000b0101080041200003904180c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 715884838 1250 715883588 715883591
    0x31506091305030f0703170901050717130b010e07180b0904090c180f0c0c020f090c0702030f030a02062d06040b040906050a0513020a120606180912021f05060301 71
    0xc4d03038518031601d40107040c0440004410300c844180b070341800c0101e03581004501d0002d10042c240104050041c00c61006414100c1758140b000074215500c0312040380e60b80e504012268a256100c86000c40780ca4803c5580c9004910020503550500344894039240c22200320b64603050034407070417204010241151072000c1c0c43c01507000f4408100028864803001404038902000107054484c0503121041d00c3c2004254818803950a00c1c100c090b0300e680d40d1030030381c03403d04480f040020303510017020240034011110040d416104603020300d0084900007000381406401c40d02111003d54442528005c401001031103104039104c0190025010f8820f115900c0c3c00010003800840c040c625200460200c03581c0c1c1d4403c0d18810740707840070721400c48420b10503a90404540c807180a0aa0800d401185180c2828803d940480c111401501e0500425900c1000500707100104408003034240e440315005010307403690503540920084030740c15203140006a00840c0039000c0c0c0d11240d800d0007a51401c03005000040c101078065 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 715886088 1250 715884838 715884847
    0x3110d1806052a010902120102090d080c070b07080a090803130306050907031709190b03280903030b0f10021011040b0f1314150903010e01060305030903150609130503 73
    0x1025180c84542600c05400010481024010030180c24400320349140e55920400840c54151200c80344c3d0103280380c00c1433609603280c5500d07480b94074000196005045103900404c8007410000348200500c0032400580e18010005d80300c02c0015144c3c440c5500c51042c81e400d004007000010310301d40085500c2000d11042d100c2c429940d851386440c82a6049640d800a5000140c881c00f901d81524180800500c1d00007074010705041c0040c804803840058050344070f445c40114a0450000454200000f00c03074103410a11008a840c98054050141c01007440c0c030840500c0c105111504180d03003024010802a8028140307000806c400e0002420f81040300781459108000104801c044040101a0a074041c400195a0390902003020401071b4660808000e420603040703844803940c2c80b0107004440307c80c00c00c00d60b990f4034003140020b40107290440e5035140329400d1400001c107120010000c0d0401e51403d8084d00c400090602d01608a08000c940c41d40d81f10a00c040030411200b003c50b460020b26100c0c0d4101c0303107071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 715887338 1250 715886088 715886137
    0x609020d0b090304060201060906030809010305062e030b01020a1a07230a0e060c28050f070806090d02061306290a0b21060406090903110d180605 64
    0x150110b58880c0c6980c0009002c00c516542441250020000000100031150550340d070050075215014410381056201c60120300700b5a204e800000e145403030241d84a03444c41c1e4800101c07428403019078030a000b191a00d00807a01550010660f00001c40d444070680705c140e01c1800343c2140d07824014003108100006006185840c009644400f1314012031020307640d0b100c01451000038260590702c0c2e0b045002e204140810405c510780020b02c1d641ca4041900d9103d10a461301c02d1000401d6060280909a80700705455440104000f01d00310040c0c8402100761946941e415008076520885020034400503403040b00001c803107070041c0300c042d0394080c030a074000300b032022400f01113240200d42c0400000021146d2101030f94280340000c0424001c2c400b40c16800c0c00c10712102e1601803a407500c0d5001c08202d40300b020001b4503a903202e40c03028026042c0c0400400140c101410b0040c20090f90440d40728952050441c4800300d0342c069035110701c000d40300d900110406810070304111195001a24088aa0400909c40780311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 715888588 1250 715887338 715887353
    0x31b140a050102040911071502090f0d06020307090611070b07020d0f0b160201060e0606030a0b040524120d12150e0901140106050a1103040f0b12150105070609020d 72
    0xc155018000150321141000310000031900f41d0400c140c58100c041100800054030b41f4102c4201021701c840050f10b404e0f601000c5010703041d100600e141d21040c410307560010403016601440c0260b05079500c1014050f2112410f4401081c03082603c1c440d5070010707601700845d251090041c4110362002d40002d00303452640c3d46081b260144114111412002c1e0401c0242e41841035103a070000c0315092000b800300034508009000310a10250509009607030020000300d40401c06e80006141d680090303c200100d01c0e080d5003043c0b051000c00076140e4220700080c8081140d207000111000b1850174040a4620074a890f441a03900202405000d1606078586948814000018054100502034140011100d2030400d800b1421600b1040d01d058828110f08014000c1c680c2c00000d64111801500f02514480400014280385000b50f46c401c80464003456004191302c280400070b1300d01300380c10001020507516034407022804900318030030b014000380e41440050046007050700146201800a400c2c1d020b11011500da00d072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 715889838 1250 715888588 715888603
    0x1030209130203090609031206040903021c09082505010305131a07080f040506060f010504170a110303031909170c1b0102070e04022b20010c031b14 65
    0x350b640801004508042401110750003601c0030081c628100c02002d201025400180031180100e5481b40040708050007000040406109200c801d20303048103541d001440c4020320b000d29881030103034004429424124405400c0c60b40c000d00681c860842c10b0400450040400400c1e1100d554040d030240c2020659052030018064103407071881d0424030780500c0280c80f800018200030440e400c9141088003190001c00c1ca2a00325404803501002d27541c443c0d0048038903000b0b17604108080300701c1203a285070725100002c0c2c85107a144540308003200d45d1181c2003016142d0000b00c4480340180c44180d002c0050003850b0380240711507803068045074840540d4101c01d041c81e801841420225078800b6200712004022185c50b00d05080c000d100600c2d5944c100403480e5903405010700024007034a101c0403403800740c42c03203c2c00750340044a031100d011000b20b815003082040100d02080a88030b40080d0462892a5407007100444511905500c520b0704030780c100442d504500722485019285003196802509100c002440f059 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 715891088 1250 715889838 715889869
    0x6020f1b060f1c1d0c010309170d090b070504031211100203070305060a0801060b071106040509040f0b01090203010b07150b0310090606050301050423160609140f011d01030209 77
    0x301c1d03520755240c0d0b0030401c4408007510300c001305040305201c000301e01c0e00180c001c200303000078a00030030f045d002d83c5800a111058058070542c000d0000c11055003500503a400094028001d48403405a9101d11800b170311144500d0102070450b1403000011402d072030045400140030b0342100c00300d0303071035001c21001078040760000c0d1144800a81ca62040c840c840c40d1a0764994040c0842c0c0c0001c2002d2427404140040e85c2c81190001040351840c0c42c00304070703190b0300c4806440080402410300c807900d1901c1d10b021480f0b020380600840e20b1038140d50000c40c88400a1007502c3c1030ba04d410146a25022035500ca5281d846051032007100c0882d00d800d542d0005440030b00a20207000b0b002903011404a14502d0080c044d115540c000d24082da14003c10080800c107060340d101e144203852886940901d100307502c07a41c10803022503a14084d1200010000898a038440d28100c112040703200b1070203142c401030080002840c496240c4070f0000f4025007080903c01040001d1030740300c4005060040c5410300490218903d1280c1c41c519 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 715892338 1250 715891088 715891117
    0x2100504080a030e133c0501030803040b0a05100e04060906060f0f240e030709051905130308061306050916090f030b0c073906020f1b060f 61
    0x1201c01400e202407140c42c1740503000c00600c0a1140f00c68461850590800030f0040c1c4041100c40a041c5841d601d017071064484010000d200e55130310303810103c1711580203030307400c43d10b00280e00c0001e82c2c201758a200300390140310708003e17540500e442d0002041207504e02400030f0b51034036644da101000081103807045a000707203111b03110001c2070780c0382a000d56038401850344400c12003180c80300318118422910080700310b070b50106c0c200260141000c902103490300040350403540c280f515050610450314802d0b103400040441c0b90200388007542e5903003610070b10381c1403001d0010085051b45012584520707002014404001c2c9980700041c40640c0c8000051004109940c500314054100e441200c20561200940e03000c1c04d9803010300303040c0904d50ba48040180b40c0041100100c203034080751544c2080110a2036031680c015801c100301745005e55920250702c1803c91205068103890040d80007851034004182c21024a0a95014182d81c07440e454040854444d42c215035544207100b00b040356504400023000e4945802c4404030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 715893588 1250 715892338 715892357
    0x2030402011115070f0f050f0d0b0d0602040504060b040509040f03020f070f09061a190e060f0306031516110a23060601030915090f0b0a020703120207020102070302100504080a03 78
    0x2006003518000d46101410841200c2c1b021407047c4d00f05003295109800d030050540c0d20031504159100074005008101c1d4400510000e07a403e10180c2d8001e0001c2c0c86045404111040d07581030b42156511543c8a040d4000308038000140103c0d01141040300454081e006480010025038015410041141c11943c085001643c050014288a100b003501400600359900000001800009024060001c0343c104104080940d804898850790785513014a201600d26034076440450800c001d107410889206010b40300e00c0740c00c42c005882c1c03030044501484580c09141e04014940500f111807200e50740a04503644200301c3e000d40000d00c2140e50601c0f180c104000119846440a22941030600c06020103041509010002c00800c801c40741140c03408400b0040000e079820f1900e0070b2220310001042c09031541514904000162201d500205440d0b03119640d1105d04900b81c05c0180124004d5002c040c0c010780c4881c50500041c213044500749407503005824414102030f56160b0003480c0c058002d00450010364142d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 715894838 1250 715893588 715893601
    0x30c0e131812111203040f17040305060a0c030c0e010f0c02040219020f060a0606202a0f03070f090510030f0f02120633060d05010f2702030402011115 66
    0x600c41e0a004c016516505194513868140480284017a0044109914514040500d641210f00075540300050b1085807500544000040100f601402e011a06201c80410181c3c03080c101542c0100d01619038180310032117001c045480d030070741040490700300c0d03802c220811b940381e00800301441c2a040b584c028280703160381e441c1c1113040080c080c00a80a41e400c2c00824880d40e500304000905000400c07800c03000d00e085041c2c20514294808131585c645020803030f41100301c140440404184000c1c01e50b10350410301507020606940d190707180315811120303a0700c8000b4400b1044c603800140e001125403158400c01c030b450392618100c1e002449001c031a0792804005a004508204100590014400001d4112842c007888100c920032000040381901071410000801c540d400c0c00c00b4210868405803101c1c0e207400f980c40c80b480c01850280100441740391034000000745440d8080001e0001106101d01e000e98008007408840a9000030f0012818030680c484104c039a46010000309181c000031210904c1c3c241800b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 715896088 1250 715894838 715894843
    0x9020403080a091a07150f05090a0302160e060d02041b08100905042027090708030405030d1b0b04050109020f03012304020d060203070807030c0e13181211 68
    0xa5118200508040300c462074140c0b02e184c140c0d402c1a80041d0364926018900d100c0c40c0041441641d04c141c55443e00c8144841070400107206804c641c8242c00721070b1001b504400b008181c4491303114882e40804c4aa000410b42d00342981201541d903c00341c00400c207401840e0b0344003810840803400c1000564100c08205044003002e03400d10041c40d01d002e08001509140d2502e24004680c2000c03c404040455a03c0c544c0b91640e01c0d600022107000d000c2c0144500683d44800c03402031084e076060500e440f800d4408600c02201004030740803110020014140084590400e550b584d660b0a92031a52982e1304c01d0341c00214081240f82441140329000000718101c0300e20400c40510b4020309141c1c0240c0c9040254510f841038400410798040220020003019540c82c40010390084e5000001400302d070021003802182508191000d0007441562014010003182d00c100b03c504d00d400440c0e0503408803002d0417660040805502003551401110f0384510390110710344030300b0740b400c2110412500103895045e60030910f43e800e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 715897338 1250 715896088 715896107
    0x717070b0a120b100c060914191a010503031b01020408010c03020a0809070f12060b0d06050103020a0806250c02030d21021c271109090f060a0506040609020403080a 72
    0x44035003108183c5003804c000c10440c082180200200d50f80c020794014080310250304805401c0f000110380114115840c00352082c000071100300d0318001c0181410207c0c3d070812400c107050320700290040d41015003050302e5405052124a914480703540c05c01022810300d0081c000c110706030b8507a4801590f11144180700500342c1800030608503082d0041c20b400d020b501500980c0004071003038207004207038200d401d003000c4001349642030f2415400039410780c0d03000402000750040e504076030080b1810a940c0e41e40f000c2d4541c40f04002c45c3c0c203042c918510821011141d0043d903406000c03007500e1400050601955011070700d030803c403081030702c00b045480c02900201e220103481e628201c1001c0c40d0942c100401201165582020319411108a98450b41c00d41a405604003508040d2941c9580c0010030800310f060020b02e40c070110241500511101d4000b0f00c11000002d051508410b45100030702481e500c00d140d4000a020140c00150b015454850001c2c580003135001800c003550040d0346003540d4441c0c03a030020346820030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 715898588 1250 715897338 715897361
    0xc0f030301052e110c1c05010c140304021c15140603120712030b1801080c0409200102120a08090c190303050703030902040c0e030f0304080717070b0a12 67
    0x1440c208000000ca807014540212001c5402c0c4560080c8840c9107190814010805c856001004540d1003c3c90413001a05854403502170b030000c00100d03040360307022100c101a40140e44002c0c60104045401070801c2e518006030324900085502000040d0381c1c0341540300b0703001404182a640ca500c1c08006151480d03901940240003100140340c9400101c1c0c0c0c113615802024405080209180841d9070b080d8001e41003000100c40c000d003072111562856140024115080c020007a1038464444401e6260600744141030003203230449400f1403956008502086031a00158419045005d82158400e040c0c1c0100003910490010703485a02e5a450a2800546081076002c881e500c02c140440e5042c1c5a164154003a03410b4035010b1400035a203404609054024044c40540290020b24204a0284055010b411200622000c406880050750345000c101e5580c00385000d02d103466045050300f040003a03034400040c2415a42c0e40c2c01e5525869448941d031419420400440e008a49407041c214040489803282081214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715899838 1250 715898588 715898629
    0x40509010b22060f0518122116021c0b07020307030216060c080d0e100b090709030b1501110a060605120a0c0b030423031e0f03060409080c0f03030105 66
    0x51802070001d19810304c1d01c0c1a40b05004000a89140500d0440041399000c100640a1040d2180105e81280d03a514090229042025108000804103801c0740840d103403220807003009000010a0b4080129911101502145091310a0621000110040300c254801c0001c0c0e00516100c14890801a04107407000f00301c00c40002d0010800c1c0b0660b500302009240d05034001c01c84648030145188010000c0404a601e20305502c00d85518009024440d000140300400960781c02c401602e91100c1a9480844d5000c018031000c1420002402074003d00900c00340c280301450310f0301e018400040c285082c281e07100000d503000c9440328000e1203241492143c0c603a00b010040010900001e035900c83c001c1040c11406074031a480700c00004181807081034a0103084c00306d201281070703c4200b40300004943c1ca501c2403010b8203200000010100045c04810203680d509005090628a15030b250010030005040030300040303420b000144841480304404010890740010740d03200a5950307504080400074031210030600704044a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715901088 1250 715899838 715899907
    0xc022b060e210c0c09092512063804050a02090a090e060f040305040e1005100207060801120b01290403050303071704120f03061512060611030a05090303040509010b 72
    0x816000550013020400702c030390703030f000c00706030411f02001840161b10002e00d03504950000f0061102d25409100d185100381c9008043d41c006c4070125120150f0f094940d111a0409003a400d030504184d041650f210704542c40c01440c0c03a488800082c3e000696412551306265201300b0301c440b80400f00300300c076000082c0e1a8001341c2d13440d1607a40204a1301c6a80141c1c4000140340010856001c40d8140e074202804001744054001c0000403002941c0300014428400010b91410000440d02d07070300ca1103c045107812010041c410703800c10311000c3c0c1c9c0703051260f508100b40040c40b0b00603104890807800340000e1072080c40990707502c0c00c0170036004000350f003550007568494052905000c00109102c1d0303a0074803900207003401c2c54000003c041c20740c000c025036070010b8003a00912190090017944840805108070a500041080c140c0381c03002103d070b650320403142c030f00c00e0350040003282603060044005d000c50a00042c1240c2c642510f58001c942c0e034540c00c1e44a110406800b082e2198078410804c00c0b11203410700000b640303000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715902338 1250 715901088 715901101
    0x2109010203010b04140409080c06100b090307091109060c0f0105070302120f060f0405011203080c0f03130c05031609140c0405040f090b070c022b060e210c0c09 70
    0x254442c070f00c901c07a0f04c0d081d076954a4105488542001c40e503c0c0c1c104480a403627400341400303c2e0b11030700708458884048034410004180710f541c080c02d80e0044400138005080540c05c140c4100010010004804c0b4201000e0052480d20340c0c44400425411301d07018041d0140e20200b0302080e094400c09070101090500621407414064440e2545279407009521040b030300280c907850049041c11181080860700541004004928491101c181a0030f10384a50f58680403556000040340250040d10f903111800703401000400c04030003600241c3e0141c0c070f00403031b0300207032041d500d00000780340134003007104841d0780c07002c00f00c0801c02108180b2803007061443d148a19840f0b8980861000c60341c0c0700c2d070301031b180c0325035503c81d84c91000e0320403584880c000503400b6a21901c58101801d0160900d0000c9070b00701c0c8141020320015050a00d96140c082d55405210a4540240a603680f0341e00640100510081503100d01000702e42c00301102844450000d01d040619591071541d08810707400c000070b040b9003600581c600d40c207000030b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715903588 1250 715902338 715902359
    0x615150912150b0d061416020604020a0302040b19150e03010c020703060c0c050a0b1f150c06020c030d050916050612090115180c03111c06050402210901020301 70
    0x358400400b10026900881c40700050300d101c0c2c56040549410f207000c12045a4240041d5141c2c06088800000c40503040c0b00e0ba01203030780d0704007120000d4102c0c100080c200018101a002286a240700400368604049440142100c0115a40c080184040d4a0000188942c1c002c1e5144ca03259000744e000307101700e48011038065038403c00c92000419540d030794100e81e10b10520518401c40220752010030f0342c103000c5040c100384400190950b81c4c4428148804583d0800755581c03034100e02154040760072400b1041c1440c40c1a101e500b00c4000c1503603183d80030081207050810600050000381601d507800035113801d02e034840fa4a0034181001054140e642d41c4810301c40b81e41c5103c2929103000b4440e501c5115661610121800340040012100e440d103803544020170212442444003902c244000c204003c1c8c428098000c50940744541c8264038402810012020884508403100007022900c490108021b59141c0115080360301c600d0b804030b07880180340300c00c1c95061100e440c40303078001d841c1900079030455040c00d29004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715904838 1250 715903588 715903613
    0x60b030609040311190c08010c050c0604081809090109030801080102131e0909030504031103120403020603071701120303060f0509060d0f05060c07050c1e0d0615150912 74
    0x8091068822003030030540300400c00441701c0451440164440c40c40c920701640600301a0103964107950808620903c814130400603030b840c0f0706001d0014000c43d111903e641c0d10742d50104521103041113503506a00c10b2915600c071000e000b00d014400000e07007035181c1d00b4000d00a4906802070400f076401080410006160403c40c417041d6603500c1000000503520701c0780300080060a6000400306410316424100b45034001020b0021a40681c14042c5000c00c16030400d910341c99100e4000605c21802e100a00c00350400070051507200d406408c1250b5050341d5011032001d002c000347d0102004a10300c1c2014001c05078180103803c001e00e0600101d20350740e4141000141040c034001c04140c0104d50664002040c48a26184541030542010a0712130b14205000d91075030720b07404207078284c030544920380310f55846041108840c0f10030154204d101c05060040e004100400d9681001035a82c0c1382c03114215a08943c500d030b40100200f00c0b180581400300c0b24030fa00a07201032005d510908080856540050114038003a81d4107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715906088 1250 715904838 715904843
    0x303091009120501051605070503070b07171006031409060105221a0a05012609010e06090a020f010c0f02061309021309050a09440a03060b03060904 65
    0x2589034800d04400329040301e41c0d68490102400c040b000d40042c803034107500c2030740111105508840078480706901030b116845140c00040c91540200440008a0010606960090070360f14004060b00707044000303141c0180d000d540614010a051000b082078030f4262051907032054081c03003160654134011640340c0c3c585c541481181e01456030307911102e030f00303041c05124034540714035461040108034050070a1151240c01220058028200d5a50110300da60241400519680801045026003022004d55888000c8090010b084540d2205030541920009014451090403450300804e00c2c078050340100450b580c000c522017818860104108804160303220090007041e901918880d6841310390394510f49407490240d01c00320310b481c404a40d1101542d07070500c10400700c4c0c1d400c0c5018441500d80301d1a0808403494040d006081001c80341080002090032181c08508518405003070840c001e01c0d884041c00010004544155038400240c4284a50707054442c0030084c00503109003900758034000000c21000d10740503002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715907338 1250 715906088 715906099
    0x10e1c06020309030c070807080c0105072003030c07061d0a0f03060e0304030209090c030601060e0a06030f0e010507180603060513020d150602010e070b0f070f0c0506300402030309 79
    0x551075001082100e24040c100d0301191b01d242e5541040382d0b1a242a401204018056410001c07199071091066841c2950482452006d08503501c0c0f02e50a80040c111425030140418440403155080902403000100800d444001e001d03c0c07581240c40b40640c100301014812094180240840341e514041001503a03480200080c0035544901c090380b0710300a0350300c001e41c41f02400d010000c0e100d40201e009641c0000a030115882640c07070301c0003600c086003aa14140e0b040b030b080010030051301e8801d4111440002c070001e40010b01401c1c41c0c04060039650100e03203050201c0d0100c13003c0c03901c00b81d0088542d0b008240614080110508100c005881d00e00805e02c00d15a20303801207041c0b1100300c034ce944580c4d03203c0c0d180703600c2c5142c81c0d075240c10203400303020044401900b034014104c000520800c0c1a0849412040c644669841c0189035550a000c1c1032508405641e02c9003120000709003030321024014000f00c0d1022602441144007a0074000109611004070501d2000307120074040180c400006076031032003408490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715908588 1250 715907338 715907341
    0x20604031808060403030608010e0a170906040b04060203070c090b090c09060c0703061e0509070605030702070801020f040e071d060a0201200a09050a0312081305010911010e1c060203 80
    0x7000c00079407458002d5400d60090006200030560958085003c55130700c880280604103400c80510303140c8402c0707400908103004008003000728520344070080c4030b10007005055034102500c58a08030703943c0d00140c112030090b0b400080c002c41440382c900400c00080210800070322a00e4200303800311340b90650142040c800001d0108840078562360b03200a0700d0354907d05170216000c0715507034181903005c1c0c1f4540350050400c00303e04401e07000d41c00140c01220310070103182008004003407810700116140c3d840100020210700a812012030000d600380020116250250b07151511a420510325400c0c1c024090020024001c0f1005c02c00c160b41040c01d035902e0200c4045501c69251110104280c1c094801001e9200182c1220307044401c00b10410000b801c841403450380d9003c9415100d80600c04010300390b0201401c040c80910030042c0e41403066110680c0300007010000180f075880b035070319213094404410088400c0350b00020901e0700c6580c40700d920084107404640710203505281800c00c088540554601030315580c0c0000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715909838 1250 715908588 715908617
    0x270302071802070f050d03061401020705190f12021005280908030f0301150908030319140403080a0c0207051c08090a080601060306061d0d1a2e0602060403 68
    0x24103949403d600600084501000340c68842e8a880c420b0600c240468600400822035244554900e40f00100c10b270003d000c4141884100714862501040d620135030004508081651000b88001d04d004058600c2d40c1c2e00c03282c0e030903c10000b614280c02071030010010148101c615a404001304440104d038000c0d0188584081c0390340448031500da5411800c0d03d44000203180c410038510200440c102c8090b0481101a501001c2c01250400344a03c0340c1412684184040f0f402c04010090084210518040004001e000204480c200510843e02940454161010881c6c000781d2401000c240700034520103060100d003020005803070f03134403220840741d910a07403041c0c0c250405c40208101c40001800a01c0000300316650344e0340b540c1e035100c24010a00000d0510800192441c0552801111803074640d44180000c1821424804050011001134503d441c5051051561420f945503c0380110b0b01c010400c0100341043e000140d481144000c4440c60310303c0c0740401c200c110b50202d083d54000fa45446c140c00314400383c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715911088 1250 715909838 715909841
    0x20f090d151a010f0f032a0e03010605150309030c0d030915050415021c05010f0618050612090a02090c030a0b03030708040608090f01020a03050f010905040c092c012703020718 77
    0x80400c5441007c2c034009010340718201c0749450000d156611181064070300c0040c1400c0c2c030824465550030a290140740030700c0c090542c000c2d5600007610401c9a040402a01c5440d250640048d13410006c60b43c0c6151600922101290b19500443c1c4004d00317202c2403c0640e01c00c80422041a00d100302242c2c00b10310f28605140d41b04c100040c1c0542c94000380310325611001d0310600848607205003004200010f40c1c1410031615100030504480c4003c3c9418149081d000300a10300c80c0c8002d22065503401a800081c0069460345212303809001e11540b4541c4a2030811801012a0060401948698420710400c0005010b08007240c098448910307000542d5280d40200030302c3c0c5603810848955550001c5403602803107030f0507400540704001c4c003030b8420600e91766041c803942191b0041d603014102940500c420f00004000d90443c0040303460707081d09981104096044654524248807000105944407215450700030440c0381c09031021b1036204501c1102507030668001e9614859480362880500d10a0b0310400000c0c041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715912338 1250 715911088 715911101
    0x70509090d0201050108060702030a0c0201030b031f05090a080d09060e0609030a031506050a031a1e0a1509150203120c030f0106020102130603020f090d151a010f0f03 73
    0x6040005941042403286484881044220005610707220000421510010303d040c02102250055403900c0300100c0308490300402d914003039041c507489814000050301e007000191303d5407015a8241804400003d11103056030800381139038032164450201c3d240401d11440840d6000c044aa90000e4203202910300325001e02000480c0c0802c3c0e00a04041212000f00800180400c03c4c0e40e80d02008401203443c64880c40403194080e04002400c240141d01d440c41c02a4440151010751018010005421800041d0820207111288070540b041801800480c1030050b0107001500754071604400b144003844c1c0003403070902070b4030550b8444400b5001e0700010500a00443d0b06400b80f119440445291944102c0040e038016510b200015035000c000081a510602c03d9429030016401b100101c286001411000b0350484400c104401030304003d454060395424186c0705100d80315203441014041500d500d04101d44442c3e10200c0c201c250034903038045580c1d0000120318000c2503820303c0780080005000441c000c0a9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715913588 1250 715912338 715912349
    0x30a03150812180a0605030609090708010c0e03072c040303060305030307050306190e1504020d092618060c0c0415050f031c0c03050d1811100c030f0207 67
    0x2240110320350030540740010101c003c01060006155100707034060158900b5240301e008001501400491110300d82410440d4000e000081101c000e1038599504c00e0840c4c5280b06a0400304066513102c042a0400340040310081101707906003607035212044842d66801040340e820a00100070240010105402075220101440e000802c42c1d1712490300710000340030350344103803110341c4036104013101440c5984000c04c0000075504c20044141380c1e074541c00c1d03131a001300359a1007466500c55000c0c0b100e400b00951030303c20103800c10300541000c2c85407120601d4811915500c00401301d6040c1e000c2224480e10005c82482c03c400000070760303440c0e513201508150715050460301082203900504004009640c1c8400d00c500d00705480d030840c1e10207000c02c11682010b83d907400351041c4051440e00c01a481c04018011060502c0711402418001c0c80e0030b41002d4080b086454040c41005602100000c030740612490500e001c0103442c055600c203c1400f85600080c14203902000010208540a01d405841328400d200000040c035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715914838 1250 715913588 715913593
    0x906180b07050f0a0c030b060904050c0f040b12060103030e09220804180509120c0715020316031106150117060423060f04140c090a0b0c1b010207050102030a031508 72
    0x42c45140503c50001581b0061341d814020348080b598070b00c1c0862406000d103500100030902c0c4031482c801c4c0100383c0742a10f2f4040d806565a00035130500c3e112584001c0da015217541c0078100c0356046180161400c050078101ca4001e086d144100304e00011810505404461003203902d0124400743d2910031210703c01da0b08520107400e0390100d905403d88098002c10b0003008500103480d40505840081030113400344850a083c15401220204220442080248410050352042d6481e04680ea1500c0701e04275070810341240000d100506041442c8400c0c4441a0446520f11040c000401c1d0140001c000110030700420540780e01000c0892240c0c2c0c0c075584045001c4052014840360095901e00f0149045070894040c1e000c0c1411101d4900305241c9440f504030b1006080c41043c0f525107030f00702204429040361603038507001b02c0641004148981000c0140003031034445002840c0d4003a40d8800c000c1c2c210400800141175510620781402680e80110030303a800591980b0300090201004031400e86100c003e0f40c000291030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715916088 1250 715914838 715914853
    0x3041106041d07030234051507110c0603010608153a170304050f03070c05030c1206181905151305100504060902041b0906180b07050f 59
    0x400003100b4140008001e6851082190340300304080e0141e21500800020080110b520b10f003007100380b0003142c2904481d044203200c60b0341d85982d401e49401300f40d45c50b0440c2101d444007000102c541c005403900c24020fa00d0080c142029010000c10b816000c18091031043c80410400190154050f002e1141c1030356000305050706814100005038134810418660002022280c0c0342d10300b17641043d01c0c1344480340f94800800001c0c01ca441c07900d88220f030400b6001301c404e800340300c0c541c494001c000c00182c5a07140c0218401c1c2903081c500010185804143c41030503000e40700140041c6003000c40455400d030700190004444015404019420381048007554002d03401d1100088401c00740180050720b1301e01c50150300307081d085d16210550940e903003512030f6000500d10350141550f0061896290420ba0f0440e102d000301040f0091039600160565040c0c1c2c0400d141c1c01c11000d103080c000c540c850b0544000b0407582c2010411a0b10054642607001120300841e241c040f40004c0c20307010018100300c89045144030f41c003540d090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715917338 1250 715916088 715916099
    0xc020f0d0b07050c1e0703110a031b230109090b0307031703070306080f0a0320010c0309050c0103020a14090d1a04020301231902040f06120c0804080a03020304110604 73
    0xe42d0413403d03132001244560010383c00309000365409a82650341c064000c041a91441e500e52445000c0000e9a82d0400c009810001c001881804207900e1801e9201b00719062608181c0402c840f0360070920740c2d00700c820001180b902e0598028505a00b03807200740f14007090003501140031030300d0071580f82d00041c6102c010600300c0c1d071421015806180101a260381c14800d55a90b082226500c10100d820210315030003040b44e8130002402a40b0b034a080303501c5020341d062560007840445084554040713a03200481d4035900b541003001301c14001c01d03800340c9007420210b040034081d007802890004000542c0d9500100098048099a5024040d42c04c1c0d0754801c0200c00004031803c607546200320117503402ca000f9070070700c08a64503105044c503065980b00c01102d1204050782d684a600040c3d0a8021a045142d560030000400d000440b09074010140c0116190410780d4140081403008560b1421400400c00400390300f4800001c00c0d80040382d1040f500c62034056225101c60a040010b0008444010392014002900060b0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715918588 1250 715917338 715917347
    0x1e0305040c0503071a030601030f02120a0c091208250f0c0905160e01090801061401080c030403080f191b0824040e010209090403180b0a0c020f0d0b07 66
    0x108038490707032121400c6036940040c55581d004e14090031403070ba4050610403034511500c4000c3c540c000c10514011800d0000c010740d001c00c0342d21101a15507504440020803181600c2802030840d140e285d442d120304440d1414100860710b10a214004000c0c85c0005000003803c0c10b141804140c1507180c40700300c42440d26900c0c0035040d41d031f00c1d6a0221050f11003918009129099441414810f405651051898508240040303448845460301c0c20b05001034040042810701d8244501805054804e69075036030707203e0820001d0301c00e24001340000c0145400f04200000681c5c4120380a4000341c1c40c2104602c1601c81e03101c0300706040c3c400b030314a101541c500380300542480c0c2100095620014203480b82c01a64a4100303012114600c240185480d00c1e0407041c41c400c0c942445d80c002e01115100000060403c2003e00004180940c16102034002904407045c81030310208040401c402810418141803800416041c007401d0428071080280c85480400d03d0542d054a0304001894160b51120074140e031464000c10240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715919838 1250 715918588 715918591
    0x60409021812150a0c200a0b0408030a06080118080a0504170303190209030c190801020c0307050f1903030b06070623010801200315100e0102060a0225031e0305 70
    0x900d1141c0f10808210710000d03138800c0011120b015643c5440c0001c600c014002d20f0515a14404040d200c0e145415000c940021b03180c038001c522400030f40740c0d40d00b003004084c000d4944980040301140d24150051400141007900740640e0b55000300403c0d00c400c9d0768501590b25000383e900881d450b5121500422400302c0100081d4031500174106800c0503554900441412800748030042501a84011803601c02c4d03240c151800d1380100b2304a4494244541c40d500641d00b640c00c42e10100f03100d5400401d200003001018071403403092045d900c1c000c2c60004859a90000b101c04019800f400341940c4100100580d1a050210f4a0254100c0014006100201d003207030b10340c0c1601114103094050f1200041a4050180200d0750a050000111003201c0c02428172000700358000740102503071070b01d14143c5031442d4031014101c40716100d940d200c82050203650000641004030007000d41c0c00310761040081d20900310b0701c400a4078990b0261031400c00220b200f40790540711501544400c15000d5540111000c9165140e0001c2c1e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715921088 1250 715919838 715919863
    0x8150603071203090806180c120f03070615080a050d030504020d060612060b041b0e061303080a081506030106180e0c070c080a031710030c030308011d0105060409021812 74
    0x7a00c940d5031f12440c0f4200c094448100c0300781c0b03070071003041210585403010004900503010402d07205100c000b560400c2c6554800041292000c0e00e803400317506074986c00b528640080500c9030140c00361030003643d141501d034000c1a000406040c0c0c0c0c1e4006c1030030354440c050760311601f0794016030402040e51140c2e804030301114500030440d461420201000040d09090180380c80a0403035000e00c0c60810402c41046d41d0480786100d403150004d80034031040500b54050a19880214002d400907507031001902c0c0c004007100f50041ca0070031950302d0103001603902d49034601264110f0b089860074440c0c0d2031805121015140d0154424880300034184203020302c18075100000c0050600c00e00f00035070b21941d10b001d210344a103c02c29000c0c0210300400c6034001000400524240d12610041480401030784a075241e00401869400540c001620b038001031110340c103491100b8042c0d111070394020a82d5850080060001c0c0316a004000780340d5008200000921140119401c03c80c2c030080c131212400c0da40150403079584d072035050b10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715922338 1250 715921088 715921093
    0xc12030b0f01030e2a09040602091e0d030f0315180b030604020904030804081905130819060e030c010911040c090b030420040c0206090105060604081506030712030908 73
    0x241a40c960191280a40209080001d000c04150081c030348011505c0303015041e604c031500c2c0540400300b070365154416440f80c0c0c491180140c0750664001800b95a6031521068550a10f901d9581c1820b940e42c1c140c80e010300c0e13074140b8265813185000b0310120064819803443c0140040107a0300402c00179000c40402415104142082007106042d104044d51201b0030381e8065000110383c4c001c200480d21910400782d2241c0682050392501001c3c400c80c507003449001d4480400224003081081d08400c034064110002c20300c00c0010900c01140f6100303040c6540450100500c1641d440703e041d42c02010500c02d941050071080000c01c0398000904080d5949d40b00e08560910983c039010359081c41a005e61011003c1c1d42003403000324110f41d2180d032100141d1100070911409924401c4128500c5d64482c02003081440303096020301090b0821214030b82c00c0d66005058644140d0b000c4c40144848a00041e242034113444040c40210282c64540c00300c2d0800c10079421105e09603800ba60b0310800d064202011204640c04c5008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715923588 1250 715922338 715922359
    0x40b011e0c17040609090c030204121a0a0203040201021506040b281d160e0628030c020a0b040c05100c03110102090d1410020309010e0105010503060f04120c12030b 72
    0x2c803141c075803142e401850040b910b1480180501c103401c1e88120605100f80c10010310f001e440300502c0110b18400c000c01c03115007005081000d440e44003101c1c80303a044549d40c4815801c40c04c0c2980045d48814030000c018092400c08800100241e41d143c00100c60f5030006890622040100a04502c02c1c401985580c40c2941841d00700007561140650241412400000303070f410562948a42c05503440c603000006410000d0502d43c0280301e58038100180100046a6070034070055084999140254030306003800420705180c85118003003a0b030003181c40700b500d90780004690301035621494018a02405908101e400c00c0c3c00d00c0028120a8000301111800d50103510f40c51210407500d84a01d0a0388510880d40360020351a03e15140020000c00007081c0b14100c02c025902c065040002400c00c0b42c100721503441881c1c0d101c20000084c20000c0c46082d01600085e0098140c40c40d040c2c0030150007000140c4002d040016114110303070b099102c1c14501c0f01d042d034000309041d40c0040341d1400030090b014540c541c5224402488 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715924838 1250 715923588 715923623
    0x2190605120603060912031f0b040519060206151314040318030f080c0309130b10260403090305010510090507020a021f0201090c08032a0309040b011e0c 67
    0x13403440c1c4500c043c00018140c10804000118060b04060040d00d9401c44542000750820f40b100c5031100038200074188035445500d06020000000c9682c9a0402881d000d807c0c203000c201d602040080d4000f684410783c5001506074000b09809039010031a44c2d1840c0d16100f1641c0080c40b007915443d015a000b0b075141c84050a8140e07803444c05c0c00251000800c079030441c2282030005070710600a44820420803065a06101840c00454852521160b1002400382c1e0740c01250303541d140a01e0000c0e180340d020701d44601111003d00e0030201304881c82c0406030f140d00d0410001030406100c0c40c410740107154008000e204a08141c104055446041e010303003400756051100140c5c01038800070325101001e400800c41000c0c411711075682c80d01c1100c00131400045540f103c83e1034000c42d2171148064020220386c4000c541d5040440c00018108a046070841e030300c005031000c42d25190400105aa4416208039400108040d4400040e1905a865100f1240512030f95540319251a00300c085138468030b014210700c03800a40300c00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715926088 1250 715924838 715924843
    0x20423090112060506040617061602011e0e010e0d050d061502100902010e0a0e01230d11010c14060615190e0d05031210090c0c0f02190605120603 64
    0x34002d001c02c1c888268044800314010350000e43e0428000380c8001941074403200c100e401e1900074510885140d0120080c00f000d0a8520091034140d0000d100801c04616019280119020341540b022007468903058192102c110a511980104803070342c040300c0550034001c00283c5150040e441082d40c0910304540090000c0b240101c445101c861070f4041d10440040c980d5280092810240c04d07410071890310102183c5494071003010028090001d468401c1758542600042c94440108120284010040c40e1200c90b88031500f10301d58566100c0200c02c6c0f40d00c440b2004884815442c0000b074071200300c400c0381c1820000e01148a90241009540182c1101034008104040f841075203106074607100e019a8441d050380c0302d000c0448400e2401071000b41c0020107a20f03400d2864000b100500e01408010042c00080c05019842ca801841c04180600151403035500113000785280d02c101a00c01d454020000086607102400018507428818140b00d11603280d030130007415034005c8182600c510300740320040b40b00362500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715927338 1250 715926088 715926091
    0x3010e0412080112060213050901120c0531020c0a08091801210812090601060908070b0409020903010e070b03011d150111030d050429040b010b090105090402042309 72
    0xd4000704c0440030368030b5039a400254440d54044000e2074050501280e5962103684090081114948504405500f030601c84000c425940c840791146408008174405030306006410b03c00c1464000030f0310380325044801020080d00c100110310001d4000c2c102464100310010001d000d01040556080740d4000c090209586c02d903400b801401540e01d000c54410112140382004c60074454443c2090b10704003a20000300c0d0074450820b58100b50260011001030008903400314900c40101100c10007402d03031030310304800c0e1385942c07060b8000c1c981c201da000500714000792800d412148030b110180e000c86810594804440d1542d40081c058907501389000032000b01d1240d000741156004011b4034222511032200366005643c02e41c250090405640030600071000740c0c0125101d81803069000d41c0032256a43c1c030038003006101c0b14401484098581c900801d120100b0b80c54030a05064441d003107282651411341c3c1340181c50501950390341caa40140006000710f200d980c864400ca084044a400b18020101e20004000c0312540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715928588 1250 715927338 715927349
    0x60201021e0a0203040509010306020d0b09070e1918050709090b03151b0403060203040209130803060405070e03030d0e0105010506090108130804030c03032006130b06031203010e04120801 82
    0x1d50300d006028059003a00400d0b18a41600490f480c00d60b4034404104141c0b400d07402602c210758049009511302180d400b8800711420119203981d505d241012001e0028000d102405008812a045404a01302c070121140081c0c0100703a812389144010841c50703000703441c0c100e03292310000c0d00844000070401e50b540510126828014080c0c5100352541c9000412044000c2094540b60318601c40c000300c11058030000c0000d14040c03c40560b6a140500601061450281500f41a405600320b1803010581050640b50806821103002ca1152516441200c1422041880740d13410700000a070350146100d141d1003ca0041407a00003400349a9130f55007004454002c40603003c0c00310745c0120007c1d0f400892101c251520314410400e0030304107600c94907144500c958070340040300801c00126070030051140c1e59880c0740c20704044000521083c03500704040010741c10444c000502249044001c550541c0c0c0038400307a54290b80003091305450b50713968140c9540c0c80d0380075a070940f030800e51a0080140e031446142d07941d060300c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715929838 1250 715928588 715928617
    0x509030a03050a1407050d0501060e0607120309140a0326010b0c25050f040b13110c0102191b0c0509040f050d081e06090402060702010c060c090e0106020102 69
    0xc0c08064141d01410005020301d034082d070f0300c400c0b07261007103612031a00f80200100e503116625410484061000c80728181c0015007170084070080e00b50207a43d12021200180c0d4400c10884c1c2d5800c4640e41034000d04240341d0300901101500740c50402c140b40018065490030300950360000322085c03503109142c1c0c03001c06101900c01400d20718018400c040e1040018140000c5820885019515510324641403542401c3c0e01c25014545800c100082d2404528042c00c440307088504005040a81002907041010400a042059112102003800050f034506403808130003200c00130f650700d801c24025954010f65080215000c40e075207656010110300050310140074164001d42c440100380c01c081c00c00050000040c42286c130b12080a200c071000800034403a8580340b0034640c07290204c60400200c0c1c402030340c0703000c2010210074408004200c41a030341d600d511604a85c05135091a600c00c0107000494044000c02c00180400d0f0800f2050500540e004080c00100c820140030080140d80742e035002c81c00e030320030007040e58400c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715931088 1250 715929838 715929847
    0x51b0a1a090120030c1e0606030c09100f15020712121803021e030706020c0306130c030c03080d050a05010e04030f0522080d08091f110309010905010b04050903 70
    0x2d5000d03101d80408508a020003100315920700010504d50380c0a2844c05603030750404032401d1142400c02800213140c01c103c074043d00c0d0616228011030f40d2403405804491041540a01044440c21900b401001528045080046464423a10413902c00c0655074500d600501c075100c4001014040343d610101102c0d4006112410340240c008101c1e56a0512038806042100700940000141d60340d4400040301405003009661004d40342e0101404e03d04a07a003e2029034025030106039141d900407400c035030f00c5030b52a00c01d000102510300388042c0401090700020040348500c1000f00c10320241c240a030500c0000b42e038040c00555a02d04204040d2a020b01c10b907a9034184881c040750010307014241610214049152841c2065000342900c0055035a40001d0020020040e4080c8400d080608c1409600c4001c0d04124125050a42000d952000e13000b445681404542245103103030f60954000c80c0030622120b03042900c0707003403032400e1074020100c1713040c112499880c1c1500c0c40130074202030041e10300c2000a04061400d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715932338 1250 715931088 715931107
    0x14010b0306011407030207150c0201090509090a082a1c0e0a061d1c05070503010c0203031b0c0a11090a1109010c0201091205070317040f031e051b0a1a 66
    0x1340c0081104a055000d0080d000c03038a000d00900d15801c0e800b0f80d641e03070741c135000c0fa0340005464202c40e508028082c034015410002240c8000541d26440d6502c0380301e003aa80d01e584040d00d104191300a409441d02f03c0c03500086a4107420001d64500101c0f00c81580301c41d002c5c4224000d86003a107001249a4028080e82010007100e0f005200c000d011251000b115006034a03400c00203501a000d8208600030b84103c014040c041c03080401086010f071100b54001c00c0303000030711403000e540e9010090050340d00d2460030444949074010fa00503900d480801604940903000c4170300d0a11128090251054060030b10380001032030707a000c00c0c05585074601c2e044419524004820740112442480a4001c0e030600404403000207442d84009202004c0341d0050010701100c9003145481d41c051030311480d015400040c203100070b0141004c83c00c60b8008503a802500c00c141703aa84040c490000056a02010300507000c1d42d42040b421403c060000e00f080c800c1201c8420740075441e032012240f043e070a0092240f090b0410f1281400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715933588 1250 715932338 715932377
    0x70303030f0237034a0102090112230604060e3103080c1b01020a030506031c02070504051803071b05010c02030a03200706020114010b030601 62
    0xc01c000a240c0507142409400d156080b02d207140d41245203070f840c1c062200c8082c1e20351100402c1c0c180031900d4203108100708041c62402d841c1c0c0b640442452003201e021407840e0801900280f01c00c1103a48040907541d1070030b03029114000e410608015001c1a503403060b81c9056101c520600100381186a03101044003690f070751181d80303140000c3c0303800d800980d1048085440c0c0c40a00e0024803607100110743d10b40044c1003c01031800d9942c00c40812003c0c00c4000c0240c00040d42016200381d010450720074464490b408094001c51524840d00140d10b41d510000b5407188003a41504032520909003a0121401c07a404000d40c2d90a1106140e905001070701304580602c8503103004d810660f0002080c0da140c08102c4011207625003944d2004c102128400c40002c0640b91380040750b1495802080242007080b08004250040390f00c80501d400e00800708000015404842180541d03000d42282d40c0781c0803564025201c1e0380190080c00c1200007509001c4152000060014500088910408040c1e441d803c240f6104980b150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715934838 1250 715933588 715933601
    0xc06131214030414010216050c150705060106050703030b041409060601140906030c28090909030e061b01050117101b110c0627030a11060c011e020a09060206010807030303 75
    0x940a540810600700101f490a0240b80b4040c01500a402423448e00b104114480d407031610f1404048200b401050007280002c500181103e00908016a880c400d615045000b414004001c582c05460300d0703061840030601c0a581c0c0d105252140071074009480f400010b6030802200b081c6940240020881e0b03e006013044405182c200c0742040e00302e4200750044e82a0000105400e400c28100400c1c136245800c1c1075406180800144900e120400a200d005c0e1801403d5800340905035000d54800101040c000c1c0e42d4801410b02d8504400c020450740d40c40d0315843c241d002600141091728030881408088501003072007001c891071044000c202c2d054081400c03c0d600305d130080313510000e140980042c0501c181c6400300249a521103540c5041ca280141411021402041c8003106010354807514103200003800d4804001c5501034200c9005407201c100d400c690340500400c000c0c0d1710070043e52101d10040700c035240d005007075415055101c1451403600c9000403640ca0100b44107051040e1300aa00406c0424003d60114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715936088 1250 715934838 715934873
    0xd18140a020f04110702030307051f060302090f0c1c0236090c0d0c0f031103160e040f020c151f0e190507022505061207050c061312140304 61
    0x643c140811743e000607055400207c4180c8294000e102c4c1c501d0900c0d20281000c584078000d8000b00b00213401d580108465a100400105504900c84085540152030009950201942190241c41300d95070b00780e0203000e50044a94144042035205c08402c08006282c43c01c000016054800302059840b8030811900716030151207104500c60400c107200c415042170082903000e01482c1c550055003988600300404542d80003180554255040c000d0142c00394170641807055000c850b144c01460401071f1800500142080d0707900242d958800100590481c0f40807070082c440041500d48541ca60b502c00b07192800c54a92a0345004058281c001c061280c3d00c005541c00d40c205004440c0c003400341140764004e4080b12001ea84800c0035a000c200e6200200c01c07200700c1d0b080440109101ca42d09240b4000c089091405840b103600c5840d41640c0000b02c140d07110ba401d40e0103090301a400c56006061180034480400b0141800b6a4400c6801110004a6000c0c5191903000e00c200111a032440d44e464076111300b11607088000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715937338 1250 715936088 715936121
    0x91c0c0b04182c070f091407121d0703021806091807090905030c1c14070f0b040b0907120f23061026120705030d18140a020f04 56
    0x2140202d0b881c03d480f00c96a00715400500901d8148001c2d5039401d94190b1020200038103000d03081a0810003d402c603070f040103060400820290035403c0040240c040400d2216034100803800150300050002200800c6900950b001803605042d030340c0c01c2101c0c281c00c590050708501c828021410b994900d914200400300311000b5209902d8881c040c0b00240d070b24911041d19198404a034038001c0d41401e00290150741c10040c1d003039100c5402070308060080c0d0301080c418514240c1c003181d55801d000c9440e00c4d24610561018001201d4501460041820202503d50031a01d200e14107002c030749072400c031100274011030b023000381c00011040d240d40d251054040d4034481c283c0c1c040c1c401c0e060124907104000d0319000700303640503181010a04000c0007151001e01c0c2c80c20b110100c3c2c205000c01e0300c124400300700d42500c0c04460303c0b4241c0c3c9594a040c290f182d881a031440562462500299014030300071000020b1800b441003c41c1c4200034440025213641c2c0090301c034081e5100d980e0150411144c5401d41c8610b8005862125 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715938588 1250 715937338 715937381
    0xc06070c050405010b03010311040c020d210e0609120c03070f050a151b08152b050109030e0105120630030d05070503040503030f060105091c0c0b0418 66
    0x2107400d0707440a81c0410541117001c80148200030390400300e8412030380161020801c68403800402592032014000d110305114800c1040c0d00e810059405031003e85107504000e0010b90303904d1082a9848900300d074500d441d40540303140382d545560031504880a1200b908001e5042c80029111051142183d1100312018480e20380c1920001c0c41181c10a020b40d4501c1d200090b40808003945000010800c80500040040c00e00030061524141d10ba44500000141c803840d04241c99a6060101180c02503c0c42c0000000e20040e8401c2240540004c00c80a22030340d101e00c8110303034810040d2518010854615440f07035007100050795500345542a45a008070404806407640303c1480031004208a4484043c40d40d0000101c080d444049070040c036403c0240307864010303d989803681300c4d2074482c0405803030004184c02050100d0140d0b03100e88183d8001c05401400c112180318807540742d400d01152a00e080f110701c07200030070000d01040700100b500d0444607c0052030320040b202068003402486c0203003829981c3d00c1e9800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715939838 1250 715938588 715938599
    0xd050d0f020d0f050714120109020a03090b0c03091b0f2b0f0b0708090607030203270d030e1902010311070b01120b090d050901031508160f0503010e0c06070c 69
    0x1640d43d9040c026032001440f82040c103c010034401c9a034107200b0049408000d061004d0543d03510850449a101c800181c07246002e080450143c210390f00040c1808240f041809000380c000f000a6008000d45000c0756140c103141c808244002d9194440c840d4040c62016806400d4100a480000c11150038608000ca04240148207141c0f5030310208199850b00320102644100004581c4603504400305003003000300351500c254011703900d000c0205507104054011020481d09000c4a1014065404407007000380c2203520325411550740c4220400c01000a4109145102605400b1440280929150040c106030301c040e0740054014095074080280c030b03048204441c5010400303c441c510b020742008840490810440c2c01c1000c802c2c500600025040e80000107144d000c03641000c00c481d0840702c2800c1c040307980d4020610b11100140d845d44089014010210082207018a403414501a1040b04600c1c0d40c24507113500a16007281c0420070307001e0560740002108541807600c8005401310a116140b40c1a101b0f440d10b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715941088 1250 715939838 715939841
    0xc18070f03090618030e04150b070c030227060f030d0c0c0902030711070f0506030103140c030607051b070e01060e030316050c0108071b030f110105010e07020706020d050d0f020d 78
    0x9134a80b030043d003600031880c041561061541e825002c003100c003840900806546880c5840b202c1c4208590100c0004001c410428103000c24402150000c22030084824545619100304150603100a11481c1c40300005d80303585060240b00402c00c002400801c0942c2842401703440c0c0b413015001c2610030031981c0720006840c520b94001503208403880d42d01e2040749a80881400d24044041c0c21500396030340c400101b80000e4039100b080d0303811030303402080b07081030052185100d40c2807440014202d07405001d54410400a83c6d000070080440c00407480c00a0b90108d0801d0703a40d916404203026a2419403204001004290302c509520411240001c0030f030780c07600c021503042c1c030b0000100d4001125035070030403050250190b0b0040308044c0d2000b418201003c1d500400f01703146241d40b01c001c4005060105800c816042d0504c40e005540100b000100208440d50711003400003c2000c0032192007005115030b80c00823551a2011400100007003c42d104d8070b041442401d0040042c00030964161170310b0f542840348a0901e00d09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715942338 1250 715941088 715941101
    0x8030a051b04560717090910060c0210110a0f021507020102031b0c0d0501051e010b0a0807030b06040b0c1b1c030c0b0a02031008070503030f21040309080c18070f030906 74
    0xc050505c3d640e00c0c4480144991101c0c003d0041d50345840c04003080000395005845c2038103555044403440c001b401004020380301c03400000705002c03442c810302040304100002e104101c11440d00071103841d518a180050350b40600d110710071000b4010382040c4040c0d02c0741245c12201039401001c1000baa40381d50412000f09552540d64001075400740e440d0000e003c403a0070341c0c80090f81d038030307a01141c3c2c51069810420500d1951040c145850208178042c0c000a060b070307200b0b038003858100400502c650b545595400d80301201b43c001a803d503070640500348070f50016002c5052071030b03200640906440007140c0310414482519040042c01e9090010303601001002410000c2d01520643c0c0800740143c607418110100100f43e0074a800c9564694004a41405180da0000c2039030302da4400480c01e02c0c0c2d201441040c144060361914008080c0300d003108180300816801130f1115013605c540700c017168004001c14040084020001403101103614014021074407552281841e00e405415a0801141755806030fa80c00088815 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715943588 1250 715942338 715942373
    0x20d080903040329130c03140f010204080a0215090d0b04080909040305040e0f071d0301020708040f051c0809040507110a05010b030c0a0308030a051b045607 69
    0x20394031242c102d482507100034607004080405c0303000d0050320f1990380501c540b056000142a0b94092100d410490004100112982900c1c00c001c0d9100c0740e449242e607948414001d01244140e00c07400b098900c1403200303000c1d5a4940300040c80c0301a60341c9a42c84044148401900685156008214001d001d441d9400641e000343e03c241e40c0c00d0781e15885d2000f04c10042e0380c0070784086001e049035002c0c46000c941c003401680c0c110000b04c5ca0110401182d1001900a210300d580c001d20080d808500012500083c0c0000301c120340c8195182d0742900c0c0b1151800015450241004100d55000d014042d200e05040d44001c2d480751203404c01582c40e0f03034808444c41c908504088212141e80d1079a603890000c3c1010b1040a019140555140350180d04603071f1001d4241c04010481d00d5000da03580001095210190a2003a030072142002c007a070f4641c4c40c0c0141d814980004080100f441d250090000ca005480e00d907090829001c95401000c150703800548400038011504103d041c0740d80c10710011000c1820000e03000d4008a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715944838 1250 715943588 715943633
    0x3090b13090f020a08160c05100516080415090c0504020c0607031d07140a05090703141b0304030e010504180605150306150304061d010905011b020d0809030403 70
    0x1403500c1140020380302c400884665450050201302d040c940c01c52901900038450940458a60541e00e10032030f80618036520180c010312400c0c21041c607100040d44001e000c0c03c02511004c0c0008a0030409448464090f20002c0803558509801c01c05000030307034050384101d88510581e154540e50380d8001416a0400c0c25044600d0700504140a0f80c140c040c40744800400003078640301801400c1485040c0c40d0b408030b105418025065200b0720103186ea424400c903002d04002088842d00e0b0422103401402003074800d84180010001c9804a000d8280c11141c022490a040310030a1550790b0300c0e81d085414480d401105414020180000315080036124a0b4140008040380001a464901130400103032542030498101c90002c104140825601c40416001c0204103400145640351510f15080004281020040007510101c1c02911500c84064212150103405440240903041140400b20701ca1403031140745c0d4000d60300142180d04500d024442182d4014511707810381341400da403a01d0340c94082800740c8150a040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715946088 1250 715944838 715944877
    0x82d09030d0323090708150f0f0c0a0509010309020301060927110909030f0406210501060e0f0102012901090905070503010909021c0b190203060a050d03090b 69
    0x3400d00300000c090701c1c9024942800414035040a82c0b400303d48500a0204803030141002920300682001071100500e01c03030080301c0303500241246221100c078050f20075040701c0c42100d010400128452158a0240100142e46450100707900c1058410751320644019042c55100c20001c0007598085c802c0c08000d01c0411008100492802c500d50308501c43c88100e83c0150719000380d84808074659445840c44c0c6d11003922003400d50703240c40305603610314003904514400f2008001030110700c1582c84a8801074502c039000014500391100c4454405a400900079203000a1100c0c1c10f00c1c45502c0d08010075800794030103000000f040c010310308405001030807404030242c040f811100803140550380000d24000600082a00f00454244503000400c0f5200600c5591041c544078076110040d035a0313003e140201d881c50010712014020711890980c0340d07074100b15034082424900465980e004030450007104d100e4034004202100007130a0008005142c0c420000a0741081a14200803440e50040700c001c06407220342e5800b40040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715947338 1250 715946088 715946107
    0x70c050a1a10050103020f04060507051513030f02030304050d140d060f060e030a0b0604020a030b03100e1207170c07030507090504020307060309051509030d061202030105160804082d 80
    0x1c2d9005900c00350406104100c6007501005d86002d072001d031034203840e15030356610040c200343c2d1400300326a581d2a400104d4001340020416070b0711440f4601c07403083e180c2d0540040c6042050b80c5a010850b0040e00c1a000240e12841591185840c4110240700b41400c6090515003101c501c100c45854100c4110550f02a03400d21a032a01300000406069046008203030130780b003a40d80c0c1c1e429528080c0540f4000c03a00480e61082c81c1d4081e0300040e10340c50780034044412100070010030001070f0500040f0000c2c0390244800c6103071502605021100b07515080501842200036800308101e195010b21040b01e440c0c01801c102100041062114000030400ca00c00402d140c00c042c01010b051110550010302414034185050300081c2e80032901c15030071034016662828964030480d03802c0c1144035480c0c0c1c03803081515080b40420310b50988029101114020b074002c10003070780c843d08030500c01c0401507580804104a000010b000415860040c00c00d85140204103407401c4003100070050190311086000325107400801d24490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715948588 1250 715947338 715947361
    0xe0d02060d0c090f080307050709053403110301080a0f02060c0105040c0e010b0a080a1e1806050901050108030301150908060c0a08090115060c02120607030b0a06020304060503070c050a1a 82
    0xd0320100014507e4603e2070341d00c681d80c4411620500200b1921100011011211240444c1800c0407414400499a80c0c21000342140072060340c019011900d09903041d401c89540d070b8240c034141e990880c001c08503510a6220341c0303140326904400f00d0b4000000c100e1102500001c2c02058090340c03181300c0c0122400d041417842c1c1200c80301604030101c0c1680a20055080c154040c1e4010303003040d524200003808284095455120a000904440f81281011108036001c404010a41d190a00031181000f051b198600d00070300b80d031820702c5507000e40d500c1440103000c01d4074070580f55882021641010350b42c1c47c1d550300c44a81400400c8844540c18240810000540c980000c8d40b164000200c100030025800940551400f0030340030300a071020450307404214411074440c01c00b6590201803c504640f214a052180140a40302c1d683c0c0c0307503001f0706c41c500c1c00080060001050b1000d841c4140c596a066544492088030091146103059506214031031415022420040380e040607071005d502240b00c03a2810400020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715949838 1250 715948588 715948619
    0x21010506120f06011a070f080301062d08071205010e0106110c15030712021201090621060f0f0e0c041b05160c23010905090105010e0d02060d0c09 64
    0x101a03421404000d22240b40c04920141076031200b07956001d1820300816404014001d50b81c0c000c10035254119120180b150a50295040b00c2d401e40e240704010384000300c80b410060080c051680340e18004500181d90b41d00660034103a2140003403a0840c0c016980405110a8960a034030010f44034a40303600500c03240f64012044c000f50740c03050f402000340308411004205030384070201c0f00407009003000c4007140d10140708607a00403240241e51400d5480e10802c207a002400c400038071440301014a0b100740058510407414140340000c00b001641c000c0d040c3c0c02d4035008040c0c4080f5540900c0300fa52584501c0b140c0c00305124a0281b1041c0e0790080403203081240620040340c0030356503940346c01c1d88540c1140305002d521008640300e01084081c1200341c1354051601001d0701e0882d400c0405600e5038a160341c03400f0b54a85402001c4001c09030f0f18a204155500b00340f0060030828001c0c00c3c0040d42c0d0620084060420308070341034540d1710107000c00d4500076103a10b0120032102541c01600000e840001c081241440050107070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715951088 1250 715949838 715949869
    0x6020c15030a051803041d1305030a110111030c0a080c031302010c1a010e04210c080702030c060d140a110306100908030d050109142421010506 63
    0x9203040001800c00e03040c00018036840c00152110009070400c16601c25896602e100c680c00c80b5125a2550350309448014105103c0070040e0010300040c040007046000407124a8008010b0351078801c0c51032040303d8034080001d4421180d03488441600c0f00c81204401184240d00d06403440e40c669021110040904502606807a0400c0e01030081c00760802c80060481809582420f0062802d80c142c03600c0d080e1400c11003221007008941c203000203007454500d860944614850503101070500d5501c00358000945c10300c3c02040000303200007a000001036241005183c0350340020100e0b00f44070320100000b005d641c8000c10000c6a03a8443c1e40400304c0105136005650420100d90303060150a194a03450b08480c04010000d5214084445580c5402801000200041d0201c402540d0303544010000c690003414081c03282c0f100c01840d150380ca01c030170113180201034020b142c2840050001c3d06500d810400c00e00451901a90140014600d42d84a00d240d9021210f800d056500102e480d141100800c042411220402d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715952338 1250 715951088 715951099
    0xc020f0106030302030924040905011505070b0f0403050712020c01140316080c040e041a060301150501050c010204091d06060a320d03080f0907030506010b16150606020c 74
    0xc2c000241c010050743e40e5800185c0342114914500c541c80102d52000707250902140c0d00000f030200301118540c120741e05942c0940041d040d005c0d10790108460034030a080e4040c1010310050003080c2240025135080e0b030018001d28040b820800c2d030740c80e20348802e80c91045040140c2e01c2140b5000155030001d40505008030710b404000d04500c0d000c0c44140c01c4040a11a1400300050720300000c41d40c02d03c004c03c0c7c078054103050414500b03e1a061928102c00050700c0303164510681d8034400110540307814003405442d4603482040268040c588401542c15401044031420300d95024480480c090506c0e200300c1c01c861051104d071140c141d50241c900c0c1e040c140b01402d400e02a41d5200c81c00e0041d44d00705011040303149150800410101c540d2803480e04240801c0003920744c007844c4000c80405043e4800075040c010f141400c1030000540391440059500c400701d100040c030700e810a0b4010801d00b03a800000d0b2003183c1070014148a80d0300941d0310302880051002414124560b5003009028041d0304000c56040c7c0041a100b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715953588 1250 715952338 715952351
    0x301020c011407090305100908120a09061401141e1002060118020405010c260a051803070515071103030a0504090c0c17070f020a090e190b04030804030207030c06030c020f01 76
    0x81e856207d0707101459521102d03444400c10400c110201c0c003160305042034151400700358100001c03003c000d480d240b00c00f80c1e986801d2000c040099210395580504807a4110801c0e14000c100d20140100501e240c09030301c9030103044c000c451a042d01e403103642180312865a030182070558101b203400709062826118941c0001d01c140b10501c81640c03c441d018071080d4000c00d0080001030100d51401c10522000c2103203416039808944003040c2900f00016008910908189082e103402c0c1c1070030700d41e80e0301c81071160b2607001c00041081502c00c000800100041c6001d05c1c49000300c0d41410001c00d1440e03101c0107190000582c005001c20850718035220300380a546140c07400460070b500c3e5032900d120900d9801c01001f85100b0000d0f0100400c1901004000c0055018041c891000e640703d90b010020001c420200d02c0d28001c11480d0781c030741c00103c00c811078002c2d032203039814800da1925202145d2f0660020011801d40c03103104404000b0070b00c507465800090150340d601088403614000c00074280300c5600e504101584c106a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715954838 1250 715953588 715953593
    0x20070b0c091012110f1b06091e0c031506010908011407030c1e0f0e0405040c14060408010905100c1b060b060904061508060d170906090301020c0114070903 68
    0xb241900c0001440ca0040f03188110102079000a240c50500345034050702c00111a8602150400601166615082d90300c502002d40c00361162103400031902d00c0295000884245a010100c04410305214906000c0312803546036800801d01c0c0c01007400783e000f81c005d6000204081c039a4000040310180610100900a08429601020b09108058500d1003416114400300e06618414014100c5d064015100c034007c250801c5005082c003160719a80000103200503460100b9070038039000b014001e9a0150200d00c4052a0106002110300d1000d2240da000404020020718000240100c4c40254081d0024140d483e200d085000203c1d2030550508041c800ca00c1404c400240c035246c09010b09940000340401c0100600c40015003622030a05002c0e8403034541744001c28003811000d8003410345541511110915280e403800c200b03526684642c000d00c050a00700c0b01403d41c0c0401e401401c1240070191019091100100000e400d80e000030741014803aa40d02d180501180341030681b007a400c402d1304e0801080450458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715956088 1250 715954838 715954849
    0xb0a0e0a030509010f170f0a0f020a0c1104200310060906050a030c0207120515010b161101090902070803150f030c0d0230060a0b06030103110420070b0c09 68
    0x102d01181400051070740101841d006c0d1000807050640380e01c1440c1d0903e042c4648002c081c0090300c03401651840d0104003514000c1c2c510885030035039415250000d4640c800e55444002c0040354020b140c1180d15444011708500c2c40c2001445082d5080e0030365a240d2618505a0100190560195042001041080001e00c0d00700040711180e005510b000b24030b0000c8220280c2c541400c0758040c410074980365404034244240410300321812a400c400100442c0d07030320300310340960b07029406282c1600c410720f5803903030300040081800b52a0000d04ac104200402e50b186a000100d17044031000b0748030504004100105140c9960b854160301104a5000a1010200011942d169070001406000d0a100c0c1e240d58103669072010003400c45c0459040c40d0700801c0180440e00c48040030046003200d240f003200041800100c85004840c81a000500701c1815a803850702c0c2d84108085446070507820903074403030340c00a600d94031843c0da04102110301e1580d40d0b02c0c601881c6c43c07203c04000500d010034490741800030710380d0780d900e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715957338 1250 715956088 715956097
    0x60b030a0203060409121812080f03040c0f031202010c140409020d181b0602030909040b0601030e15010f05010e0310021c0501230909060a0f060e040b0a0e0a0305 71
    0x440c40040e160b588078070200d4001c01e40d460002c0e0210321580c0c4082e420650010402c1c45061506211507003040e80c54a0003842d0501440d801008002c00b800014030102c20172015503441400381c0345503910a5a0b840d2000e40202145c1c206468500481d00080c1c0c0c0580c090040405440d228900081d400042d00440611030007203004040c03029070005581d4503000155005096501009003142d0b0002c0e40b03a24000d401c03400028001c108090840300300149650022080d50300c00407002d810702c2e0181c1c0c0d5641d2142403081d0002e10701c6052560759840c03005004004c01a170303101c3c1000040382c18540d50426030440000d07141540b226040215040001881b52408a6144800c2004010158980365503a06401d44440c400690303010184c81d05000103000c6c039806510319802c404140c2e000030703000e039560140420714000312450041a423044c808600e440c80c8980c010328403072028110002c0c4864a50380ca00c0802d00041c2c07400c0e161b2204200902c0506105032050384510340850b002009941002d42d0702030040c3c000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715958588 1250 715957338 715957351
    0x31617041b050402030f0115020f030d091a1314070803120402030106030b040c03021f0e0108071101021b0c010e0109151b06090627080306121519060b03 67
    0xd50110755803001c8201500d001400000b8001d544900d4409425211180300344925540e0005020000301c80c10f0000c12410010880c880165251204841410000d0103610504a8000c0340c0040311a211810200d007550007071000c0c513444000201242040e030007800031303034090402a812404042100301400000c540b402850031005c40104d81c1c2d03500009004080c03070b0b4005010b6603d04010001000b070000c050030252482221501e0741001c0e50880c203c1030103101c0c0141030120f5030102000c802076001d0304010f6800202840c05800000300e002e00d240c01d9030421924148101000001e201414030288580f0300550030a18100050410220000b020521148500c01100001c0f0745030801a500c40d540b40341b200880304094445030205490002e0040a0300c450680c1d20b01e2034116440300c181049903400c0000e1098020500542000b42c85050007079101411003036100712811442c4500844c1404800c108400140800e502c40c039152005c1d44d0f0404180708400b54484c07a2100074015000c0c03040c1036941041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715959838 1250 715958588 715958603
    0x6030b2412013606080a2604060e1903140f0c0907090e100f0f08190206030c0c03070b0702160e04150e03070605010905180c0604060f0203041a03161704 67
    0x3c801c00c0c031031002400207800607025030040b00e01400c1440b00c12403042e1091003080d102c7c1d02074085100240442c030f0045004580c000307400c40f01601030b28940b044000c003464003200ca8150000d5501e5481c40f1100200a08002080c0c01c04200d800b0f1965052040b1001c01105444c2e001041c60040c5005000f07802d640902c1402000c03000201e401404800c02c5040689041901003039500c3c1c44410100102c0f405100b140b01c180302e5080a030000c0d65070702803004a0503a029109600b952254281c10725103400000d04814244414001000070900b02c241081c0295056000741c41c614445803501d00d040409500a400c01d1220030003400009410030440100049000c41d00241c0341c20701071045411845000005800c5078201400030550003c00d174000ba006401344030003501005504803090341c40314014500c0b01da000c44103000400103c0e001c0c0300015071511061050343d25190b194a80c1c61120440b807030100e031140c44080100100014564150260503100781010790701c020001d074160252880041000708080d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715961088 1250 715959838 715959929
    0x1080906060904331113051002030708121602031809060604081b0f0a0e01092705030a034a011119031506030b241201 52
    0x4503a56132a081c0940321104030306a403055040c000c0384030041900b100c403440ea1510007113110b030291010131a01010034565820780401d152804101403818001c0d034120550100308007420014000350000c20300c0600c91110000a402d00d4010900d101c0e90254000e811365004004410300304100f01c0d410b440800044035502c11320342c2d440010070500d001c0d9620403910751040c0c000440c0300d40420300461924210980e000e01300e80d4081010032001e010540f16448000c120303500184068030a0750071481c0b0f0108480440d9034070b581c0f051400d881151860600340c400b600081840c8040f00d505000d6403010030704404860301006000f40c071100941c600d80d040064131860441c030b0400d07c000813610309100400c02e24000c2101d00c4e0149101100d5520407010b03402208a100056416035000e03106603030020300c1250500811605010f004d0700102694501250300c1050741c20151201d0a00490491480508140c820389485110420446e107074410303044490b082c5249610038542048140d21101156800d02c800c0300350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715962338 1250 715961088 715961093
    0x902270d02010c1707060c051b0607051b0a05031c1a0a1401031e0605150a090e0417160618050607050702040e070f05030f0106080c040207110414090c01080906060904 73
    0x3600c01c5c0c41d0000d03e03842c1490904200a508840a000c1c4044041c8820111300c051101d495120381d02107540c113001c0b510070721080c0242118041c2800c00e0303074010400c450002c51651603952854101211401044031a040c500b8400d415030b018004003503440032034000462400300002001c009060052aa55900032000c621040e84240c211a0004652006840c09048a0742c00e00c0040c1482d070155600a030000c8003422070b01e03100c80c001c0b620816146c0e55601c10441c10090b40998480014109a0300d031468055900101410140240035600e021180402d00d01c81e285804001d40b0800f034010386a0186185042e8049980170400a600500e40d10300147d90300aa880094000c022081d03480d1b0307540c8220540400d00c180101c4191050f80c00403400c030b4150030000300495081e1a035500a041c0b0030703001180c5940d601d082a401a0011a1048804c924049a0500840c00b11410315102146040071b40007031001808040c400d0301c1420300c080c60070582616001c01071a0b91603001920503030082e04080c000806 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715963588 1250 715962338 715962383
    0x512040f0c08061b070c06081f3201020d0e1507080c0c100c0f17130314010207020a0509180a030f08010905060d03180902270d02010c 59
    0x2220340d000800001c0152640c145950f1a1800c03105000791003811204007074603200c1c14055944050b0700103400882c00782488401c07207140c1d0019004125071070140000e00d40014145e40f601c0080d0583c9410200d400c18031844a518409079081d2002040c1c040015110469a01050503402910075040076600c040c401004580480c02d1445182d0140b88080742c180100105c450040c1000c22001d001c0701c1c81e1a142034100700c466101181603401007001482c4c084009000801c0002c01ea0b800380b400e400e00501c4d07004000215900c61180c2c0c10605031900c1003442004a040349641d2542400c00c001c40c10300d1002c2d400325060001900a5074460f052000000300010111400c4004415402090fa10000f030286000752003031010500070004204100004150850350340b141e60b1040000034245c404244541d1400d688034080c4030320040b0501c1c0c60b10404614001c440c0018224044003221031081c0303007808400d680964081e4004944122944040d6001607a480308124031280e4000e8280ea2420182c0b825001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715964838 1250 715963588 715963613
    0x171602011a2808070602060609150d06180803010e0603060108010203160804050a02060429030c0f07021f0507061103060102070b130f0b1213050d11070b0403060204032001051204 78
    0x107040784100100800c450b41d0200707c9a002d07032015100d00000d5241c2e1b56090b80d4060209008541000d45e8a410740081020350b0081401c0b64070f0031804809c0303104a51030340d49041e4800d0b046800310380850020b0000c1d600342082500d0045c14008002c50940c106907044400312100341e04a04108811007000c2818410240700404000381c1c01004541c0d80e0790365216003d0203600001000042d0340c5c0580c20007002007800070441c1d10640100409501c5e00351040c2c80c0d80030307c0d0803441c0e05a8010004071580109170101c2640d59460a0039900c94549501e50b1389000400d81b841c5000c1d81221000a00c24003c4503600080d01000b681c1030224a1a00d8004400c92642080001da02000050104031800900403100c80001c01d2031403008200410b055490b69a80300c4042042d100c0200281e0000c101110040d10a02d04814046002e8082d03d000f0380d030b54188400d66812580082c0d51030740d8005400c10400030a282c20003448044162080c024050701000a8118080c5002da20f0081e0400300c00107042081888000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715966088 1250 715964838 715964849
    0x8180d030e0d030e03010f2901120f0f0c0816020c0a030b0402010c120804120e09040201210228090803070305070c050d0302070602010b060f0306060a171602011a28 72
    0x800c02d500b05000850094020703c10108001111590840c44012301240300040c6154180c685600060080d101c0e000181004290442d010b5038601400300184068091001c0340d080682d11034450b41807081c1a240c099121122070820b5520841035a680d540f54403070302e00101da410003002c3c980c0b41d41d6400140c03a040c000000081841200e00081c05015801c03460690140380035020400c03508008040680c0d0707003c3c13062016903101ba01030000400562090b5030a6410403101010b2200302c241c2c05c0032901c20b03030f0410a0484a000404e64803140e1504060320f014002d00f0745072610016083c81d1000d241c4c2c0303078400e0250180c100040099034109000b001014800284006031140c604206203040c000c0d281c02c091302522005500300300e1034944500d0550305440302c00541d03031115403941c0c40d0803082086542c80911200c052003075500d500585070405a180512840c021304080f0b091413000e0100a01312002000c51407881c43c07502c83c207d9159203031040d22143e0b100507000d541084038601c100c501c00e04202c60b03011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715967338 1250 715966088 715966091
    0x12060c02030714060415050720011d030d1a060301030f050102090a14150a0f231b010e12070803070e090115110d02033408180d030e0d030e0301 63
    0x340c0f0b20f140019456100d54050320110406803d9400d41c0c009580041ea80c001c0003031314401c3d2040449840e400001100050178000107007081c85070784d807007481e02e8481b00c21646641000c281031403821041c1c000d08150441c00e04220510707040d0000052001d002c1800081c0c880a08100e22404000095041b1058402d008125544290ba034010300c90f141018115480d010b0280c1108190000d22501c050310114800c076140c00901c545804011030300c13043c5510100c003c5500300e45d03410b0030703050382e40d8000d03da00021080074588510709401032a00b958180520700085510001615001e002088191500158040c54007a569200e40800b280c070a80002407241e44146002c00015140c0c00240c042200b5801c0b40d200e00c03002c0c0b001c00720210384171190040500056001040444514488000182c10b0590300e02409180e1091614103200e890700c43c024100c840440010351107031a41006420030100307100460314808922040e940041c0232169640344c032802103034000c9102c41058010404080748100c00b400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715968588 1250 715967338 715967363
    0x90803040804031b0305210f0a260103030c06020702040212150301060e040c1e080706030902330913140612030c03272110020412060c020307 62
    0x9001a4070ba000c2c0c8421644202c10092021403000e030a40c00c8400c0b250483d01504d20700319221100c00c030140071000300110400e82007082485140c9860301411120701c055032020b1801500725107403800000003d911001c071b954080010400a9880083d00c80442c1d8088009600d407842d41c03000c0303070203070040228409017184e14004010000d5000d01a8844070f5600320000d2000c80e5a41442c0d080103170080d034020706240070f000e4042c4000800c4007503a01d5040b02e0361600920b039035998107413103040c8803080d00010006526007241206503d01510450041c25002610000044202044100880c82c60b0028442e110000c01c01d000c107982c61810208030401640420710401072000c03000d441880040302d01070310821018000750314050000007a608564800c03070040d427074185000443da0a25000e031a107103a2104000740c004c8002d840d00c0c080440715508640850340d0140362990b401d802d1035110348014001c10301c140b01c204030b024942515446017540000300090304200f00b6030700701d05601c80d040c0090704929800c0e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715969838 1250 715968588 715968593
    0x21503090705044b0b0d02060309030c071217040e04030c0501110f030412020304052d0d20061306030e03070f05100b01020c130e0f07081b040b0307030b0a09080304 72
    0x13640c48011aa100303802800c80b600521100c01260040f41455800c03101000741c640041c20480011a00a140f40040342e041880c2c070490f06103488400c0d0032843e00d07184c03400d030210300304241190340994540407580c0d41800c16003000c032504441c0e00010400782c100b050314200e050500000b03502000e1900c0ea0040290307541c4803040b00c000c1c8658000d03502200c2c10b10180715100d200f0791000c000d9a040d81c0004121103c0010a81c0c0d211700c0519044614504410103c6104060713075131203900710b03000a403064203c2c140c03144100c102150b0f8010240701040c0501e40c204102e21000c1c0c55480c0740b03002d40c0c0c5241000501e00c0d000f02d10192660048200041240390342820303140a026000a00449240301040700b0700c000e801c5100126110b150f541d90050b0401c880034071403080d004050f0411000040c0c043c0841d4241c0c13104100341860402254450f02ca2500701e0540b0b0b90703090400c111800001c203404d903800e00205c0600070110341c3d901c1d0140b0010b00248504c50106241d00d1440d04050310650708018030076203a043c80d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715971088 1250 715969838 715969931
    0x5090106030c050303070803061216091d0a0203030405040c05120a150b13050906011e050a0f09030506151918060501080f010311010c08040905010302150309070504 72
    0x24082612003035807010b000140303454000201d0311000e90288445046880e48014014a403104120400322401800740b49503154052181030801444085070114007000502d550395403c204015510000d508000300705c40142e20300000b15000c881c0182d4000a03000c51105040364180034618040380540ba680042c0300ca02001500314030803240caa80c04c4a07890303684d5104080e40c14803500c4840b200d0401c103020b0412440c90b007580340710ba20140604181e040400300e40348009403030a022aa85001c2000407546410442d4082c424944500e002d080254206095480f429070303403080140b003070004108811030540395860b40b40c6484240081d104424010300e88030a528a81400b1508900d51503525245d0006200e40c8104159405070180c9070034001c099003161980111809040f50311030602820003860070001300350340300130001001075260024181d41184100060084c0c0f800b8103080a60044c014400080d83c0407440f2011100c003103a0001c1e02d60300c5005074038001140d00d5100110581d004c185404180c984 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715972338 1250 715971088 715971101
    0x6040501050c0c100906020c2505030c0d06240602030a02011401061d010e12010518120a080402010e0d0b0a0c0212040302010e06070f03050a0809030301050d0f060609050901 76
    0x150000340001d42d5030341d01e0214280144010101e06038840c0440c0d080d02002640011070041c0545405840c14030305403031452803c150f0486507001c60000220880868009101b4803014100450140440740054800207030f00800c42c1102400700b0355601280c641448890800715400e0351140c501c62205030340e480001c1c1d106e0304648001e1000d9402c14042c940354070310b0483c206040e166945c5071030400018014010540801c0c0301035481c140000290181102e54030010190b942c0804007002160a00c1d03c02581c0020110700120580d040e48807100d4940d002c000741040e2800d0403182d181010305039607a030004a40d420f40c3d0681c0ba03034104a0301410401484280c000151190030401d0051005400c20101248c0e951407883c00c00d50409824001400150b110b000c205003001c10003011141444800d444820205258040c100c010417130010b0b41080e21034202100c2c079404400c02c400307142150b1500b03000c01c0d003100441100500da000295008010001c20390300500103030980a80030030161410030034182c02800d0b03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715973588 1250 715972338 715972343
    0x303050c0d02160608042303040801060e011d070306051507060c1e180f060503040b1e130203011e0b011103031b0306011b2402030702060f10050a080604 67
    0x1c0d031420a500c01d000045618034a0841c143c0b1000c0c07030b07103840011119103502400031a43c15155144003500001d1884c0c10a5034402e450000e1582d407490201043e00311801a80000c110209403001045040008009200b11034404801401a640c070248110b004107050307001243d00c049260041c0922603a410090848503204000410030001c03071100507502c028a82044116214a68100510191084aa0000c031903510040001010744540b65000403503001e0300060000b840200c1001300784181400d04030b42080c44549148000308090741901900310004208001c80c0d090040d861003152802d50145a420060012610302400c18103100c801500320040750f240041c40d911018200c00c0307030110450380100700302400c0c5da0052201d6402e40305240c000420180c1403161142d00a5040309525514040c668420481e07407510b001412031260000080440b403103440c0b8410710420214640026000c0e070040610b0300303c0301643c0d03034514000030f840e52250800c5400001e920f4002440e00c60014040d4012817 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715974838 1250 715973588 715973593
    0x81306080a11070209041511040905040314040b0403390302090a0c12050c090603010b030a1104030b07080a020c0f150c03074a010f09060e1e04060303050c 68
    0x1c400e100c2e101c030b0a0180e000c004e54001c803640040703000110b03403001c60040442c02050105a200c182420010645c0282d440181642d403503004000400d46e00005254105c0f014440c7c85003000d04180202c5082c0c00b5602004002050305040c0c240e030f15540508540c046240140f0f80002109010b07801200700041c0c0c88105d000d51885404107506130264050141640c0242d529080c05010708440d2402814015280704560001048260119284d0700000c5020381071004e200c03a81ea041c2001403104440468100300e00c0b0541c140001d0000407212482c440c0c0101c9a45480502c6803989180b00000b03120b8091454542d100d9003001048a0802040c0c48003075184002116440b0758420000046500c000c44000300054402c1c8480702d164250200300300341c0382c03c0c901c144001c41030513920f40303005800f4942004e006580341d01c413100d074080d80c0c4045c84803d0030305149081800305103040c0c0e02902101103004404c1c4512442400d01d10308000f80d03000c00d1601400140244196079031303810701902030703485240f40c01240e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715976088 1250 715974838 715974851
    0x16112803020f0c130f0e061815160305151f030b0a05030c011d0d11091312050901121404020108090a020d1410090c08010e0127081306080a 61
    0x201c42c04280310071034503000707485071840303000540ba1080141840d480e1600101d81e200240035030910100851072040c0300c0b46185002001c0031110702442c0021181d00c3c0380c4140035080030040c40c002d15101080007000c02d8200850640c40d0381c540c5008441440e5540398002c2545240c4c0a88080309023603826060001780ca04110b00319104090281c12242806156015031095410885a51040c1c0000814403020001e0940300d81f075030300000e004024034800c207451440d18444a00a180b809044040d00320519500003550760f0748560764042c0d10002c01c50345100344100800e040003164003420700079204014024041054000441c003030750500c902030b102680060020b0000940f06140021400c1520340c0081031405001c4d070390364403c03072148101340741c00340e941c05803485506c07a00e4068050190005e1081c0e1910502c1410240c0c0c183c2181c0d07a40300b41e4044c2d681041e4103014200b000c2c0340c259051110400340c14001c500ba82c1840121403050201800b16044005000140b0035800b244c4140580c21076041409032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715977338 1250 715976088 715976113
    0x5010f0e1807050a0e04060f031b0308180406090207021014120f0a0608120306040f180b01050f01050a3609150e0f0a0905120c0f010e061611280302 65
    0x88841c2070280c0340b923205d01d204003440417a0840c003078500341c1c222001d50365040d1a100d0365042600e41100c00c4034240f103000e803415160785181034000c0a014001c02d0104506150302500080d0705030340700030b4a00040c080c1c500f5444002c1d80d4444100c40d040a02081ea40200d81010307010801170303103011240b40541510703001003c00c2e10350700821400300241e80103600904584402080000901030b01600c1c0e4541e60340c0300c03441c0c03100c0c90140703e419009600480340541c0642c0343c0800d2140343c9000302555810080c080001129894000b001e01c2c004158001000c04d448007600310401d503000c013000014480c18100c1d14009620406500701c511001000396041c3c0396140c2e2044d200d0144070b001c1d00e42480890028000460103203582d40b00c3c2400c14022400c40d19110303034258010b0805e501080c49440355800c10b81165007a0f40c001d004e03002c1c100e0405002440286000f41201d54104400f0810f50200200403542c1c1c0c0440d5000c00c00068844421650300c1c50030241c1101e4541c1e0340b6a00700e4110091300458109040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715978588 1250 715977338 715977341
    0x40f05250f120c1502030405040f0903120b03100203151c030905061e0a0c060524090601020309010f02030c010c2f06010504090c0306140f1005010f0e1807050a0e04 72
    0x5243d07220500303035190740c00c1c4107407074280c2c081c0c5106a80440c40305101c00901c40e900c600841e0b00c0d210030198005201106420014240100394910f030380c09600304503121026403400980c9400d03c5a40c50001622900c500500c010901402915030354004028a240079180c0d460003040c030b42d241e2190701c400000e03a80e10028048907002d45401410000740004041ca2000101340081810150320b2405038118107841d9107180c21030b103040e10010301807240c10b103210007101c038015850040068220740540451500713400003562403003403200050412010030b00300041d02e03000700250303a904003c0c40c1c02440241000e2400805130f0f01a1003086500415000e00d1050f48100380150395280700c800c0d0080d08041e0309200c140005402882c3c42110580b41440c000404a0058072031140480b01801c85248942403d1625002d04a4068a81c0350395801e150000c1000b603801c00c8056480d44141e00f0b00c01d07440440880003801840c01814940c103406001c80230090940d0307200c401804041429294055485104000d200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715979838 1250 715978588 715978619
    0x2120108120a030903050d15090b0103022d19030903080c03040f020f1212031602030a0c0201080a061206090b0115020703021e030706050901090b03060108040f05250f 73
    0x18808400c00002d00040d120381c1120241501a0410703c1ca000b40391000e4108698a108003c10309480070342c018403120110707018002002e0002d284c00e60a00d1010109840842d5010b079045251502001038080d00011000035500071812640c2070580082843c1c0c0082e01500f0040c0046001900c018001049003282400783c81c080c640020303500c5202c0c00c3c6c0390b09110822005210490b132041c444541000719100411040829041140580d40ca03803c00001c5941905004841c14082d90410320507d0300307882d400f298680c1029024a0441115111a0702600091000d9040b103900341420280700010b010254000d508810b1041280c11640d82c1e0300c04945500720300c400414401a040740804002502d080e40d200d00f1514520500080c102442e0000070346001d900e07a01500c0440e4001c600764501e5038010b0a590010560300c0344540c80e51a11000082c014040200001e01e00040d541c0390b5000e1007400c0103101403129040f00d00340300b45400c0c0c0c90340c40c3c06100244200718803d8800310001c10119400030000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715981088 1250 715979838 715979863
    0x906110a02060118181113091a07122f0307051608070602191701180e250303020601060801060507031107030506150a05030a031b03021c0c210516030504031502120108 73
    0x1d00d00c01e401003a050002009c09810b807003c0081d248038402c880805403003050350000b03490300c0c1e00c0107a01b0902c5400c408000903002c05204144140100840c09800000300c0d41b030302212580c03001300e450580c84c1441d1140180e0030090000c034408580021130340d403898001d02d1880f1107625902d5403075045c1c08149103050802d0107810340481d013501190220040f1a0402180482840c0544008000c640c156500c6a140e100d0b40c500301c40c40e4442d040003416010300c01ea501525451501c8110b540c10000040c01c2c500c00e29000608108200e4210103000310b0922610b07015640c03003820f0361014100520b01902c010580036a0502c5429601000551460006904461244e145d15110108640044001100c000d070500960560141c1504005801100c24400001e1003441e168400094103900b440000c144607031980c410841c0c800088849115040019511400300d612a8954041098a01154540100ea1005150074180c0b001d55240c1d00ea640c000c1d0084440152030521144e0b0f030f4401030b550b030341e0707610002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715982338 1250 715981088 715981103
    0x1e030f050912191e0e1009150c020303120a0608010f3e0a0206070e100e09270d020d02070f0b07031709010906110a0206011818111309 59
    0x240c000d100c0001004101c007200f141800c010301c41001d4214240d14403506510000a080c40c921254a45021554644000500e1620781c812a041201200706800d003541c4030024401d505480c4000c55508008641380109411544c0c2c5450601400c454050a400d005214841d401d2002181d034004c641d101d00d142c2c0d001c111801e42c1c00c402104c60b070f83c8020150a055a861040542180030f05044002c000f80f1039041a03600802c080c0c0f0784081d0043c460401c042c0076520031a003102c0d0800b621580000c40034102c1c40101c84c84586601c81241418504104a143c101d1111040b04444030128003c1072444816180b070b001d990306c500e42400d04036142c0740c180c050805201c041c0718090141c110014007070440d0b07503c24280260260000311210803581812584002070307a440342c08201c2004600c0c006d038500d4034000881c460800c0340840c80652611014080c038881940f04042c6800c2410094001d0a0132038007081d80c03121a00c016003021040086400c0096005623600100050b2a140c28801c2c00340c030380e802000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715983588 1250 715982338 715982347
    0xc0703080615160f0629041d0106080715140f070602040509240411071115070f061811190b0f070201030e06090c101e030f050912 57
    0x400610394050140c0c2810002d0a000c841101070390a00300d100190702a600300c800e1802c051400c201900c40d2001c1000304031000550358200e00340c07000c10444030703104203c0d00402d180805071010504500702c411003a8030ba6080c028000303940300c0c01094030415142884a410500c03a9680b50a540401e460280d11500201c108640c4510100b108083c0200603c20b280243c9000c0e5a8400290380b403805031411855a4191030035000c007880c4440c1c0c0281d03110021f4034280b000c3c002e5030013030307541900881c80007814021041c0140010b82c0e0f01c01e200c0800808480c280280c4070b051600b414950040089404c41d101498060380a494000c0e00c40c840491742e901408128402c01240c0a10881042480940c3c0c0f09415148005c615040c40c0f0010700b240c462054046620b07103165000042c01e0322120346266590340c0101061241c0600302186522044c0003d40b035000c0c4a50360240119400211403840c0714908844508042445900d608180345070b050030f102c180006e844020080d501d03103d410142c040c40e40e00802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715984838 1250 715983588 715983601
    0x150e040b090319090801231503011e02270d061e05011401020c150d150e0403050a080114030d030f0609090f0303110408030304020d06020f0d0905060c070308 69
    0xc5940e60180e00da0041da0700b07220750070a0b03030002c0209025503100410320000b028054001c0c240b04418005403055082d492161200c1507144074103202408680000c08060b403c2c0e00b00b40c0702504a01303205a500404080c081c40095011030007900b050300b45040c0d180060700701590f20b8100e10b0341503045400c000c1842101510075a07825000b05810062407142480c0b5044a000110492240900926400f0640704854502000080c01c004a0800940c41803240409004501064500741d5011205004000518407684500540580039903449102c64403000c00402040641c0f00340648100046038032220f50903600e9004401949d64880034154040c0e109541e4502842d109403c855040d460b40d49001070003a4590083c0c00039103040640c07c0c0c0c0c1181c090030200080580c18401d550f400704000c001d01e0b0030b186c00d00d203c0c10346034440900040c1c0309103c0c410140c0c041c01241d50403140d0740102c00000a6550000041e0000a03044032142610706019400001e20080606070840301da05e5450380d2040b0540d40c1d0403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715986088 1250 715984838 715984853
    0x40b10120b01060c11091503071a0d0c0306150909051303020a0b04110d0311060c030106050a0e03010609050112060c11030a200607090f1a09040203071101020f0706150e04 75
    0x4c41080d1024050101d455500d83c03140341d0468083c407000c59110b041c940c034020526150802c01d40c020041d180e0240880e840025054060f03581c0c40c0d030703a140c000c55a000f0450046003c1c02190300603140704050b1203203680b52641c01042c0481111820b6400380702a640b0450540d0b520f03281000050b015030000b1015400290034070a1651b8414410151401250300b200042072001680410440c08244d1840411410b5001004825880990341c00300e2480e41d814420024164051802c054080c0a0a0103180c4849c4c0c0c0e081d04144060b15a1541c2040a0342c0e4504140e042c400c58139030b05030750300c2d0718003100d1000482c03081031f2080d01c1d50000d000840c81c1c07480694044030000010f030a82110042c0e41100c0b000688070030302440340038031002d07030354000300a050400721001481164090403e81c41d601c040c004094038100d0a80d030056800300e40c01a126501d80400340c910485045060069520001c3d58455041300c24018060035070044404101034004c0c0950502c8541040c0547c00700581810001400103026 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715987338 1250 715986088 715986107
    0x60706060801061212050720120d03020a08090601050d20041107060506040603023307050a0320060403140714010c0210090f08090d0b0106200a030e041a09040b10120b0106 75
    0xd00701d0843c0940444d4222b040180400c0c0310b6001071b4002405c40c1d441581301000d20780001c440c602610143d450300001840200380004001c00e10b2400c0120100c1c5010b04507000e0310360081c0038205002c201c914811a1030542e11070a03007142c003145050080f401c40d060520903141074950161110008a54400708418401c080b100503192410703d004020030344810220240084030b00c0380000f00311032807041c82c000d0300002403043c0c08801031890301001d424a020004034190001c0e050f00380284400340c0929070520320300c10303c800a41034480728082000000710550050800405550a40d840c2d589252078883c00e85002107070140245110800180100300d00000414100400801d440141200c644d1180c0050400f6400318000c903510b21643c01c5904540e5545c07541080c0c42c0e00160100303407059034024100c40c0e0619400c0b0300442c3e0f40c2e00b10240e0051074981c1040d480e000240702001078545813418291121048460042030034a010000441c42e003040c043e4400a80c2c40040050036a003081d03000c9650005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715988588 1250 715987338 715987403
    0xb0d1719171f03080706020903070501210504021c240605012007180507080a051323070306051602030406050a08100512060906070509030c0607060608010612120507 72
    0x480c0d0b2001000400000c0106401e900ca0000541c80c0d83e50741f0105420107041e9400541403114101c045c04400c0450080519140c144100004a50300c03540007140d040211a00c5500c01030801510000078050000341c044c85609a580d07205243c400ca110301601178400a115090100700d220a003003424003201120581c015a594084504172503440d040c400e40c2500b908990404140e8403420701800552107402590b001070341840510840c14001343c0e03103c607011501009449012020700000c01c40c44400080007104040703804440c415074403030030709000400c0305407030350400420319a0202240a00100c181c408031041c50f100e1500b04120400103540000c80140038014800c08064041303203d40e0f980040390000c0c40c0301c40c01400c003450104500c81c036204000d0824800c1c4802400100d0003540c000444117003032842500c2840d1a20000e18258000e4689900003105239400c101c00840ca000c071204400783c20038024558031800182040080d586441178507030190039008000d00054816055800300c010441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715989838 1250 715988588 715988641
    0x1b050702040f0e011d0c0d020f100210020f0406080609010e0711070504020417011d06180c030f0a1704030305090114120106081f0b0405040b0d171917 66
    0x81c072030f030612801c40d280078008681c01c441ca06803100c6031000030410f140b04040f0944845140f81129000a00444100c600c2941710710100d0701d02000741342c130034841010700003030404065454041496a600468001d03006140c0021503241c0001c01c180707040c12105040786c41c02c18801c55035860b5107004440211b46a24226900d1040b480300140b1502d07544020710041c90b012840300040d10110410500303480e00403a548460f48101001040c91303420115450350021084032126070f04651800166042850005d02c1c183e16001c0c40c1c000d4920070802095502c0c04070311a00d51056200c204100f03d203e140664040900010340c2030081c8415540100c51055204907500700c0310b030803c8000184d500f0710310001d800200c0060076940910544a050144901d04006980074400d100da041c01c0c60850749004034882c06102d662181244800f58070b03803d90760264242c0106550701c6110180925074074540c072a5540010410301414844a55407282a40b85a01d5941e00303003903501a00c41c07002c07121061480c02d03099100d50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715991088 1250 715989838 715989851
    0x3060904140708100f05072c060d060f0b0304030206061005040302090a140709030b0c0d1b020c0906041b141c0b0a051f05031b1204061b050702040f 65
    0x8680c20072402c1e000b80b55010040c01e204c000300807013a0640c2d05031040d25803518200700a00103a0b9400000d42244442d60301c1c121210300c80902d60380e00209005411142d004000000c0c60138003500c1640040d0151002d6042c540f00c00f50390343c2d55108243c84101d0b00a00160841c201003000c6207040c0142a4980c280c0f8640b450815440b600092101007007550441d5100c5d658002d440c0303540888800d9654000000d041240c400c03891602d5944051030024400d008140c0005180404580c066001d02034030540200182c2202c503054901075500d0060010040c85200000c1c001a598075180c0240c1440005e052204424444036031400e86049084441400c0292828442d1100200b6aa440b0b030a035880880700205440040784144261410140c20480c05643c000c5500303010004401540300c0d04820600c0c1c030f540c1c0c5c0c1c1c0d12030780d00301000c80e41880d43d003024480015901d2910210340c600310780241c2c02400c0800c104032720a14012855500350468802041051013100050300d050782c0300410b01d1000140c0884d02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715992338 1250 715991088 715991123
    0xd05070b090a0b0f0609090601051e060c034e1806150a08030f040b0a02010905011407120b0a21020d14070f05060306060d090b0f060f0603040803060904 67
    0x2400c1e801c4a01303c41c15040c3d1400c001c920300c0d0224283e0380083c12100502240d504120110710031b0341c00e00612000c50f4030001e0341c120b1340b40c40d4881100e0394200603500342da88407140b4545402851240401a940c54000c03002d0b03408a40e000c0d40000a8100d00010020119142c00c0512020744030f4020303c3d6402403081c0d087d050045820501031507210f0321000300d20001506e00c1c1410000d05003150741064400e07920a00090190b034614038100c80a449000021f1900c1e403162440403400341c40c2c1110001c145500b044200e40d00e4510504105004501c6c80e22041c0303a4410389250304040303e0b02e10034201d0f03102e100e4610404c1101403900300c51880541c4011025003191264000c12441c180c031000031541d00440203840400c05006002100c0a45902c0b08840b455625240008480b40000f500e0386100b800700242c404141c1c1d2480c2d125000c4140e0101509015184c070340c145000c6444103d5109007e204d5801803800c0038580301040f40d04c2150f000b070744181075031220740a0008120005100b12070384481c10900740c0c0d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715993588 1250 715992338 715992353
    0x25050a12231c0b040516030c050708162102071502031801050d0b03030310080111040f0b0a0903120807090510140f070507031202010b0d02180408130b07020907020d05070b090a 77
    0x2240003100c01c00e0044e640a428024101c40f15106108100227060020f080002c62032030483d400000341440c4052240d2840c00d2103e00c13001060010031300249c3c0008404502600811100100c66010144004075103482c030050741c480c407c5051030341c00c0804c1c00511004960107030004e8034064041500c00540b5807004d901091442d4001d80f1800c4c122003540c2c208100c0b44c0300074010115580c1d003400c201410315103402d00c14159007519000340350380100086950032003d03206140d41d000554121290146110030100f005d014130405039101000600d005402103103a040069200450a4103031f81c030342030b04944c0340003584890b420040020b42c451b4020402240410310030003042010354060140003a25100c501e0000c0d00311000c402210340100c859a0010000d0390780e0403022120003070b10716013440c1da0390f8991034517002c548a010403ca003620892640070030340750181000f601c0302a100b5585032050303480d890016607a41c142c079440403000900812038240056102040c058104401c0011500c0315407040e81e8601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715994838 1250 715993588 715993591
    0x312091212040b07030b182d060a0801060f09020f07021207060e1e09040507030b070c0c0e01081c03060b0f1207031125050a12231c0b0405 61
    0x36007030000248018890700c1880550010200c2c00d080154103440404034080905c10032076810101c0e03c050001d490883d0000b283e0702c4000b0000405980081c0071144135030002815108507014080c589400b2840c24030522901098858a4402141031403518084c0340282d817044188003400708081c050341c80140c680304407079035202c840c590160211030305024006001c5034003030400074406c011022402c182154440300380c80010030182d4160b0301d565610f003003082c41c04e48a07900051224900c80108840a81d021a00186051040003010f41d110ba031201c0500851900303004060054014417060b420000d45a13564080301c1d0034600700441daa42e9920700840c44d030740200012940b80c64001680300000381c104103006502900a081c20081e450032159510100c1c01070044101400300d4103502610950204529412210b0303100301151000401807400081c0346416002d1040440c1c40040c82013500500c1c2e43e103a0010080150590f803c02c8c407000c0741036621001c1c810100c84e6003617458100d0100e6841b80e0040c9c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715996088 1250 715994838 715994857
    0x30d02030c09100f0f0f05070f0c053316170301030606090e0705040e010e0f03120919080304031103031f050114070609020a12110a050d0503120912 65
    0x164494400d102805402c040491205041013060a0112802504040b4804c0c024010746040410710342d00030019075051194580c00362140030035220032030810181c1c00d100b0007078480a844007900c25504180e0f62103110908801c4015603107070924032414881010011b0f110307081c50200485600c0401e43ca031980f500d030707040070340100c0d5000000041c0140180741c0194070080054030741c10020840c4401d079460f2101581e0140e288225102c1c000003600180075003207040200000703820356031b00f0346052030f2581c6c1e280c1c030000c0c0c40c65034441c2590000d068008040340700003100201c0341e1011000c152954450744c5d6944003c00460901440c00e5465001088c100082c40c0b01d007a9061450b02e21444880076072404403031380d40c0058100100390b800b000301803807050191042c095011101203000ca0b1184000b0b00c0800d1aa00414000c04060b0705100c1400500d5504100c06401950400c03021070310744041c003280080c850800741460340100b0419103200383c07849803194018495000c3d62900c540c0c4007a42c400a50060580c0e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715997338 1250 715996088 715996111
    0x20316050703171206010f0e1e0a0509010501021509101a1807021009050a050109080409060f030b0606090a0f0902130806040515100302090f011d27030d0203 69
    0xd2040010060b403807030309002c00022050400004c0461000400e80041107181001848044600300318002e1414070300c00407000b8048260455005d04c820400d10340a50450f10903800b0403000145400c10a03d030714140c0c0c20681c054500403502840b03c4140b100060000c00d0684100d012011f44001c031707807181c0714803e0060101c2885401e0164100840300c19403000d0801c0d444007080520200720f40000394643c0412031140e0108801e0f0003410244c0c105252004054095420507142c4c100304840013006002b500c25240f410040c0603240e07100c504d07a808842c080149800c99a6000c102589000d201a15200b44002c2400c00900c2d211201c0a031800b8043e40510310690b000302d502204481342e903088102604144004101e10f18190311200d60354003c010038100804201c80125800c01d101d84c0c564806075401402012050400c0104020a03020910400c41790700350700c40c0d002028041200019000d000b00241100b02210242c1c10200080752110f0740c052a44001c00005144244a001031352041076408403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715998588 1250 715997338 715997353
    0x2070803040b042f030d0e0901060c03020703200117160503060d02040615030608150601050c030f040b070b0105040902012003210403031401080a030e150d090302070b040b040308030702031605 84
    0x14107203041c11080c6c1120900034004204400c9460304010749046600700e1a012900054900b026420301805070400381035802c180c03114002424102c0c1c60302d52502d1080e030341d8040908024004240c9280203469520220b4500e643e59042ca6215101554004000419203503200c2001d40c009000c4805640c040e5000004004004542c0c5070140f040a00810201010b4030b006500403040c5200344100034440f506101010a03e48a030b181c0400c25101d50340c001c09070256840340c840f40c4040385900041d6080307801d106404004615824a03019441c21a94103031141240c0c1c0e0303c200182803442c6a0040034400c1e43c40280180f0500e15103401201600c00c41134000300d0101d0a0605001301601d41603c3d90700030b84005180100140d04002407881b40103501031a29440c800c1520000550000e11000801114000400c01040d2003520384d1100b42603901c82d03001c41e040240d4800ba40d0889000d103100341c4120040134001000442c1c3d800008651207046481602d140800c4121055842010554281c03042c0e84000c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715999838 1250 715998588 715998683
    0x1081005031501320603100e01330203180301020c24060409020114160b090f0c120703062f0a090e0c034605010902070803040b04 57
    0x8001c3d5410401c4800c014001c04103912000d13400500d640c0c4c2c200d0140200000150340e031508030101c0307005400e1100c006400c55035641c2c6058840490b040c205c840048003420840441a010134103040c50084d20b40195051002c136240d082680c0106408441d019502044010360381d0b1000c2c04261140340e042c10074504a1840501d09401507070f40201814007a5140c00c1d0208050f0b030304035105085054074a42101d03030750f0540c44e128082c0ba0910100049ca11200d40c402e1200d4081c01080c400a5015050220b501e11600c50007048201e00281c2f81040964000d01c00500215085810840c26001500c0c100c0b0301c8010000e005011000c010300e518001d10b8030205400d0003075544806818010031149103d202c482c2000344003050b2038031010f080d03514500580b00b8005d40c00f440c0c440c3d5101e111400c09070540a18074420355881c961400300080582da080c80d040010a801666109a0700a95009081982150740d943e40d440300f030070006401900c40324445020151039212075031040301c07101806482d41c0602000712 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716001088 1250 715999838 715999859
    0x30f020307180f0602120309070f0311040f0b012f0a1b270209040e10241503021b12090f0418060f0e03130302010905060c0c01081005031501 62
    0x143c000c41120700c1d003010200213040c0d0000348002e8218040c00607a0390313600c031800c1c03491510009521030076110080c414004207108500f41340ca52a110140c900341700c4155a0030524045038001003882d0b0120740140b202840c20702c2c08154869140030240741040e030550078881014545100c1c644200c1d00c0807046c0c40400c0f01940e5200d6044010411054020314140d044d80e841c1c2a0072099a020550041e408114801d90783c2d00ca8000010380d070b4200c07090b52000070040c030016001c0d040340c45c441ca4050150700e40c40381034100c3d806681d0701115410003801127072252140302100698005a82c40c2004100010252460342c03050150415440040c01035a523200c0000c014004190f000c040c8091196103000c50746007503110000940c0711000d6000314001020145444054002c000003030341401e0910010604030150112a40c0308402d8038001d88a150303c4599820421101e4441c40c9240a10781e00300b030010f030b803007940500d81854010006c5d01d0b020741e603a519440481c3c54510042031012844d110300300104000c0901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716002338 1250 716001088 716001137
    0x30f01060509040f1b110d0804020f0619120b030321070216080f061012020906040213030c1409060a03060e0309150a11161206020f070b04120504051807030f020307 72
    0x1070304080c5c16081d01030039001d0203231500200003902a181d10900a18580d4503041164900809441c0b40d0030703012402e5200030010268a40400000c61901c3c88a03184e40c03030000182c0c0c0c40e0801c1c1c3c0e402a411200700d920a51504140038080b0029882500a50a0002d400701603d1001e00100320041180315049110309103010030152a4500301c40c04d6000901c6009082901803459603010303a032003415901c40901240c02480341001500c0704410b0120040200101541000704032500400d0240200d000c2e00f0030094980c8054500c0c95116100c01e40070400980340d60481d41407111100145ca007004801c4010400003140150b0094040c0400944150029000198001491484402440c903100419030300039845602d40111031003020015404000c0202c0c40d012030b610340b078a003082180c0300c542918049d0f40301034050710101c500000c1101c106220b18440c1080e10100c1341e000b0403090228a1030074004010703e50140400c010951101c0784401154018001076008880329a0b90200b161001c40980120360300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716003588 1250 716002338 716002367
    0x10c0204061a071101090f36020705010e010c0c1704030b0c04061e050d0b04020d0c05210f150f0307061e030e0303070f0507050a26030f01060509040f1b 67
    0x440039052281c0c10821f101002a14000c0079054031a91802802e1591402101c03041050502812810701c955601358016080c05482000203003c085108002c00c1e007030310a175660090009049010280208191080141c14a00d084205920301500c2e500c0b08401ca210803900c030800c61500003010400161700004541c1d5900e8000700c4084070b03800c003500081003481080d01c4030b400140c84800303000d4182d9039a03048641c001d0b085c1100b00540e04d00b10303e02804036007080031500009106a030402000600d460446071103030011030440c2d10782c0d9685400c0c2140340c02d0381c0b641441d000b90003032403101c2468508210382c0024043c1a00c0e0b01384030704813030400449070344214600041094140044024801000030a0740c0d0041c1c1c1c03600b090200d5407012035040305c20f40248080a081380c400d00001800b070007022400080b80d0880c07511940b0f030404040d1f00b2600c1d10f100503102c10381c403080b191004008051094015100c1000018404102900140c0f81802943d0030040c126001c03001108158800d0350300030b69044000231 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716004838 1250 716003588 716003597
    0x1e0614040c170a080307141911030a090312090509040c0f1e090e031317120403050a020f0a090f020309010b031c0503190f02090111120702010c0204061a071101 70
    0x503141d4400c6902e0384609400108211340200100c0d64203030168480010320b03a880100740c1e4075401c10580b200c4040410300b4151003c02c2d0a000141e0602174040216501d880d1152a0680041e14564500040e003018508040070099850804a0169101410607025038050080c60754104e00380074100035140500d9100c1036040443c802400c629104203d408400c0719841000000d809603034028041c10340c0700c0c2041c50199000415400b040c940b0442c0700320f5440310b04140c1129401503c1414451a92040e17000241040e840483c0c17600c018a03203408840032019026114540c4a40d0706d0542409580b80c1c80c0440c10340c650084100800d01809200b080d00041c0304500514a0404104022108110051458080000000c0040c0841000134020801903074111810406025a030303e0390f00c000e41203103040d640050801c0441c940b20f0940010342d1422002c51a1440c3d00d00b020b5030740191907900008030200e81040d01d4090008180800c8494421480410000d2070b544003802d2500609000041d00d0700c0d41400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716006088 1250 716004838 716004869
    0xa0f02011a06070c031415060a030312050a06051c051002090a06050a0201091e1a010e0c09040e06040b040c090c080103060902030a050d02100c1106041e0614040c 71
    0xe00700314055020558080e42d401ea502c4802d403c02110188494001402d502c1083c0100718500e1400200018001012030052006e80c8485c02000308071032040c40084e00007102c0e202e0303190a800c000e0b40460741202d00400005102903440001c141e040302000f200c11444034074442e1240500c0f03003d002c1e900c14200c60382030171490201c82c207000803041c20ba54010041085070104511245500035417044041c0c9030000b0b00c0019000703080c0200c20440a418400722007402c0c13402030780310585544900301c50691304500b003845030f6030ba04c0805400c500d40042413100c0e07115840700070003d0800003d0112030301503806403588200c186800d05101d00b44291680c0b10050a52414410401c020760150b005415613502c130401041d488030500000e807415949060103401ca0007614030124005400003034180d003c0810142c280b042e00003107042034600701e1010082c0c080642050001030300040c000030340c520760460031518650702ca075000c1c0c80e508102c5d9200190f0005004a810900003444020012b407002001d03074500d4410f14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716007194 1106 716006088 716006111
    0x3040c0b0c0c0f041407031505040f0c02060c0703020606042a0807030f1401031b030b0a0203150f0d15060b0c0a0b01060c050a080d1509020a0f0201 65
    0x180b0b01c84030b58044682454018001c02c00138100741031085d50b8070414103801504464060441e21500b000703001c07c080d40c484c410000c03074140007500010740d41200140070340b51442c0901700400a500911a1000090b4005225503000006403004512030040301042100300521181c20005018400701c4101425840414a03110711550f6034144641c614007015481101d001201119000110a0040c40820b07200d52180c4050180d004100b03002c035640352101002c2500c2581d20b074410b240c0000074040c51001200241e0b150719805c44604184130299000218100b40c2094000c11031842c01180d0b0000081503402000106441c51625036a5144940d000ba01c403203009030102c0d59010110300200d192449200c85035080c3d980003004041c0010140c403102c160b50070003101c04950f1174442d000d541102d640c0703030380c80b1005104400340562500c0c80c1d0503015004034000c480c02070031a031400b20315011 = true := by decide +kernel

theorem cover : BRFrame.Cov 715827338 716007194 := by
  have h0 := BRFrame.cov_init 715827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 715827338 ≤ n) (h2 : n < 716007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
