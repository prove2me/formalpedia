-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4722
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:31:38.242971+00:00
-- url     : https://prove2.me/submissions/ec99ddec-89d3-478b-94a6-3154167491de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 849100719 ≤ n < 849280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 849101969 1250 849100719 849100739
    0x20d090b240a14101e050a120522110d03030e1902090a0e0c100f1215030b09120c0618030307050316110d050403140601080c0607150606090519 63
    0x140140c54044e0030000c0ca480720040c040c0400320784480058840d100313000b10220000302a5804000010041a019010b03411302881e41e2103454854680c0e0403840200c030100440440485440e40e10865035005040d10400b0503889440c901200301e40f090300c000c1008200080083e0401800341810800380c440c400314140582d07074009074a9003281c000b00c00040d01c110604001414095030060241d000f0b00d0703000b166566154841394a06c0d070007a0303941d607400e2009a18a00c2c2c00681e0401c511142d182100407030180b01140c600c0c0e88194001c800c2d641102d4000444c1c221411060300882903602840e04603e0400030b20078201064404014180341c082c5203586000703100a000ca00015040301c01c0300881d10322050a0038001c00700036880c00c00c00c004032000d904020794010080d9015000c00c4a03200610400c541d445c00c0005040d80c144daa00304060110102c0010500c04241c0000005403804d00341d0f0060300305440c2c028415440038151550300c1c004068102018000f40034200e42d030a15030540d100c00e0400400b800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 849103219 1250 849101969 849101999
    0x1b0302030f0f0c130603301107060302130302041a0a080c01050a0c020f031f0f0b060403170409060b19050c0607080a1410030c120503030a020d090b240a 67
    0x20031103001600c401c0c2e00d0a2800100b0260700021f206994080350706202007180e1010816108062000170741c0c414000000700c407a036201d500c100949070300183c420b10030707140a50040c0805401000b00c00303002e00c2d941e1b00040d0507600c0325403000c030b4408030349245221142800d51820002c0c02450000b000d8107109440001d10a20801c40807000704141040001c0c00c66480a00c100501c000c02405c981001e440280f0600d0005c00000d400c1440b280782c5403503594510410b003d00c0440c0305004000b142010f240d900c2c0d041c01914041030b0180c024a0402c800b003820845441860040c25501d800b040d141c07140c28654030595200c101602003882010f100c0c2c0a084030300042c84940c001c4e80e500c1d0210301c40d20742506000143c4a40032200985504003030400030302400c00c96054003200c2c00703100c40d05246903842010341c13100c075515980504150000c000007086440144c00500d420b040e41c0d200040c01e40c2864413001c40d410740035030300102c00d64910001c0f02d144e10314603948182481000ca1700c00e202d40746400c0701c080850b02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 849104469 1250 849103219 849103243
    0x1b11030f1b0f0604050306040308100f061e0c08070506010e0c090d0201030902060d0606030e12071e0312140a141603051005090408030708070e0f01030e07031b0302030f0f 75
    0x30b80d11411a40c5840340e100751401041e014003240c605003010702d00546400f400326040e00180b0000600003074501d1860f40404103d50458546000d8055201002a02204001c050030103010741c0303503401e1000403400c00081100074020760217401c2ca541010405400800c001c4c0940c0c203490810701c51401640d0341c0c8040500013550900300003400e10800c1c0b0225a4034021102001d50051800c1400201280c06404c002c042001140580d80146140366040356a4012100c0242911881880c00410320030401007007000700d4044e00b0141c0400001d6005441980c03d2214007503010351895050281d01d10141c0254440c01c0741c4d0702880c0799203191001e4200d8082038a010800101034840000c200781914843c2060040c0401420075032082c60103050110941d841030301c001002581120016554600ca02420041240014101d142c03a1480780011405003125540509850050110010001301030f003001161551031403598100d128694010541844440c0010280f1504000c911202c4d491000c28182c4e0001c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 849105719 1250 849104469 849104479
    0x30c0b0109230604090209010807170f1e0307050d051803010b0f010e1c0302060601120504120804050f0d02070503280f1b060c0605071b060c1b11030f1b 67
    0x1030f5450000078080c0100510194015503014000705043c103000c250304041d54200b610a41c60315044000c441ea07244001e0122610a8101031813615106070fa5512480c04465900b045074107054950701e500e030a01c6224210080850000224400031406a1050352040c0700c04600030852001c1c5d55000c10703081c031b40801102e0704100c540c1180c808166101c00070344465180000b008500e010207460041e5649400ba186140840d0f980080000e400c00c1901405114560001c44401608079640c410b844401c030241c0100c07440e0041208800d0816400c00c2141c40d0001300d80e00803c8041c1c61b05d070a1601b00002d421504542c040c03507070304080d00142d030032586c2ca01c0340e03610208107004405c0600740540c149112240303407070001c1140c001c00103039941d000ea500417246000e58010040f9132612403023035a403048403c465015003c2220340c0680403031200d074003604e5080410b080417100740485000d4483c000a00c41000c407107001060009034003905013081401d1111040c0300080040c0c00382d50211100004620302c03014450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 849106969 1250 849105719 849105721
    0x30c03050a09030f0b010f0e01080a110d0204230115080c0915030405061b0c0d0e0f1519050306060412081c0902030f010c0e010507050118030c0b010923 67
    0x240d481071500b180210707049041d0780c03030a01300c1d4036160221040130f220341c2c00c0c190f96421010880c200751211860403100203000806001c46603540b4401030000e20440f460344030342400301c4103000d038a841c0255114201a003074601c0c034210340342034042140d8806810110420302400600d821240d04414859080540c8102c99a01c406074500010300385001c4114070780d001d24012081c041000b03000101c60b40a07800344007110141d09940c5c40880c01c107004203061103190740d221012000d00346014000743d9451101c05021100c40240c00300104031101c400418140c010403000030b045441410b1f0741c8188498010500d4a81c1c03560800c400040c0c1c480c041d41c084c1c1074a60312001c10282c200b0810304111811b8101d04041c201201c0c0c00400740c2da000f401010410380c000d0080700d5880550007c1840f07100527940d415103580d100c410007c80110b610703411444084409640c0e888001c001c03035403110f10408200e4800c0c0e446060341602071a25002c0d40e10180d0080c0c0b8210f0600007d0b05004602e85941000726801140a02035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 849108219 1250 849106969 849106987
    0xa051f1a040302030703030f021c0914210f0606030a02010804020907110d03020301030213050106120b04090f0506070f0801060905060a120515011d0f04200f040e01080a030c0305 78
    0xd58480d5520003941031140a00c00002c05810614400c0103400c180c00b510803003080b030301c0c0900350341a071180c0c46000070b00074000034840100700f107018810010340940007288820200c0050480465006080ca03000d5100d51900103030004100106030740400c080d000b4201c02602d59001801c001405400244901050400610414450380c928034800940a08070b5075491400a0060020742c000e0009074052001f01c0c080310248880c03405214120380d040d41d00ca4900100c11242c100060041c502581d900c1071301c64004d9404110084030550016005001421b0641041000500500b085182042c00d0003e80c07001081140e030030815100899405540c120b54030006c1d060122030030b070601442c0c030740d9183c40d00c0f042c0b2090040008401030500005c0e22000344520800c45c0314106110049601540301210040700c00b16170802c0c2c0c000d4081505170040860303c00391a403005030000d400c54109100a21000700741000004075008203580100111809895080c205803401031110f00f11010103001d00c440001d4403c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 849109469 1250 849108219 849108269
    0x2b030908071e11010314160201021c051503060903040b160b1006080c04180b060c0d0315060c050c010e19060c230a0f030302040506120a051f 62
    0x200754000c500072101012044000982c205090007603c60408200b4102c9441d400b034030607031100103511042c4009030f030f8a45000c10b094403003810982086540a2192560002d4640b20592200280003804942c6280008843c201034021110b4a84654084410701c49a040b01100b200d0030b49456141d40784d0348902040c801c00480c03403001401460703902c00000b000240303c1c0b103410087c180d400c0c0d542c85480c16125100c070030003140102e0042103241d04265890100b0000c0c1c9900103d1041409804e0501303001003a202503040c03005642d0580b02298444000701c056103001141c1d0006809075040c2850748c4102600c4069a0b5000326818a0502c1031608100445aa81c00800300381840813006a80c11a07459080c000d00400d0706a404076503203d08900c1400d480d0412007400022444010000c1c403880d03200c0d803103141030300881c3c2d041942410f5003004041900e4542200030305080325180c0001c0c1c0b950418412800403140000c08a1041c414401781c41440111108001001c036030034203582d5181100d028a001c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 849110719 1250 849109469 849109477
    0x2070c0506030103030309030e10020706050912070b03160309031202090d06230a1b180909080a020f12031504140f07082d151905032b030908 62
    0x95031007200030000101301949508040c003018030a903175400c4000301c248144000c0303204219088001da04146020300031280b05030b02400c0c1d5144010320030318000b1241840142070042c1a0424810000004100108030500d4680b030400f0605130b1404200e02c1525490042c02c0103145908907104035000a60450f25903180400e0340f00460f048101080090000c40040036a00c0c0e20b1980207480c07d440c2c00014002c0105071040003050314079500c1a894024001d00100c8404840780310b80c08048000c5c6102041340b09003486441809403041940b00d680c1c0c0328951004e890a509a08104081d13400044001000c440207000d03a500701451001010020078000c0000b0f018008c6c010f0f002d00d030b01d0a000100036030784034a28500ca00a0040307484981e60303519000c0c2c1f02d0504000b88035002547c1201780ca0601010b403500090b50758418500e02400510680300d80000c1c400c000e1058500344d803001001d0042c0103070724090100c24403282000081214450030f0038005000704c0c0c2c85c19503180916980e0f86080c01482007010440f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 849111969 1250 849110719 849110729
    0x3112d0f0d080a0e030708040605030408070c03030513080d0c03030b12150109110403030f050a0311130602120a090e0c09060408010e120c0c0d0312090c0509070c0b040602070c 77
    0x14070480c0024501c02060307035078201c990b6800a0305243d6403e00041c0301004540c3e0460708007211900d4607003801010364065201600454900604010301004a10951940006140310341c0d03e0355075444001c0380500039a40240c0041041d508180c840e90042d0b600410407901c819803605010a1078640d580c00500000d100b040c10466501804404012010341c000c8039a041c0c60301140100310500300c03100399045a000b0381c0402800b20300d1040300c03090700d140a480645042a91843c02054003511030340002d6407500500c402070064420f21205102268041c80b4104000c1407110b4203a062242007000105402d038944504260724121201103904117110500702e810b118009003001342da4554594042c0d008040f8101d0b0020070340540b21094480e000c040c0c0c1121407004507030008102040b000400c2082070305a100085080c4800007000c41c80c0400d95024015500b4003c204150245150400340028540b00602042c00c11401c080d14100054458002d540c203c2d411403001611a86180b0342004a4041c91b049 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 849113219 1250 849111969 849111973
    0x142503110a02010b10030b010801060302070611040b090f0103050c070821010f0915050105030c09010c0b0711061e070f020a02041505030d0e0f04020f0d020c0a03112d0f 74
    0x9200c0740755405402098a050342501c210800b4203000c8401c078100c0d800401c50600080300071004004c514070a801a0000b103024100000d40d070b114040000061782d00036400b05036a81408615014540340540581791600001e080600c05460403074401c20140c0705484000781309290100780004405d11407898080c40818409480b9500d50b1610405944030307c00c0d215004001d41080d52690380a04440a11001c03a003049c0c44031410340d22101d80780b0300140c000381c041c0c904000b60141c00c00007080c01d0001c1e1a002c2c032400c0e202c1c50010450144401d0800705c0c002e181084209500510081c641d94080b00264004510b00c1c1070843e2549640007281441c01115000c1c1d4011f00380480400303220107982c10300b41121811030440d080d03800003520584180007171041c8103130321502603014480c0d52304040d0014a000301404100078541082002c0d16804c980100b010a1200d601c2581404e0230150000329420072009079800400440000f0a20a020384d50284074060000c0030031090400007000800c00c12501d40d0311401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 849114469 1250 849113219 849113227
    0x7050d03050910031e020708090a1e090204050f0103020915070503180f01020d0809071802130e0c070204110412050f060c0702090103021c020604090903020114250311 73
    0x38001c0054001455583c401c05201100030603a50007840360205c010b501ca011680e4000184118800a4210700001e54800f002041005044e65a1140c3c08020703090b003020751000112000180b2041e02100c1d04020446072040000b84955031342c0d23508000703e0003c00d01e000f580e110421004908000c0301c0403108001c4403004981c01c2c013044404030141c03c0303941c480c0c281296209040320801220013085450710340560001410060340c14822034900d64800c000c00101c13034020344d80d58a412040c46c0c502c0b580b64921503001c26000c80030170003484520001c0c843c0f440b441d2824202821a045a1711031315400074455a9900b005880e148001026180200f165950044100c3e560703040141e152a55a029440c10b070240e10006034a40c01c852003920b10850b00540010340e030781e01319801e010b89100340c8040813044402c0300c00c0180c010703540d03d8002c001422082e1800b0415001514010b42520b07014984184025200401c210700500c0050544042c102000321441a0800c1c024040c4d0051104640c0264861000a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 849115719 1250 849114469 849114473
    0x30709020a030c030b13050702010e10060e010e0709090203040507270e032109100c05120606070210030b010c080d0c0207050414270106090b1906140a0207050d 70
    0x35018000303401d91501e0600881c65440e80840072142c2401d415640a4906850480c48441c1d42d400aa4444910700000400c44401d03100240740c602540040300d4100d460b08024080800108075041c0103000c141b5050070039090109000c1c01c103041500482002640c08000034040c090304100481c001c04040c1070664080e0a25240190503290012820300b00f1801d08036070524a480c000110342c1b041c4200c2283d4810442c0b004c554045050010b05034680c58850740e000407001582c10701c600312907500261191703030352a0308071a10060034040080c40144540c2d4240300030b01c05070300c0c0c0d000c091409900c0c1d480c0c000b41c420200001610540764010010b000024041000340a50110b50700a03940400c0c1c0350200d46509070f070707201000b00342c03006004002001c510135801300e811035028940c004212202511034449a4481c92225800c541180d0710400107181c89114500e40390400700620344507002d007161240d07190340c10614060080c083c100e046c40c08101c00014000d00d454400c2c000a4050100106071a01402c064 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 849116969 1250 849115719 849115721
    0x5070c031a0414070819030306030b01091d0d1b06090c17010f021810051b16051f0e012a05061e0402370f0f080309040207050a02030709 60
    0x840307046440020106000b50983c5000401000b11a034040040009a040e03491008503004580e0b41201030688604000c00003903458040c0720301074100c00c9000201440c03400c09440c15902840501183d940003500c03d185440c2d030012070b00207500c01d2038200d215060028585000104020500602412501c6401040d44001c1d00c0d200a2440c0361100244200446ea5180c1e804901c6144500c5125109090100304117040c00681c2801e45401411319505103405140d40c540d901001c1c0e10400d20540112024117115420340750140c01606082e5050320100c06102c5550152005000c0310106001e083c0002c43c5803030f0302c100e140f030090000c0c90b900070074181f91b1901d00f001007605800d4111090300400c400241540d068440840d4444402006c02070384c0d440d02c0d001d1040f480d098041404400c1030407101901c0f0343c4182c0c1082c01554540b1107003100d506181407544072a2002da40c00103030b48449a01c0040100c090000250b54000004440c0103946801d1484c10034074002c05003c1c000e4040c010274000240038002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 849118219 1250 849116969 849116971
    0x7080f070c0e01060504060905090705040321021204081f0209100c2907110111030103030f09083007050a03050d0f02090109060309150e0c040f060803090105070c031a 73
    0x2e0050215650b9032148402d8a0700d00a90150500003075451404121500c1c00f401010380040c1d55042c072138905500c0e61108502114103c400c20f010000d250761030008641c2c1023080c0e8400d01c81c44229107080034200004070303480f1508000080c10340348201d440a00260100c0c1e044958505000703250340c80c0400c40001c0644a81d070580d01c2561081260030b2005d4248040c000400507000c84058000c01e103035200031069031000c0030303000740296544d40c5405c8041c2410a035002980a14000d1b1100541460280c600421590b0a134010094603046041c8514410a94020b14041c80c5848118044580a48c1010078801d0058400103400e601c20108014181034200004001445d00c0030f40c14030030740e01203480036000d0b8456034000a0020781041c004020031072182d8041c4100c03038404d61850310300b440f0440042d408d4a100c8000d0300e0854014591005c100d20f00f522a1b081008003180040c0582494112360b0707900d0380aa00c001c0740c10302800080080812044030b03e0030010319441860680c030b007125001d5003841520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 849119469 1250 849118219 849118229
    0x403200f010606171303050309010204090501031a180601120f050706030c0809011a21070b0903190210080601090906141c20040f02030c03090c1f0507080f070c 70
    0xe007404d028040400c405404034850b0b48400c0c4060002c0c022650202c034603610003800018995824040482d201d40240070f094025406100c1c1108903400302d0a81d5401600302624a83c0240c0100c2045500e00c00c02023004c90455003c00c6407411540c10b581400f070070108010400030654020000081f0b0895019400a8004038060791204195525110282d0803164840040080b1005141800300c15241441c0300e140d50003495a40c4071186c03901403082d04e15000440c0c21072803004a01044490403030a04005c1014070b500d040f0b01d42c240302c40c0d080d000302c0c030b05480d2454640204041d4100245159001c0c40003a8000c0c4031071308003045610307030b0b52000038400341180108520800103001c400621188858158540d180c2200800060b0a96941600d4540042c40079994000c0d0311540c00340040790181c409980320b03400f0b010701180d030b070b00d00210164245019241810310800441050f01005800b2900a407201051801d10307903a210030605011040340107504502c000424009020f500f000310300c0551000f10b071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 849120719 1250 849119469 849119477
    0x2040e090106090e06040b0f0a090609050c030c1504050f0613030302010905120a050910030f06030507030b060d0302031c0f0905252115022a0706080403200f010606 72
    0x1c3c103d0a040c94a17020250b071b01a005040150209103c4411b003209960004d0081800040103081680d5240c1514183d0300c09070303070641081a940d000340c01c061207100031650f01258549151140c82c0200c8000d40114020140607000c1d003207162819465800c200c41d0300c42c4a14a075140c9203a96443e00034080d0901c0441110140101140000c0c103a105005079907040c1800d0701d68500f0800910306100c0000c40030031040d010162210300d01d8110300f00c140f091901a6009102800e07000c2d084d400c1203c1201d8010301380c240500c0380303107039001c012030b902005450384120501e100d0100c1402c10301c1030034050484100348a01941ca018081c074100710001800101101200b05800100008007000c20000315007407007180030080b6075840301d41c00c48450740003c404c690f21810b0102c0c9065030f51800c0c0710803600258513460000030500c000d132910502c0c00074480460110400207054250030120007c0c00034078090030003411300554821042c0302030340506d501442d080d058070440e40c204140341e94a074064520751049202003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 849121969 1250 849120719 849120731
    0xb0304140d05030106030b0109090e150c040b040302010c0f1e0b060904050c0d05281e050a30022a060a050f0f030106180501030524030102040e09010609 67
    0x5400410101c0c0c468155464850a6038a011400d0b800f40441c01000b0303041141c2c60b04040b40d5403d40d0310400c0791b04c0c00000024000c40c4a0326614284102028003101c9000c40103100c104207003600c071401c075000c0d207a0a2820920120303551800c03a031102d20b4800003d2101c01c60700783c00b90700405076035403680070103019030882003503500c40e08240944650b0a8070064015000a20f5820090130b06004c071000b43c51080c01110207915442c0300001c0310b0104c0328500340e00c9440c10300c0a9424003481541e034074280c580034050303401d02009a5450940e00e10030100d004100201c10003901c0ba40d09410b04070040040caa80c90811418001000c00a4841d404200c4240e80c1034840441200b02490310312603000c44480103000b2a291251517a03099a240d000a12200c0300050204403051840c1c038003070003944c000c0480c0c0d103401000341c8402211294400440e0003c0303042502e04020000040c1e600c000d00d503c03059405042d0b843d001303494004240a88919000390090015003400d011030f1410540c4840125170350b1120410074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 849123219 1250 849121969 849122003
    0xd03050a1815091d0105120307022112040f060f050705102c060c07021c0510061706070f1101060b0408070e07020d1d131d16030611130b0304 62
    0x516000030307100070041840c80144447d041807410760030710608680c11603003400c00580c000340c01e0301c4075001c3c80c818001200c2d43c0e075500c030ba000f0449903480300c203000421400c0605110562220200302e00c0344604100d02d621034054000d010307504460040d07400009640203104044810700280115007100c0c10b0040822201c0c0e0380c003010081580b010380000c8006048940c6030030544041c00e400540090380e00010110040d0215148244c0c24686240320718040d05880503441061001c07202b40758040c01000d884642d0212a440011810781d47c03200701810007074801803040c00201c55056090419440642c6008004a062400ca2000e8005c5a80c40812924000c0c3c560800d410407500a07220400941e002c2032120161a0240c4403802802c540c00c006512403074840c000142130021500c443d200490355a6506c9080c0c80c0c0000e00d229140728001d402404035004503110092401d00c50701c0043e003940c0da2441c042c812030300d10b43c08403204144c440d464001800d803244083d0080390300a9a08a5000c8900c5648001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 849124469 1250 849123219 849123239
    0x4111002010510061e0c020f04020301030c090509060103020a030803071e03090203011a01080627070c140d140f0904020a020d112b0c050a0b06010f0c020d03050a181509 74
    0x41d241c02001c00c2c01000b034485c880c05959010040030126800801d03010f00712200c1d15103101941c000e5000307800307114129280410301002c980c030140691590740c00010062002d80c5402c41c00c041102d600109a035500da0b54034400311a03d02080c240c945111080b07075082d000c0141e250700142c400c14021030081245108203c4117024540c0c0e00c45843d07000c922401e0001c3c1c2e042c90714100c1ca112510545824406640603200d280183c00802c481607400f00303d8000111003031016038407e80126201120085c00c4035074946601400884180003500c82c0c88400103004020807507144140c2d680a40c002d4025511400212030180d00d6510000b81d5000103103003034510300b2030300100103a030b040d40c8a800743e4600307201d04218801e89100c0030130740d2524050002e90203221000800c10042c0d5101c0da4083c2e0115016820400001003460241c200d4420801c24000f102901680d51030400c4150180d0504000d6030b80c105401c4c064400c5032088140c002c42039111200000c4400b0b14444c0c0c824120856030300c6141c100d031640c80c0b4003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 849125719 1250 849124469 849124487
    0xf0b100c170306010512040c0314010212010509060f0406081c081303031d0a030804212001110d06321302130b0c1509030706050411100201051006 64
    0x780c814860025080c00c4405070700d004540007601071600910b020180c050342003a4443c107540032101410340c40002c0060000c929400241340c40010029490102c50f020400700403201806058421002980803588075038035010310403074504028005004040d030300c0602c50b4440141480e52207551810450a00106100f10440c62140f000309440765803207103290301c044004080000d455400d2560020304c070004813508109041e0702700d2003680d446000389810719140700084010707540460750702200d15a601c2c0031a0080392044181241d801e00c40c0400c180046420302501610104e0045481d00140445082c40c3e40d40014007074034003032080d80c8440041c4914803044a0242c03c0040000c038940d61b003020461400074145400e5851102000d4281801ca0b1401d40a1485540c4108403000c0002002101440d0610065040e60451a000d10041c68a0380000d6124400c01c04c000b0107656984001604104a0012441c003201c0080c2030807241e140503003c060700070f11007510b003010b14400142e00040c46612500c200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 849126969 1250 849125719 849125723
    0x3121f0f15030e060705070213050c0a121b1b06110703080609010315020d0b091f0504140103150608030706050f15100f02120d02070209011e0501140c010f0b100c 71
    0x10415540c440008450503000f90000b06d2744126400c6200641000d1070103518042d039000c81c0402e0b5a201100c00c00f0b031040c0501c02d401031301141040301107412244110b020181150080c18a0480c40d00c8281686850851803040107000a107092252010381c000540940310145c840e45038514581c40c0c400401c02c1e84442403000801c003901c9284d030030041c6103c80d00540340050712240c02042080200c0d0000d289400e085031403809100c0300d41001410421600780c800c0c02494181c43c10400004070300740d601d151490500028183c2d02c1c0025030342c03a2005041c2e00450090001030241c0352501d03034a10302507002d4501580d1b40d0240103000404205400d00d40f10b000550504000c141515001903406e0554401101039030700c0080d070081c07641001540d00781c400140f050700000f80740142d0341c2c105881041803809041c1c214030881ca0329a0310700184030041003070034410744809081030007071082046005e0185104400e80d048180d4284041826a441b10350050000950115900b030903008803910101c46841e086000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 849128219 1250 849126969 849126973
    0x20a0f03080904020f07050a0b0603120309030f13031b0e0708240a080307060207030201321003150c0905040902010509210f0c030c0103090503121f0f15030e 69
    0x10340e50b491800e5401441c02c11000081242000c00c1071720788604164141d8020742c1c88048410401c68039140900c081072450800704070340380c00c60422813904e5580740150409031b0100040041d0341281d110f10007151800656101404641d03112801c001062440c41d180f08055014100ea004241c40c12f02034004280b20320a200d61340c1034020150144100050b15600c0080d03005100c160000c224860144002d0a00703034014400940d80c1c2e00f070b41c50000d007100c04560b10341650450700701e50b5003003110340e4074105654001810b00c0200e80792900d001414544c1050307400140349003240600d00401d02c0c11500002403c0d113040e150661a580d8440501c8140c42c521a00240000d00c208441035071440d02030800340360540c8820103c4003401c0c02c40f020902d440885415a001580400c0c40190185401c00400c615244203281c2801014129903c569a03802000d0079090903580d43ca00243c03034250401c03100c29001e440005802080e45d510316010348155924024460381c0b4030b105001030083da009000d4205032640000c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 849129469 1250 849128219 849128227
    0x1003150c050a0822060e07080d1707031104090c1d061e0f070308010306244202010f0905060402061e310605030c0901020a060504060603020a0f0308 65
    0x1a0407148108010941d401c3c084e0381c1c107408006410207651461005205071400220380103a481400e240000c030b41d001e2040c503400141a80e003102d5020710882541130000721011080e480700310040e80078180449000c083c130b11001c6000141c410319038205480368070943c0c40701c0e404981034150007050a071203080c3c0700390040010050040e224414400c50040e00c42c403120485c0c00c108840c0129000d83e481114160300103501c5200600a01c8514030644c0d102a49035501c1134620760481c19404a0348906100d054091002c10507020082c08414840c4011100b49030b0510981540288815009504106801006618044402450f107103984182052603801c18001d081c0c0da070310b0303900300807a6520072207070000080c01045441030301070880c401a044400030701c0841002d400c1280c44030070341a9600d034941500c3d20f4480d50b08001c032a411200703c070340100100403040d50356035010300180d10b0303c7c0038900700501e0349140c4003c100c140113080e400807050305e02c00c071071405d18940c4d100ea00f04000101400040d210050801c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 849130719 1250 849129469 849129487
    0x1181118010203120c0405090f01060c12201b060304051c12140402040f1406040b15040f1a040f09021303120e0306060d0309050603100e1003150c05 65
    0x1415641003894140304891a007080044840f400c103005440d888199400401c0911442c9005810381c0e40c40200300360054865803401d20014411200c0c21005845402a2500c07601554411304001d01010791030901d1002c1c0c1c07852062080c2c0d841800c0d2009240007442c0c00441c65052030a91304690140b0380250050110311031132002d41c00d4030481005c0640a00864100701c40d100503040c05080c1404c8000e80c45089213150900502091b100d0041a200002c1d00c0c000c0303450400d190300010f41c0d0704080d0503980050b00601d1003012030b81b000381c958110030038950045000102c800c3c9004500c803d81c0c44141407011070b00e420041d803000701d025600824080641d1000284010030f807680c060603140140507909240560389440b429460500c03a440480001c840c0c1c01c0340803003030604005181e008481690302c504006d00c4c1d62001031100303006002d414411800003021840100c2050726100c040c02100d5241c50407800c0a6130420807454491004448400c401010301500c40e18500ca0401c01103900c0d02ea080c41c0003404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 849131969 1250 849130719 849130747
    0x70c0507030b0a0e060c13140108040b0a060503120712090602060c090a180f05102102121c0906090f09050613020a050a1d0f06070305091503011811 65
    0x5003040000d41d95920007403c00c0c1d804105c541d018542007510586e8407102d02e04042c4000445402c01640c24034403030381c81141c60341d008c41071527400341e0022190750b243d807100040480513201c190f0080d42d161090310725032180038646000400c601c030720400102c3c1c403504640a00b23460f420a07074413070131015070809800510324502c1c0d1001440101d00040607090b206444808209001011040500142c4da40e20b40e408040580341c450b09030032071005000e4250003468800300c0e6007000160721a403044880105211021512041003111192403060107955100c00b07a480e9036803000004500060000d0b150040000305c003406054032206556080301c1c100ca859042c82c070f02c00e0203400003400181d0082d01c0400d05000190b40e0303201174030240d0303030642e20503950303c4510600030020404000700c174405403074104c5040361030345c1c403c14250038192003074407041c0c4c0351107460406907103d00401e075100e50003255204200f0050f080f94002103060341c1442e050b281d8442d030b05055401c02c031444600d04459200041102d40058140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 849133219 1250 849131969 849131971
    0xe0d2609031c1b031a12030f070c120b04030206010611060402010c020102030c0f2a06070209040201120207061b02010207051203090a0614150d26160b060306070c0507030b 75
    0xc9074080380090810188203050103d0074460310029540700403080b00940308120f4040d1113a01140c0849001503c10019500c911510104540e030032000613840c0d04025807a007540d00100280200c20001d069a0300348042803c0c070881e0304070018024400081002070041d034208400101c0d80c001001d844d030b9164010f588602c50404181c0c1507200c02d004c0c1e0340008504100300100c8402010191081d4030240c0044a489480c084030a40f0205c07250762041003d03160002520500c0c4c1e01110000b025807580d00046c0e500486041e00030b40e400e40009044400d010b10341c0c0140c264040c0303070301c203000f144510040104d08030701a50000500503003041c030500c4481d48205010310380140402090350300c950000e54545046446c002c10800c1024172920804c03440c062105025043c411003551316080c0380e461556410100c0b52080b240b00308140c01d20000e2400c4190a00640e0490040303610403510810041c00d060661004c111802446032003074074001048a8800c003440107a48d41e0060080140504503a120040c00030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 849134469 1250 849133219 849133267
    0x1020c0303030708061e100906030e030702030a060f09050f030a09092901051c0509060604060f21120c1506050f04090206070c0f0303080f010f030303020903010e0d260903 75
    0x114411140d0016550947c1140d00c05102e611201441884c11402600f40c459440b2a445140c20a001c0540561400306214604540c800b000007001007041007030100500c500328000e003080c1b141003411400c1000c004020701e400d0b080c94850000b61035031030100ca000c0c2e43d6003c1c40e40c182c412070b20034401083c50044c00d101c01c19400504003682414441c40c1c04d0194405001c06000d12161158103104541c00c0030b0040682014060344c05211190a00d0842d8040440300d1003401440b1020018041c4000c4089a001c210300c1d60040d4000c1d03caa024a000401d003114014003682c00303030b221642a4040b03179414440c940c200e40028111100044503030040000a00310004146d0700810104031039000550900000005044681080c2c50810b0441c03c004100c880020042200009500c00620000c2c2c6e58010804c21240e040c9001359807a51140302284c090100c00050170924070070001007001850f00500b0018142d50001015003224503441c1d15090340b0350069030391b1070306a0002c011241107460a4a40040b15513 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 849135719 1250 849134469 849134509
    0x10060c0b04170d021b1b12190b060f011e050a050d0e03121302090117030d060b030106020f19030503060a0e0a0b0f0f010909021e070f0201020c030303070806 69
    0x801c0181d07182255600c00d43c40124000c3d8001440080c14000713582c0e009400706101700030521403001110700c407118200451414031503d05400b001101071001c1043c00b603003050740840098501c41030b2a000103019015034406119144421210040754172810324619680001c5a18180d01c615039882a1a0744d07020700a1102000350030000c071260301043e07000700b017000348904004547e0781a041401344030140b0b01030405000d08454041403800341e03884041540c15244103503403412812902e00c054601c0c5205508045000381d052200000369091003101450491b00e1035001e607906a021000c55940702ca80940095804003138501d2100c0201c0c1c440c0000d903600a0002c1d200810039510b80b01e0a5446a000700d602d20704c950f071200c41d002c105040210303074a459010141c401c0c0c1c030701d6204940003038a20030385401260201c0f07a011071414500e40000c8a406111040c102506a8503652410181c215548101059000d486441c00140f2181000800c0301c1c4605a55582c82d18a80c90703403010002c000b151680008015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 849136969 1250 849135719 849135743
    0x30f0a020d020403081c0c0c080a0e01111c020c010f021504030513140f0a0303020606092203020303011e0b0f130302180a0b030106120b2a04090510060c0b04 69
    0x940d201d005042c0003511440d17030320107075030300388111b00650300c2e401000b5041003004000c4000041101080d0f40355805039046c02030701000f001d00100c40004902c130f002d072050300ca031480060f040140c8a0f522000c20700c41d6426a01d10b4180e0398015034401390203206200040c2d100008240c00c09a42c5805c480d00301c5d05c28904a45032412000c400c02059500e13810008292910201d86140742c030b010301a1181c0c084096981c2d100391807071610081d40301ca074003d11240c0507801100010fa0b0503075a4545040c1700303081c204940c000060580c10021750301d42090088484400c134401030141c124500401d401d0840d822452a24689098a040e4044603013207016240844900c0c0070001c0016036581c21a040811700820512155246c1600c3c0c401c04d072400035030030900a034903040c818444007031600185044560405400c0016445400c10005039660b0154070a0400403e007407044214082200100115444c4440900c40c517101c410003c1c41154292090034081855000c21000180e2103a62295100d4042c902e001d5003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 849138219 1250 849136969 849136973
    0x120c052b050c0c0d03060501271e05032a0112140f06100f0801050d0c05090a020304150e03070201120209100905120102162301020f070201090803030f0a020d020403 72
    0x1a241c0590b0300090030305012415490110080001c6000c0030b0551074280b1076a07241c000080c000d000c85403a00c0103000c18480c511070302e284041c031703201004006844500649420008001c04034802c0b034001d2520a00592080340d140d9100e0400ba040420024440e4803005e804860055407140c4801700080451519041c132400d005610f21595440341c6010411007105140000810078000344407481e00c400c0c060b2903070f0b14821480c0e205118a040d52000d03a40c480003d030f414103000d4581c800c10350000380e02140171400c0004020301c9070081e41c02503100e082895034203140005142c0645405050104c50391b0300901c031a001540c482c0d4000031011032103160042c50403420101207070448a00300c3c24040410041c0740100007a007441048c40e00840410300085050054180001178403440510006d4907664581d5082c450b826101c01a41d20150741040003103541d04014129101d40ba002140242e003c1040804002140000841200d100c1c038040002e1441d0f030380d18401d5480003500190041c081c056402c2c440440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 849139469 1250 849138219 849138221
    0x220b10031b0302130501050c281e05060a0b04090f05100e1504080a03060801090b010503060919020d020f030d0c0b0106110a0b0411030d030203090f010903050a120f1b120c052b 77
    0x6d0452406040082030740341c0d00300140301000743e110403074ad4010110443c1010940100e249600501484c2c03001c288a031702c450029014080140f0064202e2600e029500100800061005200a89140c0500a80ea414207102d921340040c0071030040585003003000200041c581500070200050142400142241c81d40603590031681d044008072801340d1011300612080c641007020640c0b2104600080c042d024400350810a03080e00003500030b0262680584580c119030312800d40f40014140074049820b00b10500d00028001c0d400280b09a6a0301000300020405900c41c41503c004004500e004228903c0c0540c0c0303c0103001030060046d1400888135003208915501482414801011540c0143e04d9050052105082c540f00211062550b0324085985000a8000f02520000109070030003c08142e4141c2440019110050942808514211013041c1105d00481428500d0344159100014000300d12070b41d00859070900008400f0401c184005010b89501d000940000c0c05072000c0800006048600c0c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 849140719 1250 849139469 849139513
    0x207060507030b012d0c02030a1e120c110909150a020c010605100c1202010605090109290109120302030d18031b02220b10031b0302130501050c 63
    0x300001c0c0c4031601c603c03656900c201950021000130000103d4140021000c000b0080301c0240401840702110400c000d5580500c4010134960300310030790303d540c01d040e5820440199116003080703652007a0603182104c00c42c85042c3c0d402d03d0f542d01200f00003444130401c003000800c030b200400e404043e100b66000000d4243c4103071a21401420750346005a1298004d4480c00c0c02d450117a004503000b40186000003254945c815981030700d050304400c0b03e0200300c2400ca0200c2c0507000b02d40040d41c0204074900000b9505045902c680c3d5052021b40c80f2481406007040400c1103940b2203081e950000e014040d06000380d0100d6107041d50071911a0040304d10b400c0701021841c041c3d0300040300080e01090a9101c0e02d01740b542240330011030140042c030848944169a0025503800e03010010075039400d192030030b030b026841155403011000640c000c2c51200d40000400000700a04032901010030a452035154001115000b402982c09074485101c0c8510500d05050045903503030481c01500c0814803071514151340c0c0382e0b11a40c02d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 849141969 1250 849140719 849140731
    0x106050702030109061a010e0d021804030c050f03030403030c020c100315030506270f0a0b0a1805010f0f020f091005070c08030304120518040509030c0d08090f03041505090402070605 80
    0x100c10821b01d007400141a120314080c0d614080c6056100d4480183d03074164051101c58500141c8001580302c0f81000c8900c0391050500509521603080301c1d44034004000061803240784660340a204042d407148003240c503151034610981e000b1440490050209020341c00ca605901c6011868000e590f9980d00ea491400c5016624001744030700071400402103250b00603250a823800300d07100411060003000315069847c00c003600090104d51203100800c6c641101c50f048442c111072194019600c0e645941020750080496040100e8660300d8150400401d41d503038001c0d00d114661504c11719050a40100610000d060038981c54020050104030482c0010340b0008804003030001c001c01580c803032405280900c2c100d04803420903400d101040c00034024043c1c0c120b00255078040284c41c081803588030440140d286028551200d0340038000c0700c098084040e40b0410302841050391000702c480e1094070848807512880b41d4051900f04441c0c90b010446190b000324001c1ca110500588014038204042c2c461000b216010340b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 849143219 1250 849141969 849142001
    0x613020406120c08010605040905041b0305060a050703150504020708090a0b12011e0b0a1106090307020f09010509041b150305062701150507060c02010c0908030c06010605070203010906 81
    0x10b0341440b840c0610440c0044000380c1071500e0a9414424090058043d030302c03c160f40d00d03407544001390800802030569408103001003510564942c0328540551901422209244224035010000303e000c0c0c80317405181c9090481c40c83c504407160400041c040650b00010b400d50300d111040000503030a4071410f500c4402801162100b40d00c40420109210403888181e100c2d000c1c2c05008800d484081d403002c84d07288100ca10022042c0d0351075110903000d98684904665096080c0905010851099000300c02005194400c55682d0345400080f4104040000203000e0f01d900410380c440007a0008040150702d00050310000040c1d80c0c026903a02d944001e49000a4080000948603414000c0314100406881d02c41e400d28000d101e04400c10b00202c070090003051282d0b400250442c07103080c40307175030041c0100c0b000541c0203503007072160001e40c03840a030103401130300e900b90002000800300041c901c6000c020b455a02c088103018124903440c241b0f013280c0d01d8002c007505030b0f8103540e20700d01c240004400b44950b4941185045e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 849144469 1250 849143219 849143237
    0x40b0103060e04050a0c06030204142106010b0d06050a0825031407150203030403360b071a0c2a060a0c09170601050405150d0503030a0f0c0806090613020406 69
    0x5442107206c004d5501c00e006144c0103001c00d20400106a241064946081d42d207015030100720401e8118000c0c60b0003104440b8000c4200129040c444c607001004203080481003445220742e20b0301071041c0d050040c0705010042d00816082e500082d00066030001d00c0d40841603524036136403a034481c0ca9007600f601801c000954040c0004010b4a42101c4d4100d01c2c03018140040c0d421442c003070701c7c00b6110300541ca612807814465507214810b6980c0021200d0b44c000b4040c03255040b07890708c070700b1181c55a500010302903032581129071011140c600c103100101c0c80b0316003a0009a0621649106048104034003400300b0071205551050056080e10070000e1a102c0c0403020804544200c943e9806001503496820580594408000780501404000750440c11148142c90006255841c481410280e28001d40040c2c0d22403100c401000600c68000050b500440b8595070821101d0412000441110500e000302c1000c5046403001661500e41440140d070f1010001e8034100080d403003103640a0407a80079401000104038410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 849145719 1250 849144469 849144473
    0x3060c030a0c090302180414011a03070b070818060708070809150a09061202070204020a05030403120605090a0203070c0c0815010506030f18030702040510030605090a020906040b0103060e04050a 85
    0x101680b05140c1d0030b4101115240c0c11500414461008103a01003100c121000101d0100b226410140540070003140080280c00c4010a11042001800404900c2071041c1c0c4408200d4140100807103413501c1e4019051031801140c480c03c0b1a000200407665940300303600380000707070120f000240106011442040020b50301e4284c1020005040c03074199003c8144d840500c000c00039a500000c40c03a043c0c6a55003080340c10b900407502d005c0041d00c82c4850080d045400800d9a591140d0444003560103135119032a1050707071580c0d1141110440d105442179651005c01c00e0081007a1110780d500450304422245000e203840d0308152948084455140d1008919520001d24441606025640c19000d441c0440342d00b4918100042103180900d4060402e00892588900841550300200200c0311017580c003600c2440b4a1401d44854091081d0030f10042da00a400e00000503e052808540442016070081207006540c403140140802428054142da0500d070f501c2c2d0010070440e4610201301d00c610301c168014942d5058074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 849146969 1250 849145719 849145721
    0x1d130809040c0305250e060c011b0903150c02100b030c0405010b0409110c0304030204150e0405060105041a09071809020c010e0d2a06060b03330f06071103060c030a 72
    0x1700c0301006003003140ca4030440380c19a20540441d20480c080361807a80760403610404600400d050b0720402c0a840e460415070040b15040042e01d01100c1c000c0340e0505048240c1d280394801d442400c10303a480187c2040740c00c0c4070807907a10340c440345540001904642034000a00c0109041311402c1c1c018440e0b0b4100483c6c2001000154015084a009000703200f604100300d080d46103549018a00000703200359120710078181500d0444602100822941180302641d0625007040c54480d1000c0c01050700036814100c0f00e07a1644c02e812a2120308103000350103400c0c0c1d651f4000d01110320080c0381441301d001c502440380c001568040d40c006004c1d040d41042c0001201500390600f14a420380036624503050200705195501e44d00300e038031060101c4a140c41c4000d241640240381041c010611031300002031903103000c01400320781c62610110104a500001908064401460000034400d400072091035100d49006140105820f048002d040e0303a030b04c1180300d03010f5401c0740030000381403110841f0940c842c448040204410354840d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 849148219 1250 849146969 849147001
    0x105131701141321020a1208071b020d030f05090409031d0a0b390a0c0504020f180a03021c1a0c040e090f0601080a020301061d130809040c0305 63
    0x10030a483c0c44148100c2c2d031a100c0000000d1180030300b5a4200322038846843c000e002c0004240c0d4001d1345600c10225611003d040080305a0750307003001550b034960310500844000c8840840c9900100030f00090801540c00f11100c54032032023a1750400000f88815a81d03a1581d001e100100380c425140c5070001000103458540640c401c103030781e03485064202c40401045100f081113504c0006882c1103051035260240f4400e801580d08114030502d0070302800e200342d02500100d00c81d05660320a980c01103145e642d030300c1008103070300410623102c4401401f0040300f80d004d011811030b007021a4000c1c04904131280c0e65000544400711865180e045050011010b00c0cc0007030080382044420391010401840341400d000e44034150040e805030781c4810720700d9008910480000c1107014220f44020702140e00944e1a03a01c0079845000c80c8070101c0c000d41c00e0650104004440109440c2046401c4181c50000e80d222141c00c00008501c40d402e03a02594200860400b0780c03958001c0e901024120384001c50b15080201800c0d012002c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 849149469 1250 849148219 849148231
    0x203071b05010504120624170c030c10110724090b0910050c2d010203041a0c190906110d0e1302160b0604050f040809010513170114 58
    0x520040c2484681c0e00207059a050756401c14201d205a0000d292101c024403241000100d02081203580180d1801c41400070803c0d5204c40f00d9400c02501075a94442c1c0d00c00142c40580c0c1e154001e01c00700c0c0c1290802c018004403015103481c01d072404042008a40e070402034250408554600c0307100700c50f117640403100b4500e01d590305503150441752145410001c00d0103000d91030b80c1c07510441c9100300c07000c8400e1140d4142c4580a40c2107044d00c245150082400505943e280400050240d0080b0510302040043c03094074800c94014102e109214140c0c810981d403030078020f2140301034a005102d0068010030b44d02c03156001d958540c4460f04050b0418034081d004031480003110446520010140b1041030f07102c1c3c1003840481d0142c8040d2155040415454064062000605241c1782c0c040e060405104154007580d0040a080d201001542c032451070f0741100d9082200c0152000300100308c5c01e078095101e5002000a00240c0d181450840e40742e40200c0084035a0411000080c0c0d115007901981070f20b840c03200c1d0341103c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 849150719 1250 849149469 849149513
    0x170f0108060132010c050114190209060702040e1609090510020f120601050405030f07030b092a0a030b090a02040501060302091302090307080607081e071b0c15020307 73
    0x14183d80000100c1d4504500e0042c0d001c801e48003c0285640204040100d49600000a00490401e811007410012046940004074031072840b00d00c46028aa1084482d211006400790386070110710380a003c06451400d81c8800c49101358403003662445260075031507015140100010811008038113110b840e000f000d030018034200d0310400c03140f0051100041140c0303404800700c010b00c4089e40c0302d80040c0c40600590740100d8160288094041c560000440c4010540c0e2080206601e1078950660740b175518110301e1001d02c41d06821030390070401141c501007083d01301803000304034222040d102e944090b0005c90540700892150300481160b021458a4021203016112924013181015860f00000c0e00b4080380200b074000705a400604944152410b2105001a000500c00c5600c5400c0001c0005e100035000c0b505244140c480f14a12105113082c0c219407070040000b1340e0f50890044251356103d041101703010048440741252103002802034886440d034600c000d80e5801030754070b8850504101402000c1208140602c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 849151969 1250 849150719 849150749
    0x50d0806011701330504061b050c330306130e1b120607180b03160e030a12080a060801051306021e0f042103090504050601170f01080601 60
    0x1000c070003140300341140c5044558681c3c00c0141039041101c10000c0c1303c07004200700328035481507005404c50001e1080b00d14541c0c1e0907104018511980010030b844880041c0203400c502c18107100c0d407a0412120b40828442c04546903c0d8426440b41504010302c0141c405002401000b00520752800217100311002e44012814007160141143e600c1d1954421209440d0381840302c00107854503200e00300c0407031025441c1400c64030f480c2041c0501400e483e0701551f00e020041d8400f280807e103194044141d034014012010924a03e010b41d00c1c05030351f001100301e2190703018803d41d800c03400415100c1c0b40e40300ca92049510380e00301074144044040152030240e00401256814101031000d0314489200c9024600e800040058070b880648601f0011203100781d230680c28070803020800c5141c03407084000901c02c8402014000800c4628200c0548624030740d4800070b0041549030038104554101a040b10b60302590500d4601020403031001000120703102540c00030448030a04006102c0c00c0020070039507000d410025400c6401d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 849153219 1250 849151969 849151997
    0x1e0c0914010c0f0201030f0f02310b04060302160f03031d0a02060f03100f0e060112060e191b050414150a11121b06060402030601122304050d080601 65
    0x4060f82c2a00241095640d104400300c00c90b9951082d01e000585410640d80c420b400d50140091000c29007140c03000d05803001c001c1e1091903111000c1000c854110401904007884c00d2002c1e4001e401c00440150b0308014001e6150020b124000ca104880707101e83c80010705505001c85200002c503103c503a0060310341c07200d55131a0160703a402e02036641211001302c03942d54a40c2e5004000201050700e50001005100820000c911040c48001c00d40c400c500c05e07a41c1c108025401c0b80c15000b500c000d8420700319080c64480c0410011807042c04035409031540190b01280584003080360f1034a00c40c41c2c000712000210049401e000c1a02404c0950400c03a4080750300d0b440c4031446a0000c0614810709001c2014020390140d140c070070100074041c0d00e44056000b140309803240c002c0d55040d0164940700401079031034040e2000181c41c0d481c142c030130713a402004103a6520102c4054850024010807050040000c513210400e0f802d03280300c44443d00c042c40340c0e200e0000780041800400018201c8032010f458281032141c0b829110700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 849154469 1250 849153219 849153233
    0x30c17070b16020402130f060f140304030c0b040609151e051e04060608010f020a0f03060b0f0c0309130903080a0c080c2b0614030f0d031e0c0914010c 66
    0x1103d070100c0300182c0c0e0f802c034a050042d03518195440301484950962000511940040d500204c0000c1f0b61074a0304444644542100c29101c2210001c021800301c009100100da04d0001244e84a44a1440014002c10136181c41914190b0b00c45c00c84c032010b0305c80610101c078204043e00c040a1401d4014148064200f80b107220000d02402100640c891003000700041c00e005017500800000d201a0700204a8544042d4404001c1c2d4032242c4c03604040340302c09003580c6075684640f2a1760100c0d10750f103500e282001c4040821810542c000740c0140715510040c04001c28581d6000a06907601b0900c1e180000c3c902c0d114600500400300080407035508900d44440d5a0071283c01810250f880785440c4421684e550120102102903868000140484440f20040360007214031a4003003415200002e81403070b0161094410169903035036018038041250420003540e103006000c0e42100c900e4809801070000c82e0520882c00200301c0380304205440018012000400c903a6102012401c0d00403c01c1c82c140549803596280e00c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 849155719 1250 849154469 849154507
    0x421091404020705100e010603020a050f0a0923101d130f1e0309050301060b07050a3003020a030510150c020325090506120a0303090c030c17070b 64
    0x350040350002007041c100001130013044842c44010034108004042c010346107000345600d020490054408103c0422181351516005c4002c5500030804050103081c0035403c4003411342c210b150107600f6000552803491842e1010103601c1140c80c0c0704808115450030b004181c1c0076164801200c000c8814400740807210301d600784079078103045e00020007005415007490100c0902e0501d0a217101c41e07e900c0c032580020951300c51120340448030100c0003880240e403505800c031001d2103100350060080d405003d900340040d80c100741d4000d68103440d82031500d9448036480c14580307400e10386101500107a80040c0d844040394251013080e8200000f81e40d06000c0e40d0070f1418001d002181e40b600f00b0305000e9900c8441d41156810448000300500540380c860504403804540f0800c0845070003200b540e681040b0001d050360500604d410404c80c0e40b0b000510581c9a5601d0a80041c0071148080e24034000c44617020010030f070342949d6000280010718140c2680750620080c1410306d0800d800075101071404029201c09888441002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 849156969 1250 849155719 849155759
    0x1e290d0201092c0108060702070f050609012006011701270f0c0f0801021315091e030b04030c02031b1e040e0a060902130504080301060309030e030105042109 69
    0x2446003542d094041401401d00d50b80880c40e10f00d5480041803045002c41d49034042c548503000c03920788503114038440e0b0707100980e8020300f50042c9041c03140fa60207610178201d03d0703003420701c07000b000c03e141d01d00101590a005d426040941e142690139860b0003089000d1007040002088800c14008802d25010f018034002141e0708090929020843d1942c140500c0c48407100051031680820007519583c1c52a160107504034892815403020202c4000664030320f40441150b15040d25034940c0400307420012016030782e00110500e000d1440c0c02c80b0000c80011715207030001d8000c41c06601c8a07450760060303204040c9413150390090f501000004c2c203000040d035120075240d070540042000809030545a5800824001c10100d80300d054540f15000500303051146d91b80c85206003a00a443c1c036034005850b02d81c880240c0d0012349008012060070001003160604c80e512007000c99101c2c0c90101d2040f554440045c1c02e503601941e00380c0b481040c14a044070a0600c101d80f121800034035080081c1018a00001181440000944 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 849158219 1250 849156969 849156989
    0x108240108041b06120c11070303031d0a061a27090a0c0909031106041e06020f0c060105030609010c0203070611040510052205030c041e290d020109 65
    0x2040402c1924640c400c814803080c1400801a0f1341c66500900000188004a0701c09140c102c2503407407140f0840f0806201d034001ca0090081c0ca141d47d4040b40202841c1d680312141070100210a02044401d0000481e0240656008540e10810010030154510031040d442d2003440103005c40494080319010740c070b0203955900f045207069031740c0b2141142025010f45004150012400000c200700706164443e220f000d010703035141880c081c01841402d81e102015100030b40007004101000e001641d400c2c40c0c104005206000c0942450f0b0301c0c60f6082416004491012241d42084006112600b820001594000d1f07483d0002c0c0b104510482010b03440c0e114404001e1b000580f158050780b01d1501d0142210000e005c0900751510300c414000c0300174443c0e040800343d0744188910100c0e000380c910600d540c3c4015148010082e0900c60065002c210003030403c001340381d01c0c08000d5050300703144078068420755444449644440c980c141d0390388030100c9071145030844c0c20310039039101d40c0c3c49001d82d9105404030155503070022 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 849159469 1250 849158219 849158221
    0x40317071704151206050402270f01120507022b0f020d0c0212010605060c03130509040b150f190e060607050a121107090603052e0b15070f020108240108 67
    0x5134680900501c0c5c2115070494000a446681c0401d40343c4200360120b288640039444103103207010840b0894030400501e0000301d9210b001003008680d6031100e6040b54080c0111a2070604280904e846905c540c2c038080072100202c1480d1040c0b517041075840c280b00c500340c40500700d400b0040501070000b43c1c03d4000170b40140307420342d000e0b000f10000b580001c1c003402000b0705403134031410070801055407944103040f02807a44410910006050400711180c90080380d21100e07000080c1d950f1410b18400311042c0c0030055100042c040f581440e6216488502c3c811080c808800c5080d0b82441c0154480c0c00c000740c4242c1c041c2c0c1003049aa004280c01151041c4400e034400b000c0201440c0c0001d0840e8003401f5404c2228a500904000090640c11544400212446081034440c4c1c048801c1076401544620b41c0c03200307441001c071314100d07035612124ad211550b041c0c0010950780303070303114100c1080d0802c0e00303c0001221252604d02824080d981c11840480d070096200d2003c0c9061031240100301d1002c0200e541c2e4506000f0b42c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 849160719 1250 849159469 849159497
    0x305070302150c1b0c0405250e091504150b250804061404030b09010b0f010305071205061804050607022b0507030306050603250905010804080d0204031707170415 71
    0x4001c02189540060003801f03642851041c98454030700402c1042850081140d213202e02c14060443e000403100c0c002c1584055540300119446102103540601c5d500990340d4002d14401040c10300303685d010f0300d62001d102c0d407a0451a41d5028191a180d001d10047c0b225207151140015403217800c89013580c0051030000b1203490000124566070141d82c0009201000403c03c000c4513060541c44808079a00464801540e1680c02e801903048410984141700050104105a42d01054a070801c43d000000074008107402203208081c1541c0c0d0405840072a044c0d000724003802221507040041c0500800150f6401035040f01030704107000700e001401da2002c180315011134101d0a06020394401c000524018003469920703d04901050450700384a40c1d100048800001070000d250b10509200042c2e41060b1181015500c445d214900c00d41c0040070f441d4002ca070200b2000c400140c0070040c5116200b8508007080c1c40b061146020f00c000b80b044001903242484c00e21003041541c240d410019a081120b040c000c01d205245 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 849161969 1250 849160719 849160723
    0xa1b33020312130b01060e0f0922060e06090313090b032d06070519110a060e15060303030c090405130501020a090608160221090a030305070302150c1b 66
    0x2c0340340c030146000000800c40903e80c1c40d0341c010350b02c3d131007001c2107081c41e81c86090540e074070402030542075003140002032288040d040c140b092036041042c071030020b1500c3c0600b00703900d4070070a40102e0450303d06445034170000c06181704006054000311081c020710f040003100b500c40000150540700da014030f10740320082c000458078180b0a4101d01e01c82028409149200c840d40d004010a800304400854860b24000600da135100340142c6a07d66a15407003524001040e110807611041003050804240c000c0200010000e20980700e0600525515006058101844080d5092140004100780d010303406c2002080403840c1090304031156841e080320005a25218003c0070400e035040000e000b00650310000f1a240015049082d0200300d4650b61741c2e01682d585c411070f80c90340d140c1c28985884056480150135210340300c1003106620001800103852170806a02d000091030782c4586a00a40100d000003d15100b4140c1c14480c9180801d4080c81541c0c940c200850003006c140315142680d01003482a088095540c070003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 849163219 1250 849161969 849161977
    0x10e210601030b010602100501050604180204050402121e070f030e15010f090b060702130b06221a0c1c030e1209181003150b030a1b330203 61
    0x40011141290b0b100d1a00201d004030a0050034058403034100f48207034414250003494140d94001d005181414035007803030211814282c80560f1402d540a10002ca00340e21140b01810001303807a109200e180307061450b100400054100d65904a45000038100b00703d080e003221807021081c02c1850002210b03401c0f0480c240c14031034001d0034081d4010841000007506401e180c07240040c1c03003008032708008500204040001c1485447c000070342100c0400020303540fa2006501c03840702000064502490a00d00340b400c00c80c01d01c410480084400381001c0c00313002c001621542c50f9030102d001c5030024500b03484180155136814142c14407105100c05180d01010700c0317109800407644041e1400032500000601e42e0020810f4100724801c40c0210704d040040c0d0540103081c40144d0050901c01c0303521a143c0d05680700c00b082c2010440140000e5a218081c00a00751020405080d2080c0940c981c0706440c0c1840181c1c0e144010550b2003140c0c40c0c0d0780e58500b0702420b40c92101c0c1c8440c002c4265881c0d0b0816004d190142d0071406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 849164469 1250 849163219 849163279
    0x601061b02010e091008010e1911030a0206040b0d2706050603010219091d07080708150d0f0611130603091401150801060b19050a02010f0507030b04110306010e 70
    0x41810b110201d007003181d444090f1511803002340301c4051410b0806548a04600750914034024200c0c801010502610030580b040401600f501c0b40540d20383c002c07034582c0c0e10543c800c5200079400500c07201c000199114121b24038902c0b980c1089008143c0c2220b660b0302d0000740014191031b81c0e0b04041000c0740e6013581220414180c03112200d1108146420182c0104440e1007404103c01d03400e00c0c1e504d02c0c401104d00042c450b440399100e10003d9201d01104640e904d100500b02302c1003080001e004c0c0090340c8d0300c0000b6824141b00d8100c1c528001c40364640340054a070400b114510314270090280380e1a07603050714108401d60314a4540000c4450b46070820400c6000f180624904a5180000412480b0764040c0e03144180ca8004000703000140e902e10700c0315028400c0038107101e8901382ca460141c25140c421001000441c0245c4004200d02801c40c6082044a0040e5800702c04071341e455414860a0500703002d001070f150300000481c0e066241000019006c4401101d0140c4900301e1489941c4018980c00e4101f04405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 849165719 1250 849164469 849164479
    0x709051203070209010e060a172a12120d112703060c0703020a030e13050106020105070e01050c06270709090606051e060a030623040507020601061b02010e 68
    0x1600e10525240e9201c2541030303000d2941035002042c1254517000a80c003c40014051520384c92600703020040c00400150020304502802da407107000140100450b681d44500c003080e10480d10a17600401c9128144036941c0b801903004aa40c150b0060031400507074801010303a00d0049801b07140c2d08020107451080360644082c81244041400c1c4c050020a201d0440180940482d1407039200c03000d40340d040380184c040040040c1c0c0981255000203100d9400d103500302e680645222408504c18041c07105684090f0000b00060395280204011140e206003081c01000c03080c00e14510b003a1010f108642c4030b40c2d00810031080f46840d048502c1043c404040c0b0005e020a181c01900d40750f0f5260304048000c1c1c059a0401d0b500941001c40200d040e1814000c29803000c6030b82101703010058031120a0002c0394101089140500d541c40900240326806600154016021222002c03152880d05041000b100d4025286104540c0000e0040c03140030b4000303010501c628820080c18440030520b100489031807a032a10001d4200e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 849166969 1250 849165719 849165739
    0x50c250c03080c1204090209041410090209040e1005060f0114040b0a1701140103050a0e0a1101020c030114100801050c0f28050d0606020c0d03030b0d020d0b10050d0c0b03070905 78
    0x1098240c1d016240ca08e10072102400300c1ea000034100300d0b400d84199850b0305500607a501c1003000c2400c0d9401000d00b448003500100381034240c4100107060224000c506040c0c4ca4035030040203680d1410111210502c1002d0070404180d80000b03904101071701945c0100c44c50300354005804110305c2c0c0106251030464000070364144956131922100f20502c00ba804240340828200303004110040c03c10300803606201070540c0140341d03000e43c644a450451003142c200e141940514048405662028040e114151150300819034890400e1920000c10220b07980c0304900d240d00d0203090000d00b900c00d60445014440400e862502d480000d03a10508030030b1011043c60081410403038031008590040044c00a09481c128100401590b41c003060707888800010285612401103aa032000290080e07000049042c40680039409609031a03000c140444a01c1e8010703a003041e41c070020071105008030440c0001800c801d4a1000d9400815580d581c1c50304028060b10000c40404000211018803c5070b4003002050014900029 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 849168219 1250 849166969 849166979
    0x904080f07150f0903050909190507030b090a0b030606060c010237020c0a090e070e130507080c03030405090411030105190c0c170304080c01050c250c03080c1204 71
    0x440500d210454062414001c03c030b000c110540c450400d071a82c0544070759103894601c034200501800700400300502c091306070b0703001e118900759485510300c58002078400103007000418040003001d42d4010110b0f90351608107481103200b62800302e86c10f600030320282c2c3c809403110354100301d05029000e03e8038640e4540c0c4108007a050040c682d82800c1c00704078030030b0300c401e0412031031600100d0300da5072151812600072022041c104a079a0717243c2e1109803211859010754401549640c2103800b18502559441e101810030701848051010920155008205000c002c0c07202c0c007c4440842d4807400740f84580e034461b40741c840000c4e083c00500c403205801054000c000300494644114585a04818101da07404401d2030801840041801048508145500060945e5038660101204aa0799000030012100c2c0c403001c0c40300d031074070450034081c060085d5052425281c0f40d04400e0014444000700c0c0c5204102140706404071004150403046003029a5000f1104680d54113031410510318005184880c10b403407070780004001038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 849169469 1250 849168219 849168233
    0x14030312090c0a0608090c06180603090a110619120e0a031e0509060702040f1e06090c090b07150b060c010603120f021005040314192a020904080f07 65
    0x2a9203100f100c488903596110b90044070202405c5541180c02d9020781d9041c1d19501d001d002510369822140101a800c60b686008030307907150415141c01c20141e020030410b6041100c01e000550410901380c81950030700446141c1484400c2920030002d050015900704205c94800c0340e080040074808000407901c2011061038020f0111888501c482c1f9050741d103a0001e404d0710b2042084581c2c9010040405080c408640c00300001024161300106400d82d40381d03180001c0c1103040c0405002c0418035107000a00c541303058104d00c2514100e582c1c130801c02c0b24080090080100c004180d4174101e4000348824549040c1501c400002d1200c0d09149a0280c004208801196415045442940d03c603c0c0c1c540c0205002c00800d981c0c1e10003100005025801034180c03c00001400d1b0b103c42c0d4002c0c040c1c0b4054145d1450b200308882c180d4000070494800c0e0300030b03248403241160000d85058074690445010400c490051742241d40608000714003d01c9420740c0e8012505121802080d1001141c41c203044035034615051404070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 849170719 1250 849169469 849169483
    0xa09150509040c05040536091e032b0b03070b2a0304050108040303020f0414011106013501051003031815030209030a0c0801050703060902070c1403031209 68
    0x1e407003242080c00940206104000f550300b2244064075030040440380f00d038410503920703410f0b08092045140350301c540d00e03080c2000400c40c026201d40000d407031065514460700d2076091406514a106038820040c2911290300c08500a088100500300e40907010948403814001d0b0205140d40c4c0d525118031040410001070f5040208041b45225000c14640c01c484030304000c0c0d03010721000449464205110400103940561043c0c2e07400b5100b4a0018545070a00d40722050366007081e0003d144031080c07424060702c6941c0103078441307008a4100340107099541c900303000c40c5000760803070b90500100f0003482c1c1d41710030700282d0011041c0c03d00c50100090040f4513105200e030000c0740f0140b00541c0050b40d201c1c41180311594000c2d47d60207588000350320411480d01c19a05401a510041d820354041c411503000d10042400e02408402402d2170030000b148904105100806846441c1c210340503142c4100a40d2000900404406045602d82c0b0380c21400e800b41900003130b04600858058401000c8401c0400910b00300100b441 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 849171969 1250 849170719 849170737
    0x30807030b0a0e01060507020a210303111204030f020f070b1908090604020904112710080304030b0604020403080705060906070c1e05030910051801030c090b0a091505 73
    0x8100c01d600e0401001840ca1030b510440300c52440540043c402540300344010510300c0c1c0040c0009c001250745000101c20001d0b0910074071500c00800210a0270107a02d400341c00a100c01040c0618144121250300031340c0c10601030402003d01c41d1071300301da4681a00912140200d070881c40295151541d8480596400381e01600d0003207019803010356003642c0e10340105a40c07402a00740c40c009081607980c42e42030091044c0060010785104201483c0e06a140c0d6078442e0811070001100150f516040f00c0d009006c1444070050701c200c40d103d000070400d1142404c00000c0c2d80480e030304000710313450701d0300c2e074402050080c403c2e41c00c09440303030900046c140c1c18031400081050040354603404035042951102e0044502c505d90f41c0c402408050300f007000b100110713881c0250900b1035000f6425245041c04200004400d0f020305000400410b40124038190301c0011000c02521010003820144103180e4640001045401103004083d114840450710307454842c42180c0034030180081c1408101002c948101c01780c00c5400c04010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 849173219 1250 849171969 849171971
    0x5070501060b0f03070311070210020c1008011d0c122703040506030f15060c0a1a0903031603020715060920040b1809070e211b030a0f03080703 63
    0x1c0042e000b14540101c1d643d64161540d40d038155121300314101d0160200500e10740b1301e10f009008000150780d0382042c008464620b5001000b2144c0d0395410310840c5030007018820103110428004001520300f0203150410540c1e0340c2400c428580e40d841060070b450080c1e0709852011003540c010010005c141c820004140708a0a403001c904001e11040c07599240303d80d00400c0d4000c0403d1010408815590b1f0181d0740040c4000d082e122850750420100308640c0241c012682290300c0500c442048c803901060344035a0103100c1c4002c0c801850900c01e0306a8030f00c406003850900b00349801941541c0342c072a40c180c42c0b01c2944403074940000360020100c14003400103070007200c40c094074150f10007168030560348025414100c0584000c2c2841c2c42c00024260381c1d041000c003a00a41600c1c02030741e915a030b03104181c40c481d4290391600c14200601354180140701009a02640c1501c03401d06200204110024036108600646419003442003c1040802d040c01347c510b04c000c020b802142c10407410036030410780980c8030300c08a0760 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 849174469 1250 849173219 849173231
    0xf1e02090a0b01120c1209081c0504050316020117041208011e0902220905040c0512070504090f020405090c0405060d1e03050717120c0406021906110a05070501 70
    0x341c80044a900240050106400a4140c1d0484000760003240d00750704c184c00d009184054030315603d0251040f01c03a08445403600024604002003144038a00b081203e03102c1c040005151540c0c482c0d64a1103031310980c12011412140900131a071003111000b801041c0f0324210311041c1443e1514891034800461180003003208003002048481121080d500081351100c0c000381c3c460704d0f18150800947c000000c40d0525030046001246c1c1c0c6604010f0a80140498403000459207081d040052062160b030b0041c03445031112640c1130741c11440000312103060b500d049a0000310050607203003420b5141c4000e10000e42044c00e040030030644c000302044041b9080c00580b018412683c0342c20805c4002410200001c0c80c0c41141c1c6244002e22041074801c03507031244642050f925245d40c4d6211401075445856003002407030301c001071100706103001d802c0c00c6801c400885a40c0d41007905002e40652507203101c0d00e6402280c62040550070a0202507000f03080c08100e01482c0c11340d281c501c070400410381e6001d0603050b600c640c01d1030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 849175719 1250 849174469 849174481
    0x80d080403020c09221104020403032006010e010e130215030603010606140a1b1b14010912020609030c062d07050c1009092c0c010206130f1e0209 64
    0x400124414021a109176001c18101c810910208001440030389182034902c8006200392140d01c0103102440c0680c841d10030b08800d130740160030055041c3d5003012a6030410b00040010540440b41e4505444207031419035903640c3e9910081445200101000e90321001c40d00c040600c1020303650045d402038105800030b22000b40c80e20340544884a00c41c03c0c81140510410401480c50710495846030040b078604600c01c08441c403921a0240303e071284180d84d2140c05d03100c100b0080511490070072014520f080c01c100c0c1d0b05501d803803046421310f10141030280c0603040c0010f440d1800c0e80e040c06429141c0d81c004104075104c2500d80c16454110102010840d543e40b503044070070f94061003c0041d00c65080c0d00a004119040c501c2c020302020120031500102070184408020814441030300410765556940c0d00740d02341036040014a8041c1005100208585400c010071440d8107980c0440e40c1640542d4411080350001c50034038060744000403240c0c0280c10300c4150b840c42c0c0d0704210144c841c0102207008540a01c1c054580c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 849176969 1250 849175719 849175729
    0xa11090601020c0105030a180c060801080f06060f0f010c0212100c03050606190203120702150a0c080c03060607240c0203032e031506031e03050904090606080d080403020c 75
    0x3c2c56486000c900280002510000c4c1500802c070118002c3c44200d05002c11907070303032003103030b03c000c0d0402c1000c600e83c0e40061118013820407605a03000000b0000703101a09200c1c0110310b4080b03d01e545a4000c041c1c2c07880685590340280d882000e815400303031500c0044240401c00340e840b40030f5600c00094503400c01d41c45094580c400c0c01100c0c0100b030020166450243c480c0d8a2410340402c0002d003200350f0100b0f0101039158010b500d4124840c0ea2a07802400841e40300b009030100e010f100404030701c1e80900c0c2c610041540307640003c00c0343c0e0203526a4a41d503540d4880b140041ca8038000d120008080801c290308844500030700002e06140800b030400c0610045540c007000366124001186d14480700c2c10300341200000d035149048540380020045074000f41c0c9644035210700c00c0300f100ca14000c64000fa1900010010801490000501058901010b40c4a441c6568000300b06120300780505109546600c0208280311007940040000d2a403182220000e40d40b000c805401c0c4501203034190003600038180200c2460900c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 849178219 1250 849176969 849176983
    0x5010912020105040b090a0503060709051008040b04030e03010b0409050106091d12030411041812021b0402130b03040f141b01110106080d23040503061b0c0a1109060102 74
    0x41611454101800c03d083c84c0c1d41e9800110300b4a1f401110aa4000350a0f1010b00040b4098a250f43c3c0c2d0741c080c94201410b00c01044010303090581001254000c10010510305070006030403d9041c5020194039060b007000070302403c03c80c140568000d150028081c00c1290550000040f2040400140002180110700001500019110f00110340104400b0000c0c020208021540320384152050120000a440814200c039080c2c5840402c0010250403007003800100803020018aa46100402003050300d101c45a0b020480c0580300390042d40c0108040744100c804078050005003e0640b14140c07249420300304021224010003040d558800764003000040b80d600807611440003801580111250382d0304000440c3c841d81c074620b8140300f55507980404185001d040c0541501c81489a403042c0c03e148002641890441c80101d4441041c5020801006152030200d200b0350310000c07031640c40b005009034171403201d641e100d0300ca003561841c0250001103003040b0707000804010189040c0c41c0c2c0030343d55588400590703071500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 849179469 1250 849178219 849178223
    0x10e131a09070e0d06060b0324090402100c05250e09030414090a0f110a030e0f0705011b0b0a02041409100b031306090809041b05030103020103020d02190905010912 72
    0x90300240f01441c038141248941c080303034418500000d4466403034110712160340054903000c41441201800340064480303031ba01242950310885100500c1d041541c006600f241f50003101d40e0a10140030704107c1800700c02d010b50205203e1140d0f5160745000b00404400700745111b0300511194107a21004100200c0000040d941511007072068103580c15525420411040401400300b1340c5c1986a0084a407055100d002c0c000070311040f0302c80c0c191503411260000c0d00b81c4058520035901d90748814418600c0883c0040c00000b101c00a00344043c02d82004000712507820140640134080301c46200902c0b13802c091a500074000c4810800905920790103881c20441040c100350b0302074000b020001428000d80000c00c000715045078000e8090204190030b1340d2136100b5211580800c1d03a10180103d5000d40b40c2c00c290094170002800207440c0c202400d040c10003d0414003040c04041e042590114485101154960445041158688550310440750250000345211041d0040a000030084900022410744100d80c500c0826 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 849180719 1250 849179469 849179477
    0x50609071a072a0b12160e0d02060a170906100e160e0423040c0504290406091b1205060102190c030803040308160503070c11010e131a0907 61
    0x203c07500f90040b0108850b542c1e0a42c003007a0705100018412011001030441c1404014086070b5450704030080b00c04510500c00c0c4105100311040409002d40c2d54141d91405958101d8150740c42e00b540344400c0780c59030311400c02c100d210007051007401158400041c140340319485d1001c050851a894100b4044150780603214148503006445214400600401c90707035008610103440065410f4002c5501240368840340d40030941481c40710180418810060002d60192105440900400d000911510502d0041d8141083c050140b001442650307900e030342008004208118083c00b02118100b201240e4598100300c10002c6885070302400180029030081c1c03849601e058016040001b52200810668420100300322003811300400003000003030700c0c1c001640c003440c025030341c4160702d00d0031058105504c0052a8541e090003014800c100c41c096004000d80400781e80842610301e80780c0e402e40145d034800040b4510681c0b011082c10580c5d05aa125800f03110f01c1c40900c08904154001401445000d0006440660001e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 849181969 1250 849180719 849180743
    0x2306040608130803011e080d091802070c090e190c0b0d061e050a062f0a052a040e060a051b04060302040302040c0206071e030207050609071a07 63
    0x4640030304a0319030710180b00d441c0c81d0341c241c1caa40d50b12001d980c0700341c01c440494246074924440031500d20107a42c1c05004c000c0d0003081ca50541001c0640031007507038031039421002c0103121104041e280c0c17901034030343c01580a10200c001c50345071111440940784043c5004941d11036401600020045c08944108041d0445a200d0301d0754103085a020300c540c0280900070003143c8a000c001030025810301c030f070b44400c2c100c660740140c01400c100410440e00d41541c003100c00c20420300d41e00b04011594808410044662104100a61a03040401801c2803040c0e9805422070240890004114030003611130501c11404022220407007410408000448111203040c40d920b5025030001012640b00c0e40c01031fa04028416030802c0000c0100001c00180c2d881034000800283e00442d003002142040d0046a06280356800035000c2403a1110703005113050240c1c91090099200c3c040d0007010329000c3d42c12141c0c0c1c2900501a2401441c01e001c92542e40c004602c9040f0400703040403007140c4050001e006036031546901211032028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 849183219 1250 849181969 849181979
    0x90b0c0c040b181515040e100602061b090111010218011e0804171315170105011224030812090105010308030a0902211b010f0c0303020f04091104230604 67
    0x2101380100300160410220500946a050600c028100924043d07288942d42d142000c60104002002d034080c0041d07600a106022400031070f1213400461954820311030ba1981c0003600102d5075503038021860241940700041c0482071000f9817030b0005c80f9040030f03240c280078940940760150849000040200001307662102140001384911100d910b0444101d20041c01e10303140343d443c0c680300343d00da5001d103410340c0c4025040c03e0b0594101001d422022261441e00b40705601d0400007800300b03609191070342da45070364499450444000fa55007400c141500c880010320141d80f286040d0b90345500c594854916991458005840701e5014005c2c02d040ea9072040c0c42e02c2c03c50303d4000160340030340b000040807644407007002c04114600640340710b001c0003032040394010705100148803018190241c048501a041040c080701e46c0c070403581c000500c444604d90601e00140c0e94580d221400c41d480c051504054401c5040c98800c8941c45080c2c03010b0b00c1540e681c440900080d0107440c0300005049078164845402000c03e01c41001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 849184469 1250 849183219 849183241
    0x5010f170a0b1005030a110a08060603070314150a0503010e0d050c0106180f0507020a021021020d091406131202030c0607052a070b0307090b0c0c040b18 67
    0x180240e01c1c004046501d411500005006902800c001d07400210301100704035904100b40510b0180c4c1480f080518941110504000d18240d401420180a44000008260344510a40c003034842e459001c0601a05420804000507a41ca010f00f0310710301c10402d001d0302003128038040c4501e40e40c07002000d0041040001c40a803c2e40c41d40c02c5219240955561010002480902201c04503400020900000340000c8032085200c1191000b41c0b9800456201800d900016255150400d02841090800584410058035403600024508840181c018000300c0c0e120007542c25078110741001d503c103c841d6031806400080040d640d08007215030440a0150410107404240b840e90904500001881600e01d403420801d2204e20f400400d59040d000034200064402c804082201070a00c0b150211a0040201581d01e004a50707503c40d070b000c0c00c00996030000100c5e06207400317071178518020501c0c0e01c0e030240c4a44403202041c1d2580000e40019002d9410442011791514029101c0d1601940c40b40b00081c0c0c039198041560 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 849185719 1250 849184469 849184471
    0xf02070b092806030203040c09021305060309030c010e030a020f0f0601051311070f0506060a05090a0e01140f0709060305460203040203010b181f0510030509010605010f17 75
    0x40100860885160398441060410300e02904150304d000d0780e42d05051808816807000741e401100120b1041c04804507010a083e110b000f03c850071a5200c0d00c0744c80b2510120f046100b10513070580c980d843c0100102e068034005c4050300c4994015001d44a014940100080e05d80544c44100c54140c0c225400600a524125490308c0c100201d03907a002485031151001d130020307640011001d548400d0040c10810802c0001c1140641c01501902c032030f00310901c0d180c0401c0e08280003a0207492207686038421520b424009500c80d08a6500740e850301583d9042c040f901c42104402503401000040c64990007141d45402401b0f02805106a12607040e003000365040c443d0310701c100c0084031340c8020007003c885641100400f0307081c1c070440c205203038016600d0a01d44101800c47e074580c0665406007481011441040a401402c158420601c0e80c0603035060907200d05a0000c0f45036900240ea22541d500191000d09a25278081c2e4810b507110310080100f640c83d0401035881000c014441e40014402010144058007104000307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 849186969 1250 849185719 849185749
    0x70504081504050307232503200d08180405040206040b1c020418230c180d03050405090f0c0301090213150c12030603080304030309110d050105070f02070b09 69
    0x1517410010207513240183d5a800340321282d005000420200031214090180001407179a0040e9500e0001c50158a250605800d1001402c9a40801380d0b80040c810030303c8440743e4403030740140120311449091814290540024039654500301440c031401a060600d40300c2d9500446d002860320381018a0a0b038640c010381d01c040d50031020f5110050003041c5000a50014101400c920022400f0102c2000e00540441c0c8010112088500c244070f40d10300304410901c10707590420b58054000340e4426003690500b07400e90068a0540d0415041818071040c1a13000c00540191601161140c0aa4a136401011030051065034894a110010030040120903519401000d0030040d000c080004180e407109144a0800b0820080740850440c0d540e0804210455600088015280c10308101150170358030340c4400c0740001040102810b544400540c00e20001d0110b1040968006002400549442c0781c0709002e0f203000d03100c81001c50441c00b0359214541c00820400140d0301001ca40b0f90604880204200b1003c1100d520 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 849188219 1250 849186969 849186973
    0x1c05011d190924060f09020a050f0a0e0411030601021c1b0602030f07050403030e130b09132303030f040c05030a0b0907090b0303070b0709120309050907050408150405 73
    0x184110354501d40038400300a8000c1d0401c4000b88424000e50b00303a01d40b8069207403410b626004c0144001c2c00201c0c0180305a80310f6131001a15071000c4c00d420350312403042d160000004200030410001007a40300c006140d400d981550280807140c00c8094120090006a445602680042c080c120105403460010012065a4a48100095001e140070940310f0103620040e41c0b0756400000700a10a621122019003064030345c58800d2a245c81c68400400341070034031034018407582090a200100c0b42048d00304c0c80038940d004114200504044025448204145804690491401c4002c070581040b00c204c81d1400400507010310320f95910f0300c48041641000910480b603e804031310f0041400c0c1c50400560400318400d20304545181805c08180c2e2501c0392a61051840f942052181c6400c0d840110644455a6201800070040d841c0d05400341c0e0285001e03006603d0a400700f01c0c01c101455840104030084507400d075510803140d00d5440e000c0f51140301d54011070660303512004402094004280c003245d40300e800394003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 849189469 1250 849188219 849188251
    0xf031109090c0a03050c030c0a0b0d020c030d06090f0e0d05181305161106071e0201242603040b032e050108090109111306120302031c05011d 62
    0x40010000c41c0b0325002990141e0100406c541d4904003005041000c40c000c4a503041280e04d00041022148245a15600400d4003c80e40701c00c0d1039030804c141c45240e80c10040c00d0202c2c90320307482e030303100141010203611303891500b0504503070120130010400340039224040c1c0d10186084050038050400c2c940980340c454009000f2200100000c03000c0c0b04150041c5a000d0701681340000740715000b080c5440003104940329820550030701501ca41c0006c4c00da00d4540000a9014103c1c114410aa0060110802c00c1d8281d110004950356000c131204071034810b80f101c4114058140c1010062010241040e0481648030b5104100910409803078801541c0e000c0100d0b5680482d2002d103810401149010b4070514400d0700c0125018800fa68100907503a5100116900820030b002d55038070381f0405488a030305040c1c000d6508410001c20050690031042c060405403c48034101201c500d00255a5444200805140f10900c5c200d403118105c00d0007030b24102c5002d100700c000744a140c00c041030761508000d44503807250b0700707104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 849190719 1250 849189469 849189493
    0x1f052a0f0c010f0b1002010506030a060504031b030f0908010207020604050d1704090f05132a0b040e220b0615120f0103060506030d1e051b030a02070f03110909 70
    0x4007404000f5411007901003100d22800003440200500400043c0659040c40e040110303e460015111892903000440401c03186c40d02e040546d00c0660a0315003052411441e10781c10107054000025404681d0a903541c640c40644e1405460300300e02071420300a40c0803204200411203444c3c64252412024055200c640c0e0f6401c030780c465115554020303031024801d580c480e21a4032203c1e80e148a10340d030284800542ca145a1020303620b1840c03000d1141e0600003c021100010001ea0091000766406071036480d41e01e641c2c541d00c85481c48041c0100300c1703454011210f2011950107000d00412a484815844004015203407a400100a03015201148821004000f44444601035007030513500b600030703040320f003445000f0b50560a1100542d003000b00a180a03070700c075521024005910944103072400c80c86404440d03e00410704800c54461003100c1c0b4001003d00214002d070344040b00400103100e101019004c440301c4669032045100b442415100240070b0070310f2603070009001c3c1049880c80f0b5000407408207481c000d000721 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 849191969 1250 849190719 849190721
    0x9021216140403082107230f0910140a02011b0c030203040603051b0f070320030a0c0f060e0d17010b16050f01050108070315050c041a09031f052a0f0c01 67
    0x1b1101080080e030410300314441c07002c46140880c83c0c0e2024800c1189488404401d80110744298010103015000d40380a920407036116a400521754a407217071405941d103004040c000c0c007800d29040e101700010388032a044603c1ea4059803001801a60503000346051038580302c8192300410008040d0001d083c20070006107080d074444001050a0100c125030b8507140d84c0b01d41002441c0d0400080d0302e18120303580c0344644402520010076915020700501c0e0400170b0706d03440d00e044801c40c03d100348010481c0d81000700e00c90022030b0110b0043c0551105548031204a1072000c041d0947c420300b0b04c81c40c0081e03902000040e41070207149416961090240084507841c000324024039017190300c01d900c08980c0d5088150140100070500314842501e1400e0f20041c002804c3c541d840768030a03c1240328180d42d08403000d081c4110000680141c03041e21800506aa9410003403444559200300c403824140c401a2815002401c075540c007a11088400d4600180186580302000802106500902d0405e00501040c000c003280504d003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 849193219 1250 849191969 849191971
    0xf2007090c03050a05271f0203190504032a0b0a020306030d051207180f0801090b090604050c10030212010b04050a06050301031a060406090212161404030821 69
    0x8004002903450075a4030001c080390b1010703105110580c03c06041c8458442c20060f6104011440320f03881d60740020f44880d40b0318182d0489012140d0b42e41d860004584441181c0c0a14440c00903a1054a1610700e1030006100710b610880380100841c002d258100140c030407160702007242410000310200b5015050301c8048000d0f20444855416540000c100036403810140225819440070b81089401d02103001d202078002c1c40000c0c507a42c1003210b408021001e402102d45558010244c4ca010580155140c5032100c0c013901e00c00d0340c10745848912101007085c42c02c2c00a48144240c0d0000003034000c0032104410424a420700e60115420942c0902480d041c1c2010005614001e040303071200c03540d4480c41d20040c0009650385502a03014082c0174001000420b1484000e00b400196419044a80d9950307480001c0003840c454100003521480482d10300c0614501e0400c4034000d203c041103060b200780c110001145d40420f120380007203e4074814407041000031154000307407800502c011003450038064414400119820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 849194469 1250 849193219 849193229
    0x8071505040911161211030702130f0b0616050601060e18060118080c03120304030203041418011508060402040f0b090301181a0c0301121101030902030706180f060f2007 74
    0xf5208140d02c0464101d1150101036010700051400c1049a40016480d4ad401151101e41d0689600481c5a0001c0f282c2c04112102802400c81e0b0302d075054442c12445d0080081001c032541e1280300c0000c51110f0040c2c01c19800c4200c001c03d420601c900c4044d4217060824054035080c1808880d012a001d404031201002c000b030030300e03c4003d00070441e405d0101454004004140403062208105010110b0b03800b0040341c040d5081321103802490810301001c180070000708892010f09080010021404404800480302020456a17030580143c0b204010402284a10702c9800501c0040d050104004400c08000d0300340d034000140001361407180048922449150f4280440707900074040b010308100d103188040250009101e480f0076095604000c3d205d2031140c1d0410002d01483c584030000d10700e980c441e400640742d4541c00750655041c29038810018294401600d11607056507561030000c10300d500c0d800c00c0d11044812598400700340706003a007819076050350f0344200060b00303043c1b400d4814001c0c1d104000c0c0c075008207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 849195719 1250 849194469 849194483
    0x513020616212316110a150e0a05131d03032a0306010215090a061a12120d111611091302101121040807150504091116 52
    0x6410003400c40c94a032503034030900b03810071400c008640000000d8800120071302600ea002014242070840002142e0114142d10480980020850109003042c4600c03484850f101c0c2e5440c1d0a200e07080000c46541400b0305a00703d03403039118040c8512410380180d820003503c8005c05480040c4040c04a0950340f0448240801e4001007101c1c030303040100041c503616600410b25040e03045040010000303449488440916900c240c500020994101d001d1107003809040e884201008064008002065801d4006d40807074450050518079200b0240c01050180891010940382450000212034060082c60f03d105400380716a0300b030004e18000084001400b5400c0d000d14840d600f50081c03002044840840104008801805038611000503211102000064440c1e424541510300803500000d242104803010040124803401200b40080311080c01803094691160031788448a445d040100d00310041e141801c0c0009004120400070004940d000241009100c0134180c1f802031004003090740d6000030741041e83c8036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 849196969 1250 849195719 849195773
    0xd02030313062a03030203072f0601050103150905042102010203190c08070305060402250b09011107150603060207060b120f0d1d090117060a0513020616 67
    0x469007245100400c8014540250f56030355a4100101d0200c4442e040181856008004143c1c02401540c294544056842029030382600310032400040f150520103142060203040004a0154030a005011b0480c00807480c91100c0d6180c0600d107401000003c0c02a2a401405009045180356000f200503a010300c65002680701d0070442c0c0081c5141c0004000e4031240340c9400310b1200c3e569080908903a2281d428180005e042d942d10b00410f01a11a0443e0f12082c0c20800040c40c1e2000b82070340007030112130700a12469006a992040540c00c0341c8040403c44054001801105c0000f03100c0d01d070314031504e08000c05c046200307a5a0741d28001031f41c119400882c0c03d5921035907901580c0c10150b100c0e00007109948001d00b0139803018520700341c441d40d200085000300030041450982c0040b40101c10912080b015040310442d40c0c0d074405001007207000d030320480858026800440c1809606014990051340c1401300c1c0750316000c3d00d40c00c11401b40d021070910701001c4600c401c5c0c03c02140c1030903803040c206100c288461b481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 849198219 1250 849196969 849196979
    0x10021908280f0509010c061a04020a05041e080a0212010204030b13050d093c090e06070c150e0c090408040501020706320d091a0c070218060d02030313 66
    0xc1c2100c050125003084004d0062641680e0312405a181c42604403d0010300c14a040183d101c0404005040c4d580250000400c004010343c00710080c003c882841d003030b030720391010240d1005080304150320075103810b0b80c401c464035005890500d0140c0741d24035112000501e8540d4036038410303400384001c03039000d001a031945480405108050094407009070040c40e06c001002c0c10104020759003038442c0243c0401c10034617240d42d0104140c4619840700901d40c2c5840702140e07543c400040b4041e101c0542d25118900410010400715070060f840118815400420ba8100f1030300245210000c00c26894902850300c22803070141c2c07803900e8030340800c0c4c0124010a080c595890802c00003a00d0311520354409400c001940d0440700c049984400107903005ca0301344c644900c02020320030986165001b00003072107100620b4003581100704201e00b050ba8440028000d014007080e520741c05060340078019404040d42040b0b2080307800c001c1201010300713181d20640007401682070b100c0b60303000300703186400c81100d01e00c590500e05c40a00c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 849199469 1250 849198219 849198227
    0x20a060606021b060c0d0818030d0204051504210f0f0b0403030501080c010207030f110a0915060503061c03090803040b07051606020a080c24151002190828 68
    0x9400070054504600c5c0034000c14401d5690205072040e0702c1004100804118940b440c00c0403401503040501c1140d0300e0f42d01c0000740c60020f41c002d10034144561980464000d03010070241c203460489541800203482040086c00382d0359003058159085400a2200e0000800500c1400c01c0f800c8960082c085400b0720700e008c2c0b5003d412504180c02c4401c940e84502040740d460b0ba0b0001d8127500341d990148c10802d041c88240b600030000c3c0b190b43c0e01c081d805481c0820200781c1072040c1d408564450000b2070500c07821907442d0002e035511310043d91282d401220b090105014180305800030b801d80c034400e28151031080d6880070401c0c1960080d8200d8200020b000460201f07104082151440c1c0c000348880390100e05103416006542d40940b000014600c04c1c000c00d410301d071800288160480b03460700f00703c81c540424054222210070001142d100b88400c0160b058808203003450a40e04010310529001000c000003020b4a040714150810b00849180008000d1882c3d042200807a00c14900701040b6001d82d05104d54001030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 849200719 1250 849199469 849199513
    0x405010e0c0f011209080a0206150d02010f031a040f020d23070f020304080a030509040c0e062b0e010e33090f0114091605130507020a06060602 63
    0x800650310401c1200380c40d5884030900425071009081c4000035500b0a01d010020340266071002d0700110001c5401445240c0201e0041c1c859040400380b031104003100d900300600b0600c18031020340003e9402c100c007180c0368080c0c9d200101c80b041c408814444044850000b4007501c40240300d03400b41d41d0300803a04521240d80d50107904120007101d100d00e1aa803030041c1400320000e4005043c80d00b000100c0e00c0d5442054003d000311b5010303141c010305842d86c003205824090701130f611072004180140d240c103008203410703482100c0c1d800c2c6d0400014903151601d5000210502d00b043c40c1100080041040188650301d2940c2c0d1240c516268100300002c15814944c280d018240302010ba00310452000d40e001d14501480c020000010860a85002d18001c0d01d0342e441152418501c26140705141d80b07401c100154100001104034802e903440c00444d0380000081800c01c1050825118141c1c02030320b40c0c0010000450700d80c00065000700c541c811280101c050b41c5404040d54140d9004401503000880300c00c00c6030082c440c060f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 849201969 1250 849200719 849200741
    0x3060906030203120f0417062409062209060506031207121d03031b0706091a03040503120115200a030309020609030d030b040e21071a01090203040501 66
    0xc001141c41c40c0c0100f81c540094250000380d201001800100414048044e2000303020305007050450200892002540e480040d0398a090708811114240e082100c40040010140c0024000ca07519442e0031092101100000e040c40312540314202004115100c10f10450441034042c002c08100c1d42030400900d424503a9207030104a000c001000f6035008585103000c074011481d80b0703203803040e1840032070803003440440d6000003140d50501000400000100c0c0c40c14420ba413001850007960900c5681302000c0e16094958410301d90341440f02c000603010b00c0c0101e006164040d0003101540c1c0780ca07020100000d48180241c110030052944011880c6065500c110701424000004d51000744e04004050301d581d03161041c80d401810151917415000c00c6403200d1041c2c07201004060100c2d880803110050213000381c544c01040e5401540b40810800200900059041d100e001d01444dc0c00c07104034519568180354884001903403181020801c0681b610011a0700078020548940c0060f1641486d15000b82520819014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 849203219 1250 849201969 849201971
    0x20403120305040224070c03080c06220f0c0902070c080d0305130f03210b030c0603060a030b0c0c03070b091605090c0a120501060908211903020904050a0b01030609 72
    0x10040141c4511003e054808002e05e00d0f0001d02810300d002690b0b6215000b0020500c00e004c0c00d00004111881000e0b01d030000d1982c05440c481d40e681e00d40700d050010103034040c625007000c03000c4142c04581c503458506101c1c1c0c01400c206012031303141c00e501400e0b40d000e1001200c50300101303401000816010b021903604448289420722507401e20503420701e4110241d8801500e044644591749003010701031810440d40300343c0c0900c03107121401d5212454000380f04104000e4002d005583c1c80c1c80342031818804882c4940c80007818003050a00303680f1001c1030002c008104d860500e0b01000300c102850010800342c1011889402e00b42d400d844c0ca605641e0502c5015070200c2104114004d09003c603540700020346610022400100e0307203c40c90f00e1b0089600401c1070101c080da06281c44001320740d03da40a01d421303055521010450304e21000c0e00d04411084403003905000110a405d0281c42c1c0c000c207100d4444184031900d40303400340c10a0301d1400000c040300c00c1919961080c55070b4601d031a02e02d50709070141500130004500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 849204469 1250 849203219 849203221
    0xe060907021c0f0210240503030c1c17040503030411031902040b19080105040209180303011211040c0201061403030906090405041b0603060302150a0c0212010e010f020403120305 78
    0x1001801c400b80c42c0682c2d0040c003181c0c0309550141d0b80700f001130340c055491901003403110300800501e10b22040ba0445503201602d450306408134072400c001040f2980503240390001c1002c4206420a44402d07400c0c0070728807042250b10008107042261551011780140e002c3c6000e9581c81c00e0910704101c05030305490340075000c0d07006909404050b011071000070b074807130781c05803000300d00d2107485000614072070624180c480300c0460074000403608900c1540b10b1446648241c80c1d11103180c8620420200586403500d015140703920030070041c40400c44510b10780f4525441045003014039040030001070181e40d110100040140e54400040250300d400d03182d0601800016001785241680e00d10100303101e8440d00c1d69680c00303070b51207030f01142c1040403a42030f0107481d42c50710800100094903240d004014041e144826482540c429401c44c524504020490306e0900b41d64541c0c0308048481d40c04d000721401e20140000065580b11803483c00d110b400c0c0240d0400c41c145110059a035402c5144c44c08215210501c0c1c2c800300b524000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 849205719 1250 849204469 849204493
    0x30106090606080a0e0705370e01210204020a080403021506031b0d022107050108011202010c0501090c0f030201090806070f14090a260105041211010e06010e06090702 73
    0x80210b6080f13075141002060f01c05200455900d414201d6201c560041142d04800c81d400981c01070f25401c11201d58810410541101d034006002c56050051164464840004005007021340042030b2800502c10480b02000281e90005000c0380c01c400c07072200100345120100000c0641c14016509d8600030003011145034100700010030b030350b00c41d621185c0030152040c21000c022551a1040781e0000c95005108a01c3c0440060f02d001118440c03a03180b641520450502203450341c0140e4410781a18240f80d00d040320b50300c0c0c0d50011240610f4145045d107543d540d422030b00011811082800010f17005a8455420b500d280d4400140208100d510581940e00076034248203401d41d0003581c04050000178500800b00403900008070549201d54401c00d41e0010103014002482d000c220313010812520210f102c0740c107440b1076040031402c0e12000c5a000b08003204109901e0201030092141403164540301c80002402001210380903e090350030382200303400300588010800d19290207140e01c0d501c00c06520240655689030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 849206969 1250 849205719 849205727
    0x9040b0307081b010c05030d060602060f040f0b150d20060f0301060309020303300108010b030d210f09020f011b08070212010c030e01061d010b070c05031209030106090606 75
    0x7541c2800c500c0701a00f85105841e8811407035040c6980d0404c2c203a0359101e41c0a11b4100042405115031009805a2400120718004480c0f106101e140c0001c803030050280745948203509400010644030030001c070300401d005140c51344a01012a14420985010640e50600f02010000c20702c020032841443c0410515006060f0b13401517a044410f942402308002c0780c87d00c00a4214000d00603410788100e404c01c403006210210182c00f000e20103001c084400a070343c82c2d025241c00d03546580c01032505030f401805042d24a502c140c82d0a000c0c09000b0080194007424294100141c60701c3d24007164407181c0f00c2542e4802d62070a00b0001d421850709003080f41c10300700c41a150f50440d80004101a1a0271004a042819515108178100300016010001c101d00e106521016004140300c044051440d841c220010400400c2080c40e07002007403c2e101d510150b41c0c81c00c82c5801d034a80c0104801c6540300c0c00301c40000358036202000a509036114000106489451802c10b0500715851540068011414210304200c0c030340d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 849208219 1250 849206969 849206983
    0x603020405061e060f090310050a05060d03050712030627050c0412080a02011104031208010b040f05280f17031303060510210201120c02030a052203030509040b030708 73
    0x6880140d01e60b840820782400300d0107106d4002e0b806001d807509181050059502082c42010500404c00c605c1d01c40c0790621800100072000100420760410020010940c0c41100c3c2c1c660000310714002c24010303255801503901e91942d14402d40416030801074480e8007140340c0036495000e01e50309011410140f920800c02501110484042c0c0405000540d202d8898400e400010f0010b84009000d959550b0360720341010900c22912200740003c12141c00410350071304417000c4404681209020211080c20102001051001c420b0603941e580244041410384074005c1c0058001015550b083e0380c0e4561406901281201c680003003181a0b400030404070302e0992074004070308140e0307810100000c0d0b582d540d4000d640c0000c54982061405529074100c48040e601901e08410909d03200303903551170320b05c000c856044042d20a034a50101c05038206000407110140301d400903000e46100030070400350780c050160051400e50b02540003500000c05c00620461141000d014041c042c80f400c0d001000041e140500c0661a600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 849209469 1250 849208219 849208279
    0x60306150310030204090b01030201081e150f04360804060c0201110115170a0c063f061d0a02030606070203240115211e060302040506 59
    0x940480802c8050303003110302820107558007801c10040303160781c0e04114001000900c01217002607070300b40000398920056684910b001101d40c003038403141e40318000d000c2140b4449965260b00240c0f00c10341c000f110b41e254003c13001113078023026014042c010400400b1210302121214400840001c0d020140001c4204044804903052441e24000680351807004032401c10a03c054400f0303030341c2000d1900500f030600c080e101d000c81d115180b655841741f036030801ca15150008540c2c05805031036101c404001990192020001c400a00443d00d01c3c40c188042295041501d511501c4001c0074189686401c0c203452807180c4401303031072580050f1074185510715880850340b8008042750704642d00400800c0c59600d0f43c500380c07081a0303401000d48007858400060b01004000d000b0482006c0d002200001400b1a141100350446c4075581d6121010001429101b03800030030300000000c1e03030940d1400300071000106171840c181c00d82480c000c0440c034039146004000a0780e2004c2d01d00c44c8640e00d128501c100c42c000040d401d0031048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 849210719 1250 849209469 849209509
    0xe06010617100b0a030e010c180b16080703090608180309010e0102010e030703050304170307020307030c030e04051f150f0e0a0509130c0605040509061c150f0605060306 74
    0x19503582c0c065000301c2c0349a80040656040443c5484000e07805800510341044542e0081118400700142107504440031190065840e4140d11309224203081140100003000302242004280c1040ea591140341e948a9142900001c0c09640b00384044c071351011a00c0d4000c030581c8407081c10f1540b052074035905d03482000f41e01d6040c03150808461032664000c0d041001c140d0001e00035281c0b10b46440c00c0240007a402100c0444901c188891300229640340c00055034050840ca900950808030071b580c094403101c043e00c40035010300c84404500e03103440d40c0c0c40c0101031107800031984942d0384241200b85041e0780d4415404c44105004085003451040d0380c800d1046169840514141c4a0424580082a0f02e414940c00203900034442000700082e01460380309800f10248035411214a02d03580d6081202c813800345008040d40601c80e400420410300d80360002415070711014120351500c1b001c1d80e9a5080611041003018042511384070b00c000100356a200f40e01c010700c002d42c0c0f10351a5250500c002040e048100010050324 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 849211969 1250 849210719 849210721
    0x21203450a170c030120070305030a1107060f1a1e1201060e090f06371b0e090402060409090507091118011704020f0d051608010e06010617 61
    0x281d540e081050002c060400b4030585104018100644807684241d5040c001d60800c0c8035003869564810000b480c074170252801314204103191350202c2c1c6592001e4811494a40c50760074201110800b440201181440b94038001110b0814141510680c2c010403021000b89146044540450f201c85074842038034494100400400200310b00002e04a000c0d40088015540c6880400310350301c22001e40c070301c2c05842581c0881c0c16044a008c2c0c6c06035101c000701d8581c030fa60049985401c10100000060103200030715490202e190b901c01284141c1203448070403090076109400042c00300d0700c503008500404600801c0d54100c1480ca02600850b441d0702c1907100303810020b0382d030748040c1c42881001d002020290842c0761050200c0c03e4a4080d81f55550850860720581c00002d614000d400c0d80a8520b2144c1c0710709d41e0616403096541da4082203e058601442260401d03a2801c1403000034805120480300c1d14044407104516a00744038400e400c55480e014031124a920541c01807210a0b04814140785404881c0b0788100380e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 849213219 1250 849211969 849212107
    0x3060406050c360d03021c0e0909070302040509070e1b1b030d0501061e0c0c080111030907060e130c0201060324050c180d020d021203 59
    0x191080031410011003040c41ca003000d0002d200140c842842c444a18640e461880c1c400030401c100d02071202c0103000d44d01000301246103190042e1b100f44491008d0504000d50030b0204045540c040003224456a0394100301c1d010f01c01c40c030300352180c41e40050042d00104120790800420900c5168094450509800038050030901d40f1505000c60f40940000c80315080a00720050000d5569084134207005e068a0030a400825614825070010117441e01c0c1000d031600241032800700b560208100001910714860032031010031034107024001c605503001c0f042c0170603560745480b2400d981020129040351081100c00c07182110642e64983d401c0860007084a00090324040108040e070041100c2d82c07000b03103004101100020300c800d0b003084101c46200b4641c028092560346140181003803103080c0e94449207079040720f104122810f044488421403407010f00b8038008000705400040300b211000c50a1131065100260000c07402c1035201840045000c18a041c40f103d294511500000f03000030b54070314152122201c02010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 849214469 1250 849213219 849213241
    0x30a050a0503042a080c062a010609180c05150304150207170306090702010c0f0f05040503100603050d230306060904091202070b030609010b1c02040b12060f0306040605 74
    0x60552440b8200f40781101480310f451081e0010345c440c09605008a00c11060b16003024011100011980240e4090140f02000c07817074030320f103100614211559a07035500460000200d100d43c1e1410154a546003000c0ea0803450301004040c901d4000714041c1c1d500e0b0915218110f11a1f007582c1d040340d809841d600c41c03a05001d01c210024020000c014005190780ca45804513205168000d502507003068800c3c549543d65100c05900b071305d054403000c80000e42d80f03464607180c040c840c41c10b820b0075032a01d1030003524007552400003d1070440c4a483d200041a03450104004202c4100100c8050f0510390074542042200750340e0551a03105103050b028015000007001030680d55861048800364030f0010401c004107999424015502d94402c52a417003d4410a0808100e10b15041c007503078401c0400608540180c0c1c00c0860300750b07180d005000003a910300900458103a0a020a00250016101480b48a91581507200d0107010440010304828003a0180b025101c5480d10b012030034544c082c0c1c00c52000700e1141c4800d800e0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 849215719 1250 849214469 849214493
    0xc0f0f0d050c060f19020d1508241302120d0f080708010506160f03080123030a06020a170403020d140304050c1210090b01050a090b0112090c181b02030a050a050304 72
    0x1407004d440018411081d034099804234940220400440e40340c1c5442c0d0102c5030751605d01c032406c0c560a50b1010707104409914550702c41513210402c040080a1310f00b055003c0750300c0000084407641550013080100c500c4a0307002c090030000d0401c13450540c0c480c2c1850400504100010f003d100d00410000a03803064824101000400b0a03074010300e86117080c000c904004054035403e0140140c0c2000380380d010161150414049001d43c0c4000703000e00541ea0490b5504c0f4020342c043c810080900507604100210400c4a032500c0340b0a81c0280c01070007030b0010011004040c2811040d00d449641e20030f0045c400031400020340082c00043c10b80304000084c45a1401d03502d00354201c04010b410509003030301c000410880101550403684d0a807202039619480e2a820029180c0c11101d8900113980d07a802140c0420b060381000d00c0890265000305482500d591a500000010010399550a0345030010030410001c0200e242e0b000d90490710245050420301c1c00001d02c03a2066062a10820030044040f50900c00b03404965 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 849216969 1250 849215719 849215761
    0xb090111030901020304021f02121b030a0f031401030b01050d210215010806060d080307090b0d090b06030601290c03160b0c0403050a0210050c0f0f0d050c060f 70
    0xe161645400719859010790b01c111802c9000d00680b20500102e5600030305041c4241c501a001f6240701005d504800d9055007008a140180900300c0d281804280014801010300a103e80d0b075039a000c851031400174095550310415003254642c44801000400c56001c1241d06588040710071f8a1381a45600344a1601680c0107640d860351288110b450400c16000540880100c903000740702c10150303070b841c034400740c803440d0440700503070081c80e845c4d00c0c00e00040d0780100071680728441d070403e120a142c03a0009118990454101c603141d09640b0741d800002c1c001c07100320300e40d40240120000c04066040c10b0035080d1024910458610034411600e0a0455140354401e48011084130001c0300c0c1c4480c101e00e440b01c964211001c0c140d50030f014640c08512250516402c03281a690410b00402c4054659824404017405940050080100a1100350303002d40e0309001c1d941850705188020700113030035130b403c0c0f040c02c0451001c5d1400510104100801290070041855a400f17251149205041c4d03035000b0b00c000090303080f040c0d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 849218219 1250 849216969 849217001
    0x10201200a02010c08090d030b1306030305030a050a2d06030813060f09032d1a0612010b1c05070510110607030b0315040c05032b05160b0901 62
    0x8454210a039640500a01103403a402400700c0000c095042c2c800100950711500705401c06140c8030102d038001c1d00640028131016245030900800000382a0464140387c00071000550000188076441000c1d01902c0d401040c42c6404004c07214158030701004100d028035400305640300d411015811000a0b5000070021600700b49803507a241c1102c20462a81c40460081e10080788100041c0301c125441000300900340d90b4418104001c03144041422030401100c0545145d6001129417070301d0008001c90f0b410100c030300044140c85c44034101001000b00340d404103495024943c0c901a4484075503a901001140f5501e03d08034030340d507c550f0904210303003414510b40119030040c0401400b102c28030340c00301c1071501c0d02c020042a03d815484001080301171b01d4038000110350580c44a00c81003100f84d00e504d000c941142c41105036500303c940e00c0c0042824160b0b51240070360b03070b280304150203114810041d4050a009900d4071381107140c071100e4613808610384404035000d44503004020000f02881401d600492100c2c0100f0f40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 849219469 1250 849218219 849218261
    0x40504021c0501050a0c021908030406060b07060b030c0118090e030c0327010c0308010306180c1e05040513082101030b040515040b01060c03050708030109200a051602010201 76
    0x2c01e6406810203480442c0758503d050b481300c0341c0078804104000c403000381c041060301d4a181c9450f4040340340c2014200790f0741c1030381c0d42c440010701e448004010034480c0d203c5e41d00854101c03288010507042040303d155550512908c2d01c6c1c40c00414058610040a071001d01d800060700d042d030800c01d5440d500440802825600c800140c5503914005d020b00e044101001c81d03030b003010001c4813100444075002c12041c001c01052002005000042c51030304141e5964105a03140c44c11201ea0340c440000c000c000d030348007100e00e02c082c4010060303244100325404080c00c1c042d9000d014904004001c0c420040440001600c0d03048045010b51446811001010300403c000780c04014a503100d0800c005480f00136201201d035846042642c0340c000004016042c4169081050640d1036841e2540540720401521412020890200f00c04c400040c54000554007a00f80c0b1171000640b00e48510000c0c40400726000030b032010000504c020070105a000c800c031022061038441c107460341d40c880d10050f805080c4401c4003100d280d0000c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 849220719 1250 849219469 849219473
    0x60d0f080414091b0306060306030a0c171005060d02240408010c09240f02030903011406120a150c030b031f0c09030b0615040305030a0504140f010e040504021c 70
    0x40111208014101c030b07840400c0d04d4100784001010040725403201441c200b400040e0382440d18102850f848030340501502c035034004c4c40e039401908140940004581c01060340300700c0c04020003084110100307101d13080e00704041c0c2081ca0010380c3c445241517000784a0075087d10404a558003d017030701c80d090402040140d45950311035040b00d029111000e03120000a0300c02000044100c80701e1201c09080d00507490b1101d030805d4910041300c0050000d202c0e1420342c401004424a59102442516110507000c0e0380d2058604021041003003a16240200c541541d00c05024500407030942c5c04184034450000724002070484583c007054002d8200500940d9041c007170402164800c0505401e110082520001e040001300d50070b400544544a0501014080d0015080040c00900b0f095054076049400d130103055040a58964405141d5408800b40000080c000708041241d400c10341140005c80c002100e0110020701c041c00020700141e24000d1862040d40c540c4045401d5484d640458034401c10f0110007141c03c1da40c24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 849221969 1250 849220719 849220739
    0x1090207021504030f060b061c0609230a0203070207091419180b0c070803041211120a08060d060f02091c0b0412030e0a030e04140c03060d0f0804 64
    0x1069009038107001c442c024220942040b18241d0754003950003a1001c2542c4c40d4103004080c100415034200004001420341030786a00385071515030f183d40d000071902c0c0c1d0402c03100c5000d94800d05002c0c43d03c580b407500d912414101c1031a24540c40140d01c0001601e035035800004920b001c04c241e00c0041d61904d000f262828040c07028000c50b1040b0404039240325260030344420b050071590b034841c40c00403144c0e00c10400030010760810700c160340020389030403481d0615425449a20030390340103403005c540414180e800c240000380c10071801071000080501500f00343e545210b202d0282e200d80c11b603200400c40400700084581e90350314642c010054114100704540c0280d0b51207030000f9441101154450710b03a0f80006505110860300f030244d010b90210180c41292641c0c2d5078540154602c0c80b8003018140c881461f41c04401e0200503a0842e03034060307642c4040d04426803040c84100c03045000d2008051052904008960302c440044a400c0f034415074608003400e85500f0030002d440c491800003018140c0000e00054843c0c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 849223219 1250 849221969 849221977
    0x1401110a05041409060a050409020d1b030212011116030513090b03100e10020304030507050a06060e060d0308041b1a0403030216080c0f041d01050907170a02041a09010902 75
    0x901071001515520a030b040004d402c008440c402c0d40401402024045824560000300d40a440a40401c80c5031203140c0e503080c40f064500000f102d01d02c2c544d40d01042546882404244e001d01c0143c0200100e40c1c55600c001c080b44070310b40e804c030b0030522400d8031b2804041c42082211048000c0051449410340c403110004081c201d568031440c441e100706205140c21039254420803804940010041c9000b8810f2240c44010b500010f10030750a0103000d200c40f401051041c0104810b0134402d840018815040480c8448440d00c041c010a00440d20021201c002a400001c1c00ea00a0307001075451711804031709070309007403a40601c1d082034400c0c1065032140448984004007a100703892007070302655500200e0400c80303036245030244140100303a4400d00800c4040d00348a44050002913020348017003899110194030b00401c81c1c102000c400c00f42c1d921030170070554100030301014016000d0300c1100c960550866030342030755984e40341401900c615560555000d040460040082519001070162941e039a56070320b0a030000c0d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 849224469 1250 849223219 849223229
    0xb2d030f25021c090f0f15030203010806073911060a050d0c0c1202210301051315050a180606050307140705010e1603020411040605071401110a0504 65
    0x1201180710307458000c680c0030985601080b0360050084500402c000d03840868104200c40c24080007100128910703000c1203034800038100d011050b1803102e01c1c110004031002c0032291294200351040c001800361840115810390402601c0c907004050000d2028044007524800300b000d05070f507246404920b0012007603a81d4181c0e081c000d0350440d00d1000d0240c1881030700e00c281d07c10400021401c03c40c099000707038294010400440c9526204e0381c00c0f201541e601c03900e080210a8540564000302c4281c25080807000f00e0301260028194840c00c5524120101d80c64250106261504640b6100c0792842440c1c0404e0010049c0300003054056180d079988050710003030380011903007002c0c0345c2428008180c05d409a0102e90080400c4d9484404880602415001c140c11a0754215859526050a000110b07810861350b440303240c3c29406c90301c0b40c80c95841004220340d1701500009400b5000e000400a00b6084402e0312002c68005044c204031000405a05004020315000680712050128504c2e000581c8200a402070710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 849225719 1250 849224469 849224491
    0x705130e070803130e09030d0c050903010f0c05190e060708040e0709031106210a0209040b0406050307170325020a05040b03120d021204060b010e01090b2d030f 70
    0x40d4685205944a00c501c03903484c84410607a5004000402040c0d030165030089071001624209807581c0d0800c0c0a0701c0e61304441900065010502c0407031707450300f803292844e80da00e4107500b0003031a107403408098600e004848446019101c2055004151401a41c444a024400030300481c0c1c0d4107040c0c58500c2d015040b9000e580e01d2030170024000f4201c80d000d10200c07019a600300703601c013240604180420505a00c00070905503022070041040710b48551201055008a03151580582c40d41104002d03c012030302c1201e01d261045040c44001c000646002c5030801c1940c130b48540042c035001720202014030754401d240c03502d807003015026a400c01d490150f10718010114400c8907450b501581c1d4100b0081643c6038420349035455080800c04e400000b0340c0400402120b43c1005025003400c01c503100072240d017603045030700755203940c1c4581d0030500d00c2d030f84012032442031171090816280141c104030394800d881c01080c8101d9494003540450601d1400c503245030480c000840300b18541ea91414074564100040d040c0e592078840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 849226969 1250 849225719 849225733
    0x30702210d141003061d030a110c06070b060d05070509070305100e0108031909050d03110105010803031909021f0e0906030c0f0402070c080d0c0c08010524030705130e 73
    0xc01c4120030b018003804034440c80541a80c15511401d0042c29604200010000c5030910030414400c00e201030b0001c0e6a480c0c071758a19120383c92110a0502c4440c0600c6880356500b044038034001010300c00c0081d0414010b1310790203810800c51500c00c0c40e0015513044658081034813400c1020156052b000140b06548100101000654444003030b1501c08080c01903c80c140c009001e01000f8184c050200c00e03054541d4070f44007201c2581d480200f20925107954040e0009020003c131092032081c00d01540f4014024200210b1440c0f410344654410302e030004040c00c00813619220f8000a6640d031002003895035100003108210802e8000010301480d01030310302180100e003441e0000f426858040b9100c1c12511000d04001d4010144074104030082d0300200c0104c420f1300c1182e0b0b010414600800c0003002502c01522040c01d07031141420420021007407030f030280403168100400c001540307107000032503407a080345104204c40e240700302d01c0080c3c2407001d10382100d90030003840d0886151507540754200d10310034020207041d1055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 849228219 1250 849226969 849226991
    0x3306070f082809030b0703060b131d010303021f0207060614010f0e0f0f130e1e0703020102030906070312240905010506030c160b15012a0602030702210d 67
    0x1611000d80b41011440320282040031603960803c030b5601c400c8520700041c2c0c0c1c40e00e854070210700703400c01c00449100c0c100504040c020072450f0105100354107880d02c1c109040c1d40c5103503402550707120280c6d283d140074050401030200b9800d9035010784600941c000e4050141c1e98580c1c1d01042c9102003c1403490000b100d661003004024042c040d40084490042d1003403941c1d0785408240311900c01038412032a04055020a1142e002c4482e100d80058003110801804600c0380300941d030400301012502c507250b20380211504200603070700081229808801550280e45401c2d031170505644105204644946650901c800c08550303000c060202d4400307084005101c101d06448145a07012141c003405201c0c0c00c0341c2c0800104201c1d00c0c00101909000c10100200c038244607a40e51164a5428203035099083d8440b0040c18480660308089180940b032a1095056241402c0b06c4c01c0440c01c80c2d2868020380442d42c0003020582491080c08003032140d1130f0790082500e50744a506049841c541c03085c0741d032041161401c807010749 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 849229469 1250 849228219 849228277
    0x15010801121a06060c070e010501090506031e04152309070b0306150c03160605250f110d020703050606031204060e0f0406080c093306070f08 62
    0x41e50030052525249010089540b090280a030031103601c0070003407292000b1450b0400c00e860103058410000e800c08c0d45010700247c090106034000c01c0c440d500501c2000500b46907050740007045030921401d500c4c0c5440c2e505181d070b00180c0c1c12581c0c10603182802c1070894030801c00d0458208400300a00199034995410740301c2501c660726405000e801c6102000401c00500c1c0140e06e041800700c0c914822460101c48024051440d0700144080810441026941c4d05001140c80b81c00d512401401072805070555000801440d41c006600301030030f1240c50700c080000948195400c0d04810303008401c803030740b1240150001c0d55500f03103032008842d14814000000c5140c10042000c00e101c11381407800c0360919080802c1030b1807046540c00e81c550050028043d40142c1c0e550b81c0141c00017001d1201c0940f580c44410400d000c4200c000801413070f220040c019010082207645a4401900764105e0300703554040000c80c000031640d2040e00000f42c00409003601c40014001408010205d8042d85d100034511106554180c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849230719 1250 849229469 849229499
    0x19091223031b030a0f0513030f020309010503070528020a060e0c0108010501231602090a091122020a030e060711031207180e0a18150c0c060515010801 66
    0x101500d40c8802c14041d61000b02406142c21000c0360901040d0800d80c0303491a02202e104441071000744205901c0c0b40f0038142c00051649200000c2d00c0598035103244100080c21a00c805440001040b0000070001c1c60f03040303a10000014010341552040303034403050840080d562205640240c0d0194503003210307449103440001e4841981413042e103555285a1804006560028464018103820a0601000c03541420040c0040c1944200f0700c0066511030f46e14014416a0500103203200c805c02d10304025a00030444844070b032418400c080b02d042c010302400f01e801d070714442411071001c0c00e8540041050741d03005130560444225000e100701200c3c02680c80c0842111282000711082640b074004100b060990720016070f4a5910410600f490340783e0b041c66000c16411184079a02c680d0380d000001040c45141341081c021082c01c0b42211182d080c500c40741d629091520350000100941c0e242e501c4980c0b0450901842c1044d0700c05810180c20010b0380f50100000743e403004441020350000f0710b05400420b058a05040170 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 849231969 1250 849230719 849230731
    0xf060f0406080a030f11071212031a040b01050d050a0218180604230f090d032706060308071406061c0f0c0f0b090411121909122303 58
    0x2008207140c903031419500b09051905210030041400036080b01b540c0c3c20004540141244e000c1450301c0015400d11450004100c440c2c1402c2504202016404500e02000780c160386000b00c1d40042d2181e03802005941030302c9101101080d00e428141000300303109442e8042c1007420504000401c0314007004003002201c003101d034100200b40e4000c030041440303820140d100c4e080b2000c00c05085841503c0603011111351303801c100c1d500742e4903aa003c030030442d0703601b014010100f07861214142805485104804440300c00c40c03440c054100c81d2040f01400050140039085440215005590300f80c2e1030071030742400344030b001c07035a400d01d00c0c244610800b140090600803400c3c034548041c85c2c0429051420365031008501c15140070140c861a100c00d402041c10880b1a4082e0003c0030644600c654802c0d401c400c0c8029507180103c000070803c400d02c0a8042c108039042d01c2680f00d40c004440c404195028a100001400f1260010f0501e04030707007024120b49600070182405001c0304445451703280f0414049048244400c4401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 849233219 1250 849231969 849231973
    0x10b01020303010e2809030f03060602150c0d05040302070f06090522090209130204060b09060f2b020702090a110901030b01020a141e01060e1902120f060f040608 71
    0x4000140700204e600da0000705505c100b60001a01070f40701d441c04e05148001041c0d160b940d144400826400c02c1112000800e5404c040c0002d80c54210065101e1090003020460b500b03e0000050622680c0002c540b00021160300c1005941483d0400a603552030034001c00d00440c0e200071003c200680960100e0301102c01c0148142c1c070500c41a000741c10302d59201d0502c0654152248180c0005070360b910300f8648140303403252000c2c800e0f410b01d004003c140c1d1a40da0107400348410801481c0b6071600c0740000c03038000208581d0140d6031034072001e801c2c01d40c1000440100085002c0c0d00b840901581d141d0300105a07250084904400c40d88900341d8010031200800020a5582d030100136100541d4025085158a08814019500b5103031161321500040b40b40c115a002c017039000b140034040481c2032000800c03030b21020070f002003050600308080c10703101072000307002c14201140c007024130303d184680354048400401134010b0aa540e82080c801003070b650788043d00c82c12b10500300d00c880722102e4100362203408211960200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 849234469 1250 849233219 849233221
    0x819020c131113031104060b03011206021e1303110613050f04021201090606091706042301090510050105060c10091b03031211120708090f1e0d02010b01020303 70
    0x1c4000002c064106031801110424021010034001584444000354014820603007600064810401260f2041d0005141105c00340014000c2050381404000e4280d0300400059a50300903e42d950f03000d00211859000d0543c1c0051a040240b506520490450b442288041c8a44040b03604000b00f5004502c42004420620681002503240100001c00700c402c01800051420051240101954800360441103140703480d42401c02000e94044511001800100c80c440740d01c0048000d046d4498101130005040c48074060810110b10f01001003002d240c1420200070400c2c002113160654582440707032900710300b040c5044000680c90521600701c4810842200180011041410190000703013a015004c0e10115141c0050441c15028401c03c000698041d0312906007100448201d02c040e6480072804410204050046040d403400d8186500d0b001b20683c14910002c0d41c481000c0d910301640003010717800900c03980d00002880080001c004c0d54080b011020b80b007403110942d40603800e82e0400c0c5d110500580c8200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 849235719 1250 849234469 849234499
    0x1020c090103021c06110406020a120f05031603110315010e01140a1803050a0506010801050c18221b0908010c080c0d06050a03060f181502071505040819020c 69
    0x5075003441c0380e17407003104000307000f0210260f05480c0381c01a8000102603848142c002c02480f41e0b00307c05a002032064680015a040284802042400090000d452001c050000408a24020b403c41da04080208180c103031285001030100b10340503210000b03a03001c0342d41da520782005944504c400010301c8440b611168075180c1c0388441111070fa41e070031240f500d20340f004100200c0050360601030716850314050300040200e941171402d00742c2150809131003a01ca100b02044041c0401070070042107e00701c0800c49261200c40c512405005540301030a200c0c1019515003507a281840031401c3c8805010030017a9164108551250851800c8825000361000400d004400288400048000805501c1e581c1100400e5480e503a40104160f1151500304880c51603d03200c003c160806c1510950301c200f445100baa00c0d00203090340f0340c5401c00071111144a0855000500201405a4210b0640082c40031000c20402d03441c00d42012000c81d0494804143c0759103000312265500740c800104000b28400060803000d10b0540c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 849236969 1250 849235719 849235759
    0x1d0d0c091a0306130515040b041208100501080406140c030106030f05040503041a130806150f0f06031b070803390a0c060f0f0f0c020a11060405100c0201020c09010302 73
    0x104c00c102c505200f10750801c1da0085c2056100ba01407482560015020304140c41c1c10030b802008440f1a00410948404101b400c60000220004580d0282454001501d0b10700307200d00a4000c201900c180810707110180040000488015412a5565a004c0021402241040d0161681a18081c14503441844107026119110500030011a2000300c142d00e0081c1e040041034984e05541c8c005000707504460100001c0102c1240711760b44207d400c84201503501d0301c4d00c0000c1d030122203001029006100c080001030407041005041850364006d81c441546500c0d180c0340854055004482544003140d0b0300420400d0030541040c40d00c4440c0341c101c0c084204503107524050030760b034010084090401455205000c0420b1840c440e14400d0900c048011500c25142030b604d40540d011080c10b601e000303141c03d1800c40f185030701150300220360b40c1c000c2a80c3c2d81d0f18204c0c1d00082040c040c9410055204d10703140c0c4c43c22701058100c18100e060500c01c0e025030307c0040b5100104a47e121f030900c00139402651024400e5050542 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 849238219 1250 849236969 849237001
    0xe0102070c050402091c0c08070e06090a1a030a08130e040203030f03041703130b071103180303120705031f0b0714070905070c0c0f151d0d0c091a0306 66
    0x5c0544203031300310f2003080610308445484250545003084200418803040005201d188082c000ca211149220305002004c0790b4040001003140c452aa40c0e184c1d00c0e07003201d00d00044190510002412a82c0d100c0c0b9504100b9410b40c04a428486481d12203100007440c00140000703188a40d40041c0a10f08001c10f82d02011601e0344014000c607240d40c1800e5103070403001d10120195004444c00401c400c90703c48036242814007404c0260202c02400109944001d06d644000304540c14102c030700c10841003401c1c0780004240b0b503006400d11560b40020079010000c21a61050145205190445034150141451100b025890001e4000d0701c0b8002010800c070710110390086205680580d000c4103d4414555804d031040c1120300a840c00000a50760b582e030102441304c914030312005051450045203240e85001070321001644500c0b041014080001d00122a00400020300a88010080d0000001041c1494003425208160107245840c03498110440c0001100c17079a8160b08880180c018001c03a19a50303494503442c02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 849239469 1250 849238219 849238237
    0x20f0601241103070b0c041403010b0a06180504020d15060905010c0228081c030b0306040f020d0828030213060302030a0221090d020a050706050a1704050a03030e0102070c050402 78
    0x110410408000407503020034944255120000c440c0c860f42403c0d29040348666400100f0320aa05005110b62f10359103510082c0c088911034142070142103c0b000d0003003e4075a031903018581c09031020441c0b8000490f02d0b04403d000c0e0351445c02040c0c007180c035030b801075030300094078000d01d4005002c0c3d00405c1c0040c1460000c4001d1070090040344410b032119641ca08002040e01d40001034913400071a50316040ca600341c800200170040310b060038402c2c8020540420750303a031401400a0020060803080b07005546901c1d184c0004250003404903a5a5071000034040310032420a00c41154a0880388560350180d4402e20954908078a602040c8105a140034000c801940010341141c04942d402c201c4803002050454a400a260418091544520384400d40780d06040320f845041040d508031592060024201154040580f8518140760f501c1d000030307440c1102c10140024641c5039050064060005001000404143d0b40780b1980e801c0c8a00500c0702e11290a0b4011080f005007400c070515018017144c0b5054018000c409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 849240719 1250 849239469 849239473
    0xa08070309020d052a1f0e03030d0501050f010c11090c0405041e05060402040807030305070302013201150903140115060c0501050912030703150503030a020f06012411 73
    0x350142c0008215065030701007114140d010314401152086841304021002d401004081e11810030340c0085551181194103020000c504511512a014090082c049994001408aa856806003069180204130a001d0f40b407003004810b031180740c107600c59450a01c0c01c551003200c0c0012500b000040c0400d8007005407540481c0002070001141c0c0380c0300c910030f039000c000c443c110030700c1c0f100700b0f0290400840d10040d00c458050b030b00401043c400b412000451404030799062520658903002820100e0051050703600d032342000c1041007807029504030240c00d200001702907440050b0f12a40d850030341107290b001030401c100110b1070030340d0100082000141d0710900c03c1c078480c0c00032070224004c03121503001d901550804404210710913101000c0c4402442066403044214004140700c0141494840b12408000c0c103690400d42c940d810064002c01498400c4014a0045e0880e900ca804c1041d0182d11005e0301d02104000d071080b00c000194410200210481d4061074080c0303003d42a4880200311741d04d500c0c00e01030510034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 849241969 1250 849240719 849240731
    0x61807140c0c01080c04060503061905041103010501120b0a121505131a01120b0a0f06260c15070c080d0201020a03050601020115090506210c011803080a080703 70
    0x380203100c00400e00c0a2040700a001038070301030b10015002c007002805500e82c800c400d01c010f020182d042012203400203801c491212000c41400035088180c1895005946c01c01c0c1049055004032001c0743c05941620000d0300d4826a03103100c4200b0360b084801d5028066030040c24480304014056421102c01420b5000741180018501d07580060401d43d5416254050440e480e40001d00038440c0d080c0000301040c802c820300135103d52504c4103082d0f007007070f186001a016002c0c10303000c80c003202901da2040d660325465040c240704042d680e103603400f01740e2000e0b0050010091191414030040b0b00110740c010344124000c020020714543c0c0c0790080e110350403880c0c045070300d01e02040000c9a5407008201030800d802ca80d81c009030f40d0b480600401025200c0280541c2c0c19a0704088505141c0f824106031601503a600740000100c56031000002082c0d00c8510440c21601d18003480c01c900200c201240a848482e0280c9810904840c91501ca01182d521840050080e18050014929692050304410340000081c80d0200d08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 849243219 1250 849241969 849241997
    0xa15020c030f0c0901150e060310090905060601031505011d1c11032a0103110409060605070506060306090604030c170a0810050a08070b0702060d061805010e061807 72
    0x24212014825000c198820306280400303107442c010b8036002d0306c1c1c0d500c07000300701c0754503250090405101810740710f00c248400710004d03240f1525040107400400700c12a051083c0c91090809603161801510365a001904160a940c41b07516619451002c95030186d4071144034007070101c0550b81020b041c620543c2c5c42400c000d803025403180402c9070283c84500505401291044d210b00b01850801d17241002ca01d440100104420741d00d1a0040c00340900c042820040b44c0e4003251b9042c1c2d9035520464001004a9140c000c0100c0c0c0703145d02c1400b414046200d042240c0a40c0c840b2002c042d030703070841113880d4041a441040010000380c40341402984a03032080a81c13501d14003902041352010b80040d04e0100000748940c0400aa00f00c0220000e001010300b600c003150700c182860041d50b1110b0690107042d00002000910b0b004646643d000c5035148181d03071804010703107030729445c045200c9080c0024940c0c100f802c10001103140f0010a0a03680134000c02021702c050000c0030b0b01c0b4603207550700003407a15050108950503220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 849244469 1250 849243219 849243223
    0x3310f060e030f0307111902090714030711010b120a14030c0a141009021f0203160f12020d1e021e0d110a0c0b09150d0606030b09060a15020c03 63
    0xc04000c4400d42da501c1e89085e44000380b60303104611019007181d00c43c2000264550000392a00f02107a01503884a0642c1d131034503021740c2c0da4480005020b42c0704c1d0002080000342584064480401c1c500c00000f8448111048100022040c0ca08120709c0721f0b402c0040d180c0d0000d02d02c2d00510101036407810559082c45d482c500c6d600d0405c11401d20a441400d80610385410016051003210034000c1e20750b001304465115600800c80802840c0d4030300c81410040c0710710744521070003001501c1542403541c03558030920740f1528007402d440e1421b0360210345200c0400c010107007150000c10b20046800c026030316021101c401d421114203040140c0110000d500035200035681544d6a501174841f03005c1c20350005c0c00e42c000b11803002841c03895a0355154000e03070061501080041d404820f1001200c402da20030940b03403414030002989164050107466608000024074640c1c00303210b900a5821109552000c02a020300d0806001080c1d000b19486079003d0b10007103051051002032205000000814070450b4401154480424 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 849245719 1250 849244469 849244477
    0x5090a030b0a0506120d1e030603050106140909070b072405180c010c030206061e0a060f080106050306030d0c1b180c020a02060d0c0e0a0b03310f060e03 67
    0x201119180c10421046041c82c8001001651240c00105006c1c10345150040441e049124444480900b001e8142140361290f0800405990010002c01c80c0f80d545030244c0c520f00c8000321495001e81034400000d01c100c0408903a401c1201c210304409031409000740e48201c16442d0300d1080b0304851265102c410040d40c203134402d0038400c2c0d007440144200d1121801e60b0500d0940f104006504200341e80c5245d01c00250701081c190b400202c107407001d18021410704d0b40c05d21011550a80c098201c0304035000000d545a015903010314480302c1c4d4032207820320713620b40c4412034461008a5609415170f000d4410f4401152145411040300781c080c21824010507498902003015202a0b0b1010b92103a81c006021203021043e44509060032801d800100b440c103003a6030214800d03009401003085560f43e00c3e445103050a0051005146254000304592001504e840707110305039803c2503800070980740c40902c1e6084240c07400001c0c8642440c943ca4520000301980d6951450b110392070100b250300640b034034100d02d46880c00300058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 849246969 1250 849245719 849245731
    0x1506010c03051e18030f03130314070302221b08010b1b0d093008030c070803100303020f0f061b2a150c0301050105180d0b10090203010f0605090a030b 66
    0x4060b1130303600102018640507900d440000305800401000b0f554007034030100d031022240e21013100740d03081c01c050342802d00708000c60340701a400804203804c1d102007032040012050b000144070300c20000128500d048540d10304403609204007040000c0014401c11769024050001703a0300b0301c2000750038001d04030b40c00e41c103281242d0002404aa400f100500c040381980f01b0340f20400d503140b42034110711b02c0b00c08040c0f10003070407440000d48000c00c0040032400942d25507040b50249a08624030342d9681c20012034400300340b003803440254014020912040740800c00420040700c800c000034020900381d1110070700d246042c0391084d40c1108484041100c0d8140e0030100310801c0031802c800002044806019200714201011803140380002c0301030381c00300030038243c6050580381076a03820300c0c06503103c6d0710501b800d90200d043c90b004e6550290180d4014030400101588061080350182d81c10f09005d9607580c0c09505034007007800340d000e142005120505c40503200310050701d80f583d00204114900b40da40d0b242c4601f158015950 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 849248219 1250 849246969 849246997
    0xf01121d071a0c0c010e0d0501050421030504050a03050a02070302191d09150c040509160f1701030215070b010e07021e0c0904030909021206031506010c03051e 70
    0xc1001440340c24600e02220b800c120b88024a0000d00d07010150321001104400c0c0d0600400c05100c54031619500200303510603502500130005800e160406951500107200740e01d110410110140d160f66100380030f035a00480e4410001c281c02401c55600b5501c41e04035903078810841c0b03c1e02000002603560000c075480340c040c211240300011420f000d000201031051803842c4414110740402c1c002e52050000b10044280c5030000c0b101d40ca503c2e075099401301445180d11403540000d006040c40340000c84180340201c0303054281c4400c002c0303603048002903501e0702d01d511009507404108001040941082e0160440c5460003881c0341c0d180070b904d07549940a80340c081c1c0200b5407104540c1c0070841c02036010004064513254125507290b1004000603031aa0b5103031004060f0380580801c20101e42010b0240c5400030192074410000d5440380c1c4203030114000044d04807021442846440f00b032124a000d400e510a00446040c2d560000200254506036280d03840f0741c0202041e044c80784103408100d6006405003240c0409260 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 849249469 1250 849248219 849248233
    0x23f090309040c050706180b041202070e0403020d080121020f030705150c2419091401020a030b090408030105060c151503061008061303090b030c04180b0f01121d 71
    0xa0007802c1f0b4140000c0c0c0302100384184c03021030200b228100300b158000c1d40109040780304142c4d803c040741401502e90000a11203050b20511041503008210146034031280d580314206c980c0e8a21500c0d07040c200103100780ca20007000c1000e070030150500422010301000040e007100e50760780d42c0b04041040c4408071080504180300c049140c40c0d10010620442c1c08084030001d5040720b004070740e180800155000341c602030361080d0750350030141700e9804d0780c1200c450070340c00608082c0c0110861100d24040c1d44404039190000b443c0880d0304846190007500c950150760001403207402c5070309200c144512644060082c4000388a4400b116038120351001940f8407540c071400c51018680b2100c018149001c4d0050185842011450000e1041201c0001c5141d80010707280c0801d0160100750070180c03400303007860300001c00700c11000040200345114400200111000303605110880451080c1c500c1c201d5569110346c5a101450154658040d84580d00a03180728404060000341c04c1c1e031548801200f5101480348a000ea00000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 849250719 1250 849249469 849249473
    0x1505030a03080615190302160203060a0e010b220b13060b090a0b0c2d101406061c0b1807020f160f0509071110023f090309040c0507 58
    0x1103e80c0c078100040201480c05e20000a0800001d40d0030140750004069011501c1c844000c802d0300401320068026043e11a18240120504043d15014040000543c04d0a020419a040004026520840150603401099285107440000e0500300329100d034007020256403105041c90700c1c8100d400420200e0039a603910b4844a040c4034a0019a500804900c1421b100070f0080223008039401c040c8001c0e480300c0010a0103c0d8030328107a5104458032842461003027040000703803141c1d00e9006914101812082c007075a9074416042042c1403003180a8000144d11134880140c5208443d00120180c3c8001000d012070104001881c020044007251100c005034005007103403000d000c06000085000381d030488006445401c00990208110850cc6402d01404410000801c168825019a00c80c541020b058820f034284402c8160f01941140041c40728114403d010a810451900300e0940744150500b55500141010051841165001800361083c0d000401c182a16039a40340f11701c7c0340900e0191120b0340c90740124 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 849251969 1250 849250719 849250729
    0x171b0408060108010204150e0f150c1014100b1207021c0f0e011112030405010f1b090b1e09011e020a110405100e0c040e10090c0e131505030a030806 65
    0x1c11f4190050021422458078207448481c0d400307899070741c01c4d15a120910030743c00200300680301d02c5100805074003411400d54241000c3e50848009550050740b03032921b94880e038412840c000c400d88904080244100303e07245a002c030040d02c60b90301030001c2c015200740c2c52880c1c5c0000310b40d00d1041110000203e20552405d49260480200c84403c0070a181154010a02c0702081d035960b220380400b20200600400000d00b00802504000e9580016201c1031140400d1403802c42076403002d500d44100851203003103000c01e500812005907400303040580c4c40614407141c4085d99400c80c0c0e02001000e41084070324a4a01411440070b00d424412507060303801003050303141a04001e403070b0000142c06144918100b40a028030b503003400a201003541c030041c0006800c2d46404c0350406681c4500e50246640c04500400c0000d80340d40c41040804640007040f042c043e004140d00104c0301085130401d9282d0000a0b5000c200000c022580200315100c2c003100c440180e50344900000345403001602e0104c000480c0c40d01048014204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 849253219 1250 849251969 849251999
    0x1119050d030c02030d0902031e01022809031e02030607021006080a0210260708160203270a0b0f0301030c0807080c010813060203041101030c171b0408060108010204 72
    0x100d450300b0000d400e0202c1d4000e46900c034808400c0507082d118009803082d50380a03c0781110401541494100b0401001d031000c0c007135005042d00d1014004900104c454142101c00308010418640d0303214030b401401d6a491101c0304c00b00005039007030f410000e40b00c1ca0041e202044a035010329440d030018002c2c003440b03c20072003d40f1069004003002c0d4010703019074001a01e4031400004008c1d501e00702000385041800c03004a49a6100e0914039080d546542441a0342d038108031a03500408414032168000c11810b01c1c280d17646e12500b01448400040d4142c8416040050990b07401302010092010003601c1ea10324491005400ca4506000364101c000010810440d15540080017800300f203024040c40c0d454584034a448001c1c8416080c18002100c00160344440450800704a440e4040000c40d10b03420141084550103003510080c0d40880c0ca4003081c0084140202a0440010040381602980340e032240c1c08000425800c3c85580b02440c0d00703000101c0c05a50900c0301c0350182043c407000503159850208190742d1303105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 849254469 1250 849253219 849253243
    0x1201030c0f0303120c21020301081603020d020f1203120f01080d0f0503060105090a0608040b090708032505070305030a1806050306042f0d1a1f111905 66
    0x62014000c1000035001a0042004140a24000342541c503041d000e440c2c00f0820554549106c4044068030101c9a9035070285060703c030030104445e10001c0201c2c8144d40b038070301d501000c0e5202e00303c110140b0041c0341c10806260742c014068a144d241c841400c070303003178a5500b040d0058040d01600600304046001071460a0340184010801011380700413212010700f16022013180359040040010002700c46901880458421b5180030f00a050707140e81d40c2728014003040c016901142d00688540115041210010740c100985025030059480d016a640e40600491402c541c1c000c03ea00d4680304850200b1020702259001314082d2003e1a0303540350f00324000b00340480074088602c000700340348401c2c000e5640c008d0945e5402181079074001050f4000042482c10090313100505140056aa000707000311040d010060802c00c0e00b90141804a80864a00c4651007500850002c0e0051101044803404400d001292031214070305080840701c8540340d280d4141002e0113051040ba0255148594800f000002c0054281c120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 849255719 1250 849254469 849254489
    0x1a031b0414150304032f03040312030507020f3c1c080906011820090a06030e06070e13050c091f02060103120318050d0306080303150904030c081201030c 67
    0x803504d41c0d07028010f11440a1072120314550104501584840c14580a83c03c00181c41206d44880c4d40f072a102550a210500035400a41400c0101d258940005026640d010b4440060070781c0b140030310304501c00a400c40304144600342080c000700350b0720171851418921a92142015001200c00031200f218600302c403592030710800030500300700102c2c03082c0824890b054481c2005044680d400300051480600205c0036801000d02c0008204013402116030018000c00000b03941c0c14201715500c500c280d0448081d1251494140c11010000d1401c0d031155000c5100118000c284600c60f44a0000c003504030f030360407034910351800000140350030b0501c1c01d000340d07652000c2c01c60004440d2081641c030080d19070f4010300c40141081390622220741258040c0d08003055542c1c5007074545c2c0000c015401d0840d6141000194130011a183c42c030045203503200032084a00c240714841c1070300d95130301c1c1c1e1500340031101400600c00e0702040028004080003580f600010802421700e429104401d5055040141d110501ca6001ea8005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 849256969 1250 849255719 849255721
    0xc06060607211e03240e130f0506070806090c071101030e0705040c090e070912030c2915040e0c060325020f0c0105041a031b04141503 59
    0x94150b50303031841c0b1520400c02c00350300c024049000740c038034010040c2d900001c182d880d0342003003100b40d165020740819101d4120440c00052038412105080b07200e4010b90041884034030004000000c114144c0d208039102d411039143c02101c80d1500d03810200c00703403003600024180b0018000070340307802d00149401c1035520f14198541a1940d5036460304515081c07490303040c15160040600c40d81d0050160078010407025005201143c19000010172510322130040d50075880007000428070940c0700707140d80d00c1528800741c0c800c107140d20144c8082e1101582d105044038440c1c030760201c0c603000e8084507054004502c090410340c8503e0500c6284803000f00c0c0c1002c2124012460584500c0014a00003104220000155056950380d111210032014481e10400480342d6841d1001c42100d02a03400a2007130b070085085010743c0d0f00c106a140044a0b580f256100c4d660403c0b4400e0700401e0711079040300003541c01c17204241426403946561045040c4d250000d51054040400d0407000b07a040b8102405851200c00e41c1e00c640c44e140d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 849258219 1250 849256969 849256973
    0x12021e0c06042310050408011a10080a022101061d0108070c020f09040b090712030519050c010f020a020d081312170f16050a08040b06040605040207080c06060607 71
    0x440e019520400502141503988100301503100d2840c4245050003400095040900903000fa0086e4440c2c45902d040c0d620340040b00200c50308860451400c81c0b80102002c0702081d0594084620640140203c0d042d640d081118040c14180350001d08230084107502c000322a91714101c2c001d402d42540d207181141d034a8100f107514801e42c1e801a5401c0d80001c142c00d2100c5800910300105600d001340700421600150700c013041c00280000c5002940c030422003901100c001944503840400c0c0c2e8101c0d9040100810400d00040601c1c0c0c000c5218003002eaa1980307030450070010010066401c0d0b680603484403186542c0002c1c0c842d000b030380c10b025500070010300d0300b006d59280c201400c401140c14a80b8038050300c06002d800030000740521496070200c5070782d100700c40c280c1c8134105000300380380f1480e0540e9412032441c2d03030320540c5e0f240500940035110b011245485400d4107540e1501d4036002c8150082c4540d6029541340400b0421340c2e00c510203401c9260107101c001da229617524040f507107442c4015120901c00d840500031400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 849259469 1250 849258219 849258229
    0x6071707090504020307020c09010b031f0b0a0e0409021e0112064b08070501090b0702091b2107021908070203010207060524010e01090e0c0712021e0c 66
    0x4101c50b42903500503a40c2d030314400c040307042c500129005a800400c00b80005034246180c806903003d0081881510720060380a404480864000d22401c041120140284480e560140241200e40d2034082c1c40880c1c003404550020313001e054075007084200001902c402d00101e5a10001a15494404010400559003011070035416a40c0940c0c04030740c203288002d6410592000070b00c4807031050090110302500c0140202c01100506d00a00521032188600140062250b00c14241c41c800c0741c20f04c8602c0761800c0361540901a035030b440200200c4810381d21020b038040b91407040e03004000c22104400b0b464140c0c504180c0680700c4520103411281154882101881c1006001d010300c49115802249079580d0764452020038060b015294000d4220b52a000130403005041c06066100204003243e0800ca0100700240155490110b081055000591f141000c1c00b07004410004960000d8415164038140340c0650358a50301ca542c075620040c0180c0000850141e00000980302144050283e00909a528003e0010403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 849260719 1250 849259469 849259487
    0x20d110c07330c03030c030b0609060325110708010b1f02100218042016020103110706061d06032e09060506030c01030b090604091e0506071707 63
    0x545140c0d8408107010b02d00403503082c0c00200e02442055420307030003202c005440240411001e40101e410002c084420700d110b0b04c03030811000001043c16007443c0540c014000f05070030080c000741003c020342180150700c09602c0b0601180601f150f80310a80380765008010fa0400c0350300e610805450781860407601380f5903180481d81e454010f0300c0302800c41008020744100d02d04840c01f030645004610010b840e102c400d00c501603805250005a038140020107503464038110960303080070711030500d09c07092000c0b10740404910318845103140140341c0400c1d40ca11081940c00307294000c400490721150365800800031440380c1d6034401400c030b4410480c212180b80100100c1d07140e8604a989a62011580e01700d40c001006919299040442d644170822540449140a80c0140000d40c0d106109101d00110840e040d031007401f03401d0b21320401510a244a48a000910026003868001100d00c9042c1c40361100144040310034003440700f07004100030411400e04660242550704c0101031100c040306607a0400c0840b58020300e0301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 849261969 1250 849260719 849260729
    0x9060611010516032406170c03070e040c020a06060e0a2f070c1d0a0608032b0207020603041a130231020a030f060b0c071a0d0906020d110c07 62
    0x450120f5005e4401059001440a105444164543c0124410394016000784c6008040b11108081d611880c1154030180003c171482000100b151118007140d0809800c400c541588500480e103180031035554000c1034032284d0300517070303800210001005140030b260f0280481e264a614000b400b019a110501140101e400c0c0803410040000601c040c20842d0f10b219210040c801d0300c190300ca40c65070131400021445400d0343c1d08243c0605094000c1609080802100c2c0800c0382c54542c3c6083e4140c201c01c003035403600c442ea10811000d07400d02600c130150301d440c3d0007940719034800e8811610041c039088401100c1c1070b003c0c01d22140004002040c100507100c403009030707040304102e0a0000001d084035442c260f001a94420003c03c10b40082004ea810b80d4040d0040e00008038200418003c558071a42203407081e010b003d0b000e0706160b106c0c2008011220400845521400390041139500c0c00180307840510607070b107034030742d08660090340000c0342542e126440c86503000c01a44244c2d81c5152000100352550395003c54018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 849263219 1250 849261969 849261971
    0x12030501060c330510090b06041701060b031e0c03040201122018040506030d020a03051b070f0602010b191a2106010909050121020102160906061101051603 68
    0x1101040c40101d44202d60460a1400503000f50301c200641001501e800d0355900b240618980780440c00b070040d07001d2203206e5900a0141800d1519007008000b04001e80c558a81455585100100b1040e280704011441907030700680200d0000090104103088042c02401000d5413541801030100503a800044046503488030400807401c3e04075480501610098850310340611080021049118101d404440d800b2410403201040559508024540c17107000103919900103030445880100000c0c000e40142a180780400c00c01256607884046580c034200180e04000001602c68004105199090099003808442903803000341c507007e1450f074110b021030b9074012028172441403809000c00d441c8400a5030003119500380b1080616004014841001d202965a1070014203e45404150b856003802024100c0d0103d002521000c9c11801c1400850080c10a0484c11405a603941401c0500107000640c00360403054800980545004c4003d4610211642c0300075450341070a08202110500e0108007803000080c2c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 849264469 1250 849263219 849263243
    0x30801060503090303152d030f01110306010302032e090c2c04090605041b1703120c0409090506250903230f0d1701030b15031606080412030501060c 65
    0x100247c103001e500d681031204030b1f00762101c0b0f01d450030384181e114001c2d05080d0242c3d002c1c83d4448519600341c074107601d20803100782d0040022032000d503c680d00641c4d2052043d00000403141541a003400440c81410b454019140300321010700c5280f40320300c100244109607040801004020940180400d0851402141217204101c1081300e02d03242e03900559080f41d8010010002c5d440c141c0743c0031403040005003020b005184240d00200d0380c417a00d003200c110010010740045080c40410100088001c1c0005c000e22405074050100080d180c0c2c09006042100e44240080e280360b1a020410f015640c3c241d03400b415001300441300c505030454210782c651068a0300440420309030340041c03c0200c41c150355441c00302002d03c2145100071b9210004104a61600300710354800c0b02c881402d0f0b0018481500a00020344541d240c0c00200e24001c0c2c50240c103584100b00a0261060443d241d41404407002041e8014800f10301c1080030842042104070a0184030a0750303081c200320350b5060050040020140d03141c000c00c4190001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 849265719 1250 849264469 849264511
    0xb130c0909020c07180204050901090506010314040b0a200f1803071d0114060d0218030105070c050c1207052107060e120a1101031d07080307030801060503090303 71
    0x5480440070705403460040d541c8088003450260b440e03009214800281740b2031030002481c880c0c5030007140d04540b002010380d46140d0801800708002c040c060f000318185540c030440002c0740110041164030079401104550b03d50b20b0052015010794403964003074074203125004c0407181950240c40c199030480b0f4501c030001d030f200e800f100c40d0000142110740301c207641441240400140c11429081c0c529120406203c3c564091b42d880d005601840c030012429980000240241ca0304c41c2999405409098035055140c1e581d074104201207801c6450940303003900080c041c4014036092004c100600f00c000001591107202c90070085001c035841c1c10130b41c042e0038855000c80c104500c050505040700c9428005c000280c03070025a841c007025001c114844034203400703202000d06245003c4004240c0a410a4202980880b09004280110010680311110540c0594010001200764800300864006010700400840e42d8052906001e40307410030503408101001002c20800c40c0d81103001c0262900002c1200310308400a0b162 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 849266969 1250 849265719 849265727
    0x50f0702122101030b0709060203040503100203071b11030c01180515040305030406120b030d02060720011802010e0303030912070317090a12030b030c0f04110d0e060a0b130c 76
    0xc1116000321002180004c01071102c096041c0380115032684801c03440c1c640d51902a278580c0034512600750306402c01146001407251035001907510146501d010300358880306851101c2440c001d9001525039040d8018500b04504041100b801260402d0a0019420004131014a242d02d114002c1354000e0310070070422242d2540e1101610b02441e480402e8a03110b5031180001480200180244800300703040904600d80c42c240032030380904113407566014000d6581c03059426503c40940750408035152850340c00d901000c5201b03201e01070021444940e03000b280c000c1400010721440706418090302c40c0e0800c00a0140000c00011007445c0c0201105a00391100000e04041d2500003180001070301c4801e0711010080c01c4100428242030b41d03841910305501000d04050b0803011101c20503800740e0154800d5880500e1480c0040105810107001880894082407124800c00b1b00d410a014040506840e81040d071901d40c414040282d110210110400c01c942c48038001a49440703d4400c06140f1940d541003500d102446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 849268219 1250 849266969 849267007
    0xe090a0621030903080705010f061703180a0f0b0301031214120a0f06060e033309010905031201030c05030d0c06020c0a050d0c0515012714070302040504050f070212 72
    0x3c45d41494684005051050207850a488805202c81c600038021072920380c4000c2c103a801d024172800450030440c1d51103144503001c142c103a5241c0e0250400d80000ba209005c10000d40103403031144407040c0c8039490341ca042072031340f00c00c1c0c020030f814094641d06140e11800864203030759000e410070030303101d001b515050480e40060814801003094607003040c001040d110740080007065064010b60448951200d51440200701c1d0042c4100023945d0b170b90002e0120f126802c481101600b050390f07038000144c40200d0b40d80d5a071841d80302140300c0064400341c0004200b842504040440201419006421444080e202c000c10002001000601d090760104401522110030061f460b001030380700e01121035030340302c1140140200600740401c440e144105a4046006250b50380418103c40490140b059145402210a01c00442d1010100c00f1503648910f41105810740c0540385000f45c0494800580d6181000180010b1321001400802200500801d01002e1a40003034041c407910b0341e140c0c5c410b450301d0344c0c0d030004c8582d148 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 849269469 1250 849268219 849268223
    0x4090221030c0c0d022209060f050610020c0603011e0b0a090501230301030303020d020919050f190302010e1305240609010f051308030c010c030b090f040f210e090a0621030903 77
    0x49014849d140c1c12034141c0c800c030b001c1c903c2100c408102d524085003c84c0e81d0181400440d803c06000d04c01001b20318800c440024620400c0078020b1711064840c034100041d5004140c0da030000441400c1c0802031940c018560100c202d4000a904041c03080418031042e45101c10b2000070201680025031016203481c940c10b43d401c5260080c0440d1012038103c0140c9a0ba60a0f0300445100d04012420398409103822080b130001c00d407020010507582407440c2c0064500000c0303c820744d90810104560b41c041382d07815108007441070f80b10320301c4407005a8514500004190040a00c00c0c000c4004024006a0741e80124050303c108040380723019a5200c00f4100c058004100d260b0100e0014440401d1149000d4010741000b0181c81d03c13030354200460004001001a01076040d02d8541e006408500441c000c0381c4139211102c0901d005400c18170794541c1d5004001104c2da2500c800500045600c90220000d142c00150030350040c40d407040901001d42040c01c0c600c3c40030000110030016000c80181e2104250184401400440d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 849270719 1250 849269469 849269471
    0x412050405060a020d0305101d090c0d03030c0e0103050403301103180d1202180d0506040c090506060f0d0f140f01080303010308030604090221030c0c0d02220906 71
    0x184036084069a940311005c543c80100b030030f050002d4504910301c00f00304120750b5018a40b00d40303400c00d160b02030380d68600540405124061156018000c0e1100020f14603054801d070f900052140f03403000014051100d800304c0da410542020300f400082988050142140001300c1005505001800b07a404a0399900c0302040031000d04040034241810301c0240075510a602c1141081031002480003880d440b03007454104074000c1409584001001002540580700d0205000c2c602d14166288100050400c0001c00d000c40d00d035803045c8204410009400078000081900b46010f1245003000000280319010b90314a4212458010809268121a03504440b0001c003400300f041082c1c900d0414801161402180e04e07803c449492400040c1c0041c002049038100d0b034011401c14110740f80c0004200c0074002188090340c0c01400010300d0260f06000c0704040c611421035100860791070341201d074942e09000e41e181d0481d116104c1e15003840b01503104c00c840003040c62085902d013042030a0003002100107140b0210050005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 849271969 1250 849270719 849270727
    0xd1d060c030a020f15180f101d03090a0e0c040504060e0a1b090b07152c0c0a03030804050309040606030506010e0301060b03010b03090709050a060f051023040b030f040c0506070b041205040506 84
    0x100b503a002e2003104027940030103012510350030025a034070300c0751000542c0c028208100810620390b02c11256034001140c00e80b00c500e00f9603500c1c0001c0c1901c50641004414411510a000c18803284e1f1042d0402d10301c0c1d800e911100000c00b40009040090769104410200da000541141002101560305103480f0b0620030030490941045102c035801010b03010403801e10402e00f0200c5045010014080840c0c1000401a002c001d0555404071603031030f400b03030040b60984402e1001d80c02ca03645502030400500443d99000603903190560004100001002c500c5009915011061080803004002c90b810758101910a56903921340400ba246000101d9203e040c0580c50324050103250941a00600211041c6032441750800d515001004041c58442d0350807000702d01a03042d100c9402c4c001003140300031a0340913003445062558404e005030385035004854054148403820108020406840b0451002e05802e547d180e00b408016612154810f03000780010341a1400c0041074851640b06004440242902070071458903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 849273219 1250 849271969 849271993
    0x70807080f0a050c13020403060f0f050c090901150c0b0c090a1401050318070b0a03060314340302060a0c0b070f020d1d060c030a020f15180f 62
    0x66151a0040803000d010360007808840e000c00007041c1411503004400303400f40c00700c00700420582030640004400700a0f021f10000011036840d10640528071860070000c161414000341c41004c4603001440d4991649060081c203265032580881941507030f81e043c9402d010302010940580354020229401040d9190440420040388881c4000e0030510105852922940c1d0300c43c207027040601d440c01d20f0030303000440c18000501c610382c420102c11681c248101c20760390003d4480c0c05040265106220110101c0d4071050104200100c6000c2c01900c80b0711704001e0903008000e10034400c8403852852056201e8a10040d150394000304001c5c80c1c0008540c01071440742d689441110241c029401c600060b9400c1d1000c0001030f2040f409800090100d0a160703010741b1450601c4007003640c0d440d003d44010004900080340c8100940c0f1183c004016091140c0c0007540c88403113800f0002d20307103101d0a003d82c0660f0010503003d81d541040840302034000d101000b4005c1a000c1c41d240052600305240d00704c0c2c50610502c44580d0f1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 849274469 1250 849273219 849273223
    0x91804081801030603030c12140a0e180121140601140f010c020f1909050a0b1002012307050c0a150b01050403021513030f1506050d110f030c030708 65
    0x1a10340c0d6201c1c00050380055001074003240e81510014010603065142c0c1e43c00640c40c50004001480340c0e00784000180c043c440b4a40964000c0c2c141c48001c1a4294245102840c141003e41e492140c05003003c203d80d030400020510f04282004025008081c9100500820941007441c440c000340c5442100c17025a55200d042829000c0b00d0b01d198012040118000f909511517111021850340280100c1c4466420030240306c82240c09e428091000018290085003650140c051140100d005101c0840d90b004075a0030040081c0c1160600c0096a2400a072380081c02c5080200301c030b00c480c2408060095039107180701914140f06540d400c80c114041c0384030704030402001100d4071584400f01c41c4100300c00344651005448030302c11404065449043d03070b01000b00c00804040100a4155080329610a07030750749544041c0030540c207203000c0301c0e141c007441e00400542229109000040404981045076401141c54a20709010f07100002c078000c5440818418058600304a4840511005006c03503040c9130b65403205907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 849275719 1250 849274469 849274477
    0x1b0604030801061b0b010b0d0e010e240f040201050a090306021201080c030321070905091009050a09031b08250c06020a0c140a0b0c0f06010f060c0809180408 69
    0x20302003201c03092000c407003000744c1d5010a0500c1c2d000c4a0301c29035908000071300b04103800400d080440340d500c40b00f01c0342806000b070040130311001030200200090f04040c12005407404990f500f1070114003505080007030302101e40707910030b80150f0207003000c0703503121002101107034110003d40019169a00005402da140e14602080300e04950701c0c54181d0340841c400c3c00400d40c41c0e100b4440b00b0f90020110410b001d0488400305420b85d0000c50b14145146240d40c0e8a01080018004891000601c0da0b0700700d0800524109000301a405038019904011692803903a01801c522802c08041c869095003801c001c00708010002282c0126075050b652013407030407804000101100e010030007100c00c250745240010380180002115104181d22860000701c2c0c074100744410040c10030075240d0541c040301c1d031400001c1c4003183c1c2c1d00a2a04042d150050500818035130049482e006042e03015500e80c1507003c80400807103610982c01c051480d80704910681d180340c203c0c0050120300c0441d060501a40c1034006002c1005031a40c010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 849276969 1250 849275719 849275729
    0x4080622080c0a06020c1608010c0e040f14130c0906150f02011e0608010609140606030c120c09010e090106050a031a0a06030c1b080f0703110109061a09010315021b0604030801 77
    0x47c02e040c03600c03150440d09884035000d90401040848112145a00e840c2c0c001c1000c031102800d0005200d4003154400003003c0050300c440c0c50012000c24240180038000c800000580302c295000d00c076203482c280c6036008603c44030204c1000c0003440d05a5a9225100390485a07040324030854010720400e542e00d00c0d8000380102d1140ca036040d86045c03c00280ba80040c0a1090102459001e01d01d4079611102841007540c00200150702c410403c00c01d8408104103928030b103009140e011582521642d0740d10004d441503a82100c1e50340716245610041001580c003008952030002c85182c00300e000d4120464010000040880d103a0703100d854050701140503503055000400d80c08a55540c1110340b0138408581240c11300c520310280c0801c8081181d00c0202030b0150080241d14464603203094021b207441042c03800c40307451810840712107444d140d0040d114600c15281c07010501040b20305020310751640da140c0243c1c03454034000000b403540201d080e4111510019001004181100c107442e62441e0620b8018140747c003d00413 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 849278219 1250 849276969 849277003
    0x5010c090807140a060f05160803040213022b0b1f03150803270405090c040c0e0603011509030c08030a09060903020112091b060504080622080c0a06020c 67
    0x4002410091000f4085880c1405028100700b20704007030003110808102e0f1540000c0c000c00300401c0c011400b081006000c0f4074040c0180c01c2d10fa0500340b04010b11200d5180512440350f0043c0070342c0f1001506100c0015184081c81c03140d8a251605004203809000d0440209502540e44894510314881d841025107009044c1e035000c1005031813000d01e403054207060380503a50341644180044160b0300810808081c0041c503210a40312a489594001000e0f60411540001e050700112954074a17410b160080241000850401e000d206407000007207956400148507441e001d684482000c0b40f0a80100035580145801c881002f46141d2250044c80d07582d0310040b040e0001400310240022418070482034032050b01c5d8144e40707041515052581e503001a0503100d02c02d0300c2028007650100001c5686c540c40000a04540d202c45c0d4445d0300d0016494180718006000c3c05017032018002c469a041d10943d0a03142c12540010490345514012600c1480d1140c3c0341401042d6600c0020300740484040021540c04144210b01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 849279469 1250 849278219 849278233
    0x402070303022a100510051c11030c010e040f0b060a0f0219120f120204080a020a0f08062403010c1d31020f070602041a07080d0203090a05010c0908 65
    0x941d2100500b4480203d07120b4100d00b5840300110420342105800514000c66070519a45850005d4055142c1c890000c0407000403210080030810b140301c0c40d100008040300506124030041e030000e04107a4045849a01c83c0382e80c0d0441c10001e034800d5200004029000d04820b0700c507645450301800070390040710200007603c1040c6180341d100031711104c04102c007980941c50254620480006039004003818440304148400c00103c1d6402c5459071000d800200500381c014040001d080c010f000c08040650841030301601d5030355040c02042e03070000d00250001d0b61003404410000b41c1d0a41e51030b4420380801c1c420f6140d42000c020349401c640c029503a40c001d07121a00e48455200c41101005410112a1349940d044103503440c40d102c00060565007803000c0e0100380c001500d054400711b0640c01e540e220b02c02c22240c0a074080b60900c1850106c0088150081c210003226260a41e2604d0310308940c0140208269165000800190070100600114124960110091100a200d030501030311281c458050045503200d195 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 849280575 1106 849279469 849279517
    0xe1b0a0e18100816030809150309010f0c02060f180a21030e0a0c180b0303030709081b0109150207080304090f0b0103050708060904020f040207030302 66
    0x103200c44116140c0181201d000000c1600f1400d40c0d07a10900c80c3c0c1c083c1c144901d00c44000e40780c00041e0540c032400b0304c0c4001111426000d05400c1080c4010040c4480503505402c00c2c03084500840051107c1958440c049940d03940c1102e0480c208080f10307000c10407060350040c0000c0201a00c07400d440c450b9425448d40c0e403104803016098541e142203440c103242030540c0343c4260418810f410001e0480e446958407440c554030350030701509603c1050310020f03154401859019001100016082d00e440b03103440301300a0541c0340f00344901c440714014181d0b2019000703152920015010700584071344003030b1030400c20011410b80030240a00c1c10351040b901d0212345204204040d00c0204404500402c0d8800130620b0501070b940301e444254107043c2420140170002e90005000d50340703d0707010781e8041300c2c0755141e00001c0c505c0c500a03440e4a8001c1e200040500a155044d001041600910041151074020103 = true := by decide +kernel

theorem cover : BRFrame.Cov 849100719 849280575 := by
  have h0 := BRFrame.cov_init 849100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 849100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 849100719 ≤ n) (h2 : n < 849280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
