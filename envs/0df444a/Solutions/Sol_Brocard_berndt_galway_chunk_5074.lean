-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:39:28.38052+00:00
-- url     : https://prove2.me/submissions/6d478975-bac2-47ac-a091-b07fab012a7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 912410071 ≤ n < 912589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 912411321 1250 912410071 912410099
    0x4051801060b1806090a18020c010e06010312050f1309050613090209150d061803020709061203081e040303060501030e010b09061c0b0f0105011416140f01060801060f 73
    0x407950703c91040b0102200352500c1d1004050100c8003400081440740d9501200d100c0b1500120350b20320301600481c642c07811060034030482401c8044030b401850694035544488031100308842c100ca041090005020300c82c0d41480e001c403821080b1800708810317071039542c04003100144402d6035601d1003540e10095200c513442c841c0c040e20000c560020440e2601f610344903040c2203541d40c2480d1460f002251405200d0114505100d160f00d04144051080d2100015240090400c0c2a64120405072443d103807041c04030005500040181e2545814030703541c0c80e160140c9003040c40607040072007110f00440e041044205075064100c441111401e88040c08842a042540c5003070310360486004d80c2000607000041c01c280760061280f926131184030401c0744012803e40b03d01c03a03042c50440b0300082d0030400ca4010002568001d001d6425030a40704010781c10300002c4c2260003014520144054101c01c2454140c407903400d01400b05400d0f4888142c001c000d00b6a0303880e51503000e06101d1144188000c02028000b407451000b84c44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 912412571 1250 912411321 912411337
    0xb0703020309122203080406030e06042001030905061006080c040803180619030203090c06040810150f2402030307050d02030705090901121502190305060f04051801060b 74
    0x2401c2010f120540b08007164212010429841c1820306204900055155010700130f540641001030b5a5410410040d05580703a1400b445001e03849841044045a880140c4d0380d403140c1e05070600580040d030b0000481c050046d243d400b030518001c20301401805241c3c1c054142c2211035507200c6e0000f036644d855001150f409144900c0500307400070407060303624030203031041d4190a140050910741013022140c48070210a500030a042c000c40c0d070000511401c03180030003890a20001c102c42407454a0b042820860700d07051f00c40d8036281801c0d201c031116020403140d441d80700c0280c00c405003810540c6580b2000c1c80c03e4020a10514440c01c1800c40b1216500740c4080200c2e8407d0740651101c9190150300d22407040254002031800c001c110050000c44542e549590b07419008100d140c6070f1440c5091b1030300386a0b8280400d04480341156104200901145030070501000742240305081c00109942d034003001c1001d01018840c1c0300d51103813500e8200815071200400f07018440606000811010f51510487c0420780303c1c5581c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 912413821 1250 912412571 912412573
    0x8061306080c09180a23030f1c0b010504260105280b03060402101701090606020d0c0308130303060314030304122607030b130b011814060f12070c0b0703020309 70
    0x26030740000c50414a018404c480c8250302e0341c4001c08500d186d980c20750b001825000c1d60f00700f00080d94041e11607002c41d03c0c229251011800c02c05100c4403400170305a48564481c41071082422000d803690018404600701014074040000c2c08203152a522401802c02c41c0300e04802e404508060306000341d04140309a03002190080e0081100740c0303440e02044042d0004000c00303020003214481002c1e0301d00b0708010b183e008150f03000002c82e0403410940007904243d00c480e2048100441c0340780c00350100750302c454403d820401580d004c400b204501e09044010b000d00340c00207030030700c00b006042d2002e02c1c400000541c42540610641c2c00c10b04100350048840403101c86071449240d0030780a000b1040350080302c0c070507040319550400142844440f07000c00c0c28010640c1d003000c02e05a4a1182440b156004441c1903031062440751a00031850401d219281c030005522046402000040340d01d44100101d00111586402c0c0f8618818952510b414010418a10804102c0381e01d071316840490200381c00781c02035a020740c501d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 912415071 1250 912413821 912413833
    0x61305040f06052505070c150e130b0d080403121b02130e060a050a0b0301091a0a0b1305070201111c090203030904140f0702071508061306080c0918 65
    0x3803900c00241801601c010f0300302135490700d0092a4030740c0c629128944031050321030300d031a10803500340703140c00452030361060184585100300301c3c04180c0c0c000708061084000315102101c1048441d03690006040005600340c1090b82e000b2500103200452000c3c00c1203c1c45040410501105200100d45440380b06401103003141da403080880051500075000c0f000e03c107520000042603c1c0005160b80741050540d100c0c4000c6d940c6405001c5510320500883c0c4030003c043d070091040c4d10311a90b40c0345c452132200810001d02c02041010030003030a100e4208240750f00b030003890381a02c40e1010f60b084006010580706038015610301411403489900d20303000e84040d01141c03450081020319800070b10014024043d01240d040c001086448401d40c0d03203104042c1511604a0300a10f140342c62f41200704410783c050300050543d8407080e002c020203000e880b40703c0f0110145151034031040d140d250214081c0d0000b15400b500380d034100400401c1c0f224000603447c403046021540342106841d8242c1e0b07000e0040203c600344030a81c002d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 912416321 1250 912415071 912415073
    0x9140907120c17160e04030201151a070503040801110a0824060706110c0d030b0f0607260d090303050f060603011401020a0530132c070305061305040f 66
    0x2c1900c0f018185020a48240784084204455000d000d504040194103d107414002030581c24441e680b05111071007140c15500d81052a0061511500c0d4050b51442900140c1841008000e00c159002489000000d0055188400b101140d54101c901d07803400107221940000c0f00110011940c54010000d8941c5040201c2c0c100c003401819404080305480454603842c81c1d10711060308034018031041811001401c242b80782110300034251142c000e032441c03241790215420105a55150304882c05030b0380c4100d541080e101983c48900c6c603070000d5104441a0b05020901c0d4402803510b40014011078401d9404010523510600d82503180d20003919404d4200c81d00707000600100440b4104620440814011501d01390143d51743e6030303e0174601101e8191124000441c51082da6032100000008210001a9509000c049160490090400e10900c0183c1001c09103911049800030300184000e60300702619005803403d03000140c00b500083d20350501030030100c080e17000d8000c86032290a000c1c941c00420000c0c0d0751a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 912417571 1250 912416321 912416339
    0x31902030c1b060706020c19060509010e01090b0c2802010207111914060906130f0509070503061c060e0105060a060302040501050304020603072d0206060d020904170409140907120c 79
    0x4144521f0345180314140c89400601c280f40f000381103003445007074042814035080300e55500b52008517070f10760740796070504d16404009490042d01540c0f1841c010581600c905030a142d26035031444034904580002501048803640340c6d4190010060140280c4040890901d01d1050042d0000150440305072102c8184042c0001d0b0580e0030000006803000340303c7c03411b2240c3c0030002080c1d580729002060300312104070400c2000014010fa400d0050074204d602c01241e1a042201405a1000600203440b9001c45c1c400000c41242001440c080c00d40c00c003c0401c03c032030a4218840c02040c040e92528030500c518500050000c0c401d0084030140c1d101039460380d0554986074240805504007521181c14030410a20048200c580b0241c000302c001c501325610301d84540303002006414110050800b0780240000c814010158441412243d00030b41d0120a0500c01070444100e444c1600542d00220316190900c1c0034003240480d4503212901481e03d2100369019999202203083d00c83c0440351004069a122440801c03603000703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 912418821 1250 912417571 912417577
    0x120403120825110f19020306010602030a0c1202030d090f020109050910030b0a0b0607120305010609051509030c030304170609010903170a23010e1311060903031902030c1b06070602 79
    0x403441d0b00715a204c0c0d0b413004109007000361482c0d8814264503003031607140a510b000c012142c0100528005545009400240206282c440e0000a0f003000031118840309264400c03c125121141e456404109480d51031030250806810b981d0b0907070014920100100322844c040c0c10150003420304001d82c22001d4a10f03610810100401801800e050b5079505208030b003034880308020110303a4400d224051045d5580c200181c12a00107801110801003415410721498aa8a2031208030b02291042251100b01c100c000914185d0304c4512141c16001c08a00021100400c00601481d29021300c252074140e6650f1052a089a114003c0070b00000c01040b0b48201d840e20340c5d110a074003c40301e808081002c007503550003101c80f4002214541600700d842401000182158544190001c401b100c4c200850701c61911100104010241c00c1d602c96040011004e0665a040003140d0b004c40e082d81c592115008081006926a000100814000d02401c400c00403031002c0000c907040f202100400c818100080d981302c5c100250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 912420071 1250 912418821 912418847
    0x60603093c111203030108100912120b120d14030f040326010b040603050108030712030c1205090304090506060c1506210d0e0a18020c120403120825 65
    0x28000240c51083c1c441d2510000c0d10840c6070010f59595243c40440d91410031045001414103203001c0304000010781401c2c8a012500c040e1503d00002d280044040004001da802000da000042c0c207280e064003280440c490764211110344400100441c1d03603400883d42d01c401c40318690000a09000203000901860405505100b59400d800700c100d00da0b0018003940400780c2009214880200c0c0070810300368140505405441d0300f5010f141030140c19a198540a02c1d0800d00205241e120b0090f8207a1600c02d90000208001d00c107014412420a0180140c40307501074001c412026003800d0016070a82447c900310b070780d07140c42d55000300307200f44014240d22624500a40800d9200000440d20004841900310111007020900b0140c0321020310716001420700140002d2444c0140703a51241041081d2221301940c2d00e07c42c04000c050ba850705011b03280c0e4100220003050112600d0045004010301aa4008001402e50141c440c400240c036202c403ea6952054401c01c000f00304801c0785000300c1540305007010310540d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 912421321 1250 912420071 912420083
    0x70e041209080609030301150f051b16060302032a0304080d1107111f02031806041205100b0f1e01120e0c0a14030703031107030501060603093c 63
    0x3511001020b0401c103044e01c41554079440800180f100c401d20120380c1d042d508950810904407a01503c1c080e003c2c1c002d4201e250807242802001c420310000c01d010411440f403410007038a003c6600c680020703009401c15502c00b43c00720917101040040300a10303001c0d07840d20020000354506503a00c40d692002207600030207950034403645400b0001e090103601c8000c1e04e0480d00c02d44140c00d00c402c00c1c41c00d206001c102d41100c0b0003410f0f161000f0b0701030300d50084200c0e140d401c942081c0048540c29240451030503c215404651000d00e250000c0c0e0034450301103401d18802e00502c2061204180341ca082020840b440c2030031a600ca0b600d090b51482091050f40c00d04c807040c9041c100300c000c0c40d004041c04c0c0d007101c00c12000705409402c141c203840d01c42cbc9071214014000e42440000c86608040e0030340440c2d0b45071890300008040c400101c0785000380d0f44080140000440d4008001d2100c1c40d107441000700500004042122529000b00280c904201d100d0404100e08001c040251440100c40308031070807040ca405015030304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 912422571 1250 912421321 912421337
    0x1009170705031b3a14031605090a0e0106091a03150103090510020d0b01020a2013060f0614070b0402012618060f012d0909030e030d02070e0412 63
    0x2900031540c0c10210810707034940180001c04e00c2c0d44032080c0381d0420400001c10810030030044964852200182c90b00030309159101c20810780707a400d05881a20540c5007080e840450500700040103460601014162815951040400f13540d4503600f5080714aa0000b03070f4410f0034113000047c55210000101c0626850501d00031800d444591039080c10800c0d02e80d501c41c141c9400090301c00800c6064040c0d001884028401840c065040b40c0f18401d800c80c200c240c0342c02d81e15200c0c4036481c83e6520300b02940104041c0490420560ba665624001401c4142c0714420128080394000e88504e000716003074510044e00622102c409660703650045510b40c0001004079441c804001143c0046007862128a200e507203c01a6014017245e9040ca40c4c5c0380900080142c00010b03003c10040c4650b1b421680d01c01071000840004101c40d450f04e40c4400355244d46a00045040307403030721400500f81a80000d904440c1c107816815501c2c0346c0568127040381c445000d400b4038014072800c1d034089000518100180f0704514003a16040003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 912423821 1250 912422571 912422593
    0x1b0d021c0e0d06090302011a060403060b040207120c020a0b070b06010c06112227022a0c120106060c140a1703010f05060301030b271009170705031b 65
    0x1a06000c0c000030b80e4444e956444550030950248294100603818130b060b10124840310001440300d220314000100300507120700c0080711076102e030b405a40203241d10440301134600500d407000500c00c40000e082644110402040003800d04512004c072031a060f08480c2a40c1d03141d895500564003504800b0044030310f039503110b00b4141e0340059071020704900b40b0102c0310000001d07c08400400201d0341c64005a2400342a032a0420135403040055410901c80003040250310f43d4410b10540940c08503644003e09012600701e113541021201080c00b040c245001c80c1c034503041c042181e00150803180d85010304804200c0c00e4a40b103020400303a0380c1c004c070520091b504541003103045603202c0352072031000780c40c81d6100c1c078000c40103008807035040c1c2d1148064141a82c600e800c562450b00e0304074403040058022254000030404604103502034080b90304040404030100c0e004075640c4d41c0c102c00100b0308880d0948288442c2c2c4510301d0303080203a0b411a801281c01800850400300304240741a00f89000c6a006000c6118480e443d075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 912425071 1250 912423821 912423829
    0x9010e040c05031c200601030f0c0509040803040203100b0f1306030804060c0c090e0a060513060e06091603210909090c030b06181b1e1b0d021c0e 64
    0x201502c298400340802c80080d010068035482c0282c00c012088580d03000340e85ca100d840040c1090440e40c00088100c0c0d040d00c0c50800030442122a0003039038120000c0c00810043c0021a40250701552080d400c91b004000084500421621070200c0540d0041a10b4803030006450401b0248000b00c44081c400161250303282d4560b0b0440c0d200342c1c0031801103140480c0b0202403100c0307441804000c2010302c0003441414102501a500c072099641d00030300d03403940d60700030500d030000070303070000d00010b0388a942007058071801a4480d981e802c0c1241e00c2c5500d4420321650080c06c1d150b101c0c224007126441001100402906030384030a41458218480081024440000600141d5030003442074850140b40709540075811410309030203000000340418001c0d6005028404405803482405038001c5545102072081c0c2c10310320380d142e500e00c9141a840008101b6211102043c00480300034422120112141011004c1c0112802c3c0ca40315442c0b020005038104104104031003505000d280c079a9411031409940c4502110001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 912426321 1250 912425071 912425083
    0x1801110c0c0102060123040f0e0f0a0209011413050606090907080f0a29040b0d0b0108010605010306150305070207050d0b090115051c080f0f13050f09010e040c0503 72
    0x850055809240d0a4007656014044c44d809016141030381c0040001420001603488840110180242d680c0d00d80c0000c005071640c03104940d5520740080e515692011442c1650380c030710110081c0d2103032401a000142e0301c04090b80d484e09002c0041d00000d084072940300c81c8801024018146504a0010402c00c3c80e50381da64a481072003020940c44611141c10b00c0420001c040300014034500040c0c1c034200a0f8110700c00d80281140c00350708980c05200c0c60748080400304020780074003405c0355008085010440d0801c0280203142d41a0340d0044002c00c1015611030044050341c4142c420010301482443c50320f610184a41c1140d540300c1c1a43c0103e41c1c4050303a44c0e010030000da80b02041954802c05400612411034001e02550310400d01101004901c542484000740d0303440c0d0700102d81031040e996400324204000d125000d640d06c07160164000350722440302420240c4640d005500c08420900b0b40100030803180b51149d90901308240c040c1140c903680e070802c00c07411400e18015100b52504900f261002516035810448 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 912427571 1250 912426321 912426337
    0x504151811070b0718060e1201110d09020418080f0325030207110f100f0201110a0207030c0602010204030b0c0304060b0d060c0f080c0a30021c02030906180111 70
    0x221480c1c0c0d207400f5600524170f034a80e0142c805071080225040024990211601107030a2049072181d480350121449103004107041e24189101101c00304072001c5540996210b40055402501c0520002c2c40294070310b225800d101e000240503150900184a0001c4c0f408040d50b800a030350780c10105007100e0000140300c4489a1062400002e80000740d10040011001d055007900c6000e071040381c507841810380015080001404504c04100e541003a000d090b510035044080c107244034840c525950610920002d45984ca180030560702031a0255000401c01e01c14804c49080700d400c070a40c45010b84072004e0b0603200360301c080d000b900c800da2a0b56040a869807401c124444140c0704800020b070740c400f1040080c010300c21140d444400d0210107020440d6074100300040b80c141078424508680a004000c107404483c0da07291170b40c00440710642099080c808603e5004080914240b03800140c1c041036170b401e0700c0680c0301c210354a41d03044d000300340405c0c0c03241600249204100c8100c2c0011420741961061001c154104a10b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 912428821 1250 912427571 912427583
    0x2106020d0506130c09030308060415030c03021212070611040530010606020c040f15060c0c0906050607261611180103030c0312060608060307050415181107 68
    0x1c1885114602240c000c907210b0720f020b6090018005103580944184034130b02c070203002d002c07441000400300c2d942c2d41d0001410a51170348803072668949038205041c840750340c1c2c0000c0740180503441603000090000204079034170780c18042801e031401c40c1d995240d101509403040c04005001051202080980d10905481181003520040071480100700e80160070000400c88101c1a07030740740c40b20a01615030f0208a0307010392807095030003082519000c44810000d1001400c0007125050514021509aa020f502c0d00f02140c0544070400718a03480b203120601b1034003d840355907448101005120006480440f02020004807016058452100880c90100d50307400840720009507a4440342190800c900420b940e2070510003980c1710b03280504245005414994103000107001c6c40300c1a44100100340c4602c1c1051489041480140011591780d03101904d030100640b1268400d00810300040741c0b5003441d00c18901c0e405027000341c06618516102941d1071041080b0510340d8450f17240d5416a079079008900080600502c194 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 912430071 1250 912428821 912428831
    0x1020703021c0509090c0d05040f0c1e05092503021c0b010903081b031603080f06031c260714130306050a1404110f060408072106020d 59
    0x85002800c116480e4070030310300505038414035003280750b001013a40c028200a5030940000d072140713108071805005403414141c0d02030412040200300700c0004e50204809103d1140c20408a4454510b0091420344110490140e0480c032020805454660103a50f08842c4c0300e00006500307115803070328000540050040384042038000074108104005044011984840314208210001034600000c2141034039100140c00710300b000c00e03c150240c02c00c0c1d0010140e00502c208881e0707078100c0188400654207041109501149400e00000d03c1507408039052071060a000340a40000b03005c010703405d1002c00342c07a1021010412052441e903062b18402a080c0c08081504d250510355141101c2d0061045a140c0d0300002600d206010820301c0c610340c601c1047c00d5a61003000412280c5e200c00f00d01c002855099904103001450000307001c01d00140d40c952000300101940c20300c104600040900c0414400c900c12402150b010640401c461000080a00180701c5c00c640c2e8001141031a4444a0036a08482c2d01050300cfd580d64 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 912431321 1250 912430071 912430073
    0x5130b0306151201090207051006091401241808100e0d0216050f150711120a020603222004150303020c04050703230103021002010216080d1508010207 66
    0xb0380e098003060020424252500034020f058210401c4113211710310000c0e402050000402905011b820031085802a08000e02c59449c04542e001d48191401d1901c651322070070010540e0100e4981c040c40c140500d03404101441d00300b91084401d41c68011081c2d402442c840f001040308007090082c0700b07445642007001306002c420080b1007403d000002c01110195841b45c0c4130540d212901d03413400021a9411256484038070b02c1c1c00301007008a944030740c000502840002c0c01004020800520034182c034070a82d541117114190031191030742d4000e80710010354003410070310018412207202c0440408e549a03020790900c40741c074650740380d41c039000070542c5541c40c60110000c1c10362a41007620a980d0f0302c00e9580c2c50220322038a1600c000e17490704610169240510b8880340000c180c240a90048545184081009644003200e2280356580810a0008920400c06095003024a07030bc14025101c00ac5000898144003022a40c0c5070100c0303a2207080d03c18011a224158080b401e040700400000518014002598420341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 912432571 1250 912431321 912431329
    0x3190b060f030a03080103080d180311010605040b0109030807050a0f080a0e0a0f090506030c030d05071a1b0d0b0415170d0f1803140706080a0c05030a0b0105130b0306 73
    0x1680d01c860003580200940004030b5442912030f07044a8202c100e41d41c0c0c4101280400000d800c00c0a50203c2d0503041030750135810181d00401441c0d0310005203008003e01c50b260020481950507900c8040d0000c0c004074010700100c0c0c0142d00914190744520101e0303900344603d070785a43c5880b03024882500e03140c0c404582ca103000e54001d0780d4800301d84d00403121107440c94184448a84003c15600510b02c020303642e080041c0c403644003082800318038000102100c2219454000003041ca81c0511001c54040d5481c1000600c1d1034040460b86006010780c0c2000025441618002011074000054003040942c0750800348195448030320411558511255008803198204840c0c441548040444034070704c0c0e8007850f0000c0c0030540c84900c09401e582e16203009410b545c0c110714211001c640780d40000d0540c100150089034140c00009104c000c0302c406488804055030b50300800710031181d0303041081021940070000181c600c074003584500074034031b0141801c0d41020010718406040c84029002034810041c00000c1c40014a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 912433821 1250 912432571 912432589
    0x40905101505040b180d0b010801050a110423150d0603030305060f0a0e060f03100c0f02160b0a090e09060613181b031e020f0a0308090f03190b06 64
    0x420750900318542071070700c1e040784010f205003000e211581c1c50040108200f81e4032040c2c0710b860391303401101980c025611030600743d0092506440a920040ca4440c2009010400d10140c4c5c040b5504011144102807a006a600e1805000014582d10020610f01414510843c80180c110001c8407880000c40c0360441c03070050100c810203000d0b20700c44e1002d9090521a1755445800f03000381e0340c41030740d280035a45030000860fa11030901c04000c2d80c0750260318510301c48030400d58000c41200442e580d9140d0740542001044c1e858004503a03680c0304c0700400c120305224150800c00204419034181c07525803441c9030350f001c11180c1070a003a2004100da4100748140b040a18151b98980c1501c1c55031b0400f0008ca070310a0804440003103603541c0041800511802e003090203981c10440b10000c6802c00a140322440501c000d0110450034045d04034413031900e82d0164101410a6075000054130b6000e50190f1800a040d000c0001c039035100c901969162090712614440780404e90a00d5150510800c041b01a03401e0a00800030004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 912435071 1250 912433821 912433859
    0x2041206270816020402040b1b060c0702060703080910020418060603180201080414032a0109030e0418050304060f092301080705070203070609060314010b0d020c0304090510 76
    0x581840000c1d00422900c20031256540300c6128581841034840c80818003900440d071001040e1304e400300300c0240700c4000181e03034647c621101c000e8501d55a215a242d02c6940160388002e90013803010310003800040c0c09a03d0b0590000c0c0c038002182d0301ca4503440c214070300303a0740580c00c0008403d04d88424505414654042d240180034503003414004481380a003d480c515040ca500641080204030219090140540450684002220540b0350300d44004003026911500308030b11080c04074040300e40d00003241041c07145007801649590b60000500003001000b0282c662880c124840c06000b017403c00008200304004c02c0200200d4032426a20b83d01510003900d400f00c01ea1180310036400144078140050300740034240541100c00d0070900019118400202c8450254060094041c8144840421b642d50011104000ca841968052080100e000404a06a0820b102e003441141090088400b041c069130083c0004000c82c40481c0e041070340c0c42a440090704c82c01e5410032034010718107030144a2959015210140c0c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 912436321 1250 912435071 912435131
    0x3090f0308182b0c0b0f0702090106050705071202031005040309170c0a0603020a051303050c1002160329010f06180305121c020c10050601020c01080a0e0102041206 72
    0xc10700e4074180c80c0c03c440e040321a600c2803061401c410030403074480f6000c1c01500b00c0506841e02d400c01c1000b4814190300840c0c2c244d1150104c0c500018a0500ca60102d6007030907808800342c80d0182c80c1081c034400032041e40b4400c0364503004800000e02ca004645c440c803803181c3d00958a10040a2902400c800507404142070f2002d55044021801d40d5030f00da10400d201219428500143c6e07401d00e0b0081201d00b400380c07504454404962240000921400203050340c4540e034100c480804020312468145e0369102c0300c004410403c00035007400c02c045071002c0659041001034800f2161242c0500c0244508840241c00100c00c0d9089000280102c580c805048600c040812040884103400d60711079540d11901240e000140c0c10300041c8030711100000e5620881100e485507015034aa1100184c03454480c0080090b507003034140350000007042c640c0b000800c1c2c0310224042c7c603101c02585500f140c01014000700010030307080399000c020008100703640c000c42d4060903018110002e01c05070348410302101c0300c0c0800e803a6900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 912437571 1250 912436321 912436339
    0x90906040c15170c1c050712020720010e0414090609060103081e04090e0a1a160e121c03060e061e0424050306011203170403090f030818 60
    0x80c960700082d502c03c0b8410b01c00d180c0149075a60340440040b030300c1200100860001040034003d858404d03a00954002e09a50315401c44600c6940c05900490280b00300140040c0d2004000313a200d03019000300b5455020040c5003034081c40c1c1000300410705940d180d1800c8005800c2d040c04001424a09002040e0480710380320203042d16502d036890750001402503400125030081010504c0201d80c61304011600107100c8144140040d00d002044140c485010490a441e10744000e954030364030480203080b40e1311460900d41b0420b40032a00802c12140c0800b00d0101a0b0071101c0380104880b007000030443c4400c10b003d085800480554034000c020700742c9101c1d500c20f01d00703102d4420a100c89507480b0030340035080b004054a500d242400200c0042c0161490124020310184100034040109204c0c07222501515401e074229049a40d035020034003510800c40001400198068001c1082003951140543d0420302070300e82201d0080e100ca5030144100050340c07040300e0340780b4000744440d80d82c50345c1440000139800840b51814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 912438821 1250 912437571 912437609
    0x14090a020a15020c09130501050103060204060809281103060a29030a02060a03091208011d0f0114120f0a060c020d081b040b0706150e010303050913060302090906040c 73
    0x5a0380d10402c07407545c850040c41000400ca010100402130fa00c540000c000d20083d6501d0800710001e44c081d02034030002a94030340014400d031754005540e881080141806c00c06180d0b00407003541c800820f49804507014100001300c04890703a01004024022803a03150b0005500b404e0990050304c405108802c45010304031081400310950303001c03400b4955160117661050307581020030b204a00030003584034028400d500880c6da8145555004808605981b450041c0d80c0c010155403800000c2c03070f001140c80c0c1c1c1e0b101c1c00d00e10041c0900120307182c0c00d03181707030b02c01914000300a03400b59140c60a00350384181c0c00c02c49511140400040c040c450080c02c00d07402c0c082c000782c0f200c401705410042c2403520040c00c040c4003111103c984c0c0441c080c00e000b280c2c01080502c07019900c503062407400310080c1801c0c80081d200303214403400100b442c00c046540315040340c5d490344400f80b07040c102809000d000e040491144d404540d4460000015880302c000ad144503000c094090000c6203014500760b03c03c954640c00c252100e00d40740c0c201c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 912440071 1250 912438821 912438823
    0x1609061a04060309021201090b010611070b043f020108061e0f06090409080c150105060a110a020621091b0622060c0303050903090d03050d14090a020a1502 68
    0x1000ea641510f40481c03520024004110400d499154031440c641c81d116140082c4a0b0012900d41650010390f00d80d810200ca40308001e40c0c0b00250300482d807043e070b010842085000001805400880c0c41d1440e5146148801d11148a8a98030101c02e0502c0c1c20245c92a1000c40da449086148e00c0b010072524001e409a070000411042c1c0d00c806440c50181a0804803094035544003025070308000d00c001d2007071200c2c014918001030305401024010203107209001c0080a071050521402d410713904040c040a0605505060844000445a05260980c00f070300203141c002d42c440d80010b080c0001500e00461700e05000800199040c00300404044042e0005508180d00d001c11000046130044101d5a00d46c40d03943c50300f03180c0072a9100360149080821204400114141c00104c0800e620740a601c08001175660003045030780324400c04c144154804041040c0f4800079016002400d50305100500010302c04000140c0200080020745071045240d12a4154404600e0308840f140040d0200c07142005144c030f50b011020f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 912441321 1250 912440071 912440077
    0x4060f09020715020f0c16060c29010f0314060606041701110c0a12080c09150d0c051909050d1e060f020a0306060216090f0e1609061a 59
    0x220440c10703000105101481140d002c1c0241d21118001c046540d02c4640c10010802d91221640c5980c030301903410f1001c50500c0e8042d803902212446e460710721060329255100640c18517101340506094075440d40615502080d540d805000c0c000810050f11058214204080228110110005564400070400480b5103580c001c1d07408890b10300b030301080b10030503807100703140907013500e00c8400010040494900e104140015001c0c4c0c500b4022148440b504640b14022281c48034202c0348412102c108001c02c11987c1822407542880266030500c26052901e44031021094695100810b0001203006c0f40c2480680c111090b80025603c4908128a40a1409000c0340c400d90034150b001d8001440b01e495070351303002180c1041100d542c1d13000d50200103801c80c800440c00250003c00302400080d10b8208040781290000900001d00200b0f039000c410750510f401035090250245580d4a601c485e21f8404140b403170b100c07c111952544000f052403881060510744c22404032101d5901030344c03107402501c0504004180100172 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 912442571 1250 912441321 912441329
    0x304050c040e0a06050901020d1b0f0513080f070e100807140316090609060f0e1302040615020303160c120c0c050d060b040b0f2b0b010e011404060f 65
    0x804500b8500118a0328200040440043c01003818442001920b02c01980104044104404100701e1a5900140705100c6002c2d0034100001c04c10101203c1d44042c003803c0a8044405403217021503840f078030b071500641001119200243d49034401041840700072001701013a40c0c40002c8240203007441d40340c85901d40d0b44030340b50300c6840c1340c00007180c1d060115503c0901c441c003982c520310282102455612140e0000602e4070b4414400420319080021604158200d40030040ba6450b1001c036a56403108206041c0d000d24141c800ca900956a0034005100c4058070880f030141c07809500956200e10740a0b098100d20105510030300b0410201440c8a40042c00311000c100b00c1500c24540781c21040c0f158901100c8146103504115401906101d5810400407190440c1100c0001070307400703010300d400a0701480b8041e01c2003000d56a0210f00190303c2040303030141a05601d41c20754088440840d0408071340b62204524070a800084001582d6030052200c10703a0340e9107055041805440c208007241c0740c00711484010380c070360003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 912443821 1250 912442571 912442579
    0x120e09090d0c0320030c0f100b0108150a0f0b0705071401140f160c03053705030909070e0111030405060703111014070e060313060902120f0d0806060304050c 69
    0x2001080c0d80000a442609000b4000c00c803580d91180c110b44550b2841911f007560821b11800b1f40b484c20b501751502940305003080c1a12060ba041c5c0705d80c54144040020403c58a4000713a070118002410040c1c42031040c01081500e10300e0303a840c030301d81c10300a00340416034020450641003a403100016990040c0e07129907282c0c02c80c0c03031117455004000420740c5500c5181e21124a220000164500b405401316152049034800d50031078003039442421307208041140200030340ba40303a0700d446428105444004001c0d918540302e03c06a925103e0aa00020200d0314150360080000b03809825829107540c00c13803000c030051800c04000b50f003424904000201d951140220041c00c024080103980d4181400300005156080c01030814044164444510412401d00300d070902c00007600c403034944601d8100801142d004008954455440501c66203600c00036050850080343c2185000302d00d81e02204061000740515487d51b00503002c405c58813400181a110003030049842070200700240000108000398910412005031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 912445071 1250 912443821 912443837
    0x603010b1b060106080709060819020a0306260613121808060f0a050109061202040c05131d011d180709020f1914040e060607120e09090d0c03 62
    0x2a01c10010302410307050341000391052000100341031790818581c5100e000c20741d43d10311400f9a20300b0203c40300c0505030b0340840014000c0d180024441c1850300100002d160508000c203d00e682e640d14030400b09802080801a100050102d010580050061070b410a50886520398422107c3d150800004402900d081c188582991000485102081104001d010b918280d481d80d01c0c003410b01e4220b40c14200c2d090f4600c2e51a100010580441d603110b8507055514582c0707951031801183c4c0c04d00000704000c0c14070105008060044102d5034120b0710900c000781c0302400b15500103890840c1d1018514030b047c1c004d1811002c3d070301d030100342d004034155046501c140203503a4882c071040c02118003070616540e604052000c1c0d00026500710080640c000400c1280000c6100d1440d20381ca121048400403c8200e544698200400041001960702402c4035000030340100181e140c0002a81e4021030003200c05142d8000c03400310711000c0d25914101d0405540f0848110251000042030b140040c1000c2c209800181801256 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 912446321 1250 912445071 912445087
    0x11e15050a0b03181e010222080a170d021b1902060d021614070302273c0f07030e101d0604060516090803030f090a020306071d0a050603010b 62
    0x1c00100c800311a40030341043c9200e4001110b94003030360110070b2380d03000200d040c401c108411410782001c2044407183e90252035098120b0347c0c0d000741840c09007a131040c0c1640a004200c0c6030141440100005c9010400c2c84807182500503070140bc10a140d00344c11000d802c1c40c0aa0009601c0e01d20854241a615000040c0c1c0d540104040300061140b1020140001d4605d80b10007a1101e0b001540700140e034021680440609040d03100d000752303a018614000c0c0e941200705c0200f088000c04030042c1e40c1002c040500640c0b1140c85000a40f10b44194014407560280d901c41800b0108c0c403d90403943e084116403400340140d0014580d0142e40d82800c0444000180e981d0300c400c10158241400d4418a02d500c1090f44c2c050306180c1040e002800381501c0603485901d42442d840390b05401001f0810440310320303001450842e92100030080002000800c070044a008400803000103130380601c5400d2180b802605c5d40c601802100d140d040c411101412240d0042c40c051905128a0380e9040a890448000ca0b01c42a6aa200c0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 912447571 1250 912446321 912446323
    0x30303040f02040917130b161202071e03140d090b0309010f06030b06090c03040c1e09022101062a080909070e041109010c0311011e15050a0b0318 64
    0x8644005891060103200d080b086105c5400106411180000c500c102c4648408804000d48151121520680b5203590700034005403603003c00399140ca03400d005640300143c0d0703142c0040e10002c0c885084010800e82e418180b04008504810420031001c2d0401410a800c14a4002d4000791240c0513543e500076001c00000c1c0240d509400c90380c80c5103000c841c04d0180558a00c0c00780b01800c010b41c6c50b1032144900d00c0000d403200d0b07009415288242e40041d0085c0c500b914016188240608000021070754a61a84000c104064180000c00d0404444c2d02c0c203070501e248003000b01c40f0001041e041981044070228030104050031095846641561002c41741e2a244201d1401a400f842140491500081e964003009100c58001005008000301a01c050120f01c0d031410760814640b03d4200528082aa424000780c0464458401041644006000000c503000c4418011801d10f1030740c103000c40820384640c071102800d10280c01e0034000300720658008268a08010100d03129001c01000b03120b00d14081144900d0b0104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 912448821 1250 912447571 912447581
    0x303020a0f0e1815040c0c05010b060a170c07080c03090a0e1e2502030307020721030f02010f060f0f0e0912070f0b01090f0b0901060f0e04062c0108010b030303040f0204 74
    0x8000b8000c04c01100700c802d018012030742007e0180e0b51940307040e011821a0400300d003245c01c080d001c0c0d034030f106600d000c03112001c0320000050003600503014103002c118002041c00c002045803000101c0110b84075802c9408000b0802215000120790180400c02c3c480c03034480e507007406404400ca080010031596101c07a08511510200c1d0b5101410040e09402001501c0e000700095016a44070b50985a00d1500c91001e40180116000154400604460a600480d114840702498603d841c400840c0c621441401c5030700307980198200300345100303040c03404208801400d1040310081401c1440c1080a117400205030b501c421008805080c1d40c40d000415804124030032a481b03040560254800c403540d61149841401042078402c0a03041a1401025803031078a0151040c0c0c0c10bd42d8190742e0888042c44002d0102c0388421750588640e002074403a0000f02d180e420301143e060a42c4100c4452048410040382107401e00413041c4c0c4600c540d07034501500700c0c9242d10040100d0303034020b410030340c9540803507058030100700242 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 912450071 1250 912448821 912448861
    0xa0b03071a0d1e02072f060702030a150519050c18180103050105060906040b0a03060209060d020408330705070c08012a2a05010204120303020a0f0e18 66
    0x100381c0e8201036032400036a9000e01a1140140340061440d45010711010094281105140d006e585050013842146804c100810f100c510140c280d9100751303c2c0c0e07550545180326100424240a84036404c0041801d01d0301112000c00592a40c14058bd003002000840c091003601c08850f803d00d600484402181c071003030960076214405802c1e0403440c2d03075a810210300a010070744809119a400b0408219030745044d000d42454024006c004820061850b600d800003503002410484d00420103102c0908550524406480204001000750900c0c2c0325800c60001400008401e000440d018010710050410542003419480201e509201d6594135150400c050750709100c1d4040351003582050b888114003005c019602005007000102c1c3c0c0d120f40c003250780580d4904144008a1801144040005800300c0c1c03034481c8100c0140030b14001071409485540e26401c030f400c08042500800e400080e054400c640c0200e2100d00021503241281c2d94180000c0060704c0c01180301c181d845141c040c0c90100d000c035001041a22088 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 912451321 1250 912450071 912450101
    0x40b0301110d06030b011706150307080a0311102307020a0206030103050a03140a020c04090c0302040213030c050427050f1f060b041203050a0509030a0305030a0b03071a0d 75
    0x5030340e801d1402d2025148601003102da070301818000107841003601d0380b840e500c024120007400c050364800030308010b0100c001019a6141c850511300241c0a0f10600c65510698040d6940a180c0d00007102d03032515100d030305400c64540c2441c000c12194036a0000340b445e200740f0016444071609443d448000c914051034040046c0d80800004000010000e0020341c0882103482502c400421f0703003c4102d41110303030141c80090409600040001c0b041392900c0e43c420001c0a105181110503036489030041812070b0403680c10354400c20881070082c400e001950345510000c0c0000c84044c410341d08440c4d00411889138841231840901c99820a103003c105061290f0444108103404654509000d00082c0030300503010820b03000b44078134240d00407540300b108030101e50645507074120300c1403002d801c0c3d0703800c540c0d0b9440200b05c081006010f128030035280da024420f24171954066640c0c180c4030b042c020098400c445d45600d01620a41c08403074204800980a00b03220340308500c2100960701c829003440050082c281e584400004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 912452571 1250 912451321 912451327
    0x4091103060102010e0c0901121707050102090319050a060b01050903060c0d0c08040b280204120c0b16020f040f05040602030f07020d022d0609150a1a040b030111 71
    0x10405824099485010242c1c001c2c00b050019072000360f250070400044540050361540148180e2841c0108086040c0c4280c1440403410341c80c00302c9482e0768108c0c1c0000c847c1781e500003540200b141340030081400003804c80a6845050b8a09070b4889a503800d510381b0040c034181d101e802c0c40420703a0245040d2081d041001d000c0c2d800074034005400d0a0254428401c8a4506140043e1108120302ca11903840c46194401a1141145c40ea20005003040d520581409404041400c4804031076201e40040d200a0650b18009007550f502498400c41041c4150441407015806005600640c684130100d6550650141c0742e010041240602260240c2480310300c3c044d100d400c0c01d041c04104081039008600c1070481d10980c0306180c07115403003281c40710401200b07800140d2048004210000400140c0035001c07041f10340d80202d42c12000c03641d03424030f0f000715a0800c0a40210701c0410071015410a4583c0c441b0840d10100595060074084000c041210540c15000340d6a41e010302c0e40d1900e00354010b1201a043c0344505031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 912453821 1250 912452571 912452591
    0x601030b06070302070f0b04030c0b03091c021c0302030c1206030c1e1206070210020306130501080a0c060f200a0602301501050a140a03020706050c0a050a0f03020409 73
    0x2680748414400e01011b00444540054010307104400c0d1400d4a9025040c1e0007989d1800c00702e0b008541010b01184080d000380e07420b0803008110441c06190040443e00a090501145004840c40c8882d001d440410315004204104191802c80c00711004101001044a038545402000c0703898144401d20941d0081110f408440120900203a48002541d0407540305207210011820f01d074803003400355440300c05030348000010300107041a5000b075903200398040c1c810402608800506010f450003a0710076205a00280d56640520031a41d000380080e22031403c04900c80c40000740018042000442d1002c908079210034000c081d8002802411507641d041758055403600422003401000c08231000140074105004003c12201c442c04c01030051040342c070f441e03512500603031060064074640d0248084004000606029045854038840580031140081d900183c640400380303030031012564080c0001180307140511194030415030150444c0c404a40c1441e0404102c04210000d40203402a82c000403446410b00188030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 912455071 1250 912453821 912453823
    0x60c0c1503020c1002070c180b1e09241203070803150307171009050f060a0b10031103070c14030403150b04052a0405040e10050907060c03080601030b06070302 70
    0x44240f65050701640c484080300b400c110102c2c407031410014594950134400b0001c001640314481d804c000300300700100b07181894600145c42c20070406145010780c0c40c08242c006031400c2452116620000001c4228401071104124a00e4035110020040c40703211b0304030080d407103a50280b042c0c07004560301041031303a140e091246c203d004011500003018001d01c40c5000020354000040c0c0d078900c1c44002240600308060349600233102030702010b8410b07265481420644c0707600307540800c807051040303007400ca0000389154403c00300304020061001d11420103003032442c01d00507c2401400c80343c004100d803d20045500c014070b411505001441c850800d213000c041400030500604001000000003c090300f081500d02d48001c102c00c880094403e40002c280403480e5110820034079801d100f080d0f110500480c24141d0b507200103070a83d0300c04281124035402c4807401e20343c6402c4e540542c541144440003d402c41c42d051002c000d159404851014040200039800f2450070790081d40484070400d4064810f90380c84446003000303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 912456321 1250 912455071 912455077
    0xb0601050f0d140c04060e01030209040605030604240608120a09050a0e100f321003021815160c050619110607020307020402030604060b070b0103110409030504060c0c150302 76
    0x301541c0704419001861040f211421541501c1180c3c942114010841f80110000c0d0440000301d03401ca6500d04c8049901e58003080703118429407180b203015a56007800a591007a0860400001e24400e00348101800340c010040740340450020105805c50301c030003803841d0032102075a41d030344103681080d840000402c0a03042040401e108180c1c0b0000081c00d1a90703400c089103146d416108882c84814240304400c180031580720b2803101d510004c81c4d1080c0009424000031030250340b80351902c01196000515001ca030714142e0b11424000300403101c60900501c001c80788501c40c41428029a1069808800003003081003084101028000c003510082c0c5542d1221400d00412402c01c41800200303c0207009491014800201c20f40310328103550145003410415401d010180d00060521640a0380741c2201003085059440075107115030286ca60070905500d1810700e6100d901103030441301d02590030002e181c1c010a4214084134211501c81ca071456141496080020b0384a00c250400a8031141c000c411b060200da0540207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 912457571 1250 912456321 912456341
    0x50904060f031406071d06030901090c06020d0e0a050d02010503040c0b0409020307030e070f2c13140312010308070f02090a0516111b1507050303310b0601050f0d 71
    0x215070103600c404c041a036130650b11b410018654841603c2094040c184003000d1034005402c000041144000c2d80d0b6180c0c14000981c002da00182d0200c0f00085060358030100d941d600e040103442d080400d40c1482d001c90182c00c034801001c0d05000c8000046400c00c51081500320081408041251f00d0300c2c1c1300c2c895180a544144c03551000642040380d91a01404c0205e0014203d48200c803607460b100f0318002d4a00d144079980400100a058124010000a05e40c008018403a1500100800c0c40c01981d1610081d601111081344003560710607c2606200000071340107134103483e0801c569503110521032074011100c011080d0002e41228030343d0240300710031460303030032480c018844c0f45610019448949400c46a15602c100c1c0c1c000e203a0b1010f1004400300d01c61501a09061101030302e4a200c1c3c0380300006035200756000d910221020340c000410408604c5d4a030081c0080c650020407a850119426070307140750300c1c0b04030b1007000e0a120002e10120740d00c0c0e0b00940031240c0180c071134801c040d01e52004040810081810b842 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 912458821 1250 912457571 912457573
    0x40602040e0f06030d0e0604030c0b07030f3e0d0e09070302090303071b03170703030b010801081b010201021b010911010314070f1205180c030d0906050904060f0314 72
    0x440c10b441086022540301d060060005d0103840d25880e130481d84c24050b90950350704034404100c00f0021420412324a800741801920b0640c0e12001854000c000903807401809041040c3d0085080e500298802c07000d0804507141c03003d84455009141200c80d480030420081800e00c507055098200d550002c140c1d00380320208940b074103651340d034441055080e03209082c1007581c1a002000f00c42c00150460449008598000e03c0224409480c1e590343c111040720400005400700c07000c10385004140e494000d01407220801c0c6414070b0b00354507040c1103e50700c101c003d10105004401901d0f6103107a0740300350305660f1800030403500007844010103209140200035100050700d1103081e4601001b600c0d4041d0241d54851058466a240c2039590b940003200e032442650165010480b0a410751444001c85008171350007551040c0341a503102640380c840d9882d001981c44a5402600840c100c6c411a40d008011801101d4217400c0555440c26810b002500401c0030341c01c030791014504500044184000d038005800340045d944 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 912460071 1250 912458821 912458849
    0x1f060e010f0305060a030318030c0806191103010b0a02010e0106140a090c091203090b03160f02070305060a0b060f0c0c030d030204030206090616061a03191203091a04060204 76
    0x380882c25500129042500403050f04410800240b0950145404c80c50b864084040c66407a66103c0c55401040d903c000350960110080c03003544080e0700b203100104005200200040f1984110030640c41c0814801c2001c080f00104828014a0007904910541c0a86070001c004558482030f002000d1290300007010b000b80500c1c01c020a1703a100c0e500c50a00d90441035224a0780740e0349810300780d90110314407110490030048251000140d001c041e0000d9401000c1c082081c0b0303511409110018050111000e0071001c6600606041000c190041000f541040c00e04170003141c0038083d4400b0030054031030305c00b03144810702c00018000382200000c100c280a01c1000c90170749a80040d2490101d09038040c03408043e40c001401c01c101c6003d882c00c0c200034600c1c40c00910100086800725299601219000340d41a42840340040728000e00386010301203080903050800030801c4500c080e442d01180a80d1200100307080c584d580d4072460174800e09070511001070315403271164001840c1c286070540203500a4424048500180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 912461321 1250 912460071 912460097
    0x40c030b250f170603101d070609150e010c0605060d02060f040812040609060e2706150708030f27030a030b0a05060d092604230d03081f060e01 63
    0x40d03242c0f0760044034018018000c0800c06200c80006040d10000300c2100780070100015403802003480b41100608291312001d81141c6090792a14804004201d40360800541c51040c0342d0580c1c00003625a02640c10200000e001d58942c0d0101d040944003110280d03102001041c800c00844510000340181e80c0d0100030b980c45e1200a40742040345015500948004c991500001d00845215100362103418078001c02c0d00c02420030300c0c031110008800d109007a00d01c42030a88200711880c1405e44011032946026044217203000303e5611540c41c0e9000c05009491240310450100e12401607451416000e1566060442d4003001801080c0b40d90740e102c1c040d504d02081c02d0940480c0c242c82c081c510345003107640103084c8a03e8034550107900c0b002841030017801c480b00351240c1d8042d9000a0107250360340f02c0c0701c849d011072541d4600701540a02e411001101074030102c88088800a901c2c4c441c220045d00440d49406c0100b6151501072040c210f1401200c484450344110000024050358080c0250400b51404e0b01e178000e031140342c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 912462571 1250 912461321 912461357
    0xc050a080f0114040308070f360503070b0702060d060806070f0806060f1c0906020c030c07050904050d0c110d060911041103070c020402070b04240203040c030b250f 72
    0x8100c130045d01159402c0d00050f40340c0c0c015909a10051310510300b0360079000081c4980c003240b08110403402604808030554074201e0030080901405018200c0c010441036140100c01001481004802801008081141d0703042a215810080c0a01040301c00e40c2c0b458035054200801e81d103a00912000010b400501049880c1404000c8809000240280b0b61a0540718640107200c680e0181c02199610381e0341001074041803142c800f5144815400300950354139900d0310440c2d0329001450700028032404428083c04005440002e03030781c06d41e521500b0640c0c154081800c04680c41500480f403035420820814060301080500d500021083e80b1440301ca2980005400a01040f40c20108600480000c1003010840306402040914035403440140054640001941c0e0380c2407020050314200d80500018801c0400f141b00d101000020351110300007103085262540f11168015401e10010f021580c3c0c0c8804201450081700e03a2002c08070f040c884180c0081a041c1f8010440c08019000c0c900082c4c000c1b160b9454182 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 912463821 1250 912462571 912462611
    0xa0606050a0e030f060a1a09130b2208040302090a0203042a080307050f061b0a0c11032d01181506150201020405100e0102060f040c050a080f01 63
    0x5940e680d050034540c41c407000740c1d051907019000662511405000300b00c20281040030b14810328030340380046148050001e40902226170f43d002c40d88a0a09081000304840a00c01114440c9802c010401030617141c0c050803c2e44010b50010840188004403041c0060003681c800a00480340b09035000c20340360b66a0b6250800720702082d1801041001c4c90340e810385000c0012111007003800384401c45510480c0c1d507204417910755409040115100d03003140142d804201414000c5551160000c1100c14543e81c0c04d2100003103078455103082e981400440103d0342e080c0315070f9614071070380400023404071018a104026040462400c19042030b030301c0c03800880254010f090600074419500c0c0c0d0744080b0740920405585200d0300d00411403240a0040c0e0b036081c00a0701189450131640c00b5082c540005070346505103024030286c5800d40200341c0502400039299595039a000525a5022140024140315074170b0390b2410701c2017605540d128980c0440041c2e0003007512400070450b000c503440a08003c0043e007159030250b518540c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 912465071 1250 912463821 912463829
    0xf0313110f0904061505061305040c180303110709020708070b010f1d0a11070b0103030207080318061309020d060f150903120512070903050105090c061605030415080f0a06 75
    0x2103440030209000800b141c01c0180c5000c003441d0030700415601c42011510a0f00140323a26442a6121501001982400c1c4102c4415101529007106080040c0b00c481141440b10b110050070020004009441844140081c1d009400c6580c0255039441c5181003071201c0d90000d0000f6034406140400001c3d803500020609021107019800c0202802804801d010307401b44010484040c1d15141d1b41c141801304460001041514821141c543da1035040d0700f8002d240881a401c5500c0641c8104040c503000414010220b40200d000c41d045a5110300c01129154a117503658407084c28240042441c14000d0030b65009042642c0354044d44120301c6903914113544500100501da0303008184029402d0020414246124144e54018240b2920b0080903440c03c45000b14101d13012000240b40c80014030070880c0c2801500d030404030540c003c042c201c0001c1c000491500c5007200e04090000c03c02068800c0203400c1c01990010000c0d0800b0b070074228004030b8058a43c010455400446010100003d80100014896a030030b032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 912466321 1250 912465071 912465079
    0x1e03060705041e06020c1507020a0f15020109020d0605190f0614041b030b0a030c0b04090e0102120105011107030602031005030d020f071a071509060b03070605031b0f0313110f 77
    0x206c01074810700980d0585901c0d111074004040054501580b541c0b90410010301903c984038201c0c0345010707401e42c0110a415207407030469042103c44000b50303840061209403981c002e0000100703610380c0000c61a1041c0321005405005060a0100341800701a41c061801c4401d41c91178050715021810800c401c84024450380c0507850b5000d0116119141310340d01107140060042e043c0f4501d95100c0d00c4141e122001036010812918000905000500180c05002d461010950007941480c407120300b41080134205025040c10440762082e203040007802004110300468000301c04564070309001d990a03059510318020380d8004d12650a0408032030b0310008201c060b40a6070360160202b181040e1103401c00420100e40807010031005c0c000e14020520440c072070a40d0420f40880050001e00305d103022015542c02103020b1307210340c01c12003080005642100c22030b64425001e00009800e42405881d4840a001e640b00145109001004200ca40d00c540300e030102800780200310640540c15a10100070b203103a24210302da504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 912467571 1250 912466321 912466333
    0xe010b120c0102060f0c040b0408060405120711101206090522051b0f1503040b2215060806090609070b031315090605070302120a0902010e1e03060705041e0602 70
    0x42030b00e1781048a90414024000285001d171784110060390364010790002a0300c0d80040d1305120410038104420303806100400303c1c09050280e25114000c171613911603882c034001d00600022018041c4030795000392200c01c1052040040b20345525031032000f0a002c8907400d036505c400050114400301c940c201c039409240c2c010002c03e400724008903480c0240c6146941c0c0b50b0042281d1155081540d42c82201101c102c180850070b0b0344a19040c01d0404012402804900a80b102c41c05000143c2040250034130099401c404152130801d580c15000004004030b52249189020781821f100210034003242e024006c45100b4111060179854010340c14007840705940c012040782c01780000c032000034010721010101000144002400c0320300c1e504c4441c2555011101000000d5000030000ea6410b41605807a1308a00c000408001490b600d5002800100d003c1e00620710403140d1003030070380c164010440c60044454001d0140ca0386070601e8600945941c01600a800011201002c62500d042c4c0001d0300c1d00c1220301c41e900600ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 912468821 1250 912467571 912467581
    0xf09060307032d1109070e0105030a0b0a08030708040303020d0207060c022206080c031e0d08061306030f0b061801030b0c25030801050604180c050c010e010b120c010206 74
    0xa50118540c41d90040080058030007880340004800c84030015000741c0f081304456554030b0401c40100c130000d144400b8403486c0e68180420743d902030152a4080c0c80480002180d2900500043e1050010383c0300140c07900c8006459420041c4200c0980202c0e4480d408035080c6800644080e07850300402e01508001807400c003d50750241c50035119504c014550b01c4a070014140c02c108080050303a2440e000070405a00000640e0503030709041250805400100c00c01c1c4150700b41d030321070043e1580b0b0403581c100104480ea10108074180d86071400101c1c5003052510400c19640e580ca0107070f00510344007001343c42d80d03a06080041d8140c28001c0c40e0b014160643c0c88688c0180c0e0a544d00c145c8040009440d25100c00024046120307180c00a101c0d10724801380360f1601c41070790b560528004150ba24140c2141c0d0241c139003803000b0002c20000c0f010015103031094840200c0c07440d96500048a480c09040d00c0c9056075803d081404031072280c11b501000507060261002548011076111280e40d45043c0060a0700503880040066 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 912470071 1250 912468821 912468833
    0x608030f0a03111c0221160f0f1407050c0a0609050a0906060c0b0a06080f060412090602030f0903121614061e090c10110609060c0d02070507030204060909020f0906030703 75
    0x10000c9007220003681105035040051ba010100700311381c0a803404546c0c8052044031034100080f9441220146491000c0a448440041c5002444001c1c4408844041484801c200c410b101c4810b07001c002400c4024000c1c2c0c0c641d40107042c500144111401691040d60209481805004c0c403010740324652501442e610060751640a080002090792814130b070340b40004549501c052110f1004e0306d544400400f442d0800d42803415000c0d00e5052400b040c4243c00c02c0800130190048155281031140843e9540c0f50408030000c242000462500da09210900280c030b4900c8003641042c0840c1203024100140c4081e100c0140300765a13400540343c10564143c411003407011030400c1801c0036803190640c1c050341d4400403501c2c0400e148001c07c0302e010b00800d0390103174140b28941c01000015072100c0200010011420700d4182c9003c18803807000f040b4840ca8002501400f1310608000c0503004690160040140c1680e60030581d004106100040780319290009400a452400f00d045600800f001009000d030366141d580e4203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 912471321 1250 912470071 912470077
    0x1204030c0c0302040e0d08100305121c0518010f3b010204060f110a02182203091518050904020312120a05130c180608030f0a03111c02 59
    0x101c0e80ca01d4032032004001a2150b002d160340c02c0550301c0040034003c001d0000500700300c1c0000c1c0384400502d00000100702003800040c0300c48800c62201c000035943d500000c0c030701c540d511011a00e50105400d0400348000741031202c202881d00311021008012155518000400751010b000c0d6440444021500c004d0941075440300d10038103200849100e43c3d10303006000280d03080e600140d0010000c18491000c42501c9a04058510030007204100600600101940090340c0900c20140e4010200050380001c0c81ca040e1504101c21520218044424081e8035440c00400310300c0d40d406400d400190040c03021030700c0b81c0036411244069031001c0922007a01d0400013400b03a0810b00900980e030504c00c4050005ea580c1d280d500a1800084207030a420443c6410000343c1c003038600181001000080c00c2585401040c0d0100f80c0f02e00303656400e25182086621a14280050165500440103501000680004102c01900203280c1480c00381c0b07040c411006d02c0315144e00d02d0b000c0c0d05415000421070010082c1004126402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 912472571 1250 912471321 912471323
    0x31202070c0b1605160524040306050a061e2301020606061e070602040e0609190c022508120306031c140f0c070b090109060c14030705060703050a021204030c 69
    0x6011030440d482c1d01d880c2c5c03903c802410200401c42d00c80c00d044c050303800e00c0308031448410100f2000408004210543c4c0380c0502c110f12016103680c1d07560703010401845031900070030000c5c800811000c4942c40709070450007484103d0321072140c1c1001840c080c0c1e0900340140c6601c09240905030003409190780c4107000e1206a80c00000c00d0030507494054034400e03030204450040c000702c0f4010341c401a03c40f070a2100030000c0d44405440c01e0b02c184010401c12401410380204184031101181011a20406001050345805244d4204012020204c0100078034980c0052855040b54504000c4a0062151205540340c0f80300c00c0c0c0b40d00b038054004820703481119060840200204aa41c42e008898280fa4042d0103205d404c17581030703007050f45d80009a583c000700341000614050103240240c649440a507500190400540744215401d110016610b68180840c004559200740440416039581d00301500e8a00d03212401294603002107450500031481081d0340d40700b40c400aa07103950003040130b030311240c0b004d494403102200c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 912473821 1250 912472571 912472597
    0xf07140c01150b0c0f281a13050712050d0815030102070c030203010506010e010e040c170901061a090102030301061b1a09150907090504020102120c0a031202070c0b 72
    0xaa65400940c1c502d400080c840b050a140d161101d07640502c0c1011108086005aa40088001d5480b1002c2044a0f10a2080e2001c2d11800301c0c8145002d842c0d010310400208941c0c42540200b0520b03110032101e02110324409c0c025602400e8803103e510500703410b02c4002420030740c1300c80c80912003907015184c0c95404c0740c0d02c204405115902c160010742a03134002d2004a4469608100c10400c500302402482d8100809090840c00304c1c00200c00203001d010f044410310b00c180e44400c400340c0c030103020301c0300700b1115204b030540f281a518080c0c9801d400380500d8403a0303048481d104607604280c40784440548498500590145d4616440d00302c048560441d903050703d80d008194100507000103044c414180c1030980c0107112445c05450f0280c0d92504202d180c0a062007180b10701c90410040c0740d00840d10a00752040486c000236607464500040380313070606100310803080f258002041c0e0307030406000070302d4100584655540b00d402821030360448187c1c091a0001090b83c512403005000c2d1081000c00f07001c03c655040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 912475071 1250 912473821 912473831
    0x1c0c0507051f0e210f0c0717190f06020304021c050a060f090c051302130e04020a050111101d0d05090a123503070302120f07140c01 58
    0x240341c09040c00caa0440000c03003070900401aa10400d101d02507043c1c034143c140064410312130703505190341c5620f112205280301c0e00e4000901a4040d0180401d0b101814404c4084882c2152180c150660008900f415a4a03d00c24000d01c498003103801d6050b030b41c4003640028140c05850065031840041d400c0640202e0b880000340e0700c5490701c080d44119609005003d14001c0c00c034a05542051802c07580e21101340b00045003010020380c0426810004003040b2501518030464075588100030038020300911034100301d084220100011109402c0c907440c0d02960088448808096841005607600041c810542c038140e04200902682203403503600c805804402e1110001000c140c4038000c1c1e081030502492070003c948003168010103402c1200121025208075006c50a22245607116540e070664416410301a030001e00d00f0030b0410b0511aa044101c200c4c140d280561a4140484c0290203900300d40c1500403501288400262006681e190315400340c000c9441e0300405818141d8001e455601c003600001c82076403a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 912476321 1250 912475071 912475073
    0xb0a09030510091a0415020706020901030c08011424040f140f011409030a050313030303050618041202030c030a0504050405130809012304080106030210050715051e100f08031c0c0507 80
    0x11f000a0086030320421005076a0348560b400502111007800c0210204808240140b0140a02100c10605c011040b90140000341e912400c0f4480781000c13844451103424003150005800c190405c03400d080d04c3e2050b601c0030244800c0d40c00d00044d0740e03549188034005483c184004034004154070003440140c802a00f50303942c0169640f1050714580c0110821269120110000c00516038540b05141c0c000c003049403107603902c1c52001c80104a103000500003809008142100c80115402041102c03582456a0207482e292a175403140a406500244201402a0304180000e140500e0310718545000701e41c0300f50303910300f1311180000440300720031903c4840300c1e030303d000c10250301b50314062601800040074204000310303240e811881401400c160702d5419806002043c00b4010004403c02c61211a01385200c10010340b5a03212210603501079030340000ca0300320248800610400701d01411200c4180c900a902c20001c080c0c0c1c0705295540c1c0e100701550240e00c615094900c02a0511a81207010741d041d45d850f0450602c90030f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 912477571 1250 912476321 912476363
    0x501050c030c011d0d02010b06180a0f12140f0a170412051605010f090e19020a020f07060906050306041d101b030605091506040b0a09030510091a04 65
    0xa00f000760030000b00700c80301284c50031400c200b01c2421a004c0c1c4020301400454a01149250003146c1245908880d40c00e00076003181c940080340c000034607158682d04011075880b2300481d84100c0d00742c0700b5520520340001c3d40c400e2400019101c2803422020000305418443c94a0701c40888d00d030300c0100c4241550400c030000b592000701801e040700e28010800361522800c0c100e8a00359000381a4009414000d200244024241d048002c01040796034644a1012035074a1007404c07111051200c414120651012032440000380e80000c2441000040601b201c0c040b0b0b8840d20140c541030300c0c500c036850000e8002c000103051410241c20640d01044032182280880301d4217021907040103402542e6031340560741c1d500c412045200410800b8000d11082c103040001c80d003014023145140030f0082020784a0b0f489892542c81a0303c1d80350840740245002030525803542c0c1d400c031006040075401d00c800d680b40c0c40381d4040c0800940c2c541c4a400c50f5140c1c01401c01340f82b00d801c201e201c0b0b0848001442130b42e409148030248409028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 912478821 1250 912477571 912477581
    0x504050c040f02120906130b04051207120e0303030132040921051206040504170a1106090312011e0e01060e19051e03010603060e16090203100501050c030c01 69
    0xc12015031200c40c2c01140c42d07444d4000404590309540664148018080550010340348241c2041d0301c944148d49a04009242400310550300e000482d0004060b0207000c55103821070f80030b0549030741e8580301100f14820142e50340800c1c0525100c143c1c031030100d00000207080c0100d1004507000b0a42600b140002400030341140c0340c0e05c1058070710181ca10007246c20302801c0140c0c0c40b40148107041c8a82040d525041500c2c44000040c9154001c41e503600200702445144a00c1c1b06010038030030700d226074650880d44001d150740e80d20100c400040c07148401280c00343c1c40220980300e03000030240502507241e20781840d040c80c2e116000c148071040b44414402203a95445888600d01038503030307902c0d41e4900f5a451010300403411110005c6e000e82c480405402d014036512041001c2061040800652000380303108006070040c4125800204024500504154003200c041400c00102002d05131500d20a550750507410141d10044580c94460007404000f03104a40c003030b074060810081c46808482c00c1070304210029007107072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 912480071 1250 912478821 912478841
    0x3120f0603020319032a060b0102100f0204081515043314010e010906050306061b01090605070203130506131e050f0105040803090d061401031104061d04060504050c04 73
    0x8185250a04107040d000035a5003050614032420b941d02000c4404466130352008402c000301102d0b1100c0720f048c000e0380b081154a09810b06144100070111031174840d480254458400e071a05d5001d004c103000c50f91003900f40c0c40e91081c0760b07240c4c80b41c880c03c09141c2088004c0001c009205c0c203940c0e030841e0b01d54110300c0305c00392075003c0a101c2e20040001030030111902142c90454009604100800700b035000c0c01d91b404900d0404940240c00c11640343d4645c500020168001e0041c6180200b080c6581d50740e805030150080780c103007806054108411b8651040890701d91040703501c810180895240104401e091003002020700c0789811620705440394075900050100d002e003541a501c03040509100303000b9440c180d56400c02541007420710034685071030003109944034042c03400168880d1812200f50000d00030550081b84820440749032a1082e50384034500311080c010b08003a6103004502d090400318074081d0404060411002c0005196003990302c640d507800c042c0c240100121440c2c040c0b0200d207034482c0c90324001c080e021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 912481321 1250 912480071 912480103
    0x14040212040f0501050f07050a140405040e0616230901030b06030f1501050a02070e15061306090b07030806040e010e0d020703020909010c08130507030f1a060301060303120f06030203 80
    0x4503120f0300307240e030039604040c10454078241840705120444d0342150440d000583d0034145082c0c03100f100c0311100b81c0742c001c80d030220350080d007440658500310001041c8284503090503074030101d0142c1da02c2070466020141101c805004c0c0c0803454080401c54034030300035240d42c010514001c07602036841408510b494100350f032218034408034102030000101d5036081d0306031614428613050341800c400d24030080d56000107104240e680d031203c201040e03100c0f00c0d02001c03589142d8043c0c00195103400012800003035004510481000504842c00440c91071201411154090b4043d0350700d1000741c80e07040802c401011140c0201000d9940c0d040001c044540901c6460488001a005850418910300600000c1070b402049022180d26000b0469510781d0058001d0360010040301003000503041d580307409450a0341d250030280042c0d19174070030030b42041007849002800b0071044116403c641c41e8402414240c0f50140402004504440401400c0d00815485940000e003151800700b207555030fa402084c10a0103092000c0385c0d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 912482571 1250 912481321 912481343
    0x304050c1903060e0c0f1c121710060e06030718090209030f0a051b210105180a030e0f180c03070f1106010501120e10060509090111041404021204 64
    0x2c1c00158400c07403511005213005131074985c5010000405903801c49110b20310800a8016010808040702c1c1c09061050b0320845e2094003000c10000540541c041d40080c1c4641c0002100241c0450181c072243c0080340c250740c441c1300e03c6699150801a080d0401003c1008000300c55000c0b4510189490180700280310f40c0d81c0040e074680c0030805050900b450414004d60380d43c002006540011030004000c881c0203840110018052124400500703070030200500403882da0041c0d59000ca0003081036100600409681d504100400c265040301a02d03080c1c00c00c400b401043c02030522480d5410001c1e0210010354005005c1010340010150380b200c4d1540c03e803418648110040200b0800540010402c500c6c58118103100490307840341c1421a03518081400380a04002644403040300601c507a4004160070110728054440c1060140000001000c49104040c85110401c0200d41022410702c00c180007407203d1081c8520305801c16805030822a0844a0990802d41c00c024007441c0c040d6410555002d6481740b040069 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 912483821 1250 912482571 912482573
    0x5010306061202030a02040c020c0306180d26101502101103010305030a120212090c03011508031b070e0106080a0b040b0616240c12090201050703050304050c1903 71
    0x1201c00d9900080c0d8489819805100581d0380060707180d484950488002c240b1a124080807402d04040b043d07202d8052040f07000307110300202c80a081442c010b004c0411900c14013071001c021200c10425400d05207480310209444240e2210316400d495104000f5401c513103800d0360381e035440c05078014590300440043c2c01c605101d44015500d4054010500404081207085505548503a610380c41013906c00c8040c4404d00c0410f0951004580540340d5148000f01c20b0b0000d4500803038240e880c1e010744002c0e94841c2d46440c0000c4103100072104804240c2d0341210065041c01050b403041c05d5a10726640364189107114603000017480d8401c90800c40c1c0a041c00390786034401410051070310000c0d40c8084825a204505000514009480e02825959400b00104802000040c01d0030310185001c3c40300c0e14481d81031807485800020304010307003150102c05441e9891702d00390382d000b01e1844102d44100c14000d0010b5410842000403e1141014507000b9014106881800c481080040c244040d607618074250302c00803842c104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 912485071 1250 912483821 912483833
    0x905060102390a03080306130e030d1e150b070302120a090501020d0e010c240e16050102070b0904050c040807091505030604032304050d080c0105070215041707080d050103 75
    0x207000c00005883d82d00c0d5035401d540e038003441c4e070100400150150f64103075104911340304070360000201611005c00b0341e07584003a50740108c00501249040c6510401004d400b010320502d4502c103800118040001c40700f40d15041000003642644507000540031231041c40d040034031082c2000002c10400000d0785800c510107150a0029062448003150f40044c4481300d0340c014010b0b41c00000042c4950781c40120000d00c01c00c00d400c4032025081c9804101d2900f0715101759004c02c1000060003880b074409100c03419001c103035581d00491351a1828014814051010710440010742401c0d00404d400540c0710700390700d091544450720507140410f00d60010a81c0d1b0f48130f06103a0301e81c0b2040000500a440300b900682014070301600d02410441420040019100d0640e030030140d4040c022046d1005030100410441030490b0f181005443c0350070650b64030009520301004100a0ba000189020790318a903007181d000e0607074540e106c1c000f0002c101440c94000103010828080002c514800034026918020400161941503003010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 912486321 1250 912485071 912485173
    0x90608010b09010c061e09030e0a1d09010902150a120501060e0f010e040906050609010f060c110109170a050610060203090f030703020409050d0305070f090905060102 73
    0x60089210061044140c000c003110311444080c00c04e048040d8491802000800d00300c03130406000d02919841ea41070036100e400401350305010369100016028040104004907405105021601c20700200050300007454a8900d5031102d45000006600403081c1c01080b001b84190300050000c060009800300b840e42c105544040100707030208108042d40c101300c3d0191401ca01154150f109005c100c2d6190856840b8103101c00c186000a08107101460302450600c018080664103030b4410b8865000105000c03035411100300c01c8802d02d580f00c081c0c0340f210780c0300d00d000322000d88201030401980030804124203c06031545c1ca180e50100c801480b0360040c9050450805002404011214490000c200709280d030000655480c10750032209890729242610010740b500740c4c03941c4001d400600b0004010244000420156180c9849440502007995800400c07918440b0700b440d0300c1e0109104603401d01040e0203a03441154800018012102e900c0204152401c00404403680742c2c1d65084c0751100e000072500c1107c61 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 912487571 1250 912486321 912486329
    0x20d050306090609040609050318011d060412150513050f0d1e0509042a0503010b12040f0609061d03030c07110a1203230702180603030f12040309 64
    0x1203045007000d81c0011140c150240035180b0030400b0301c0100f81402820307408100c5103030307101c02107907910380c0c80c00c2c0d6040c0c44c0d0078111105404143c0c12903182c0d1098a00352452070383c005004008904d03040c00c1204041c18040c000030300303840c2130b004000070580b031400b10300c6180d01903000303180343e038541032260300e0300c030f0b00c0c025900783c1e8100a900f0080d5000082d50700440a40c800e1403480d611490020b0004c441103e03540110307114164882c1c1843c0c02030a03020060300d01354075400c165200b9502003944941c4240d40c00e110a22407411004010412900c0348680011807613049803041207210005005521000140c1e44040b07401e40b09242d031170302401901c1d820060b0905003c01c05501541c01e61901c9205800a40035007400901010040d0328400703200e17034800c4032b0b12004c0c020018441542c0354031401c000b0219803d040c50403c09407110174214404032a0030003a41c8101c0d500411000081150703140d9100015405041150588424405c1c07020b0f446125000c0d184d50084c0000301078880c68281002000c003412640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 912488821 1250 912487571 912487577
    0x90a060204032f090f1915081e190309120b0613060602060a0f06080307030306150309050a020d020301060b0d0209090a14040b040c0e01060806130c35040305030403020d 74
    0x440414943c4601420a82c03100307200c00c129038031781e44030030055074142480d0b0b0401015034a041c030307c554080e0700e2282079805d461800c000c8684650500502e800f1001e002050209681d208c0410886000741001d86280c1c980d00c64600740da0040d43d226600084490950021100710b41080704009141c1001c0c400c0e83c6407500c10399002d1013075030300d407000c0a92901030251540e48000d444200a003005015500240000c082e0503080302d50f40c10190500500800c002c2c020b2142034030401d0081c0c0c407024480d0056555613504480900144280c80c1e081005031403c600040b40c0654a03903c0000381201000c0180040941050b070250b500e43c9214104801c001008120303c420714600244190158020314006500a47c42100e81800342c80300c2c09c4c1070f0740e6031500d50b10203c800b01181d4004694540d00c414024001c0074151420f00c03440c242c1d085480d0039940c00c8a440d41c001800c0d006a1040c3c900c645890603410445950703a440c804204005089090f8400c88040e00480c0700003050004140c1e04100c80348400170280303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 912490071 1250 912488821 912488903
    0x31a06090f0603090703120f0f02010501051023030114040509060709120618060608210a1b0c2c04050303040f050f06040303051f03080a0305090a06020403 68
    0x220005a0641c844a28240114030100024144070402c0003c4d81c0a5600468014960020754400500f0b040c00e4505040c0014110350314005080c0c014029a8160f4000030242042801e13443d2003201d01c5022178824480b0003102c2202c1050f000c0b500700055001c3e00044c190081084404000e2105451000e00302480c203a004008101501b6400800c0500740c44a001c41c2041068150402101511803038607075241503c4841c030904200040d991280e8111207001c41515804050030380854a084a1004003200140c01080381b64001c6200e61407407003003440211100748a4440b07035242c030740003103129400506100d0f0058980200402c44245440c0101d030340691111207600d0a680c56035101d0001601c0201031108051180080040901140200b002000112075540c0b8150800901806c0150703242002c0c260040f501e060007008410102d011391750021400703231801c040360070110010000144415814040c502800c00010040d00081c0f00642c001c4915507140299031381006070390991038081c40c10000d000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 912491321 1250 912490071 912490087
    0xd090f0b1f060e10050c03041a04090b0103020a020d030e241005150706200c21070302061f0509250302120a050601050d020d09060b190b0307020715031a06 68
    0x39200e0b00407120b60600c0c0480c1c07203c0040384043d240d8000d5401660700e0500903084c2700c0145050b18050320032164403030301c1801414500401541288031390b03050100103810000340350180c240250045801c0c610042d0031103c5404114120b0301044c0c40210780c10380d00c54200800e012201e1004102c40c3d0141c1310449a4000ca5030085001c417125102ea04c200900791601c030310316581100c0e641c40d40306621100e10040075580315a943c09854440265281c922034602c640a0f85140c00c203c090103031221654550018562912041c48040b040c625054000c08900000c50380400c943d116002198010805440c40c3c80d551540013807044100041c2b1140342c400c0600c1401119011382e1000d2850750445030000000449850b03001c0102c030305110703819a00c00c2c075a00006100342c00b00400d50003d001603001d4182009100500740800040b0902900d4229006c01c0b5102d00f80045208080110b410010340d0040780c000540c2d0b1300e450b0035a41c4007107205801280d510b04401a84624400c1d0174145010b040310020b140400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 912492571 1250 912491321 912491329
    0x8190e011b080c2b1107330b04020c01151d1603020d06080313050405010e0405030a080910061401021903051902210a0908030a050d090f0b1f060e 64
    0x348091081508018000c5004d2003140d0710807200030300141c10401d000381244189441200da0103440b0403038a0400111444981c45103401d07160f140450032210100010300c0600004024000a154099016908101a0004007400d01c1000303600b5000003080c2c50700c83e1a100352a042030301c2140310a19060a00300401c001000300102640740c94070741c0d080060b11a1000d45843d0010300c06908000b0132407200041e034001c1b81c0d110861301c2d01241c000f1242440103a07291109000010016200244158400d00064003810f00a03d1a13684c412041003c90b5a1250001000815958154450003076a602c201005641c3e5a06005201e0948401c0120f0140d0b5095683c000f003c51003a003d80a010403410021310607403920a00c41c4450a801403081c52516102140380101641d101d043c0140201d640400d001034502804415102c500c103140d12050700300980303200c0b54401b0f01042c4204842c0d00c40202c0c10400050041c001c214028451002070041d01d0320307a034280c6a942501604030905010715410fa144441d65 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 912493821 1250 912492571 912492577
    0x3309060f0302251b0b1911030d02030f04060507080603071401020f0f06090f0d080114060d02160b06060702090613020c0d120b0405090c0108190e011b080c 68
    0x1105240c01690750043c400d161211400707101e0001c0503504000c0d020010300803007428a0242070488440e000d41540e5644001c48288584000c0c00d113400000100c4018060041c401c0d204a40304e00420b41e46000c0c801081502240e10031101221654046000e20040c0310813807140b1940718043d420980c9032030409000003542d8081c3c1d40b20b9005242400c0d030300003000fa4070a101e410516140c0302c0c11182800d042981b500d44800080f180880030303200d1a06403c60080c00060354100100c01510741100a03428042500c0b41c4600711020356030815020800d2071522070045c130040061091031400c0048003e0f49103080414a6405400140701d01c10511203000981e8a02c452250000001c0302c0302444c80c141041040080d019003400c5075014000c05c2030b03a041c415007000710000c000d00380c010304000484007181000201c510554001d13849074051501c8103025400f0711a0300d40c00a940303000c0700040000012801c802d90b00b1400202c7c074035035140c2403e101210060890049410050704110510745459455420707940 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 912495071 1250 912493821 912493847
    0x61b0306090601230325050a03200711010e010e030309040906090506042303030c0301090c0e040510090e07210c080a08030402090a062409330906 64
    0x501c0040208195038040d210240e101d10102100c48440c503c2d414000350282c000300c404e42c0e442c98000c85284c80211103000c011a101089860f428200700002000300c0003409a10700000085120251310511407140c2406442c250744a40b460300610704415000511074040c40128a0500c001007880e038055a80100c00e4a1070554240d0300082c0c0c400303d80c14007201070315131401c0142881c0121300610044c01281420440c85404c03184804488440f00c030000faa0b00c1c030007220342071001d81091005100c03030815074110004d5245a4506000c500d1541000181103a0301a1060b02e40d00c0c035070b44410410b24601d0300403228289401c0c00585403031464004658909409010048120488160f08404204030108004c010b411804111040c030241490544000d5001b960164421611200040d08000e40340c0100c10aa4038414810340100d842620302c017200020800c140c1c0280400e05c140410b415800951807400c28086d114481d000d1034040d100c0e554070002d01030880040100c1c1c110b05000e02504110145051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 912496321 1250 912495071 912495079
    0x7121a011a0705100608010c0f0f200c040c050306030111090603072006040c061b170a030f1406040c0c1208100b030403020c01030507020f06060d110d060e061b0306 72
    0x7040c00b8940f59013440840ca4446412500c2d0040c0031800c02415801000304100c5030703c6441030340100c05002d480810305031800500040007040113007030952060308400f0842907903200b01e03054219007500180070344080321003c800050002c803c0214529090054900c080f9040848515007045040840c0e80c07071200500741000e0118402202880b01c070008804802c0040c401d09651140c106494182d0700552039100c2c0c100007800025400c180b480d010500704403569071045890860209001aa1900390801007412041c19518000507105003000d0262801440300c50303501d02590300e04082000704403044684000308025007004c940c00091040c00c0081405a81802c00c042c00d0b94403070b007241101c00382a4108031101c03030000c010322003011f4002804601406098905021a6486000480e6184245000000558880e001089880c10f04450300e060325405040003c3d040240240030418a215528046036620b84d82c081b40b0030122800d00c115a00100114241000d18a84803007040403408040d0205100b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 912497571 1250 912496321 912496327
    0xd0c050615010903120306150e1008060609060a0c05061e0f090a020406120c140d020f03010e0d05070501060b0310050f01020c030115080c0603010b16060e07121a011a 73
    0x607a070b004420b00c0c3c1c01141e21064440145402c0100180900518850072010241c0c0304110b014080c051040413141c000060301c5056813104049003140d0440003c0c140c035821030000c011340001c946900004054901c441d440d08082208145070070717407038101300529611607010007694012a125241c0080c58000303e400c03100302d140303440d503010050401c00307c1a802980207280c9400040e00204142003040c910340100a40d8100135035a441040c1e0000d1640b08032680b210720315000170014a001c040c51018500c01800000f64510003038812460101280c0c41c40c00480d801041c94810407109000d51005040310300c1d41c042c00c6003405c1c0301c0e0180703500143c0501b034880c401c12021004c199200b00f142c40c0800703e005000707010f000b03d00031030304d40c081e24980200413550098140710501070515000b2203040364440400d0703510b0319a0ac3c4040c20200c60751210101e50303003070700c1d940321010349903080207184082e04060710181d220b482d0f54036040c00c500c5540011070424110317000041141c00708006801040c0b01d280c05809907 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 912498821 1250 912497571 912497611
    0x2150a140f0417070503010218011d03120d09060c02211306080406150e0711030304110904050f070b0316020a020d02130f1b09060207120f030309021c050d0c0506 71
    0x400d01415070170040e01984007040c40641044103409a8041100c2170301c0e0340c1051034005200d00502c0d48000000c03500f580c4901c154442d42d8120740c00600040d400030900147c0038029681d01c00c2030700c4007242d0000050b4041d10018400d61144881000112a121442c0c0d1a0075514010b00070b8001c1c9134480c12052000403400039052003080d400a01d08030588400040c6c10035100d00000d028214152803090000d1400e107404403c0c0c00d400011a4049c64000e00948224403002e420058003140051044031140610600e02050b5a4100901c44c05403030030045c42501c0c2c1c540700d031401c01c00100344c8400e0f008543c0250000409600ea040c480d081079034054881003c0302c80840c020300c1c00740503515403040b0300d81d1500002c0c0300b03042038040c0705011a00560f5156000d8581d0390350100c0c1d50325294029115582c01000c82640061044151800c41520070b00b40810880b115400045401c0200c20b0f40c2c100d1048400111000c008043c8000c0c010113445080998800350350751030f00340c1ea4035001011181d1a00c0c010521003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 912500071 1250 912498821 912498823
    0xf0103150e0d090e09070e0a020c0a1505010524031b090a0f030204060902091e040f0204090203180f1002090d0804121203020a141602150a140f0417 65
    0x48401c00700c0225000180002d1006000101074400c4038904400040030a41818000c030b80380c42140c07034480642003079032a4100c40d0402984040c45031036013486214105400104820700034140701c81e40c0310300015291700d004240541c440051980100401c042e6401c0c400070700482c030580b030700180c179901c003084d4030080c1c001a0f0206110b40840158400b0312604001124000c003603501c01a02d1080e501444030a03914582036051b030042549a80e44110803405a0b400e0307006081d200c00c0340301801400420004907584020b0b003260710640081c03540b5900001001800707900c0f05d0355030203502d4041d001807130445801d05050703890f04079000e40b24580d10b80001e101c00072550f907510545c1c0c510350040751680d42e4a648600001480210b500d0071105620744141e2404600e0003407090303908443c1c035070711000740c20300f40381c002c01406070700100d183d01d0510b078414048805601c070000f8040081d8003182c42c40d541d41c00344100107000880b606102c0c020301d01e800c01c6099007200c0302c5820754007158040015482d441c45d4200b81c40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 912501321 1250 912500071 912500081
    0x91023211009082b020d09110a051c0804150f031a0319050718090c15050403023d0314150f01020304090c091716140d050f0102130e0f010315 62
    0xc44e0b500b60000c0340409080055a03c0040c11900c1840c8416604600e241813041d800c415100c2c055024903014504c181c07160301200c030242c15901c01d4044920342074403145075406c90001966800009401400e1141c0e2036501445461818409000a01300348080d81c80000c3d555460b40c211703d41600c415050850800008204542c06003ca01c822a0740912505005200418a0802c161420446840000383c5d5005444040062000a90b911880c1506607000c0c0216122421200c0c1d40b4500741303819130060390032603291421390414048090911000c0c0014002c065030202c25150382e503406a0000e00043c00c0d1002c040c05801c1c00269110100d010b0a100140e046010f2030340701e01a03250414103000c84550303000039001c0655000603034800110b56040c50481c2e5507809401d0140407244610814003070f204003c17022504500c0300034408074181c48a40e403003d06001c503012914003180e401007458100c40ba0741503000d1000d01a008910452072605440d0700045a40620004d4490040d1640400300c090880d004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 912502571 1250 912501321 912501397
    0x170d140705030403151506050412231501090c02031603030605091f0e0405150411211b150702010207050a08061509102321100908 57
    0x1030703e031225640c0c20250f044203104a950046185494408a6a140340c01504810b03a29165209401c01c1d042104284100d04591025030300244c114901502510266928684c0d0100c80c0e000b4084501241c1c0c42a0380303452040e0000d01c0c02c80d0506a00700001c0c0d40c00001d440d9000c8803407112200706a8903041c05e1b001443e03160022900031203900100310b9800c1030b4a4000d401e0030003030720100c0b100680d5600e2a580c004002d84004006070802844419240400c4071000e4000303003d40d08035841280100c000410080001030807102246004550b441e04880c1445141c0c001030444980c4c52038210607100007807031107608068014024601041600569200b04500b00140c00081c0a003c496911007840c0c1c0e84d21501241c80003c0c06c5030104889a460030840301043c000c03100c01130f02c03a5000b4101012044080c4c03202c0d016452104881540420907078400980d8098103000f00d16009482502d0301c51035080c01003101c0c4507140c850510088030000b41119003200c441d1742402c052180c0684c840102400080c850300300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 912503821 1250 912502571 912502573
    0x30b0a020f19021239120403051002040e011205010609061707080a0809061b0604141c08060f0301140a240510030e011d1c0c08030a0c0203120709030b01170d140705 72
    0x40411000c11070b11b401402a01d01520032613842c030115144402c164440d5010320501e194540c40108844000c0000300e9440318071640001c0340d881d49034104601128295072014030152640c40e880307055584241b02030030182c105500906500c00300c5440303d401038402c03400d24a0003180b0024000d202051348446400e03202101c441590301604043c01c18280001c01d4070220306a9004810245200440c001401008104030762541d105556406040282d002850342109070595281d0f401d01000905005515100c2d0904180001e004c2642d068090720f800f28501184080c851210001d219a6484c0128246402c00754030b004600245040c01d420b015003031340800c1480418901103481e2192a0100d40d0125254a481e0802c4050078000c004440c0d1400c41e843c0506145410800718000e9419500111000c44072130041b00d04c2c01407048081040840210303213200c0001c00e603010900c20044511001401007600c0250ba05003810840d00742ca40340c0c0c03005084203050280040c00f468500304140281c1d52170720b030420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 912505071 1250 912503821 912503833
    0x2e0f05040f0e0412110c1c05030f04140303030f1f030b04060c0f03110409090c170a02030606040209090f04032304170a0309030b0a020f19021239 64
    0x400b40382d10400c400c1d1412500c04d4540b200c190b407142e02c03e000540244200314021310388004408140143e0084054104012200c554011004940204001d00603941c284a060b60380d81e10346143d1218480007034482d103120350002c10512900c0c4a085114540000d01000703c1d1800c05001e4501c0d000740280c0307a00080000c3c446c10104407e001c3c0c0755002006100313160701c8000e0000e1214038200d045808102038030b0307030b4000309000510040c162607020407040c501c1640021285511804019454582040c80c10451342c400c82859045080921040e6000315040e501541081c5a10f80000c50740c482c010a0900b9a4450340002814944100f0f080b007400703107002540e130300040c951601004107030b44039008990b994550820b10035212a000950824129055566800d500d415079407400d200c40005404400c21316024085090000e400d0401070000003442c4c04c0c3e0000b0406480c902a05140d805960114100014842071100c403260300f00c01e54107566803521010585041d6110040b5003d44440030381c4241c440c1e8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 912506321 1250 912505071 912505079
    0x30b06190308130609051305040606081c09060503060a0e0a0f020a020c04051812160614070e0d05060c0a11060709030507090623120f06062e0f05040f 66
    0x340b00501c011040b601110040545034041911101094030560760003441000c0c0304030035a500d5510450300903104440100310266075003c2180342a404d218840784c000c01c402001c1010030740009680004050b14102141140f030084006640b100162007903034030810f01e400c0010803140e41035004038090340d0001c0046444840740e04000b5901c112101203180918948801b02e03c10510b283d0794001c4e20f90038540200005001c000d00302e2003540000c2d50306590840d0400c19400044c0a5004210082e034440c1500010b03407070607001c000c16070380d24040214014425484824045140070601b503902c0980d0030303610ba43d03528240c602114055900f0340100300c240103d00501c0103595104400c64203d80c060422079680c41e4460750481b0490b41144107440d4030a896409032486210711052489010030010804180c02c82401c15090030120011031140c0c1a800407000c204843c5070400c01068207800925504c000d4a2a040b201102c044884143d0014420f43c4501a240d962080d03080741d02421010003407881c41a07803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 912507571 1250 912506321 912506333
    0x1a10030b120307050a02010c140703030c0303050109090f06020c1e0a02040605060f04061b050604031110060608011202061b0c030d050a020a02090a1d1b010216030b061903 75
    0x40a2916100c1e0795401d0400040560001c141d0356880d8000300508046032150f030055402c1008410100c4454044a04c10002144e042c08030000850207074890346a2400203203001403c0310030507003040503018039280c0b040700419036814000d1a456030001005942c0c140700144207280c103200f240741010510040514403c031840c0400e00d500d04a01c00d4030203005c916190020030038103000c0c07c06010707040c810602080200f0b911031115040c41888040040d24001c085840b89420110101c4d010b50200e81d0310035002d401e10b601007000c1010000c0c0000d042001a0810314003c0c0084070611603540311007a074804040070b540d5000c0445c4c0c9142c4e204403650760000411000d07a03455080024040744039000d82c0c1c00030101c1c103001e42c0448020700102e038090040f11400d6402c203c01d48001074440d03801250343d4899030000f180004075040f04242c0030402050101d041c4503040385410042c1e0f45160442d00408252901303440a0a031002c2641d9100c0d035812155501c3c0b1012440220020b501103a003039150440010501c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 912508821 1250 912507571 912507581
    0x81801060f030606090b011b0f17070512040513050901022101060905090c0d02030403031b021e030c30040603050106120921020c151b070b0403061a1003 67
    0x200c036110a0000d075680f5240e5808858a1b03003011800314481c011700015048040755061203d501c00c090b0308140d0441600e50103900245c0d500f00d041c42c14000078045090001c2002144040c001002c1d559240600380400320703a2807003040000b004015146d8000c00c1c80600c0c20740580301b074180399070000d1044403c040407810003040c0c02c0c130070040412003800007c075050801c010309a110310f1a070301d0014a0042409005030003075000400540403d544c6a02c04d1124002c1d2840a00407060140c3c01000d00952580e40c0709500301884046c0106944100483c0856000c00300c0d11040c404002d50000d440890480d080703001000103040004000c0c2d0001501007041034042d0b0007941030b0b0b0055600c4200c916000e03007010382110300075800903011040903c03211100c0742c0b0084078061140d00f00e105840c0032444400106240030b0250814030248140446d082c03845840b071a000d025480d4600c0018041280740901c00755045c8207074080a0009c44d1260074002841100e0a0441060380010302100c0700b2503c084030049c001c007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 912510071 1250 912508821 912508823
    0x120e10020406170907030308090109020a0905061c2a0905010b03010608090f0a08031e09010207020f091005090714120106030f020a0909051312020d03061d0601081801060f03 76
    0x28030643c010395800500855800c0c0700c2c0c03026038014000d40381143c4003a5110080100140c15940d01c54035140010f84500d12401c1c0141101d90000c0b496050000811070f4002d81e0554000341000503400354004242d00c8030070807100c1c01e041714007040c0d030280c011790303020341c1c15610f401c60560070341000d0000684d4100325008504a9450307954400741034480b5180213456001068841c40c003a40600c000031b003c20030f000011500880783d40700442d0040940142a582c11108039075400103658003064100540c01c003400070520248040781c680d20240f5080341519130900c064040c0d140950720100008200501402071640100051807496449022280c0280d41c131201c2400f5031f00c0001c0c2000680712110300c2500903207074060780340c0d103404040c01d04010400c2c000b010020b11407500e12405000c0440800e41c0f50b40c10a081c2081a8054501c2e13807920000542620050b512851102c8811640350101e24100d0b4542c0780c0000003441d2045041d260107a420004180341c1d4001c0076994038041d4001001503c01040b48116 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 912511321 1250 912510071 912510077
    0x703050901140304120e121f0507091a03090c0405130201092411030405060c15130f020f03070302040509074520090909071401120e10020406 62
    0x1800b008686409000c2500c00801c6952055001c00307202d40190740440300a9070203410005210301c0c2110040c544036a00e01030743c0c254444c010000b40140d05d0783c041c2943c49509410941055450704081d101040e82035a002c929100c004004030310302c0c0c0020f101c030115050000b0300901003800e1041100e60401303018001240481c101001c000303418086002da0124003101a40103848403e100403059807003589607442c00e081c3e404108000302d5950303990000f4040e05040c042c000d1000c03c0d110701502602a07409841c0440d13500700a03103140006102080702d141c2c1c840d810b07200300344d20740a601c01203807602c1e045400003544103003450b040040031301000410748211100c4985017107649c80c01d854200d00601c828001214060b06422980b44981d004d448400510094401c0c0014945a20341d000d031004090030207454070340350000445c0c0348980381a642043d00a4030b200080c01c2e800d86849000c0c2e082c040c1c1d4070300160522042c88403074088840b9aa001c00c1c40001c2044c10384220f0a80e0140600003544140501804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 912512571 1250 912511321 912511337
    0x30609110310110a1803210908010608120a03152304050621030d02030f07030c020f28060e16150207090213050d030c050d02010207030909020711060703050901 70
    0x30419207000d0903e00806043c00c2c0e6140c400101d40c2150340d2078100c040b80e9075510403200c000000480b030010029440c0d02011010025074101e01d4000e00800305a40000c800d1303810304900780304000c808107042030703281001703c2c10740c0da030700708440058024144000c1d0300c0c0b80d544000304001500c00071030242c2c0400c02141344010b43c00103071920b04200460b1003e40c1d502d030f0032040c40d144818540e202c041c044003030a41a00116410401d0310400c01c82a0b900c211a1024042144824822155010300036107203e0b99050010300140c40a0380e030700300e0350f0301045e0001c15118111443c0c81d04000d218000d80c0c441030790b041002030020407142c03409680e031041141c042148500d01d081c07001456140d60b040700c40c00b01060741d01510f802894207040300040c1d0400c0c18186900c188a080000305a40d49260006c2d0062294075120074601a82c188542060a20851001035900401c901d400107944012080143c500d60b44006840da189400d02e00d05616904000503040f000009848040c1600a0701402003900240c0e45c1c41c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 912513821 1250 912512571 912512593
    0x11010c17091f0c060c03060e0a050a021204210c0302030a0f0504080a0f0b0610140a090f06021507020c01020304030807050c0306012303031206060307032007060e010e190c0306091103 80
    0x400c40d00203200380c2c000074a2300d001090360912a034019680142030301c01c0150824090b034020104032201568202e420040a00d1480002d0b070800380820042517060a03c01e0b025061518042e480b031141050703031410408050b0f08100d4081c010030a43e40985003040172548100d00c40e20308002c42d545011816201c1d20b04c2c02002841510344030b000e6840340199a074600188142c40345001c41c894118100b884103100c1240b20120304c400404081000804a950040108182c40b2707035401301d48040030300188110341181d2803030380443c1d0300041100c04881e40310426079940c1d80c407400c00700d040c104072458440e8180500c400000e00740c42e15519842050078489245030704040c20360b00300365980c4a4030360100d0580b12680d0000d0300b945069006540d2044803030801084071030039003000403100c0e41100c41c1d1842e240700c0071540320b090102c98840c184035092190000c004191243e50480c0d03580305070070318a100150044901000308681e642c10600207541c00841071000511910341207400c20b0503c21168081d10815075070032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 912515071 1250 912513821 912513827
    0x60210020f0a120f0c051b0d0f0f030608030d02030702070b0324040b0d1209051509120f19060b01020d1e0509030a0f11010c17091f0c060c 61
    0x1d00d405a001e240c5881c1400c0000309680d095044030255600c1c568450b5442400040d034010f11564281c195249941d80d40d040c45491466104011141c1203648040300d61b845241c1c20220700d032620704103400c00000101c9103010440103070005030041c201c030740001301d044e1305d9904d0035801440c01060f49400356503086d81c071f5100391306150000704c0e040c00a02640d00e11002d2b00d881d030340700b280e42000000781c400b08003c140d000110796010090001100c5400860070b004403820760180e901c6010b810201ca000e2048562180240480d000310b00000c0d00c5280f1150120350100720400c80d514007950106c0c01d0780c0b0724107803c0c039414161300003409064505070704100500d4220b40c8041070103811031115880b4030841c2d1403404150010081d03d024100c05102040159102c55603040059001043c0704030300f1210001158034101506503242040030303051021010b01c0500044000300c0030024034240e40107080e1940001d40004940005600501d00c41150401180c40100e03848032841c0714183c014601803004142c186011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 912516321 1250 912515071 912515077
    0xc0115150215010b03070302160b01050103291002190b06130204050603041115040e0108011a03100f11070f0506061905190b03090304063018050303010f06021002 71
    0xa080c8449007100500104c0b40100142d0342040643ca00141070000e0308004c194020b80202d07003900c041c04642c0c0100b08961381805100010400c070348060130296429000321a8454151061502c182544d044008007207208000c40601ca0355000b0004040500e00c2c00e01400d0b0b0034050b036000380030710384550a41e2040c0c240c3d402214201c81001e417000f40f4540e115110341e1041d0680441d030552007103540450301050007103c8080d00103080a1114035102c0e52404140303a00310341101c40804a145925001c04055560100d000392120865040202c0c01c1101ca2240d90700510310b00201c12603815003c500542803101c404580d0800d503100d0000c9501d01d4403101d0800000020800c07841080760840c58051141d0f0811040340ea501c4406044038540c01602c0b80c25404d0a50022120308c0d1403a40041010010301e544020102c8092071291840b00d0740480403a2186d203580041603243d6061a10350841b10440101c03c285449038070340202c141c0780c5130750716841180c1001060f40708078030051060280c1d00101e03848034421 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 912517571 1250 912516321 912516343
    0x110a200d140613120c1505010807050f0a03080708030c04150f120b0918011806020c06010b041a030405100507020c100e06031f03050f06101d010902030c0c01151502 72
    0x500e601522440740201d42e010b0b4800012a258414102c000c8170003240342c007c00f8060010400a40041e034100700501100841401890381320f003615030f40800104d135203602100c003484e400c000d100f9660f54610404200501c160751040032200b0b09080c2800700b6131703072080b0090000400c0d0756a0042c1910544105000c2d54100c402c001c0e88100d4810120b071b00340004036142d0035401e184e903001160a060846824128042c0054250340351500061124840300c1c080c801a4050300d07507440302c039040c181440d114048900c4543d0036040481700010214040c000304019a0070003165500301444280b03030004009440d07040c914101c0313014000c1e95114061060192040483c0c1240c00707424181156174041600400e04800301c031280368101c1c03081c1c010011800500032219001e6000000780038900b07101001c0e1002400d180c0c02880250f40360020124900d0070503100e541141c50300c120158886d2901130201c40e0f28492000c001c00290700e054109848109400c8603201103480d05400310043c14656039017680c441003001c0c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 912518821 1250 912517571 912517583
    0x70b0c03190209030f070305060105010807020303090d180e250f020a02100e151206010801081e120d0914060415090503040504060602010f0c110a200d140613 69
    0x15074886182160b42c060141c83c1002000c03151a141401d0440382040c1064000307075095003000c401441956004803d5a401019a100451440c50501c252503203c03c0140c00403800c1040e078420980d081c01e40c00f21941d000d45101e01525581c0d0a2100f502c802804090704e462800051003050044511b00512044440d040d4580141c1501501642000485c42200d09400203001013181c5114080d00c0f070240c0c0a44100020500540c0c1d0304940c04030864070720004207024100308130b94006202c0e0076008a840001000300807a0380f004401e052404a040c116101e80e042d100780e10104010804000300d0f0044080035003d41000703890074035a40030b110740310700b801c84c3c001e0904404440c0601081c40c1e158031000e6414041d009490030301d91200c0c0001c00350f80c01c650000d80140c1d19881f40804200c102e105070300c07000c802d60030116440d407403000350340d5201d8250304000303030030a4006800c485101d80403101c1d020000200900f201c102290b1480c049000481280d1407061358841c80c40040c0118010400007001990040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 912520071 1250 912518821 912518851
    0x80c2103010819020d06020406080712150b0307110d0c0c150c0215090612040204231b0409020d02070b0106030e0a0611281211090f03160308070b0c03 66
    0x542e8040c124910703c0c03040360844c22001449010402500c05000a40707115950b401c080c2c1400600144641e4031b81880c80601d51612201c0b190135000140807100b10307020600300544a81e242101a21213401e4600d080400d0300400554038222540200f03440401449810180295a116040044c00314403243c1901c01050210210300094035101c03000702005a1031610462400ca4a1004920590024000440d130203412205000c2107140600a031007084800c1e0340649a240303261006040c2c80c4030060700c0303841a200b20641d81d074440d0001e403084a01821440809565503841c4101040007035100c0c00e81035505022080000c64505d100e80148100500900010200d66039107456030001081c4040140c0c0112004020500c07103007079520700c1155403c0d03c0740710903003440c2c00201c00a03001c02082c1c82d080d0740c020301d840c0b811161009080145c5801100070f0b200c14586081c2000800e10b015850008601702e8072000b9000030070040b859000b40070592040c03403100c81c00c0d2603400c400000c178001a03e034211280c40136 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 912521321 1250 912520071 912520093
    0x70f080708061317130f1802030412030e0a020d050604030212160303051e0a0606110c09012102061201090f1107260a021c020304080a0b13080c21030108 67
    0x4d41031207401203e03034031645440c0c806820551100540c3c103034030000b10844243c03420400c0c1c0522507a00101038074008002c3d80795103025903540940341ca1803040d407403d156442d8003c0008040400101802d40e03400b40030f0340304000c91401c11715959082200c0440042c403480040c10800f00804080d611803070240303503003c41c0421990350290007500c0018552114160441d5000c02c0583c041d1000c80e0080e07c0135600080d40b2400d250005028200d80d00440c40e180d4000082c10502e501c0c0d00409038111a4030300700342e100c69101500c01202d01c12604078042d500030f03404918005812000640281202c2000c0e0007008a580c03902c0c841c400740d440f01101d80d03270602c205020b40302c08540b2407003100030720480d14010304185c1d410f040880d00064100b402850010390100c1d003808140409101e00800c080c030a40001c509040c0b42101059640c1c20140380209801c0100c00070803103a070301c60710ba5201e07025400380c4040e4031140030b0348603107548420b141c0304000124800c401e118034008184040f203069900c00005800c1a02078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 912522571 1250 912521321 912521333
    0x305070519120c0809090103081308031309050402040b030f0706170f0a1802030313030309050a1401051b0601060806100c0b0a1817031b0f0a0807030b03070f0807080613 74
    0x90b444084d039004004001030a0980d543c4d003c0d66002c0d51140c1070032520384958500101c03907601c6d2500b10701041c2e4070401000510228500701c4008444c00410b004c5015503ea10209000d0010001d0b8141c143c402c1103207000c009040801c07030806503181c6075100310b0b01b440c560740c0a50550744107a5124851340d001c00086600c42141d40c100c802401001410792801c4401079010a00c4d69100680359100154002800c2c0200340c0e00c50041da00030801100c17103d80d90303804c1500c0c2da04030000580a450610100040c05121000048065021036031504242c44840d13a41c0c1c50060401941101d110344242c20300700443e000702d4003860054126603000043c9128903594590004010b01300055405c06075107040202d80c00064040c0b068601045406524070703164280803034840030103040d01c48641c0c11800103109103514a4070328802d654175040700e03191000d5181c80d003c0d0194000c1081243e540d805002e4500d010030300d40c0d0440c10001c225a50b910444486581d02d5079000c0e1181ea0a032000e520388000800d2207804151 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 912523821 1250 912522571 912522587
    0xc140703020f2a06040f12170c030405010f030c0906030c0e03010e030a020d11100507030207060f09110d05060c220e0406150b07060f0216030507051912 67
    0x442801150b03082402d148403645002d81d20407100141c2804502680040310b080011480120801e07114281014100420300e00c0194150003010f13042c5106a02a60512030318514901105c0c0c40340300742c01c0d80d4403042c10b46a52a075029004841c081b805901804003c14840d2280c40311407461940c500c0055410305a080f0f010340b0740c1800c500104480100050317103c0d5020b100b507541c010380c0c800007150354808108001e410800a8044d903010300590b0011145054004100800d150300c810f000050f40b9603031160150024000c00b00041c1405151405034809030500707507c001070280c000d1102144140d0314404201020740c07214001041a0046c1021401c1e41e50f006c0c000e4140d48001d0b91034103038900c0c00c990003078648001a91000d0b0b0340403103500901003801120b100b001110281601505201818001420801d105403540200001d070703500c0c203409003510349030b043e100700c0001003d000d901c5d009182401080c64029080540b000d007d54041340d803640700034129034035800d580803400c541040d000b0601922610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 912525071 1250 912523821 912523823
    0x1e0c0619230714010f0f020c0f0601060503160207030c14010315050a0b031e04120e0a030b07080603070b0c0a020108220f05010906060f150306050f21070902031602010c1407 76
    0x264998440000d050b92a0043c0798a0310083e1b5001030300d0310a80c103038072031410001061100c2141c01040061100e55480802c0301d500140400100100f080d19010403464891151b00107851411340c1c1d000421640d201c1c1c00c858400c51400d98003400741100088080c90009210300c100b5500000c070000400c90005a40080c40c0e01c208202000702c410954510307000b03491003080f00e04030361902500300c0d00c175002d0ba0005031420300e6002c02d03566051b07100d040d80d07100c08031b50001070b00a40904c0741c85000a642030760f081110b203015001c42c207040c948034207911552a5641e0031071f820881c0861740e82c8000070601b070100703050300d207099140e00c801d03440002060b00c42c5c03007607455113010990306552200300e2100841d000380241c800030814540d2099109203070101c240311021203968810101410308008001c6503035980002c010020086030742022115064690400025a4202c016024050701e1000101269030398043c5114803100b902080d030032641460301b00e007264070f44501100850460031405032450030020141840d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 912526321 1250 912525071 912525073
    0x1d010f060c0512220905040506061e15090a080c0310090f050303100510020a11090a150e061011030a120b06030a05100807081e0c0619230714 62
    0x182207001001503406180b004c981d43c584442065000e2007180d0080000b858500e01c00c00c00350420b40e076a203032156005804503110f15150010f0326480c828000ca60005060007c0010300389014482e010740c5c05130408180c1c2c92203003500c4280003800c01c101003003480005600a020701200448400c9490080c1a01e40e400e407010b0718500c00c40000500c0c01c1000354050780c072012007100c45502e00810025030b1005080b9900841d00103184900c0000d4202e03171400b511080886101c1340d03543d6510040401000c84a0050364000c243d00320004801480d4424107000382c801740c030a01040b0300c00c001c0644111001054450159004210f4100c62601c0307030f002c8210034a400080441e11860110014003a0303041a149107011603950024490a48880b00081d802001010050502c0510f8280c81a0700c920119070000b15040f4007504540740a1010711201c942190000d000c5612a003401c41260a0f20308001c00050110381c07c400b110740100c400028100b15480103545c2e05d49070010540d52a0900c0e02400c01c40341705 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 912527571 1250 912526321 912526333
    0x90204060b2a1c0306150e061801140a030b030601090203010803030115050d0e06070e030d091a0c0a03020307170316050c010b04111c0504020306061908030307091d010f060c05 77
    0x4002e800a0b07200d0390040f001e0340c002c502282451075180166402201040922454882415694880c00c0c2600d807141102c1d030000c8540c507600001030321201d030702c1d004031680440005820781010750142e21010254009130103e4242e80e0301c501e03c1c00d080740700038003400c481030340b01b80b0042048900d038044046140405180150402c54050001030a941c0c922101d802e05800900401a030782c1c0c0d006c0389082c1019411001018001e2010502820050450203448440c82d200c051070b01d4222071010490380c1c400c9904040301d80d00d0405040c0291a504103074401c0707521202c0c6405061041101905032801514605103c94850b802003c05640990120312481141d540350540c8a0146d5150311030305a00e0380010311541c1e62101718440d0100c00003c1aa2400e04c60b9280c0801d00c00540c40008101c1d510030700598102620902c03044540410042a610003215803000004200c44558070524180480310380340c105059280340504280002002401140d010260940f4100003440c8250054038180307005805441c0c0f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 912528821 1250 912527571 912527593
    0x80c0d0b25080105010e0411031302010c0812070206070f0905060a170708090d0212180a0b0a18170c19240915080114060c0f01090204060b2a 62
    0x2495071410401070042141c00e0300411807540c001c58504507000c0215400c01c103105442100c11900c1c0005441624a4082c070342000d0210b902982c1c10031021600182c8498807900d1003000a44101004c88121005010301e40109864078000c00907585812415100e0100060500e01405030b0341c1c004401d84004c00240c0311421901c01655080e550148a89640399001850171a85c039620b000c5d0b200c44c1450455004000461981c7c07103031003d80720b0302d081340150014022030039000a00c00c1006a0803c2800c1d10000801504581e001107402c0d00200025100e0300074540e40e91001130701e413a0303004078a03c0c541d00b0103100c0f0070701031421201c80041c0c55404080340915540300d410070240840030f560000071600102480401e4030f038004405100030072184428145881e1a40340051040300e043c411620301c054112480c056a0b0359000c25540354841d84412154504141c85000c0d01034040340005a00480c40d180c0c0c045050440c800480ea90140d06010070081c00795940b507290075005403520360b4100e80c056044402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 912530071 1250 912528821 912528871
    0x30b060301080613230f0c030a0c050d0c0812040504050f09100f06151718190812130c051509270106090e0a061401030b0112050a020d06080c0d0b 64
    0xf005c0500704e04010815040040c031a20314001d40e0107209442544005201e000090102c00690180c580c2550708480b90b2003c5c0c6030440d1f031641c080c0c01010b4903020700d0115000403114000a8012282c00719001d02c8180c685013024490880152341c01803e64001000043e02c144594002c4509001101d0000420666032480d103141c00030179000c0305000940402e41001d0990070070b0052500002c865000318044520302c1c0f841c55659440ca2076600382e0980101200301802040e5044d18078450200c03901c207501d0315010b141d0100a5828030700480310500c07182c00214081c24054010506110310f41c0105162030070420030090458400c440740c880c00001c008030b01803120711100c2c8850081002e5180e6103049810482d01060080c0d005210108903480e201d410409a1114078a80d41108000e0800003207528000004035081c104480300c103011182401e05121f1050b10300c6d801041c030b031300b46140101702c5c00f600d8044841c0c41d0030180d925964004040002480030500700e5544a030403001c101607010026110f442c1403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 912531321 1250 912530071 912530123
    0xd0c0309140a180b1f0806090405070306060e07030c02010b0306010b0d060314060405210405060a050d111b010510051203070b0c040608010e1303030e010b12070303030b060301080613 80
    0x80d50b01c0c0c9864102c0401360b03082c088250040b0402c40d07800d0001c00380d00720000814402d0700074002d52040c05d400d008503007404000d00c03011000d160407190a002c1281c17542911040420140c0300640002d150482c401c2e00a8810310803000645c900038080c1c10103910b4030b20740a03241d0f048022a900102ea60b0700000001030003212121351400d007000098070740340c500790074102d04000310907006a00100400c0b11028081c401d040840303051ba001182c0241d155084d11404490b14040c41c2c1d0040661454000c7c1c800d84501d0030005011003601030409025181d642d080040c1c261001a12221350048010805002903d00303000c0425686410700201e0781009500c1d01d49900421702038030840741c480700020303090100350380c400440b40c007500f29080d1186103420160800500030000d0300d4040e04069079003041060120080d00704210820700100491505c0040c4440725840300300520044000c40c0c0b030004500018100702041d03d0480e07002d5005800c081d9941c4160039415290380000301c0d52003000c0c8190f01d444480000c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 912532571 1250 912531321 912531359
    0x207060501050109050a0315110706050415060902040605040b070809062b1e0c0915030e0d0e010f050f0702150a08180a02040b120a0803090d0c0309140a 67
    0x800c040d403400d00054800d00198200a00a902c50a0188045185195806e101407246140043c030a500a200510b8500401c1001041036081c01301b40414000600c04c02510999540c50030407400d90780d130041000324440e61013550040340042c042044140e1040000c0d01c0c2a84c0110fa410385070100003000a0040c0d40308171480103020580c02031114281807900700100c100030000c6410407110030034404180f4103140c0303003140219140e19883c400c440c83d882040d10034000c01802c500d1207144003442070094081e20005078800c40c644100510306541e02c0c400d04600008002c1a120703030300c0301c0c0074500301250035a00a204143c0103450400032240141c50305401c108080722540409038403030f441800002d002c91030107081d0120309228800c0101c544d68000c1000511180e040f180098034108250100710385030000e020348202802071600880c2840484c5004500c0390441400791240303000700302001d44800d10714400141c0000d06c6104e080c40101c40d0f50460402c0008024140c0c0d211030b503605108aa0a9a1051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 912533821 1250 912532571 912532583
    0x1101060b0c030d0c021b0f130f091401090c03140c0603040c090b010c2307090c02010605090c030f04171c150e0c0a0f050d0f1a060c0c04021c0207 64
    0x680c440c03c58003510400d04078803000e102810300e0f646000084c06406606800082c4140105100500349948080c0300c00d0f1442140181844141074003c0b04000a00e40d11000f81e8550081c1d405407a40702e40c0600c600722809138048400100c035421500c6a5100c0801d5500402031072040744507104550307440501a5200d58801c610328034a850402d406c41090380c3e000000315041c4100305c0000c100042d4038042d1608000750300120300a402003c1c950040c0b8180300c0ba40001211071400d06c00407010755064011a043e5041520041e02c80e450f0851081c1c02803104451102e180c00c1200c01240000e0030700355242200c02c5009210a00b0104204449038040ca00c600c170410340c06545200860102c58107140110040407c0044c503400b88c034054990b00200d11924042000f001030824010105601481c01e0300c0320400c010008000380c619034007000000b03245845a810074550140c07180a50782c509901200ca5051044014100c0300c01140140000382d08044101d481640907501c000032040380901c00381c1149400b4030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 912535071 1250 912533821 912533827
    0x30a0803130f0b10090b101d090a0b03071d19060302031e0d02030a140c1e1b0f011704110d03030203061e010206010b0703140a02060702060709151101060b0c03 70
    0x81e000d0301000340c443e40050007650801e00c0341d02247e510104081c90f0b01e02141001e07000b40418480f140ca44003d0054031b2584190001e00f4043d8403080b075400310b50080c1058048440841e15001c0001500c140c030703019171040040510029050b5944c02c1b0000220300200030010800c15140d0740001d0600b60b503101703581d0141c40a44c15003500c140040000e520344402d1800518905424803100800d00810300c1184104404001501c40c0000000c012440701c1c0c01200c6500b00076420042c258945445410110560301c950131160600e05140503071841641c07940507110104540764800004503a0740c0001c2040d41e00d0809103660151070b440b64020b43c4c041030703c241c1c0d0050307a0b0300d040c0d000c21011b08080415400010844140e54455980018419043d6144221126224640b5113800c07102ca1101c090700c964807010114103d01e100350001400c1d800b030002c0b5000e40f407041e0381d107000c1100c1e044035600c40d840b030140c0740c0003c0d1f203101400342e0b00381c8000465110001c560b00340c65101d103984c1503000c0007908909034400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 912536321 1250 912535071 912535081
    0x30308090601050f01050417030c03130e070e091302030c0907090e150d0b1005040c1d0d0503031b09090f180303040b1504090b1023030a0803130f0b 65
    0x911481d800750404540e400035108664000808600407401107030b00e9907010000a2140c04020001d0b02c10341060b00c41280e0b230f681e400c0314800c06501070b507100b124502c81c5000d0104203030300c0c00352650802449002d000c0c1001a500c03900358050319140307200266054041c40c9660300103a1140c2c00d19512645840d00d64800c0c0720325140b03822007044001003040404092042031260265201d1140d4074070540c000d0306c502140c1d2204c02d00211406040e80c070141d0700918007080c3c065410340056002c1014008104040b020760031103402d000000965560060041c0c1082001804007001070252880d20060018903a003482216008030f6200c040c1078031540841560481004484415409014000d00083c4042e50075420f0940e584040c4c031002800103c0340c1807241101d045152150ba00408580f500300d0a0446c40d810b00e0464405aa10300740204000c905070441e1840051591a4503200064005030007400b900040341c0b12401c582d04054401c0d00c52200f8410602c003c00c202d07001c140704c2540582d402071001d041c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 912537571 1250 912536321 912536323
    0x70f030b28060306080c01080702160e0a0f05060a090c120e060a0b150301150c0b040c090b03370b0a0e010f0c080f0403030e0d0305040606050d02030703060b06040b0403030809 77
    0x81c40d44004101420880705204404003c100c0c2079079643d003800c02c02001d03128020140c0c10a0700099050480301d211810001c2ca681c648a01d990051002d6001009131492540003c002e4420444a590300b03c0000c00e4204504030762580442e40141c20780c60580b40f0040684d0034501910400070610705598804030a0215a58462148440303c5500b140e11001c401d0114440d8a03043c041481404c0066501520801031940039015030184c1d6a400160102a8909443c0121070040c2742e02503400d0740b034909a1030a4980c14000340381030582c5041d02d82002480001110b600c01c40851074040c1c14180c031002d110b01e0025001680d02030055070310000118048103581c1081c4d08403112010041d02c07190800301c0e00d0002e160410011034020140c0e540712411a9a2800d00394042d1203502000040c9118010008010b140c1c95444180a035100c0c0c5004d1116658030310811900314206007010b036060300000410400549141d00a410b2010081d01d03e60425a85860703851068110781e1003075022840290030000b00a030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 912538821 1250 912537571 912537649
    0xd0c1b081608010606120203101212020d1b0605090304030212070305010b0a050a050112090b2707030804060807030e0d03020703080a050f0a0906060e0106050a26070f030b 75
    0x1105400030003c003031a00344010100e002c00d1901c0d00281f68000b010480403001102804007809140d421241c008034507103881c58051081a47c00d000500404001003825441001e03882d4020700c0011640c001084a9100c0b8401040003501824031840204800001030b00e44000450541000f031029151240c55803e003a42034070340e070103495840744007085418040b5586042d20384d81501c5c030130720301500b0342c0704080440001081c2c51b603400303801803560108002d40e80302caa854500c80508148081d082d90a203401c40d056480101e03020003054003a00780403d03c000c40c45030040960040107440d020500000c06000f15081245030ba0004001070703000182d03402859001260190020076180c020002440c0400025540c918064410400652207115020502c0410740204000c0d080c45181070a0340e594648000e4a9a40a0070b050008143c00e403c030700703400441025a44000450040840030b9903a91000100e40300000951101c0615682c3c0c40003820703070340381e0311080c4161080c604072000080103119180c0bc6604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 912540071 1250 912538821 912538829
    0x1707080715090b0c10060f050301112d0f03090102040f0b0901080106120b0307080309040b1c08090d330c0c020607020f0d05010906050a0c020d0c1b0816 67
    0x34807007800c00c0403490390106028040718180c3c0c2c04561100e40322140340f800c10607800c00c07030700c125410070314046881003503110f480080703070b074100c0c02044100c0305041500034500032041803c42a040303031580000088035118081c0d90400d04081d40c2450004404908040c2d60020748034042140c5d40803906100340d5680d11308210180101401a0b0308085040d400206600414007610081101c031120b54000e5045540040d01222001030503510041d403070701c00c0c2a503640c0196040b5803242d1700704507107001941082c40c5140c0c0000000140b03c040c803545034803041113a51081d4481600103091800788008100360000711154010101c07580903041e041c58040040443d0301001030a0403c1c03404101c0b407017444e0030a140342d903e01d0341950401e403a0061800007940407120700c0b440d280c009401824610401006501100c0310034880e0204200d107031038290b603000c12619808a1500541d10040c0210f9000c0e000b889044819442409485146115404074004c011030b1b84d4040c6807030b680840c07014445085070041c3d94000d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 912541321 1250 912540071 912540089
    0x303120105040605121f0b03032805031608060d0c2c010b04050112060801050f040c0f0f0608040c090c020a020310050f012d17010506030d1d0a17070807 67
    0x5d440590803103880b180b808500740544c08210b02961030240b01900200d588410003015280c440f190b6800492000d4900c264890203030500041e000d008a008100707803805000202d20001c080c0070405004d448440c0041c00540d840550301050300000b0300c5102c061005001117001410000c02c0c00303c179600c0160762555440d5002c05d0312000602c11450f20f0020b450844209203054851410301141c10402400b0070f82081c2c10030350030310081008407101034400e64010b0b44540101f00489613660a401411a12402003006080a0110400c0b030709220320f0555400601030844c2182640c0d0342c40ca890111031141104078003581000302c0300e40035480c0078440c4d10340005034180300344042d1500341051340044105000c0e06030140140d00d00d1450094414a1042003e50342d1000030903c0e41d01c0c0c140314400c0203e400070f01403007076003003000203202400c0c04250320070680001e440c1c00100510a880d010a1078a2123512107800620102c000607141c03c90307a180507201c00f40240074055290820b5120703800c0102c1038005500d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 912542571 1250 912541321 912541339
    0xb01090912020f0c1c122a122604111c020306010b070c0e0106020307022806080c07170904060f08120d06091d07050a03080403080f07020303120105040605 68
    0x3c41500410711040700c490485407060722611026610100400e48107001d40049141d4143c0080560044c0030900c0038081d03158132160000810707500d85080b1602d154000c0100702105281c1a090703004819401a8403075042c0c03080d5001624880020f4030759802c98082d207241d401003000c03079582d0500d22249240169091885000034205401080d034840061051184204001801c081031150782070700440541000303050310669580d264002942ca81048009a00c920541414a002c40351443e000183d1b00c4bc0420808a84a140002c25614444000d0100321410340c1081100000b500700c10440036580540d4141070380761001c07503041c802150350702c0e085a0f060355140c4106010904000442d04041c10140c0c01c1d05503641030b0844072002900d83c640c0002c00b02800d00e035080a1790315407103681000c550150390480b20029918020002d1081c481e00c4040e01c0c40c90300300001c2c000b00300c404000b0011920700308a20b03840c01101d980032074031b190700c4403100c0303070320040440b0040c029480c15000d0b0704002d207000c07205900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 912543821 1250 912542571 912542593
    0x7150c11060115020f0d030b0306180c15090a091406060a0203040911041211100504060f14130b0c1009080910110d050c01060e01141c0b0109091202 65
    0x160710031041c000c2c50046556955440e100c24400c003c0800e04580b043d0903184500306a200143c01340c2a1248100d129000741c200040280040860703402c5181c47e510002c02801d0340e602c05124a4800c040c26002440c041000440d07016200c101d001c2c0d00800702d80100046448040c01040748185001d00b90621414040009515859001040e94156204500d00007951085120303000310501c542d500451342ca42e400c1300d0b000288400c0d840c5405602c00d00390303012800d080316071004503001c0c810f50049001058a8075402c041d594440c14034a100000d07648007903440c00c01006501000c107403540d0302c00390109030700141c0c400c201e8005010781e02c0084042c50341401000c5080c1e0f01d070030107030040302c0340540209034520b66105014850000b060325508040e00340c0e0040030303103100010f0150340000c3c0c1080c819030038924001901c0b0411038555048039441c2c4106007540d43d150f410050805652082c403401d41911940303100104143c500c00c50300030084180001a0305070780303141034050303544000482015500903000075a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 912545071 1250 912543821 912543823
    0x1050c040501091505040801050403031a0d0c0b0a14130512031801033207030c0c02031c1709150a0b0901051005040305030c0c3115080307150c11 64
    0xc01361a030b003010103440c5243c0b03498115100d004a0b0f0041e50700350708190501040c980c065204c001024210210300c800811f10000340300095410400c002c2c03105039000c10801018400e140038105da200b031480c116003070040407518541c150b042001c0901201258030800c001c5850101c01c001e0070464100c018500b400300200b1036002c1d80074407c001505040e280c4602e5000c001140301002884651000c85110100d40301e20124066102150f8040102e071400100c561098081e900b02d01016600030018100890605803d102c00f0101d45050703070a000781c2c030482c800c3c03160481c01080c0c400c59040c0001e11707425a63300109204280c004d80410070f1685060210946904e0b09070545055800c140e64884100c03510f00003c4543d0301c1144e002920394040403d00c00c0141c103011860040086003110813101e0000b6401485d1800c1455140f8003034511440404941c08070442c1c1c0010a00b85551080000d036240c1e921022030440d44458022980d030442c1100b503070043c00007440791250b100301914224004803602013003a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 912546321 1250 912545071 912545087
    0x80103050613150915110f160f0c0305030903162d0f09090b0f06010219030c0c0602010212010603050c070b060a1703131208071112071701050c040501 66
    0x250a06810078000820301040410403000d07502100f100b04010506801c00c12090255624110801e80c1445006141d41001e04160b8525415a441d2240b40030b018440c1c0080d0350014242c12502011031850003004115000c1c0e56000540c01a0040c5a80c1e0741041c040608028502c1640c3e054060401000d01210a4203025075102d83d441e0010140c0390395a142000304182e841d54001c1e04001c0c010840824045035a4110a010ba031052075000801e031180c1284200f80417049401c00d0041c6d014045010b0200d102e4541c00300d900780641460017104c0080c0e11991a00d4185410110150f9000103401c4055003880030030500504842c40c00b0042420507080c40d490074450500d000d400b000c141c00121f0b0a694422120100030042920460b2144100d01c860980b25006918520700d4519041000214000051560300007107a000d6159840c2a051b80d0703800d04d504040e454140e0308010f080795003c224800400040c0013912428a01c15850908400c0301030035160020481e480d1800280300422059801100c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 912547571 1250 912546321 912546331
    0x110a081b030709060e062b1103070c03020c181b1303230606030316080405060d0608100c050d270506090d09030b0408090111010212150418140c0d20010801030506 71
    0x1125818400c7c09240b0000d403001c80314020001d400001440b1140b6041780030030000c9031098083d2039103850341c40d0400180c01719000d00c0c02c01e01e45165001030385a1070b40309080803001440000c1141099000762442c0d00d4034460341c000300d0382c41181c80c8000b8012200c4038025000d291200d8024850791074480041b0b42c4078064000200401704007151200100480c0c50300f52000b801000c1c042c247c98403060300420000d0500340c4103680d0927020700d00401d442c0d03c045008407900180992641d03444c00207070441c00c000131300300d060440c440e03105202c181042c10102041000c0245000310300400050410340c0c0d41c02e090202100c411030070301050b84070400c001341c040f4070001d81c440e402561003500c0d803011f880141e6294041d298a440b083d44001824414044850300c068052048032a0000d2002440c0f400c1c0030449001003c103940d1140070240c6480020402403100d000841c149060710400d00c912800300304401c01c1054102c0303504c01030134091101d40e01d00b602040000c550920f03061019501d182c84943d00c503000a48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 912548821 1250 912547571 912547627
    0x3020a0b0a0b1807091502060103020f0a0306020318160303080a0207030c1a070305070807120b04060b070b1503010203070f030e1617010c03110a081b030709060e06 72
    0x80000d9526005512841c0c2d0403030050806158804661000f0703000340d00c100d402601103025520013084451000d1000c04e0245c22940003001940d0860b020030100c1178005112660005103c0e402000046803400558000d0740b800490310400f50b01c000c50103081c4980b0704580002c03c0b180640400109500c480303d80d0304080c15140044e0345d52000c0c1001c545c5a4055240504003c0c041036040070303015016101e1300d1191a03550b50401003a00c4851080301c01d0a01680c40e070000404072080c0744d0b50b4801ca90301610314881c0045c000207809a846464010b1b6070882a82a12002d503982c0400c00701c0d00070b0181098204608500031469803402000240201007070641e140f0825070747c1c42c0c10700e038900350800000442c0c8a0302400d18144035601c00c83d00584480710443c90102d9404c002c0e20191700d60082c018240007901032140b81d0704000c00d4103030031904158014401e00b400d0b000c00d5840b042e95105c6d0740085000d50907903a00c2c024401e09214001e00400012007a40e070040004000c01c1303110800404421360040c100c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 912550071 1250 912548821 912548843
    0x41413020405092b020f01060f0302010302180307060905030f06060d0b0405210304060b1816050412030302040815010b041a1209011a090108030904090812040b10080a03020a 76
    0xf5000d26280030400c001e241c00c90140c8001005003010140c81e403400c103240d42100d010409803804982640d03428842d95030038040d600380070310056020383c010380400956038000500c00100000040e260414951109020403003000081c05141403d000703001c01000041c00804680c142100411a11112020040c249201403030110317080040c14054400041070304035005041c4610603000c1121176006640c1141c070a031030b0003d4200302e800e0400401407920443c00c004039095039212101c00c0c01c1340105400808000d01040f01141c85140c2101c02c1090034003e950051300c60f030400180c94075104800c140e44c401020514010488498004125020380b0180002000c00c206440801c85481c015420306688107000b0004000080300154440d03420918261b40301806001848188440b9440178010000c0a4000300410410740c03e09401420710648100355841c40e180310b070b1044000080e41911304559043c0c0b0301042c000c1103000322038070201501c02000a88240703540c9a5020350b40b0a00d1100045c041e400d11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 912551321 1250 912550071 912550081
    0x16030f15120f08120f2511010b0604090e0d020f03300f060a150e190b070b060f0a060c0b0a020d110702090907080613081b0309041413020405 62
    0x1088003070b1602d03884070000d621004841884600c48104681c01904804c0c401c0010381c1c0c03444a032608403c881800a1403100484c0d85a40071183d681145207106455900c510300c41d032040c1c44901c014001407055003000220144441092410200391050040441d130011344500100c0801000f07d40b4000400c0c0448902c01c0013103800200810f00c0748440b9010680341004202801d00d0a0555034450a1700b116801010707038030754404d502003541c1064240c0014000354108200d900748880086401e140d4841c008030015641c0f0b072072a0040d0301c140c0c000c4454903400340078800c16042100c1200d40343c0d42d0480700c2d60003003403c0c13140040c03000503d440c6c040d158604d82000710f2420b001030748c11500002400030003440280178198503000b05e580480c00803400381071980c000070074030200440c00070143c41460000c1c280680f90302c0c1e0080c10300c40c10b590058503c000100b01c0c003625034a80c0080c1d10301040c00300c0c0c041c2d51210180010413080329815462460b2489134101040340240d82c001c54640b0040e4101c500080c1c680321 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 912552571 1250 912551321 912551333
    0x405010b04090510140c09060304020a0312020f120306060d050601031506030e070b041508041505011d1605030703091703010f030c080a050604030e1816030f1512 71
    0x20031810039820500e05034140003404404186180c0d00e4201040502004100c07a00704912000c0403a0003165080b801d00111034146000700c02103030414002049000141e440b5282d280c042082c3d0049040980c0c011a0202a200001d0005040040ca1360207898154035242021030414800d11070400c4005950b00c002805581c003a40c0146181408000703150910b940721b21020340144000000c0c030581d80308282c0001500c555070301c22101030342c400a0701010b07410740c40d40d000c0e5a0321038041e00441d43d080111401c0c2d600b07445a4800c042c000c003091050300302031074401c000c210b00303245c000b0f001401c590380013100c040d00107500201101d0b001380062500041d0074460381000b0120310341022010310b600b0000000092071f04030204000090b80d00a136228038010350345143d100d0360342ca000000100f031904120300003008079000d222f000e42d140b4405000c81842d2850b0101c40c001c00d0328116104031806044900c100000c1390b2600ca2062407100c8100c1c1000303111400d03850501d00da0351520a03070b0406090032030070004001c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 912553821 1250 912552571 912552581
    0x40605091f05090f1c0305060105041a07021002010203040b1f030c2418060e0f100305040b0702030702010c15020f03160216120b0c16060506040b01030b0117040501 72
    0x100444848007048002812001d0042903515105502c19620094240703000407800c070900c40c4107424031030204035079003400f079010b0080101842d051000c140400100610034840c3d80369a100035250040e40c8013524410400a5194245038500b168410720401001881007c0c1c0284c02c50400348203500c0c1d80042240200b101e01d100e4000820018250340009402003c090001003e40b82c1020860b0000da00e0f2034080307445130744680c1d1074850401c0020b0108a910f020b09031264250102402c00409440040b0110310000756088103400000d1340d40c0104001d000841c1c690b9900103009101031072510070503400003000b0070309100340540702405000c51078286850036412120545080b0000945a01d003095800c80c0905e840304914003d402000e0042130f142c040c80307140d00255280c3c000c1802c0510070bd629070030810680104035a1089000b003207410031008001a4003814148500d0001c034841c5440b030103000c165110090b03030702e0500d42010b107110001c0c1e800c020411003104000b081c9040075901d60a041d40500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 912555071 1250 912553821 912553843
    0x90d1b170114090c03100b0a0302101d06031b030901090209070f120c051b070b0d0603031b1214070b010b030a0e0606010f0f0e030601060905100e0904060509 69
    0x445540d0030600d00064129190000101040d1030240d5120f100460b140c009a44031207615800c00410382e4901445503110300d0b24108003901010400340c9135404192810141021300000c110504a2185481941d8490131b4642d54107661aa055080904d014580000030400d01d8036141c1001c000651050825441a0785050f0000c2100085042c5075002505054800240d0000643c41411203003480342d240c050520300041a60b64649050b5407080c2c4c0440aa958a41b154080d000b00f8000007840c20761180980031039100e880e0009009403945c50050006900201d0702c046d42014070350544041081401c41c411000000d04000044032555515030b0524850301c0301c0180312080d0f040001c905003c07801c01852203a80e44c40c0b0100001506541075980c0c0c3c82e0102c8005000545561501891504c581c400071008822400e042d51852244000281026426002440003400c0c40c44d0800140c5000e20300c880307040344070307080c40003080d8100f00200e2416400104054141d035190300c046045c08104100446d049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 912556321 1250 912555071 912555089
    0x207080403080309060c0702010206061c02121c1d010c0224091203070c0b130806010b030403090e0903030a20070f031d06030402131805010b010311090d1b 68
    0x480d12031400410303d800030b07515410340c0d100b10000214809051800c030361600d50160010b020341c1d501c06c0200429169604003916044031968242030040e242c01010100c0900020040e01c184817003140942030050106002070100811040082c0b0100710f80c400b030560070442032910210b00701079070010420040c0304152084030700e0f40114440034200280e20150554040c225884c00e440859050110380c0c030300a6002c090003000469904020840a010052900c580100b00e014078066448000da41010400d0f0700a48803110008100010035904c148144080c1180c0d560703a15850804c2108207559000003065003440030fa45142580b002e000071000d00070712002100e82c0c0d694429480c50000c03500000d0b0b260450100f5451107251214461800ca80242500041d044138203695454081051a98000302c00c1d60201c2c0e607031055140d40903415104070020b50300400010418021400005040700c2d070f585070070407140109000c02900c950300c50344a0380115401c032a5004051116000c007030120020340d4400204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 912557571 1250 912556321 912556327
    0x102340f0902040905070504140d03110a0b1b0304030519030902040c031a0a06020d05070c050d0b01031a0c030a0f060e070908070906120b072f10150b0d020708 70
    0x1c00340d03150000c20669443c0320040c88039448183d020b0303d00780160b000b070407442801c200e8000c00c141003480c81007001500905c1d01141c9000e10350741e0ac50410810303003002c1c0d80c00009103041283c060304010320140800608080c0c00c0c91460b060324001d0580c0102c24071903810f1840e4503003410740c06219820812030307141c00410800103030304182d00240082010a4201003140150007e910b064506000740e01c080740c50a03009003c0155240c03004603003a034003905044544c0800c1202c089415190607440504980c420356901c0215411410182e54035140c1400c0f006841007248100030b0703440c0185040e603405c503504e03003404141903040c052200007600d000d411240074844940c08000c000e69111901d5000c03140154162410151242d41001c00c3d12098040e800341031402540ca40d00060860150683c402200c0c41c0403400910f000f80003d140d140031088010040c00626200e04440800f4848004c229502c1e01d070801c81c9501034114055581210302c2500315103840480e00e00641d2655030100d40b002c503031040850395 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 912558821 1250 912557571 912557579
    0x91008070e1e01110a02010e0607080403140f1002040f03020906041b120c09050307062613060b0414010611010e0712030e03030708190c0203030d06030308060102340f 73
    0x500b5111034900355001a0306080401680d460100b140135580c0d03010782d580d800600000702804040e60004e00c08980c00382c4100400400b00e160340c2c1c1468040d10420b4044d0110000005426181102180d00030380c40d180f0402007004008008030140301100d6040c1c074114119a20700c000940105800b020b41c1030246001c04200841c0f580c414825180300f10221404c21090b0aa040d04481030344e00e5015846d0164000c82051240c00d00a0158020150481002c1c0a02084128081c183e4050546102662074480300c3d0100c100300941c01400d0154109076420001149040c0788800225018407510042c0420f404524a0f00c100c04e40007540ca000114081f645820b030f0310810114241481482a00002c00520f00ca1038940342c0401103c81e8180c02c0004282402801901c6080c0a401c0d055030205200841300101c0050302c0600241814240a003030001d1f41c6c030b1443c10b01421913400180050b0440d0080d00000003c56802c5134440401041042001550f54007400c0008280da0903400c049400c44004070001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 912560071 1250 912558821 912558859
    0x1305271b0a270303080109021615020d060902090306071d180603060114010807050c010605040c050306030705031f050a090c080a0302120301050612090a02150a14091008070e 76
    0x1200c0002c01074030603807000d024103000e0242c641c68000100095140c100400c89081960003400540c0c60800540312a050256140b2003544051810404010340104021107207000521400d0020900a0029450905c1550010341c491302e000740401c0500a9803050064000801d000048100c9030140400c55084449816010f40800c11580c051007031150308000b18030020080b8200e001c1c0c0e00f040c0c41d11001602e078210144d4050704541440c1600b9980c070700c400034040e0703514090040c06040588402c0c0c0d5030704010051505044550708098041d5000380600310305a0303030060002c841103a42d42c20008254882d038068601038500144007a00a42c1d00301008154900042100414640309400b142c18210300928070f011107000920803030b6409103060004d6080410900500e651100701d4000743c0d0100d042e17650000300952044544d2103005080410164200c0d031300040c0e039101a01100414504002c1c0050001d10345440340c980b61402c014019012521046c011001d4460704880209811042070ba0030802c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 912561321 1250 912560071 912560087
    0x2040c0507140307051e10021204050d0801030308010501110c0a0605030f13020607032a110a0f180207150f0b041b080106030b0604030c0b1305271b0a 66
    0x140e4422075110050482000004100c0745285e83c001c0191420340c0c2080030035000ca04035214000181c1c09040481088034030140300406010511842041150805007005407810507502451000c1c01309030300050010079000603001d41126403d00e00705942c07618902030f060030646186141c0342c10980509000c540160880041e41c86130031040301c00209692800000a145070703905c41c001e5003107007040081c130b00824802c003000d691100044140d0403066111891f0410a04100e01050f213380603a003c030380d4114540039403035200500007110f40c011070b14104034800f10490000300300c0a1403541c1c0099900c080094040d128922201c45a030100302c0000c5003041031015000044180b0720840c0b9040903107aa64010500400352507445954a50041c0e0800c02e0650080c44600b15190b4010024030000000501c00c0800c0300c0609034a4041035190300c505100d42030498a150440b034403d41d10b52651000140c0340300c0314080c0301c5140301c0100c1425102c5094070580d44110b0717500400d02c40d03000544008116008000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 912562571 1250 912561321 912561323
    0x4030807030e1e0603150904210201020421020d05150406050a18030f0212071a060303040503120f130b0912060c071103031207021b060a0903081602040c0507 69
    0x4000050301e04600300005001204000101d42d83d07682c803540401c1c00e04030080d581c0251300764106002200407000040e5400c4c01141c04907481c000515071040c0d041c0900c018003c8030a901d0000758105428101143c800e4901c04200c01c889400310800d920035581d90010740b003031a85c2c011090380e65119040716010030440c001c480a4520909180210302d994442d0310030160b080c1d40c010300c0e280c2c01524503501210b9603901125040d0440c4a000e8440c0b040740c3c6068001c00c4003610840f0100c5108910404070003c040c0000c0c001442500180001c2000e510b01048145164000b1111503565000c41da8240049009850204010760000e80d000310313400d8003100c000c04070110b00707c030140100629842516980c0401712078590382000103010500006261250031a2102001002d82e4103020171144d02e048200c0c02100c0d1030703006070310400071000d541d050b0140c0054401015035000340390000d204000352a4201510004048000025002c91488048050b481301c560340204180089810312100810326044070038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 912563821 1250 912562571 912562577
    0x41703070f030c020c01050708092b02130501050603070f110106090e1c050d11040305010c0305011a0a0206040803090c1807090501090e0a0b19060c15020315060a140403080703 77
    0x201d032814000070310f1405d03402c0140d50703c41c41e06030241c1c1c40500c2034003c00003aa421481981c908003040000440c03040314141303185644480310f0b0443c0100905511969802c0294514000050007903444030720482e60311006034180708424480e07a040448810605071381200180d46401404209182d0a0b040480c10303140c041c04546000003180041c20741214032406a4010900400240c40c94240b075030041282b11607001c01d0a802e140d5030307840e503d00303407604074002100103540c400040c4085060102100d8002c8080e8040904081d200700000c1d5603800042c001030800d500100014807001d404110500b41440b014054400c1e000c15000c043d100160142c400c10003050b00040e0208036948100700701811038a2000d24200c0c65125103094074010f0980c45d46150f0441d5046a4030090008509000c50091000740d88403040070031b0750700306030150200480b1380607203260040003841125181c0000c1040000301c110f0381c441ea511381240c000e450380041b004005e40c103100301180c000300348600a400303840c125000391 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 912565071 1250 912563821 912563831
    0x41101080f0702060403030b030f061e0112050a020d06110c07080c010f02070e070e060f0a0806060327100603030203030a0e01150911040302120c030f031809041703070f03 75
    0x10340c0c0890041c11200040103038010400640424401d4100c0c8130b07004c00180a40700c204035690541400c1001c11124100110340c43c0ca8980403042550260074014000280b005000213043d0791166243c414850000e481507254449030414440c85a01030500c0f04064004070b0b03947d412101c040f644414452040c02803034020801c0184841d4054820518a0000e60740903019841c10860360078495100684034800700b0446158648040e290340c00108004050000ca03140c442d848203c005210090050089020311414030501c1506a40e03502c00d0300e2102084104090950441d0162516001d40a884021b410341130a000100340360300800118001e00b42031100340100615140040d0999800d10f0402e00503400240f01001840c08a6208074140f90042c0c41161410350f5980016000074140d1108541c1508070390705868407403801f000040c01d180c1820010b1402c209000440088002030511120700403020b04c000102044000c40700405002d0421550703d071241031988004101c0f000c0c11100304007181c902 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 912566321 1250 912565071 912565081
    0x705030c130f15060e030114011413021b15011202060306060703270314030f07080d06080d030c200c01140d050f01031218120602193903030c051204110108 68
    0x44d40009050380c625004030000ac40c10352040c02541100e00c0001d668107a070a01c085040500144213010694600f540104003410180480381ea0b05e44044c6d001451041c01d0303141c1000183c90780d00603a40e000004035142601c4401e00c3c1001c0c1c500440510f040700c03401300c40e4015100f0500c6e010b0100d506a0f401944148500c00c58006565034074402c010b4070041000c2c0c14011140046d9104008141c251140300020510a9403a81c0d0340e071401c503905081d000481d4807a01501041c50780031190b01c5c4541e240c02d56400304003145180c110707180d460704850039040080c84c0f4656036040507403008844141c1c03004003041100346000d4400307241d071120030300088502c0c031052422520482e10442607110480c0c01280c0e0403900c1841c01130800000000722500b110195000d2100c645400421981364483c107442d500d9100c014808908040c00160545804500c20301d0b41e05031550440040d2401a000194182000958082031070825655801803802c0310240c80350301c0b420001042408585031103000c6c405c0e00d44440315100c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 912567571 1250 912566321 912566351
    0x50d050c120301180e1e0102040303030c020c010c03030209010512130c08280c0506030a1b17010902070606080a05030a18030210081f0b09030705030c130f15060e0301 73
    0x7845038030711040078031021300c0002d951940b0280c0c10520520480d442c0c00400e0711101c050100c1c1520390056a51702080810605416000d2804c0189891000c1c028201c002400a89100c6d130407403001d0b04043d408140529664015030483c1d40110880d4100030081c600380a184d5070303442458030100d4145c0740134000000c0f03d020018485000c24160507201d000c00c080e4244080c9030041d1844181c0e08183c1769280010740e078503010f00440c0110032019001c9180c0817101e4002003000001c0500c60200620003000e404019030545c002810342c0d208680159948076a070602501030811900200d2443c014a00c04608101c00080240556550750300c91250742005046041e040045a00c0013940140301101d2101d8018400d3710f1403980004003160518610080e441210401e0500da00f100a0b000c000103241500351030104501001800101d000b8040000d00c80d010410329044000e0b0803420f1512102160300d070300050341001d00b001102e490032070b25070f0b80c0c0c1c2ca500a00065001855501a510380305828801c054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 912568821 1250 912567571 912567577
    0x18061415030f0402010903020913111203040303080a0e150915010b04060c060f050106020c12070f0510020a06020f1c062103260609090312010909050a050d050c12 71
    0x20310021050308654642d0000462048010000ca040103580d010110040e502c00c00c2c094001c503582d4111a58107411403600820310200464040d22464405405845c400e400004680c00c0e80e03032524112501d600e501d011a005030003041c400000c0d074015004418008010743c06aa4800c1c04002c0c1191004400c4144110300e190003802800d500030001c00060001d00d024800d010b00c581c0c42090700103401800c040c001383c1101c40c00e07085440160081c21796411a40b900308400a00d403140c410282c8006490400c0310880d583d07075445070301e002d205a09031b0b1050050007400004019901301c1c40c00e6546a00340400d0848580c00020f41c0c40111a041449800b0842c4c01c2c0300d0315040e18454500354519940000c00c041ca500c0105100b1030030000c4480e8034880e80d462410003906010120380c3c114285040500030481c00b04001400c4002c55031003440f82c82c0c21142c00303445007070440c0c041000004442460b800d2190400303003409800340031441100d40f01ca0540c0c1d4400c0040c41051504001d80329080b03408022800b0501c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 912570071 1250 912568821 912568849
    0x503090307020405072706110606030c04151509170c0904030302160f0c24090b16120801141e0f030a050a0308070f030e030a03090606180614 62
    0x36000703100307400060a103540000d030800328500f004280c0224060a140c80c0c55101a0070a00c4c0141d00d0008020554219403510820030158019150383e02e00540802ea860301c4030304815115580711581c640402d1a8695020060b184412844c01403030b11022002e8108402449082c2101c12030f200d200002e0350300400d8001c05910000d2600030b194545440460103900080c3c010710900780001c02e2007002a9506048001680c80350364401d0402d8a00003100520300c1502039038126603580803407641c030301c2e07030307015079030302d050f521482c00f025140c0c122151044001000890003d020046116041020907040b030344e0385e8103c440086608100c00107000c18000b1140c1a0003104c215258240c1d0452114903043c840c400302c3c00c0340039007242c10610031915128a04905000e00303502142c000710600c29203d50108840041204c141014044c109150702d4803683c1c0e201d00d02d040e8003090355400e9a03104004082c0c1042d4024090a217020303110760201e17001c800007009288900b91701e042000c5000b01c242c4c100a100c40c0007803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 912571321 1250 912570071 912570073
    0x305060f1e0c130f1d0903070311120414190f05090916031208010909031e09030501051509010e010e040f080904050a0b1824010315150f050309 63
    0x71509401014002010180034401412801d000c0c000c0b0940310f6a0301c20004151501009042c1c0c0e01d001c0310541da0302a0101c410404100300e608000001a000003122821941840d29400c8151502d00140c2000f201d840003240b02d80300002c0006401d4a04218840800070488005030703040200d0307540d1100c0070000c5c0b1540507040180c60b0200220b00c2c2450390158000c84075015600000c285407011410f44030b407508100d68000c901039035880307115071140c1e005000d081d0704501000202402d4030301812203034418090001e5204d01000320014144900440402140e111000f07120318207006980d15051126036420703a029611010000075440d1003c44a1412a4141201481e4030344681c0c940302d550100d40c40042d00c0c5242c00700812080341d103d610075603129103030b0843c0c0000c40c800c0000410250080c0000000c00310030742c03502030092120b1014404044840c880d1658004010381400503000703040d00004000c841141e910000451901440a403c00d000c540d5036942d00540501d42d040e80c550105403203805407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 912572571 1250 912571321 912571351
    0x403021b090a1d01050405070f0605040f0b030a02070c0609050f041812111f0e010510090203060406050604120302060105330d0f0605010e03030a0c02040b0114130305060f 75
    0x1110403540c006035001c104650301200b500251840b0901703481c0309890496550340310035000c00490400143d01c5003e030410349011441c2c1f0f4a0001811800c2001d8000c00b4284000000401d484d185940e040700c22542d03000120807805179a40101074500521481028000c00c05401000c0315880c0911554421074002c0d500c02841c080d542d19021504055542c00b40b0501854603803840003620101b0201c20068071105201202460482c40841a281c0e04a20019140e0500003400b40c58202d00c9008d0064a5240000685940c0c42a00040213003806a01082e082a000203000c101c680401512600c0a40030340c0854072103903030381d20a101c1d0340f204406a01010328134103070003030314820326400210304807958030300200d070504041c1c605800454001c000004102c40d510702d020030155030800142254120100c02860030642e000c2405810030301a610700078400c558801d60310760781d42e0241350040c010460b1114a9622a10704402020841503103020a0321540700750700004060f008500c00140c4101d4203c00c540c11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 912573821 1250 912572571 912572581
    0x3060f0b03070309052a0117060415050402070606090b150418150b030a060e190b03122106100516020a180903030b0607111302040308120403021b09 65
    0x41e400142074801055243c00e910700104408005540c4072590250140381449465192507000c9000071095505020a0318542008402d0005469078026010340f00405c9520f10700358511901e00854104681c001c1c804103403182401b520390720103001e54000d0301d01045241e1803541001000c110b000c019241c040030800c014810841d40300c0a400d100c20003044027051400b000b41c011300101c20306412945e849030000c0104011401540980002006a80e60207251820020b0b50f072200d102030913469101264072960703100b0070f0f40c404008403500220341408880d01c40c654070308500c00c51a402c00f000004034071900c2c08280c1d00d26024400002c0076001e13485071880d090958031109028040900b003640d21a040020024411800040514031a8282030f00020b80d4003a038500901125050980c65000350b10501c00301c000610101180940107c003111a1808000c01c11000000380c0304039040100040d101107481c5100c99096074210b03000c0d600c25001e64580c0800c0c000c0300c00078035211219896001c4103400c0403607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 912575071 1250 912573821 912573839
    0x250b07030c0606030804030605060103180b060609130509010902030d030615030f0b04051f06180902130911120a09020924060c0a1110052205031609050703060f 70
    0xc1d4000d100b8980803909954945400301e40740c10640c003c0d00d03415100c90421400c1d6a16215102d5218084a072100d82e0f086580c8130450a09401004140145c0700010060f05564420900700300307801c0200001c0c8003030b10344407c07220301820200c0e004034000e208003058115140e001e4010003042d84d04d181c1081a581d408500101d016012509000441c25521281642c00d5103d50041c1132080f0b00e421091070110044201da0f210840303581d4001002c00c0f01001c07000c12817107044002a4100d681c091000360316000f9906030851165110361122035007500d410090401141104090005215480c003410100e9540354030301800d0702e409640087d842003440300041c000031803012850100b0560561021001e400600c00708210b58807160896100758481c802d0301d410440c2c07020301da00007031714152404015200c0c02035015007140030b014104114030405100500c06580c6401c00340008040060482e0907000c800c819a65801d03c46010f5446001d05080006048600034010f400c01c95414071000e60005152074591 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 912576321 1250 912575071 912575087
    0x403020c0108040807060c021b03010605181f1d0a0212071d0307030311010b0315041223030a060504020a02030a260103080406111c0c0320250b0703 65
    0x844c0d40e04024001800800c00611410718070b81c60a800500c810100c00503c0e002c0c140c400400680b00760304200b070034801c940740d84074001c402900340207604405885590b400d218000360300929803c0d100c4020400503050180d00202d01c16181d041d8010140364540b0580c40d0240d2042514162454100101165509200305548698002004070381c50f030800450b030000742000c0c90396005500082c50140c4082e4100428490b411340d601044000300400801521142031320300c4010409440b00c1c03081c420120403a4081d0109000200d800d40c8003404482e108508078503242c0060359059a410300d85034001c03031607044c103100700c40d6000402e400660828203040801c40302c2060301c90700c4100340e01025825a0003060002070241c0614031034589142c0b10b5051041c0185500702c0715901c40f03a181e205000400000c402c1c7d0b0381c9112403901c40d1510b009058254181138540b91640c0600329200754800804a5940901003211b14170134000e02c00700c548a0146034000c805841c0c01e8007d2406d400030412400b00043c0c051150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 912577571 1250 912576321 912576323
    0x120807020a060204090618051302060c12070605190c090b1b0d020c030d020309060442110f0d050903100905010f110c0703061d0f0120030403020c010804 67
    0x1100c802528a82e1070381c0580c1c01550050107000d44070103082c45408008100d5141c4d10728020000c000900c2c101d0800c406211101202900440c4006440018110240701c80e2001840072105036030b440341070b0b2800c180200002c0303619038101d4138210060003a1200600403100154229a10034026606186c2103801a9102e0005e500f03410303076243c5641325064001d0040641d000ca06401030992b00324080c05040c00c081c1c643e03980800b10f4104011b541483c0c1c1e125002c0e1400d8410f41c0400f100e441501500041c2840c446070700010b01c0f040300e42140a070694003540241510011a0344d40c00141d0038950703501360b5445900643c203031640c01c41c4882ca80c050b4454400f60540f100014200c6010600390410325017150450403081c0c40d83d0351542d10215814445005540b031b81d25030a48124a000444d500890f00c4011900001b014140c031409441d0880c941c5010040300301401c0c105680340782c0c10a00c135003802407241e0802802c251080000940d900c0c407030441524400e0ba055000b414400110000455038a080184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 912578821 1250 912577571 912577573
    0xc05090a020d061203030615090b1b01092a060c0b151c211b0203100204091a0409030504090c05190206100f180203040c08030324010c12080702 63
    0x80080a0031540d40034120003044c01d0014200b01d01c110303040080503640c05402400d0790b40d141410044070a41c0c4624030780c044a281410791925060078a05000c004d40030460129000e41c2088402d00c20310003d9070b061011145140395071030a2241c411980b05411380c0c0c611441021031912480303040840c0c40320842d1a0300c01d80f00e036031403c11007020100250f5000402e000e203441680300c0c07126900802801e280007010940946003d240f010304109001000c056541e1300d0040000103404d42541151130070043c0107800400340c6000c0d52120f4480c6503040c002d040b517030010309101039104400092801d1500c501c14035a034040c7d840a1406050003010f20180554114200030003900300440140c2142101d00020030301101c0d808ac088505040d20b038011072160307a811001f421424480208030300d50401a034004071741c010341c4001d612541c640c207203c00c1100e10742d402940c8a0000000704410b0927076482c01442e03504490000d4041c01c0780f10030700454151505844c014512a513980c18100382c54050006660b00c600c40344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 912580071 1250 912578821 912578827
    0x906140c0f010219020c0a0e0610031e02131d18070306020d090308060a051e010921020907110604030c140a06060501090801050405071403030d051f0506070c05090a02 73
    0x500307a0703070880e032200d40c4165078003005070032409a0359414082c00c010004200c4048403042d05000a07440d00074805040c003841102a403d40c070741c85a000350080c09540a6081c86241c403254002041d5002e503116141c10300d01a045c501d40031584080002c60703010b6500c00030f40c8408e041d0b0b842001050001148504050162060600000000d0814001004002c0900001203079030250341ca0702030070300ca0014145c1341c0700c2c0e886003400b8091901d0b1008130903036090b40010b114041c0020000161840d2100303810041641000c041000d00e0b40074602c0d40c09403124820b907042c580b1a502d50404440c1d1494030f1403025071541046020901192080400d01702803801007980e071141116008400b8680031481038115a0682c0300c0c1010001d03580c100501400606a003002801185095a101600e404c0c082c0607240b44504112407030040764604006650000704284010042030400380f11003940080c0000e04c003030050840a1000c200c40c208001514502517004d100d0001d6107003403000700505070304003c0441c5e041c03039400c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 912581321 1250 912580071 912580093
    0xf060207080304260d031b111005060109030b1602060c0304030f1206050405130b06010c080706091110020102040510090605090103091403070f1101030c1e02070e01080606040c0906140c 81
    0x303024101401c442c0c0c0d20009644c10203080001e41221147c1d05c1001407010358002c1d0f00710b800d004100030120ba950500c00150607612600107841da503c1503000602802c2c1814200050001f80c42e16695020300c4580131a4030313990310814036815601c008c540080002c0c8071010100c801c5400368002c200048141c181c00300c0c8154039503000c9011680700b141d81003101100700500400780404030400f1600002d003843d0028812001e92501d1140e0720400310010999a030342c003c485c0a02000100301010207900030503003c3c04507030441000307010b03402c81c0c0260f030321a01d5680903240740705018408041c00ca80164a4a50400118000540080c1110b410030b0b40e40038840d076a44071004000b48020041c0522944c00000343c09110f040080c60024880c0c103443c141468036030105c03d01030300030001041c161100d010701c040280740e07141d04034180402c56201620011783d003400130032440710108001c0c0c4617940c19602049030b5a0680350495001c2c05a1007404041500c00401c50110004e0000a054045d1104101c851480710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 912582571 1250 912581321 912581323
    0xa1205130506161406131403120709080c0a030309060e031006150305011706010509070e031504030e03120a350f010909020603150d0b100f06020708030426 68
    0x20b1102040303000d040035034581006801040c001801440710010f0002c2c3c40c01e0b03003007114503500300c400c047e240d10005002c407480c40c0c034104101c0c3c42044060251001c035040030303900a41443d100d80104e10840c01400c1e88042681410700e5100c049075010783d1601e079110310300741040d60f598942d24000c0d82c15001e0340305803440c1c403034843c040c3c14014144004074a448000e4940e004044542c1030b04914603401504a0940801800140c9141134076401c6490108a0700c40500503103211800c40420f036058050740b656400000c40e480c915138852400307616505080c596000806445624486445c88031010900059030703a035100742003090200c003030000f00d42c108464007e001101c4800c100038108082200c8410841c403030300710070038860042419500a000200c55540003405e01c0c0001054840e5015101e441d407400380d0b9508410250945e04600111050700749600441140e851900402000e07040700d04000907402e01c000341b4503003103440c02c001441c146800e12f00c88a0071141d0503001e183ca95240b140c10001d00f407030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 912583821 1250 912582571 912582577
    0x15060d0203070b03180f030712051b01090c15120c120921020a050a030806010512130201032f0c0721060c110309120f10050603010e0a1205130506 64
    0x116103c010348900e030178803540024074070810700080c0541295110f4125420004140e641d134a500581d881b1280502c103008070f5441c0a42c094510320300c108486da403103000341d041d4010782d0f80340d00412048899640ba11030101201454185040004a51030100c2c11000110b610580940300b032454400105410001460160342c006007003a60200c41c04400340036142d214481c505841d03070040c009840e866001c4d4469a4880f0a007503809010321640d000040c03020b038490800c0b81e40201815007444000d0510003c8035012212004049001c64a00140c1c01d8032180108221450251101410040c0da880c0113080c040c550003020201c0c95034800e0720008901051040c25a25025109020075030585541e41000750580c1c0c2a0a2004c040c4030b002c01030b411400001100300c480e41030741a102840d100d40d6100700c036450030341903080030721840c00341c1814038001624a402450240c802100280100290003400540390348901c40001c1c580101d60903d02c1e00d46010b00060010280c1806280c1032040c0e982c130106210b64 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 912585071 1250 912583821 912583829
    0x8030a08011401090605041520030720030c040e030d0e0d0f05041d06030f03210c0a050304290106090303110c03060105040e07050604030b090d03020c15060d020307 72
    0x5100e100040c080c0445030756440200c084246071402c40c02e4038260015000e4450380c020101a0300c00b81200706180d502840b103242d45c54100c461030041c40408955901d03129009054200c42e02c800701c401d00803100d802804c06001c140c1000300941403240a8500700001021010f54482c500e00091014101111552003018440c8050f5000b80001800ba0900107280d02d4140e045031003840010f020900003d05402407025007007c6400b040032540d02e4030380c0000d00e0300f4104500d070440c600c0700060710707201c2c1d890400340c1200c0c81c1403000003913640d40c40d9808039607a00c0c000c144a0100041041c0000340c0401e000c000c0312001c12014446031402406020f003a10713007056090f000310011844501007081015405206841c1302c5c051000074292440c188800280c0f41ca0040c814684a0350300d413012048444010b0040d100200001048641d84503545d240600c400c620889000c44680103600d03181c0c210500900803140e100c19154082c14440c01c0c114a60603060101801640d044002509000016141080881c010b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 912586321 1250 912585071 912585077
    0x7050a02150405031c0903110112290307031509031404032004050f15060d020d0506010f110d050f2104020301050603070f05060c01110703050d15290408030a 69
    0x6141403c062620780800060316100e10311003601140309569010498a050f6a840026400c42c5201c600040328801030420100a4003845c000080483c41d42c11589000810104110720500403000b104064445245220162846a488680c515069015400a4038582c402c0c02c00d403c1d000d10203200c400c1c65400c507800460b007039114410840c1408407080c641d41d810141c126000e1010345803040704015011005881c04100404041c4802c11b5a5a4041a03c51a820001c2d003151a214540041400b41070190303513190101e40b00d0b0428016107403041d407556111482000003491a4014218112115481507040ea401d0301401e10004542c505050b143c004800c600343e40104040c20503004040c211440508920b2007680003040401c101503071340000c0703011680c0850f080781e210000e03680d185015180d10072810030040c1c0c002500204054210024042c0c0300300c3c45400700101d0110a14000485c841800341007420302084105050000262500b4841500d20881060802c2d50305d07040103103960444040345003c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 912587571 1250 912586321 912586327
    0xa0305031b070f0303020f28020d06022106181b07080f0a120f2304020a050d050303010816210606030c420c03020a1509050f010c050f07050a0215 64
    0x11075041000703442304480b205c00219040c0d0414800070030b01c4140814000740200418021642404866030640c1d840c0540e56200b007080c1000c0805007241d941d01111054441c65001e15444901088107481600c12241c0009800d0081d10031544d141c440c2c0c210010440b605002088213141d986c1c0038001806104a03103881e494081c0310b003140c01c101510300e1001e4503001d4500d01580e006520500116001000aa0a56001c096140c500104a20f9041030304140d4100003891402e4041100000086048900c800180c5d1117500760410902e0501356180f18440720803122007480e00046090540342d1001038411100000c920b552a0303903d402c5451940d00c000032800e41d60f0360400041060705800a0454250045403824817902030480c814410744a80ca00304102c5071100311800c050082051400e06078210f58140401070910705100c02515007108215524041d40403a14000d502c140564140d0a400751100703800c02c0c0d03080310700c01c450741c000c00b1041d0703007a104444110340580c0760409485614034000b50383d556 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 912588821 1250 912587571 912587593
    0x3030504060f0f020705012106030503041818020909010e0d030203061918051803031906080105090c1002191103060106050301060c06182307050a0305031b070f030302 73
    0x442000c2c01e50a09080c880b1038502c1003809903010540324103960003420200c4069104104d50200c0f12250b0004110152030501c022040c040c002000d8011036401100e00d0a10b40d44000c41c8000740c0320056402c1038034031048020f800c010302d081d68003198010b00c04000000c01d5120b005642d450650280d91000c040781e40001841114207103110480a003c402007003403c1541d1515040344001502c50701d816041a40e01c00102c0c000b01ca04070752514000d1100c6048a4030b03803d212804c0782c0286484541c80700784e1032410100094000c010700910b1300c1280544007400a441c200c1050000301c1ca04220003100314082c101c0720340840c2c4200310b10800d084d40030307040300b141c0400d00700c0a040c80c2030b00c113802035024000d050004000b0b00d50f0282c420007610758800d00c0842c2c0754a210b660b0315003100d10340d040108500d02403901d00003081506142030b141042924103c50302c0c29501c03024014294194000034003150001c02404030014074000c1c01c031010ba5464802c48080b00d544002c0d031207940c2040d0704100d0041c1c21000c42c40d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 912589928 1107 912588821 912588827
    0x130507030507030c05011704081803070518011d060904033509060a0c1b050705060c160801231320041103130224040303050406 56
    0x19140c02d9280c2c0f9102100d0002c0d40641ca0000b180c45158540b000b8007100003a001d290000304444c17030883c04408060046001e003031441d405100302c510000300b58481111407036200a00b01e064002550404200b81e808121030403c8407900e071410010302c901c0c0d5803402c480540217607060611000d68200d220f05c4500421103040b5505c11900e41c00050410384000300c83c00f5214402e0b203000d81c0c40d281d03290b032007038011200c01c04800000640c80300794245002419460280c180d41c084c1303040b100d80139500c500040316a444071130908210b420480307600b051300781030301d2000024140785c6000340081d150020603200702d05100b9078a20300300319410001c40d02056003c400c820310701da0011442868190102c882e613200320408041030740a01c1c80d1020504d582140394003581d01841c0c10000004404c000b40d0200245080380b146180300038a241d1000d4150f0741000c20003030004522035250180c89920303101010b = true := by decide +kernel

theorem cover : BRFrame.Cov 912410071 912589928 := by
  have h0 := BRFrame.cov_init 912410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 912410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 912410071 ≤ n) (h2 : n < 912589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
