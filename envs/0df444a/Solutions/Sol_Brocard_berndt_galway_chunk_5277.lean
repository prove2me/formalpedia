-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:20:09.774253+00:00
-- url     : https://prove2.me/submissions/ee43c3c8-fd05-42af-b803-00acd2e43132

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948920863 ≤ n < 949100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948922113 1250 948920863 948920873
    0x1614010219030f0908030d0c270909140d120b03070503030702060c030903060a06050316120f0311030d0b0405010e07080705280509010f111b06130f06020c010c 70
    0x3070020380e850f1401d40039401c8851001d8130070401c2900901514131020424030724402c2e46038815058001c654039680030200c0c0d20b0220b01c0d40f5140c1e0742c1c4009120400da82c2c00700b18405079a080215150710030314401c11801d008406081c0740c0110607140800040e104000d010031554184203e10041d01c1c1640a400c902d030400001c00d980f0300c18140c0c024020080095040c1346680d0a000303940741410020251902814039640d2500949482d020b014840d00400d1010780a003501c4003600390840700c0f03481c00f502d4000410740315024122034081c401d070140100100c68140c504001d10082680c40c09101c000110349450009200c00c554050700911b004807122810306c500150401181c80d03203c040c82c50620307605c2c11000c41656805020350103d50403c180c0d18150561150040c010b00300413502aa14111580022142140d4030121070301e031464280c100a407600b28000c00744540000c941800781100345414400d0003400d8140515034400320440401080034032040764180702b1416141e10910b040c2c0741840d215214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948923363 1250 948922113 948922153
    0x80411060c1209060403060c05040305070e0114040c030e0601061805040b0315040f0507030f1104061404092a0806070804020f040c36060908070b0a1116140102 70
    0x602009000402c1c07041c82d982e00c4808403409154449000d21040c010508d001d4030982113070008444501840d14049016005075824504079081780c0140070115465405220003003c542005030b04040c0c654601c0341e0384032802c006440c000c04540c0d031040c1480c40c0382103070308080c0380e01c035005039202d242090310450195030001114061001108100d603842e4582e850481d0b0704c0c101882004102d4000d902c800018420130800100040e4010b01e0100f90001da0842080308650321070044a02c4550080451300c0c1c2ca04160703101218061003844007915034000312050442c0f02d0188032205500d40d82c900018004140c062110540000c220706243d4802c1c00c15600140a000c0399909013400707141e96140030307480700d4400c2800c03022100442101c0758422085090100b860702001350150104464044000303001c522840316103007250007800c040e0070030314200702c1c0309840c60384001500410000a00c101c5200c281c0e050224106c1d500c0c62803a00041c86142104c001d01550110354802d0540d0040b51a40da41a190300300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948924613 1250 948923363 948923383
    0x12020f16080f070f062f0a021e01021e0721020f03120301141503070f0207120c0e09030408100204030b070e0f010c06020d0c020120030709140f10080411060c 69
    0x8001b4199074144030000760101441031000650f8180408585400fa401f10b441d5100c14000d1720204014480c101c40910040c40081c0480c0c01070348807160020100d40c00080c548248042141a603030f0312a0349070a00100c110710810350540080e03040c40364000310b117452002e9038180030069000e44401e004075200c0c0446800144600301c0f018941500c0090a07903540d19507141d1010140c040d01c0e0700e905280c0c1c4014035503959188000054414840080340c0c3d050f001c0300c0c03000303480d9001c032050003a00d013440603c3c0202031025100114912041c00082142c500902582c9011107543c40e00584691941c240041500c2000d8000c2052210007a0b407240551140d1030181c0d1092800c0c00c1c2040e60003003e160140007440350300c4104052a141210031580c1e030b0b9040d0002144403602c1801d00d100c00b0312071030411009200c155000b0000c200103560401059080741e2402c4d02c00d0720000c2105e21046014801f041402d000750441c2c400141c0b06030104410010400700f07458100d90240d5003141401c5a9030b01c41540e81d070f4100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948925863 1250 948924613 948924617
    0x41511010c1b080a12020403080c01060e0108030a180b04030b040c050114090103230c0403030e10050427050c0a03051023040912020705090a05060d12020f16080f070f06 74
    0x28000c03042d41d000d464203101701e03411840c0443d55190b80341002000d0b900128407400c002d50030020001110410555418145d4039100c020754034208400b40255001e144011827200c0019a07440005105000103000d08003d602690101c916441c051600c00008000350b0055414460005e02030a5106408000d0300d80e03913034082c00c0004010b0124880048a035900c0405c03400981c0f141400c01c11010740c00300203401140d100752a80403420005504210700c02c00d2072150040002d205020030440d5000d04241340b00f031601036417001c45c04030104032008010780b80210350100e4640000640c100c81035a0510502c0d03400800048148141428403400c00d01c0881045500040350200030002c41840d51194810f4060a5004041c40309106003514041d444134400d1040e284541d444000080034003940340a00352040700000c20b460800307103a5070340780f400c048032000961086102d00045035007162010000300212a4400c106000c40f9843d10880616103c205031011090f41c0180b07004104aa04520040041d56064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948927113 1250 948925863 948925867
    0xb150706150e1e041a01081f060b030a050403050c1902010e091603150504060f0806010e040f0b040f140604150621020d02030706080109110306031e03041511010c1b08 73
    0x50403c026048003068421409821000c0001401c1900040343c410105036181c4400002d14423002c079400320741c424855078030404400c0000a454940700d5001e10380c0140310741401c41c00c0100301c400ca01d01d0701020147c1701071010007001002043d9a00b21181411840d02107501000e185420482450030441c895a00d4060580310300e9483d559503100c554100103400d003d041000380305d03940d180110300c80000c0e10900400780075032800071900c012100042c03449540c000300b0a40b410b03080c550710312029810050003502d4007220380450070006008001110130340484d240040000d0b003010b04014540000140d00d05001518050041019020030000c64001c10001e0090340c0e2104050300125a11078803d280095043c041c500011520703d4004409138180c0f40e10f24020080c010401041c02d901e44000c0d5a5a41d00d40d03c10705401c0100740185211149003100002541d003025900e41c29041a490f5051015012450045007542504801d2140c42c039901e105140640d1044880c107121f210b101c05189011b4406000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948928363 1250 948927113 948927121
    0x50f040305190905031911010f020d05070807020d23010507020706030e070f0f170c06030621191406040b0f0a290f04060305100b150706150e1e 63
    0x1820098014000902a100522500004200800c2d030141b011101115260405507480d4443c038005641e408a0f0303001403a0b8a14800d9080c1c5003500100b4040300c1c1c001c4c0030015400142c0700e07080249a15403280e100c00580c0c54040c0c07028032141001180c3d1440756031606040080056000030010300f12110390400190130a030664400e41059038680000c01e04c2001824005004040310000c841211040b1440180804000c914180c4a910500c1c01d5a8098003d001107032461402c80102e000700001e130000d00d4591540c1d4400e45003000540003603c83c40e000c4000c02642800110a040040746140e20058181442c0c20ba031054848203003d480d813524000200e00040d4689500d603c811404804980407540c40c444500680d102c000b52181c0d2140141d5194040b0768403030415000e0081625404809000b200001e1010030f0002d1004200c8aa0301c000300100f0f01140030000001421003e00881d8045034440c5a400004003840c410781c05054241c94200030000600c03e40c0405140c8280708214421403511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948929613 1250 948928363 948928367
    0x10f06081c41030106091a1c0f0c0201021c02040f0b030c0708030f10060804050c0907031509021209031305040902060909151203040e18150a0906050f04030519 70
    0x2020b481045144007420501040c52056980514100c03500c90740d4401d00740e074654000511004e1079131400c02c0c0030101440a0501622038044011038001c000e48002038843c0300fa8000426145c403030039100090303540014801e200941c1c00a081e030300b0080d4100103510307091601006103c1040c0b85e10456000110200c00303d0b6504200c141224610b171380040703440f03889062001019800107420340310072150180300c0b0b800240090048544e0b034030880d00100580075021280d01801400c130f800030007100c02c16688820300d90005038010400c201030003420b24016100c0003114220704d803440f0041c0585007168030074803840c8858000380c1000d1058403400d56010405801b00c1c404a0341c14001c03402500e81c080c84070b1041000d951000b96840e03003000821035200d100c0e101c8000e980381c0c82e841503000b01c1c030b02c0303c080c1c07000142824000d242010074800304d00d00310303142280307035601c0d1856682c801d480d01030149480c1d500312410f1007a98000c85400061146500040f4203256902404a1080c0c4e045d0307883c101501c030800f9115074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948930863 1250 948929613 948929687
    0x31c1e2c1f0b09010b04080607030e0a031d0a0b0c16050312090103090b010801020a140a0e09090a06060b07140102030c1c1401080a02090a0c050405061b010f06081c 72
    0x1001c05000f0440c02d503100c00c04105a908940514501e40c403030000091115803003401244107003948400a441305402c9614206c3d9402c4410704001402401c60325100d60076111034a1520091004e814100e440b444400d5059013451200c007400c1da4a4403000009014555006c44d80e61482070042420325507840003140183c002d419130a2000c0c001000d5900009200c0006400418000086030f0710340f81c6588104101030847d000da10701040000b500c21030802c095060040e0129040040c2c01d0442d4841c070720590300d600980b4415045829010341c00f081c48005c01000d0b9040740300c480701020083d821494481224060340c00390403044000048455002000514190f114002c10300102c1c2000e00c0341e68403a14401d81d2035519200881c06003400c1400110401e410b03106ea02d00b0394200b0307902c085c50240b801c020072426402022a901c0c02c2c1035401c1d01c4043d902070034071466403082e900482c0821114a000300242c284444240b10310f80300038080c0411444c00780d0001c000c1041416420310f0407440850810070190b86 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948932113 1250 948930863 948930881
    0x90f06070f0e0d113d030e0703060c020f011a090c0c0703200301060b03040201030221040b101d0606130305011503050d09030302031c1e2c1f 62
    0x300075408104420b204e1004e540e104001d00c103550054040794804100540120096400411100c0c1e403d810416025010740050348000c2c40d141c0030484050b161080c1e400c046041c0d02c1201c8541d81e4030705615066070140302d244519030181008224502021011000e609a00784030b9903c02d1081d42d00098003681c015040e82c040003401d030202c0302010703100d140000c54590441880d5000507180718540980c1d107014040d400643d080000c000c1c3c00d44e111940190080e40202c100b03a010304211002c03081f041da041800e0300d0712a601613007401c0c040341400480c403c4c0509064201e00c107410317965400c000c06880e002c15840d820070800da48040d541c2c00d42d4021050b0300c51390758100500715400c01102d20202c0010f00d0200050340c4c0510199143c0b09139000c0c0558040c1c007223210040260704280040c12f09400b102d100c0070b68814103054082103076452040e00c0c1d0201c1c49200040c0310310507500d07441d00e442407000d00c9414811041c114281000101e090302079603034601d00c0107235144605410003880030303030710106401c84080c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948933363 1250 948932113 948932119
    0x1803120301140d210306050a061b08070f05060402040b0603042019140f060a020709020304020a180c02010606230c0705030a08040303120504080403062003070201090308090f06070f0e 80
    0x13095501c030310000504100e0425a4001a003406000715041c50000300e00c20464140e600c420641400b4030124151450400c2001d842c41700c418000500071400e520301d000d040c0d81c82100582101c1c0340a2041104991078402c446016000c18010000010300c2d8440010381040802c0399807007440044800a03403002140e524000881660305000104000205604101d01c03804880d071000d441040300034003080e070003038111480050f03100e00b404002c10110341e401184c005001070011804580c80e81803080c0a01e40c03508100308216940c01c20340400303035420701c11344010b41403e281643c1c0c0f0200150351508402c281074401e9818081c0001c00d2120480200614401010060180c1c0c80c4141642002d010135003092001350046811ba402a2101c58000d00c07501e03100d0b03540000390a090a0a40e21008010001c1601d65041c01c42c0700b00e1010050800b64001d90302c5803441d07070b002003011400391034001c050003009880b1405030351152041191440d0046184d6502002d42d00c2e020b00d2904c04124200c2e8541510726101e50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948934613 1250 948933363 948933383
    0xf150c0901050c1e0708152502160311130509030906161205070c06030c14090d020d0b0a15081005091e103213171803120301140d 57
    0x40100350114020b000c075040101950601101e1840145501e801200c019030000b4904000c0c2d01190700c8c2c3c0c0310300d440c43c244510454808500d48550303c0c040c08040e803c295800021041129028907145405e150044c150001c280924104155120307035070301601e90002d2040340c01140e0311280d99400c41003d011284c1001c0d031a0316402a017100940301c2d84c800d9000b6500503c50340004140341d0702070f01592410410301c0e51010920100e4a8002400e6000029410751010040180401613650303482e20500c05401648450ba10741882440001280c0c811060000074407010f50041148007004185175058042c8010b0115150380e0300d1000c1403d009641520f403400b000e40c00c200c2d502c04200002c1192402c0c100c01c10810401c40140d2062044409054403000e0180311a0340d12025220b15101941c1c12400010852031000e0890344d41c4900c4035100d141810760801c02040000803050340d098580b103100400d8001e008101c0103009048410301c41400f030115520301211449648d921100c0b800c01445421000c498 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948935863 1250 948934613 948934663
    0x30f0e0a03060506040b100f0e121b28091814010221040506180304180209090606040501080a050903280e0f0d06180807050f150c0901050c 61
    0x10b0020a07054510030301492421030b4000036400c10001036201c000d038035215022102900c2e081100c5032503200801907040800300582c524034640401403c2e248400201c070095107108070340203114250f4680f001200c003501e21420f16040e55031010f14880306881516002050b0a039074144131241060300308d039005251341000b60700076404060644c0070b08288081c801d061490000070090306005e83c1020b8401421759082400400c001201000510700d0f4416820107072828241e4a0144403403482c091004941d5860300059a40114a031051009500c448100d4085003130500700b00008010010092000d00c2071940e0354003160010300104141c07035a01301c0c005031420140f0300080585074903044824104011410100d10080e1f51314249120100202020300408004c03c4284c4608014008110003481d44400c01004070020030450b1008241d07403400380740103100095031700e81c0396468400781c1403c1d4000401283c00740004841c0300021601c0949003480e00076219401c40d42d4150130b2210100110800318101e41e114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948937113 1250 948935863 948935873
    0x905060f011d07080c0a021c02030d1104061e05040503030d060801050603010902060a051806040603020423010f260406151707061412010f0504110a020a030f0e0a03 72
    0x818161621071a030303602c1c400c21100e0691001d0714290307407460106100c000003c410540010180111016a104071201c81a070040b10301d00807040280d0540040c1c1000601e509000b15038060f41080203c0003103100d18040c940200248201c40c145883c016072050803c60000d400d21490a9501901d0014289c0e6602c41e100c40303c0d00010310182c40380340055420f000029140c2e140600c601540c56801505051030603c0c05101200c1d207a0040c20403182c20440680380e10703d681c8132640070300301a29141d240103079281d04041700c03c0c903a518001c20015400b017031040800000d0740e01011034900540e842c20201d8400c01c1c240460910b803500401e081005602079003c001c1400010707080400104c080880f100c01c80c1341c86040c401001c1c2003078070304595141e1200b4410411203114643d080c21003081142d5a82c14448144c105c42001d078800e9000c003004c6483c8207414001450940b1440140b082e00b070f804030380341c482c100301c5c060744806a681004e401d21944211384686e550003054691380f00710000f042c0064840d2a4500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948938363 1250 948937113 948937141
    0xc03040902161a0f061309080c1020040501050f04090504050d14070c0b090d050f010213150c150e160f0515190e062d0a05091201090506 60
    0x207943c01d03141c000c0e00241070746640101900401262610300300707036554042407041104411302520303d210359030941d040c04605140c0183c0f60904816001d003658851498a92050301c03a002644400c1c4100100b00c0204075503000110b0303040310020b00303146403101c1d1942c00e4804603000310340c0050003590501081008100011507002101d504a45400486031094030b8070b54900d0040002c000c3c00800c50348010311044c0441c2029140303045000700b1071800e013443ca540300c0d41403c20308003400c00c1e5a0b4000c25a4161401800100380182400b200185100c80f10a14001d04030140324401902c2001100c4085024204503000303000c1500c1075200700d07141080202c02045e840d00e0a84640380c1c1c041d0346120003003403074509921074007491030518072510704044c9042c91400c81085400080801d02c210b0368250401e03910390703d015096801c0425210394a012252155800c50030560704044040001003007131021790b0740c000e82681c0341c034034040d141501c0401112001e00e004101d08280035000344202d2041011910100070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948939613 1250 948938363 948938407
    0xe0112050f0406111603030e030d18050d0503060f040b1f09081005040f0336031a040c3506060111070b04030305030a091502030105120f0c060c03040902 67
    0x10049464414410f9205004401c2502d440c3d0840030175000100b8480d0300903441604031003041d0381c5402048003106d01214000c0b40c1a1190b543c0e442ca85005100007400560118055800d25600d1442c001e40080c50300118080068130803595000c0034410341c0c8814060082c6003041c0807802c85000611000607020740030782e2060000610440020f241000d11900a1a000303640c014002c1060541d5942c0903a090210007810040c2d400741c02c45401c88036003d00d0308007460254544003840303469045052110105241040030001d200d2501e0078040000c940c1c11600c800c0310382c1c0300308103009072007280d50b91601403510744404400841b458030450342c00500400d0080c0248000d0721102d070342144500e8050703120515440f540d051000240701c200301084c029801154840c1d90384c4000102c2c01c0031a654598106285031160841a038040011701503410080c038400f900c1600c94005000740507100741d540d5620a25045070328010301d408201940340f82c3c1c00300192000f80c421240e003551510840400601c030880340e85 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948940863 1250 948939613 948939623
    0xd11041119020106030b0402040c050c06010b0406140901230d020f181c060f0b031e01050c1216172d010b1806090a0f0e0c0a09060e0112050f04 63
    0x7008000c400c9005100b03020499600c0004981c0c19610768003008010280b07003c80307a080c003000700240400001d0621030b0318081d00900807205d0f102c5045c103000402094840748141094282042440305a03a0800e00d008204207102244108240b070b0460360303041c00e0207545ca81d0000c403800802c51002d00c65002d0302a1200d04d5110b4a04031580c1161400c00c050290039012050703a1105100c00e64001c110143c2240010455000c0702186000b07401d0301103450181d81c5c0c080100d520710368403084410103001380115500b24106140243c10324076000902500000041d00801e1200542c518001c103031801395411580303001505443e0241450103111607101c50121158000200b1021071201583c0c0c161548410b050f10015800030342011100c002078400d241d06038600507800082842001100e0307407801703c040064002c802c80300b1170b0390b1310342003049001e0344000d026041c1445003400340300c0600381e0050080040b51954549403030a43c11030710040c0d5038603e45404154440703050a00b04141140e03018016801503101d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948942113 1250 948940863 948940897
    0x1050601030207080f0d090c030f0b070206060102100f090f0506010326030103060504051e1e0c0904020913051506090709051e04060e011e080d0503060d110411 70
    0x114100c0c403c000d0010074280041c0201021900110060301c22803420007800141c01080380c590644a11a5500032184028480748590400100d101ca194010140740014085411b2860010392a07140340151050311faa07036503003e40c59260726a0080c500142e0002d07060303c03150740641006603c92009010540e14050b8865a4400d580010030001d000d061030195007600316400c540e10807014000141003036600e80f040013404200803885116181007040c43d4802044206007001140c43d22110f200c0c402c8219400900c11605191600e19585602c0f44e41214503909541c0d03100441031603613000060251003031040200080c42e80300340740e28007401100101e548070029690fa18080700c803105107016258000c0740496a681d200b6003940f104001a0200034404030350035468412041c0b0003c0c090b401800c402d05840c005000401106000002a00920019055000b003d00e8003400c1ba202c05030005001c0e4251100c800d05110100360b69180d03119009006200f026842c00e1010300799085841c1100ea0400301d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948943363 1250 948942113 948942121
    0xe0a140705120c0d140a0b10050309030414130908040303413906040c1e15020d030b0307030302060609250f02010c05030903180609130603050105 64
    0xe1020344900181d45035111600c0d0f03554820500650b0070034500d99131001d4880340070040f0f5110302c0c82114030500c407a10000419034013101c00c102c0c0b16009803001c1d800303010301001409400c0501104580a0300c072012055030007442d509010440620781081d5010030300d8500590b050807c2925001041200e0181c4d940c0c102e41408161844130454001c0100c410742c0340e0b116501000600c04030458a091070482d0074550800743c600c1d01307550038562411040c840002465110740010304881484040c1800140020a000e103030950b201200e1040343c0c00b50b0301d41c103215072629059020b1030803440000f8200349a120200d4071050176010350390703c111a030390502083c00c3c840c6030300060034002902c40481380c05a0007082181c9401d4288151000b01802d500740280001c501d200454803c80d800e052000100c1e0741d041780310741e0103c1d0001d0855040b02644401c10504000780200200004180c030448086114039005a10700140043c1c0e90344504010142c21004185201004004e5603101c0000c403800740c8024401276039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948944613 1250 948943363 948943367
    0x2040602100b100f0905120606030f0a030c030c0c0f0305030315040b03191a1303080a0b010801032411130906080706120905012a09050604120c0e0a1407 67
    0x42d0701802c050300280c03a0b4181002080c0304031415810208a41003007075405483c0c070007240b52074401c110b6940681d8084020b00030a4201040080ca01403503c1e0301030b007042c7c1d6480c0c0d4001c2140c503400c100a01000117074006107040c00819044d6400602503103c0300301c07183e50703603141c02c903102c0d00100e031074040c4100b0f03c542c1c4802505090060100026001b00174290a6503c50f20300120100c0c55082540c450482196000700d00240f90a564001c004003032070800d0050062800510b0303180d0050030300180340c1c1445441040c1c0d0342c00c00c0860381501d5000c41102a4400e29441c52107490743d041c0032014401e81042001035402260100070103541904068240c12141c45d2240700081d84c11500c44c101d220341c0000030400c070b0a4803c100c18400b181c1c090a01207540289600c8041c02e459008000c0c0b8404018000c045000200c03010f10000e40300345c28100403103450320301b00000b04207005078402d928086d2141c0b0840000c000411800401800300000c40205a003086070021005002c1c0000c507030b015040c2200410749a41c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948945863 1250 948944613 948944621
    0x1b091909030c260d18080406030204030c12020907030c0201020c060a06080d090e150a08150f0a0903020616030e1b03011104082d0102070b0a0b06040e040602070c0302060d0204060210 80
    0x30303045080007480d1416032007484e0014840804d07500b00c0400d203140030b0b00000f1240c0000b00000c00c0c8655000d0303140c40c1503040440c5080c003140e0010350001c022044040040c0c4604400175400b10b050f00700000c8002104809a000e4420703807207004810b00500c810041400015801001941c10b000100e0300c604038070b4801525595000d0003044141c2c0404400103181074800040c4000884003d480094210ba881c50640d00c1d003082604d100c07051400344000c1142007042603004941c0001c0e030b20000e11401c101c0d40c4000c1d440f1103000e0b08140c40b10029450311402103010f134220103c1a800601201c91a0b00700c00442d03040f00007000c03801440f035400c0110700694100400c0c2518161126103003d0403942103402800e4002e00c440c1958450121118040d145c1e40d0b020030310180c040300c1c0c0904072158540c40c010b503007130044400e401105845298240002e2248504841e0001d91040c1c2c0a500140c0d220058240a00c407569254402540107200048600060100c1d8000c1e004507491902286d08805190310070200365 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948947113 1250 948945863 948945923
    0x5040b01090e0615071a130206120c090d0602030a050901050103020a0e061504090234030309110a03080d06080d05070f062403020901081b091909030c 66
    0x1a071410402c0c42160030581c802908004010481001180c0c100d16400d4250001e174030980e9480040e00940c0001c02c600c3c524603600000500d51034140c905c0703960000d41d00e80103110002c0405d4540070001191070341c502c0201e480c09040103040e45860410340c581200071707600c210307101c000c00c9007850041080b1450502400d4180d9600400c103502c168200000c46100210050403217601425540203060841c0701940204050301c03407580056515244c8211030300c014005c03400b07214444001600380c0040c0211b00f80511403e9681490003041044150800040e003a0000845c031741d00c058270000c00000c000083c0d000b00031140840c041400080e5664000c00d4555100c0d074074500215404100b40b00019010b007602001140c4130ba0000258402503210128040b05210503001400c613107010701340194034080740405e005020100003004600d03407140d034204d03803901c054107080c1c081c2d400f01001c25041d1900c1400c0d80714440040b501040702d85401d040040c4140c403040d0040e102c20344103820451100100d51860094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948948363 1250 948947113 948947117
    0xa05100207060f3c0903030516020f060c210f01030212010501080d211401061202091003021606050721051608071b120e01080112060f0b12070f05040b01 67
    0x801c40e0481140c0780c01c15007082e426000c14134120a044604041e88500c181c214000c2c0c0c2e000650f4074082c94501504000403d100056600404440e944c0b0782c00014450b40c00410904216103c0050011182c840c0c4104159008603034003520400130007616010202e0b049034021242940e102c001c4000b05030881e5028000c0507041e8009601041446000b142070301d244204940580c00c0350403440528004803039010a404140e00180f100420216030300ca0510580e0300b248690447c81d200c4100300144c80c180101d0301a800b81600481c1a104c0c5182d492075019219421420601181c90075642c0203000b00071449141041040b940901b11004c0e805228007032080c40342442e00d0381007404003a030940e0301c500c004060b9801c204468024800b803400c9900c00e6030b5601d200b540c0c5003d80c03420248014040114440364141001a000010048851404100c514540d0001c1c2e0015454070000c880e400600000e6040a0f040b215640e40c044200e04001980c0c0100c4003004001a00b95403101c0402095a482d41a40c0340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948949613 1250 948948363 948948401
    0x50105180a0902060403240c020c0102070e04020a0e0c0405041505030c0f060f040b0c0c0405091507182304062603160b10080607050403030806030a05100207060f 71
    0x811280590140340030310300081a980c01c2946c0d0740d49244944100302061145804000c641d840d1200d96400780c0c07500c0c0d21460014040e1b007102c00d0b00003590b60010b80300719888154400003040079902d5a10a030809001e051076259114504159881c00c690b0140c49401d008902c0d192040e00c00c106044415815a42c0044c0549507105c0030390100400c6041a489169100c2001c00c16100744644c0040240b009150100314180c644001814450a2060b4110440d0146050030308024580c0b0001ca4402112001d003200f910700f40d11451011101410034892030355003003002c0500460003004181c0f00c014568909683c1241c0c94800d0810301c03090302c3d402d20842d8030480e40320000e48a01080e00c001006540b0f82141120704100d050040c51016100130301d4240e803088056010f000c8803181c54004a805440440014081030400c00c000070114451403001604105061780480d4441d40c0911651303e441e504030040300c1c04000500d40120013548401c2c4100e032040d140101c640d00c121010b0140920400300c41500d96 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948950863 1250 948949613 948949621
    0x31805010311031f050907030606140c03030c0a020a021c050f0f060c07030509040207030503040b010608163e0c01110d050a0c0c140103180f060e07030204020f0d05010518 75
    0x44e60364a2038802900a110010001290079124000300c10b1081d0066940401e42c0c6140c518040d211078022204410066001c000010003404d0000c11a0340000c1501707440c1b652581102c0c0d0490400b400500025403200040c200113a4060040322541a00e5000318242c6244c200313000060399030380c20310324814220b607040980058000c03500f0308050074500c1c2c06820700d940703840e40d968002070881c2e111100c12008100040b040c8030034045ca0402241c054001da050000300c42c18130000c02c4072000c0c82039007000d0800c400304648140b044034502c2c0502d803113050752010412034000c015050320f40c034096071250700381c510500301081915845003020119905071107010b05080004101c04a035a940020859810701c800c01c40f045d000100c40612140080503141c0010341c58044800004040d034030703405109000c1030072032200a8080740383d1900410203d54440d40c0050388111900f41d5a0402da82c0c0c1e440651b010b8400f203071071601e0784505c1d030050114112001c02001140e0307d400c10044960020824500302c20b02c1c01d0001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948952113 1250 948950863 948950881
    0x14070b010e07110316050d050301060503061504050916030b10050910030e0f0a0201020d0305011809111201060e090d0212090432010902041811070f03180501031103 72
    0x241c01514034030b480316420f04106600e0385503074050284075004045510a5000b440000d010100c03504400f403416034030350f500d4084014414040588401c1c414607200c884510103050040c101c900030880034103c02c0309880c146440624120b4250541000f003814808218514500f5110015120300103442d01030a1048400500070390078804070300401819a2040c1d80c2e035145804006100000c2c0d81c900040c4181129407000a082400244c01c04c0e081c54200740060080004000400c0103039412418001201000350030004000400401c0c2070f600206864101c41c400d00040d00542e00740d4030350707922803d80d540340d800381c803683c45900b0201c00d40160029038490a07803645880003040140703802803012501e80c403030724107440110703800040300e0001001c1d9180160201c0d0360111010b004140c1c11f00218141854642c9502d803d000351900e244202d41e0701c1500c1d102100d0300e1800d489140381c1240000c410700d4001d24001c1c0810110341000955586a03035000902e40d0f10a00403403002100e40c00c011401c6803103080302 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948953363 1250 948952113 948952139
    0x6050a1a07290103051510060c05070f1d060901030b040f1119150e2202042607090509150403050903010e0c0f1c0f03110d03020a14070b01 61
    0x4480d500600b5603219280c4400702d1840c90b220714502c4004002d5459442d019150680d060746c1c017001c0c6207403c0c00b08401c104c04518118100e84c141c3c28000b03206140c0380380042c181403a80e0400d49105420110100340c1c1400e801d10f4200d002c01c0d0aa500d041621020100483c42009100040850000310b0010340010210700004030700c14443c1d008001c10140c1c01d0001440c02600b05460403803482100ba080181c0409001d0a80d008517490406043e209802c0c400300d01150712180300000ca00a420fa0310341c8842c485c0390f04a600400c0741d14003d030403403180c0340000700300420b204a070f20040b4480c9200118001c200351288500072450500100340e1071030301e0307005100318290007071050b001e000c000d20080925440a00401800305143c5014091026014042000760440340c046030303002d583c00741403807420000b01c0717031b016090b403600314401d42c0e4500040c5c44c0896074021215100911806065161403e254064026042d0781800d0746514a800c11103407000ca01902a428006e8451002000100102010014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948954613 1250 948953363 948953377
    0x4020103230a1b08150603090c04020c01020c37020103020c030a123b12040f050f040b03191103030a08040c0f03051c0302070b01080105070306050a1a 66
    0xa01d00700445061482001064100c0e6801c40345a01c2d1601d00100e074070040300000854500b41401c24050405030028081815800491406440d00201007000400c04003c80000850000d00555540c00c4500e040c83c007070b400498108901d4440ca6040900e00c6010854a40019a120200d82c103019005404052101c800c900260305140d400c111f03120041400340000d142004545c1c85190b020381c9a60711003401c403150030142c90700245460182071250241c04409a00701103880c0081150340c680c030850941010b901d4520210034410000d40080c001407044c181400b240c00445220b5000400c4100341302c03d40e10041229035140d00400c0114846c03038000c980403800c03940142e03d00000e05000c000481d285902103a4000007052b4030400b007000b0418030200d590050030056441c036801c40d1859440a070340d80fa1a0b05401c2c101420041e507401828444e5042e602140e07007100041825580d00c0320300900a06c019143c100c002410440f01064504169014000705c404004140400500c1025100010b0700114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948955863 1250 948954613 948954641
    0x3100e0a060f02042c01090e0c012006070f022109040903120509070515190c1a1501020105090d050901030c051215120106051c060207050601150905010e030604020103 73
    0x3c080445c0e40540084850142a08110b0507041503002d43e034201c000d10f00580c8104015800d240d4002480700004c2002450000e082c2049440826003590020500f48844071182040c401c550030881c000c1d6020b03c0070060001356809651090140d0451104030301c4024642d00481d02081105645c42d0070650312081c40640240b038030301801c12032110414151203085d1030000c1c0c1d03580402e6043c85a4074022800300c100c2c4505031041c1e071500040d508850581c2030981c0140b000c0c8101e681c0c0031007d118501040c8000101102c9000c0301d0b0340741170001030002c0d1060115040c01507180000050317080600080500210f00710b41c0700d1134100001e4000440140c4145c8121004200b42030040c081c8008000f206c50740a1858641c51075505081101400000001040c1341d00c0c82d070b03050460400080c0c0b1000c94400c3c4a52000c40780103240075460910a010384141e14008100f4070451000045200c1d0300d600c0c4100200f080d580701c441440d51780d8011220180031013142039042d0040c6000c41c0c01036000e0760044244a00704 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948957113 1250 948955863 948955867
    0x2150a030f05040c230901171c030516081009020306060403020a120201030b010503010b0403201906080108070f1518030302010603020a0e1e0604061a0903100e0a060f02 74
    0x1c003214400340d8400b91001c90740e040302d52906000104504104507050b6811405000204000c0d600040d2504018031034941c0140c0c1854901100b00d0060141108200400c0001030400185070030013801884101e0740101c00103034520f10103e03224815004540a00103407001ca00c0c649080070368200095001511035079100034204400001601c5403203155000b08580c512000250b40b042c00050700786e4845203407450410400300010b100c030480c04001d4a0599400c51400200002d1484100640080c00c0e21440e60003502c44a01d003410030399480454081c0c55090344d880f8403c0e6640c44c015030391080c0300d01407501c0a00c01c1403401d018481c1201c0301c506080741c8d11700d0b0050003009440480014100283c0007a40140d44491062040d400d00b9560840142036140d60304a003441e017801e034501ca03407030b4145503080300f441001d000c9407461351103411000240001103c1c10322221070140e0f03042e010398810644107000c0d01074801411140e441511a82804000c0e480140a10741540d5032240000d00319405011074050382 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948958363 1250 948957113 948957131
    0x181608060f120c100206090c1903030c03030b311e0b0d0209090f010b03030f0304030302070f140706080c07020306010b070305070b0f0411040b01140702130c0201050403170402150a03 80
    0x462101070340140341500503001c641000c451903820040401c8d0894003800c0c0c00648007045450200e441c030102c80d094074041220f80c03600d10f03084002c1d1000d40012940040d6000c200810181c8031038200011140009005400200c540d444000342c401010b880e041c604200700c40c820f81410b4507004410b00759001003030b230200c0b018680c0c0005c02c941030a41e4269003561241560a24000003480b9039030071320404600031400c00850080b144140c1c4030080c0300408064000c00c0800400107520b0111b08040d901003030700024151242c043c1c81c1d94410620910001038030f1500481c0c5005410400c4942d80da401034080c044503070370500540c03402d0340400812410000208455800308032030303500d098040c03554402c8030742c0305d41043e0800e1001c02421040c00b92141b464890258642c0c1e0b001207440503944207a031100c544038551030002410114040684490144c04c01501d00c085513810740c001c922480c400c0d200c840c0a807518030b0004500c01c0040300c009400103801c450002d41201041c1c00344c01100c015160100340040c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948959613 1250 948958363 948958369
    0x4080c190c3614010f030b070509031f020901230703200a060c0e04020a09180e03040e1b191d19051e090a02070302010605181608060f120c 61
    0x3001802c488201e96070b07951403010612103000704900400e40748141080c03440c01c544459041110141503181480400904030a868905000022055401c44c0303000040302000208203021354020850180000c8000140701042494002e0203d000742e110b150040c10040075079000c2e518060004034451801110032250808124100601c0502d140304000c08501c07081c04241c0034044460304000316101b1401440880065070780048948100c2e02514440151041d8048901c80100036160440316940000540802c1c2045100441405002c609a200c400f40c41d6004034404580600031412031440c03201d044c1424241c0c41445032003c03984c04080c910004400b01030002c0d03c40203807114489070303050140c2c404001500c1d114020010380d9000d411060f0f003210800c0001340c2856402021454243e5010542c1c00605100354480006450f002d00000201110f000303503141000c404482e6074443d0654044042d04440c400c011a601405c409420046204484410086043c1c82009840040c1c4562206208a56 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948960863 1250 948959613 948959699
    0x1060f0e07021e10050c0c0a0b18010c031d0c1513090e0a03030b033c060c07050c040207020904020f130501150207090911010f02031204080c190c 64
    0x101880780213190010801503520140e510062880a040200740103280107000040f52801032581d0062040d49169a01c480805200c98000e032440040e610304161582c40e075426501001c0c1a046941e002c240750107000b07689650310607040103541c6e0030650a0308180c001d92034450242000d031035aa00c0303100d0350640b903a00e26021240c010041c070040d82d000d4a05941416058400c41100e103005401922101c0e2000f1000348090241103103260300558801c0124501220f00c8100c41c0c41c00c14054141c07071050408141da8000b03500400d0341500c01d4056450710f800705107498400c64900640c0a8580e031941d640319020031000710201e2000c545c1002001d013a9018003000703442150701030003105e800040b00000b1b8080c000c0c545044d079084010018600034030a80402c003840030031140c0c00c00034a4904042d02003644205d04502481ca510b000d000142400d01c010040403802034034109140004460b58142d85548040080b03e501c030015140801c0c4050502001414290003044940d6002c0703075621404038514414549 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948962113 1250 948960863 948960913
    0x721060b16060b0f101b151d030c0706080c07020d06060f050306090c091f0b28081603090803040c092a050a11030310030507050301060f0e0702 63
    0x1207149000c05400c0100030310420300501c1065451102504014002c5084228944069030904c507010102c00211b04c90342041100d0b2540c41042480c048280d4034011001d060100090300c010f0303041d2810410510380c00000d454200d403429000708445460180281d0b100b2a000c0c01004900508100103000368568908a4070054460140020003501e03101070006515856002584260400001c0c4034108a00044000e41c0d90b03412200000369894855011240b039880030070a1400104d90390001a03130329800740c0034242d0a140c119034009030710442c01816010040c030b88145c402051139800403030360298008503a04440660347c2800198600c00b601e6a6940d40c001325400c91301403580480a0109068600034008450211060820038000b08580c0c8414080c60800007010400040b035104900c03445500d00204481e084001c1d240c1d80c0c18802c0c2041c09955880c0410b40c1c052181200000301c5050510814003242c038030414400e01706d0f00380305826280c060b01620700b8003188601d40c1c1d1220400140a620001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948963363 1250 948962113 948962137
    0x9040b18090706080112051f020702090705041a09010206130204022106040e060103080340020a06020f0705060721120f05040215161205041406030721060b 68
    0xb852510030b00400084050304201c5090900080340000100b0010340b6040711344100d44038240040020108000a01482202030741c803c180c0428860300d150840c0007001511552455487d8440b0680300182c10361080d2902240168054800248101344080081c0c4040e40700400c0546004c804419920f201020780001a01450550040c0541d5140c035114244000000002802196246d504c8991082c000208100c22a806038140000c001d0400d9250241c040c41200b50064448201e40c0255074000074008100d000d0a00010049100d03030000901d205001c01c220014803440382050107010940e003002d042120034850600e202150345204100c0c0800c0010700e40d88041501d024070b164003064031070b40581e04422074503000502c800343c3c0701c14081e00f02c0803440c080d0984d07540d04810a5500300342d0420360007511100800e42c1d1008442c1c2d00c18018412a89401c1c640d00004100d08108031003880306032240b101264041889080c2c40104107107078000c103419000300051031661040d00e80c070198840018814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948964613 1250 948963363 948963373
    0x1061b1109060103110d0605030c041b08100f030303060302010305280209010e03120c060a0507081302010c150213171e0a0c03080403152c0304030f110102010506010c0809040b1809 79
    0x809c2c2020840d50b600020222010711016088034019480391210450050401c51643c0014a109060080d007034000c1410b05a80010f140d540d0400a000380b14901040380003e04102c00300c0e807000340305901c26034003000350b50780c1e59501c203111281840207602210a0310306000348001d4900c40d613507003032000221a846c090340d002d5603510000c2110313007000401460104003920b400c0a0164041e0300c040a194400500d0300004030000b8030b4001070b180d07000499001450f94010701d12807a1404200d4001d4a0041e46a10f1040545d68403081100401c0890460f404029400004101ca4020303001e020400c003038600100780c0b009824244c4a401d40c2a150f41c0061790043c0e000102002082013481c0c50318030014030040100008284814145071a20b4204004c0d0f4415420000300c0c41440c0c0144125402942d0150b08881007902620b800003050003c210414055441c0500040d03095020703100416000750700c0700d2002e18103003da10811004018040c02c860f0404401c0446c1c3d042c0f40c0000703513614014881040180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948965863 1250 948964613 948964619
    0xc030302061003050a03080a06090e010c0306050a140d02041103091c0306080d0807110d030605100903080d02071e150c18030602181801061b1109060103110d06 70
    0x203403030280050701640c0010300284040011450101c5c0800c00c2543c9841c0042e195100d00050340c0180c107060700300540051400c6010000d41a05600c000b10301041e40d201803041d03c0e076840c1000b07607011440c81075030014403035040c0c4e846107845d12511030b800c0d040c8018000070710703070802e40c41101040d0030840322907a941c0c0c17042c416402c0c3c544407010038104640c00c2e803805008580c180340b0340c40c1d12190511505400d00441001051042d4060809030410049420485071031015000b40100030b00007a01c54a4000c0c8003401741d0a400902c102c1c2c52070103480e0000c030424030300080360312103d000307502094099031002441a1041d4a03184144c1c04080c1c0203000d008003080070b100e0b0549610445e42407150801c01d000c0005403080080d442554810304030f030b810460040c2c550015260f6050070801d0612141d600c03000e800410400c5c0500a04010305960140d41c071000e8180308c1d01e00e01c0000d0f4540c00000381c070803844210780e04c2044c60b000000541c490410b00d0301082c550350442207004c8035002006001d8469445038014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948967113 1250 948965863 948965867
    0x2120903012a080a09120305070309440306060c01090206070303050105040c09030209180109020909030a0f030e0c0d06090606030b06030f1605090c0c030c1f02070c1e050402070c0303 80
    0x180c4c1c1c102e850444100324820103680c981c02d90400c02d02c020824036446a000440d104d019078005c2800d2608030900c000c8a90b0f22055100f0120124005203401c034010340d030302e0400074020000300541c0701c1c0740b10080c61864030341004000c055007101c1d8000605640358000040140c0b204000307441014801d88010410703504150810007134520000342402002902a4200050781d1071036400c0342c108400e403030b044485403200c0c00c526000d41411718000c0d4100c10741c0c42c14010110300000c002e00403412155501c6032504c121202c00c4055800315842d110881d8040b085040b550300d0800da4440800b807045800240d01c0190fa5a000c095421325881901c126010108101c038a050621220815141060107429008076010306003204528038000e86008440302400107040211440494042d02d412400f00c0f926040043e85090340c5280e000048000d2116121803031310342507954003d0340c525907408a1085012401c2444494a490f284030741c240c0c00d060050f40004094a95100510140d4059083c84800c036045040c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948968363 1250 948967113 948967127
    0x60b0a021b330a0815190603020c100204120302010e0a0510020a031d0c040c021501030f02011b08030411060a170603011503060e150c0a031e0c021b1002120903012a 72
    0xc5c140542d8920300040f11649500521030709a81c0c0741e040051b103030070801c11554a480c0c800340d10300261074030001d008601401403c1651004500c268009e20be03c0c0c804034007140d11440076520003040c50b0f000000e0401d8610741600a0500100149400611091600314800a101184401c00c085400c5030888492904050181071011480c1e40024043c0c6418000c5007a00c0c00c0c41413001400d550107200c0b8420843e03204410002c81e007030120910403c46d001504200c082c41e4800e80e8102c1e54003140181505480c10003009860082d03110780c0300d150801c00a14090404600c0c014120350b4155a28024241181c0340c1c0388a0300003541c01a0f60000f0641810300d0244c0c0340503d412803199014030b1781010030182607516030840b1144040c62501048403050440d4096054551040740d4840c5420122401c00035580002c5c0b805800d28002c3c07907520800c600006210410203000181e4005030003908600680700b502d000200026100507000103542d19546214003004085d4403003186071507515000582229508c110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948969613 1250 948968363 948968401
    0xb1303140306061c020705061906080105010e1f0515040906090506030a082116030b010806030303061903050109050c09010816051e04060b0a021b330a08 67
    0x41e2960800000241c200c1c0500448107082d1004c14000c400032030242e8040e114961380c010101e5416041151000f1108403c0140420145241c080d0006641c8414020541202d1865401000c10b45a101040c401d103401c50700c19442c1c92407040d600042c0c3d138503608a40c100d00c05640c0c0400f51110b052001da1025030b501a402910414103140900401c0d68000c2666400290f01c02d8009a8412034140400310b150b16101c02040540c16000c00c211410f0008040c0e11035001c5c1035a8108034100c1060010350343c9641c1038410982591092000940d14146500c80300c207510069034400c12107980e2070790780509403000d040c411581504500c05984541c10820001c5016044243c042c2c43d886040c20314000080c5c90b14454144500c00003c9485100790b80600c2e9403c00800281050003440d44035400d4207042d6001056403001403203080b114412404c4610300100376140d0080c2021a4001401544035501e003c41d84030005a00c2c4180c0c4409a01c161580285242c0c021034407000c1c0546840f18104c284680216 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948970863 1250 948969613 948969647
    0x100309320f250b040603091b27180803060109030605130209090a03020a060f0609020d1512051902030327100503151011011a0f22050406090b1303 64
    0x96414040e03040100d040d04e040d80c0c3c0700c2c500052006101d00304a200c22400000098000d13020080205942d03065510310400c02c039089038043d0380f801d0b00c113030f54404a0300f04860000311403000982c0a000100d003100110341018051600c040314548940b00c160443d03074140d401c80036042140002c6021410b10780c0710107038401c200401038601841c040d20b02a444048000c0300402d00741d950b5490300c400a109034068005040074002c21500e84292030300c030600030a10316041c600028518040052010180540c0c1000d06a004001d0b000568031580700520200c0129401c9a050005000f44800b07030b0026500f44004928a025020380103031070710280100211450700c40c004200c410020450b219040740142d44503c0e1003541d001161900000d000c9416402011250344d8550800d0880079444004880042c0302e82001c8030f09003601c405038030401c00c0b50041000c00d80754801c9030705e45c1250104242c0e400547c0c800e00a004c0401c03c0e40b0180c0e43e070760403242e04941d4242e00b102c00c9100a014180d10011801c5440500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948972113 1250 948970863 948970933
    0x7050105090d0b0718081e1605090a0b04050f0a0c03020f1204020f03060a0209030c030c010923030118110a061b14070b0405100309320f 60
    0x304085010224885006030840107100f01160400740b0400c85031801a40e2506000b4850b13456203809921010010061185a41c0c90043d40b0222039010941ca0382c00201141c032020500e1400b01800524407000702044455562445a03c5090301d45020303441c400d0720112003402407460844c0d01d4004591a54480200b058414040c1c841c07000250b400300d568070b100190ba048803d179580e04c00100ea840d6001d4906030140190018402901c0503500900030104040302980c00014038030b0145a079618030320400a00107941c804040001c1843d00b10065502c03612860390304e000540356004242512103c408501c4001c078803e10a20a03c845c1004501c8495000c48a9242403031800c40c0c001d003248100ea150b10090200c0040e05010081c610191400c4250844240c54007580d803400201100e070454415680a64004400780d400948a4800d181a41750300c400a94484116a0b42224104501480510100c071820703200101d20801000303180300071000c0200a00081c044130340d000d07180082511041000d0400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948973363 1250 948972113 948972127
    0x260a050f0f01020406050412020d0f03050a0306120b01090203072006060f04020702031e010e010e01051815150604180c1119060e031e030702070f05030a12030b1009050307050105 78
    0xc4142120229500c123140385003200e0060000407501c241c951001003581c00080d00030820142c10074050b200580c9a910104100c0399504140c034509001018001d001d8007203040140405c00956000d103400050616092940c192003e082d0b402c0303000320700d4030018150310080400138240340c00300503c0f042480a950a41c181181d503070220b0b96540503a03403042414049510680c602c20782c00d620031881c20071884001c1c445d421603019898001c000a6600b0205032026103400c0c1c142c407200140505405d0444030814060350f403500810006200340f080c0003036000da8204000a51408010194180c4d0154010002900e4803c910702238040301c5980504c6203d6005440352803e6041d14222202d505034006801180c88a805c04805003103214030901c520442d0101e640c52041c0312610b074007540c404d4500307400710384043e80c86007201c03045006644240c550541c0113040302800600414440355910707001d420040390039445d0070002104480946554000030b01c00b124200007610b020801c03600108402e01f03145242c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948974613 1250 948973363 948973367
    0x1605040b0a0807210e01050f130f020616112404060503100b12151c0210020a0501020d1a0604120f050a05030a050307030c140301260a050f0f01020406 66
    0x809012405000c12100065281c5004d00a00150115a8480c030403009200300312a0008250031007406420307619000c0010116000c0380401030040d00c80900081c00c5c1c5402c1d5940a4031240d210030120b0b00a4020f1212506103082d141caa01d03550352040c0b5001241c0300c00c140602c0f0050610b513044284460b42e095000c84440d42c0801202c050b2031452500c40e03500c4c2c1d92840c4c400c0e0441c0583d0f12500104000040014001048148042c0078200710020003540e10006000c200362251061a5100c038894228121001880c088508004202c1e1900555100c9116070300c90b0390072600862074035480b40d51114503031180384c00f00c07884523a6840001c6602600705820040349e00c0000400c071500505015806280741c003130250821044941c40d078010112a618180a640205a600f058980402007400d256a940300030740150741c034181440300ea074121811a0710786403141e0007601e13000c0c811074103100c02218041544102808801c00050080009108801017013130803c0c0362101d04006069942d2040c402480166 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948975863 1250 948974613 948974617
    0x20a0b01060e010201020412050706080703020c060f06040b120d09091e0c09030510140c071a06040212040f050d0503010602060118020d090c0509090a081c150303081605040b 76
    0x141c8240b4040350805803100060b402441aa0461448251a0480755040000018844055996917584c0302126110388205a081c0e0146803505001604414002a84080c1c404030450303028600500104000d94000082481c190510303140305502d800c084400500107404c0a205001040d81031400c015001c1400c0002201c020361020300c80100c1c0c2c8403910314601520544142000d580c0000950704601c2060046900520002d0428803a2002d0340d00028400130a2106680d00c958001ca030030609514610150f5650920041140754440d5081c01501e90380d07220006410301c03ca100c0e520550803048582049032800c0440300c0a00e0400c40c4c1000103100041d03010442e241140c02240501c003808002c00078981c0a4040e80c22101062458072003080c1c03d01c40d8460001040703c0c01902c0320300032521120a4680c4982c1c007000007800b4000e003041062039010158403d400c080c4800000002c84a0350a001440d0801c1c26a200b0b900154010341401a8078424112a68042c00c003030420038a001e14111003104e442c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948977113 1250 948975863 948975869
    0x415091d0c281d010605040e060904060e0318120309010f110a080f07020a050907020d110c0306040516050a0e0a09051006060504030303061401091a2a0607020a0b01 72
    0x91480c01424041c80180d1076220a03015030b0700302060720071603180c001902880f15844444450750a80c48000220030b402072080b64140c4843c64291085a6a840140200714202810803210350750340e82040160300300140f010300b070b034201c9801a03949040751f5141044481d02407554101582c4c5c00800c0414220381c0c00c98400303288031845050a52550003421007842c01c0a242d008050400c003000640c1140940c8120004c2c80024421a20010065107540c00d00506a40c1258480013690010591968407402900e00306c010080041c22252014140c00209087c4881500e040720325500144000b10403403801c00e40400903141c19542e0f642d0113031901c0000800c3c114040c1180b601c0994074000d107014400144030b04d03c000e81c4400c009100550742c461008105501510041e070000346040404a500c3e1020700d521041030805964035103903a420800140c02c0320620a80c4044030740d8003004540d9240310142901a411481e02d01c1c1d07070144803180c4001600b0814010140c604640068142c2e600007102404580c5c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948978363 1250 948977113 948977119
    0x21605010b18042406301e02030f0a030302070b150a0306020906160b01060f0e060708130906030602031806060117070e03060a020c070e10090510050415091d0c 70
    0x350001c4420a490074411030407101d00701c9041c15008281621549480401840d499140ca80d03149101c10350f8a8004031002001060301011491080d1fa009060601d0407074140000d00365441c000010071114a0803811100881c00300b60082001000e0008050b4542d6114001c10410b07030320076802c0720014172855864000180982da02280056240c2c5401d81030324051910318140b00b00c4455582130124a00800744a00c10014044a0320101300074441c0c6014600b40401415042c1001595a0307100b071645c01400d2a1004202020000a9095240d000d0200203501440300140c0c0c0c0c2c10546004280021804010701980e4403c0085c02000e0342d100101000002c01b03040010000e0716140340460381e40030100401c42d41841004240040034610b5401071120340280001c40d5203030396491002100400080307032200c043c00880c203001c0004800c1e039000503034000075220200c6019a103c0c00020704076203090b104a03034805d2698405001c110600d11800c5200e040905181045e10703100700001d640c4813007291f14140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948979613 1250 948978363 948978383
    0x6010305070509030d021e1b09040f0b010f0f050907080a0f020f04061715060417030904020a0c0303360507080a080c240103061806021605010b1804 65
    0x558402c50a807080b561009040c0c2d4041e4500540003580d9440c0c500100004c0501c41c1f140c00042c0200041044520a014a03440c0c2c52055460402078041d80040c816900100040f0260002030230210100380039040600201c000c6a0901d82500759812298200718090b0000d01309100025400070b0320694020602580030a01211100d0160083c1c05100e1100350382d02400f00c2d0200f00f260708507004c4241e900d0f0341e0b0107480e00c81d07482c044801c0d03645400d144e500390000700c200710503c1003e50501c0c08400c203072071041c102c0e4a0200c07002c010800b00e0f88000c20007400100d40b503d01004150b41405800611440883c16800030745048000c0420603107100121011005d06010303400401c4000e0000d240286050b400341c82600c03216083c2032609901c0400031807864010300b02c0301c4418009a141421410504001c40340250f800c50381c0d12401000d402c0b4820b40c0324441180300200096640c0028170720020546400e018554840c0703400303030079105030640207445091850740d003801211550800d25409500314103400303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948980863 1250 948979613 948979621
    0x5060f0408030c0d11040f0603180b0601050a031407080a1b0206132405091c02060703022101080d03061a120c0d15210201020c040b030313090e01060501021506010305 73
    0x200502041e2000f085c038000114001170f84449240000301121060380741441208550000003000c20508080144401816004540b003540304101801c440c416a080c00291070581c9900480d030f03c4421074600002801c61030070400013260038000ca4428050b00d1407030b1040040f11010280d1608001001c08090894400380300c030500c044040025094258400c440d80c000c1c0d61100290060102118607440e54414040507c6504012800c8444420302d50b9024003129203514001300e020354400e1062b07075090005c410b2501501c5041c0340140d402800840018501128100e601030152601588051840403410b54004041d99441c012101d1240d00c05804003102d03500c0e003010703d480e030203a4221034400c2072828088030b0300111841c106800350b4403600110500003c020380345081c0d0310f010520080c010b81116803444120b04040c0c1000c01e032446d000341928100349204030901300000741c0354008071183d074440803403010700c020a10811014100030301c098000c480c0040001000123801800035130401d541d450000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948982113 1250 948980863 948980887
    0xa0e031b090a020f0d020c120403111c060e0c12010c050d150f08280f0609080405040903080a0b120703030e2e09290309011d0a05060f0408030c 63
    0x201c50100c0c01301c106a071030341d542d011094025000110118014850104041e0020b0b00300c1d0280c40403251304c01002d04039228181c06111b4005015201c103145160000682400a8102d015105030000080d0003810b204c0c07646010070051090505468256914100c00c82c1c100b29446821241100d1071800c0100320383c034003541c807100c41064a5120401e0400b0b101c1000c200514082094007038454068214407200c0a403800d001030206115038000c05c01701d103100790300000500581084e402e02d0301441c002810180e5580c0401c094602001040b000a8420360030486042610b1056407200301e804d60314540360f07818100b0301d15581e01240c00041c0510600300c031003402941d00d0090b4000048103141074022000b140d0907030440f0030032500e041040807440c41040421500d100038a201c0f071020400c0d506491401e10b0089030400c40e84090f00d0500d5954843c203240745c6001024a07840118902c43e8003c0c101c4c2076180c14214200b4501600344650604d800707080c840410a0300c010750f80c212195034002c42d0740310065510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948983363 1250 948982113 948982117
    0x50a05010c0206091207080a121803061a09070309050601080a0f2003120a030c08070207060c0516080c1c1109150301050c040503010c140a0509011403010b0a0e031b090a02 75
    0x21701d41c5900c103070704001c542050f000c01e9002d5a10702c00d80700712840000100040d03450b40f81c6990010500000d047c000c00c045002034000c480e0004288040c5201d441d020000310346015400c0f20380d580030940341d145850400c142044080c0c01011214080c02028141c0c0e910417000c50840c20001d014074552a010f03289141190402a584100040440d400719035117034081c0079160040040d05c004607103804508441280036012640c4502c6190340a03101407410102c09071550410680309a88a100c0c059001b4000e0f456548900d000d00f00e554001d0100140417010030240b4884006000d0855000e2400000000d10341d030003820126408132801d0f031495869a5943c08040310720501130703501d5030030102404036401040c4010000c0d82c1c0150020312000c0d11012041d9030030f0f813401c50081c0b80800c08001600e4124032840207481100c50501d0000b214400035069019130760001c0c2c00030b20b060000010311110460304aa40b102032000705030003500718480900c02c3e2401e44290404070310b0042c0c5a0320001001c820440d41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948984613 1250 948983363 948983389
    0x1b030e1005010306050a050109050609010b0a1107140306161b02011b06050a0b0f130203060a08070609080d090b03061201180b27210403020a120309050a05010c020609 73
    0x5001c100569482c141000507200075030340b5240b401d10341030003c22500004d01071640b180c00301410726141c5900e805017004c2c1e80c0c1e001c16410010003441010481000380248005002408484882080d41c8a900c0805041070030107400d0030f81d045440d80700b0045058100841c0798030198912880942740030b190005031f07290045910719580c42210400828104032850307100c1400747d034915400704100c0301c08406100c015901c00003d07a0344414040a0350f00d099090f0340007960b005501501068200c5e5507254100d140030b038141c11100121305c00700800c2c4031514080284084c680014a06100014601010000070b480042c0c01c1c3c41c01045d00310140306218009404c2078203101c1c802e4503a440c0210032030500148140b000d59440c100c111400c02800041000341c0907114520b044440a44941462204118500c0007511808100c0100c01c0c070002000d80d9070150380500800d0850800c140070800352800410070051500301500c41d070a004401c1c462030342c0c0301900c1c0f0790b03207981900c1d03159980f800360001032007a00d1010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948985863 1250 948984613 948984643
    0xf03041a09041107290105210109020a080f0609030f090d032304030203010b030616081005030d03021801030c02190c15020327031c1809020301080c041b030e 69
    0x134500080020104042c50402e4450070f283c01c503191140c040f510181028800c0303c0d840382e100c17001c1c2c201000d101003640d07560100b840300001d200401e40e404070781180c085501013104c0782c000e400403206103d07040c096994000b820001440c6007149100000e00f80740a10441c450003a40d0700b011000c2014004c01109100e80c500b5180c055254152055414003580140404c0380030394248804600700b8180010003074020301044d0102141100401422207600c20020b280c20145a00c0c07000005240e1001c0c40440d4885815940260b503d0000c201c4140440036403900480c10180b410600b030b81c2440c1c0c007242c7c1c400410f2424112584600c2c6904200701d0500481c0c100c00800c000c503040c0312184940001c010800e099a1120000e4400d40a4080c3d030111081d601c000b40d01500981ca0342d0341003102c041c0e01c441080f4440d0410003003031544081c0c104180314440c1c00580d00d40f540000140001d4400300b042c45184c00003100c2c24070075250360b440c10125a03a044080030081c0b503201d40b02001000b00502c02d0419803403440d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948987113 1250 948985863 948985867
    0x12110d06230603101203021c090303142b0b030f010614060414010503191a03070503010c02031206010905090a05040201030b04020a021b030f0109140f03041a090411 72
    0x54581a01c0140088088880a000c00c1d402481141042c0042c0c0b0300c00c2500035240480c507894035411526803032521008030300714086c0b000301601c0210388102800d034292060351032140715402c0d460082c000407032201815440c0501400700385000110080e800304220364003000350310440030034485500548540d038015641030003601080d107000e810551005080320030843c00b400c03103500e0100074085544124000c441c2000104280c0051a5020300000c540007960f00050540c031f459503250f540211030b82441340200e0108413051903070061804000000281c0340c21402001403851480001e036482c8180141e50900d4500c0b41c0004196a00604404000384800b4021160503e0501c1001d001814200d03030032030100e0300d0040100281d040074400e40d08000c0301ea8004040c0181400f068990038411642c009a240c070810310840c1c2200c01c00e0280c2c0200500c54900c040c03c021003150f080c2d003062102c070b041c0c85a643c028041000075013040c00903a28180c5c01c034004503945c0c10440e0040340140c140708240844800700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948988363 1250 948987113 948987119
    0x60b073003290a091a0405010b07020301060e0c1e04030c03080d0e0115030209130c0b07150c021c0c060516120515210109030e011209020112110d06 65
    0x60300050a105a0703803000100030580c00c010402181c00d460150383d000401c2060500c001d41c000e03403018280910a40100481071000c500040580308260040300a035440030a0307480440c202402038070090250380241c51602c2c42c2c0b6107026926030280085007801c1c800314200380a00000c1c0300382110081c0d60400075400440c3e0301c0e800e1850095108503409100a480c0540741ca400103010703c2100092400f00d070400c40344da4030b15020400c0c032000207042c140441d8107001c0400700140581b01c2c0000142034000000b034403a01a400c000b900031009110210000d401c003200c818581d43d0100b950078060701d82d01c6c00c50b0203001d42240102c5e09840d01110003003a40c3e140101740030700d500790b096000d003c4079a60303a1110707103200e0000044816181d065405940420a20f98a33100500c1d0000340000b200181011107030034180f905031f00c103094405091b020750100d040c910103032015513800f541c041c010400390070080c0415149540000e001070958220308810503a52501c50120707800b14000c072140303210001828480c1c941c0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948989613 1250 948988363 948988367
    0x528060302191706070c0b090c0a0e07090b1306082e050f18060108070c0f11041b0e0906120a050d0815030606040b03070f0b03150103060b0730 63
    0x515000d4003c40590414008900300c0c00020302c42c2c416a0765680d01c2141c0503071980c5940e00c507040030f8841201e9018100c0c400000d51210542c00c802001c410714004070320b041000001d445555540c02030800700c1c0c820004030184c00300102020045540b585016006a07484180442000040113041d90100754499581c0b500ea03050800d569084c0c480441d0311106d100c000000300038000501030f0384008150410400107090f580904009036000d20903041122602000b5030341c2c400c01300300c0d0781c2c011184511a0402803505003018440e04103884400406420011264540908240c0c04403d4007481140080005421341c1c076218081c01c950701c8201d04840c0e41b0701c89880e04030f45401302e0f48030340d00004100100240b10040e030b001865a0303520014010301510340310b603010b00000e09030f04c502c5c0030b070903201c0c01c2c4e0001a403000b1200514001c1401e1404c5135100e080661095030b000c070740c102125040508020080c0000c1000b074007180c040e02e60100300000110344203242c007441040d0110810016034080e0100c112926 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948990863 1250 948989613 948989659
    0x12040506060405070c02030c0d0c0b070c0f0623070c09020c0f010c09210501021209060a06051e1c171b0609030a08090f0d0915030528060302 62
    0x40c01c211814065079071074010440c1c15042c5050007a52550250710040303514206601a2001036015507040c41c082c039103529205900e58454001140c01803050b0a0030801905036500c0c1c00043c1c4454039105103807402e0740c3c030050f0591001c2c00f19001c400000107901820030103001502c000038600308205549a92209900d20b842c0c50b00b90041d59107035400c0c1820190b81030700c220f4900041d180010070708982543c0320312481d011846c5904084550399800c21450201c0c5110070340042c4a0191000100034a145c0810442e05550351944a5401041481142d51805c00b400c903200100d0341d026106840980904182681140710481c40601002d0442c8104510f9250500081040c102c00e4411070381210480c5001a0381c1d00401c0b00c91401c0c40e001480303c040050712468000ea0441c070794604541e40ea4800e9090541030018070319280c03012840c084802c00007400d0070082e1124074086414108202e1400007a0754050307a00651325807074058804003400b074611036558002c0019503005019030100b4014405403180c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948992113 1250 948990863 948990871
    0x40b180a090609240b09060f03040b10150813020303160804290406110319080a050a150303180e0a150e070c0602070c1e030c0801060302010516050312040506 69
    0x24070704040c8000134240c4103000a0340e1403a80d94080c0c1e80c04074981201e00f40c02d50000207500364802d500b00402e810a90404010f580981c0c010740180e122030070021611050610650320108036a44d12641c2e80031800d4015031002e501c03964051610b003040d1000d01c006801c40c800d5124014007e1804c410b190144a0000040d20940b10078000a8825020141156403200f440040090300c907081007000307000c101d20039000c0d0698241c0400c00c407030508a45114410002c1c4080b01e00307c0c0003e40d510100109070b06036000e41900001c11200806c8440003402218404008a020280606c40042401260484144181802021034680405460401e0f000e400b01600400c142c0540c2300301c0d10000410382150103104280a40c1403501c071240009402d0340c0e9040030f500141c105440e0300c1504d00000450b410030b50113100e10303030082c040254440c0d0f043d441d0031b10031141660042e0740141e1400c0c80500050340c126085030f00061001644000c84041071030710b285140700b07800c85440900a80c2041c0410040005426401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948993363 1250 948992113 948992129
    0x609130e12090a05061b030703030b03010b01110a030f180b0304050d05090d150b0607030509010206100f050d060b04060315110f0706091103011d0c0a0506040b180a0906 74
    0x22129040207550900404640542c4a04a10b104008038035080c00107000ca221a03031021000c0b400d00340b000c00e00f59000700310284c0200380c42c0d8821203103603c1e0a2181503000e4809003808011852001c0e001035444070034600040501c404207240c05000c500940080c06000c0031855484c1545403a01d86000c8140c2041da812611032103040d0041c0e100e28022815607803082000380180c459180162608246200607a24071030500d9601c10791070b82641c85a4000b018464041d031036455880d40d48100080c0b40c1b01d0020b054505408030b8070028030440c40301c16110411240d04440c2d003070380c400343c0e42021002490010130541d4081e1801c00c0010401c00324118032864040300301401c0203204100c0500642c24440c99440c600240010851030001a1300f55000306500390081c1c0041c0403001c0000040303401c444201403d61b16180383d01841c4000f40380e0400140140610581e60780c030180b454400030034800d000e5800789045411001c03443d00f14030750560500115503007000b400350501a030344010540081c1554050640 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948994613 1250 948993363 948993373
    0xe0f1e071817032b06150e030c0f04020c010209041503030807020102030c2a0d05130807081b011103160605060d0f1b0b040f0905010501020f030313020609130e 70
    0x10000e252215500d075680c9600043d44c548810140c07210b000d84074a400c0308403008001c0c842d039408000e0703a11680d00a132007180440c901001c0d00c0703580600300201d0540c140d4482c0d400031b580c210503901c6a41c104282d000081c1d03000341e1110000d17821180a07000303041c0c00c9908140360000b01387d07440d46441e0240c000c0324026199a0719640f0b4009089090b88001c4844c00b2210782c0410669a0203080c45c02c1c1c00048200b000311122030041981030a45c1403008002134000000d5010801083c4c52245410542c0100720b42c40003040c02525220307449032204a0321003001545016007940d02076503405a90021907600e50350042c0d940c3c9951190600c0e45505050f0380070344d000d51900c40003400d10b040c120b040d481c0b80703500080c840c4080300c0c030f07556841e11181d0041d200414003080f580c0c002519030244400b43c005000442e403514041c0c1d01b0b003010102250b005070f00a50466100701071030305d400c000100c00c5a0b040894242c0040c0000050700214101d40310303018600d42c03c2465131740103034240342c900e5114220000e07103002a20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948995863 1250 948994613 948994619
    0xf01091a0403140a0f0f06060e250c17090303120a02030702070905010528080d0c12080606070b1302120c03070e07050a0e04180b0a050609010e0f1e0718 67
    0x139920000402c00602d00e01c0e001c4140b00203c1c407041102c5414903c0740b2404140141c84c0c0c265410a0f0b0f600361411101c41c9800c0c0c00041800c08454001904103600b803030a100488140c4c2c40d9001003c09801c04d2000ca11400140482e05450920441d109075039020700c040007600344404100003e40c0212407200060090000129400400e406081e040b14801080d110782d1403128814500315031141d224481450781030700000201104103012984010368941c590102007181c5081c600261078a04070b52204110841c02003280715529041074404480d00b20a42e020103583d00001c1680100701120041d5121314201c24403c1e4140000500014450090b010340d03c55550322a00c1503032040040c1c0d00d06c00070800522a0a403d180b09a66490b002c010040000c0760105441214a08a180d040010360740c41c5150130800c00c1031050b500449070000300a0f64081542d6241003151016204040c10000841c109480450400c06407405103000980d080c100ca004241803402e0301800030b45026440d5464105070202c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948997113 1250 948995863 948995903
    0x4022404140a241119061a0a15121a19060e0607061803110d0804020307090504030225140913060b120a03090f0b16020f01091a0403 58
    0x600111981e0f60a885a90101031164001c5152001c005200300070032611034114020040002110700385001922000c40c480c541814802c2d2400e500c4030240508070f08401c3c48881e16040b962200b207a0114041f660640700180d8111403421501850380362080c20403554544c890216450a080203400711b81411501141c4014007060360010322501010a13820300c800101c50400100a16141c2d1290f60001080b4040c0d02d11058000500c150907400901807807229410f0300410131403040d40f00b15500308510280307426400079682c2c1d16a4020076014980b04c0c00418100350082000d002c0014034203100240130940d01210050351f240c64880c6142d80341000043d500c041c281300c182507010f4800c00320080f0b1083c2c1543c50341c07005000b5188000c0d400c9a034510300038039000c005000c1623603c64400d88e10010090324100c1e40c01100c44080e008020f040d40708001100e02c1e00b503e00182509242e0650702200101200c40043e20689420341c06002c0e814000150038440c0da070004d0041003580d1140d200b110401d6580300c21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948998363 1250 948997113 948997129
    0x9110910020c0f06090d02150306180c0f0d0f020a2d0e0f28140a080d1d060f1207080c03151c030206070e010305090c04050402240414 59
    0x4140c1d0048443c1e00d070b450182c14402c008000051016100250206456010032405500f036001ca05c400140070091000c1483d00040100f00d80c5010360501c4801d0800714001c007050b2003681c010094000d0001202d010140d4079070000020040340010440d107480c001c020142114035081503503488c1304003180706901041d111a44000c440307015940c5541401001070f00f80140c40c1203026049a1041c0c00c1189824150035641c1c5520b5598a4001d12017038851030a00001181050b06960501c10700c4002003d01c02c1c80c030300007031700b000d0307045c1d00e01e0006002c05403190181000c484075130200b5000b4900180c644040c15808000780b8000c041030b0318243c4140c0c0c903914229030680c4d00340c4100340114800c102244121003c05143c0400e400020421034100d400200c85081615440070100c02680004c0100107445030442410b100d50b5401707003814041403034415001511000c60300c2c42544a156100042415904c1c4c0c07074103641c1520f1400000181148140c41c800d131458001c1d1141800e03442d0824128012030801c0e5003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948999613 1250 948998363 948998383
    0x302042301091e090503070611180301021626030a060e060301180311070e0109090327060309150f0b130603210e133608070302070911091002 62
    0x9030311002611a4004602130000704100f55003900c0248a0321010070f40a21078604107000140e89640d5942d0000040e039009031404c4842882648180585d8900c50900782c1414502e039846402e120290407444400020905102190300c031280011003080034105040e40444282c070301d4202c911881d9965034040600340e801c0407441c0c000860200d0754000001780205039801000d100c0c04159040c1988444494142d08400d91010003540d413a444810203040d041000c480010304800100380d003e44203800070380500c0e0f45d14440c0e202056540c1c0c000000780008e8000c1c17411a143e8014081c8016440000c1c0d40d8058204021118451864104050503c000301c2c4a5002160752040c49400b000000c03c010900c20040c24031840c043c8181c078a049440340d43c6a2490040412181a00080c0c5034404840d911201e803940c240744890410b40e001c00c420305a5002590b0310260350282803503948011500d030407030400348641c2c4a04091400c01580700800100d101c007030040010250340d00300c912644602c0807661000300316 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949000863 1250 948999613 948999641
    0x180a08030702121207060614061e03090106050319140a210509060d060905010b07020a1208160c1d0f0a0506041b120e010b010f0509010306030204230109 67
    0x114a000500309151002c0808000d0400c0d10703185034031a800c5100540c00703901c003111b00380da4424060221010307021a210800c282960301500780b06841001c9018000801902c54070820040002212074100b5000075000d02405801d440c0c0d80403100100c103403070b4071004000b250020240002d0400c0c5d6500020f40390185600108121103500d504100c2014103031071030041201300a4100b04101060311071000414260b6030394440000c2052070845000112401078100c204503030b20801184000d655004100300a032210003100a00516040ca00000a403103008000141080d030307100e294040c07222a2051070200e40c50003404007800c10210a05a4000c2401c0786c03030101c105a14400300e59180801da112551121000d08001400790051019002c000d90f900003900001e900b1003440000c03110240202c42e2517210880c001c3c0920340794a07001070107041d08080d09400300000440c4032007050303119422000055170017500c1000200b980c240c100301c01603100c8004180c80000741c0c00000b481501071183c0102e9482613 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949002113 1250 949000863 949000867
    0x40507110d050a0216080609010608030c0304030b1e01030f14010b010f0f02070e0108071a0703020303061017010f410d05010c110d0e01050306010c02040e0f03180a0803 74
    0x4400c040c2c85a0700070888050071482100d50014a841e103030032584015118600080209140c9095680d0a44100360002c503102e400500109410f004004240c0702565031001241955a0b60180d0402c3c40700541c00300300c00c020b20b40000000c244540c40e02285074403401008a907080400018000d400d9501030401c00e4005100101c1101d9075501c5040d00c4460002e00c1c1c03041e11a02580c030225081c081100f030b001000c09410099041101003008084100c10701c4030b405039075041c0604c646029440707000040445002e8546401c01e2200c0340c0c803c0000840700701c00c0c46084c0d00c465071100082c0101d04140d00071042c480d110704c0c14000303420f009100d02804102510301884001d4900c03006c01001c41c00542035040e04001c005041c01c001501c20b0050744050140e9a40d8100c1c00009101d56a00d0000c094240009201a1200b0402e0301c0e648241100d61080b0282000c1c40e010209102080060190349a02c00c2c003402030701016200c841c0003000901038040c901c18411b0003010010200a0184006d204400d074603441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949003363 1250 949002113 949002133
    0x9020a0e15040f09390812090613030c0515070b01050f041401080c0f0d05370b01050a171509010b180103050d0f0c06151503050604050711 61
    0x880e0b0800f0000003182d0340c0c007185800710366540282085024850390305c80c500031420610008054020005a19224480380004610f801c84c0f06d40c03a42094414100d42d09000078011304140c07134034800c44003140d20340e441d811655503403810040020383d014000c3c103110b562042100c8481c4400d00e0123540c030a80d0003030710400c16a403901c81001050544103101c03035080740d1600c0301c2e02c03045a00441d04500903d8410064542e07900d00300c0401c00c54040c040d60007441820240610404603200144d280340074401480900f95003103c0594000d1002c0721481040c81144c1000059400c0103040b0222034103c0c1c00958034140d0741340e2501582c5498103015100a0441d42c4a400c0c4a0381c02c1d6034030401c694002c003010300000380300e030795074004941080c00e02042d1285060f12480104100503040000101c0b01420740f800e0f01400501d000300801002c1c1e000c0d8050001c0752501402802c00d07520148082c014040e04e900d180b014aa0407002801600c000c03507250f80b00c0c80ca00400101c0f8580107000440c51218a24050501803007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949004613 1250 949003363 949003369
    0x6140111190b0402040609050903041a07020405012310120b1507030206070f030c1403040c0806010f0303021006050a1a09040207081b0d0806060c010e060a09020a0e15 73
    0x31a5a40101e100d0301c07440184000e601400c10302428011414104140b0f82070040c48140c592690080918501d06010400021400b0041d00c081d5076a50360422604041d0668441e494042c4100c0698002e10b04400040c49003c5d20712004140040e005812003000602c0c410001d406240c807c07094042850002e03a0724000c1607681c807400d2003c000601000300d072003480040207103d8001c202d04801580c8044241f28a090300118100340c50788080c5428408007003102d000600c0700c001901c4d15100094040045401c000a0410010190150030100c80700c640e03581c0810701054403d88419005402808804040f040907402802c00f0345001034600001103182250000c0c0101607110306001a42050001070400c0d6038074001080c1240c0150b80550b107400d01c0c0303030241d4070f1100c000407000344580c00000044081ea030030601d4280d109500722006500d6001c11981240500300d201e40c041c8080c05500d08102c206074460340500b200da8000d894002407280c4944905a02041c1580c0c190f2a400e0a01c0000c80145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949005863 1250 949004613 949004627
    0x161a0103021003020d061707050316050a06301d03070506010b030c0403060e0601060e0f1018030b04080a0f090b030610050d090c050f03070b161407080f070504061401 73
    0x4c5d0107180000700d482d940d40f80c208200601d940090100d410000301000340345000c00066816540225204650a2500000610710f244521814007400020704d0303404014903401005203070807036440340240c10b01b1100314a036000410302490185e11201202c4070750900104000142c4103102d503c540203000c00d034240100414a0b810003010380c4100c2c2810440400000c0c920301540601c02120002041154100040502240c010b0009680560300030b20080000c2d0366440c1d800c0001400c1414040c06111450380602103003040c80e00013802a0340d00708284800c0120750340081911a282d9075400d030014000060441b1a41510720078040c0c403903000c3c07010030340c145002080c44660301c0c100d080407450a440c003140d0a054070a80c00e401e8801e880941010040c3e030806400da2010190102d010b89003d6003091481316607030280340e8138085c83c030150842580030480040d42c50fa1140c2c01d5801141d40c0341d5640d00c101c5503241c0d00400204242d0088050000c3c0e9801c05000780425142c8008112290301080c3d40116a02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949007113 1250 949005863 949005877
    0x20a05060a0e120a0203040812070f060b0112091a0a050106080106050f120a0b01030e030c03040b030a021b03190309030e10120c180e0103030912060f02161a010302100302 75
    0x10f0041c50b4050f845180c03e4001000c4080c859000386485514181c00141800098031501412070820420712000440103044207100c0c69101000140100103040125281d42d002051596190b1130020705109000391a02e84104126400e2069410f40c4c0e00c3c42600d1094520a21600d030210303220f10014451540500302900c40c618800803158144030340110f18402d46201528a80b09569580002c4805541e160066025210070280110329040500d144d16990b03100d80d1140740408a80400407469641d03658045032184288001307072901c941000307805d81c1d8030b81e84001c1800c0201040a808410031078004c2c040d01801c03541585411251240802c00c0c840c152140580140401001d03900110040c2403c0c0b286020012040d0f4440d122442c0500c01c043c5000b6450300300c00201d420700f4004000182d8000c00000c00c0e594142240800d1300603d01e018000f5150000c000d001039400841c1d002c1110710360844000903503020f08010741040c0b9844500f40c080d000b0a00001e50440e200c43c8010b43d499000f50010a17032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949008363 1250 949007113 949007141
    0x31403070501060f060e0409080901111002030f071116030f020d050124060207051507020a030c03110a0902090906010e1c06021905030712050a0b060711030d020a05060a 74
    0x50030015548107400c541c025004041c915803118010700c0542c2d440b00400307240100956040128000a07290380c002c0f0300880c6c2c0510704210340e182010301106014071400480c0d070302509065441e0b0500200c90562800304035200400162301141d040301140b0000b50810f103518010321403680c00317411910307000150400d0107400e0f600007441e0782100002401c24482c080400c40c1c2581c1d01c503502c03c0f04500303403010a901640b040c0e0840d80511000c1c8407640e0348080f41d0000f0340e001031003940c0d2443c1c1e03440412900c0041d584043c00041d80580b0010a002c5e14030390070300720f07401e0881e07a42d9001034540603110228000d0603006900b00c0704a00001c2d0b00c035400303150040c3d61114001e05084017a814941e000b003404004610884034160042655003002e454030400900303405440c10182e040d46420600107100d411002414400d40791a840030400c6071509500a5400d0300c4080c001c2a55281507003491541c11804100c42c1c0c0c02441388050003091588045900c26061340c2c82405401240c50302083ca402400c251041502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949009613 1250 949008363 949008367
    0x30518010e09040b040b0718180e030a02060a0c080c031305010609020a020c030105011208030a1116051b040507120518030705060a0c0c030f1133010506090307031403 73
    0x1580d070302c2440140c45940302d40b00305041407401d03203080c24040c0f0000d4030340d8040c0f020035520800e0b8001080e90781700c103941211040310000a0410038020182507148000251030200041c02c0802680c0030820521410064000380003045d07030f20304115081d00c011103015074172520034408110342074501614000b140340204000300703040f070310742503103204a92040d44c0d02c02c0542d0281143c000309080c2070240c540107040c2a03c1c0c42e8081d06146d2501e012a220080822103816591002c2420302003012055540100401d022140003804510b8035a03582c544840c010744a01c28915038051a519060180601c00c0c0c1e01595400c00782003490300050007901c0054420380e00c0d65119000c00c4600c100030006440518007460081205003045104003044928100140301005095500e02021a41241d28440349106503c1c1040340b558003001101e0420f502d80c81c80024142c1921408038001c030501d06180074a1200c001c00c80181c1e42d8900800009115018400c1e40503001030701c2c104007103140d0700e04041c0d280d0310703841c245c80c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949010863 1250 949009613 949009637
    0x70512070212030702010c18060906050c0102070c0b1b0615060702061c0504150903051b1905030d0f021822060f030b0901151707080303040b0906090a03051801 70
    0x110b0503001280c0010050f955580d10010045c2e001d10740f0039880d02d030050503c120310300781480207107941440c1c0907032030520000150342d88030b41700254111500107802c102035668240d11400f2554503a800180041101d0a12860b0f0840301d0388041001030040c00c0c030705211106602650280301044d00031f2141a80d0009080c450b07092110b50740403000c0c251000f1800005078501e454070f8140000d030001c0e6805101c05261200260019410004440d108681411800e0305030102402d00d9107401c4c404003030300880300d449204e104100038000029100d6924041c0c4103001c603550780c042d002d080740a4804e5800f000d0500741c860303d5050802114000f9011000c4000b808400c101141c458180c50305680170710a810080389040003030107003013040c0c260020ba036400203100c030808000c1e680c03119586501920041f0340c842a504c4414900401ca00e000800c0341c081642d449281c40e052180d04004119401e2085000d940f0004c3e0403180c0200c0c03c2d21500354140c075800d05058031a807810240c202035540392410f115240780e40c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949012113 1250 949010863 949010893
    0x1020c1005042409150c0303020904020c0d120501081b0d030306120f03020d030911040506040e0a11090f130b0601032c0c01210f0b04060312080108060705120702 71
    0x40210f64180c41c806200080b0510028202c80095110b400103018601030b0444955210b1015011250076250244c0c480c0081c0e0b000a00901c100000c3d4482840741000c01e01880b500f0040726003c1203d01402000140c1e6280d40362900c0d1900201000030f042c489012000341c601e8907500074600303280030b46000200c0075201c074a8100000f07034140040e1100c20310b6451403420543e04008030003201a6501c1e05104500c0e072951803002c00038451460030b1045031604001b601c0c940310759000101c000018000c0b1141141c550502c42c3d0b4201689071946e0280800c00d0000382210365818081b401418500058540328020b601c40c9210140b0192500d03041549840d9140b9112000c01c55080b5406416511401d604240d82402450189150079180c1032105000a4503000501519600c1001091440c0802c1150780704141c44024140c1e60003155000b45031070008002c1c0b0056880351401d14a090f10b9410040e41c9983c201d5176622800c55000000071400c0161040c560b1240580e181c1140c00c1d0f00450314800c20310181 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949013363 1250 949012113 949012139
    0x6052a0702090a0608070e100807060c020f010201110313050c0f0609010810120c15030c0e13060f090c14280c0b1f0b0c0d0503040c120506040312050601020c100504 72
    0xc00d4007c1c0c08000c003841302e454182e150307100040007400001c0000911b4110080c00414203001c010f44545d1907684610003c0e4002c1d005400402e0f042200b45680340f43c80100c500340c01010090544a1b88500320714441c040c18419414049010300038156414204207100458699000504549080d10700000000b811140f4042e1000d00611130300e601a10603050070050164030001c8415030081504007001815007542114210380ca141d001d49030004a02d0082031400301074a055405150015151200001c4409a0fa401540141c0a644c0c034a2088c10200380510400d000310075144510b624903040c044901c140d0b0301006012000c150401d030303075800310070340340c4c0c3c14620021204100501c071030146005401c140c003142c501c041c10b096002c0d02d04003c2e2000e100c40da038504000c8080203001000002c41e0038014a01400402042c05d15801015040c0b1407809035101c00342a00c04034086080c10b4000324411801d4080c103803147d401070b80200130500d1001d080214000d103c400380810b1000400c804201c07011080c42d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949014613 1250 949013363 949013369
    0xf050d030207110f132f0c0c2b110d1104050c040605180607021201390f180801090209070306030525090203010306052a0702090a060807 60
    0x34016103524190500d032440300c0034450154032540509040641690310003441c0b0b05c980c51460000600c207104154176940c00c00d582500c1e001e81c0201d454105d003051100000a081980101080d2034a11400209000400804541020384113584000c1046410044464500351501881c40800d0400e9030f40c0120340420200d550560758101000600001030609018031500302070101c1d01e2510b014a450002040c42c014100550746d88070101d1240e50342c0780d40f0b10003a2400300e40c0003009600b08011402d035180c0200030a9400f4210004100c040146900303040c04d0907044405c0300b05182c40d5041c1c0e4134404503130403401010603d0500c1400d05811651140c1e0b040000041c043d090000038030314189004000001600a003400b041504020741400001e1002c18010a90307561142416440c4000000e05003a2858540010359642e2011000100344034135070b0411030049910201d0031a2554035103101c1070440301d03096041c0d981000208581d00050809200c101c0e8020306c07607140083d4154544008605240c1554 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949015863 1250 949014613 949014617
    0x6030204111b060c070206070c080f06070306081f0e0106090e031b06040c051c0510020a0e12030301050d0609050307050307020907050a2f060115030b04150e040f050d 73
    0x300d102c028403115000b00e05003041c040801800249000052003c0911810780028040c100100c0d00500b0000a11000300c0608440c03015114001c8078591104d036545012105da03400079090080001d1410004101d0380513685140a0484d103502d202c100d658003801402e80602029076036170f000020145107500ca44114100301c10043c41c0d0702e911180c00988400c10707106134a804d43c0c0000040c0700004800d90380013021508140c50011000e00907c4851002444880001c0c2090042580e01c4c80d81086550041407041c0298484400024440c014071645c5504081c4c0b8000c6a0300c20401440146440710740d00303005502c00c040c081404a5103941d11030071600811821600340c0c0c40814250110324007102070607400031051400a040a01258008080705502c804100c0000310f2249003110a078003610155400882c545c00719405540e41c0c80301071050b412001e400c240002e00d81480300f502c9140034011107215030030450740c00400b030341080255544060701130022545450107248010010b1418130a5200b00465a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949017113 1250 949015863 949015867
    0x1032904060f06090213030215040305010c05030f070e0a1e030204090507080d08040f080a0e091501082d1e01060f031a13090809040e1c08061507060603020411 70
    0x1c1c41503038080d56100d820011380f00e40144400d020700f030151000d02040b00d0b0101d440032244447c3e0101a0428412900301030150b500340b10420090b10b4018000314014480010031400c0b583e2000d4007111f645590040c007503030207031100c08100004440d01046003682ca0b2403540454071076940780c1c0080c0482d44c80d05002c807559080010108440141808814a60350b06802c0a02c01403400e9600c407040404041002001c0150210f96695024440c1c1c54101c0b9181000d0705c541218207041150300c000c112800038103800100d402c0000391000c80c00410074190150000015510380e1842034141030b010304020450a56800740c0b8206400031481e14140c90b00914603501c9021070710000000c000c0560394152600c50b41d21004070030780d01d00d60300d860340c0c0c040e2070481315440019901c1040c50807a1491081c9000c41d86d1160038005002c403107540201e50076a045004c0440000040e46e400345c19680c0000c1222180d5114200c0c80580440440c0e12005000c841d21509001446075266230000782210b2001c0c1d03c0d801c4890740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949018363 1250 949017113 949017131
    0xa121b08010311040c2307060f0f0506031c081b0f04140f0f040b12100e0f0c010c02060c0f010c1d0a0305030a140d0e010912030e060103290406 63
    0xe1001243c0750710f02e06550a1154001c10750018252041d0748014550728851030f0f400507508a0b0510540c1c001c90307030161040c002e21900c40b801102604174140b10081040c07a08010448c01d140003d4100c000ca10451202d0079415010b0354180d40702007004002c1803003081d448680c0302c00e0005901c02807212900c0031081503103540c03c055484003031008030071416005090307402d02c0b00c90a585503481d400300400101c4011400c030f40008085079070890119941044c52280300c810701c0f07498070503401508640325200201d941130003580e0350182d60345070041c0710b9601107402001c41d0030150408200a10200d00003000b220440c41001c294036084410144141d00090483d800d0030b03240441c0f44800841e0600c04440030003401d070468407074a440e44140b0040c030080c420349000d44100005083c05980310448040300070000360031100c241901074061b081c07044840d011a40c9145c0c1800d4003e1081107c107101110003041d5503829565110300c1410160100103110009981c00321142ca003914025200d04d21512020070b06030b00b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949019613 1250 949018363 949018373
    0x5070305250e0612160c020102060f152d060702092707080c1002030307020c010513030b100f08060103050a0b0a02091f03060914040204020a0e030d030b03060c09060a121b080103 78
    0x40508075800b003080401b0390780c000d81e034000f070308640040781c0b1a103074400d503125180048010300043e103146412101034140030040074900102940d0700303a00d0201c4806104200c04c00c100030703485000f0000f54440c4083c00800c03180903840584c07101d01800300c000c0016828a20b82d04629101469210722680c1d400300403605104e0900c43e036240720700c610b01c7c0001c40c21401c11940294440100030740b607504000700403030310400400c1100b40481c01190000c64000b040d0600c0c011929207807640d4080d008042c14030140c0007800d1030001500394100c0c1d411801800c11207a566840c44007401c0060600b0000c181c003400408001c0d510106010380c2640760001c0e200500c0414540902600e00319800341048070710302400300d03d20000e144500d0398891307030455005036030302d0141e1016070f40e00040181c42034046c4940000f02c40780075050b0744108943e43d8200c040390078958540303040303840034442c4401c05a04408180071300e82c6038601558111601802420780491802d450b0409040424422141000092182d100410070b02c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949020863 1250 949019613 949019641
    0x30705210105100c11040b0a0909080301080105070e03150c0f0a111b240c070e040516270f0c0f12050c070813050307090902010305070305250e0612 65
    0x200b05801c1c5190044c03001c1c0c40c0d40301d0b1000b5003d2694080c41d11001840b0300c40e501c0c8501e0030003806882034104101302e00c90030240b44c1d43d0000d01820160b0741c41c10012880c0140030302c0a11800c80d4004008080f032203a000c10034080e0000180460400e010b082c45070800c0c0b450080302611910b1740654600e0414903050314803c0c90712454500314151081c1e041c0b46295981c481e05000841010b180601c9020b05d0310303801141c040b91044281c000810302401c0d001280980c035070003000c0d002d1030013402252000c8280b26500a01200075110b240040589006015030300319000020704144181c100f800911a6428208101910581360700b071400200200324035408983c01c102500807850861004100300e250404242245100311700d4003030200744000c507255404422241c00b40d0090f000c06010303103502a0755443c08101601e44a5800c9000c40e0400002801080c8a8400c0c42c2c800c80040092080b148a05000303110b008284100366001c0000f0b0720302c840400d03214140140079500601e0209030f01840d0102e1141099 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949022113 1250 949020863 949020889
    0x3d0f0f0306150f0e090709030506011703120901020c0d0e040f02130302190f0b0307080106020c03060c0c03072312030c030c0a030902030f06010807060c03020a0602030705210105 78
    0x100d031424a080c00740d608824900c00c01da00240c1019400c120b2803040907100c0100c610900c60b4420f2a07007003000521a84555001c1c1124031403022030303c00d40d80385c2214460754841c1c0007001036241d005000d800007568240d41384540102d8480001480c01b9080300000342010540710700c803400718020ba0340c1081ca5080520511811440000e4210308107540a40b0f0100d07051013900c0043d114800921076088280350624a0340001d128600749401c03c5c40d503d01d08a103040c1c00c100c071564040341c0aa030000a5039400440e200d0713031380d61009000d01b0060b500d007040c400701c68000c0004603505100a001030b20004122400c0d109449850031501e0f880380c07400f4969946404818015440c0b804024414042100041c105807a0007281c00780f032154842d581004114010400408040e50620905240690307284011881a040e01e000074203540e50961140b00540d0050854a0002e006070300c2041c0000200d210b950156402a8545c5407042c5082080385110655518202d4a00d00305482480100058940305000c0105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949023363 1250 949022113 949022117
    0x1b0f01210c0e15030a090602190207061b320d050711040204060c03110c06030a02180f030706030917040b040e060a18050a060e0703060303030b0f3d0f0f 67
    0x403500865031054a501015100302816921686c0180c03c2052580548410425180b401d031104c0c0d402c100000e40e500405c2c4560000303c0c89040d41e4140325a54030802a469540000044c0c1201012802e06450380d40c10006500c0550f4100300f2000c60100280004c581c0c40743d45903511360300c4010301d00f4100c48003000c1c06002c81c4524410041085241c0e0407140120b4540d07010f09140c144071000c8541715042013040645194400b00000030012240010307030182804c0f600200300340e8201202d500038045c0c1d51898681c0503070b1643c40307a14100700c5141300380c020302c041501c0340b070000401031801c0d110510b994029401030301c0801c0c4049401d03c1246104042560310090449000d801c1070310b01400200030b0071040e8051628251541e00107181c0b801d65400034801406285000f5055244c000c10040041c22a80000c0b000282010100009440c042201500720800144065100d01001c1000843c2503002c00700c1da240c5c2c0340010200c600703828000f04181d504000584442c66950b01440c00209102d8030b40001c081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949024613 1250 949023363 949023379
    0x210a12030c0e030a0b06090c0c1212130c0911070b0408030603120a2003120106110c03060405030d02030709032a0e16030e0304030c1502010c021b0f01210c0e 69
    0x404031710f81c103149980100b81943c0420b004e4540005c1c420307062103038800c03481a0f07100d005002c0046070340c403400600e000500300d1000e0005444a24460503500e1080402409035400274406010701c02083d8403010200c8002c0c1e003050301d00540341c0d17174400c01c4c020111410f86132410003000700300281c1428800c0c14901c03502c1801c114945410b5585c09000e4003d02600b40c40f41c040e4500003503108403820001c035921801100c803203034030310341c0e558000510004681200d642a0301880005a203e03050004603680030b158800003a6040c9403601410780d001750802010b0341d003042240e0100001107921010034112003400c00300b1900e640340c0d800b6034081e01040301c3da100300407101802c020092100201981964000711515000c0b4078441150101455401039030800352481e85d22440c00542103820030500c0e40c0e01c404075002800b00c0255000d041c1d85401e90080503104005150350450028a011452280c12142c14100345910b03815030712000300c21036604e00e09984050380d02e101c43c03240e65030444112014101c0485404c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949025863 1250 949024613 949024633
    0x1d0901050c1608030601030e010525030209030712170408060f370608030a050408010c05130306150b0307020609070b0a020703420b04060302210a12030c0e03 69
    0xc5400802000c2c0501540d0020011032103a0307219802155448050710028006030620008541210030132820b450010407540b1036030f03d8060b02a0082c1c5404050007170240c2015413410546030041c030f007810402c03100c000d240c7c1c4000d40c1407281800940050042d40c0010282c2d03141030403c1103030045014040d19003085003100c0051000c04484d0941c80704040143e002401c07011405d403003a015064542185641e408041404201d2a80c001c01510880d8ac6074802889400c201e080c0c143d40f5807007840e1440c1d2081c0341d12207080c40800e2007900440a5402d8003a0700c410001d5442001c02e034180c0013a81d4800050304038400303222115000300203004c041c1c407243c40482d14004030103001a40d00d048a1100a0100300e42800358400b0308112052155044107000c4001040c3c50100c80c0356a601d1615280b00c00424a0035120000f1400c0a104000c180da0b4081c120200400c014144005910035580c80b0813328401d03400c503180011103200c080d13410081d0607200826010710340314000e480f11450130000c60080d44103e40e04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949027113 1250 949025863 949025887
    0x6040321120b091f03060e0f01150b2a0a031d0108010e2703030108030a090b1c0207020d020a08030307030f05191e020301060207150201230606041d0901050c 69
    0x94000001d130b100a006400440302584010700300b6400940010b141c1030780340c0c844180100e800d561002c0e08030020064501281034008072100c1d80e0103050f503601030034403400b10427a60503211072544503868801c806c0c40440500d203c6142c0004e800f400c6000a40a1560034822002c180100242a20900f000d044640c18030342d03206034810005202c0581c0d04188840c1d46454480c00c0803000d00c8105030301c190781d0740b0360310b94094035a01c1e44040040c50008040c2140019000385510503035400c3c1c0781c080880340311b48811000600c0650090340c0c00f41d81c04268003204000503a0307910009401084900c000e19104d00c0c2140c1c2c050111960407000390f030580d04040411181c4000c0608000001f24800c0001450302540700b440d800c660020810400c0706440040041403254000460b001250020055440e00d5a40068103e00f80d400b1071012440c010002e4104110ba292254405580040c02074540c0f8141652000c220f601387c15601001e2804084400510000b40b2003030145540c00410100240c1c60b2004007084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949028363 1250 949027113 949027129
    0x90915021606050c070203010905030703080f090c010f09080f0a05011b05090607170a02070905070f05030406110c1002090906010e03060109020c1e010b13110d02070206040321120b 79
    0x1c00c2c2c1c6030b54000041d40941500151341600d0307000b80c000c0041d420385181c0903999a001e0403094020401450004d08061a83e88005108480303400281c44003031070032001599850072410000c2c05000032104042003071101000420415407400c1c000301044070f440d041980c2100c0c080c91145603440891081580da041d086000c80306038803000d0f6505a034484071070230003000c69801b102100c0c030b107a1800640b0000300c540c0016100c0070340344c13180000c00451300d585606990855042c40d440c1c010503c1803000801180301356210405041958202910f400da030701000e5824a40f95050740c412481d8041426100b50625460313665002d6408e08149402c82103510000c2e550740710512541c080c03290002030b80203180c0c1d0207005010b01c1222008215011000c2d8407801406801c809500398010901104020b540b110305002e0700380118000300d18240340480030900320010390b20034101680c11000c20400000060b080040703c1141d04005141d00001340d440d0040100b420411840c6110384070b044c5406e5030407503518611 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949029613 1250 949028363 949028407
    0x30c020c010c0312020708030414062404020c0a1e03110d02120c0a0209182109010f0c08120108100c0e041a150a141204020f180109091502 61
    0xc103615020060900f04002e03111b16900202014008410b01c03042240350741c04840a81c00e100240e540598a00e00528018415030323070402110340c40807a00150302d081950007030101d41d004a041c2c4140448a0f2501c030005000244c0b0f19245402e84420030040c0b60b80b001c4580c1700c2e41d08100207000080c0c54400025501c00c90b41a090780d40081c00030383c010360792a007001188480780e400741c981303030461404501c88185101c0154269419008405011083d90301d001c520b00c031010000003200b424000c9a000441e402e40309450704a041c041c204080310040390b00700012f000d044245401107000c942c1440b541fa424455540c0b004014035013032074501c2e0409078003c0301c1e003201544c09841c0041c41000c5100c2040041602458541e080340c00c040c0303c04203111907140142a1000691542411a4000c41032520244034402c000803809501002050040c82c001c050307190718180040c00c8141035454100550701900c009e034829030b000b681e5140400208041021300c2185142260030441c1810340501c2c0c0c0c0c036240c5415074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949030863 1250 949029613 949029617
    0x10605010c08030f09030d06030305090a14011403090c0d0f03020c06120c092b11150f0c01020906030907061407030e101b0605060f0f0a06110102090916030c020c010c03 74
    0x20700301788030810948a4019880b1002d00203595603045c0034040e648410410790003414041d40105006100500110084206940d000d0b00f41c4010b203941d000a410190480d00c05000703540c4000c600ccd03500c00700c040280c00d00680440d50b0a0000e454041d02c0c040942114a005101c10300c0b03e156100c101d034001c0c50344499030880b0203a58440c92000514501088490034424141d207128140924840c10182c1c01800c2c8580c4500204030758500802032074004405d5000e0f0b0011007001000d80540c2004040c1800c520309500150070903075064002a00c90300111442112640b00c01c1c03003081100c0e032241d5801d20401e00170149602e0440c1a8030000d05041184c6001409000b08480341400315208480301340503510300c2c0703201e617007602d1961801c0405003006443e1540300300304080f41c100a514000070071602c0c0a00c010a0300c0c41d03862810109803460314841b042c0803242e542c02e214134030058131050184c0d84196543d28401e03101c03581d03800c00503040760100e1240a04540c080104520030f66045640d9004907500b41c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949032113 1250 949030863 949030891
    0x3060609130305250b04050708120a0c06110724180f0c05042903010e0606011d1c1217060f03010f0c11070e100b03090109060c11010605010c0803 64
    0xf100d07180d03d41110140500003d026003541600703003c9802d00c0140501d03c40e9003900d08103580d03000181e690b4120241201749110b0304118bd41101c0b8040c1d0354001113a88103041c04102c02d000480884800c1e000100d0039620300344032000300b03244116210840a8130013401101003041840e06400364000c5640690020100c58030340300742e001402403204020340203050060090000503115013022000d412454000d0114210070000c9000903d4107018211400752f4800040c41c07a81d035540011244100045400a190700c8445d4010001e621094042000d1014030704101e111841140f60040c205000610f107102001144502c03810646d0089442c0d540150b011101005003500020009004010000300c00b07620a10741910016071a4004150b14089c0e2203460079200055565015080104800c644851101820345014442e60400344080d42e040140d4500000722004903aa60308101c51000304108040791080402e0000e400e000d0040038060f0800b8a00000d0341c800555580c0b849010160200340d141c190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949033363 1250 949032113 949032127
    0x40615080607050d0b031005070504060e01050405181909030801210203151b032401093012031508010e120a110d0509010311030606071b08150603060609130305 70
    0x41040080b090107c01c640401c41070510860141c500c0d401440b56201090000c2801c02466000f0015503084401c050091090105801c100f0710400000070032072040c040035403004941c0d2107054400d10403070754400d0329509502e506200781c1668a0301895454590a0b440038940001a00c011481d000c062140f0309584c0015140c40d1011243c00c86100c1300d4084440d070110800420380650381210404c03058001e90300b0b6414100500440d944141c0e4040c003002d81c140500314482c0608101401024185520501200301c52035903101503090101c1c4ca034810010784c807400f0200404454580750b20041c41100e0003000743c020000c0049494050b084100000e0050215103465000d029145502ca002e5005040c0c0301d00d00c1041601503d1600001c0c1103d000a20300a03107030208480040c2240c1c06150300910403414085290b84141402084a256a51900ca10040011034603401c006280ea1f14500c410000c0329803030510309051800385c004050301d00c1003240c40c080c8011004441d00d9038101980501c1c10350f80da204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949034613 1250 949033363 949033369
    0x3040b01030b0f041a0c2203020a050f1e0102070302090106210c0e09040f020603010602030a03050603211b030c0304050f040b0a051309051c0809060f13031106040615080607050d0b 79
    0x148680301303815064040701d1001d007c40b02e008002c10750f8406c4890895040d121424480c1d1901c681e41105d4100307154008280d030f92200c100d8410380200d0144100d9031183d0700c0f5404503d042a0a0707001c81c020564240d40d201002007030840d24403140e04d4400d410402c1742c5210100500c0f1004407282603015560803804101840b00b406143e0300999005080c450356940c2d00c0f8002175481d807003000e000c000a4680008a1024a400b013210015006d1b202c40c2071010b0440702d000c07864940d200b03443e80c2041c849400014041000300f400030307041c0000c00402841d15280f5000601150070401c50005110b1407900e01e184055945940c0044103854003520300d81c08280003100408010241040003511b148140d40202c84101030003c0c42c0c070307100ba800d5900d080031502e03003251141d0b8403003056460b0403000e0b000400045040821189282504e80240741000d201d00c1d500b00f10f2810000107580c01e4900d0b031b403a0140082d4118884419100401642c0300601d00e40c038190702d0081c018003400140c120303500e84550600585030707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949035863 1250 949034613 949034617
    0x11b0f0e04060f080703052b08060303070f0507080c0324072109020f1906030c0203040504050903072105030411040b06130f050103090803040209130803040b01030b0f041a0c 76
    0x104150ba031081c01c3c0740e00d90f03078840d959155034401111148039420580e49502c16108095901075030107910700c0c00c80105140281c40d402d000038207468041c4400c0c032011003c03031030030f080d40b400884c000c00282200c0da0130403520504040c20700703003004d000b94800b0040d1100f086420003210140d618419903081261a010310032a0b01c12402412002c038401d0b82c3e074800d18401915800000013a20032202e80034609054010711461388824a4120380400040b481004002c3c0290440d000101e845d1050f85d00d000e40303410000d8110b60040e60115465030012440c0001c1007904006104401400b440c1a01c500c0e40080004003248402403000f050300505a85d400c0d2141c885401c50000d5000c018034264031904041900444410640708082050403522000100382d4041c1c4120040140c1000480e846c42d900c6070244802804050622568507413448030300400319007400702030740c061880f83c80c800e10705501d141002c10b450000a00b4101c4900008010b0100103158000424800540b20503411190750710489220b5684c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949037113 1250 949035863 949035869
    0x11071209030b091f06030b060d06020c0d0c14011512061d030c0106090506100507020613031a0105090f0103030305370e0606010c151e0608011b0f0e0406 67
    0x554184040c8408000f000c210004040d281110154401e9100b000d0785058440a102c09000d0101510100c1c1441c100300c1080c00c03400d1b000d540c0162802c0b981c200d00390301c0c210b041710390140050003200303403101044040e8030007d0003019000024400c0c80005548025490014400c060039500c4140d40401000002d41182c43c0e4071000c01004102800f021948503107035403200382103001552804c13501290306400e52050b54000d90010303120000401c4d41c00f174269541d61000c1000c0e81c1c041010700c003403401900d40c201003901071031003049180000007001610400b200b43c1038011900c0342c0c041d5000c100d6092528030101d411070380c0610b00481c0c99141d4921084011142007499000b22500071001c030070b42481c0c0080003074414031804040106d255080541ea46518050300c88500089076182c0080224801441e080507071801d40c0400a281829401c4020340409116544e00c0301507219902003140c0c50742072061621107807801803010700c2e0150b00f4400904441d552400d100c24400b2140c0c13030f030b546034450754024805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949038363 1250 949037113 949037123
    0x512010c27181104060306080c0406150e040f0501080703022e081e07020303061201060f052b060914150c030a090242160602220305010c031107120903 66
    0x240b540c0705c0340d005028100d1030140032818810b0308000c502c4c50800e072140008880c0220320b5203560b40c070300f42d001315007000303042c09800c2d401a1030b03400c0c048500803584203550013045800000c20540d1324500c1030081d00e440c19109200c040d280c0e451098282500d85118200d12406490b205803e0369030000359150403054250300f95a018512010456081c1ccc00000450007100c040f01d82e030041c41100445c04d030076184140500600100c09140c1005107041954600031002d82e90030010660f0751040b1101c612101c07540d4000d64045032904452401d110f0a00340002011a09a006e04030103016141c2040d443c05000e0100410160008009840650142e001d0000b25130300605903c0c1d084600410b1071949401c84a0202c02c07ea84c643d0440611008083c000f840040703c1303803440e82072a074020003400c0b030080d029200307841d215003c02419806045a6000100b08a40340031480c0c00341c2d040d820142e0858200101c500c050612340347d40000c03228043d0056030030f103552049180303041e40401170382100d500317000350300042c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949039613 1250 949038363 949038367
    0xf0f0903051605031218062a010f0b06090f0108180d02160f050a030303050406020d0c0f030e03030c0d1109041e0e03042d0512010c271811 61
    0x4a030182040c500c2d044403012005c80c3d402039810b9511081c14421002194000d2200201e0036242e400e001c000340c540100d520b0000c045460700594800b825500c007a08110702c6035074406011080034080d00c14241406010707524079042c0003481020030b1040003600840c42c18040b500e40081c5a14500341041d1040c034600c0c04c00c0e18280341034080065550300400480040c9000301d1030b03000c1810481c41100c10111200140a0030045245407025401050060300540d05503408114005007440c2c48d0080115882c20b0f5a0b59240031060342d04010103e40c40b211200f03031290410030600841030404030070b0707448000c030051001422140340e13904c0c407903203102c0d04000b02c2d0007500703012a1051044929540c011500004401405021902e0751031030717280d21503400b0780e5800d0400076501901040f5401c0c1408004c0010041034802c407919100001c410040021001106079118140c031b2140d6030340402480210304610b0108902c1c028075000c103065812050280f0304101134229042109841250130464401d803015031010303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949040863 1250 949039613 949039633
    0xd140a0c1515050f03060705031603020403050a0b0a051006020706051b011d0d020604020d0f2316140a060c030219050102090f100f03110c0601090f0c020d0f0f090305 73
    0x11451418803c042c800c4000140d101d03064140440d606104010680d034a62175541c54010358255001c050a110041540c01e20010001940400144180e240038070400c1c1800e140c5547d00c1010742d02c0040108400140c4d00c00f04000180e0005110001e80b80340d0b041c07280d00c1e80c6004500c4030083c2ca8800c5211040c0d800c02c0f0384000380d59101070b14140d50a2043d0f05903051540c40c8402030b0303611300d0282d070000e400c80c040da0a080f01203080b0319040c80d42030b40301d0342420041604003103c1c4c0c21150484d01707600005800c0417410950005a014a0300003d00480b181c41040305a01000039000d89030314410142442469009082007501c20f0000c4607a0128407016510040b0003418114000d4010411143c018025803152220700d24245130041000c810380c1d41d0301c1c0e0400d440200d0840103010486181110b040b802e0215400c0100c091007941d000c0c0c0010900000c00c1884880c00c1801e5a090000c404195080038800020141e400070342c10034072050754281410f00031030900d01156aa002c590024000f8013840d0300c4d20f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949042113 1250 949040863 949040891
    0x918150f01081606080c031012060519090f120302190201140604050118090312090b100b040303050708031003060c02010209030c0a050a23030316050d140a0c15 70
    0x8607042c2d400400840700c11841400c12104850102e0181c40c001c02d0028002451101d0100b00071580400603a0314025a00d40e51400c5c0440310b041d0710011a80d01d500c940420150f408800b0100070400c03040f040521071103155403502180b1014004005d0844044010315580581c000e8044400b5078201c500501c0f48500c041e94000d008001d200207003d214202c0b140418228909801070351b050390b031641410320452888080d148000c108480301141845040d4080003217104003881070203515401401c00a41920701000b80c150702c0f00003600400c00e9102c0078170050021940c0002544c0400c1d503c0307503a00c6e80d00c0c0c50b815041020140107605c024031003070810840032600350b41134024004149080e42280d103681e4101040060690941c0501e80d001003080408004010f415050040c1041002072030802104010307000c2819580200310124007180038112040c200302c0e041080341500c01c036a1801409095681d108091140300300c6040c0810414605110414400aa00e803821a218214020450400c01c4024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949043363 1250 949042113 949042141
    0x8060303090a180e060c0f0c07050301020d0b0f0402040303171b04060c0b1311041806050c07140613061a1f111609050c0d050f0f060f091815 62
    0x128a1801c01a07041c1300d0610004a4601a40c0311480c1c1c01d0922100c8000201d1541000c10b10f4001072191810024494400b0310007080014040000440c1034040c2d24240200017440f500e100d4001c901c1000208003007540280c4094010508110043e41c030380310900e40c1c03009203600801d80c41040c039001400064140c3c021000c400d14911078081151680d981e01404031076494001405090f108040c20040309510f040c2d4080c1c07030540b030860b1100b4003182c01602c55100700d807011900300c440d8890003d03214080c007550080d860750b403003140c0b40105000c0c0303001408000c0480130007030024a01b0b602d0740300620000c0c182603c0760031203401c007401400e00c00c1007409801c0b24007403004058402081ca1915252815040480d411503218421b0500400032860511002c008050003051806411803d001d4100015110702466000c0d440307848445130745046c00401c00000c0480a8281d0340300d6441211a07400035100e07804000da00100140551444045500240d030500041d500921002c82e07113070082018452002c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949044613 1250 949043363 949043399
    0x60a083403080d0b100c15050a0e011a33070809030102071a0c0f031603020f0d050403081503060a0c1b030206010e28050601030b06030405010209120705010f08060303090a 75
    0x18080340d116020313142c00c0c6c42d0f008807100090001c100c030780d0003100344015640045402508a0600040c035000c2c4a124a00715101a00b10b880c40000d010220800c603c0c1440c0e1254020508036551201002201b241c84096034030102a140000004139104041c044544c0940b503003000302400941d9200d40e00e10701300105031160200039a10034440c2003c00e004c540b610041e00e284505140d500c91441e12540090044000b046085100b0160200018410345040c503015140c0702903180000314243c02c151030082c00f0180d0080003071300c001211800c240301564002450030340007200e24200060300c2d0b0b0713000421154910380210480350079000040c2c040406a002980a040710104007803007075143c40b01c0d54500810751010800c2d0300200b51044400300c400c1116071215810030b42c1410002180304008000c6036058208407015241c0e40d60220340b42030681010008881b8600c0258050718607641801c00182a80c51012500030400c2140400500661420070407078005c03100040c58181d44a5648840c001c003055104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949045863 1250 949044613 949044619
    0x2181504050702030315012f06090606040209010914030115080d0219030e011b020a03033216170705072102030c01050d15080303060a083403080d0b 65
    0x900056100d500c04019a801407040306c02d4a8440d08885004465001440b940701002c141000c4071082408a145600241c01408001500303071850403601803804c1c402c00401ca45e0082d401000f0303026203030307030701048200580303c1246c600c0d06200e007600c0101e40108001c143c068507a128600c40440e4100000828040340500c07642140d03040420b0200229200c000807800a021409140001d90799600801500c8868181110028038464041c0c0000d445103845501c20380c0850a050782c2d91180403282486c401c1c508201c0901c000c0c4441c0c01003000c2c55a48a00e40070300d04408050290b0804000c0c1c0e400141c401c0400300011282c80f2803403030903c0381d1991080d1142c0c0444001d4915400004003400351324003d12078000300984480c002d5500191410390108036010700c011303036503a400300480941e04240e8010b4080c25008540380d1912005100341c4680c0c5811104803580a40c08401c081d2000d5003400300032104d034019502c203202c08055040c40e2001540c00003440c040021696101a091560145464800031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949047113 1250 949045863 949045871
    0x10602030c24010905060d122d0903170d02120105040b1e04050a0212180d2c0102010902030321150603041407050a06050310090c1b02181504 62
    0x10503180c00002da0021402c02040c1074000411040c80c0d1580540d0340100c01411400201c00c0710b540d144861040c0124090101303003d00030500070791001380170018510044034240c04075003410002c06000c002441c8801011910a184902c2500400c501a246d00c0b05400c502591034070200a0794501250007400b640d40202e14000151582d407a08125018100048a2132580d400d81c03003100b072001824009041e528032613000c0189100440301d100340c1c4c91141c403104007071b400c1000000035620f041c4003005a541d01004060f03c03480107800000e102d807407130003c41c1160400e401e242c4400180e0140c000240c001c4e502d40404601c80e82c0b120000b0300d21405001e410502448a0740d034810340c83c0000c0f14503004058001409100107030006502081701412520001c0440745000da90301d00040340c130038aa07000310001a40c08014408040707454220710317001d4030001505202002030407600401040048443c0600da1031a010500f00759143c0540441441031003540301582841d203910101e07004200b2043c0f9038029854 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949048363 1250 949047113 949047133
    0x190b21060121060b121e04080d270f1103030906161703010608090706031107020f28051504080a0206070c0b1314010f05040612020412060b0307080114010b03041406010602030c 77
    0x3800e054851f40d4025202e03803c000200b0703501c030010105545e070118807031120446202d00d0310004601c0081c1034841c0c501c540c003840c003602d0600c0341c0880c00f0070240d0095105026042080c0d0f078010503240d00c617100481451401c1114200b00c01c454034101526140c9400001c00420340ca40d100b501144039403011011500a03940c0e41c1d030210b0896540d2400b404000400340819801480e083c03100e40b0007003c00820030002c400c0b0784d40440403e8000d00d2060a281071040c0300410090078469000c0c1804c00c010f4902c0e42c2041d00c0c2a08007903c0c0c0e0002040244503490004501c02006128000300b0090029244426283d410304560b0801004403800703004012400b007000b0909940c42256007034203011150740d4080c28289419010ba59641c04e8500c400c041a40030b00c8046800340b0140000c001141c09104085100000780082c10304140e5070360809041c0743d05185222040030b010004040c1169203c0b0801d9a907030ba5681071440c100c1018030300421041c0a80d03000012040d0703000026010032010748060380c0c590f1031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949049613 1250 949048363 949048411
    0x9050c18010e1503031e0c010b0a0803040504020313061404030e040219052104050a0c050901080706081023040501090e0a020609190b21060121060b12 66
    0xc0d00340301d00c02003064103034000790780750846100000a01a000e42100e0500d0301c42d04d1a1901c3c20b00c4044069144030000ca0039040d0b03000d0900940d059010191140740e0502d0900c80080d03141e01c04c40c01541d01590700000810b08070301c100c1d03a04034900d5400840030000c032250480101c0017080140c90560001d1090b01e20b10010345880c0c070840e252650315902c902c65030a501001961540c001802030504440c5c03a440d0500d000c1b60b178a5816210318030540c0a4911100f6910f454000d14240f80c01203400b40001500610004500041d084141d8046082103403095403000040e40325125075400c212820540000c6803150031110320600d11081100312414060fa0382c84070042012150101000030b044e5005680400c0581050002401003110141c0000c41c400a801201e000900303403503004108250002555074010b0024488510f00e04403400c000c85558104480000d141c40c2c00e680d0b442054225010281280d0805580714100a055603401e0b1a20388503e420070001c524401c070740b0108031881e03081024170700319 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949050863 1250 949049613 949049659
    0xa14031c0b010e010e0603070c03020f250b04180f06120323180906031519060602070303050904020903070e07020f0f2e150f030519080f09030703020409050c 69
    0x485e001e005181944c0d034540c411108a03504000540541c003851000341c4020b0418880c3d0100404440400744a2404035a0403150107a1650311845403201c003030000b8401c0405800140724202d003d07176404141a0308445c1004000e1207158400500f10540070700440405030400340c40c82d8044c010340780303101c19140c84242c10100c4e880780c1107112480629240d501e015500d00385c10503e4203e0000380072900011550000741e500780300f094034400c00310740c0d0f0065440200e0b00b4a005038009001d552024050240c07860364050841d00401c020244203d8020410302e41baa00d00f044002c0040031440d00408090825040103900c603a80c0c81d04082807400343e444150452000054031648c040700700200d59140042c184506580c250500c2c44404000c2d44500c402900e020100016001901105c0c20042d201440c2d860324500d800c24001c0c01054985e00701400d0030102d262103080d603c4400d80e121500340d0320261200003904283c000c2d08020f6210749800d860800740540058881c651140584401080d0724509130411146 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949052113 1250 949050863 949050887
    0x70803210a0509072303070303081902130509150d0c210209011703041a0d06140102120c03250209060a030b130c080f1c09080a14031c0b010e01 63
    0x5644070600400622890b59503502c62820505e40c18200b15a40600203418003420754070a80000d05201305001d8021080c820003032003200c54210441c0340200100040541c244144100d03071164410000003014440300008c2d098024a000b4022080e5020304d01d40300002c40c903e4054001840d540020031501c00c400001480075480d0014040c03a8141e00c0d00d00c4021007508483c0550405000c140800262454806251000301d1000c6008070340b1044c0800d18041100c0d002d920007015885150113164450f60007140b40742107244011000c41d9114610000c60b031540c4140b640090764400e4000308a001201c5083c000704030b8620880e0b490140f505c0e400d080200c0c1c0c4129010140103280d51401191318030901c0081074030300c0c900c0b80c040105016515140a42401412800b110041d0406604a500d0020b241407605c0030782468209003122a04260403980d4400107498010b0041d1200d281d22810300c28104141c0e15100304220504000412a401280250001154071800320f5160b9103503881039806031550540c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949053363 1250 949052113 949052131
    0x10080a03080105060304031116151e0e011115010306181502070512030c07050607030c0509040e01020c011d060a0618020a0c080d0b1c0305030f0702070803210a05 71
    0x1d0f420036007000350603440070b0000c0b001d11880c0315220401d510305100120030012581c5d40309140d6890200d440d40c5403d0660500710801c001d070300c070410010707101004201c8022868549038040784d40904c01610b0b08032140070507601d603116411b03004524110000030103040e030380b09480600215840e21070300c200b10790003440b0080400c820403048070424045640945032150180301140d82c8141d804540c968182d01c2981d0414112000140500c14002c1c104052a00240e10307141c01c0004005881d0020094002d00d29040c0c0304d140c50303040050150000b501540d00240c0c841008100c1d15080c180c001c001c1030350320800710b05280181400510040c4080c0700752400c640003e05044412161848008003d40c0b11840c0e140c1401050400d1502290490340503003504115820002030a8601e4010006000c09240c1c64082d007001031608d00b00000c1d4058240e9800c0180e200702202c03c0e40300d00006904020340350f0450240340c8004121940f011800039003622051300514281c80140c0c8600031900241d980840d22120 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949054613 1250 949053363 949053377
    0x10608180c06270901321009081b060319290307050607050a1e080a0903060605040e0c19050d0b06040b100206010905041401050f10080a03 61
    0x140290240d40c285920203022029121540c1d8000c0025080750414003168003015401400101c0d03200c441c0031401442c10040300c20740d016624082130600a40038401c9440441400b100c5001e52000d0400d00184d8152801800b001d80c00036504c40c0107020300a41d10900000d4498030f00c241c807510039400c041c6207100d0006011503141d543c50b030b440b01001c4e841c11100c4466003030744c4052617a64517950b00c3c10f4080e10640c004640c1101e03143d1200b0907160164642000b0f03c00c50b0204240400600c00041c4040c103607078401080c0b20b611092020341101e1804071500a440c4250004100b41090b501c442e01c081541e2081004008658030344040c0300449050072492100740d848002203980074a8601c0654160024441301046029152170114a03801c0d01e07800100c44800c00070342070110529090183c40c00001080d18080000041144000d686da6018410b469129a6400100e0184271007401005a0041405c0092000e400d10038240403034108202c4080c0781c18116807801181020b0089117600c081501a55120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949055863 1250 949054613 949054621
    0x220e01141012030c06020a02070501020706020309090f0a06050a090203040b0a380a06020a050c0f060d02280c17090114090a0932040803072105090106031505010608 72
    0x34000c032480b003030160b044c00343c40c80e03005000030800d000401404040d0360150a00c2440e181c0003903d481501e41104095400c1400b4002c2a91925407005d0342c004550b42090f00381d502e80d145074200030042c1da00181d8000d549c2410208082105800850169114003c019a203642c0c0f4511030f02203590000302d03041d500726116824403c24040d041c14551021a00c07804c4002e0040000c00540150460703800880560040030908050000c244000304071010107440b102c03868218000090032074800c4001c400d05941d404070310fa588000c000b020007142a0601c41422248546161300075041900304541107071a00c80d4010411031100760101611080030040e100d0704c0a0081c002d00205254020803482e03508051883d0000503000424042d04031941600500d0001c1800303807081503035031042d12141c0407051612003400d110000740b4540440707a10220525100c040784407582154003100f90000307032419425040c4400d10054100c194031180403244940320030350019a2203144201605c0007441904042210300d0001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949057113 1250 949055863 949055879
    0x6071b0b180126100501031103010e0408070c030c0b120907080c280b0a1b030f0e060d050f090f01110703210501080c0127050609220e011410 62
    0x15003c40d20b20301c01d003c004018400350901d9030001c102c070900c02c0c019419200300207a50305440390f803400001507043c80d80b4640c1044081c4209401c0a8030003810030000280900074004411446406580d101204c2c4002070307031718440440d00e504403803a00415502c4290108100420000d100011201e10b0006443c0095a94040007646140a044c2a011140005002d0030718640d80307480c1005040404400ca45030004810b008200c88110544031448898103204140400d400007501e42e0112032501c0c01e00011a50000481c40902404508200b000c0c14030052020942e140d2a00d00e206191030700031100861814041207080e1825480c400110090400489002c01e00c6103195815500b40b1080b81182c9010402614040712402d80c00711b001c54105c074010a1603907900c0040074000300340d02888409100d0f00c4420400311700903144a0f40344140000201c18403940c0b10b0204540004800d003840402c0300030081c17060030160003844a0f2422a500c0c003070f16480220300380443c1ea07018070081464180090704103402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949058363 1250 949057113 949057127
    0xa09230f03010509061f080609010f0b0109031e061413020301051f0b07060e030f07020a3219032d0b0c0702031c0f23090d020f06071b0b1801 62
    0x9404201511000203e1901410001103000300d520702700004241200c0f0040504440c00c0480c61070402081c0d00b02040480c1401c10a42c1d192240703250305421403007051505100030005c070050010521032840070881070a5090560081090081d0020300c5039640303110003402004c0c100c180d01c0408400b0440203203c0100044064543e0b40e00c03071400050810504015540307590000c0d0480500e1480c0050154218100210f042000781240068110034080c1494070102d00b0740b03981c80201004501c0c1c08040c0c0140e548010543c103940f0a8003c1d8a18252681061b405201603c004441600300310310f6240750303060300c10308040c14682c0c0101004079103844040c3d0812042d40701800583c0e25204420610204004019040020000380e8440d100d100d00c080c0e90103401518000c0070b039001c188140100c654002c141408541d82590100d4892804140601c00915083d103903402d45500b00e00b0104480c010010307000d0038102e011030405e02c1c2074800e0b95560706107d014424070000142410b41c0030240002540a050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949059613 1250 949058363 949058401
    0x311190f061d04060b0d0f0204060f0c1110050c070b0304020105040b1309050f040b0f06010801090b2d2d09041401050f01060f050315060a09230f0301050906 69
    0xa403070081c00c030444002001d64006400c010038810000411151100b218403803402c1f8050410b06c00e60500d46404d2000d015941c840107000b05014240c0b00d0841089030307588441403d20001414808040c5a10700010116007141100100c0f030300c0340d080b000c24000d1a030003d0700d104581c140e440d10f10345410030000b10855080901ca1202056169601040036031705030243c64070411014200640501e0517050407001104050b09082e5990601d60910040c0d03640305d25094191000c45001041c8080508041107900c601c4c0c500045600789888042c1401d40150460b0388505501182c40c02d103076440440e2001c01c4c5400c0101400355944184015121606241300c441e0750044c026403040070f10214000866003584c07070460b10b6420010000c00144521034100c2083c450000b2186000380c2580781c00880e004001c00c0e200f15003441080c0208400103903d1140d1000300140407907410090816411500b50400d001d121001984140f00b40000380429040507c2098400c00310000200400d444040d00007200e0b1a40070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949060863 1250 949059613 949059647
    0xb03072117120415110a0c081e0f030916181e0f2708030f1807060206090c04020304050c010e030106090e160503030c0304210c0311190f06 61
    0x441401e450340c031030001042c401c0303000c2c03820081400c564005060444004419108881d40144100200035610070b4007401d0706540714a90700e5581c9243d1600314140c005c9c0d036002c00c240d02c0300041e40015031444d04d8080c40c020810b42c805c95000c140c01020740162605640102d890351031340243c0c0880850001c0d0440001040740000c540040f0381140205400c0d15007401220004546800b1440720200052502128811400c5001088149142d541070120711000d86415902c00b0381c8400300720030303101e000c2d408159020301c142183e00d41a074454029403914012901175450340540c800b01d0340b041c149402128422a8010041c080300c0082c0001510f0400d2460801505517684000c041040403091094005003003402000701045061000000000515508405c0c086e0300188001902c1303031000400e032420342d4540e034030f2150001c4110600390403030800f0000180404003840e03400014043c5400c1c80c0c601340314003a01e0400203458040d22843c4c02c2c0365144501300c1c0d01030486400700320091140e8119100704205c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949062113 1250 949060863 949060867
    0x4091e0c020a0b1302041e05040b091902061e1b060c180910150201061a04120803370c110601120303020f1812010b10050d0f09060b03072117 62
    0x4000c04135044109082c000480c540da23542032001703000003420741640c007800003801030509800a14054520082c1a00000d00428020420150003081005040703280055030003c40d4070b4203189110024a480c0740408001b09020b200d002c50b0b090281c501c2101c20348180d419081480d05071003010f00c0786411009056281d01d40d00002c0100c0e41c081d012507c10181c03174441e40085000c0342008580c49442c81080482500c0403407c200070021180ea0b408243c07420707074001c00380b5070f00c9a8500558402c001401003032100c2e61800305c50b001d118290001c0091072084103c4104000c0524800b600b0340e25460381c201d04000c0c0340e200f00010455814446010040980709143c09801e001541c00702100542042210160401070500d1008881c03d002202104114030900244680c01507180441e0030750710006100c0042150010b403d6884901e1034000519001900c1c1c01000f1080c0036042c0706000b0303c1480c1c501d034402d0090b01c02c0020229030701914503e01400c1041a1601d100c400d503240018082c03e511222040041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949063363 1250 949062113 949062131
    0x30f0504052b0f12020c0a1a0306010c050f060f010501110606040f090503130821040e060d08070f200a0b0a0c020a0b030907171f0204091e0c020a0b130204 68
    0x50752141c060f4007442049409192045a98080d0420440c02d1010340242c080d0201000710b10360a82204103002078090025549894510040b0742d20403000740d0240040c443e04181419401c800a0300610985484040c41d815989038401142e0160f002c294940d520b601800c0403035000c0c0b030580c0c4006604901c2c40c6d000140b03a0702c00c1e0344850850704000b800c00f28414140d00e040207000c4e0240400fa1140d06030b601142842a038080c0350740d806015501808070710841d1000003032140e454030252800c51b030741c0040b40e29468001c5407910200c1e01e110316200302c43c808200101a0744902a0b048d080d442284001d0007100c900b41840f040e14520f0304844891002c120411210b8009030711f400407800094104000c4142d628909240014500420fa501503000307c3c40d4a40440d40101c00890b015208441400f42080d103042c0d4012a803000e401150014011545030019502c605200d1107aa9404210804414001003c44003802d0341c45000280c40034000030442d80000d4034a8555114400e400c0748010b00020f14144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949064613 1250 949063363 949063373
    0x903021011092706010806030a0f1106180f0f10052808040b09031201050d0c0f08031812030306060f19050c011505030705011412040f030f0504052b 65
    0x2403000d507451403c0b0f10f095005100d07050441e4903d41d10a80a007803400503414400042950350100d5030307001d003005011205100400c100344c8211880c0000c01490716499000000100e66402400c03541d452058500401303030f00c00790074521384d200c0e586440100980790001c00501f0603180742e030105251844031143c007001080d040780002c110000305403160b035504140c0d00d041e140c00c1644580180440c503041d40240404424040d0000c01241918020f0310b000a4281d040d1605030382400807604004201c2d4480c40c0c012942c0c00e0000701070302100541d2100c2400906035201409840e8003000c1d100300d400d410030000200c403810020000c10f004040c000c1b1182c9009440510940d82040520391500003d03000140e14241100900454000d2142180409016440c000010796500f0a601ca0141801400c030b4003004410101c0b4280d07200300d90680b4868000c2c0c60b040c40c0804141364100d208a010500c5140f0100240344a03000362002ea400150190103008080203103072004024032000303586030300c00d03c0ea103010010b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949065863 1250 949064613 949064629
    0x3317010e011103010f060e03030901120b030105012d14040e030d150314030307020616091212170c0409020913230a02091c0201020f03030f0108010f090302101109 71
    0x541d10492882e00e030750520000c60713403030b9170036138132400401040c04980355081c0c1c0c0c08000c40302c4864003400c1451200302e0380b00c06c0ba8080c1c20100d406d11b9040d403a200c0001406400881205c210f40c110664000080310920003400c411031003405007109582d04588038980c1403c141d44100c1d00c1e8600d183c112402c3c41c040c0c0054205607a0a110035403c401c3e00c030314040040015428172045c0b0140e1200146085141010307000b503480c0f10092440c1981d00e0602c4800700030364002d40b4000040c140039031114000f015175080440d01c214144aa03440011500075082a280410f000301600600384420040e103403e00d884151030182d000f031103c446e0b10034075030700c000548200e00340310f0351200b1444ac00804109601c0007491181c030349401000c0354400c0b070040011600075036880b0030803454806404031007460802c0b6400102e1501707401e031810128a2000009000d554901c1d035900798100c0343c1c180004e01c090380390812844103481c4c44102c0103000d64000f886010a101c20350304903190100c240740405062460403c0052110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949067113 1250 949065863 949065881
    0x160b040c180e1204080d140408010c0e030f2a0303120708061f0903140304121506060c021807030b031f05010503070617040f060f3317010e01 62
    0x725a80d0041d22550076030601c0389440b4618601c0c1c445081c2450251030399120032140c56018100300944c004000a80e8903101510083d03d8080300170041403030001c01c0074100c030001000561091155092541907101c0003c2c1c10070f0159102006d80281c0c40e491001d1a001481c42c01403280d05000c00c0c055003034940113490385644105442e5649019904150f028000d4013140c1180d10440e8040105810820380d40000e01c0e20120b83d44400c0c1030540d800384e801e0721401c5020b1500644a40040c0c3d11600c0700303210703801c0c05040c03903d03081d070008000890743c0301c0060321101c0221300001e4001c0448401d080d007940b030b4002c4041d40064541804a044030f19800000c0c20150714202445110602d08003010040d012842107a0240c1025401400024140f001c003504094030701e050303400300712109030010b8200710100606c00d194550120f0184000c402c459440300190800750359010065480207100805c80201c9c44091303007000d444442d00010141000b030910758000700510040455900e030380c40100486401d02c91ba0843c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949068363 1250 949067113 949067159
    0x50c09040c030b060904120e03120d051b16081c050c0a09080309130b12160e1e0606030601030e030d050106020d0216090902220b0103050606160b040c 66
    0x700d0552400d40b10011018007002d0280a02508000002e4103e010507041204181010b100c0701d40e080e8000703860a09080d100c1c024240020076080c01032502c80d08114010364001d034120100004600710000580209000ea065a040b051a0640441d10400080500c202d00355017407580300305004186405d841d0103603182003000c1c07400102c5002c4203910444c10005010341a02840c60043c2c4040014940840c1010741c500c42540ca0000c4013440ea41c9002c00c0c0301d0080c2450943d802281d0002018000b02d0342481240307400380c4054000f840320a501da00030340b52108914070981c46901e0380414010907410083c1210305155652620b14000b5a04001400b520003810202003010341c10110001d0804550030801805d40d804042c403172400700000c6110320203460303c0f07a00c006844191400003940c861100b09140b40ca002034045940d01214454200d60340540080c0ca0910040d00c6810030310541d44074909400e400614500c60040005252400c1c0c244c03c140550b404041382c9881d0090402c40078804410064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949069613 1250 949068363 949068383
    0x304050d031a0906060a050c12040f1d07080613110d060504060b0d0e10020d02070605010609140d06020c030c0d020c010c0b0c0901230d060e10030f050c0904 69
    0x111499242c010082012042184000c052040501140c400c0f40f01030320151144002040d2154220302c140c06545400801c2012030314001d9081203041500c2e4440d008151902010380780220f842d101c00700f40e100d2003100345007004001d6a100e00048850210260541e80e02a802035124040c80c02140075010000140d120003640c0c548140c0303079083c115003440d480344c0d002e0390500c01e04024421030041580d00445480001164601420901030309041e00e801150601a2000c65a12400042a805041003c1c410201007081d642c80d15400e680d00350080c8900b1031212050125810141000d09400c0d0307441c7c0c03140310090700340070080b4445411a0010300044080b94444c0c044508015410062035a000000b801c0a020482540d107da828804000f08040288040002d005c1c2059116504030386081240755440d401d511107420b00d9030f810780d00210040c0340d20743c246503011480c454403005040c0281e000c9480c0e01012880c65440d01005a12204180e40c24058240e449204d40c0b240207850744610b10030400c0c51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949070863 1250 949069613 949069633
    0x51002010f0506030601080d08040501090b010b0403020907020f0c10050f03010914101a03090f0609070f0e0c120403021f0507031d0c0f0a090f0b09160c02101103030405 74
    0x2034200c2d20018842e038400c1c1e002d44010001d81d8808a0081c403c0c0c0c0392441c242d405540d46042030307400742004140c01488804490000541174103164050002c2e80d200301c45d0744907140c4810104985c0c400803d1b100e24000e0304454030401caa8905070020003410f00c41400c1c03850818200c0d191052140c4c04c26031000225540340d0740c010141d0b8254001e4158400480c8a480c1c91190030a8032065144c5801c0c03c3c405080f03100040030070006281080380300c0d140a051002c6444138500070a074180c41340c10760322801540b40c003403e8022038035403000390300c251007012000e04150801c1540313540c5419010380548154254040d103400030f6080400d03150030f4460307111003c0300400d4609114000034203d4001d1000b14540c0c01030460200826131012920b88040d12040700e90400103c498000204407206640c00200030525005904020b40e101382c00211140360b080325000340f1aa03601c43c4060190141d1224000090701d281050f000500d85590030302000c184920b000007241d0a603040d80f40c40c2d85d02c2984e042e0b403240d00044481c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949072113 1250 949070863 949070891
    0xf0207020111032b060509090a0618020303030f0c0903071d0a06030f0f020105041706040209060a05310c0302130506090604030f050a0c12050705091e060a05100201 72
    0x42c0740d5003007600c011460104030789050403200d041e001071321804d1034804200014120558014030060b040003441042c4504240c40701036610304450604490443c01e0101107a01da1001d03000c441c83c0160082c0c080c503d10f0b41c950307185091800c001400394895190a10211300304d501d042040401034007030101c600e24494032040680f141c05100500d40b18166050420620004003851100d0f19510340c01034860b80502154401a140c42c0644d40006060880c102220f00e05884000b400301d002d01d000f03959500c80c80d210502400704000c2c4034000e00360886030086069170000b00d0b410407900c0e041d201c00001d9900b149090042015101ca0030f80d0100000c0d00400e00e1820303140911443c0d001060101d40c01881c11550002180050241c0e01c005044c0442005000d002d00800307000e42d04180d82e1203d405410703540ca0300304054850301e0040c400d44551045410208050804000081c000c40a12042c25008034800800c140750075401800ca40c1c112002d19400603698460029000020340c0540011841c0c0080d0082 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949073363 1250 949072113 949072127
    0xd1407050d0e0615060d0b09190b0306090c0105160812010e0f240114030103080a0f030203191d0d02011e0207150504031b03030519090210080702100f02070201 70
    0x1e0070075800101c00c0c41050013140c0c4e0148643c1d02c00fa100349446000040c02e038001448640038458208440f0400c00c10b00b031903200c80010f00429020703805c00101203998249940d408040300c1d07044c41ca03403107194070112941c041e50146c02460410351000100c101940d95041c00f54204030030403d1000801e02c014050b052011b060760381e01c288600241c112034580322102d8201c40350b803401d030040b02c0c1c600a4110610303039201d40344c8551003254102485a0b2941d40385064046540480380800005141581d040041482030086a009071015580c08100d004400400c4004000740100e04c0031022900d804412501380c288080e944a155035000015a80e050b000004070303650f4541c12801c0e02078030412003007001030404151003540c09020000003c4690740d5290075600c02000c920903568007458112802c0030907506400c03140c0704990031081604041541d41d180b4050b0345034408002c2d88060703000c006542c03692252039440e0f801b00d25841214400e0310f80d07213803200440d120745040c808050340020350f140c19540c04c02d032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949074613 1250 949073363 949073381
    0x60d020409021902010c0206010608090f16030b07021603060b04021c0e010c0906080a050703060b070f1e050312042108040c0605030103030519050702040515150306060406050d1407050d 81
    0x30300000486c040002c0d110a01400703880140104180440c180c0e071400c000403281e80c4041b0044030380d450103900708840c01c0702d081d20040341c03203080c1c520000b40d803a480440d184248861444201c1d26090460740c81201a201c043d100c43c2d00301c5d609100c441c8a0403914041007220040141000420108101e201425150a040707a0018082089000c00040c0d900211181d0b02100c94000083d4540741e03280101c1c09040d0541c4002042e840100b689010b01c035401d08146140ca104090300d44601c0424001410002c2c0807072005031045c1c2041c8052401c80f001010340c3c0b42d020b803207980701301d181ea0751003048050101d09a04da48000641040d00b000100b1440701000c40c054946401c051f0308640c9556001000342c4260f10340071140b03c0c0b046108828440c000c9054407045980100240014a40003c8024512140c0100140304000064180c03020842030070449001e0440078181c02c0c0340505081003a070b15984854420070303025550345001c00e0f03808030085000d0b001ea0003c0e035444e644c59000e00c00032403c0e111410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949075863 1250 949074613 949074617
    0x329030f0c030d0302070618050d02011401050d03030507140c010e0601120210180306050408031504060614091909020a1706010c03110a06240b030609060f060d0204090219 75
    0xc03000074601d590000700680219040d1601581c0c1e1081841c04401408034040ca9019052030248080c0411201144000a8070801d40c000c00400c1c0c1e48d14050b04105100380304064002c1c1402c158400070a104e0382009900140701c1c1000319081c03961072503051070b075488200400c9a43e5552a408212624180111030040048242d01c0c14074131196000140f9502141c42918184107407440b034044145032800000000350b4001608005074039143c1442c0d140350344111202566402945103202c000d1800f0711035481030319500d545090070903400540440c140e5010440e02c079401021b841c1080e03118800489854050903500c0c0e00542c50304442c0b00050b0507009aa12184170780c81c3c1c035500300f02260741e210722040f14164142c0f800c0780540a20016050410201c210094600c82c140120091800400042c05043c52030702c0c0710702025103a9901c09044d1601042c1d40c42030348600681c010030443c3c0351101e0f0074051400c000300a01e1804400054a40032a480703a0301c01100c0340c3c0c000c20001c42c0c0031031441d10035070b240c1054 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949077113 1250 949075863 949075873
    0x1b2f19060c0906030b0609220c0206070807180905070309080708210912180d0308060a1502190c051309020414010b0a320d0f0c02030a0e010329030f 65
    0x4040002c00310f0140c7c04145000d0b0511480d1000c915540900c00a2001c8210004201c0c0c2c60810b14002d403919030403105a4045a001c901040b40e0512a26103654070911607500144140d080c4207800001c1c00340903058404041e1918400c501146503000104281840b40f401c050b9541d404407042c900c04800c160541700d01060f940c042100000b00407e40c0401a80d551451665651008440c0344510350040b0703a5035003051301900b20310101604100e0741e0740075a43c1150000107a035681c01c03400901d1071030525500f0051304517480400004009280180314944601180c9200c036841e0300205203c0002000079812030303615004260298280351003034001aa0002d116882e166050011501407441303520450710400c065141010004c680fa0013524030504400b0380100c094941204111000d030f002014407400e001c3c90b02c0f0341d500079009244100304201070036801071401c2c241c44e02c0d425116011800c00490606884550f0400c032611f18aa00040c0315100d25440800d9115150605140c0380101d00440c10710343c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949078363 1250 949077113 949077131
    0x804110301052202031204080a02011205130230100b04021206060319111c06050a0608070201060b040e04050d030e071202030f0304091b2f19060c090603 67
    0x2c0a951940d5042c0f0300401c907240d0543d1020910700b21032100c8891000d0804200801c0c84071300441c56a1506000b41e0729040c8200c184c43e0900100e80d02542c007130460018480001005007040342c6841c4d20b4044000318007108400c8012560103600480920300843e0308400300c2150120035501c100100520241c0d0114141501e00e540d0342602d100243c4054850800440091400c55507030ba01492072141200c028041c640c0c8003411074110b0741007a94102c014403e00743e05225034100900c540c4040b9000103040041d039074544002a0f50790306000e021081195200c00000c1234440c0c0304c0d00203000030442e00300080164030b024240750b420050703036054a10805042880c41644103000050600c19140182c4241d01030300d066200080c503202070400d0707000300c6000200f400190b070041079200209680b89100c000003001c0e00e201c000c0320a00044c10101c1e151080701d148846209590f9958001003824074000c0780d00c048100c0442c00107801101c03d04403022074951074808080b547c000107031b00c000d00090400b0b0100d052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949079613 1250 949078363 949078381
    0x611030a1d0d0f110411120f0c0c060114150a0906030c110f07030b0c0a050f0319091506060201020906040510021510030618030210051510080411030105 67
    0x807041c100d20091160303504009485560704802505560b5022208800f4801c491030072900a0042084442c8540d240c0840f0242d8240b040c41100c01d4401ea0701d070281000e0395032000c80860b800e40508144125a0180109803d506042007a10301921644425130601d40201c41001001d0040c004860752100301400741810ba00d130001600010340d82c081c2400b003802910441c0840d418001500c3c254814490350392080500d090100e00300d010380e4040c105034041c60740c03480c4903840b25108082124000807401c020b4010500d0304040a580c000c41d0401001d1005601c46160905665101d4002c2d036101742ca01c80380ca07405098912811004003510b00003075061482d843c0004d0014040e81c4201801340740520401160940b0a00205080540941c0490034a00300540703070182c40c0d80680421a1100d00e88a01d91196072b5008210056040e031560052402c4610100361f0000b0b045e001c1d121080c4080a80d04004895581c85c1e941c42c40140705030760341402407410b401c000e4007010704801194040d074034280a008000d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949080863 1250 949079613 949079627
    0xc0d0201120b060f0708041809170703030b040c020c0f0306070e060d0f0c09030309062a0c080111090301050f01030809101215140312161401050708010611030a 70
    0x4182060002d110180c00001c03c00d03610076012400c521000000b580010020000045d109542901c00440100001c15a910040b200c1e40103014007008000c00003030710221444030007000420300c00d20b004981741d480d41c00414266003003c034205016030800c8071851524141002441500c0e10220014401401c2c20000504183d601030390590142200158540e070006450b044001c0c20340140c101049034514010008000d42c2440c00228001115580c3c0080c2040c42004503104961890f1000d00400c407503070300804240d0f900c00c40104ea88500c1c50000117404442803064410307102490b07040c159243c0214080500711407004143d0000d44240c0030040c00890070030b030151407044200365040f0500f603420800c02e8910041c103d06001c5164140350508404030301c250002800c0715180780342f004482030917078200f548503807080d000308843e0042441541e0100d1510b420b012100c40c0225080e84180010321041070948200300c61803804981400010004c10b41e20601c0ca0304066076200244bc00d007a040c6070006c040c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949082113 1250 949080863 949080887
    0x60708060f0607030e090108010b1207030c0b07022d130608030702120307060501081e0303060312090604120605100f0305060606030703140405010c0e040606020a0b1e0c0c0c0d0201 79
    0x5400106a441c205402003001740c0485100610084556940c3c0c506203002c3e050b00210b042c024880003004c0d03003110400180007010340b1f0307011031880c043e41e003000b002c600390380c10030b85040c0da0090121140c610710f04002c0745445030146000200b003090031081d106101140c003607075001c000034501c0d003a020401d824020064440c020350403140c40c8003401040c560180366000d220009022a49440c000066218000441e41d12030700408401b059003a00c1c1c2c0c3c090136164041228895019006000c111a403241c1603030040004c0e0800429450501d5100d01e58004000f8001c0c42c102c8030141c0d01d2091003003c402c8040d482e401400720001118441c0e04650303031143c0b241000b80c2414003c22000c8042030844d8002d0700b018040b0034261541200900d401d040c0a40a000242041c03c0455201624200141003034014141550803603001001002c0042d902e017800d05c403004005005c3d80320314010b070542c2c030702982c40024003031903202049a40b074a2245a030740e0700346143d0783d0a16100390010100c600050342c10030048062 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949083363 1250 949082113 949082119
    0x40302060d15080d02030a080c040e07080903190309110303090303120402030a0f230c2d0d200603040c0e040f1e0501051305150a020d0f060305060708060f 68
    0x1280c901c200e40000d108040d81050601e4000c6202441c40c045c0d00001401c411401ca668008443e21a9a4140c099124501549000803a00400074000364000c503101034211901d481100e1810b01c1c0f07003030104116203001141200190f211030742c00c000d0280050080140e03903c103e001c3c502d02880800065581d100c1e448094204002441c00138082d9a018001e0305401e5802c040b480409150b1f03480d0021610007510468038428061501c200300103a40017a2000c0c1d940d5000d02000d00d0016101070102c204d05c0203400c90960886034020030780c56600c50329102d074480c92144003885144014941841281c40c24662280d025000a000300408100d980c15000c046407404505075801c2c2c0c55605190391140c451440242c03a200417041c103215441140c0c04040d500c18000e80013044643c0741c154441002007804940940181c2c004250760000c9903400c0c5c40c25030400468030340189800d00d45856941961a000b403501c4030983d0300c4204000b03000d020300005610074011310701007541d0700d032403030004000103450b040d00c0340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949084613 1250 949083363 949083371
    0x1b031e0304051509030a1a0a0605030c0f0a1a03010611010209030307030f020c090f06030705030c030303060f011704060c030c0509101206050603040b06210a0201030504030507150b04060b040302060d 87
    0x1040e090b84000300c0705a000d01178140c0b1100c0d8554145240700b06000c041103903165401d0340021b220001d40d84a904203035040100130745146a1b1035801c01400c0c2c812002c41c80c0d4440240d03080020b9804144090400701c2015540a5899602d09100900042158662030905900402c0161010707a0044111091158181058880c2c0d00804030100e203411404103500f500f08540606204000480c413a02078071400d811001c444145448009040d1541d01054420b0b405034418408145289028180c08040b40410714001c01032801e0214502900303c41610161080c0395908482405154140114808000030b4148113161828000c04680200b0f080c0f090303001084103060b82130010381419040080101001043c1c581c03241030231b0400707075180308050711000d20510504200100003450841c1460003290018081c011080980c0c0054018000c002d0048080103800c001e140005441c2c40502c0a240310700c6d42e0300160444098041c042241c1213030708000d055200500040006944103002c444044111540100d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949085863 1250 949084613 949084639
    0x11232060108251101050f090708030406020a0212031201090906181109150d05072912190f0b04150b07060e010b04020712090906051509030f1b031e030405 68
    0x4034440130031002c1154079424103050204154031110700b140200305040c1078800840d6211201952446240b1500d4090707081000407101603e05440851000360f12082503d2425500a88401510200f40c20016070745a4400e010418015140700780824103840c000b0b4601090071913120032440142080c01e8070700c03644049002581091400c02c880c00e4101016045a102018500c1c25980b90f48282c060f03a0004e07444000c0b007881e003500c00703210400710b180360044261030000426010f0403007003401855002d10500481d607865040c00d151180f020303a0b0319499800640c0f8808039042209684940300060222102000c0900c03200d6500000c50f2100b9601c25400103500c3e00c040101c501400d010b0081c2680140701186c40024414642c541c03203038140280e5500c04aa070f032188110421640c0d14002e080e0015060140d5141050040000707003140100117044980030030901d003031076141440e0b006041003c1054103230448180e09003000381c1504280910391204421201c040703c1c80d03480c0100e00c00c0e64420b640001c0f080e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949087113 1250 949085863 949085867
    0x60a050a0216020409032304030b1b090d0501060308040914180615041d0303041509050a030507051e0d0201061a2505030a031505010e010e01123206010825 68
    0xa14441401f0003144d9113035100e008807d5869400038441a10010700301000200041c40e00e404a040c06480c1421072402d11070765405000540240d250110303803a66989a01002040480f00508001c001d0441c0201e0002c4e201c1d000e07403840f140b01506178000f0300980c8821038504080130806a90104105503061129101640000e01811030700a85240d041031310b510581811002000440c419402051040e04100301c074000e13042202c61034a0050580d811400a00d00001d110300018041c66024100b10b480781501c0c2d80d03010f669980124060700141c0e0051620b00e44058080c01980c0050160090318561350720140c840c0d031803e10802801e86160b40303541da1210040d014200c3c1c8500c00c103030004100c9840b025901e401030020510f012110400411a4030001140c1d8403540030f0307405950040e03603503524180c401c400549485900511810540313031500142c14070750302d0754000789225004200840702032448076040058000d401500141c1003000300c0c403c100401d032a103098200c00c0240c1603901150720b141d040003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949088363 1250 949087113 949087127
    0x6131b230d0c020f0f1903050c031308060105041e0e070b0c070524070b06150c160f1a0a031103040f030906030204290706050405060a050a021602040903 67
    0x98500d5100801c040d11862610351010003840b00780d8003200da100180c191600e036555101030051240e0b6000f8201000400c0300000c0061009100e0305000d401c02002e03003001800d5821490100001300340c001c00c10800f406042003d68014241624100311000b409c04911040828941d0000308807a141d101310004000b003080900c1c01806078000340d0b525a81c0042c442c580b10303500d510031107200e242c44220004500031013100c00c0501c00e0302e1002c1c036840d0481c1969122a040c100420040c0e02c50014111000b02c806514002d01c144044580545018815401c4c2100d45e0482078002d01d040304040a4144810280781c00d50940e141e40a403105501c3d4861000c0440180c00031030008090076002105101c10880380c001c1e07400049229441d40c3c1c03401c9844117800c400b24019441023801908082051a0b102842d240c0050740c18000040ca83d49403041c951030700c0c000d560060b43c2c111f0345903000004010b0203441038410541c200d03510720019442c0001c540405904111400070291299079904000f130301301030080711 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949089613 1250 949088363 949088417
    0x2d061e11150709030b0709050d121107120606140f13020f0f030402181006031a060a02030301081e28050a0b01090c0305040b040f0203070b1206131b 65
    0xc1e50762014601048014038186640c8403c540e029803580100340005d02070090340741950b00240c49401c050782e9039111403c004190441e10310600026944001c0d04030000d2021001614204000000d000740500e00001228032640c0408150410500c5190690f500c450740c10b060f041040314a03005880220030400024840c400c1400d1034080001a0911103d0b0315001841c0302d280200e4849004402401c5074801100c0200d603151003c15102c2c01c00d1089600035413040104a03045103c002110b0381d00c0001c80c100354031410000000d80e0002c0010042007800304802000b504841b41c009410250400b501c568030100034022800c0c13007040b400e4840e00c0309002c1914048035070708601103c803200c07820300302420101001c0c010070780ca00d8100f040a41d60140a4001c0d00d0181d54400c50540d0555501d07111030400440700d010490b8035002c3c00d100069081343d003d0281000350f840c4440c03c8582d042031010400500350034a5503a10742d03410000d1040440c001c0744620f00c600c92460900400c004500c1507018800c1c1c0e0310907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949090863 1250 949089613 949089643
    0x120c04080604111e0d15020904020c06061c03020706050f1c09060f151a07080309010509070504060b0d0504020a0f030516080708070b132d061e11 64
    0x410001484000e00c3c82d44100003007a0b580c600100e203007450524480c41541401504500071106410024445125841804102800c01400c1010000004050b40d1140f04078012590000e814406030303107444120f1980b03440f0309451200e001c0080d60742c0030303484140340e105000c00d008002c6a462a4401000206c40e285125400c0720750083c480000448010406010b05490702481c2143c10f0311611564032031964107101d485c80040c1c5503460000d200c28061150450380840c0481802000e000404c0d05015501802009001086601d40703104200d151410b1a40320754030850610303000b04030f031240c544115000e00300c50000105056540340040b8418005a6210780282440c01e48000240403001c15684818502c0310440c01e84155a5004655500c58500900c0410b0f0052103081090340b8810000b8580202c850b09550708403596010820303051900e80403c2d8200824610b20207800c0d40d0300014460107049107003003151a040d10055a400780da96011041c405100e80b034003c41892032010440108811024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949092113 1250 949090863 949090873
    0x9030b0411180109050f06032a0301021b060103030e030c0f042a02011e0903080105061815042606073c0212041208090d061109030d0311120c0408 64
    0x51020342004200481b031004da1402e120010800c140380100303130703c1d1140e4031580e20051190b4103007100c1000c1d46031100e01e190f4159820412040b103c51804180440c0b4142d10020308010b6245042c058000c400b4110b042c0e101c0d801c50074074480c0680e5020001c3d5940501580c002881c071120300c8100c00c803003039942e100840081c07685c161202115415003000c2400600c4c030302e01e01258a00041c150041c1d803021a0300030081445840140800c3c10315201a080c00380c0c090151140012141d80032801418403c2c010210084000400384810f642c1410314070084d01c0d1180d000ca0b4410b006050460b01c803a00900b4400400c08844403052168400b486965030845c910740c0c00203d1280034143d000480c2500405003005401900da92a402e20480420380702114000d06038a18807142c2540d03112240c0c2c1c403500540d03034000b20401c1414040780c610312500040b0790050001d150b481d0b12000801d4034040151030100708160810810241c006555010f0b902641c40880c642c80903501c40e0074a9021a004075080081c580c80b403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949093363 1250 949092113 949092119
    0xa170319021812060a0605010c02090711070b07030807090b130605030a1e0e1203040b06010c03051902070504050604060f0302122a090c0412032a030908010c09030b04111801 76
    0x2003c01c4c1580580580345040180b07503502d100640741e40c544410040d511a0044000900c0140652000380000c4a40740682c0c101c6602c4010414040e00306d6881a0000b81013001000707000b80e04102d40201500e0594111030605107091104000078207a0b000c0c0c0c1041103004004210b0400351078100c58900d0302000200b10402005088000c0208049401d030503680c0714490800e80840c6a01003240d00640d044214184959580401560780c400991422801c22404005204101444000d1402c081056130301a2080e146018104020b0b03c0c000b4103071600ca68a091020450941865544000c40e5415a000640c0c0246c2c540442c0c04d001074000304284130354012a80c01401d0b04400d50800942c0b000316a6000d2903210700c90b440c40c0900480c0aa10720a45039084a200480c0c000e2049080304900e152955404540c1e400d81015400010441240844c0450200f485448030a001d07245443c0340c035190075a02c0078510f0300c13a540c8480e805803001e080e4042410303120855031104500800c422010b01c90544d01941c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949094613 1250 949093363 949093399
    0x232419080307020f0f011b030e0a17010f020f1c0b040608031909030f151512032003031902040312120c0206060a150504050a080a1703190218 62
    0x40b18a500f2440b590811280b454107282c0305654038040401071b03603881c8000070800c0c031900b0079040107081a41031000d00d017096107076640c40c40740e1640582500d0b042181c00c44020070140313081d0380c40c0000d034000320350040c440c004010030100156000c03261003210f00045070a421135103a0003441c1e0131451039000303070501c0c00104042c01c000009001d8181c85504c02840c0d224130090494500c4d0785408020044040e840b80e000206849071205043c010001000003100a4804180c10800e0303529807041002101240c402004e054001e00d41401d545610381c1c900c21003101e104040343e26880024001701e4540040b003026500090300c2c0d8180d030080d69111980c0c01041104040150050707140300c200c010041d0030001c0ba821214808039895000740b10292080d10300604101d81880a02140004842003110500c4000340a80d11800604000c042c1d11024201c4404c440c14080d0048004040d40108142c0030401e00440c4c0c16042c5074050255644800181c031402da010000b510302443c102c0081e4000014008212801c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949095863 1250 949094613 949094617
    0x324060512070810030f111807090b0408150c040906090b0909150a0203190504111921020f0402120910090203060402120111040602012324190803 64
    0x903019100d44202d584814046a030410126141103030092140000c10000e0315030b8100385200d602c02e800502c202400800807030a00c00300f800c400300e007885021061041c001d403c0314424000c2c056071034802d07180a0401c400329036a80101c6002c0e0bd100c10302440000c0c0c4a082031020303100a0925420705000c91641e0303a071018041c1c440d04108911903025140810740d44040020a9540600b510311214901c2e51000c100384002e41002b007030318827049804c2c050420b11040c0fa02c0390301d110314400c2d54a800c140300e42c1010301c03000040c6485600c00c81d070000c080a00100c0701c0c03020642d991000602d0903900b03403003c40c4086254203840381c207450342107400420441c410705107203508540b05402c05000c45025400140d820000e4507040b1001030b415400500c0854050f040c0450b00312440600c1000220b5041403501404c540c80d840f81d400880140d54840103505200900c1c094050440c00310003405030a0b0821900c030030107a106007c81d420a071200d040c03100e807036034955001807110700d56441e05544204d5518000e4035266 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949097113 1250 949095863 949095877
    0x6041205040b280e0306160e1903060c080420060409060e0a0c180302120309150d0e07050a0501030905210d05010915030f03050c0a080a0219080a03240605 68
    0x209004107105103c9502c25402c0c1e91150304001c0040c500d60700d910021032904802000c83e80c041042e0714000c4d00194541c0e07490340150040181550003110301c0c5090082c116440b012111003045444010b100101d041d5403030003504000b10311140b52480644c000080c60602c10381d84040003036801c043d80003511400350f2203141d200741084a01403002e91008582290001c0d44803a04a00b010382901052000d824000c00d1004000c4d05002100e25107206000040d4100e4203910420880900c0010082c040800a004a1500030031180090c007041d801d2200044124400e401224100743d6245031060500008010f1940b42c110b941904422804600350050182d81c404124a61640d0410000060b03030346091080704000541440c254403d50b0542d900c11102c91a03444081d001c010041c010b003030030b050062082c1c080b180d10601e007055031003aa060b0003a05041d02c118101a0418142c3c05000c08200120704130b0f4a60582440d0015110305050b541c02c403900714070312000e00600c5010718003085854021008001c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949098363 1250 949097113 949097167
    0x906050a0303271202032e180c09051806091005090c0915040606080f040f050f010501140a060206070c0602090a08070810051b09100c1506091a0306041205040b 70
    0x81941000500d0704d9107c145040c40102c8040ca4a09040400c1144c1c003141c1c68010017200ba01c1d41c480305403500c0c8031a140c150842c005450303480d07003440a00c6501e032312256000c24180002d4911850501c981c2d5495058001a00c280325444000080e52104d0034010b50031011401480c2404609055802c81d0010503454030280c0960b15080340443e50a000b118590311418007000070301000d55855483c2c048200b4004000c40d400c0c402d500651402160a008941c06060000191414044181c023000090061a4171400039500128103002e80c55501000034004160004009030743c1e07800710000b144031100185d004d40e07554042d10360041580369010942580c00d5510365814461a103d80f00c05134070100700020101d0010b41c0c10070010740e0f24105400c1c181801d99140c24040e070300004c41e40710340c08121101d01240209681d500d9060100360391621820402501c0142c022010036a004080b030382d900c601900141007402000240c42c14180306404a1740a46906504076841c1c55a80440c50400f024604480c0f076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949099613 1250 949098363 949098373
    0xc040c02030705062223100b0303030711071206090c050f1f02120c031306180e04140102130807060509010507110f04061e0906050a030327120203 64
    0x1140610000980d00da468015024082c6505d41003d41340800e54460031072107821101d4401000414510307010210644c0c500100c1020000301000c1e13450910542845c10b5180a1401c802100e25860000590742e10681074200501b00c0000706900a2620450381c0c01032111a1221514604200c119003000c400740d40311341d050b1440203440e0002c014500c0e0460308003940222003050042e580c3c2e0a506032500e203140940c01035426990141e1110304081e4000780c0c3c1c5801c0e03603000142144580e540285110003c2c5031914042c1d4100d210586102400780c03207441025500e0070100003041c10710228580b0400920b030700030000c41d80c440001d41000034400030781c81480300f1070140780030001c2da8078000c00889400d03020507560710385001e01995072110061000d5025541196080c0e0001c1c0f440d840754071851003d004038164070814880c0802c0a0501d100c80c0d41c0055880904103a801c00c02a19000100000d483e13050070a0312100b8035040078111243c1060f643c0b0f4050010020000803200e66000702d40000e14000d0341036074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 949100719 1106 949099613 949099631
    0x60f030c1c05010f03051509030f0a21060810020a0e060c0c100306150513120510050c0304020901050d0f03030e0309030a05010204092f09040912020c04 67
    0x45411314824014024003400700200c40d0401c60001041030507140100d0482e8a03030148074400a9003980125a400e0094040c103560658a00652000c6003500301010001c0040c1401c1d10402d00c4501031404e942401c0070290084070182c0c141a203454803542d0910061000390350102e10319400d1400b8078600e03041a44e8506006400c1d880182d40c0c0841e046041117031103840030903800c03500385c14000b01b0040ea440041c80340b105c070000c031586002626032003203103420007608041512001d82d80a078940020014030388042809140940c3c026124840d2a0b82c94106015001449002c040d0120644940050000384a034118200e40b19807641624240042c03107012034640903034500c08072266500890f042c4009480e500c078010740d00d045815568004645850035500454403c404400038160025080001c1d0311940c0100c0c52140e171020b00004424042c18009460f000314030000c52045007883c07015 = true := by decide +kernel

theorem cover : BRFrame.Cov 948920863 949100719 := by
  have h0 := BRFrame.cov_init 948920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948920863 ≤ n) (h2 : n < 949100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
