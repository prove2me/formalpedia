-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:31.015607+00:00
-- url     : https://prove2.me/submissions/4e97c6ce-7fdb-4217-a8e4-f050f5916806

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905035971 ≤ n < 905215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905037221 1250 905035971 905035991
    0x1206061b0f14014a010b09010b0d060501031407110f030c010204090605061c0b0409140d0806010212030403140904090620041415090d05070e010504060602031c0e0d03 73
    0xb1102008140031140769101300f140b60034022100c0c401805a80369281c11416a11000700f009000d00100c2c0040ca4100388004000301c5c210920720018920480104000c2c000d11b035440c030044040b1391000000e41c207009040c601217660707584102c3d14424440352444c00c85681110f540d454900350740c000c40712a000b581d800a402c1000c000349d4020200100011120581043c80b0002003a00c02e2216000241019a903510900c21a6a40c3d40c42400d03003135000b00c0140d20794410412050f13076829016522101280c0c1000c00079006610000700a00317042c1c508003200d42075407190f81d010b540003005100c3d400406c60043c2b00c01380c0c95454a220301303210b86d0301450001c592044000311404c9040310844055450a00c108028000030801000d045400b920541e51403040d819404c0350b89145006500c1c055a11151111009042c80000102130094500300c6100390315690746d40c002c11003190070503ca55409a003042c81207440d0841d55030074083d407200c00c48a01196450704105803a051030404084000400e5950708810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905038471 1250 905037221 905037251
    0x5030f0c03120c19051c090321020a260d050708160912080421060507030b0f01030507020c03060109140a060501050405060a11100209011206061b0f1401 67
    0xd20b000041091042ca00a00c3d102e210383c42c0c00c2e100d1440319003450301a80100410204204440d200c0b85214403110681e841c0c0301c001801e0f4442031205440d01514140701d12410072141e5a40002040b06030010404d058141d56000031520542240c4a40c5564090134441182092001400c5410448400150381d2030400c101a1100300c01501303100c010765003841d43c548580e4025038020199046000c0c0e04e5480c801528010510344640d0300300d080c0009030365214040407420b140b01120700a114607414003c07542d80f07540c00c4003142c503a466491323030000d40240314948950103a802035030001464070585243d1001039012034980402a40641e50384d41ea1900c4a241c0050b82c09a80e5030400b990303a00070f01031a0f107824002803d84c0950f0180038807a00700000c1d20310300c650050f07840c925080c40c9402981c0a144094001000a401409506001c00c0d2046110b0890b40c003248170b8403043d0340c242e44442006460790002c440d002503245008840d4406011002004506081c010f0000008113000105000e140b0a01603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905039721 1250 905038471 905038483
    0x1a061b0c2214091e01060503070f05010906020d051b0109060911100e06072406120204050f0f010905090102162a1d061f0909050c0a2705030f0c03 64
    0x80c0720340441c1909000c00301c100458481c600c2c2d4030510f43c4e100207903002c2810500400066020076070510407890002040c031302c051b48007001c480c030988600180a80c0da0b90240d0700c400d00e58a151f00000c2041088030845a02c84428581a07203042000103445601541c4074021540907202c00da4000c04542c00022051070b11541c416803144107450f18031412040c0030081022400364203030061200c45400d0407850b828084c007218154071004242e040c041d0a583e454100c0174444221800e81c01142001d0018103180b41348020140100c0051045940c1603107425107100c01080007400e407a80a5408200109041d00c00c2c500b45507100d4000c0352448200c520120003040404c680303100409803540c06400c1084a0000c1c070020366602c1e11a00c02e9010b441c0d903002d001803080016500d1440411055400d580b610355808030f00d45068170b20300201004540c4441c01084610b00403403100c0000200c2d0045480300414040c981c80180c02402822882001c0c0c4520010381400a490b15980955102401c2241c1c80d103000c01030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905040971 1250 905039721 905039741
    0x81b1014030f240603161106010306050103050712150e120f120108010902011e020312090c0a091b050f0705060106020a0b1f0312020f01021801031a061b0c22 69
    0x2650303c2c10008012408900004000c030b0303490300d213903070700d01071704a0007290310402c070101e203c060359802d60310313480c001c00140000c3c001a03e0921900f280410113107004444c0c41a030903000b0f0800c100d41411341200801411020f11050f00501540b2283c440d660320200281c11910b40040380140c88035600c0340c03100d411020507404485541c0c10081c407c0003503600904008914541c074000341614103d40041a450743c07150401e1000c3c2e240b020320810219013008288000401000c890300c080a0340d8817585001690f081e140105a8810b9814002c1c404e03d00420080030f0042074148120700b0f0003040d440d103d003805000d80c13203d00076030803124680c410000d1500304541e004015242d0341d03042c080900c130546920b42d0700e40401002107070f580c142c0c07a02e010f0013000a200a049000d0080d0f40e0761990300c28000383d100c0810511404242441c288078100c01280d681d80d60040c030701405003030a02c43d12000410b120b082c0f5103614003441c014030010500c90f4446005d03440ba220101503030001c03540f0b1010383e10b100301d60190b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905042221 1250 905040971 905041021
    0x15150509090f0c030c0a0504051306090e0a02011418060c01060303180b0318031204140709062d09090308010315140f1008061609081b1014030f 63
    0x2c1042800c6643d80c0c00c2c0d82c2c0007130f000d00d120b0b92140281002030b2580e20542e040540d0059080440d41e42e03001c0c068110700180d030000e0360244219800032080c00d030346c4c5405560007404141015407c03d220707100d00e4058036406240c8a40c0390303041e000c06800308000742d210f4046c150450351500814000c1c50b0b0065001649041010780a002c024509a0450020b0101404040040102d0000d10703030400d804100350703080c50002086103001410507290506114040164822050180b06c1c3c0003d1201c0c050300ca40402c075402d204404d484075114003010b0540010104c00d111100714603642c0411268500c2c401e1520440c403d03164004c49504604006a290711001900d00d000f42c1428005482030b140098065045032012001d001281c8405141d440c00240d00e401c010110311400b4100148851411070840100401c0c1d02c03100a45074440041c0c98a56000540060b4440c15019007621a81000140e21140c80480d1400852182c6220b81000056009864590100f1a590300b40f00a00100100c5441d028610f21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905043471 1250 905042221 905042251
    0x501150b090616022106060139080307020709061205100506010e1806040e060417030402011e1e08090a03031e050106110c03010501050a091515050909 66
    0x550440180c410780301024011840458242d111030184080302d8680d0358001c1c6800d4606820100c01c28440d104024202842e10032000403800650081d003040042e4150b4083e40300c01100c046441000b91284040c0044a40078507260000c04a100c62000c1c2d07014100f6a805030501611b03150709031040d0b800c5a04030f41500c0040810001c00920001a40364400040040106191703841c1c20058845e03891049032182c110185410400010340500b003400c0c460202210308006910b0111a016580c10044800501001c00111400d4441d26090082e56000e4030516144000400c0301c44c814a00c0034039070782d100c000305a030034458003103a183d0750044555580281c9070032a4146030021003c1c3e52254035142c0a814942d480f001d205000c03200d42c0308a015100301207400d000340e5950b03410042a00000c510302c503000d0f009681c42280c4c503140c103001d0181225001001c80b81d0441c1861070385402802c0c2e20602d03030002d410b80140000d01c0840d0380801d00000f1515164651100b08500074440c5040c0002d10000c41c40c001e003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905044721 1250 905043471 905043479
    0x51c0305011a0a110c040e0d02010f0e03030402130207060603061d340b0a020717030315010809030d050115030c0302090306040320150103110607050d08060103061809050115 76
    0x40207940c1c861005262690034130f08160101401c0041000c8030700d0701b10b0b060213040301c0c00e01d0740010000c0c1130060703981c000c2002c0c004101051040340c140f602c4400701a041000131401501c0d04040c107000c402d41182d00146031003030380c0e03030307840110341c4e09902c1180c0240d203402991005001d100741d24605030351000054504903180382e2403002c8503151006c001449442101e0303006030314643c0d00c0c2701c2005440503800403a81d40b040f03888080c1d44ca0a84c0d10840b05840d140f40c485042a00c0c01000b981c1c0944000f0603a000001c102c0300042d04d10810044c0a124244400c0c0300c82000b0f41c1450050134005c10701c4400c82d880c0100304103401030503280c504e25160141f60041001c0516030324001446035003d070301441c00c0366094a0104020740b010208580c84600ca21a08a0342e402c0b040406003140d0403244030302d84c01408036800c84244229030054110103080c641192840104140c0540b007810303030049052400140007034840d000ea0f2415034006000e00d41c1c01e03685107800b6040260903c1240340d40411103155410310340c50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905045971 1250 905044721 905044769
    0x50412090e0f010e180a0b060f1206010905060612070f0201050705090a181d0706021b030309040e01110d0912090509070f14030103030c060606050a0c0807050703051c030501 76
    0x42c031980c4c41050900780050f4060150000300d080f9141301e00300b9035024010380e0070941a400000e948044c850b15004444c1d070600d11385042c0351804d1110701e6014151503840c210f4404c0c0180700040140380c000c50200980803540d2011f8100520601301d41d04c41e403581d0000507000a084420091011040c804100605034035a5501c00c028403c80b59400840300c4040603032032861000e0003203106a084030550000d21004001c2d0003050500541314581e003242c040c42c20008940c41450006012075405030410055900182400e8000c81c04a00d0700c4400441c8c2c4070140d1540b07101e143d00144c1540310841c1d907080c1842c01c1080c070600420150300d103490592403650a05000901991019059006100141040e0700d001400364090030562950100d1180e2250b81d82d060150211842c58011188985417190110b1038501440544040074560707641d488441e83c03030340d070352003402e5010071425240d91042050000004004020004a0082c4984aa05100c09584000e01520f41c1070304141c001401c0210b42441c040d803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905047221 1250 905045971 905046001
    0x105040209061605033009161203030b030d031409010203011d10030b040c05180906011a13090204030b010b0316050711130204151e0305040201050d050412090e 70
    0x1140341d0810b01e0780c00a45003036441e62050b14552414210540710180c41c0f16401e00011070320000c0004004260342e1003018448e1600000040754480c140d44c0d02061220264482c0315a007400e101e4140041c41080010019140220b0083c21400090715610129441905400b400780c01925107002903003103506001d81030040c0c0b203d83c00030000351036017100003841c07200300324880800454002e080d0900700c1c101400d1544945030a40a010f02030365128509880000c6110242d0b4130400d0f030803026100076400e2504017418140312020468030910203000c4a1030b44c4008020160040c103a10340c0050f6114a1454184034000b4142d11521000c0c0d02481000414504001603c1e10381150380b50450360782c1d07024030b008a95965841d40407600060300c1901003282150b2079000784291400903e80702d00b0012245012150341d100c0306030016110ba01c0e118000c00d158000d800a0f60010310504281e070800703400131340c1541114000c9030b0548005912201c0c2e06191078004c05c2c1140130f814040c1400c0224035020042007032a10b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905048471 1250 905047221 905047237
    0x100f06030b0408090d0b040507050117040506150126090d02070b0909060409060c021b0a081e072c010515161e050a020a0b030105030607030e07090e0102070b010504020906 75
    0xc0094800341c03945c1e52607032141946500ca00340503002d04181c204150344d07101901a090210b107140e945e0141309014003003028401c1e54054028009543e0345002c4150070745200c011a070510540d800c0c1c203d0340860301c10124141444c0c206100141c0d28150110900d0301040001120644d00005402e01103140d0030f0040b03584c1c110054908030305603150080824018074904202070042841c004461503156030218604407014030b5420404116899281000300c1103495101d2505107522541c203031114140c2c80c0f900168018510001d0b80c6a8940d11507038103442000d10a40102c500b107180f40740d80c0240051284e00d5003d0001500c00305c102030070b01c14014400f0f01c9115429500c00b0308400c580f00410480a05480014001180c060680c070064a0b0140da581c0400d0b40c12031041c804040045820146a0b059a048903001002040300d601c840500381c00424583d0401100360040b0207010070005818003d0701c08042e0348500040e44d5807a907013002c500c004010b03004113100340c1c010001540340e0350710201952488 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905049721 1250 905048471 905048483
    0x20123070f0302340501260c071a0403030e011b0e030a210908031201061d13061a030403021f0b0604150e0307030809280f030320030301060e0f0909100f06030b04 71
    0x141c0c0381c108c0c0116050141c214010080c00141c81d0f201111024004003034015486618180078488041e2003031400d0f03510750060080080c48021440e00054426541300e61000743c040c0c00c0c1c81a00345581c550004218213020406180c0031200c500402890b031024524008240d860091814140c41007003003a44940180308170810402d9007810391031440c518514040900e01c004005000001580400c200544071500c5020480d00050400980c001030030003c5030311070f0303505502604000508840351880d10344411100100035a803040c2c4840c003501c1e0040144044c010b103401c81c801201c96940010b060140c001d4400d80030340c200701c004000283c5101c5c296403280b00d04a6403121803c13040384081c0c4202088040044ea04100f10500080f031210103c0410252806036a62407181c2105d025507400c0321078441950842640100010021184103180300d03040d2202c010315100201d48603000141200c2c03070550300c0440c9608021000b1400c061248521080c12501890074009580303075460700c0c00350860090000e000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905050971 1250 905049721 905049797
    0xd080f0103050a14031b060106181223011e0c0e1f11120c070e24060909090c1f09031502090a0b0304020123070f0302340501 55
    0x3c031041031080d11131440c4501c210611840280b46d0b055520305c0d0030710a18020919807201c1100440c0341e425040705903100320001042100081c3d80b2a060460380940b1035054641c292076640003103400b80503055018030020070241c04843c10a036180119590b070142d1a003400103824108000e51540302d1750346d030290300000034901540d80002d4280c501c02044501e217502e40c061000d42c000c44085c0c0f440580004010101241c1e072154890205080c9008180e83c01f07180161129a90842c2407413046e40d1016049001d040c65040914400100781c42d01401c5d1882a1660400745a40030700b410402d14012026980031000b52601c1e08810f4081d102181c00c1c00042c01c040d0079110f1183c1c6000b03503a0121381c0c000c203000c0d0000c00c40c6640d80885400035041687e0890020b810a00300c1452100c40c06440540c0d5900c04080914007416070742c81540110b1304500032800d500440041141d486800c01d00180000c03a524151500c0f0026200c0c031128444030f6420440c144900e0380400d0003074104070b0a028103030000041440700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905052221 1250 905050971 905051003
    0x302340b0414160807061407170f07030806040c02010b010c0807110303040e07020f122d030a0603060e030c0316140102072a03050607030c0314090d080f0103050a 71
    0xc0c1480a400c0d040b02c10f120380c0115001d42d04420110004858244042d10003145e102e140c100d4a1800010760015803080c1445500f001c01d0001d800e03002c0161070119810b2800340d0420203420306410040301600407440001c204262400e0501801407059050301c020032900d100c62001030810440c110004d018500041201001c200d0802c4c00b18080307450042c2201e842e40c0c1c0e2402400d01c1d22200302ca401d0014011869200440880003400d4a00303110484111802d00c0036504800c000c3ca81030708682c00a062034060b0501000301d0340b10085014461900000c5072460071824804240c0d280b11314550220b51041140c0c83c100400801520000c980302c0d421035800ea080c5090001c00700900740c101902d00d510020f001420844007010b5521794070038a0310f581c40c524152040e143e0300c81c0440d00c0b019003d600b01c0c80005c0e40342440380d4400b003469011b41c200040d1003a41901c044d0a140c00403901001e8540c411000c0750080c507045002194401b07071003d003807940d943c150786e070785512803880200091141011030b58000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905053471 1250 905052221 905052233
    0x14041a04080708010902010f080f070c060f05094902030706020a02030a141c0509070f0f090b0d110904080715060302010e0109081f1b0302340b04 64
    0x500800c051801c5949854483c5407542c003c084469089000c1519090f00070301290203007000e54031445107064104080da6a008061314085105403041b68134554401a180c4004801c1c81034034080c031010401800300d0000302d01254001c2143c10061020f816030040e80604820039a5480b0051940100c4031589402032242d003039107903000d1400b0041c400340c00440e00d41c2102c0e50005c06003a0384807050f0369500e202c110400c04501d481c81520b42c8003412a81a50664824100e560001500071441c50120b070441540d07030351032000c0b19005030048031030420000c00c1001009054050f98205071400c6456143e100503954500f514001a04a564007078060140018280500070701079420240e0400d81e20f00c038805841114030700502c640e000803408240840c2d04000300d544208507040603258210014142c420001050005400c00e0104002025886e071071107081c040c40520304841c0b00050f40c2c130302585403003680002d45000c2c5003468a9a002c07072600916052034039801e4403880303101600031413404021340f81c5050403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905054721 1250 905053471 905053477
    0x10621030c0c0b13060806100e240705060c040501020a03030e151612050603030a1409040e1e031c09060b06041202010206060607050606100215190c14041a 68
    0x7900b070b0580c10000080445804005080034044420050f14454840409540011003503032406e82060301c6070f40002039240502540c0d1f60340c120043c80690b20003901e03002100c0000c0e800b5134042c9075500c041026001c00204000f140d13048a8042141c42c102428440000c0d82e0340001c40b03000e002c15880e03546001b02c64009012a0700001004403982146141014009014000d054045000200e0491200b0030701c1c1514498240603901c01800346181600f03606044a0b045030071403111070600740802c804001c1d035031503109044103104d58101802524101180c13505882c804c0440b00c007199002040009455241c548803120040c42030600094040400e0a008009060b00a189500040001008510103406000800e0003503c01da0032940c140d52603070103015050280000c0181154000e002040c01803904c54000b911101080c81150b54542404806d09103d0300f040c1e4100700c0a49030854444400500c074040c5225410060030003043c00125a60000b620348100c0c46200005e005000030307504189501011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905055971 1250 905054721 905054723
    0x60a050408060a0c0e03062202030c030a03030e06150607150902100e0a1707060e03390111061f08060c090a050306010e06101b150608010621030c 64
    0xb200c2c6240b501c10310050043c89040c20003400b1910390710b0a0522440d0000d5600d1040f84090424a85c0a0304611809144000b200040b41e0500401d4000d00f0070b620200101102e15001e56000f1943c95082c0540702e0420f20080c1420f1010314240b4005210b030388500f82101d00c13050380000e031402c2d13864110006030000c00d0b60880007035000503107901203414103a0100e4180d5014004840c1d440304c07250359145041024580c1d44090b50386401001c0e0812600c1d014081002c901c07070000d02541c026110880090741c81e00c0f1180803004510850034001d102c03162240b00381c1e0048442c20b09103004082041310003039550310801025030041e900d002d464280301803100700c0c2c640020494042115950b007402c4201e03007000d800000d0280e0040f0807403000019545000280e0300c2c100da07901a0308091075107880302445101c44c0040d803d40184044100e2080030f031440d2a16a050355401803140b04a40d840c00c41c0101c05480865010a00f1a0705110050000d1920f61224403c00200c1c0c42e81e90780070305410b140a80e90104e4000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905057221 1250 905055971 905055973
    0x2010c1a04031e0e011704031412010f0e0402010e280303080a0b0f09150a0f14010f021b0f1306080a1214040b0c0c060d020c010e070302030a02060a050408 68
    0x2050008040e00220120b50400003022112000803448100700c031000212980300340014406e1050b081c01c0c8078200311140d0068021718080703058400200d007640c0280c3c000c48440c00c1d4911144010002144000302c440050701d8142d50f81d180e2800c1940009181c803c031a590584aa24100b064840e003500c41c03916034034a81c0c40040700041041d924200030708039000445030031a105090540803006071404900210342200000c1a41a4513180d0700102018850080c2005401101080c00801c3c10040e400d880320080c000803c52403030b00030390a4001000025010036280c255071100300b981d1464100c44400002c80342c02554080d44401000d4005030307445001582088a1b14905403003c24140001315160140324012510412403042c040070845200310b103c18004494407042c072091140516120050280302000c004854248041ca40001e541c2d41c01070903021030707481d800902d41100420038041c3c520400344520107801013a103581c020070b46030404480003c1c8030303440014540c0400303400f40003a1400340460b08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905058471 1250 905057221 905057273
    0xc110d050406030b091632031501030e100c0c151d0a03020304050418050f030915090a0905060102100608100f0506011409040b030a1a07020d080402010c 67
    0x2402411561240c041c140001341070034000501ca0030701461280c002c0b0824404600b40005d60310049a060410080030000404882d0020b13500d105580040c09621071a00ca9481d500c0c03d00b0030750000b40c001c0181509052500745450101400c00c0400d6410817922100700203d6060940e4804036100d1850102c001e003a100e8664640009030b01075030184000740e50800e00e07024115140040241e94201d01d4034000c0040e802080107110904003900200705041650803440c0c4884003e56030388e410044e2499103242d40341d2000c64a144d003031821030701000310719580c0c0710030324074082c151400300c1e504504500401940ca51103c0125020317134401c020800c0b0745811040100221a05d80032101c1e1070300081a071400c0810f007401010300300049244240b50103040d05171601c1e628022058000c5151303410120038164040da44600f20400d80d1020310019504a100310245050051405610043c1410185c42d40c000c56100b41906118280c01c5110950040e409003800340021525240c030b00c061426041d4001e080b04050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905059721 1250 905058471 905058493
    0x2040504080d06120f1212020d1e06060c0b13050318040c1b110310020a020c0a090e0601030f020310020f09040506040b150d020c060103080414010201140a0c11 70
    0x480054021020b40090610015a0b120403400c030060084102a1036100c4c03d00700000003400000318018070f02800c0c240400390032510040481243c00a111180940780c0342d0f031100043d15039030f076600c91090201140801556040050040140f00c00311002010410580d0200e0201d1507140404155603612104880d51040140b201c914066002c002150081c0c0c2400d0704001600d00519404403580724201c1120201a0700b038a40f40344417201d6590740d175014040d6860325a11455240002c2c00c0750032040c1c0081800303004080070b001d580400e90b489070f1710b03481c83c10802c2603070103101041c181d04490b009045100030840702d00004e405c2c5040150b4140c50075100140c1800c004c20100090312121404640421150303850f10280f04c141c0c3d1101100c15070200079485221515036510000d4080d07850960001403c18030f07590500c518000d000e8100f580d40c107001040810540600d0781078207032800c0c8284000d00101c4c5004844046151018000c1c0344040c1c1c4070864040c2c1130b4840e000f5500c41710340c01011500c800c090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905060971 1250 905059721 905059733
    0x6040207081606050105041a1e031603050c0301020c19030311030a060302120f0d0c03030f11040503070b16020d020609100306050a08070b1b1c031a0907020d1101060302040504 77
    0x388402c115421401c040c000074007442c281c4203100d0301501052607001034000d0b103001c02c1079506107000c40c00d610764848440e4039501d8404101030440d03210a81c1484070040d0031410040d1502d0240d94049100780e00400107000b0060001c586500400524250783ca0042c100c3e180c160045c00b00e00079840120307580407041040401c81d941141c011a4000e56038142d000340403440082d100d1084400b851140c0e802007003190301440c4100f5415402900031b00d000a40340700c050f0095811740d403100401d251a90008a81407010f89000c2c0f107035000424060b4141d501d03118149030903540c0b103c0900c01c0030348110f907410100303403d40d00c0340b200300c85000c1402800103115402e02ca00c00f41c001c1040380a064025040c2d1200400c03059030000b00e00003507880600115050411000300c040c00c00c03843c8112800315000741e100b01c40000500010f4000750190b40d840c08600c460000c406000700441c1c0b401e4a6224000d5801409a06c90300031400c0e510039102460002100f01000454a003d000d0355800250071074a044200014411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905062221 1250 905060971 905061007
    0x6040e090105100b091f030f0504150c090311150403140a061802210106030212030c06070801120201030c090503030706020403110d081209010b040e0d02121603080604020708 76
    0x21980c003281500f02e449551100ca0780c05250b0446401003294a2403540a5800300c2a0180741e07120741ca4080f03120560309070a5020340f14150740407240c151100c0d4070250800000e0040030340c100c0092501c9010f45286440c6d030f82c08aa21140040c0c060101c4601075658081e287d0b00729400b4542040031400c110b161508075940d981c01300d083c10789030b8529015614180b9240d01c20340130401034009207150701c040b010300791144a031840c00d80c1071640e666885000000680300d11804515801100b0302130350f240d0f455000540c0c03c100e4002c0520040010b1180140b1031f20a9140c80c000c2c1c929028640080d40c50040c620075184100260052903150ac8045040303c100010381d0000c1065078442d5052685021450003440401c5100540003069003e05021160191145030001d6070f01c0b5941d1000400c8060381807021078200d0b4000c20019a158110500b44000d05404202c00454030004803000d03403a0811917810b148032540360705030003410443e882e80418a0f9684640544661503003105c1c00603610790003061910f030009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905063471 1250 905062221 905062231
    0x603181406070e0603150105091804050a06050c0a0807120f0e0a2009061003090606060e0f0907020607110a05060f09060a05010b1602240a021504020d1106040e090105 73
    0x7441d03d2842914608004094034096120814540304070b506080055801c2e030030514005421a0041002e0b10b402c040b02d8041074001d500500141841e11114200081640c50080c403112204c0b404000380c0c0703004c03503009d07044580c450100d06d03004101c3e214042c144005400030121400507903080c00c1e840c2c1c00914022880001551103682e94840d41c49000322011034500907168070035840060741d0b000480600b0b205080b484403455514000803460442d607100411640560000c0d000030f09841203040040c141001c1c1c0b40c000d24400c940e0f280007403510344d00c029a200001481d031703000c104203036810a00f00384c410442c0e1560300e40d001054400900d80325810144d1228115201c01d00e40c031495012800c1c40c400303445142d05a6642410302480c1000c0303c81400e103080c400c6541280c0000ca40ca00549924041c4891110520b4039040c90343d82d1039820703090080c5000b941006402e00007201900f88001039450000680c0741c80d0740b181c8805130304105030307001034401c0c000d6500441a035800c00d000c10508240652101d4410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905064721 1250 905063471 905063477
    0x1c0b0403091805090d05030907030503040e01092d020903030409141f0b0717040b0c150105010e0f040b04020f07030e0103140402090a1508100203090c0d0804060318140607 75
    0xd40c2c0c4100d040c0155101600d880b807080d00180751604649119000440e40006400c0c200d801255590b40c0e074a00c0c0d5032103548188002d21040c0c0c0103004403e110701401c0c3c12000315084ac0211241110101d040c020304841440d000c8582c000b8134030045880c207200382d90080031601810040e030074a0040201402d84102d4030441d503410345200c0540d04051440c03416054900d090861030030320f00c00381d6410194440c4919500c111103070510000070a0a442c0c002001d150141002914500c2d4580b1000c030a0408103801a40c144a0200401c41d19602c9505c020f0310903150844001c2000f000900225000744541a00181d9140000a81009240d00188030351940102a40d0805c0120f540c01100a114242510025800707403a07540410704c240e641d5009080a9a01e80402e0a101540d4416040c6007075601c00307246400035000320030071101c5103003880b51103a50901902c60003c03002086d568070b0745a02c02c5010301000d0664074181e00c050600082034403444181d10200d070410780b1140507981aa01c010440c3c0c46000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905065971 1250 905064721 905064749
    0x801140612030f041203090f0b0a0f03110a03021309111b0105040b180f06091b0402090102120f1312110103140105010c050a0203031201050a0602010204141c0b040309 73
    0x3185500008445921020100f007504040c1407105c14445c540360144140c0c00c014284030007041164034210310800070401c40740b00315a65002c07004064034803204420301401381468034540c1c0000e441c6c80422258524203e180060780c41d1000ca100ea400000d0642019502500e8071440c1c81d01140f84100400081d22440145018680e4512000d82a01d8007100d0041c201210303034020a549030700070b40c07003101c20f045034005135884801d1511000c0d103049021110549180d0104000001181c420007040c4081041500c055151082030340001c3d6996008a0702d0312104140081ea50301915a40f03004d0314203200c5245040351005545800140741c0d4020220140c1d0000481190034045601911501e08540303400180105907a03e84401590300410020741a10a03008081c0e400b00169403d1004060303c41c00d2003101c01d401e5043c54207002c1c1d0618182c00070025a0300c1000280316030903080c0e01120010100301c0d180104180032400100481c070060400402c0030034000103000c101a0009600740590b200402c50400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905067221 1250 905065971 905065999
    0x15050304020315010f0308070f21110a3c05010b0a05010201020702090c0a0302120a15050a0332030a090801111c0207021507051c050f09011808011406 66
    0x507100f4401e2107201c0100e29118020000218008040d2074880c1c00341c52058140441c039140e940003101203010354007920f03810f0b540c0c11800f150080030800b04120030100a0110910380e0740c422520400c012054007800458914034205c0b0b0507003181c0a92035280c010b000d4210709005180c03d078003810003250325911800702440b0100d103030f510510035140d40503002001d40d115511480c0d40120180d03c400303480000c05808019880c000c4400c0c540441c000d0300c004000040d0300d8a03200c0a001c8080c0e054021a01c502e103200010404500d11527080146001c00e0403910000300c50201d02688000640c40c06915140000b10b40540d80641251405040f40e85180080c81806260210b441c0180704410846074182d000c8581d80080c131540794060311580748007a06410180c1c610303007075018481e004144203c5c0c0b140e108401001122a04541d4411a00110f081407410644c0000207084240241035403d81080103842e060420012444c1251000380072000c020030590f40520700c8003e800da8101c40d80c901a03e80c0d410242 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905068471 1250 905067221 905067253
    0x90c0702030d2606091602010b15091504060804030f030b0a030b0a05061906081f12060f09020604051909020a021b060c0a020112150b0301031b0609060507020307150503040203 77
    0x28410718005040540f50350f40e02071000c10704528082810119966020b0360025522101818107400c50782d038ac406501c400049040250800145402c41214841400304010035030b0000300003034001e0b40c5400c00800c0c100b09040110300402480d085903502c02503040d80003090005042d0501e0180308030300c40038070803a501c0c00240300d03101c0e00c604046041c0c0411042c080000502c10341c1015044910328034a00300031001000b1030700381c00c80180c01011540c24800c407452b080040314171500406400c40c00041c070001c5542d40000303825024500c90316020b1130340c030380210f0b0724a5004031000c009020300550443d103c2d00801c00c020341d2045a280e026070301c1d601c15580449107141c50019620780042440040c80602405e40c0119031aa1030200c482e42440e8030359000511600744c071480c040c00350849443c9207440798598101100a00d81c03d080c05107464100c54010b12030355520220140545603541080c40c1d4a406503c0802e01c2c0c000c481e44031040f050180010401410f0303010005500440c0210225811019010108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905069721 1250 905068471 905068547
    0xc15020f0a121101060e04030201021c0c080103020607060b150315010903260f1c05010506120703051302091302010f020f0d03090c0e0a050109050114030309090c0702030d 75
    0x1e400e04010341c400300020b901c11407140c0c107403500d90000410040d43d1a024000f1203e03054030100c5c0580d40102e901c5a01040c0d402e101c000c1c80110110500035498080400b80c81c584060001038040c010000b0300d007050010307a410070755105801030180703d600d5422a0001d80e96420503203840c030207800100c04414543d0b101d01840f10650ba0070105a100b00c041c03440402842c40310440c01d400d20141d0a0040300010900c0c40302422405161804280c000c0f0304003101041100c405800892042274148110f002075130741950a0782d40921582800607854881084901080580640c001d5000c81c034002001044102c869511040b18404e89800180d4410a801070741c42d1401a50038070543d42c411901d21400910070740002500300c0c010141e00111544038a02030030311407402c07582c080180e82c0307640040204143d50721682d8018011504487c0098410a00081d2603100da5880030784a00b03131050224003000848400c4481250303004048803110508258090254191112000045058249411031840b030842c0780c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905070971 1250 905069721 905069723
    0xe01020a051801020703051515060307020a02010c240603020f04020a0c0b0415020a0512060f060d0b0a0f230301051e19050c041802070b0c0c0a0c15020f0a 68
    0xa4504020b003040e40054070100c0c440c01181180701e6044008080b40042c00010380380851210f01c02c0c031138641510780c800e054044c08181402001c0420810880035404200c80f144141e091070107000c03080781c0307060007044041c40100c00314003106004050080c5180d42e91000048074403d444495140c03c8580401040b40205418140414411180d020010f1984422580d0081c400e9040040b4407444c5800c030b81c1283c0000c2221f0001c2a400150b60020366100001035912600464110f014080c00700d012844502030080110102610744110404995602d0075180160508001c00000c00790740d0310f425400d241214840c0b540200c1402d4080d0100d04041c0901446240c0c0c18402228018440b1400c40d0310080040542c400d0b0910850000040c400d1409020b009030300502c03125444504105091410803100d626020300c06104004510005860b8040c4d281e02056542076141c07a900c03a040e074142048501c502c02080345400f148085000d000342c0d643c0f800352400c2c50382114038a051004c0c3c6207564012140e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905072221 1250 905070971 905070977
    0x60a0309151a0d050708030307080405010e070305120a0201090f21091d1f150207080f070e040201050409060303050d0e0102090d06020a03180f0b071d2e0804060e01020a 74
    0xe5071070150604001c0e20010f544a40100c83e82c286c1d179070030140d0458206580704c03000509144103200c01e1260034065101088010806000410325580c1c0f010340c4ca075118071490014600c08103503100303154001c1d070080070b0031900915400c0d00b04c80d151401601c5007240140c03000b801064407440840541c8161800c0080d1021141c0e804001c112840c0342a2491000070010045c42150155014090400e0004c1c04014080c40b122020142140d10001c3d0030001c198001440da5400404506048580042e003d03084402c202103414050f103950004032214440c5400c001c21141c10801c00101301503110008100c503841e211010050320140c520b10340d00741d100d1203030b20700d80c480e04d50035818011604070350040c5001130381400d0018002c00303065a5101070002c0348205503402c02426001405200c084040c1e20703803000052414905c3c03607000181400341c50204000ca03034040c03c90044981d40c2ca0548000d9804800c41c2d21801c6502510210001400000d045a0445605013000224450714205000390b4180010640b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905073471 1250 905072221 905072261
    0x1f060f0302090409140607020717030403020f030f030a0f1b080306041a0a0e150102032b02040b0f0306040b1c0b040c0e010b130f180e0705060a030915 66
    0x641103000c0d401c40401168031590390301c550b80020340c0007801340d03007084074000c044d1042e45001440a800c2c182e8551000822400e550301502c0c86910200c1100c0689034111028505a02080301203841c000c0066070850440c84001900a20540c10040000700500140e42c0e1095416070800d240380b0102d140c100040203140300384080394646c80d043c2c1040e201d001b414003114180184035030000d40950103a0384541e044075944001d000d250f040d8404075280c0c840d402c0c001189031001014906101d0b80b22007442c030b0701503030640e100515021017070b404442c0107010b40251642c17980d10105104115034403d0340c04611945c6800140c207400e060060142000540412240f03112010300d4603440a06030f4010011202c00101000106011020044d1030340603040840541d07071034882208031009001000d400103000380611050030800c1f5a0143c100180705100110041426080d400369189411480e8002d1980410080340350603c04d549a404244130310b0081c0c204007500901c0302c50f610101c5108443c2c02c8460b0240c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905074721 1250 905073471 905073497
    0x14030c090708070c0203010c09062307140a0213051e04080d09110a030303020405130b0d020402090409020d12021e0304210807080403230c040e190b1f06 67
    0x1814440d0f80c411281e003010104d4003626070009084840111400d408580c002c881070000310780c454500303007814042ca4020800e2000401c0f0f0b4805c1c40c098402d0082402c06403c40718a4100030a0200000f0994050500c0f07414540c0c52408101404040712000c1000700c0c1e11815181502000b40f1850050380c01810b00d621780261248504090b21810800380c2d00c0804030307801c0c194540c494028880056029560040c3c0306c500b4601004020b10444400400c42800c040742c4004558030909500d04e4030364102d600503550447d1601141c0074180064029600034000e4040c9401e00c1071500030030380501d04907030a42d07849040d03040f80c9411303058211000c1e00d52948144018015501800c0b6000c00042d00d64200c41c58100300f641e03508a041e8401881114011008982001000300010402d4100d25041c0580c80c807400322140c0165a541344200312510a549070f00e8071902031403060111216a062a41e00c4905c0c1e08698180b980ca041d000b91800c041d403a0403a40810b01c2d91000041031800c1d28000d80d60a0882850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905075971 1250 905074721 905074727
    0x3080c01202a030c15012d090c11060403021c17040807020d0b010b07030e060a020d0804111201140609061305190515030d0302030705070b090102210114030c0907 71
    0x480c0c41c03540c0c0540300401c00300c4202d913410044000540b000b10b400c01c91640c1020741c0702c01c0d1901402c0112101e010b1000c05041003450b490454001d0b40c12910000595625504088880070102040700000380642c800740014164040764906441001e01c044407400f1141c64400c4030303801c445a480d0225501e11101050000d00500f000300f850900003001c0744100f581c162603020701c1c04001c1e40402c5c01c0c4400010000d00b0541c004c0410480f00504588060034101d000c41e001e51100540781c103820422007104005401c0106100c8084403000340602030001080704032058078007c0101010341d400d11810440001ca2906e4400701c000c1c4113034000350285250304124900c0704040d22015140304003082640603603a2102145205192050758450810940940340c40306040c1000c4884218000701401002001501504003041b110001e03404040e41000395291201d007030084c01480c00c070402d001c541000503038000b00e6210149050303c1045090041110408042654038a403890100b074000350507000003064140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905077221 1250 905075971 905076037
    0x40303030b030c03010213030c06050a0e09040609060615030509030f09010f02070509190509070f2d09150e0403020c062206020303070e0915060c0703080c0120 70
    0xa07016044401030800c4100103401c0e07070004120384036800d40c18041007050200c3c14038081d0040490b4117000d85041d80b112070082c24900720308210b0380101c6c8a100480e0421070580e1007154580e4016100700129a00d400d61040c1c0e016a030316100c00041d003800046001c54001004585030800301540141c6407105510040d242020711840340815030003402000100794560881d50342c41241120754000c0010071469403001111030242001d40070ba4003400d41441410030310b07802c600981d21502428468080325851420401613100309110700111307000740004889443ea0400e032003808158410829107900d4501c400e8103880100d40242c0168402d00c1d034441d0070300b0100000d005484d07041c3c4030304400d0030303024008001ea00455449000160b100000300482542d20095034541c040c0219a403c3c01820413141d420b400411903502d0b00e02c1260001164960144100300c040700440d40801015201c41000740454020300e1301c21030359400d1441c1c02c1c064020101c40d074000c90321120901091440d0200483d01c0f83c103142c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905078471 1250 905077221 905077241
    0x6030204090f060f26030c06180a0b15040213080a020103180b0402010810120b0a050702012f0c0a05010603060c0f1706061b210f03010b0306030a0c0801021305011404030303 76
    0x32117641c180340c0360b641c0c0a00081625541c1d090061505060400c078002a140b0701301e00410f59078000c5c0944800240c500c50b82d1070b8005810000101081d20440b0014000348143ea01006020600c0500011355a40208821080c21f000b40c9003000244640d4509041405405000402d50300745800040c0056000c0d100d80d80d003021014107513184003511000700f401c42c0707001580b0940e4055410400c201a042181c043c1d04e034004254070007406210311300f190300d005500d04002181540740c20240c2004034080794505403401a0b8400c1c080301c0d96036083d81807090013403a65000a480090514040b51b030b8a5000f0482e6492140d240d9075a1130541042c45040100d40d1005001d09504c0082044400a0a2001c2e030490000e41e16841c060800c01d0b06a0a110702032410184035025511014041034101210a00035281101c0070280c0d42036895641c0c1c00000c1c2000046c02000740365012510b004540510150701500b071240360051052561605c0e08015607818484440c031640c844001c02040c0000b0303100383c000c44108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905079721 1250 905078471 905078519
    0x2070305030a0f02010f09050a06061502030a0521010611070b040e0a0911100504050f0f0f01050304141f0c020105011a0f04180b0112020c1506011806030204090f060f 73
    0x20700f81201b0300e016150184001e507125440110103005008042c4240030042841104803586c0c00c4012801035268080c540800c004c2c0500415051304001c02e000c01211428940c12034012190307100c0c403001d041e0301243c460101452158840200741418104102c509a4a0740d144204c0d683eaa0b0300d505402405c00d01038100e40090031111010000d840c1c05510b01c2034401ca82c2ca505840da800d000074004000303074503207025106a0208484d42c0c0b150b294080ca00f12110388c21318100355a642c07582403602284c99817010203d824407c01c20920000000e1904040c014442ca55060141b906044402c07400d03540d00707014071004646a80ea0004041c5100e074002c2550184241a040c103081d40c5115441e408130300c1040010400fa15103030f18100c1503902c0056940d401402c0c071404c604042040900c155540c8002d1421048446070b103000c41ca09a0180d0450b50a1070b01002d44110003e48455005002c0e4100348100c0c00740c2800c02d201402c40203068080d0106030303421001d640507000c4c034101860070590108801147e003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905080971 1250 905079721 905079731
    0x3030c060906061201060302060405011b0506091b010e09190b04050c0d27110406050904050d11070608040803100b07050a150506030c100e0301060e0402090702070305030a0f0201 78
    0x512032a88207200640142c445441c0c00d00034000c40d11901e14014000da4542402030005981d01070070389003078480138680003199506a00c48103203030920b0420041c05501c070750400c02121000c0020814201400d03200c0040300001c595005445080045a0b555072203003500d40014444106220154104041100c003c80c030b800c03c250202e0700b141c60580b13520130b00ea90001004908150503010360a0054410404403a402d003010102d20a44a20000001c0404064a004a00300c0e9501d400002c0903142c01002d4103036a040c00d29116555001c00c080a00124842c00c01c0c01d4141d410100e50a802c84a10b078698038120f1381d403581c4204141d40300500c1c840d544401d200e40410a50700d444080d00d07060340710324002d141c0d00d00305083c096002404120b01420013070910081280f00e850110b05c0700c4c503840e002d440d0441e4440d00f0000683d0001000391005030198a00280003072864003061025004034025903548000e5140c0c1c2c8001c0362103401034040600164410043d6100c020f1040d100e07006148076910000039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905082221 1250 905080971 905080987
    0x6010e03070914182b03021201060809010c02030901021b042a0806030304030c06050304233703081306060603020307021e07090f060902070321060e040209060303 71
    0x484800a0243e1120300100040103600c800752528860144036420050a4000418885d0581700d01d0651202101544a0455950b040c4c001d0f01a03400d0406208800e0b45250b0315450000c0c06800200c0304104598200806201031600100840b00090410307130140a440d0203000004134039802c0e008040c0e40081e030321070654020b42e40e9581040c05401c0c400c0c180611041880385d00401c0d201024110902ca80c200b000b0400025541d644800201c0c0c0d40d0303080c801e40706da4903802d100040942191101241c2050b50955500b50f0001245019a841000b610b03400221591a034418501d10201c003d20610001d404200307011034003a42a00307511140103144800c00c1000f95540320180d8503140c0c041030100740c010092116903601405540b441ca0400d042241c4015a4001d0055641c5444d1151032250fa1350703408003041c10300c25078100314060030794290290f56580c203d19004058812280000c0207100c0e201c0018804c030000303401520102c1d02daa03030200701286c0b1560208200c0c401d02420443d8588406c2040310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905083471 1250 905082221 905082239
    0x60f0409020403120f0f0e0111150c040f09091106070f05030c03030a050619090c032406080c1c0f2403030908010e030d02070c080f0109020103180b06010e0307 70
    0x1551007156182003019280358017400c40c40e5500d4600702071110014007150a00c0e4461040300c800e031801d00e4029400c58100700c49605004c0c0c12039070b2a2a80360700400700300c1000c100704014011a03500c10a90700c0703020350303840c111411200090401840390881545005441c5810005854500d000c1c00c0602440d071720a1b5200742c0396600510110000d50000720400480c0545da21943c2d80c000415103403e100c070008880340040c0401a0702036500b459503180b820840e4a882548030030401026040740343c1a94171850700c1c03814001260b02c03440d8006410a03001030001d0180009907282c5a29003148803490314229034510000c3d1020080c500401d46d41ea101e03c01c07201c1d000f4110401600071040d2800000c40c1181002412805039810424040e07040c49004412641c00200b00e0b540c1d030003554001a2200101d141004000d0a1580b120083c1d10920503030343c1d0300b0181940b161080328400d0320104030003e0320080c205845043d40340040d0060341075000048030b03035001d503a1250065070020113880d01c447c0c44100e25 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905084721 1250 905083471 905083477
    0x20f0405090f0f0a0209060d0c021c180f050d080d09060204030b0a0b01030203100501080c0d090803241807090f23030a21050d0513230309060f040902 66
    0x90316110304600501c034084101422058010700b995805500d8041070b1b40c0424a14402d40c1ba8001d000da5582c6203c0c05828804e001241106030041c00300362038035100d240c000b81040034044d030a0200d1a20008009003103141040300504965001d045072420410a885040558100c0c2400c9007015403a4040c1300700003020342c80104051071013818840020300303150311680200c1d0003003034141c3c0c103051040003808040400304850108540742480c04075800d59a2861458039400361614560b515400c1c01880410007003070380b002c2c620599684002d0008410000c2075440c4071403814840b65044003022180d8010000050b400a90101d004d050070303032000795103015030088408140e01200c3c440d911282c09100107641001040c0098400b20001c1c0941e8005032166841a004144050603071a42c41240101e918040e0b016a00c0649018500300860b16111010004105111b54100c6803003410b40c3c04810403060030443d41c21082c0380c4600550808090070180469903000100c1c01c0c12081c3c092000050b07021480c001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905085971 1250 905084721 905084731
    0x31509040f0605090a080301050f040b030102161707171b0d030f06050a03120e15030405070f05030307030801050103020310050301060306060f050d0f022b030c170a080a020f040509 79
    0x1145078030a810080100c0e40040c0a801ca42d03042284208041540d10341034030b0645000b1129258800c007040b001170020501c1161003a0594004610001c0d02402d80079800c0496001c0c03d1480394401d05d800380201148112000105010442180303035a00c00310b900003500e201c00c5105044011207500d0a02d00c2c0c505910000b110300000d80750190f1269400103400b408000b0b260a89130f10201070f0031941c501240f100d800d01c01004211706400da09440c0d59401501e440802c0008240c50346d2810f0608119444e15198012082c1e103080d404c0c0300103145e044c00070444005603015510504683d00300401140a036001500b01081c980586001081981e4288603041c015842130800145a914200100d001402d99502080c8915400c80503c1c02284010f0040d10084c0d0b070482d8400ca80083c01141d41c40302002c600944c0202102ca8800c5204064000b8080b0540d18000c45c0c01e2110705180e00d00b6251b07544541e218500c001200280410741c85155500a403000101d4060424149901d50300400c0010b00d085407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905087221 1250 905085971 905085983
    0xc2619060c200d090504020711062203120206070e060d0c021218330a14030c0a080c040f0326030705030711060c07020f0301060801020d020d06090b0d0803150904 71
    0x43d1002560700402d51000600c0241e5046d42030507182c1d19038500301c2c400c8010103405102c0c00500360b00810500400062401c00c082e19a00303440d9281d0408035580c00d209042762006d449510f000c61021400b0b06041e821145c0010086840c00074002d1805026004440c10b403001d61081001215080c210791000e0501c03030184551600e403c1c03401c0d404100c0c9207000d141104041800080d03105c00325180b01a40e0656405002100c0d60b5035610303200c0b040354100f913500501e003140c403804401c0c4018040710301c00800d0340d94190740d00d5052a0310b0b10443c0400921070f41c42040c074200e102903002c20000d442c2010030841e4580c1035511101024214880740f46a034400c88045001800000070003100c19000320162400b164140300500d024a001180f41480344501070000e0300c11030158203040c140356001d4100b031015144401c020364075810340201c4400039400c0300518400040c100400426180c509110b210322a030710081c09003044a2103505c40c85201d91000d030404070350042038904168203491300452a40200e1180d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905088471 1250 905087221 905087233
    0x2090d0b0a230f071b020a090903020105060429060f071a0106020604050c010e0f100201060504180b0109020702011b1208010608060904110d0c2619060c20 68
    0x2c0c2801d4864415840b460400c02500c000c0c0400081e15114041d40550710341043d0130700c0000e1220480401080c1c250003075025071540c40128940600707803c07010046100340c0080c81161610000c00c0140c0c1c40d072414100c444110034000207455800d8400c0c652444a000d0b04ea5490005c8403504906290300011043d60700c2d1000c1c4100500c001c0c90034140070300402291014180909041d40c40d035448180d0080518104101c0140c4081181e0702c038003100d25480c0008041d0300b5103065141001c7d010302498440c880c13042e460a4080400480f01c5420b5410182e071000300c00d1456824002200300035040351805030f040100e0350030b82c4003042003844040e00c5024040c00036000a0703c031002c001855140160030032402c0042030001c4c490070f40c851a030995017055214002225458140700441c07952810801c020340900c401000000d240c1961604985401c4461008000d4800d02d100380155600700003a0120184034805920070302103409540103108501039480c1503140294000341d40c01c9543c55580000d07409070024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905089721 1250 905088471 905088491
    0xa03060f0b090a05120327030a050d0806010203091302030417030403030e06070f17190c031b0906120e0c0a0306020d0e0d0e01140f07050d02011503080304020402090d0b0a 75
    0x4400c01e040101011030351180b10038600e504964603401902d0701d02689600c4d68201400584004c4000e10704580c000d0103c600080150070419032f0703450044020000702d44d0380703c0442e495510110444681e070710090a6400b050b070551407008000d520042c820746030460a031030021000120b40008501450081d600425038481c8281003d08000d40501f002c0203002d0012940c29800f5013101c1c000041500300604400c40d40c0c1c403450242c202e030000b00c12181d040f92411100040e070301c3d010b43c0001c0c040c00c0c0328a108034035010070103030030b41e1410520f00490b80420f200c080c9411201010360001040125044190f03a400a11130002c81c0e0080c000d82c104071403103030300071031481028405c0c0e118410107040c020008110214280344050100000c03014558100950741000d0311007049001c0807038103079178071030441c0c1d598420003810030703580301d0880320342450041d401c203600603011401c4d8035002c0c0162900181403c3c40c1d5201e941c2044000e5004503c1c854200300c0c1c40c0543e40206130002c4045204421203030010811000c0707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905090971 1250 905089721 905089729
    0x61710031e0b01120c032003010615090905010303080f0705390c01051b031605150f070e0d0201031e0509010c1106130f0510061503051501050a03060f0b09 68
    0x5030400e000140c550607613203000c1070035801d1200072650801c0b454000380d45e031261104005e04c800e03540644c042d801e04d0030010340d40440130b084000ca0310032035542881c075036102c603800c0054580a202c054000b9041202080d00898448402c40d0055040e081040c0341400660602c2d1681705080240da00d06454031210300d140c804d14206841c0740203072000180403030041c00c81c0082c00c0e40c05544420700c080701c203120502c000803400300222a40c0e01428034031100d0700d00320f81c40d2060760380c9407030059410340310044008282850180d0307039660300917a442d44618140d141a5400d0224002c10000164105520f0300c046140b610b0b803101c141c00748140c074a1400b041703d00c0c06905c21400c3d00c00480441c0204604040f9500304a0804159641c00bd10b1000e002480b40385181040c5c1c0310a091680094a9800307603040c100001310159010f84115840074154880888171000c06070304032002100d54915103000c1481320503940d8402c40c01422080010f090002d8a541c81d080c100d0785040558018201482002501b00103920b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905092221 1250 905090971 905090993
    0x2040906120c03120c06050a020d14010f061809021602150c0619020f040e07020c0a05010c171c091104021c021c0e030a0810061710031e 60
    0x3500c0c1c0c070341d03180140301951900200706440c4005403240d1550461201e0042c0f15020200036507400800510840c00d01c1403418000303510082d14000300924050360070708090006071503213048034aa0707503040e15010314040c07095501d44000c841030344641c882101e011a10b400a17101a0190070881c0e0300802c0c060b00c032441803100581c01003201046400d024001c511288400241069211100c0020b210094040320440c00103030084c0c803408240142c012a000c0b800c00030442c4128465030203582190014984201071000c400b0782d5001e264001110602480003045007080c005602d4907071074501c0c078904a400c1c0700064074400c400c0a0340001c0e1391070709410320a01c4090f580d4001c1a0f5401c072170441c540a8858030403070041e00050641c4010940204814808440c00e00752071803515a128010300207540c5040074142c60f40d10010000700400d8040740132507a810191084041695016190400f03007140f41c0100c81d1050100901c0b0f540c103a200c1c4000880000c4032490003154980304011100410101880c4c1202c80c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905093471 1250 905092221 905092229
    0x30507090503010203190e0c0306010b120c1908060d0b150102070b03063105010b0301181b120e0f010615021f050603030d060f060207050d0f0215190302040906 70
    0xa8010300612000c0c600d030740b9440b05541c007244070014501c001c1c11101f9040680917116070ba07240c05031000005002d50100014140b2041d12032203007144d90f503461242111400f5415598401105c0b85120354034050140400c0ba0f00300301c006004007454406c07980c5400c550141220078201546030404000441d50b010030585002d0914030b51810300f03501c0c002c40400c642d001959090210840c0318121140709011a2002d0420040003000900c455a1100381540c11544284600503c080c85084540e000c401113204034070510400702030749581c501145030110303110b0900740d10034144507546100c0d04032000c2c0100044c4850814210002c2405131500d040940002c0c2126000829500400e0a80c2031504049801c251101780122001410707031282804a80355024804420884d18585200800e54505054105040f00c46580c2203a10017511502032186030310303464130024802801d104107200145895034030042c44c80070344142c8c107007414880070140010441a500c04404280c1c001014442c041280c02158050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905094721 1250 905093471 905093473
    0x40e03040501121b200303070507020f010201150b1b0f0105090f120a03091403180f01020a0818150f030406060e06010f03110405040212101205060a05071707030507090503 75
    0x440848090301c1000c450b24032041003040817003140d09404103c00920f0100c503003202d0b0203c0c1d8070391501a10142043e0300820302a8070510f40703040354410039031050207000804c07050116010451454003041080c1a0003c05031402c0c65106901c203164500420851a01390006240001c280b03030600546c01800c144840f000880d864020b40c01055800303030800102c50b140c0c410303813030002502c2d001400c20122010304c0f400c00d901743c1d000c009020000c0c13031955559100ca00300126480e1500744541c40043e0790b500f078884c000815448050041c01c00e4107080070610310b0200c1c8041d2010364100d01641b801011580681c5000c40c0706c500100c00c2c0801d00180d4400c8002812030506111800e043c00c000184c000a1031617000010161604070100c035440040e400d4400908010f04199180c0c00702540c84400d4a004596040c0d44100c02c0070002400035210740c1142d0139a0b00280540384a840f07486030403018100c000c4c050000d10121550312002c5400d0b001003180f15511b40c4d40d0001c8c850802c60b00c02841c1c0c104a40c049882 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905095971 1250 905094721 905094731
    0x60609010e04120503070207150c0201120606020c0d020f0a0b0c0c061204080304050a0c171002040b040b0a2106060f1403160c0c030c0e1f0b030c09040e0304050112 72
    0x1a140f0691419a12514103095407240e550445c03ca203414415000814085099070780a060203800c10489141c81e8800d80303d0071003c061103804a000c80301103100300801a4041490000c036424040042d03208540050b0161925000e0303400820242603165000c1c440803440003424002180051040000ba000100d5211389488020164a00420b01c054800b82c241c50001011a01f041001c000c170300b102d10342c1f19803a00c0040740c4d5a8203a0070100c42c000c0c1c50403554040c950521404044a01c00c8606944003400041e0419040a50741c40c20b54020642d0001031082200c100c00c1c1081b0204040c1001900c8403001081d0907080500040c1405842141c482c10710203101110703a00071426070300360b951001d43c1038043d0521141a800889161180303030230141c04892410000303c11310030702d102c0d600d042c3c804101d5085015101c040c501c941e550082ca030181a001b582140074088c0403006002950001c5081201c40d0518403003000180840b078480a10100c07a91001600300183e58102ca020011140c00300070405c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905097221 1250 905095971 905095973
    0x7090f080303190b04020c0d051b0a020604120312060b0a030b040c090e09030f0c0a0215030f010306020a09050310060315180b07031d0c0108012312120c060609010e04 73
    0x3030743c40e4003440b4008542c4035804486a0f4859905640003408000100c0360074480121014000d540088020168615440c0c4110450800000c01e81c0d4059800f4005d1072416103412607900e452910740c1412410440c100001440c440082d005460160014807251a580c00f44000060115024446500d0059052810448590741c0040076002201c3c004545410a903070f07650299420f502c00c0e442c0c0004510700c0800c02c0c546040c40054445072a034425070391001641080c0c110701d802da000807600c1c444000c400c1e41c01400081d18940140c04505440c0c00c06621035911070000a041c8041120359030440d654030790b020024401204401001c0001151040090490301c10200e0400c0c810494090a110404000f02c4d500501c641d206415460040340050240030a1072071403500c5500000d049800100003800108a1381c042d0341084100345443e10684608005100a01282c80d4610482d40028091601007458660080004241c005440f2000c1d0000b03142c1041040081601a00600c00400036101080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905098471 1250 905097221 905097241
    0x40e070813060b1c14300d0b090103032f0309220e07030606060201020a090504180b15090c09030d0c24090b060306161b0b07090f080303 60
    0x10324042d040880030980c81d00b031002103040c890b0048100c209103044100f0b00001c1c03003220700c1c1d0340d0841403401051390b1840190809090010002001c40d49010150f0751806109640d08401010880c01a500204040748402d000900340d8409074404d40c0440c0c030400c3d80901c0b5946ca0490141c10400c010910780c02e008a020f000799603030081800803400750004100140801034500d0501d5079075205000c0922210122000254803038460b4401201c070b650600310041092801802940e0380c0604031740d11150420314290800010323010901e000c20302401da81181c00c0c003050154103a188503910004104200c15982002c0c0703d10f604005100204540c811b00003002ca5a90210710b52a4441e500e252007400b1003c182040070002d040c032070401201c0300300318500544003042d6811482c1000d00074000b40c85181c0d40e8005154449100301e420011081013440c01e000740c80d018a945041c100e101c981403103c04030440d510880e581a0554140022032f18001d020026401031044010107004410051401d41c102070b4080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905099721 1250 905098471 905098501
    0x60a0602100c0302190207060212073c0b16050301081b0307080d0f1209050709052205070503160b0301050609060706091a1006090519050a0b040e0708 66
    0x21030007094032140c600c880c00f48250150341d610803016804588029803000080d5882c0a10302ca0f150150040031503807014503035000103581c2c5041d00701a070100c100c0c80083d035418103c0c1e00000e01d082403e620f40e0040c140c80b44001481101c3c03500c54440041c190038158002600707500403035604000c01100b0801441080808102901c0c51011080001c2d2401c5242c00041d0400c203007a00400f0031845810011105e880e803119000b6049442502c0c2c1910b00401d100c0741c18141c0355494400741070f03580203200403c526880366102c1030384160540f004101440504003c0c80300c42c055484180c40c80d500c2090103000301d2806004045e1400da43c15200b040307052805a4000342c9010510031588540408203d001e05502ca40e0201c1d0001c035030101c41048109141e140c00e41d103081401d4040c90a05140c0300004003e21501401901529501d4403000240c61600c001c02c1a840c80c00010400e41400b081c900180e55195400c0c0b15007d05000d000b8503440b103060110b42444180010071010420a15006200e11000d0403031384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 905100971 1250 905099721 905099743
    0x90603010903022d03031e070e010c0b0a02160c030c06020105100317040302100f09060f02100b040603080304030c05010e0d0f12060b04060c02030f011a0909100c0c03020105060a0602 80
    0x244090200401032800501455032030080300c0c0c1c0030000400482c0110447c520400c8180c92003a940a034684103001c450050f505040303a40803440d03102864020071511000355074001c01c4200c01614003003608008400c0759584000488980c413860030280100f10340d000c071f5107003e00f8542c4000c0040c0e18220104030340d584520300c40905054655010490709052110072100a150041d00c01118501480c50041c03003102c205001d9400030b4125400403c94602c1804007502240080d0f000740803520312045a070b4000c0100c000706a500658038580000058003660240d44103e00036110400207400b941000e6080d94184031800da0b441d046833000d0381c0c01c10f8100b400034548002d00d2415034400000c3e642c800c401000e003a0801148140085000600340303a2141c0d4900085100741d040d9800c04580102c42800d803003030381015a21341002e00c4144401ca003000d01c034150340400444200d501a440c0c200701d020445c0c0b01000303010002402050b05038203064090144030307001001901d00302c11582c0b404000944460084403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 905102221 1250 905100971 905101003
    0xd02100905090c0705010c0c03050406031116050102091e060a1d09011707060c08031308040f14041b170a06080f0604022103090607020409060f090209060301090302 72
    0x1104091a44039041000107800064211031a43c00d202811400039000450111829801c0181e802d6030f86d4803441100f08615030544584e404d040c18468203402621450000c00040c00090000d401e8807a8604201e48400340142d00040e642d05000b001c2c8070740c10494442c3d0708035030950401801004d80b0b4881c111544540d007458016000b503101d60005103864528007840d903000035848004180f0b076440014510a60301d80004070755995130340d20701c240c1d049070401030003414032030041c40010101c0c44460040c0700400d00c100740c41d0745070a4541c0903c4401104c1d40c0c01507102d0450481c80290607003840d21468800035480c4812400038090044c005001d030f200083c046000f244902c0118401e85207581004000c2e1125405407000e00358110b0a0607510802114281d01c58125611080784400e0380248029104150a029625040801b02804071503070000e04200c2e005941c80c080c000204a00d4070800e102100f4025001c40c1400080c01000900031014100314826490041c80a00298000a07030180c4c1c1181d640d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 905103471 1250 905102221 905102239
    0xb28050a020423010f02190209180d021005011d0a0906020f040617060108041a10090e010507030b0907090314070f032307030b2e080109030e0f0d02 65
    0x9400c100181c012a4000c0c0d000310080c00d51580002e652400d0051100001e98131240c10b0f00d03030b0003c120f0395102c516900700704e030030b401f991075a0150405d05155540902003a007088000c500038005585045810602440141c00c10461001d480c4818002c107401440f0083d100b10040307200215126400c4c4000c0c003100301381e5076a0300c1810f00304003032074044e190005400003a041d152507031008007070700d800d0740c1d6403032411503103003520000da155030140c032445006540020140c0b042c422090201c550401001d00f08504101079030b440020000f4142c000c0d005039003002070000c02d180c200090050706454400e0f1802d44214150380c200300309268000ca03410101c0b508030349183c034007001c041e0b02c1604005960b0400220f4020810010050142c1807804010405200d200881801204c0b020b903622941c140c08010b049000fa00301291040c502c280505204080503034110341c500b6200d0381d82c6214030186038809441a515000081c0c18590030003015611103100f0f407650b21a0720b0400c4001180159940d0000b40700d42050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 905104721 1250 905103471 905103481
    0x307050a0e190501030506090c0403122a0b160813060f05040c0302011103030c180102160f05030106060203040b0f0a020f0706120c020c1e010c080f04030b2805 70
    0xc0c4072001006101425481d01c020014140718400c4501c0e000b020b012a0600d4042030460504a100c2e44c4a0a140d028060516045030340300440c002244811904200074820210242400380a0369004c1d5001d16841c41103440780792800d203443c0700005102c820303c202402c03a80c0c100541c0003c50305500a9502c810240840b07958589207005041076050310300010b20304020042000310300368054003524000d8a4641c04100e01800d86640c0384011506600c00030f03400d0084030324015010049420041050050b04c1c0b8148244d840c08881c1415640a64485100c00c102004141402c3c070030040a8480e0784043e500e02802c09102c004188600c624600c0b51079000644070203d913100b4452103000241c40d4040d00d10590740c070130000b40881c40398a0405441858a80d8400c0064000201000c03e01005807059082842c06c170100e4000501c002c1c1c0f001e042c40f81c19003403003001501d07500c0180764641400407916100d174210300341071503008001030002043e4000003c11564003007100f941a121045400c0e0040340c59950 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 905105971 1250 905104721 905104727
    0x80106080615040f0602071e05040b040f0906060306050a020702031b01031508031c060e070c05100c0810050f01020307150f0504050c130506180a140405070e15060307050a 75
    0x441036202c0740303441010801190281d0b078040544200d400c240e084407070094a0300d44c0a00d2403220300c5445040003c0007041000a801c042d01b20481d0980d00903c00501098855500c1081d982c00031030440d03502d650f030b06081c070400900e4801c0c103420007503000c0118280209640425a6010406c00804802d203100d200281ca6a12907003012030442e82446c00700d0801c0b55540e0b0340540c0c9800200b20062100c804413040d035088801e621500c002c031507081d42c894007980c54140c020b4408140d108420790742c0d80201100078400c031703045010701006a030ba15a140b007104c0c68201c0d82c0619145030307608070501c50100c84810981e143e0340082510b0150384c00220000c03218240031021070082501c0c008825100c1c0c140000c0000348403003c6410484e408060750040170012001d2900b104a4038211400307548080003080f07181c4c0d040205030b01a071307103c80105000640902408510000810215822581603000c007905104008030440001e40004099041402482d6030b88002001ca004c010030f0031041000c04580e160010388 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 905107221 1250 905105971 905105989
    0x5160810060e0d0f0c1805100e100e07050d0510030c030212013b070e1b130e01080d0306150806180103050721050c0d0503121509010b07030801060806 66
    0x150010801c148815946000d1591402c0d9118109006c501c6c1240303408007900c0c40c02081d208007542c2c4004003110307081138400741202c00042c0a440120445171008503030009140506401410301e42c4604d626020781d0008001038680041551551076070301502040010403600c948002c0c0c9070304840c0508078104541c4050b004055480365030629044140055485810891710b9605c88419031a1104c16003129188481e940d800c1445200c0802e00c0000004010040f01178801500c4615500328504c0c213101051400781c44550303030304007402d80c4240d04010801c240d0b003000980c0014803182401d000051038103009440060760707003800c2008d12030704900282d40d5503219280d0068800c2603003810034003561a418401d9841800e80150000044110411100c000482c2c40010050313901a008112080c0d1081c24060000f1140300100e506101c00c4c41183c4c01c526071303c45098401c4440c1283e120944030103108102c000601070307024681e504030401c460740109902ca411107040d248281410711283c1c46090124414607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 905108471 1250 905107221 905107223
    0x20a05010c1a0f160804110913080c010501090c0c0803041b08060a0f0501080a111009080a11041109090f04050708011d0c0117041e0c060305160810060e0d 68
    0xa0714404001d003c0c22000e11181c082d881808100c01e140f11000c0302603950b140140d902800000c070303d0803168680e180140105920813201401181885400c0c2d0714403165800041141440c2d9440d00010701c81d6001900c03a2002d02e10843c50440c228202e507444200c094070000d0006031427054210341c000348040850309010003c020801c100c0d009454520b00b6480104450081825082e05160000800001c005100c001d12038000380c6074407900d45900308004000c21600e1101003440702040000640c80801d0280401c45401420f40c079801f030942d04108000c031014103451038041d800900860095458810b4011ba20400004903003035070f078a960928034a046842e50040c08190300780351000341144400a480400084240c04440281c1c400c24010b60700507c540001c0c8240f05c2200001401141c0b640e003520075001010a411b442c1d0f1200c5c0d48401e01680802e0b000030011a840d6801c2c4081100d40c03030240e80c4981c1c001c0c9461009400d08c51189090701d1443d01c42c0b070041051100c1040c82d1543c0b114441c81d405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 905109721 1250 905108471 905108513
    0x30901020702090a0b01090906080304140d140307151104090f0609050723120403050d0e060c0c060f090d0c0201030b06030906180307030e0d0318080f010e0a020a05010c 74
    0x740b6104c14000b02030184550054002940f00c03074001030b5114140121001d60750320344091403c1c00d080c42089500343c1e1580213005c0c0d02881d102c03c031501007020f42d4501d91503444c0c280095a42c0c0c1c045410091800f0111004042c5032030310f03256004100c51004002c1d02c041d00d604000c08285142c92101400180407160000e402152500c003e12041e180c11a41a441e11440c0c11102d04520504081c0110503018054030b0708160101c00b000213002070b22030802001d40507915000001c01c441440c421718034040046845a03100c43c1c0c0010b0384841c0c4101001110b03800310090502142c24034000187d42e40350405900d0f258240551020000d003113a01075001f480400310041c1550b43c8a10b480704079030b65a66420f4031070010b401c0007426010200007000c03040713910303040d0544c6503c10680b04000034002c00078502c0000307400300101c1c0039034050100442e5030b405008240420040c1000001c0142c140e0841e0a104580001340d0f200c00110401030300c3d59507440040f0782c0c090805020644007414011110143e945601e440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 905110971 1250 905109721 905109739
    0xb0906120f060a09090b06061e19120b010c0b071b20060301230d0219030b1006200309060c01020c06010b07051914161503060303080c030901020702 65
    0x1040c110460740c5101d481d08640401429560750700b00030481d0f2100c0005480c05c0110300003c1d00c030b42095002402080342c00c201c40924182032610029064120080b0f040751071180c40d403034640c000d0740f1040d40b02da03080e0030717402c00c1204407806d0300042c101d8070207104010441488000015040f038090580d8801c04024052500e803006090300d00010400d40450118440030760301300c1130486a08000c029241070340c03005450000018216042900b9a807030a0b541d882d0b000f03d1680d690001070f00c03400070312400407100500194003c0d0071403400c20100100140104510901e0200810902d0341c042d00d01c50640c0a030136210780120700c910000030b0441c8220700e82030b80c0010001031541700d51801540108038881220056507041c9e6203400c41d0911030300c41d00303c0150003a40b1800140790590380c0316085204c40762180b8108080e0100030200a401c0080351001c00c880a90355240c10400084c0307607550146820710500e0200800e90335543d02400b0705c80050540504043d010ac0042c1d0824000d40c11030702d20039001404005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 905112221 1250 905110971 905110981
    0xc0318030207081002040f17010204050a0b0304020405180307030e0d05030301030b010924140103060512030409060518160e03010218100e0303090d02010306030f081917010b090612 79
    0x254402c1d0034400c8001c180306643c00401042c0f0180300707aa0541d20b4849170a45524544220862412400c88220b10b195508010000c0e203651290050001403403800c0c030399601e0307207070070b00411040311380042080504901642c806c6019a4012040751101e039454209501410104800300780009182400204180700000010041c440107502c0345c0d048880b04903003030015081e0304103944c4a034610610711591100032400f052000e04081d6450080c1d100381850009106c0d81e0300d5000980e00d0740b13004801e2940d0380000400703010040c942e00070703440605000e84862111410015580c0088003004120400070b558000038911040e00c61110050b481c4030050095444407a030500c5e16613580d440c4219a44102c43c1104900100b90242c0c0c5d084000c41c0d00203014605190025080c050080a01c8404030704044e0b69120200000d0599030300600709034000d003000741d10745100c6000c5860304601090f070b107014080e0b0400186450710680100905443d0448141510b410032840403448074000c042642030220101e02c1000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 905113471 1250 905112221 905112223
    0x2d090507180b1f0503060d05030d050a020a11070302150c0a0803040c060e1807110c030709020909130c09020708070b2a0c0613031e0f20100c03180302 66
    0x40007000844451071030749a070ba03054800843c911040040850800d000058242c60221109400c480c0210140c0f1720341912070780e0140440d1b0703040384d100f5a007650120349076880c070754002028007880190303000030812181150000b80e0141c851a8001c18404400211500909008d01072080e42e2684903e540b0b0712414140741060940c00f1038060310b40041c02c1c01002c1101841c0c036a20315000b0f0b0108541d0150b55486180c2e08442140032180240311b00d10968070f2103007498400f0032440c8020041c4010050b00e0301c00c44002c0144888005e40317559503003031000400d0700100d508640000121141403000580e60084d516045c00d55001d800302c00341c01d6020000c20043e00d400912000c01050150503c18090480985001021030242c56610a13840c0e00203800200d10944860010100601030300b4400c030140340c00601551009003c501039000140090080d21815030000c0b400300d115101d114100300441075a080b03445e80e480d0711146c03040c41d80f901c0d20740d01011240240e0150342d4006050003405c03005012401c0203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 905114721 1250 905113471 905113481
    0xf121103240a02040e04030e0102120a0305090c01140d0e0c040f020304060f0e0a020d021801081507020a0b0c0702130f0b011707090e10080715032d09050718 69
    0x30341100040c480082e40070315039403003140c0c2903880d01c60b4007665588458030115203c0000d00116410f51080c103114022807100580940400d071520754000c122840d210003224241200c07522503a05200b00d03640e072140076103080780035035411810741c20002400210301083c09140c03110715211260020b240060103500c84415400840c80755021b9070090007655400c1c1c8005085490360341c031808040d0000c14442c00189007401c00304803054002045401030012842002610130000e038410707032003517000140d401001000d020807654070450a001600b4000c2142e00d803000c0c0004001e105d8030510000203464002c55641940f0540c0024020104011b84c3d20340101075002811001d04480c0401c014118080f461018403e0b46403050442d681e6640b052454019071444800000e410801c0d40c140044011031031000401c4000c00801c540f17086180d0032000942c0150071201401408000805040c01c254902c8200d90301b0344d600b9001110b00051030140c0e504101d801c010081d007003442c0d2591801d0b011400c242c119081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 905115971 1250 905114721 905114773
    0x406060309050c0307030305191116170c0307060807230408161a070321060627061809020d050a06052707090801150602010c090f121103 60
    0x2200c80343d401d8501055500c800d035202c000c0004034104107548440e40da00c0b140c0055401241424101c105041441e641001c0007450711003c22802a1401c02200f090014914642c04142c800343c040075502c0c80100352204028041c801c203018a00740032403140ca10400703c0c405060740018041009800103160b091803540184110002440340100c00c4090081006065040302d160802480d2000c080509004882c1c00062050b0180140c542d001c4c580b91050180d215543c844c200700c0000c000e410140050b06012909072110600400303900071342402d10000c5591800c5e82d2090034007084102ca0740421501c408166008010034a0000c11100200c100d03a4110901400c8821410f00a07181c4030428802c0101518003e100f8018105007060348096501c849541c01607078a150851710140c44031200da0946075a020304010151119000f0000143d084c403a12540565524003d41031380d20303200018070f4002c1640a40c210b828941e41c50401000200d510311010f150024068580d4007500820f515810919082 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 905117221 1250 905115971 905115973
    0x1903080603010c170402190b091008040210080c091203131502030f0d021303050309120106050a050634060606090e04060207151a040f050f1f05040606030905 69
    0x10031020300e41801240d86200d5142e44801e92a04201c40c40710003080082d10a81c2c002940f840c95154200d800c056400140c481a030101d603941c4040001e00150034000141082001200000e00c4010307a074407000100c2e850420f140090681d218141000c045114000c44981e1109040886c00300e40b01c004405480c106141d91200c004040d61071005006451080300c0500050b00100314841d88452140051f00c0c032040c0c40e01c170060800a402e00e018100f61100e40040e0745c00d80c4041000c0121b80351005030042c600d9100b00091000381d2500002c1a010310990052511078038000c6954131801c000c841c111890345030840c03034069010304160080c0d19502d02c040c5d410780d03005050180110700380d4010140c40003192042c07a02c2c101d043d40d80381c0343c2000941010b20207c0da0240502101c0c42d0102c264000c407041c800e8055004418013005004120850794218140c201b03041c1040f0401a001605d01565070348102d500081c00c100c4c0780e8a40d00ca046000c1d040d00131990041ca040400300d5060307403560107210164483c0d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 905118471 1250 905117221 905117237
    0xe0d17031f0819171303030e1314240a060f021c05030109020a17040303020d06081f0b12061509011d0c0f070605040b040c0e0f07031d1903 61
    0xa50b1040e00e5a03031682d06034021840d83c141441c0040c4000508040046020a0f8181000d40c1d502c00004044641ea0043d40042c5000311049050b02d0011104004a50504410801000800c0c000c4031400fa000b000b22421040c3e0000b0740d00c50604504241c50807102c02082800069190f00015003040310b0300b04900014030500010300c03188002e9401c80c0c4c003240d070306484d498196840c0000000280d889660000108010301220765814482c58181600440c404d0f200541c85820100da48001c0340c2d0542d0015000303600c10407600f00e40c50302c1074031200e420940421000c031300120003502096250a032210301b41180d1040d0343c100411b09680a20020030305001321490003650349c1e00c08a0701100d0320190b0b803000f40d8818140c00f1a10f4070185a001f0149403880410280c03d005564898070119001220151600e1101804020800403e4200000600410402810381c1e082410700181e07a040014581001e1560344d003040360035401e02070560143c3e01e58a8040722400d140c0000c00d6821001c0f00c15003180407450403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 905119721 1250 905118471 905118479
    0x10e0103020307210c1b0305070f0c030f030f0f050a0507080702120303010801020301050102010b09090c360115210b0315090a1506060210090804081615020d0e0d17031f 74
    0x2446c0020388281d019651581009032640719030007000c0d82d2038021103803a404404004009040002e21401190190701c03070340c1c1d6050300e029000e040706030390341000001c110042014420154125050340d052030741009030701d0348840a903c0428441d9482c80340510a40c1b00100001403400341c15001181a90713000e0740284004485103040c02540d03d01512018219040100445502e040803034a014000400c1d180c0c001594224058100000c0504151681d24080c0e0800511031a80000d01c990261442807801145800c00512840d181041c0401d84240507900d44440c005290b42c1000070400c03202c01540c82c0381306810306e840c14981d2031407401d01c100c1c0c00607020f00005040c104a4030071001190240d40181c101100421020701c0100250700c1e00b00c2c2c0104080c4000304000d03400700b0147c5a81080a5010b10810307003800040904540105c1d181c2d4210340c00700c5d040a1059510859030b840340442a03070400d003400c2407403038400030f0b10b006a0450030132404080704014801d502c2040c1480c1c00f60714003075840310320340e11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 905120971 1250 905119721 905119757
    0xa0204110a18140904240903080603030310050909070f3209010501050d0912180f12060b03100507081f0b0304080a021f090606090b010e0103020307210c 67
    0x101c3c2c030942001081c01c5000035102d080010000d50301c24400e41c400003aa88284900c00c0c02007083c0141c5c030440d9a51954048101500a01c20a0700450100d0045044d4504201c402644402e5030140900504038040071480c0c1947c02c2048030081c000720b4070900a05a2680c5a4031041039000081c40366140b0b05c500f80604540001885070711241c0094071a4a2580c2414010354143c0d11194084032155642c11003440801d0b941d5140c0c1103c03442940d6502c289000e04450325140c0d110b80d4100100300d03400c0300d908100b00c00400346107080c0c441c3d0018000c5000700ba81000a41420104000a400d0700c3c2010200302603d1b0740300039a13901c5040014407402001e141c142c1c01c04010b0740b0a0080c406500c1042011070701043c04c00019008980f80751044503603407100404c0c03400c8404640482054003c1d21022176008211060040c00050002c08104000b41c1c00e2200000b0290f50070413441d94181607000003c6243e0921540a80c08040000c07000360001039041110a00140003c078003460002d20100b0f032018494070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 905122221 1250 905120971 905121017
    0x8060f0105040903080106300c03050708090c0d02010519020708010608011512020a0518091c1209030513030312050a020436090308090c0a050307030303020c0a0204110a 74
    0x180540c5d0300011a806e111040d14501000d01ca104e8180f101d800c07844590810600c003c14212102078004588901c0000700030f4150740c1c000e0141d01c180500b0304100f102c080b600142e5002e01440403507100c0300c1e070805800144c1c4c2c1072240f541000c41d44103405a80004041d0009110300c00c980d402e0b00208406a0345810a81c201c65243d101a206070482410130050b03100e100245420701800180f2920489580d60006000182c500700a103103486802c00401442030003d000c003d42488000e40d01041c0ca4030000700007001c0b141494401003416079502d2855080c54031410542d00800c0b01003c41001d016101c1c28041c01c2144401220b1281e941040c0001d449080301d80251421129013060000000a50b840039820005170700c02e02c940342c0601c0a004c03414005950140c042c180340242c070740303001509013080d54904000b80ca13841103006109854080010742c03000541441140e42600d00161100303082060f241c100998100e01030760260401103590203802c10305d4001c08060100d920740c0148022103040e0350703000c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 905123471 1250 905122221 905122223
    0x914120315010806030c0d1b080105060f010f03090506191109031207140304060806040b010c0b0c07030c0804030c0e070804021c030201150e160c0804120206040f08060f01050409 78
    0x44108000100e550046503c16041800101a6000e8000540100700c0d1200142d2056484151040350541d031800740d692072030040e040c04c00c0203001c94541140403c0002d01d00311151410040c04840d400b01c0c10f4400d60101141d11b07440416110740c1d05000f0300c2c10350118502c455480740d60307203480b44030841c10494008440d4082006005403480160303020681d03160303401000d01a5407110003252011130800d01400240301901c0141c50b440c40c54100a002e200072180c01c90046414071001e4000800464180e80006901060507080c00780da9040a1404503840105a031004000c2d002c0413502004020808920405441032421018655074a11000f00c441071011382d4040d410144000e203075030304540101f503560b003091b000f40000705005e20760403140842110264810030001c904141403003a03074a00d094242c80c4c0251a80341c00542c8600a440e500b409214034445d00c220800003000040440d115a4250382c010105c1956035108159107103139641e2a0541180c520420040c542c00106051800d40b0500740c0365 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 905124721 1250 905123471 905123491
    0x613060308091e1507031107231c061a060f07062a0c0320150a09080912012007110126100b071a31031209141203 50
    0x5007204c60402e114aa01c030311001d908202c04d0490002840e2403c20030000201030f24601504540b114a0a006001424548441c0b00780202e1f8044082950102010b848070f03500182c3c00515480c100d04c04500c1118514840ca80000020480180381c002c140d001e40f400c180941c809200030040300c802005e4100004803001005040928a80300042c030078044858520f1090520200030308a41c0c0c0c5040103401200c11400290348120b451003403c4400d0314007540c014800041c240040107256983ca1500d0081c0d003002d0340200c040c0c6400c100450f600b50020350031901204031041c8003218101440c03501ea070181100355061800103d5004055104101d00c4070b10300c40003888007562409d51907000a4800c4043d00e00e1040b02424a00480d62120001c01029018498030703100051541c01c00700a0303440b8100808030150782e07504c40511250b240c070b608a00050300f40c0303404c50146031030005d1500741e500c0034044c5085c621081c13409505000304500006400300402280342100c82c04240e221507028944021a03844c08a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 905125971 1250 905124721 905124739
    0x507050925050a0903020418050f01020f04140d1a04172505010b10120b030c0a17070e10050111060402031b0609100509100507050d080613060308091e 66
    0x92188202d02501c0c0119842c58440c440a40e260001403c1d00d0030106092188010b5100003c10068100001038070030044800079030601c4102404408a03028500c240c1d0324000e000307104000c955407050012921a540007040014125241200b8400c284013180e045500c03100100582c0c0c01d41d0880001c1c1c0303031900d002c036496440ca07071070345505162030444d41081240d00b90340b560101500c96a54481050117100300cae58500c4000042d04069006541200302028000d8010011406440d219004800261041d502c1d10340c14464003074503410300c0c008056002551008008043c04124500c090350700c400c03180240d9605180b84840141240c035014251002589a8041c07224040c0703e845503141d0150380c09000744030a013440201408507466880d10800b15002960001e0882403e00e000b02d034021070400710703180450800350103607900790b9610101c04156041c00074500004005540b601e0050900710740421062001a5480ca031a8240740c008000240c4143d130010780840a2180440e80480241402130003c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 905127221 1250 905125971 905126041
    0x70608100603020d0b04140619080303130c3812180a060e0c01030c05160636060c110709020717030106110c04060303020607030b06040504060305070509 67
    0xb00035801070700008103041c0c90ba0402441a519446100c0d54020a940885000e00c0e010b41003041c1081000c800345211880c59009021b13804001054961214041200c0b02906031141001d10780742c1d074907038005e035045111144d40c0000e1090705031160103551214480e40c01460341c41042550540a802502c0c0010030f01000040e04085500300700c41c1c9603117030040c1a02c03601d089689410007515031114a42100c0d52284511800780d50741841201020201450014144504002c1c02c1c005800724400c080c02d01900c41014159105020081484801c0300255401030060309603458518820a41c6060380c0651400080e17009086c000e510412880313104d800605074032428a1032000080d04007080c15201c3d102d040300b468283c240301c0c0004602a00b8541ca83c502a950003426052406a402468500480c2444020400290000340312138100389903041c04540c61f0f40420104106000b690311840d4010300303041e80002801000b0a11106a078400e407281001c6540e01502e110b0742c0d080ba180d00d07240102e0002501e0b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 905128471 1250 905127221 905127227
    0x4080703020d114305100903030804060207230a05331b040f14100e040c02160f06080604021e031003060c050301061b0c14030f06090f0706081006 64
    0x281503805218003040b00c5042c0406070400c6000c00f8440c40100c03440300d0805d0000380b0b03101d085408440315a01e0f00c2442035046030f0700203124a02c003820040406ea00031071001c08010300300405d00c5d083c0300c0b08034440c145c020103210100d5550000000070f030348034003034100e10308113801001a0700d00c201000e0021a01f13010240101e041d0041c44020184110031542d030181c5481c0070324010052008100c54000b401440d4203280c28100300741c00c40c40b4401c0c402c032003400035904c14540000441d90720460887c1c0c001061050440b05905044145c03103104240c0b40308200109032000d81440402c141c6001e1341d50b89040e40d03980c0003404101d10955020b110305440c0043c801d03040c6061640110391102901c00c282900e01e40d81c3e034030351080c3c035160554080400c0d40400140280d560010125000c00c0512540c005544055214180300700d150f0f008085001c0c1000d007001038651001c20210303034880400070489001d8030f0200d031890388541c2c01881c00545405080301c00140c992050f01070502580200380307001c80040c034181007030f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 905129721 1250 905128471 905128513
    0x50901050c0f0d11040b1201120c050f0102010f11190c0b0103062c21130b030a1d07050f06030f0a0b0f19050103060b0703080402100c02030604080703020d11 69
    0x2c00340e03a548034003820404d0b418400103070000700005100d01d511000400d100480002050300030844c5182d010340074601080406411384110340c000d80d081a0b000d0311080c0107d02400a221024404505006009000c94090300040c43c5685030030340349400c10100c0e000300711580821000f010300021009001072000c5803080d8090001c0c08004860601007081780e400c1c0020913501c1c505410010341040200f65641440320202040e01000d4050300c0d0b140110001c06100024110700914519104c003000007800d004040d4410380c0d40d04540c011400300d2158035003507586d03100d00714002c10f401200c0d51031007107080d8249081900d008550810301640c807a40d0b095a420010721145003030b698003003001c681080640d190112581c900d800d249003900c51040c1400d00240940340c1c00c1c2d00c103048100b000c214600c0030a90040ca1030340c00ca0350489010079282e00121040703488603104c2c400a5418000c9200384810002040c000300095440390302510100385000e101540e40d41081410071485800c110102c0c00081108621 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 905130971 1250 905129721 905129737
    0x1803030f0a150602032502061b010b060c03190807090909030c0b0114040c0e011b0f05010203190510030b01051908010c050414190b030c0c010915050901050c0f 70
    0x4001440e002c0705400c8525445503500032805a0000a10700c0c01caa840521031141d01e00da40d60700500d420000b54003090007032080b61010b0509010740302c8803036860034080d008003034401e000030a45910303081810704580d00c981c803200c046d50084444442010365140502103817442203000e078440350307041440c2c0702014010388400b107411010020962072100000da0207008041c0644820340740b030003048115009100c11183c90341d24400502940f0360710300d0b000c0c1c1c0e803040c410210000e032801460307020701180c0340070382c000e1041e1840100365500200c10001400d100c410201c6090385120000e110036140d1813180000202c00b40405003030408628014403c50902c0110160f40c6c0000001429441e80c0c0c903041c40f07084a10755018500000d03c002401c000018961180c1d0081d140c00f12003d03204000c114000310b0100440f071080b030162050110000744503c440c00140e44081d414000240b00142039490540c244038100259003140d2441c01c0041100c00030140308803481030842c210b4043c07034140900c030041701d0f54001d140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 905132221 1250 905130971 905130991
    0x60705071e080c01080103051b1c0605041e050714060c060a05060315010e130c080d0203072a03020f0303091504081c08130606030b1504051803030f 65
    0x100010300d00c03000914040c85070224014255050304003040c1d2030070444078a00c032904000c00d000041c4007060300419003000341e070f411501d2044400045c4c0040750050f401c3c002410384007152a1039040a1010f960401071003180300f1481c15072402c14280c64180b40740e0002501520300c0d409414107010301c00b0340c42c0c0100c1d401c00000742504e0808035601700043c600354088650414150b1920140100b9050402618410005094200b056903041101d00505008020094500700384030038644010b021354031142d40f0142c02c151707082c1c070383c50040040007030755907070000608443e50050103d07220003800426100c0b40704102002800e032401d5182d40c0130025821003500140d503050108000d071100c5566080c074020003500c0340d100c1954803513160030006c5041036440c62191340102a043d003000aa9035124215a07032100081c5440e0030010028184500242000d800003005032140c0c1d01031010f4802d04070941098000c2c103d4060100399034005032007a807500c0c6850916410b074014008140c5a1250181c160344c0101e102d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 905133471 1250 905132221 905132233
    0x3050409021c0516020d030207021e0a08031206010e0103060b032703040609090b010f0206040308070201110309100b04060515210705070605060a050d120e130f050108010903050702060705 82
    0x8150302d0102c0b03a064800003440e0190642142605805226480090b4035a060071030400d02d140d00800e4840d56042d440c0040803130030246d502c40566a11642101406124046944450850003c060b054106882e0796004c10705085880070380e58407a0003003800b9942c81c01ea610317007181c603030b0b03e0b010b224810301d0f00c4040007030902c036105949030307150070809800106003a98031005128a0b00355000219064455164104444080c054a180f500003560540195052401301025902c800c0d00b240145160034086d0850040001808503c04c80044c0101d204049001e040001d6516082007000312145031260580007403540c00042c291016120240c00c007201c98443c0e01c5041412800c80c4640a142214001c0105e00040381c001c0c1406a584145644510141c3c1c01302645400c1000040c40d01e202c0d017000804500c5d140400106161044440004a11020b80f10f00200703c8000c00e4080a001611860180c5604d02400003808440c14000c2890881e019114180390a00d44d0b024001036034080701c006c0c0c405100344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 905134721 1250 905133471 905133517
    0x90203100512030a080c0702150d0e0d0806030c1008010b07050f03030a0510120b1602030936150f0d0b040f020907032a0c0c03060207140a0305040902 66
    0x22250b004299882ca1020f0344d5a00415500941500d0020b002ea1807062018000c5100680b10440d26040141c0c00c89020342d00d401d411a42c00003c4d0081d05032208050083c0644549a03a41103060603015100c01c9013924107141c0d01000f2f10544544000400c00013404c89801004075070701c22001802414021015140c508140d800d0b0a490355005440c501c0c601036450081040310a03152050002422480d03050345021f9140e0703201c82c0c480b2840a40070310800b8200e2601c0c0d07101c450003041110f11103480504020290300c0c402090101031003182c0940803003400d0a4212030003c03180d481085216071001079200040380c3c002424026540c0e51b505c0c2c0150080c040c43e1840011030b00301108603114038450320380320396401d401d4814400b005002030030110a042c24408900e448801070407603440260f00c008a400901c4c044c110007100c3c00080c000703002d0f00c00c04000b84040140308a0345c0003800c10368001c1140001c92031a07214110b503100d10901e000342c00602d080c0024080074010340c0040c00252034544015000081d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 905135971 1250 905134721 905134729
    0x7080103120c050f15010b0c0a030f0306090c030e0105060f180402031608031806190305090309060c010e0123041203110d0b01020114010b0d05090a0f0c0608090706090902031005 78
    0x100c0b1007450b0b040d4040b85c051400281c41d500701d2405007494143c070500384200030300020f588040025004061045862201c01941d100740d12460052a40d0b4006020300154101d000e00103084103241c05a02d03500380b10001703940782480d480413a0710ac03001520810040041000101c0c0d554400750013240d0501420051034007100c00641e088010300b010380082d60b5100f51b611908800c1044507942c4a0040005102d85007441c10000c0ca1001035010900700032030140e03070740135882e811486407401e0954801004a03034126510015404040401180402040709800d04511206000014440e0030322403001600003800282448004250b0200c85040100b04400106020005508000040c08420740d407840381d02072540e42400303a41c034100903040e5410115410322b00229a00d11416500001d00c6481d02d0219621080070401662242c0c0c00a8440f007104401e8a8030b00c0e404a8603100c0c810001d0181008228000004100801101e0154951f010764a00c1c1c012004042e420003402c03900360001c00d5000180d80c0d29 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 905137221 1250 905135971 905135983
    0x11d060d020c0f06100915090905280c09060305030a0c14060411091f050103090503040506030a05010f091b0813140304150816181a1b030307080103120c05 68
    0x1400201804e42441c3c1005404041c02d20f6034040c0001c50700701141d00c0d86c4040740644039001d6071004000418103034100c0c1011071130f06012002d81007200382040590780c9041981e80d4440540351091009408155607620068280c5e5020b01014209800410940030079070b0103152005101403007103880100045003061080c0c00c00781d084400351040d0354030308010711083c5001d00030154441003100d10812000c00b418001d4410391050701a0340d0515907900d0401061003002c0090f070b00200300003042d127a52490b103060f404012b000c080c40341104184840307101156194040c06410b040300c40308042c8403044a02c1c100115161400505040100c40e10850314002140040c0c500741445904400250b646d07601c2e1091041078100d0146220742086140c20901440325401e01e038010014105160682d115500d012103819148111340c08442d604205104800000c3c400c4006030810040c8908020402d92104a020751a803100311844000550a90010b00014408400114107815949026001c030003007607448510b00300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 905138471 1250 905137221 905137243
    0x8060111010911090601022a131109030c0a0303230c1b01091a030112060204210b0c09060702090a0605040e010e120a020d0516120c030e011d060d020c 66
    0x2540c3d40070080b0b200d040004140340c011000784000c100c0010f200591031807520010080e00c9408031075080c10340ca01c0e503a0340381900e504107400e182003010f07410b140c5102006074031400c06e4038000c0c02001c0c801c07411841d10310301010440f42c08d85c40b1b40340c101c0441014400d03038514401c01c551000078280405030000601300460b485940c1c1c8103901248a40c026000904030003c0c591295030700a0b81307c0f40d4800307000c00900c140c90444030003140d440c24207651850a14060b020301d030030409410109500c01d0b4560070144040311191405241f44d80c0c6c854450407400035241c8244030503140c000c8c20410040005040400e1400c1e44281d03034030f07400545144c4840008046e41c0103003050702c10903911003c006503501c0c2d040c0f109210344003620941c50301c1c203649041c010752502e5902c1c0341d900500002240007440c1c1c2004440d050002948407011103c0c00c01c00000c080c214041d920019400100c0011a0030115409101a0280b80034062810b80b0120344031020071000e03500280b0520b0300c0540030301c86228200d104201c568205 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 905139721 1250 905138471 905138483
    0x306050901090318060c08131e0e01080c0907050a02010b03010c090f080c030c092e060e010f0207150216080705120a020a0332010c09060201020c0706080601110109 72
    0x10ba0b20b0381401808030090900040e034905000307008002a60700314000310060f41d80001c1032904e5980010050600001d01e502ca42c0140158420b070350790104132404c0a42c2a1041c01c0c0c100880c690302e400003184c0d107170344a5440540100c4018041240b00b030203200900100c40280c400440c60503102004682903c0c00c116814010680c0d0740310912804c6550180e58024040800040c07036509030050002e070341d40d0400e51600c0d02512059004ca40240d000d448440060200710405a402d140c001c1103a030317000c605d2481000300141103502034542540c0b14251000318071001750b00a05070300342400301c07800000382d0342625032065216445101002c00300181a4600070403418000e000c0191500c000d108210548000d0010280c000c441c0b503000598901d134a8505480d00702c0442500c000d1080c81116140f07202880080c1c40e02d0040030300740c40c0c0301015045150007007032a6603809030140d41c51005038240d00442c1c407150000d0308008800e200441c80b481c42c656016405140002c490b0f60120b8869003196281072044c0d850b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 905140971 1250 905139721 905139731
    0x1020703030b10093006110a09050906060d051b040b070309050f030601091a15070506072a03030e010509060406150501020a08090409150c0206010e220203100c03061409010305071a040306050901 85
    0x8c080e0000303e000e00425065401454514100300050282c1c4610f0340ea05800c107070380e0000700d0002880d0a4000c0fa010300406038240d6103545070b1204925a8002103011000680c0b82c1e2800300d6130b410b142408611600b4090001e200b11303407e040510001d0715002401c0c586408404800b40c6460356009698502d00700d01d400d40d507548007541e042850402070b004004c44140078000e00024245c1c114580030211004c0400c81c0020b10b250145070813001350a421100701459801e290034060820404560b0764051031280d00200850a5a01101203521501d44100b50168002050900204508400070030044100900000d28000035664442c020218400f5014440b6075075010304003416010131581740074000450394404c140c034180038040018080d884100402001d680200c41c1151401c00c0f007682001c1082d1000d114040900c1c1000300100868410000142c0c1603182050250424502c000e0580c1d8003c00038000301410310940325224540078810795210a010000000801d00a110f8507000d020000c1c0003080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 905142221 1250 905140971 905140987
    0xf03051f0f1d0702120a0918021c051b0304061518200d0c14030c0c1b180408090a03060e161809021201020703030b1009300611 56
    0x61030700004041d0300000b00305141030141d8280c0014040080c02400031516070303a02d050400c21140c0f0255640142c22400d0b540c00b105265181640281c145682c034101c881007004804418801510782c2510310449091001d1102ca05004410340216030050007020003007581c0d84d00c100e030900c00d0780c91350f80070b40000c1c004003001864000350380c0502c1d811404807a802e24000300100c050110644201d10f18205002ea440440707400c0540591250443d540c5600e0f40306840f07141c4051341034802d5201c0ba09120369405800002c1c072102d10000c80b4115142e0010f0580d0301c4458100184540f5000d0140060300e11303e509001c04100d0b82c1d1182c901e18061407284c4400300e48082c001061a1905190a4042c00368101800303050000707030700303184008910701180c0c4404140e441040c0003182c2d82c4244c00e000070844d540009502001c1c035800d504801c0c2a00c8080d03868039080803100c40126001603c50082004448410700f1010b13280034524040031824810818406000b840c1e942c82000702d0746110206298a0760100c0d2040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 905143471 1250 905142221 905142239
    0x7080c150906100b07060e1c1202032e0e1509060603161b0507030b1b390a060e060705070c0504020d0207021503010311100f03051f0f 59
    0x41d0308150030728020001e900b0301c80f2a000c9002001c2c042c00112032004034103441030110f10781100c034040610600f903440700e4600904144600705036820080c0414a102810181c0360128821640301d0340715011a036449504100304800070501c001c2c80030185a80c410000b166102c3c0000360f080c005c1e01c2d400303503606000704180c5c18011341420040400f0312401c0180100701141c01c5150442d44100050b14081d020703000c110274906958901003001505600c6481c4002c010884081602070041400104078070f2a9a01c203208100f2030700c507500703407a2909a841d400b01190301180c120480e0359603040b8100b101c54040741c03801d450315110a02c4800e0381c400e921107030314090315602071144c260001450300d4200d00d400c1081e01d400140440c2d9106840c040e40d40090b200c2e2183c182350b41540c040943c0107064515071410071405903015002030006484d0a45130000b004c1551906141109003026952906045031b00c0c1d105060f40104401804088200881003170000b11400b0800181c1c05081451100e1104c541408120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 905144721 1250 905143471 905143513
    0x10080f100302061207021f051801020427060512030706062c090a020405100603050105040603240e010f021803010507090302120106080628050105060405010e030307080c 74
    0x14100000208401d10142e1944000c0f111040c4600e541c2035141c0c1c482c86400c80c60000c2910030600080e00014a080060f00a5000140100c00d0000305840b500240d914040c203c0c031551141001d890032a50092104d024466800c003e20f40380c0c11030000e0b02c03035901c80105902c4400c04501070310342e41001038598104405442204058482c10807d0102c041e1320540091040515802c060b1401e5036000005a0f541020000529002c0d4081c105001c941043c04010388174044501900d00802e062400108050400344a0030045a800460b008004a04071300224110b01684101c113481030b84480592150101c00d01401b18029884040140e0319001101c00404031010500b03054826410310050009031644250140c090342d404036220784201d8880e0f1040350050000d603009a41c18001c0c0300c20015103c14500d025840a021107400d03800f1170070743d00e000b0350032184240100355104005100510907035202e82449160660054112440c0400b03175154500d064018420907061a8419901450303140d05038280 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 905145971 1250 905144721 905144731
    0xd080112031b0305071a0606160c0306090609020a0b0c060c1c140601120e0d110a150507260a0b030102040f0801061419030b04150509160b040e0402040c05070210080f 73
    0xf4041361f410424009000f52051018000e40c1040f1017a6031800c0c801ea41712900025540848108203d030b01500c5d00502824005400368400d4402e12800200180c2c1007003202c101d080d2180140c43d036a039459007082c40340e80100c2040410302d2a107921111380b5040a204a500c0c00440340d80440301c82c5071000004028080c9002000c20580c1400e5010900d802c001881d010f09401605100c00c042d00110b00c1c540c03801c1c80204004d040100d11003c0c90038002e140740d002900170301c440d680d04000c41d5400c0c07080034101c511100030703000003549650000d40300e20800c2e03004c80c170242e60080000d40fa05507215500101c0701103540080311541d64800e401c21410141c0b040c00701c8558015605426aa03072100c10100c004241480043c000c4414040000d04110b5a4800380c2c000d03840e415010006800c180c0495540c440c400c1503206141030300458045003859080c03040d6806c440c4480780103041545c403a82440b000d1701d00c11a007103061000a000010050340c482d040c60511808070365882000b0718109168180d02500901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 905147221 1250 905145971 905146013
    0x1023070207141230070c06030605061207030b19180c0f090e06061308100507030515060d0603210306091808030402030c15090906030d080112031b030507 67
    0x1030341040e20001140280c0840203000400c64100c0381c103400c0d804850200018813000c0c0c100000c0f503004003e0100318120644e0003945e0308024080c0c8810130f001c154030800301600d0101013070070300062030140f10f0781003040c0161000e0b1510100312150700a21240002580110466100c2401016001481071159441440742ca00c0c0c65282c410740b00c42d028080c44001c2c0150600c80c5a002c0000d00251124070840e880301113421070004980b65114443e0740c4a401140c10035000341d040c000460f020314400d001d214001c440e8504005e10a07010304081016030f03880280041c61580d01c2d00b2001001c84d4040c0b8643c50b844900d50401a60a030100e20f0050072190560801c15100d0f180081d04c0740c1c0300202d0101006115030100d4015565201c50000a140814083d803c1d60320817502d81044203481d1a0201400410307070180d6219003d51070700c1d020151600c1c42070080ca0001400070004004d0f00b80c090200e111311034000e0800800303000c82041840420894440c0607004900e0000c1c02d20104504802e004203c94803c0c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 905148471 1250 905147221 905147239
    0x3040311090c070b09030c0d0305090d0305010302032808070506160801031a070302090306270c0f042a090e0702010c0c11180a0609060b0c102307020714 67
    0x89812a8580503c810203801000140b0016448540800403202605564002c60303103040d8a03510002d0207040c0494400d0028010a1840c40303c0e00c0c0a8000d0034140ca9009002d03000d21034102c860902440c9400c060604215200600e050200e04500c001b44001c601441c084c0c0100e14001e601040000c3d48000c4003c200094400100003080c2c00704110644002e46100c032450034ac075184412070190089003480755150142c40284925510200c801da01c40100d0585c0e00e40070701030703052849500c40100b658042d8001c03862002c5840c0a00d0300c1d80c05041c2003d401300040440d400c4904620584034503822108000c0f491390481400035041c90640c02d80e0001007440280668520010001c01d80c00c10000000c00b01d000381c92085115075200001c6609030154501100e200d0b184c5441d40c94094615880368011203071603d8408510216810110b50781441d079080280021460403466000412074055110b000e078880d907001c402c1c0050122442d6029441e20f034020104c040c10041020480d660200c904c40c4258001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 905149721 1250 905148471 905148481
    0xa03020d0c080f0c010609060909030512130c06050d0b1017091c0519020604021e060708030106210c02070303120e190b010501080f011e170304031109 66
    0x4000d000300c891840e190190244034a00507410f80a41074400115070300108060200d41c81c1540316038102c0d45481400c6c4000d96541d14110119200c0707000280001d24200221054640c3e0b1401c0c0942040181c84084454980e6444105400c0b072640c2040c000a000024000c1030000303540a03080c0d441c08103d8202028080384040034200080c00d042007154a010100003c80741da500303005c07c142420440000040070100050000d000b540b00851280d0610382e05102451510310004120348a03540c068210b005078248408104010241c15101e182d20000030482c900018584902550007090203440b01d03007407580d603038660009500700c000803128a07600e489003d0740b000780e0005448086076054182529065803400e080c90180038441c00c0100c15209200e60f40c0d000d0405541c2161203d800341c0000d25580e602c89004503885042921100c0d040840080188000c90030185030000f04038026401c5000c10795500e8603811030907a0308083c0422a003001c80c0810603c40f6200400c041c08408440c8607655142c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 905150971 1250 905149721 905149723
    0x30b0a0f0302131b090e011203050919050d060506042906131a0403050f0616270608010f0512030327030301030b04140607020703020f011209080415020a0302 69
    0x10520000c1d00c5101c0a4800f442c001c0c0050f4010f0001c0c0812811100e00a001c21030060580803841c45001307841545d100000410202d4000819962903150340ea4600d0042c3c45801c100203038000c100410b0343c4146040780003079a41d64154462003002d1241d0400300329841e00c41c1c10413003141d07031203160100b4507141c8901101c44640452160b0b0300c903940480340c1e6500c0e1030301c4410a2107060798680103c6604140c0803495000c074080070b40600100d0340f1840850b42d03404a45114162200000c0c1d8000302c204002544a040040c01600c40420b1580c2c0d68601c25224500c0c0e00d03c03000b542c0c00c80e174007040200b803c201c014003402d003102c0034840241c1016118a02c1c5564506100e5590344401020030100c410a525944a407405508078040012100c00403281c0729616030030449075402058408840c1040c1e81082071060101c08500c06100e80c800b500540003441c83c41d0203100380c1c480504100750400044108180c012003d40c8141502030340130300d003025110340c10310600082100058111100359030100e5841070009034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 905152221 1250 905150971 905150999
    0x90203100c050403020904140607051e160b070905040e0102040803121e0106030e1506010c0f0309122003061909030203070f03020c03011506050a050c19050d030b0a 72
    0x5400c00000e5910003590003181c030b9002d2a000207500440450078002441906801c081c46103881c141038a1140c0c5482206558502c00c1c1112000c10000d105442030b01405e0ac407018120031001d0003910380c40125580d03281007514404581000100c2c49900050066080600c69040940c050100071807916081c02c442070341d80d000314149000003856000c0003d0119580740307480e45820618402030f48a55855a8003e400307802c0d4807003608103501c05c41140846010702110701a005000684a000c03d003500c41d2151a204107803c00150280200510005206400070302c03034003029402072030310b034198580200043d07215104008076180300390300c08400d0114800d2900640365030301d205200005034003085850282e0840c020b9460107040b8511250680090680100e038803251607000310000c11406118962410214496000b090000303001070100b0a81f0500a40050894885050440d14880d5107424840c41680d003000341112607801841c00180040c0e014010741c842004111003602845081001500d0281 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 905153471 1250 905152221 905152243
    0x903080726040203031e0703081005100c14071401090e0c03070c0c05030313080d0903230f0d032403080a141308010b131b031112070918090203 63
    0xc0c106002c181150342c20030850384164100750303030903000340f584811856a80c0c104500a0707020030380d40e40000e404000c441d000002034540c0101044041081c80c4400c0301d604440006c100c0e5800000788099a03001070800040d001000303884031220f620110400014188803007a84005030351485002031200418080303098aa1081c4c2610b0a108061150304200307081000581c004c94150000052090500c103160300410103480769902145c1e00c1e2440014212240f032454800600240c80c1c10150942102001c8500c912000c4007901701c0365115524040f02e07080400361004040420790326001202c0c419103503507583c49800d80c030b06038040a891658481030410b100b03021070f11003044001300604a81780000b00559403203401415910b4906501c6440c014001d0400346541481445548140c440354074031401031106081a0751003c0c40807000b00b0100303502401d859090111142402d11402040101d64180c46200314003070707030f00d184105181000404100b80381d03102c0300c800340782041418070250301e0004a0380911 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 905154721 1250 905153471 905153537
    0x1902070e040f03090f0b09040b0f01081816090c030b0307120b07091203180503010605150a02010b03030a0e090106111c05091c1205070c0e0a0b040501030609030807 72
    0x90050b0345000c4404a00d550003280c984203410201003442c030301e21409010b9200054070104034071f03003000b001c010026000000c0c40b400641c03400001124420844001820280c0100445400245258a4404901c640c2c2c002c5100d50741c1d240b007226122030703241c0203842000c031040c1d000c3c1200a00b0404400e281242c07005020f008260340750013144455100700307003010041070421001d0181c03600714a001010070403881c5002c02c40e01c2d82d00d2030100d03191034103220b91021924007c141c01488400c11200302e0554114080010940d580d071345080c4601d0701c0900090036a90400d0381d9941d0b041c80020100030400d00f0603044601000b80d000c2742e60381c0941c0c000440b04038051003c45a60900442d079030046469100b00d4100a0704480305502c10101024011180c00d8041d1041e0020040c1d5518204215101c2c000e4000141c1401c196020800c4214082500e00f038001555440214043c214400414140c070420307841140d025030307288075041c02e1560158506401241501c1d100500c050042451003840741d00804902031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 905155971 1250 905154721 905154743
    0xf090102191103060702060108030d1104030503040608041505060904081605032d0f0a11240603010e0105060604090b010c0210050c100c050f0f0d111902070e04 70
    0x280c0c0204240040a224210390010348001440c0c0404801e051030b082501a2041d00013141c42a8000b051403416285d041004606052460300340002038040e6042000751404c007000007001003401400103001404003a1284103181c00c0526100010319240030065105074504020300c1959600c042d496078000e6080907145444040c080d104440e80c2140740710081003844002618240c041885810307a40340700030140f07080d8100940190ba45220301c2100841902000c0400c039002066002d40860104407070008121403000c24031190384074901e10254075110342e995103d07080008501d801d0248401c01c0004000034451030030040302003441780c0100e000c0e40c0101501c0e81448080d99204008050310250018211940e1140c0c400c0050116071007821640315900564481c1d003c5001c1d28042d5030490340031a501c41e0b280001d500c0a90380d16810030803860b4030480c0100000020714145001d04806481110940d640c2c400030444201c000164904542055400c00d40c4100024580320070301c2c990140d0410b1003102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 905157221 1250 905155971 905155987
    0x6031109092d061c0f0209041509060204090605010e180603030904090f020a0b0403122a0c1e030c030b060f09071e030e1e0111040b2802030f 62
    0xc0d010040c1400041c1c03407805803005403001400802e003640030b607506480001351443c0c24403400c005528643c4015058030508000b800040c140400c1d8154880c0c041c180e0503620038940041031003034404c0c5400039070308580c000c2000d20010350b0a11410740100400d0a051400c6a04100400c0c414421480000000b841c0070f4009400c50b00c0a004461101e10010010000030803e0302e8142c00b18042c90006038050301c811040454196407000454003030360307041000c1310303142c40040808403805019124070000c8284060800f0528a810040c031084281c46210000c000c10b00340b600f071f001c08040d5013550841010018404002017008080d00000303480e004488510203964020200303516007403441306030b030700b001140d005c0200c10303984120b034509100340841540c595401c0c101021815180c103180011000e401a840c072145c41200c07481070b048503001c03103400070800418115120700c442e001940b10880c07803080000c1841508541e401001d0b50000034680c2c0985840510390b00941d6805194a850500350002550074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 905158471 1250 905157221 905157241
    0x1206040c1206060c0506181902030a0b0a0203150402160204150b03010b03010e0105040203070f200619060f2403020f03040c05040e0d141b0601060f090603110909 71
    0x6100810007074410b0203403541e42d03807008001a840724019a40d501610022484003210255140d508800c41001040080c21413251120014140c2c0404c0313915101c0c00c0c1c15980001c0c620b019983c407401c0b1b186070041e100d01c2c0c6a00c10710440201301c1110b6112b184100080c250701e66140002d041400d0b01594001140284110712840010305604602d4181c3c0e0080000600301d284480258140d070314111040e5902e90743d031428082640000c5e180d0201017506010244221481041d40b5210596440c0310310401202e58802a41094000c0d2554010b02501c0590b1400001342401214001d0505107092154a894410070404131301e114240c564001109001c541091807090b01550a101c1890440d15a01c1c280762034403004502da03078032842d8040c0e41803404072542c051021604074844d0403151210700c0802c1d841a41600154000391004402e01c040c44100c2c4135404040101a018104a45070404040c56115015040101c00e52100b0209400c09100d02102c540400c00d0342d42c991419200361440e919000114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 905159721 1250 905158471 905158487
    0x406030c0b0c010f02191101110d0f1e020a0221030708180304081c031404020108090a080d0605011803080405010804210206060a05060a0c0b04030306030c060f03111206040c 76
    0x3844c0810300129512500300d034084031400c01d408460300c0f4265806500c12103103013aa008003400409008050202108540483d00a2400c800014900141c080c0e43d507810920b00b4130480908a0506601050740040c09404102c40c81002286500020a95140a4400031148001030150003006003507004aa101e45c2d21210071400c180c50841a40d40340c6844140c09943c035820304049011242c98040d40e00d8805009114100c8443c81740d526403c01a13417a600195000d000190114016109021652020415034000341414004403d00420300b5441c1030001840076542060030040c1244040302040001d00000c00c9808460b400c4c2001404c1c5d54035810320740315005d5003064000352121010400780c00c49a0104200e84201c0007101c07001080c989401c20301400d400780d40c1d03111020171035800b00400481d140080a0741d01c14864134002c1446502c0359143ca60300b4030a64021000319856a00203a036042e0580154103420322075403c803d00307142043c0d921480401c0d01400e6540169074501400100c64440e07191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 905160971 1250 905159721 905159741
    0x31803010b1003090308070c03170c310b0a092d03051e0c180a0213060807080a0b09130501060308390309120705040f05060306060406030c0b0c01 64
    0x148507600c0d00400806400303021214030403000551018002842140940c5006a48c160075549070060816411090842e00074081e11085110b841440001d002c0e004108420455100b40c0000a240c11250480f16844007507a8021203101001480a40c0c1d8050380008008225010401c401400b0b24000f00c0c221f60302420603000b8400340c02400f00c044140000001c1c45001c101c4803135203000c00401000700103a2600780c500b651960142c070091508200f210084042600101c50043c0140b60014020341100344c0c003050b510030404100000c04205180c0d4001300d400750f108500c900240442c0c611300340000c60024004113003039400001038850318180070b42540894084c42d400052543e65600b0030044400a50101443c003110110f01c1c2115608405c4104d612030310031450f50000c40c28141c0e1002040b90749004622480c429114600e000100c03030303031076000d2509084441500002c650804400381410301a000b0040c40c0110b00b460400c000155216540004403980d11101c2511088a20fa02c2ea0240070b02880d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 905162221 1250 905160971 905160979
    0xa05070506040821060a15020c060c21030405030f160501090606150c0503030105151c0603030e030c210a050a0b07020d090b0307030f020c0102030a0e060612031803010b 74
    0x400c01041180c000300822448400700f85940903600344010050350084c00f207450541100d5400f01c03c210840900543d90030b854a10700581c2d01d080c00380340204407a904a045056542d51094109912401a00c2000c0100380200d962541c50751803c0d4482c641d40e27114140444000c0040000d0035002c042c0c44c511b003114141c0d03209000b4000d40e205410b080002c3c00090045d25124540f504248030060700a442c0182c03861781c0000610306503031034a020008080c910304104031008008002d5044090110004c1079000101548002070050841c140148005a0f4204c0b0a000741e21801d010240755959040c0305941e80141d081d5a49856003181c0301c43d09201c0d04600040c56881213102e00e0782008502c0c0c0384e8038400c20b0254202c03100e103800d148007201c50303801c9885140c1030142e0800105a13580d00c80e802c2284080400c000161801000320205402ca0780100c880c095842c1e92100c40d4484440c0c180010354000004030380c03107200104a00d0324036840b072003135000d880132440c41c16035100b8183e00d00b07410040da0340d54020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 905163471 1250 905162221 905162233
    0x20f090a0f0506010c0308060f06040f08160f050d020405070917060405060703090209010e04080714060402190503030412020307050301020406020d1e0f1d0301020f0c10200a050705 79
    0x38a0101904040c1c0080c05a9400c0c03400041c1594891503031442a01d41560340d810303480d140c050611507010700400025030001401c20022a0f00000c44150000401058005100c05c4003021040c40e4050a03641010800c2c00e102001000660388a485e480e400a0f0100c500003401d803604902038aa040c0c030f6501410300c208040d400f2403041342c80420610710860007282500c2056542020442c2125403200c1d0003540b0043d500c0061002c0112421038941c0944180d4100745130400580710b80c1510489800707c50550343c082c50401c000c50604030103a03031050a03581651444181454002522070107980110030054502031000c00655804000b010011300000e0001c555854a03100001c3d25050b0107248440403e42c0440042200324040303000c0c1000161680c1c0d88040c1c4d034004001162030b050341d1000113404a0290b400070080c0d68080c801400c17244100000103070f031419000c5c1c0d090f013004031100b40030010514242a00d0140a10070b000c1c194549041580140c0d50b4041342d80c107960601038600003802d41d108034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 905164721 1250 905163471 905163481
    0x10030b150a121106160f1a0a1b0305090d0c0501020d0c09030201091203020a030309020f090f010f0803131a0d150515341406041106040f050904020f09 66
    0x480b010107410b40691201185450100305000c070502c078020511074005030445500002c90030000e01440614442c40c12100448500c10507072900c040192070001f2129a00c4146000e41d061184104012001f82e050601591501c0b0300300c00e46604c0d982e08501c05100800c0485000c0200070b504650405041c01c40c00c102d0070b040e204005021002602080780400c1150801090400800c484481441e070f02d68020000743d4041e5608401801c0081e508076003010803039480500320b546415076580300b000c4d0366610581c15850300e940c0c080c0d925500d50105180380c2041101c1080d0440141501d0161030f10000c0306165824048c018440510035410088200d5280c020410081013261141c81c040f6041200c801444d4906d5100910140c132035120003200c1008441c5991905e0880c1022056106012803400d20703511400340c03900b0850800c101c20449072074101e03134208400c01c40c1140300807110302030650740b99040a09040b400424005140102880b84900d030f030002e42196a151031085280300041e00c4d0440314140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 905165971 1250 905164721 905164739
    0x1d030708010509011409031204080a03020403050303040501050613020a1b0311071212030b061b03040812031906030816210309030e1504140307030206070c080c060310030b150a 77
    0x80b80381c048102c44100800d0100d06c0000503204009003051115980382c50316034a0b1000c991155265205045c3c00780400008500300b40f024601c80d5004a0005c5807074a0b03d90104006880744071114054180305200e1884041d40c810300c0c5245068a1903000c480b004114142900c210361030668139040c0d0320a00f440440c02014030f00100b075400e849a07580d0074501101c160f0070b4003990030180d41250000c905211041d03d01c040d040440c11000b5101c800c0d03900d0b0036110707070190b030a0110043e11300134920380000034040312040c040c14003612602824020022a42142d517090b0041c803c110811002c0050070805c80140240248403000d00041015100410710f894040900a0240301744180c000c52503800c29040581040314850010184d80c840315440c02d0b04280290030f542c0420041150144206540800181c403044000c200070790260140b050401d20b012500c030f1403c01352490701405040d05106100684019020a105a81c0d111a07034268a907102a400006c3c40c4102c00c01981c040785044000402c0e200c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 905167221 1250 905165971 905165981
    0x150f030115150f031e0b01120c0f080f010602070501110304150c05010f0e0616020106080a0c0f12032a0b0c0d0b09190903021207060b120d1d03070801050901 69
    0x69a5150300400f5880308400760f048840300340100800b10920000c2e80404072503030340251039802d01410b00b003954820035854042122500120f01010850fa41c00c01240c0300d401c0b4402c558803102c03002c8080019814628001d490701d69034880d040c1804185881e0b00c21490090064030b000c2c0640b003d4882e003410001100400c0f55010701d20079035035035103000303c041141e04450282c040b41da9100c1d00109001e444101c0a00f03030785108101c4103000c5558401002c541c00000307024004c42c060040c564407200c02c0c105803950601185950042c0c45020301c0c0228200000d070041d02d00b034000c04034410b118950345003640304083d2403420b400b0010301c11242c840402c005003400e90054011042c00d45000c0200d040300e601070040c0d01c0419502c4045000d0074aa880718482c401c0c2d000100424401e10554507900100040003407141c000b140c0464543ea01c0700125000b501301200c0f40c0030301c1e96800004242c0c2a414040c060a82c1c0e003c055441b54101103d0200030113500e042164200909440b0300800141c6804c2d041280204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 905168471 1250 905167221 905167259
    0x12100b0a0c11060705071e0807080a1101020601181a0d03020a0605180312040c2c07080112060e030c1501051801050a0608090a02060a02060406050f150f030115 70
    0x20881c0d00300b10504000041d1004d0a9024000f84038840c00c00f005109919541d204050100740140c0022859510900c070903001031840c0f4004050a404c1c500c4e21030308680035499001e0456210000410001c0b00910000c1070342619124001a59440403201410b40c205000075680c005401e11074050800d640060500c080310700846017000140c817500c0714480b103400050a000c12592003800051100044900c40320b41180c80b406850420a44d2440d00c05907143c80816284070100d9802000110740c020003403d294000c6440c0350400705036040101c460140c503d60300c00078010550703c400000d0795140030400c482d071039030a84003128a10410482036a012107800d0040c076000d15031002451300c1440c800349005040e50001000c20040b0360404a00300d4038044001d00042d10703440b03070311640005612407400034004c59901d50b010f000980b6181c1441c0b401d03200003426418450500404001048503c0714881072020400c07600213003035190402c0043e015103034000c000c2c000c000d800030001804034002c08c0c600c1841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 905169721 1250 905168471 905168483
    0x60f0a0e01031427060105030706080a09061d07090b09160314010b09030106050604150c030314010f060f091503020f0906041203110f030d1d010c030c12020f12100b0a0c 74
    0x38080ca4144c60341c450030207200c3c2c60b405074016801401014046e106c041d0b84844000c40c00201036400c0d84605054685c80074103518002084411007014100c01c2c0580805481c00b104180000041500030903110303400203000404030100c8803c44c03123180303200c0d1704045812800c9102100e404e5864100884095001c0c00559100350310b4802d00140c5410075405881c101e404160700000e000d4800c41040d280010340c0b4800301c08150b6102201805218240006400781061141c02c000407070034514080c2400141e42c9006040c400e40c2c02c000c00030049203904607001c1d41300e94070300540c882c1120001c91901c2c0c0240302c81d899100202140110f1414181e00c0d000851902a40e122040a0320710010300c0c1d140d01e1700051180d0190020050000b4205950f04245851002c40002c1d00c0701c4400e6251181c00c4900b18a24a40040e89440c0420f0b03030503501c691035001001000f2011840c002010426014520440402c880242c07280800100021a00c2024070002e15040a900d980e8404400e4000c00480b0b10401c11240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 905170971 1250 905169721 905169781
    0x12032003061801030b071b06021c0b0405090c1e030717190b010b03040f0609030903030f090b1905071205031909020607200307140906060f0a0e010314 66
    0x2101c502c02d006812030ba0404003c5455448900c03040b02d007110303013010800c0103c08003001080022135501c010420407170107601402c050000480725000390340c48146202e00c654200b030140000c2c10f0004c2003090316544222600303000441d107480e800040d88082c114a6034903010702000000c180960910000032141000192140c0c550350121f0b003015000514000b829024400005000e100e9607840110740184c042e1145081c01c20841d928001500c00412046002604c40003040003015080044034400d101c560170300007101824604c204005002d014101700700c0c1c41804042e403d01d540510116a21690000c0e031104410300c0d0a00c000e40194029038801021040303241444240385424415010129401000c552802d84d013501c5484042c000280d80c000c02541340351244107280e500b0481d02004100614842e0741c0d0f4080d100401002d04001030009025030810400b02d96040a80021500c060706d007410a201d030700c1300c1000100c004205011074414030700200707414884101f141c0122040f081d1361040c00105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 905172221 1250 905170971 905170999
    0x3706060c0b0121060b030304090f0e07060327020406030b10030515250212040810050901050c04060f020a1208010e150a060e0f0901030f050f07050d1203200306 70
    0xd4803640041100d58003440800a00d00003820351700440d48004000b012241099290803001080300c0d04c500c40c0050850742e900c03114080303903010b02442d40103180509040182015600300c0d070316900c1228144550b0b43d428513020700c04669841c1d000c1c601542e040002c000c1145001c4a54500125030341c00141d9031841041e112401c10a03101031401c2c13144100c07418840000001030321b94607908542411400640c01a0a41d80d1010750b01440030304010300c0d8110060034243ca443c001c0b01e0841d030002e01b86151590619041181d40a075440407203040758041c0c602182c100c001d13504100e0405164220041034004030080144013240c0c40f4070100c1c140d03010700c040040c9586621861070b07241c01500600d90b810100401d4200328507402425486101c400c003510f24050600e5100008103002026001250991003c41904007800001c015600085038803070014040c5c1420640003d10030307522400b00519084880221410603403080d04808400c0407a2615034080d01b01024801c2c85039081258024060b041288004c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 905173471 1250 905172221 905172239
    0x40822030809010815030d180b0313021c050a030509090f070801090b040213080d020d1412071407030804030f02010606050904051803030a05060f06033706060c0b01 72
    0xa011a80d000440310315124181d0700554804030010300c00c000003950018104045c1c1c406000b65040204982c1e9144103080c0c40070b045c54032601c26a0054020100c2c1402084050211a00020699501121310121525030f038540000d446050040060403070003400228002c140c1c1000107018937040c00c030341c1001141d850600903194500f040b26290001641c14004002c654466403003002c1a86005d8009490b09209101081c100f91f001e070300a078442d901c0300c55209020748d0b0511060321502414500195417582d04440200f15020b4107102c5e0190404280c0072278501e078016803a050020894410194403101581006021900e00b2181500440d44c0d0010038188144103208a9095070100e482c1e00c0d041c120b8820507c4010704006004101c80c00002c2010390b19030f0b804101962044181d60303c007188e580b5004080c0300100103e2070b5a030380106810f0003030104400501000d40c0c40c0144281070204000ca0380c59103024440e50400709a4031240ca0110007003203099005480d01d0003507018071460f64099903503034010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 905174721 1250 905173471 905173537
    0x23010503070804110f36041a0a0623011202160b10030512030106030f0603021309020a0509010602070905090f0627060c03012d09020d02120408 63
    0x4070000401000009000640d40420b5000022010342440c0d005807003000442d0502c1c5100b00d040800140c90184911040d0100300c44010700c1100c0d980f45181e50505540300c070800540c0540041a0080e80c0c2c001502130120355000c50b004084000180b1801c040240403c59001d007082c408a00140f0a000710b951a1089402201d0241c41520a0016854519201c28031a4038004e4600c0c00d44c0d0040440000210b00b00300111113200e0b44c03602240380e403545008800f8048800d05050751070150b04003c0b04202590f9218556041d054079842d0100d441c9600d80b000562215807500050fa00103684400820041d900040c0d52081da00c07207200c01c10240d07e401c04002c0c2d8840e045910f07030320664450000540d42c4071078403240070361113244186454070f0050104001e600301030b0100c601d2001c4002c007000411205240c1c210420140d032030300f201c40340001d040d40c0002c056421326014560700640c0020304108a044150304650344904040240d01103814079140103034090380b003112044078800f4504007900c1e40b03a40d41210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 905175971 1250 905174721 905174731
    0x100e0601090f1404020f030f180c0a090b0105070f05010506040b0d02030c0d170415081f0603020f04030206040305010902180f0f0613050708060108070302091e1923010503 75
    0x20302c2055240503c0c0000540c42d0042c4650015000c3c0000740041001401450081e00c010030589600c1ca080c042183d80380c440c010780c00d0882d500642d1603030055110035101e94240c0b03280c0d170008220080010010b988034442d207000100368011000d40c03501481010350009010703000c11602405010000402c101042da0203510103549600704031401000c5141004401d004903100b0f04000002e8034407000c000a0640007644003c40808c2c0a000f0815000c0d4040080c03070f8880c038510403503032080004554015045000340201d805043d40044c10030103010107807060328002c640c0282110f60380c41c0c41c0d2804601030000c1880c2240501c42816a1000b0702c5861703042144101541074421440d95514910914400c401410051304034110f6402c01c912640b65000b1a88590003039213691503d420030100051100d28014901020944140a250355541d9920b102d80140c0c1903d60640d1030500181c0006602c1d440000720200c81202400320000724542140c0380c60991240860a030086906884010755440c4000c9403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 905177221 1250 905175971 905175989
    0x10501090518101a03010f09050c070f020303040801061d1003030c1e0206030717180c0904080c0d09060e0d08030109020d06080102030c07021e030a030f1205100e060109 74
    0x2042e001803500300c250720781d0210840c040c8504540c0d840700500442c13134080d018181085000401440461a60a0618020070400008205511300f8070305002c01ba004c1c010005201c0f000c01b070001030a65070f0410685024001020081180d00e650b502110620464415940f1044846000054445c82c00240400c200c079055181c400105c3d9440c0d1765461061042c940c200e441000003100c040158440601462054000d80c40e44281d500d04491529a8110021b080c4004117034070034407800035140045580491002c2c10b0341c500340717143c481c1d2a04441074052422003100314030441d00101c5900f0f503c081d10f50f007101c080ba00c880d251003040c0c6040c071170424040c1c0c0010f40360302e904000400614115500915100030203020010700d103515440503c1c02e99209440000d401d52020a42c04117600d404503c042d1549401154040340302708440c046500d80180d44005000e000c440c60080d20300c54020250401000c15043c000c21140c81e00141e90320a040301c500500406c05500c074001151540140714000586071000c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 905178471 1250 905177221 905177239
    0x703050f1315030609141314070f03060204050102011a10260f040317010e13110301110d0e01020c0a080a0504171e1906020903120d1a0612070e0a030b09150105010905 73
    0x24448d240c64100000c0d0f10300c810b1082c0c620024802440c0181000994410300c000341c1e6840c03400c0d0009003540c51452a9510503030500e25100107940d01e1000900340a803803800c00300c48000d036414443c00d0000c0724020120b50444d4520410441410036501144510701ca0b0b100c841d0002e00c0a8203408200400340200503000c62080007048480c1c0d40d40d8000c1d0a0240f10b903c100c401503c12002003425501d120b41c03d000040008904c1650452260260801c1c81004500850501040d10401955540c2841000e03154903030014010700018840c00855000e40900d052a505107403808840396510b091800300c981d01c0707284c085007034102e03084003056255404030b041b070820702e4003120fa465942c02035220051a07175140c82102a4138440141030344c0a000c4144040c0d0000441c0b25800d000c14086050f80780445108440801c2111414000c1c0300006070081c19a1030300b00a010165070214840340801e80019000010400030030290780800503002199015242111801e070342e07940019500d1003501d02400764045840c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 905179721 1250 905178471 905178473
    0xe0f090303160e12100b150a081f21030f0f0e010f230912011506030203041505180106090e0a0b0c160302070312050703050f13150306091413 62
    0x2d40c01c3d01c82503078008200c950500404061189048070201130008015220502d4144500d070484519924503101c090340c41c41c16030450710045c4058401400c54002010007003158448008078241701c40500090001c644e80942d0720004822420000da10482c00035048071401401c0b20f00c1200c90750402c42c941c1c0c89071000384508070015501005107040d09410488003412190024090211f1a5481c4804245447d500d002050078030009900440342c040c601e0b030510000004181203644c4507003c4038410314005881741c40302d2a000507219044a201e019013030410060248905660509054524211008014403983d9202620a03036801140401e019000418031601203282c1a40d15a1b11a45c0d918641c1d2406500d140d12244030104900158010b901400050042104d4106001c80b680c41c18180707681490382c181d038010718a20460404c002c2c001d0380030800a0300d0743c2c1c11000ca00054507a1100b0501d80005401e4014011300380ca00c285102c41d03091038402501c0752000010f0301c6c010240c24800d20601107503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905180971 1250 905179721 905179727
    0x80409020c010e1605240306090912030c041d01050a090e010219090503060c1305060a0e042d0b0d020409021c050304030c0602010507020d0f0c020a0e0f09030316 71
    0x703440104003654a98183c042120003d2005400310786500d51818040750500003070016201907940f03105000342c1c0240b0703c5a1100c072001c0c2078030746c0b0400480c2d00304a60350b5890794460922228801c500d18030480030046c010f0080303c0c44040e1050361002424120004031a0320190f5546800703200d03941d040b410100d400e000d038110580068007859006800946080a080fa1215004004d1f003030200014244a0f0244000d10f400c0c007585801c03802c0b100c6c0e032a0070301041d0b1001c02030321516441140d215a80c0002d40c401654099500045d403004000c1c4100144000d031005461201a0001c100c040448200310b42980d0b5070341032041c08002c0c0009066084240415801e0000a01100d8020399100708007401c00b01235600b49080c0d007811240f052014507103462a40c6051440080507400139011369042c202000710580d8001000b0f28aa1558507005080c0c802180782596014041d10000c0e400034002c100c041510b5031020b41450180070307a1240d00040e9038440e540591240400d4a410105000b10030480100c184 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905182221 1250 905180971 905180977
    0x90e0c0d030f180306050105031c020d050a030e030309010905240103060b0414090a05071d2a04032004061d040305281d210a020a08030316090308040902 67
    0x40b1400d04445000c0140e00d0584040e040f90700464002e600ca100600c040d0405100c0c203585850300f2800c03421240e80200019440301001c500e148108000820030540a600c280c2004c2e101c50088401d49544c2e081c8240002c0c003a100d56034055402d486004400421041946594509074141e000c400401e64210f603185009030100201540c0c1c03123078864071803440c0f2012003042a4000c0d400d000092441d02203610707016051601c964407a0755983c0c60b06240380180411104465403068090100002c0307002003540b041009060701104400d48030010902000300030790404169111815400410028229a410441559114004c000c1d021400048440038149501c0c041c90300310303100b070601505200000d0080c4103240100080d04802c04100210b0080c41500000c214a4035444070303003101d58410f03100001c1030f099111420385c50040c50061024580060091041d028a682c0c001c0198a8003503540280325075a070000e0303900140c401c010380110707044140500000c41c2143c0d40a900c250030146010690790088d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905183471 1250 905182221 905182247
    0x3070f05130f0509060a1406010c030e030a0b191521140316120c02031906180309080610080705090603011e320103062a0801090e0c0d03 60
    0x10751110400300e10318142d8041c4601c6500040700400d82c1e49011894113082e82c2c000b01040900c0c90752801441180d0340d00c40d03080d400c1190103003032500c1c104d06504042484c0c290b4a040141c100c420001c203004241d510030210080d05083c0810500c1811074031003050b10040494880c0e50070f40703804005142d0301074412410b95074040d80210b0380040c043c4050f02032107003503074005070a07095401c148100c101c0802498100b030807072190491602114400246c1d0103e03035500c104000581d00c40718415030303510030441180c025a22090202c4804004c1c84003901d4060700e6040103000743c0b445400341c807001840103400381da8594100e83c02000280701d075510b45010f004035414054500c903015500c92028814820000761890803032046100001646001459031100031a4013041e4145000000c0000d502c6000342a405581940e400c4103000a00c0862079003102c2031118880e42c58060051915420f01400f0780100345907040703490112041c0310015a0012080c1c4400c42e5160300d9900105812015000c40e2007100032403e20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905184721 1250 905183471 905183509
    0x5090402011b0b010608070f30150305011a1206060d0c2606011a0d0506010c02150a03060f270f0e030306030706080910050703150602010b01020c03070f05 68
    0x20300c0d860f44a01562a03002d80110011815100600030364541c0400c100310b9101d49840e0000e01840c5031240d602c8020000e807900917072803040415118004e802ca5029611050b0280e0524240c0760f5280303400b90191540c0c80c000c1c031046c0e00d1220518900e007484100b6025514480028011300c5c0c0e40d4404104040c1450070064650b01d90f03030040440c070b0b20b204131070741144118000800a25818815000c0d403030403a0580000b04044100584000300c003980ca0282d5400400d449804a00303980c40c3c03c0100c889074004031019501c85c209500920390119280014040c001149c1c0d0188281070300d96140d401d100c6150b1040748015400d0f18a107003101d004900c1d14503440c0300104008214034880743c080c1c5040d9002d03441510442c0d0400003c1c03000501e01049039034024000382c01c0c40f003d5483e0070496151151982441031a8842d142d1000130034441c07290b400100e2014100440d5540c403a12804002e00900b6070282d154090302c18040e4169641c5030004500084600d014410050b050606040c080a0350394a950f4000e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905185971 1250 905184721 905184767
    0x515030a08070c0e130606080c0307060c0f051509010e0c060f0d060b030907060801050d020a0b070302240703180c06110f0106150207060c0b0708270304080c030105010509040201 78
    0x4810803810154000d4040c100c0c01c01c03004c0c0c907508001b4121491913105203c6039000361380d6403925403130110724032045440c1420005404040c50400300d0410340340c00c90040050151001411408202114450148109500800c45495a42c00d11030399413418190045c1e01c05020700c81144824080c03c01000c07484440c00c008100550307508c442008070b030410740b1103080716048000203203c40d9901c80031560040000b103900701c02402e0283c01180455240f27004000340101c000800c10207040c001c0080c0300d650759410058211140c1e6001c0ca0368403098051f140703030000070b082c000e188400055541e00c1c020100d80041002041c185000d400b558a01c004400b11a03182c0254041031100302d000b8428617005058000000b011885c403420001d0904e41660091401d100540300c0d0040480c2c4044a200e510107241d00301241c0035250301c10011040d0000b50510410004400d8850b0744244020018204844401c0c0803100b1988581d0109404d030780c42401059001148500054003661091055641c205800000529 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905187221 1250 905185971 905185979
    0x601060806090a1401080102030603010e070e0a1512032102031b0a1218020405010602030a090315020f1b070902120a0902060c03030403090612022110050d060f0515030a08070c 77
    0x1442c0c4009074803130b1b02d1507580030040101d141420301035401c10842501c0030349011820614441d03240c90b0080e000440381c1c2e5031012034084500803136890b42c000d441030505145e0b105c501031030300074200509a0f12080c01600d020801521000d164004d9038082d04040f0907144100880208402054105060440411101400c1802c40500d5441240009a40040c0242000780140148000c0e0359040e4804021035000b000303001140381e400500e442c02d90764407494000c202640c80a130724019001d07002c01400701d00c9000030648020715409001c5280032283d034003915411aa109c114070220300a007007104e00c907403506d100020013805243d8400c1c0c1c14944000c042508060141640901d160400c94044020074424038052204907082140184420140c4105515148545000c4640280c42800c1c107901b000070f000c08a09d0380c00508103140062301001e0310b072041000d21401c008001d4896400c070071f0390b424540400300c3e41d01c0c00b0045021409a001800a0070442003d07640d2040d1940003c1e419a04582e45404c041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905188471 1250 905187221 905187251
    0x1203060e01140114130e1e01030b04140c0604081e0f030702042007050a0c0509040807020d030c060c17060a0f060813060207290609160c050709020a020d020601060806090a 75
    0x409030928006d101c20b540b60500d41d206001300c040031100e00080144004000041e50902c4a680c4150700010310211041303c46a43c5182c0003015000a600c40070108020480140000c2d01d4907041540091a56600c039401e030f40c640e181d400744a48074140b90001c014140240c18617411003c8c0d88030040b019501d01c03451080700348083d5044000e00329050380220810b44240080208c05102030b00c4100d45403116424541e840402d64451010b009024020025414050600903041c0d818420b4015138207200311146251700500d03140d071050130140c04415400106000b401e180c0360b44000d0711400c0b100c0d100b078541002c60a03074401c8030081003d01202d011548080000e401800076100302c501c44c440d508a501e0030180c4010080d45040410729440d080d01c03041140d2580c4110701107802c52201c6890b0009034001d40e508660803e0503010240c580d200358000007860214039401130000134a180c2c20344407220750240c4d04a880f0502846840c002078030032004160249080070b0159005519a500050500d056007164 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905189721 1250 905188471 905188507
    0xc1e13080d0801060201050601090e07110f01060f14030303010902090d0501090317070302070f0305090103020c06100314030406020c06030c07050109030c0611070206040e09191203060e01140114 85
    0x8500d041e084076020307540c03030754100b40928007510190000348102c0c0b6112000074035520082c891020341d000040d02103600c660180d284100c041c95000280ca40c000b892034401c0c2d01a080d00d220f00280c5616a0b01e001174000040036281104c020001e002c2c52071a481c001117400a500001c0300700f42e1104e26840040000b0f2002d00c40c03106024403e80300ea20900c1034050030040140c0d00248000d040c1801008404005460003030b440d09096818145179881d4100c3e040100c00a0141824020070340c4140028041881070110019048a12170542d80060b008a46c070066280d000354490314000d1307406102d1190f16440c1c0b070000b4641c0b10400c0d02400d07017000c3c0d030f0b5150107096400740ca0054010907034102952040c00031901981880303080604c4001e16103101680891030318803403485032140d40000d041c0440c100d903000b445608020300103070100c2c403100031150401c15141c0c8071701c42c02030002c80d10384500080e0038034042a51904032241c0c08120000768104000544002070b0090905200e964104420300b66011210b100d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905190971 1250 905189721 905189729
    0x2160f06061d10050406050105070213022205030c010c081204030e060f0a0305090c0d020d0609080721080103020109120203120c010905100e06070c11030d0305040501140c1e13 77
    0xb2010b5041103070503c4501c0d40d03103400050095090075800d200e6a42c0100486540540c1560030041200c9a9076516009000b4051042c1c0104412880031007122281580f6400fa61821420745941414002c01580d04980301000240140414082c01c01032216414015034014040d06184000c0b1064a00242c0076030300c90b05c0c014442920100c0d02c1804640e02d44182540440000300070304451300041d0000320481c0c1c50900c0284a00414002001040520b030001c4038079580c800c60180c1c031408907281000403550350000c1e01031904540e221140f4418030030023074a03042742e030103031100c07078209040503240300844030450070580e014450b011030007403c01c042c034004200c1071b003120000081d1001c003450141d041c030b016107502c0c000c9a403e090902c551400d0204500ba00b01e17905003060070064440d840d10340081c032076500c007495140c0130f03100040c40d51070b070150000c80c410f40c0b00b140200700450b030311000d0645540303050341d0512100009000b28601c00c101401504d03140391031107001c02c0c2400e00c180e007250281e10302500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905192221 1250 905190971 905191019
    0x3302030405011803120e0a020a0603060e0a111605030909010608061009180b031603030905010e0306042402070b0c130609080c1c20100302160f0606 65
    0x104001d00c8000e10880d0150750440341010b40040854a00070a03001c8081200b2119a82c0c424072070307400e40000c100b2010242d50280c0403d01d0655100000390060449110341c88038001087e000448540840c810b0200706e000a00c11942070100d0607180380300780c1400e41012907481c8800c0245859607a15203103094004c02265840ea0b05034641001800803450f03070303040c004042c01031118080c031403080d10420102c0840100712001520a4801d80042d240200025890064240e012004024960f00825641c25140d0a0322003818202c80030b0f042c07554482d400c0701c000e41b0a1203689000d02d80e591080074501e403220f40201e005801c01401342c07262066601c00b03440c00480e9010010341c50603500700381140e41006008500f00300c002c80380b80424050320399620201c45480740405920816120785513a982d0003070542c014074188104891005d006401c00b41e100251840344200070352a1440901c6402200e0108004511902ca01c5100703031769070000d4450004040380d80d20b441c0c0c400400c1e00841c9070749440102d40458 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905193471 1250 905192221 905192227
    0x609060902180114031b040c051603110105011d04150b190311010206092e0609020a03061a0d0b060f0a05030414150601110c03121c05040c033302 64
    0x442a8104030071050504c0d4020b130400f41400445421400740004214020344010803112412241101c1920860070b068502c1e0515038200028140e00442c107416840415000704503d90700c41e0780303215684803000c24883c0c00c1c0301e0040010703000401c01e07080140900715828000c9603140c80040041c0c100004285818040340c1c10318010014841100c0840480c09070a00107010f85040c0700015039250341c1544405203100030f086002921054031225074508080b55a281004043d840d010120302941c04803000000290034a400031854481c0844103aa0085840b00000d00d00050500114040d20041034102e51181041c0100964002404010050f104a6594050752442e040c42d000110113016184210741d5031149070708a4141d0000c0c604290000001d0a14683c40705054000c03e241c41c0c1088201a054081c90302c100304038404a4004c2d101140b000c0030b01c095504810b500045c1100c5003240c0141402d00d500c0c0703041020400316018506820001c0400d1400d258003601e032007120030700c0441c0700e00c6902c1e400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905194721 1250 905193471 905193479
    0x70810050f1506030712060e07080a0c020615040905010c03061e030206030a0203092409010f05090d05090105041e0504060b090d0201052109060108070e01030f06090609021801 77
    0x1900c50180d00c5141c61514107001c0c01c22102ca003514040024255005250000201d08402c0c0a503041d00072080a003401400f02a884891264603184140e83c0c20002c02c1e071403000318101070701d207016043c01200b06070300800c036550710070691195850240c0c0c3c40a40207035075000f924000c90800c0c021009410071507240412030515106950007003e14804285d141070703483c1001070006903107210441e504851050400341e00e0f51200458981090303c01c041c55003890280d0281c18203090b1038107844e00c0c81200050005c00107c15a0f4510b1419200101c80e80115504400003104400c1d004502034181c4400626055088c15224072034584442c50540d80c00031011f484500400c01ca25041c068032016022040900b803d15140300d000c64450800850000c0c1440404142c1ea204013800c03804550149004005031a601d041104a00f41c030ba200a0054151501500c000400e01c91001814503041f01d03031040030066240f00c40e844200050150a80840d041da840300b0002016a80349000c5001d00342c2c250070818034a500d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905195971 1250 905194721 905194753
    0xd03110919061112031303050c0109030801080c010906174210020a03030906020d0204240207060221040e070e0a151d0f060a26060603010b09030109050708 68
    0x1815041491503030000d07202c4032006403860140d1b41c110b042940b000c1282005403034103a400d8042e801034540d0940c80c3c102c00505042c0d00898403412900c0b07240a0703402c4101081c0046400503590301541000c42c110050f4603003007084408125500a4541e00c0860441455505541113031900b800c5581c0180f402e41c468565a04400c80400c031140801c9800d40800816840c000c4e403241d29020000d814183e40d0070070141803203441c0c0c0403141c04000446045640310740325034a030f01c000c034000207800cac1c000400d044000580791300000300a0140c40c030302d400030800d000c45000742e107210b00c0300400c0c5031422610034880002d800ba9000d6000340100c6141d12004d03d40b0780e2031800d00180c0c81e842d61100401940758405103e074550081c0c4460211003e540c2e0031543c800702180070410340c85112003ca50401c0002603040c601d981e014141c00210b6070ba840d20004010303440e14040354029420f035046507014204000402c802d40e005002800c000380003800100d22010980c0f9038908111240d0b100d41c041d0782040301caa00701484 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905197221 1250 905195971 905195987
    0x902101d0103020a170a09060513031403010305030403080f0405030a080712020706050a0e0114070b180105091009050a050601030b010602151611250302040516020d0311091906 77
    0x2880e086082c00004c0800518103d032034103640300900d688202146500e0381c6501f00d117181c0e45d04910280701030f08014a41c0920001000c00c00c0d030018490241081604840104481c101d1344c01400540c10b10303085454000f1160302c2034407000d0a898080000240a0f00c0a000c050440c6001d414659103070030a600f0611000b451403107030001150071028090004580041c281c548100031417406045034042c480040e1103150100c2c00003800128040f40305010841e0280d44584076942410b0018a00b070300e509280c0f42a42c405950084c00e82d0444945c41c04a140e09500c2940e071a07001d10102c2d0301c01e0340f564960a0400300300381c0040d01c88110070300043c4089070301000b140143c1c11702010317140c0079444d002c1c440c01d0480d8155502c2c2e004010b04103010130070849081041e00354800b034010000259041101c04450f1402003484103d000b0b5040c04002903185100f02607184544400d0f8014000b080f102000031001003515005500b16000b0a200f4040b89403034402c40d40e2501114151001c1d00e160a041001e00044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905198471 1250 905197221 905197277
    0x5070606091a1002150613060f2d140d0803091612050c040207170f190806090a111603020c0301050114030a060e010906020d0b0a0906050a1701090210 66
    0x10810300d80d10141c40c2e80c00074450480060040c2070380c17096102c11002074051041c1880704c491050600c1c1002c03a801c0300c0402c450003240c1c8000c0c03a1070241e44100480c0122218180003104c502540c2e04010081981a0610100f1b003402c02003450696141c1580e414003541c00560b11045540e000c0e600030b0070f1580414550002800ca085120342145003140c0d41e090350380d008925194000e94020442c08100103000c00034002510034012450344030301082d102031740c250700042d151800e2003442d0441c5840d01c0d070081c900c40380200005098203000c0e58864140c0405010510802c0f0b813030070820050002e51003146c0c1290481c01c1c0c4254082c004d81031100f010142074a0707041e0044003d00e038403c40c0d80e140544d40001c005070800e91008000c2408048400054010000a03202038080350001541c00f20041d80c5901c9a10100300841f00c001d00b29840760403810450b00c1d02d009064004c0301122040c030200001c4051898042060300010402001903408904038000c42e00c4010041501c001101c0c000f0548189101924 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905199721 1250 905198471 905198479
    0xf060b0412032609060f0a050f010b0c070b0d0f0b120a120219150e060106090b0702030a0614040201090b1c1805060c031503010b1f05070606091a 64
    0x5070070241c08404100c0c1c152001420712500c64290f80b0000094000d031192a0310030342c50503000d031401c54800c030b8031180c08640141d16030340a003002940009003446168000c10400411500c142e08013441038645501040102030345204510000496840310002082c81d06143c14000c501c0c85124408002603590340d10115100d01c2c00025240c0c8034410009018000e144c020b2a0110740103144141a42400c099041000c15014480940014400102038001c4101c41811080200c0d804500b4019284d84c8203015590004186441c100512007000001e040c405000505072128034070350313030758000c00c940c40030f00039501000d9000200400d560b0840520070080600c000080d14003511324075140d4000c0203880001c060b880e03841240b080c01840f0300e034042d051264070000300c030b00070300b40f040d0006119002201c88002c910401507605240781810b00926007034010140c001044603001da8804c15801c030a1494402c10040c0900a0030041003071070003510b0003058450f00000d510000540c09200109040e400d107405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905200971 1250 905199721 905199727
    0x3060302030d0c0804170a0308070c0b04150b041a0117040b0c13030203031c05060a0b03010e0901240609050904050a0b070522050a08070f060507020a0b030108010f060b 74
    0x150310003042e0b4115801140c54100c40c43d0f900341ca013503071060085070803000d0414141010780b490604d0005030020000d0003a12200c3d0a90394006e02110034018181f4020541c40d04040440c1c000b030b8841500034110b07a0a00070100d2003442440200c0c1c11074030130341c0080c0c80300c040d510750b038104658010b8040000083c1c46d80380c040b29407509860311020400e0140242008503000114031500d642000c40840243d5402002d603551340e01c11440903011010400c4204040b40d1030007002ca2401e1800c0306548080303481d0001440d045a1903c503101d15031200003840c40d85555211400101b13034030392405a00801890390f40e05070010904260008241c0351030b83d01b0003402140248140008600001001c4a040d5484900002d01303a5502c0c06c129124029a0500140e07140140c40c11491907030312303c2c40c48080e16000c0e22158001c99440380b40a54030045e5110f04454850861000c2c8220f40c813400c010980c490000d444281c01300c4e903034450106960f200f60f1010402c0e95440406005811103409000c00805d403884007141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905202221 1250 905200971 905200973
    0x30f110318190f0201090e040f0605060406060c021908071509060503060a050f0f090c0a020118030c170c0a140f07030b01050103020a11060f091005070e09073b01030603 74
    0x1001101c0d42c4009090205010011021684a49052809403496040300e064904041c40c10010751507128a0840e040b90400c00000c0003410140316507000c41721503580d900c50300b400c950240840011220803040c07d81e0801c100c0444c0d01142040207000815081e81d0448291100201c010300c40e550039009401000410414400940c8d85c40300d0b618145c07a03044400c00d0785062180000380e541d924000b0300e6900b0040c44410000c2d1012003001030165500e058000f070040001019580e2807048803c00000c2c00308011084400c08507951000100d185001e081e030075450654903421503442c22140100c1120140c202e8000010069018007003400e500840b08010703c00e0a01f15902d01080400501407c1d0405902003041c8040030b10428001040300c1884083c2e03031641c18070480b48151010110341da4000c5101d4003079078824514161180d0b80c81a80700b075444420000c1c40780208288050040c00c02d2040003000421507013100300d03480d215003012100c41c411220702119041c82904007185ca04c00b2074180761900030100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905203471 1250 905202221 905202253
    0x51b0a0306020c03090306040804081510090e1e240f0c0315150403030201060609080604020136050108092d0319053a050601030f110318 60
    0x20659500400241c1c9800c82042414a107006080d80c80758144602001e01090104180003002640c02c0d14080d41e003000310510400c1e5140d201540c0c880c024883c090420080c032805648092158490a4250b400e0b28070340b01c0c0c1d0b1a43c5000000e103c0600c6030040320b0074020351655002c45a0b95400c00c000c8081c00c038981841050004400200f50847d040c1002000030010190060035881141d0000c02445807401700d0034003440f0310340003800201d02640ca0481d0200d101400392690b4421214102d0041802d42e61369401190f44481c02103031242c042860344040c2c1441841e08500e00c60500d00e61042c00c0302c00f80740400040c00440068031030f2540390004c01c0b80505c0310b000080c560345898065800d07520491016603405195101c0c07542e07240e60071010680c480d00800da002c001090142001011aa240000e003540701c110719100c012002c008014800c0114603952680e00481da210005041c0000c1c3c0a50b00000c0400b83d940000790707039204450002c100520f00c11080e2650b54004501c000402c2e659603010604 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905204721 1250 905203471 905203489
    0x90708010501080708070e060c0a1109010503030d020a0207050901080105100504050903070b06030a0b07020d090602120304020103150308030a0c1101060f06122403021c230c1c051b 79
    0x144104441c0900050640340940426101407c0181070184d4818000c1010780e1a400c80b440c080fa00d21072003150700c00b6680b401002d00d0341070310030003030213180b03440b0780c4000500c000d601c000c40b4442940204d0400264594507a01740e140284a100c0021840e8602204806588030b02d98205611541c42c0c1414000040e0000058603000d40d40940004003a44039a0300191405104002c01814980c82e03030100502c0b02c0e40418a141da60f941522800b0b44140c807194241c2c0c071144441c0c103043d112401440014003640c469002850012500d40503604925200e80b10340400341d00458a810525480e16044218164008030304480070500030020040c903420403420103405056072140c03c04100c2c031100c004500d11070300d42c085001c0e102034090103124105842c1c00380500541501c400d034030030140320035420310800000d040040a00d501c0416051b0062038ac54060f00e1000c91400061490311035078020301e08581b180100014004415021400c6101403451f05901d800808200901000741d05a0500c0241d2580c0e015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905205971 1250 905204721 905204731
    0x1006020c0301111c0615180e040503070803070315030b01080d0804110103020306060c010603111f080606130305061e0903130905061305100611030a050301090908040e04030e09070801050108 83
    0x64000380032194003180040d0007175410000703007901103010341c660780ca401103c0100303074001a016401c0d2440d039643c10600d12000459000d021a0070402c003803030029061078019988030a0b00d00b000207240400410414000803150800c40d8050076900052041e003404228800182c1c0852070541418605551103030019600311600605060300400424503903600c50050354001800700000300503a96036428003246108011207034500900e14412950309400c25200b122402d0111a11030300d50711b03115103051103407a038014084a00e18601840c0c000c0001a003e0040e00d010700104c2192008048080d01203e2086001810440c1103510400c14902d07a40d1219180108603000140002096502c02d000714004007082d02042c060203180c00c007002100c070306803e02075042c0c0c0c120b40d0311848447d0503141c1d92503591042c0c14441011400501c01040310002c2a005078446501c02c40c0780e1810250784909185607598155403c4009c15010181140d00d4100540110f911450ba4544a03420b540741200182440d100030384 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905207221 1250 905205971 905205997
    0x5010b0711240d02071a070c12021905100513020d03080c1b06070201050a272303210403090302010302130e0a02180d021518091006020c030111 63
    0x9080d644080e03410a8a48000301c0801615640d0f00074030800c00c000c0d07004240803107003600100000742e5621040a41540700324025100e00302040c1031501c80b100e00d03181d07003030449085204951924841004900012101e140310313000611612110980e40410381d4001440206040358600020700537035201209041c215400d410b200102c0d481e05021721a89100c0c43c07403030741301c3d000c0404032804400d41c0014200340305003520f600030420307900e44428800039109060008941c03030308a031800801440404a41c1c1d214584200150341c10000c01440743c0e0302c4956114a15802c2e81c1001c1603d0210320705030f0704d034449003038080c40c01c002c524607207594041d00d52415400082d0406601290013028896004030b00320103445102c080840b9480d18840200181d0300c00e080c0251410310081144100e81030400f00700c120654018180d0341b101d604003a809019803c883d94105003641103080d140c1035a2207500100380104281c03042c1c1d040e0a4140b4801138580400740d601140a030789000752044402800c00292082205030348 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905208471 1250 905207221 905207239
    0x501181e02101d06040f05040c110606040b0f0306150111070341161a040509060109030b1009060b130b090d02030712140706050f07060608030c1005010b0711 69
    0x5404448941c3c00032841c40d4204d20300003000f04000c00d10b6050f00c011580122020b21282880f220308650220b075014100082c1e91041002c5020b9141603000070312105806401c00d0440c41060340002e107000c406a40404040c6a60040240fa1b540e010512100041d14600104200da2441c1c4d034400710101b00b080984181c20001811030742e0342a0300728045111140c1c002d080348501004a4a8036100c0810121424240342c408100003540103d58030190b6490b000c3c5040e41c0c0c01c1c9890481400b04102e0020035440c10002301c204040005000240064010459069468481401c1014250071105150800804100c0c103002d000a410b060301c0c1e401b8261112111146d4441d0748200c00f1030500d8603000b200945c1400b4800002c240038007444860082903000794107101e6003207081e001264480442d030203500c0c005281040f0700900b1343c0300c5400410b80345220350800151140c0e02c2a1090442d0840070003610150051103000c030481c4074900038507000d0007444e50454508851036483c1c082d41a80600d035140518030007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905209721 1250 905208471 905208497
    0x120610020606240706050925091104030b0f0402100924031b08100509070c030e06190513080c1810050402040b0a17040c1206090501181e0210 62
    0x100501222104609914607144d0801d4a09240504000c4a002d88103206a28003c84042c4402443c0c80e0704503200b0401c0391072141000b20407005820107c1c130011400404010000001e540d01c4900c600c40c0300c0c00e006062a40c20700d407041200204072821400d04010540b03170b0030310000d00d50f4001041c44a81d481050003064900010640207040003c2c42942c084900d030b4101c1c0c0c0d0766138000e000c461043e49084144e8000948030020401741900c207503594000174441c2c07401080080d024204c0285000d8009000b48d05014100803645402c80d0109030707000c0010000310b046025100d2061050010700b0039100604400648c85010555254446803140040400c1101140041120300c009001412005e441550340d19114140d2602d50707030000742810002042ca80503208058400c507030940c060303684502c000c0c51711444e000c00000e0100c8078070000d591140c0d0301e00500c800550240303e80c0c02e07004440038101d03680503000d0804000788400c001440e4440d162440c1c080c8010f86d18204860361500301c2d81814951240b01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905210971 1250 905209721 905209759
    0x209030a050607030c020c18160c0c15120614040c030605040c11061614070501180b06150906030423030703050d0b030a030f030209011b08120610020606 67
    0x5440000792540c05110240300e501d40c0e06401880e03c2d00320540031100341e038403010309000ca07058940c0b200303407080d12031000070644116265020342c6415507580780020303125400d038a03064a1080f10350701c100c422100b200c090380c0782d03280c00c600c18a03a19072000500704845442d203103220f0112403844004c90b1045a94030384a000e105e000f03a000c0e801605000d0002c2151030520540a04803038101504100140700c1c0c02c0000300c0d6040480001041940d0991b80ca81d6006410310304207405402030142103945540707990720212044200103917008a5801030802c0d02d150300f020b01c14844d09003640e04940794030750810071a04240b81c4414040707a42007640140c503400d00301c0d0044502e105011055084990b607000004a030400d160b4050040c08039101d50210402a18000d80101607031612002d2000340410301ea0807150183c01d000380d010700b058500c181000c820816422003009001ca403440b4007100d4045001c100e038200c10007406da08503440354050700c481046c18000c0c2d00c040d40e211801403e191044188000303c21203811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905212221 1250 905210971 905210983
    0x14041212020d0e150702430302150c0a0803040501060b0301030f0b06010309050c01030c0917010e010506041404060b0303070212012310211205130e010f09020903 71
    0x140000c045480e0240401204050800105410420310030140040d0400002c1d26445000d0201758005122800480900e07084a0401040000001c91058292400d0400d880480701d910107610180380460707415032041110240150744040980340082c00040f400f00000108540505d41029a01c0d40300d41c2c581c0742075405800705400c24103956502000000401040210680610b840703456090400e9031004011070854065100190840c1c0c00b5905840080d4006d90141412100714580b000100f030f25a5006915440780b40e42ca484180e649141a110007102840f9031500220112014450b0301040210b1800981c0045c001814290390b5550508135560200101e0361142e82c0030341080a17030903140f00003038020030110300640c8041d103100011b60b007410f21030b140483c0700d4114005407144060400900300b140c0a000c3c0125606d05038019005c0c0085000184c15130090362103991060342d101201c1c0c9500300345003019032003010021741b80801401414608425070701500c541400c01070300c520302040028a404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905213471 1250 905212221 905212247
    0x206041703030106081b090103053c102409120b0f06030105060102100f0e16030507171b03030d090b0a060602060f0112390801140412 59
    0x1041038000100c5409000c00950304035049504c0300c03000f80e0340c0c0c0100c42c00c3c1414520f0864020441c100310349111580030f1760101c1c2e04451041e0f413001c410701c203140030074403a451006201180c0d600c120018442002081d403150354000c0700315460303800351403038281501c01c048100c46407000c01107900b5503081745107407003108081d009114442d80c10790700007514140030440c0c14044d03a60b00d500c50600c4002420b00c0c02c050003021301034075040e401040c00041780c0d20160001d0030004002c0c50b04c20780300c00c07502c0c1e100350b02000170010141c41c081420030100d00e140781c010300e4903081e50302c41e8241850b440c1c04021140b80101d94002e180c0c041d0225807103124205400241180711b12111080f10078501103980c0140106203030018441ca141c0c40042011503218982613913240c20460782c12200400d00c0d40144895240100520b144603c50308540c691000607140c04103003100e50b840c600c003968035001503502d1984060301c105401400c1070300003000203410f0464140d0011300000d0000e44a021241c00350038040340300340c070720341404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905214721 1250 905213471 905213489
    0x60c051203071e021f02090d0f0506090601082e110715050916150915030c031103040b07030e0c04060815011a0418090c12021807050412020604 63
    0x7494070030b402403c01400400d204005a0310f8100c2000e00c01c2c00010303028004100c007426510f240351120110070182d0b002c071010940248120140c800010400b65110b03c400c0c2c070582c0580352030710b00b8640c001d1610b08142c1c0880c0d6aa480382550340c0d0288821418844180009400314a100f410384031008080d00b403140d180c404482c40000c2060521460100b000480900440203020548401804640d512003003001c41c0c040716440c0e0710410940c441280050842541810700a040c0e694407030201c106482d441018501103038494070203420042d410320071a018140400310041c02c60605880341090008010701000070b040d80e80700c0302c0c8410b4600304101c0740d0b1728000074400c1c006030341c5411881e030300c13900c5510184400000410010500b085081d0a81145610b02c2c0e179060306042c5080c11002510104c04050b03021030f03a0f21076228011828809070f44002c0d025100c201080512148107010005980340c1c0d5801c4040003040510805641c001c2c11601212583c01e10714000b40010f0001030214800d650105001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905215827 1106 905214721 905214727
    0xf120f05042304050421030c171510170c0903151b0d050411220c05040801020c1e070e0402010305220c081603020a060c0512 55
    0x20081c10b00700c19041807180341011404403003043d6025598003403010000304865008807828180642c1a01d402c000c3c95008000040001c0c03c802000700041c403165011030308440608840c89000c00c00104501e030140325041c0041c0400300e2074281d4800044c0c2c010005140c68024006940801d8009006450a0103945c09502031041c4000c03c00b94105d0740c0501c000700c00c1503421012380741a00500000040d10b08041c104003043d00c24201401c0d2060f000906002011400740240d203012566504011454450088080d111401241c100c0d080d07940c40880c4002000b00c0000b90f45441c2e0902c2e01e2282c0055080130541500c400c0a07016042d80090842c010a005501c2940304a51101070750001100a211807503103c080c172600440162404115220309011a01d810320250f80001d0039000309011052840c0d000c510060424840d4500344801c100d09041405414450040e09904046005035 = true := by decide +kernel

theorem cover : BRFrame.Cov 905035971 905215827 := by
  have h0 := BRFrame.cov_init 905035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905035971 ≤ n) (h2 : n < 905215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
