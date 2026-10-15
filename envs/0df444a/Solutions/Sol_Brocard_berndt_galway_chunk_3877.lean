-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3877
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:14.494979+00:00
-- url     : https://prove2.me/submissions/8ae745bc-1660-4bbe-b899-5738962b9acb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 697122302 ≤ n < 697302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 697123552 1250 697122302 697122311
    0x1f0302090a02091e060406030c0e10020304061106041110030e0d050c071e09090203070b0d0b090a0b220b0a030f03020105070c11040f09021306060e010c02150d0b030a050a0501 77
    0x190380820380d04130900303c150443d204200a001d0b881c440d4000d121520703094140b07004803069400200f81c1c1c1c0c172a4106881e00680011a09000c0c00d5800360b01c041d908140c0e1401401e10f424a40c8a41c40b00300a01102c00b41724030304010203604154065002220481c40c5181a1060300f140190084c1c00ea520500c80481e0324022a240440c3d035151840787d0002030b4842c003284580007070038501410001c0c00201016a418031030280d000035405200b070001c03c040f404149000c80c114201e0130030b100c5024805401244201e040003030181440c3c45421508040d1001c82550240940c00040d85000400b1a400c0054000705200e001105104039402a00c0d0502c2c8260700030441907552440444611488a000900c030525102c03510189103040e401c80d1300b42041582c1c000070b0741602a4009403582c0d148100660b401d0391110707010071015810040128243d42c083c28000c060240e0380d4001256444800901100d80101007031108004045030b0106c08080e07009021201c0f240309506042d40d03500d003c40b0341100c1542c2032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 697124802 1250 697123552 697123579
    0x16080a030c020f151306140432061303030b030a03110601240c052e0b0f0102100504170403051e0304140402030910050c090f04020708031f0302090a0209 67
    0x5800101010044a105002d498807900b580e820201c1000540c6c450761910314007451114079121090240d4411428030500480d403402c403202094903042c1100f41e1000f0302e400038006100c0410495400540c4c000c240003100600d26041d0001c1900643c9540c05100703810011381011380001e10750014040c02021585c681c1c1c0d03608a071002110300b2001651002d186030821002d654020b144501e03003148102e0546525070144000d031100754115202840c1d100c1c40325901907007031280da0300c07e045c1d00c52001d480481c0749400c4900080e594520901c40b0f80d1140341d40313000040500c031400d4242d4181c01110a11196119501d0505a50354018551030100c80c05900c081c003183c1640000c1240c00716010100c1c0480b8203482e0004120080d00000c0000c05a40241d481500c0700d684240b141510035079a1a440d07070380b00c6480c1820320600314050204035001d2441002091b02040e80c81050b640d001d507218100d68070341004050000d03140911948000d400030024000e208010f000b5402400c0340d09001d84010241031003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 697126052 1250 697124802 697124833
    0x30e1c080c04051f02030c19020f120d0c050309040609090c0e070c03030c2330060d020307090905010623150904060506043c0b16080a030c02 62
    0x50b40c031500f5803110124400c2c0000c0050025000c0080c0107500582c0d080c1070801c1441410f03c015990042a8501c0102c0c03118114a403200d4811031b4290180d410642c0442035220083e61449590745070f8040c000042042e90411004004880c01102d010744240092070303a9400c1d60001c0c207124201120000481080030560344000900c45102d40000c1c1e481400a2000361130580c010f000c280c0d04113040241c01c40c600c3c1c01d800c3d400f03010a103407074110403829543d45110003034038002450220145008a6040303804031100008008485411840c01c0b500012050340500c00240340155a520241c02e060411049805000065202d00c0854420401d02d680d07429492603a014200701c21121030740c0c1b041d9000440d40c98442e0450280191712000b0388009005a00d813000161240c015500c0552000c41c0c284448001c0840007909031010f0f110810085061800060020300d282c07540e0041401510f000310b50341d80c2148046e000c240000747c000501c2651021402d000802400b06007480401500c9010718100c4643c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 697127302 1250 697126052 697126057
    0x31e0c18110c1501051e040504031b12140405011d0301060806010e0a0f0e0d0309020a051305090708010b131104050a140a0e0610110a12020709050a110d05040201030e1c080c 76
    0x5900ca9031204c10146c94004c0200402001d4019002c10800100f0500c00200c5100402d4185004281400006005510061204809a030b44c80460041440100080e0b600041080e4144a241d880a0328507038003140841e00415560b0b115000340e01c1240000106824800e007031038080c00500f4000d20031002c0d40110441914001400500241d00c40d1a0302031103948281e1095070800d2000780800179586c2c1d1500014041810f036400072030483c1c0e4070424000491400c00188004140b004002d105e4036a00100213440c601c40f4407286c650b080d846500b404817403d0004112800b92100074016000c480e05c608401182c0c210315008940a8200c0090200e040c9802c042003a01c40c10004041e41c50281d140d090485620f03610802130103c82c485c0000c00340c0040e50300008002240c50039401410603516244608080c2c0310090220004145405254040300318014112041c038041d060000c10355403904d100480c000c020003074101c5c81c3d90090b03043c1c500325494180028401c07a050350341c078400350382c4401120300d104c0d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 697128552 1250 697127302 697127329
    0x2040b03012c06040b030f010c17060d120c050708010c0c0b07090b0405120a060908032202210a120e0109050103020405090109051905010807031e0c18110c150105 71
    0x44020b500251051400741c2045103602805815201c3e00305525a0345420750b80b0804580c004a044400c0d155031305103036034403007541c8000202c1c2c0c00c035142e806070348440d1601080055040108811021410300307002c0d00704400710050a0b1100200308100c0b8a01d03004010b401d00700801c07a015030702400428001c5100e0300e20316061724042d1824507e460315003010060003080b0503082e00c80d07501484100c02d0101d242445100d5103103018804450b920f1a10205042c03615400300f0116060460412404d40581c460490304480f0032240c24446106107010042030b8070b45074004100809003d50303e654040f525601c92414038110b4400c2c0c13580211240c58000640590186002c5c540d008680b40d4010881c0828603000190041803046190f1240282900c491003968001d1700840361582c03000e18108200701c25500c900c001009040c0440300040960f582d0b030b223450880761084480003586032001484450050b07109494021901c0c200640d200ea0b403500076501c0f60201d02c15241d080c1c0382d050002039a03050005c50103101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 697129802 1250 697128552 697128629
    0x150103060b03090606190e0c0304111c0609020120010e010e0f1c0c0b2818020f060c010c110d020109032a0b0910110c070303080c0d02040b0301 63
    0x19650781170184400f04044003842a00407281100009401d107141d07840f10300410820402ca542c07450142031130511010781c007031618003e03100c4102442071040d122180003100c5520031004100e1150780e00040b25055070801406103081d00e4200907140c41034056002c2c070702c6005803500a01c20440c02400381c640300c035070070f0600010641112075041403845480112400e0341000d802d18140700f03011526010800c6000300d40c110003041511400102c2071040756010190348038900b205000300200b070300240916001c401b0009000f0000e40000084960391581912038200c10345008100d080610203004140c410351601c005801d0041c41035002e03c0a206000314608190276807a03a080d4116a501c00d44840c00004800000080d10b034103401c40041c9130184101c0c00f0700004402030041f99804010720342202e0100e03507407080c5040c007080032007400d103c00700d00003003280e400d8241800d0755510034414511034403441802e0140c0d1440001e0102e5030700748443c080c5040e80c18116001d03a4004aa051640c10040442c03a0f0142 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 697131052 1250 697129802 697129813
    0x50307022505090a0e25080309060f0a02070801050a020703090515040612200403111e041d030310060207060305010b12040614090d030e0304150f090806150103060b0309 74
    0xd508000510580000500c1800a51540c4070707030390142404a00320310703a01079910a80400892040701c140344805807d000300550720700300c00c10000440c14494900c003203005040100d0101881c900030702070381004004201c0248502d28245203114000d50010300100d02096000102003550305201044414450b4410501361405003440300c260340303800760000c48018058940b0344130142c4034118501d040d034840111203061b032504d06610300981c1d074071071810081d40180b0504200d00c071420b40402c411901032000f520001115112115480e00e034034250500c10409101c000107000d403804162445804840b169800c0d1002180c45c0d8030201d041da00d080c4602c4008031003e00c003846500f07149244103600244030b028000f0380001c42480852043c8011240001d036074101c4c030000d101a0b41c0600440d81d00304581b602035441c2030300b010000d0203491100f00c00075041003c44001c10104500a00306130001d802c0c6c20b8100e6442c3e1400c0c01c6180d0f44803440300d528600207420107500044d0352102100362030080c070480c4043d20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 697132302 1250 697131052 697131059
    0x110d09030515091e060a0515010e04020313080705070e090a0b0403030b060d05070e0f0a03081e09030601151404140f15040902090a14030601090f0b060a0503070225 72
    0x2d402002c05000d450340ca024555411207001c812200d0b81c01da16100314040c0c029441d001021004a5800924109141d25841c46c01000b030ba81c404004030300054111001a241e8883c0000504a07405010006040c030700700107a43c1c001d05c50001442011620f010104203c0c41e600c40a00d992140d404500081160700412b01040020313000b50008070741200c020300494180100c8109903020303a58240c03841800300f4041c0c45680140e08002f1401c03100c544094900c410154a143d0701c041c4684500403849005550030b43c0010900e07808401194103d420080469040356140e180100c0196031819040e000b160301c0c150310080042c403c1050380d007282c4031a400c01c08204894001d20091104100c2d1003507002c2c0210880504070b4801c40d000e0030141100300da0040c0c07114241424440245d0064110f2655810003101041c00303544c0000740d41d415030300b9803a00441d030001c01d90440005031501072002035101c0c0020843c5081954046d0145110300c0481d405ca80c6481e02c000c02e2154201c03181c015070006540c81c1c80050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 697133552 1250 697132302 697132333
    0x6270203100c0c0f05011103040f05010b090c0406050c0c03070e01090606030902100e15161712061e0a060822020a0915030f1b0e07020c01030e0c10110d090305 70
    0x13900030714007805c0041b910b6041c91110b002282c0c021a811100401400310100c2405001d204040d00d000060301d500495081c414201c1c111401688140402c109001401d103007004da042c8003650b00e283e40982200d41e2252205000601c0090902903e402c0c40e29008000828034402d000c0d40ca591a00502180140c41d9010022108401154852074220f450b502e6030704801d1007a43c004050146c08040417480c040030610382811220311364614210481c90502c4605403c001c030010305900900b0440f401840d003035405401c00172160a0000d4198841002d860006081d60013442c990311400e181c482003050704480c084111403a8070134010103500b01e41290b0081c0000080d980c080152500080c80b0103120655079501d01000c0c44a00d10103c1c0c2c0410740c00d0300c48044602c2e00c070944c0050540c8040b409041d140c4040b000b5950b564076602c1504044c1c440b03442c01ea84550034440c0d0b01c1c64540c00b030000501c4010401020344401101b9030300b0a454802da04040119034410213039601035070362001c00307807404003100c0e40075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 697134802 1250 697133552 697133573
    0x1060b0d180c091d06160810080304060206070e030a050d0e1203070503040e060319021026070905030a0b0f27010905150610030906270203100c0c 64
    0x240441c0070081040440441e11241c05500100541d0b0008120100c1c841e0041041d403044002548440e400b10707040c01826030b0f842c11b0240d48201d09203080a42a616091903140700726840d880004c1d24000068081000f51780860726505c100c040340c0711486144008000c2c035075158040b1030081c107a0303007000e10005d2000c0d106803011850070f20010b01c900b070051020f40805007140e0001d08111440e500001d800c02c28064000c1d801035020408a02800e034107041d009516040c1c5110560007481011407002d05002c590090380e908050354218282135180f1000d005c50403258100940d80318020400c03910001500f0300d400112341c0c1c12140d0000a40d0b03881d8407006080102006d0141c81855016003031030b4014002e190545642082c41c2a05001251280b0282030003400d00f00c00301509a680c29003a0200b15050325103143e00225505140740025a8601d103003020001040a05a10503440c043c0508066011005501c0011480d00031420f40301c0701c03049105940101c44104001c400491540119140810780045d00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 697136052 1250 697134802 697134821
    0x61208071727040c11060103080702060f03130510020a0906031e05040b0106110601050f1e0411091f020d050d021201090509010c0908062a03010b071401060b0d 70
    0x9558103000120345904062800210310b840344011052002042d4070341405804822100e60802c5400c580f46041504d0711841c2c1400054a1100300003480c0007151111002c445a00c043c030000c41c0d48a04060340c440e44198891401031325a4800c0383da80d00e24100e0a84211a040b0b00313a510f03060710440c0350500a034081c0c074a90740c4160382400240f49515581020f80917040c0715503ca40c0d030420b82981400b9018103803000d2000d0240c0300d58031410050201e626122a407040a0794101c45030310035000300c500883c044e20141b0035125002810030414840c503902c184040c00604408903030321500e4044040419104816013045c0c040180e001c4000807280d14041d01c020000c2c1380007540e025207000c410055100540708207a02c40503a03c2d0b5503404118150800384520314282d011031a100413824a00340019a4600018009a0b0b601060840e050500d081d082e4a0b10352a13000101025120740e5145c04070081a048208249e610750f5000400300c1032a6010b22450742903031a0030420f80d003000107110320880204032048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 697137302 1250 697136052 697136093
    0x15060e0604080307061d07060906030209190807050315100501050c0a05062a070c0e0a06050a03050319020d090e1e091b0f010509060a3006120807 64
    0x1c0801c0500050000b415624010540481c00040e2201c440e207001914850709880782c1c01c810014009245e001c40320700c0494045240140e101c43d0b07030310700203000318010006c8100a25104500010000e40100341881110343c100d0903503058410448d010000e0300c4040710344916020000c5020711442d80980701034882c080e0074008481c1c90301056510a4509242919080079058002d4000020006285140251f03075409074265030401d055561684039010179030241d140b62003030b07000008400f0703175281c0d00540c0140002440c136038225a0b6414110380b01d9200503403024002d906030448110507400050311107400c9500d41d580b80c440c1440c0404a03506000c0140400c0c40c00075040302d484081c0703440c1c9042103016901c004040c1028200c00545011040b0852a183c2c3c054038408404034050b0b038025041d900e02d030308180c585650700c036105801107901000c030700d02c841d01400401c806c103102d15400003018015240d1012080000940b41d07003490284000208004200107070400030040083c5a80400c00e04250404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 697138552 1250 697137302 697137307
    0xb04030f080c0c0a030b040c051806130b0d0804090b030d050a080c0d0603080306041b0507031202090604030807060e0102091f0c081b1c0e0904050c0603161215060e06 73
    0x860000358064013540c41503440d40b022905100500c0074118101c0c00405c801c84101050340c0710504071081d5508000c203034511815100b0f440700c0407448250044c0840d808020980840112280b400241b1600540506d070320051800c003409100d8140000c5488000c1d1044e159903044c03036141b4404072501c1c43c00034090b0290001c284509588000c4601802d000f451054000d507450780b800009100031104030440219031503452600c0868059045000c0b2030000b601441c10070003800d621050100648903d03400c094114100260001c00d0010440c080c0c000305115001c00d01491030ba80e40c05509031300555014543c00150301111411224522401e25501c5180d070801c02084962916010295046005508290400840c0c200300758001070240c001c03803100d00201001c100d01c02d00c100409500d1400c85450082c80c3c03c20114060040c2003100354940d940c0141403641d60b1424210b4880d0b40582d0ba020750010400741da841511300c51a5004590b607400c040c0d1408214070b460b10100312840b24050b04420f0304070404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 697139802 1250 697138552 697138573
    0xc0302030a060c0806010201290a1d061807051c1e0f2405041d0f010209011b020916090302030102030901090b01050111030a030b0a15020c0306010b04030f080c 70
    0x14072400c1c100a01a030b10003c0d41d841412006003140384014042c1d411039141500d10003071141038802c0040101e2408160140080e0600085500b14140c0d400412954007851a0040502d114103407680c403e4000b134802c0c0454106072800c2642e420003e88005010a609120441040084800b48840740311070000c045082540f0441000e1181d042c81a640311491b218031034100101914010030589140c020080c0b540340c1c4107020316101c3e2013406c0c0503091096807070707451428403498801c0588004400e48002e90300303042850300e401c034001e43c04a00b0075400305003800d42c03140ea5001150f2039a1585074000d4100b002a0f0b9401c0d00000003c01e040c0d03030b16828008041404009610244003561292010710300000740d245407420805c1120304140e2103113040000401e59403072150008020780b0809007180c200401d0f0700200400080c0700311001d8000c4180d11034035109100f07980382c0c00649144400d80540a80d0440c1e41c03650601300d4284035900000c0c00c014a480d90100c00510020028980c0300c000c20f041e0f07801c4846 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 697141052 1250 697139802 697139809
    0x90605090f04181115070b010e07020a02150406080f01060804120203040f330c030e030703021c0b101d040c091107050606010c0221250e0108010213120c0302 69
    0x3d648403d5840380d2429000003038600300b0f018003001000c0041d10315402c0c8000f07a0380d01121080b05020345047c1c160070300701040302c16000700301501b400d0b58014420100982e004040904030742041c85100001000d07100414440801c4214543c103075103081d0365182e8240d84680b99041d408030708040813400c5102c100030008103151003102d1640509540001030507484d40fa0407541c603420172445281c40c0e4500c801f040c00449150042881c1c611903078035060020740201c048002a0400300d8551002e9009030050052601c1500380d1101c00b155144601d1071541c46890304085041c0082c0c082c000d44100010a010f5000300e03865180b1620342c040c1c494218012003e0700d4070002c4041d40c03510314101c83c1c0300354081840000c100060007150782c056028a014200c201c115000a18883c80314560482c485440c08034144a06400f80808010304040840c108081480042e220050715150720400032068000740010402d52018000ca034003400c0280a110885420b1401d0f0581d9454840c03002c441040c0d00c81400001602c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 697142302 1250 697141052 697141091
    0x7080609181c02280b09010f1802100801030203190809030d0306181103012121030c090b030c2b02030a0c0c0f031d2e090605090f04 58
    0x141402400310842d10000042e01e00920b0100c0d06041880d11003085036200f290504d900a001d4000714040c406403594444a401041c1d295008001107040c0703440c040440e6002200686010b20985541d100f108550303404032031015086c00001d6150b0003078101e0b03011400600c210340400d10b0003130101c1d51030460040e0000b0310740b0004038000340200751525003c2294044003008070040703041c00142070004d4411189030090038401401030500f2619040c0309105505003403400d0f01c2c2800c0e4000c9250586010140d02410502d4581c0d000200090500c0001e0403124419500d0404903855207284a0641e1120103a58119401c00d51010141d9690849400035184101c0c012450003590201c00580d00d04219009205403280c00a4403010701040451001c00140c0c1c0c25141c07905160149010002d000d0101c204041c401070701221103a00500e0007080091040d290002c0c8807000040c014034070340351360300d84205039400d40440c401c07400422000e03c1180760740c3c00d2007109500e840100810001c3c2e401000c030170101100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 697143552 1250 697142302 697142323
    0xc0801051903030806190f1a030c0a051b150f010911160f0c030803041203020403050d080910020c03040918121407140f0c011b0201031d06010e090606090708060918 72
    0x602d14085c040123a26855840c1c0c54210310301541d41031840c41c3c40310003494140700b54045181040000121081010309500c5654001543d1201f60f544400340200810032402c03042d44d10210090011000040b000414490541d038203400c940c1c480e052000d03100001050034015401640c06d14046818540002c0d51245030701c000c4c1d4032403040c858a030305040c1070500a8411400c0400e0a141c410002440030920000c0c2034080302d507051400c1061a17481d450b03280d06208070b0711488030304c250000c03540daa00709401001030815107480c0d480400804109a040044103003407403001600140c0801c001080291040b4070300241c00e4a891241890301c0003e0381e40c070f910103180d0303d0204030396040000741c500061000d1100c41300c001024604054100107110b1030740008801404002c0c10b26644034007036038020600400002d0000340c0712041d58201d680d40c15640c45820f00880b25030050f4050b000001c3c8040c681405050300400c2e81d560740349607540c1e5610a2000c04480607007108240c075076003103610306007071010030802000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 697144802 1250 697143552 697143569
    0x10803030406060e0103020906040e1e0706032004030807050c090a0e1e030a0e0a0b0c06010503190b0a0902011206090b030d020f1b0112050a0c080105190303080619 72
    0x10381c6458101201103402c150044d2540700c4290b001000503903203c0c00c0641e04000210390000d1076030200c1e82c8051801d4120060202c0c0c00c000300d1500c401e400008103450003150f40343d8409000700d40d502c80000c0c40800124801000c816018002031000c07507901030191911511075002c91740700034514000120100c0c0304851a03102d164903120020403880f8284000510226410704c1400242b0343e0b405055140d005d00012070042080c03507502a00c00e540c0e04076143c80181404608503a8500d6031940241d114402406201c0c028410f880281c00b00302c180c482140a1503400880000064561040340d5007c4c02c1d0282c01a4100f00c488241c644802103144500001411400780018100405409160500054802d22419900002000000c2150110b6181150741c500088501d0305401900140e8010760914421941680f0705010400507210561001e4480ca4690711400456070342c900400c20382205503200d0b101d520100400800000c2d0080c415150000c8004005681100380400d54000c2d855099120100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 697146052 1250 697144802 697144807
    0x240914010323060f0124020a060c0207030f0b0906071b030e0a09021215010e1c0318090501062327040908180102030301230a09020c010c0f0816110114010803 69
    0x90741c80800c809000210596600300c2d03c6d400c0825019488a142c2c5101400c0e040c0c8646524007042e10034060381c4055036100c80c1d054014020307801e25990480003283c00e002103220794404209034601509110b81007180e440700b140e00c107660a076421102c00400d61032458000800c10780100d08550035002404454000e85141030451403e583c20900b40c0100030900303414028202c000c000141c0b603903000080f442c0130400c0c2080c2400f82a26003100c6101c0741e030460a003450515200800c120446800a5040304c2050b9034000c0e85207013807818000c88010030110b07a00c090808002409413005c44481c142100d1402504101c50040c0c10340200301900c070b001e6002c9411b01c1e80010105050320210543c081800c8082c4015401d540c140381c6240d81e00d000c403210014454400b00a414603982c0c4014892020748480305041d9103592014a8250190981e8160b4201250180340e0341c20b180352042604921a005108001455203815001964802a07808400d400f554176441100c0d4082c00801d05a130003081128000c66 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 697147302 1250 697146052 697146059
    0x509060c0d08060f011713061401030c1a040312022e05010f08070e09030d0c0e030606011706040e0309040507091a19050f0d240914010323060f01 64
    0x41070703680b00816440c421502e0600d060364590380000078445920759403118a60325120200d00419500424600821190401c5051603c0c101000c3e80d16040b24072881524a03240c1c3c40c0d04101d00c11900e0440c1c0041c00180500040000c03480715403015104c01085e00503290402018141c0850140c0b44816080d00f000058150b1484400c05c1d01c522801030201c01d0141b5907140c00c2601031502c4000510680307022421200100f01511400d204544c05030088400420480e130004038080c02c400c642d0003a95100e4001d41c400501194040c0c02c401300c801d915400862204d03502da404003c024040407601040600c001c0c050350085440394481d080c05414280c80c1c1b0007400380340600e0003103034424080760074002c542c0a20049034040030307100c40c03032580c01085d0414030303158208120100741c00e024552002160f9402e00413000709281c4800d00b001c0100c0007508031840210303100c903030860980c0c0c2c000700f803660780f0143c8100403c04a0140303082c10310310350304500703004400803c0b40701040c0c0382c80030030748000660500490040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 697148552 1250 697147302 697147307
    0x606130b151b0303010f0501030b011403090a03030c0e0a09052215060816030206251101120605150c0718060603140c070605090c04290d1e030509060c0d 67
    0x62100b6150740c0d0041d8a55070404c900b5143e01c40d01c0e84116410305071914070041c07041e1f010300700c4040c110300021691500c0340741c410400340e41c40b48607840940c0407900d4544050890b0703200c0c40c040042440b000c0c01d5104103521f441c0841004101c001d20110750703504a040b00d2401042050f1280d90036502400c0b2403c0c6942942c0101d20803982507a2040a0561020014180065000d1003003400c4030b070119052500c500308a001c0381c0d0a000d428100415000c0020715034001c005020006001d03920302a42c5150054118501100454143c0e0081c250321680c80d844542d1301e40501e5006026800100b010783e110036588010210341c080001c1014942d040d140d101c148255640b40c49084903188000e80c034100301342443e0711503a40910400c500a4002d903281c0e0002049818100006454800094003c21609015106942100d01c0c0481c1030b03502001c4400f000030151500391103103c070300e0b504000d102d4a4210b0500c050210000317005000c0301440800e02c41d10405030b8405018284014480029217420460071100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 697149802 1250 697148552 697148587
    0x1b090806100e0403120b06040e090607030608030904020d0b09071709060403090b13210c090203060f1009090c0c02033d0b06030103031716020606130b15 67
    0x60650091002008000d00007196402c0341c2c1040d0103007024003031814130350400000780c005140d080e5003002000a001a420400e00755030fa100d51100401e0380d247d604c0b02a012001c2c0c4220384200c134080c3d80b0920100110340f1b080c0c0d00401182d91807680c00151866884041190340741d0445a800204a00c0f4a140d43c202241c15061540242100c01514140c03a01f1f64000d0450304046c01480744528001c1445980000c002002d4400b401001d0020503418262132540001201a42e40498004084002c005a8914030380260b900442c2c0060940700d6400c1e09905000224202e00c42c16070400480c0203001400500ca84142a041c24595540343c41030822801450b1614084142038402c0b200240f01480d6440240c00319911080d9403000106142c002c20b81890024202840306280d11040000c000402c154008100e40c034401d03980c03103082600d540e4294480c44615480307840400541c004600103103040c40c0110024180d41d1760741c140000c4240e4404007050309442e200741c003005070010000d5060790880c0070840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 697151052 1250 697149802 697149811
    0xb010501021507050a030b0105090d080d151406090d0c06020a1707171605031612050406050a0e06251b03030c14150702010b09060a12151b090806 64
    0x5100b039414100300041240c424200c14400705a5a000309410700c1c0e104404465210300300030000103e40200342003141241e80103208000e5228901010b808240e650110380208943c0242c1c02142148011402d20103140e008c4441036500160b83d1890500203204d030400302d8098195503000b0074001e002403401d031b180c10b4802d2101c600a076205010150010700000c660301034041c604401c0e00d80302c2c480840d461403c4840c0900c0188607010200368480c108200c420203210aa008400340009408a51811341d2148150b010340b00002c2e81c204044c2c4c0b0240e0250b1241c140c5100040c007240c0c5480d0490400110110944030160300c682c882d8595017040c84a600540d40061000254620040e407441d940034280800b551001821299598241c0303400e454140034481c540101c8040d02c00036498403140090003040700413602c5215400c0c8201041c2c280c00c04c00490030a880d21005801e5241c81c4c1601c90810b400300320215120503a40b14031444428140c22081d00410b52141d417030341c00620b41000d01041c00c0500042c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 697152302 1250 697151052 697151083
    0x71208090a1d0a0e01180f02150f0412020105070210021b100c060b030312040f05010f051003060b0f150921031c0626010b0301050402030309060a09030f0b01050102 72
    0x101d80c0071100001c40103194111401800c0021003404820030b4901400c1158801b03260704d481c400c00c520501ca01c0b00403003040f59100b200c24450f035107014284e07010380d4018954540b951040c10322050000040c0090070302030940c01410141c1c1403801c15400036441955581d150fa005030090041030700a000504a6102c04040031075009040c80c2282c84000d00c82d0041482c042e00c0543c0f02ca01d4104a40c0341442104c1c2c3c1e200710000461315901d0b01c1d081050f0755000342c3c5011103d45d071904500d98082c414a100d168011084100c03650b94003403039500c59030042c0030030000c140c1d482480e2410303403039280d87c0c2c4040b40700c0c0c0158040c80c500d440d410484208010300300c00b01c220241c0d40702d060004540444001c030480e01205c6d0300401107202ca01d1810b0310000100741c65000950003d400180407140c1c2091212860407207106240280a104100802c1c9804d0300d02c2964025010752007400b02404034903001020700074004443c900710b03041c16035036100e1110b482d440007401e0714464003401c01480196030502101a8039020740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 697153552 1250 697152302 697152329
    0x501030b0409120509010302040b03360c0d020102030d050907080106050609030a061d01060303020c100309030801060f1824050f070f0606181505030c0120071208090a 73
    0x352a05540c0038420f44510040020004001c103ca0703000c1c2d03040d82e0142414950664032480c1c0160403480c01c41a001c8a9030005996200449041e44003040d10a91860382d60050480e2814000900c00e45201100341203042d0701048c001444d141e0400d01c038a511030311700354004240c02c40c42c00070402d017100c02903001280503000802c004d011540b000290b0b42c07001988002c00080b02d2400710b80c0c0b4025601c120998082550070108000300341a400100c10f1107455080342d0100074120b29244c1582101d8407400004c3c082280c2c000100407050003142c1e00c6a00c02818200303400a200110f40094001000d90070071407085600c803104031200c480d0b64420b41014002801d20915101c0c1b0301b68182118040c082c00141031558260100c401c0203075a400c000000d084688503880180c80341d0440340050024601000103d941c42d6100281038940024100010308040c0c4513080100d400c5804c0700c031540810001941c0c0ca00c1008d40000306a0040e00090449600a11380203450303591000030005683c0099000d034500c807070b84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 697154802 1250 697153552 697153571
    0x1030207051c0306050a06121b0e1e04060303180e0f1b070b010314060c030c0a0813080408071701050106120504111504061407050712150203100501030b04 68
    0x40e0001412592009600b0741d200c08031000c5000d0701d030340d8001940002d451040091841d4100401c5406d111480302c05010401da4224070b0003100c0303a61800480050445c02c054811801c141c007628012000c40d41e407030a103000c003102c00b14042d00c81c01d9208030002402c1d8040c1400c4030644000704409404585a0011079040186c14003014500c01340c50b0820044941050142c10442c0101311400b00c1d030f001c00e44982541c0e40f410f10b1601080c0c005100c98850142c00009400c03088003100700c0348504442b07480d841c24000101c40450311150700801e40012400713040c1c4c85001084270080640000c200f00ba0007000e5240c1015010466240318142c180c2a036030401005010745031304a110501480701c1e80384001a40d41d00c0d400c101c00e5607141c1d25040e07a04a5821010004100c14034001041034a07180d49985151202003103501095100b909400b9240da003210005015902d850590010824050051400e40300120746111040f45d0086d910710081742420354040225507090b025202129000302c1d0104022801e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 697156052 1250 697154802 697154813
    0x90e0d030f0608061902281205070f12091a1906050a17101509060506040506090f13020c0c011103310305011a01081b0a030203070512041b0501030207 66
    0x2000790030807220086840c464105003410380c2c1651142501c80120300b1501f4036042030122000314440c045000030303004000103074964205000b02c034001c081985e10304402c8030224200321104c01c001524024244d4a8140b00320200d07403c0d250f1158422180c1e0304c3c0ba0420f0910440190f203501c0304940c0d440d11a801c0c040d00b00040e0340c80800300000c46030405000c051002c0c80c02801424000b0000700500080d2415014214802c01d4980c40300a607824407408000c42d94440d8200010750103a4443d03030b58481e030300700501c2d50f040c106804800d1054902810500807100ca00100c42c040c1d03040780880080d00d40c883c800380350242d0380c8850a0306083d0000b40145207030004400011500c2c80415000f860302810041034900031801c0400200001e42d0420002c204a28455521142e58015881164002a4a6070100741d4800c010309a9180d8081841d4000e03251074000c81081d030194000811a40c10301074184482035403494414201482244541c144040401076070300c00c1c1510010503086a810180b050081c0f80001d007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 697157302 1250 697156052 697156063
    0x308180901060905060d020d05040c030b01060516081e0409090b070908061f080a0b040b07180e060f040914100c020d1b06020a18050402070822090e0d030f0608 70
    0x101c0640d5506da83d01603601c82c0401070b01c0342314902c1c102245040104802e020140b10540b081e207120b1805a98180d0340c5100071030ba580a040b02003008440502c243c1800508003400130b00a80070701050700204030560390781e900c0c1d042d00b02c0e50110412584620704003042100d0507a00c250302c070906083c01911503050000050f511980205030705038000740301131500c83c01c6030203a522000034403d5004640503813140e07180a40252170142d908907110000003010070385c1c0c05e010752291481c0c1c400040f19680f00b5850103000a12221380508110340210740c1044034010b80e107803030260610a6000e403141e15402140141410302d41400303840700f40c0c0c0f203a1424084042403035000ca10785010746c44910f800300c03031240c440001140c490381d2a240200460303c00500a0b41c080e400080703050405482c41e41102010f548e400511060b1f03c2001c000900506041001c41c10898400364a15101c204c501e8280074640c1d00e4004003c02ca994102c1c42083d03c0d44050b41640400d5030501980c1c10300c004080c0c060114501d040d1905aa92 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 697158552 1250 697157302 697157309
    0xc010b10051602030f07140a090c1b080408030f0405120d1b110402030406050402091008070303030203090a0c171b0904020d0201050c030d1b03050f060909070f03081809010609 77
    0x40d10800000003d541d420403503102c0e4003200c0780a0703401055403804c0f9040f4004c24114003d0144110140c0060f404002d4862000c1800c5151900c2c0100e50200a03c03215400110500301d41d0018280800b0038180b02c1080901500e100e4015416680c50810f800c01a0008882c4040c42e83e0b81d112910718002240c3c4211100d070300d09240e005040030300c0002e186c0034085010312000941c0241c0302004100500a154000303a014500075160a8800c0d22a417034503119030070072402201402d9010400070400240f1aa00442d400007240007030390001d010950702c0c00c48200840d44040c05c0719001e09180d10365803009000000035040001071003406031080001140700014020000784c440c0400b500e2a1044d0b9004008607400c03034850106036030b0b6400c030501214009142545014501a0240d41e200007424000c2c80381c03e0040361160041e40309030f6152803c00c0300e102c50060405045001e240340c0080c4030220b9001c42d101071880790f48c426841d14190808000006480300c1440e100e40c140400400c03903039070030060032000d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 697159802 1250 697158552 697158577
    0x3030e0a150905060a0309080f03060a080d021203070c050312070305090309011b0501111615020304080702210d030e01150f15170a0b01030506061e0c010603050708030c010b1005 78
    0x151071031900c081d0002e241104008d41603d07000a6480e0494030424000c40c4500801c640c04d4032440d480e408035a540c1c01c1c0400350a80540c3c02041884954030404004d50361108840c60504800b90310b55a841d821900404088000301c000041030010454040c0251588640a003009508104801000034007038600e1510343c884100e290b00103c014440300b0b40100e000c040280304040d81c1d4090001d0b030794020000606007a11400c401070704011a400035802200d00481d002140035040c0801030b0200f00d001c0c600c01d141115603540c1383c0d01740e0342503102c1448203507550503a648002414032940c035005402c1d521100f1303a8800058103203909110075800e43d20010265200c03e8403203402c050700d01c031040d50410024043c8442500150007005212001d54010707a11030036081e82c3c10300003503c60b001400b1550103110041c41111103441d00740000f0741100800382c02404002000450015503d4640386e04290483e00007048a400008000c01c011000f4010104c11303520a440b0000551650500100b441c06610740c03c1a5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 697161052 1250 697159802 697159807
    0x70e09031e190c060e010c0c0b13060509071a09030d0f0c0512090f1207090e01180c08070b040f090c03151401090911030c07031803030e0a15090506 65
    0x3404911078050328070342d080d1050780d044038042c0c09501409201c450704045550340e007060011170144906000d00584400c0a40b240390184850340e03114800004e00605e8140c9140d072045401740842c581e03004003402070310003602134000e207400c050440000b52910b640c0d00b01040001c200c0310941da1000201c44d50208100e2500e005c0c2e40103240d4046401540c1e900028010740301e14241803011143c003900405001400300d940b001c0d00f00b0708030309001200345405282c0c035690700041c5003000101401c2e0005241e132803150f00001a4240c0031400b11240d0702c0f8091050715400c41c0759400b446813030800c019040107031080b001054146840d10501d030b58001d0050003600d880b580c544c040b05110714001d80155034442c40a281d07126042e61501c81c41c90360002c80e1b954090004081f8100000c200301ea91080380346004400300428a950384101228440d540460802c4041100780130b010503081c407141c00e001d40994420f42e1110172000248081000100040e00003108a82000c445500810f82200e0036800701c07002503c0094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 697162302 1250 697161052 697161097
    0x1d0109020d020d051219090e131401020f0403200102060c070201180b1b060106051c09170a0c050c0a210201051b1e010207031706040b040914070e0903 66
    0x10300340341c5c00190705103032030300049a24243c482c0706440c0080130505655a5805485d039030300c00000d0412055440c1100381c00c4074690707100070a8007282d0f540b0170725011000161608912401651841e4025031089c0c406e841a141103038090746000035a00400d01c1c0134401040e841c240201801c12901c120074009042c004c0029041e00440203509510b00180980140161111000b158280c100c0c40d0702c80c410f0b0a580503800010130118090401c1d034400e0009004d1403519200b04c1c0d01c80800811818800343c07400d1010642440c2c000802c0402040c151001d603a0305000e11080e0301c1c010b89803e50b41241c444c400e0703441c60802d20000c903c0645224070400300628070600400c090006980b00d00c18050303201c0e0046400b4450950700440040d070307038020b0810b0309840951080f06035802402c07401060002000031b100c0711540c41d81a00d410440d0f5400020040c00007134812406e000140413110b00c00c40407100031614214558064a05001c444000c003040c8018000070b1a01000c415140d2065000c0a040700e0512260b40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 697163552 1250 697162302 697162313
    0x51204020d0f03020c0307080d09091a061303170910050d151409010e01030b0f040c050d0b04020108130203032a0105010e040507090b0f0f01030b131d0109020d020d 72
    0x1c0d82095001034218455150609000791600c244100032800b071300c1141400102d1030000641540c40004682c0c070003050354201050b00b800750001581d01203c8200500404092383c0d9403070001d082055103541400c104c4c528502d8070316a2030180044854542c90305000c481050348540d040800641e00038030b03000340c4c0c034502204144014002c204005100c0e0a5856010403c2083e4070000d8510300421aa244901c2c1c0c0d840d040000411801d0000810b4070803441c020a254994415002d604030b4483d0317001d040403d0325800031903401307080b248082c0d03207103034000040c0802d5582143c01035811900f0f544500102060b5038001ca5602d10079044c135007480e0103000008801d2003c030181707007590b104800e0000b0310040d40c0d1500b07602c11006066605680c40c0c0990034000504000500c02d03101980c43c06811020260005801c020a8a84009245061649980080c4040d0307aa8000c0c19014082d1620000345007190b41100c441f100c80c495021004581c501030b0f10602503a01c10007818501e55040310a56040e91a6203040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 697164802 1250 697163552 697163569
    0x6020d090f080301081926360123090406030b0f0109110c12030703020415020615030f070317040b040b0c0c100f030c0912110a080604020105120402 65
    0x9000c1c514100020000c0015680065040340e1466080780e07117500d540d40b20b03c03c0041c004800200810301d0000b844404a030b100002c0e48071400000c1165091900c5080785e0500382c8071044200809000d4400020340061305840311141008082c6828604d0140c50340010020501005188030070038008030b5003021a5803603030000000307164409641801400e081110449081c4203008901906090400308c070b0b0106001c009a80e02001200c00400010107881503d0081c0c1c1d1000c1c00b03a104042c1c08120204901c0e00f58008800e03041c8142d0700422051604c0c140d030b10014404c469a0318842e4001031446c129291000a024080d83d800942c9030030b4084100d5041545c073310a990103039480200228001401d031403810702070490000c004c006c3d04c40d404c001c04204603241204100c12000704002c1300f0402c408038030aa006603030000c0716042950202e91601c0e60f1070300118200f4012034107041508549080390030514900c40040c694200182400d05280c0c0c0003030683e00524580481c060390400004080d036031421903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 697166052 1250 697164802 697164821
    0x1b0f010518032b0c020c09011d0c03090309090405241b0d0b03061006170f15010201061a092107060f1704030503060f0f1e0d0206030906040b0c070c0306020d 69
    0x1010000386008541c041d4850a8503e219441f450301c030341c0006461180c6409204a0100026a03143d866890643c6a112a00090300c011010300c010b0000401ea6160213640d240618090703402008200c0c03009050175001e03902d140081120381ca000052061440105040c00006258560740c0390b180c860071007100000703203558020160b2500c11031040c002c400900c41504020750b400b0b903031040c02e41a41203a100001640a90720304070403105200c00501c502814a03075500c1070700014800480c141e581c4003031021381c00c070b60242016694807000480b000c0f0352400d11144900144441c100c0c007107a1442da19902d40f203048911444084c0002410800300182c40b5811a4078026201c0c01c0d0f05040d41880d040040c115002102d0b120701541e03040507010b406142000c44404155002440d8050052102c249130940d00f42f00307201181c000101c200c041005940d204080d5101740004001400d06181505042011007805000f03404200d4013004902c021880d40c040407010b0341d0b0410005681c51582034020001045001c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 697167302 1250 697166052 697166137
    0x9150b0d0231020a030606110a0506060d0609050a03031e052509030501020409050a060503031206060d0b090103050307110a03150207140a0515070e010e13021b0f01051803 75
    0x901840701396096846003054031002d0340c42c40c14000b820303801c960707a800000320040c00552003900029900e2500940d81103c2920982000c65800056990340340b07810848041100840e03220380e01880507141c076243c284144843c041c4144260b0a100c000d02c090326010300c61205071002c1c408030303180d00c0f00e002d440000020340c1c0c04002150b842d543c0d01400c000a0006850700c0a21034103205002985d1301e0004150350030075100c101c9a06580e19660f0410540d5401a074043d4001380c2c5410f929046a581d02c00705a00850060000d1640d8508901d0010804880c51108a105640b0280140003141c0c00040d204910713205150010380c2d40e1001c3c00e00365403c0800701d40c6407150384600000c5000b0000041040d00c0e008250824000c00ca4945040c00c1d900e0341030307100d072060014000c4800000c00c1c2c0f408020505605201c528010f01e40180b19403070310802d81c00941d1869040d8409286240724140c244506917002447c0090111b681c0202c074407050b20380c400d20758802d9040e850686402c500228800c00101407140e0711 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 697168552 1250 697167302 697167307
    0xb06070b180705090c0901030914010c050306042301060c0318081e07061d040f111306020703030c032d0306180b0114030907050409150b0d023102 64
    0x160300c1e5429007810310414040354040c24a00203030b1410020b012500400000040c1420f04c0303008801100140110203017a01e80d41c1368201e0386901c503c030a100320810750350596607140c6e0b00e107403420038802616010104805102e0b021840703050812002c81c102815a40e080c5001110441c450a00320b071000c0c00d4a4120301c0c1251203060029100c58000f0f14103410000300703044000803554078107899481e10802e04c6000007003883c3d01600e14003041092070301d04090400900009204001000c440102c600d103004100000000013508455040301003609401041c2e40d1008002c40d07411a03074020812820580e00030240030340000c0c0b08852041d0207030640c132013224545041300711b0032003144010042c05143c4510403201d507402c50310280e84c400c14000d1201084041c2c407409440200740e0b440000f1a40020043e4900d03029480d030102d4103548074054002524000c50900b0390504200d6180c404442d01015518440c8010346c880c180140c458058071f19a802075080b000381d40606210003045030f00e203502510341e10180300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 697169802 1250 697168552 697168561
    0x3080f0408060705041d06090601200d0503221106160605040302010f0b011e052a0709050a1509113f0403020304090b0406050402131e03020a05040b06070b 68
    0xc0050403c4600c074440e4258881c40c040a00215906e003901c50380d800c070440c07a0000310350754001c42e01580381c03030210302c0710305030612010310001d050224082c207803c0003075000020320a11900d00100441001c80030700d012000c070312540e583d0415011400702800d0241d0340100c1c1302c01408415248442c00603412400078440313441c00d80340080c02440000803103800d00e4908001c61a072035214000d0705071401e45907403500701e5508210b103050301c00c0c2c4c12500700c0e040c902c03007090001c0701501403594152060074042e03c000d00203a40ac000600c001d442c4002c0000c801503203040b409900303101820246000304c43c060840000c240145a2450440e4401c1e803091984601080b00c41e0301013030300380c815058a004414040720140d01565030080c242c070700c0700395009001a881403105214990540c0d0001c009400020000a841f594403004101030340c200b08100510010340310400c000e4003201081501500410450209501c1e0541d40003c2c1149180d00a45020b41da907010002030700d882d64011542c000740c011104405030310b030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 697171052 1250 697169802 697169807
    0x1b03071b02130902040f0606080103060203040804031406071e0813050c15030a0c02060601050d05060a170615090106120203041703010f1d1303030504030c0b09030901091703030103080f04080607 85
    0x142d40008174041c5107017948540500c1c506126180540d0441c0d940d43c5400d92850b200d4101a400182066440303040401002000500035920b500403400030f4806054907282c13100e00600040105210340303410fa5203203130150078280c0e4400c1032964000201c0d00107035040c045a040c21490034840101c0386402c1035481c641c14000002c1d800145101d502e0300441803110346918207003242c4406c03040d00c0b05404100107002290780010a41c00c40c070b41c01a009003400c0300c450b564140c2c10701003100296051683c2d8200741c0500011200300c108401c958030050b42d150702d0301c2d450440d009026409050380342c01000e50110104081262014a022800b40c0c07004069880c0d5840300c0c214011143c0610030f485075400e80105044200d031200500074440c2095036800c07042000076071003d8019081c014412400c04c034040720880d000a2826888034000c08400700113544880421001419036212900000224007002c40d18503488640001102d0540e0340c4107020760784039074001f444800503000301d4000b81c5850041e2010041c4043d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 697172302 1250 697171052 697171061
    0xa0608072f12040e0711011119030e150a1a040f1b0314040f0201050d050411030c06091e06040315020a03050112020d06020c030f030103050606091b03071b0213 70
    0x60030071041d034045072403029580c621482907100d0416200b1010b400161058010480004003640755000443d2401d03c8510100b4540e00c51a0344034200903441c0b18201c0b165625108041240000c0001040808a044e0b14000040300051400442e40c0e07c8024a030300d060102010b40d100c040c000f40041c040e041c0314904079400f4100c3c542d4904424034812140d030b02a203200b4003072482188000001004191100c0e02c5460300f03210031507404d9061000801c14058440d41c684070b203602c0b4501600309440110041c40405013010040600ea070700c84c203414005a21581e0310706100c1901080c0d1170383c0800240a03128080f5140c0e00542c2e0001e420603041c00000810107002d80c00809481074103650822242c0c7c0c8a90381c021241031034203400f139007100052712160000b885030390080c5a40b40c1800210790a01e040c2c01401460f030341c002d0b002101c0759000801800520304050540d81c0e00b20032910442c000c40798801d803000c1ea00b0b000c003c3c0b00707404201d1104081c8028000010801e2185034000d49061907411804050b0300160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 697173552 1250 697172302 697172387
    0x30109020a08060106170f06040f0912110f0a11100e030f011a090108030d0c02031c0b090f16081302060d1b020316020607060e011817090a060807 64
    0x40041c1b8803002a40482100c640c0306d007210040c1c000031911010280801801002d08000080313942d0304141010408900d044c0b80c81424680d01c0b48208240d0000d940e00341000544c414803e6072101d001140068000c0004550b03100040e91030710003103a00351a0484500d0f2030700c0c4031290580911404000000b02c19001103040346550400704500071108418090100024071904801e5081400320440c0389503d40c100f0681200c0d9841124102145100e1207107000141c0700c0356080351680e81c4854001800c0c40100b55a1021010401a01e1843d0024240c072a4a0384032964004106203440002e503110403142001070096000b80030b880e00c0e00d8100c900c00c0010011000032001000c40c81492190441c4000101d030703001d02c0150204042071364a9802d2107051381020500726801a2500d1241140341024401c2c0b02e0090450008042401303800e0402024010300d00d4140442c9103403c11005903281c441c0301c0d003a000c89070b040c0f41c100d10380e60b61084101c40407207413000070004402484000c03409503c4130880000d460b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 697174802 1250 697173552 697173557
    0xe010803072010030e010e01060602150604020405150a02010f0f0c020f0a051b030705060703020a120305100e070e0a09240e010b070302070b07030c061a03100506030109020a08060106 80
    0x80d01400725260091101c1034120342e40c00503c0303c100a040600c203412905a881c1c8960000c90503455103180b8a0a41d21309410650041c1e2180001e00a103000d01512a600030300180c03400c529080c00c0c5070200740701e081468062400c00750002149640c5902c01d40c0a0a0b01c090800c204010404c215468900501640898000140b203654500c14981c0300c08144095501d074020014074042409001711844880d030700000a138103010715480061147c44071001440c0e1180b2a03400742013280118a40a00049407030055042018681800c10804c05003045109064a0441c11081c05a85d64100c04503442081124080d402a43d5001c00083c4c42009400000c0800360f0342002d00c041d03240c61102805003020380c1c404d258095032504010404200c2d01001003202d54068419600c009889807002c040305e6010b5401140000e40c200342030003c0c400c480c840d01c070780440024500202810a500003070303a103400b645448940c060b600c102049055600b58440c1d54070319805040e8a41d2a5503403900306403201000d01c0744001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 697176052 1250 697174802 697174823
    0x140105010311120d210b0310061d01060c031b0f0b0901110901120b0f0316050306010b0a0c23011a1e0a060503040c090501121211030702040b0a0e01080307 68
    0x181e06102007101403084d00c1c2aa1020381d00309064081c1d44c01240c510314030f10034950366903203d260103440c10300200329038140c80f10b4080303545403402035440c440740640342c905006080e410005124080d480100b0031107040e0036151400070790140d076404d0b0203000c1000c0401400512881494130802c80c080e088940710f110f148001700948110500c1c100103a1103024911800a42c184c0154113106009601c208001c0310017400f190070310403500380464075094030054610340080030a00b04102518003000f02c14050860301142d5420304100880240040400480080000000c00e08894484ac181845200c1c505c030380900a00c0034400c40f10500f10b5030340300741780355500810030b0b42e100000c2501e82d00c4520304a01d802a0205810916020b8126000d0700041e10481f1004100000040d21141d1030103118083c080540d20b120b44496240303410a1000c3c110702181e028040d0195004c0c241c0d244c00320039035011540664001c502c0c8180b44000911100b100e4011a40d58113021f000410100340000150400754410b002500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 697177302 1250 697176052 697176079
    0xc0102070b0f120408070f081215061b010e030a030e1510061b020d062304053309031b0708070b0702210d120e0d0c140105010311 57
    0x2512480350316080115040200503150b4000e2403c500d0640c4940a01d840c1414110300b44c1e00c11004021400f029284810b010400c04485040d00101e0350704080000e40b062a982c80d1400030a1190040b1080091050b4810400032500e0f10207400035034418442005072a0380f01108007016009003050101502244190080c103074440c103184503080e005094241d140c400b140e00d0440104c1c0c1807000134605407030080001c140d42005840c0c2a032411000c6209000100d007201352600c200300d000d84690414450748510b00140300120701d001c58103c01c680440d0001c005420402d01b41c0c0c031409080c1101200c0048407420402c0303009007020000d0010700040c91083c0d91556450b100701599031459018158043d00400000c0002c00b41ea0310042c007406201400d1841a04001c04c0456101d401c03e40c44503502c1d40040d14080d4443e5030040c14810440c49580741000401001c90380d15540d111030603003120500400020b030030141300d41030603000c80907910f400081c4400d68603403030322078004c541c0c0d0f10303905004800760000903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 697178552 1250 697177302 697177319
    0xa050702010b220c0c060603050705011e0f03110c1b0f01090803040e2512110403030207030b04060615110d091d060613060804050d080405030a0c11040603050c010207 73
    0x4a00070b100248500c1c2c2000d14032105030002c0c91800000c4c0d0501c502c000600000807654040c00380110300804c003403c070300c6180034000b40c0750340e8070041001e004a8400311483c40c030315040024440d4900091030000745440c02c154407041c0d40e2290182c03409251290948802440c0d070741c50950100c8801c02c0c0c45030005100340f0740041d00c425400703001d02d640503001030009008800b0440c0110350701c140a2000f20039240d80c203426100c1180e100304407100000300711000c80711808110303009070a074280320b02d10300c0d0303141c2031171a14001d44601c100d0000600600c0110081414000c503600704402030001c0c082c040d1000184401c0c087d0050141e0705c0c0180f00350040d4040302034a280512a03d400b103500342181e404031240d410500f403546200041040d6800801030015610000541800342c0240040b81c030b80300d1480c10a800d2640c6400b0440b42001c2c01c01810404010008001006459440c8003905220001468a01e04903020781e03240425141c02c03626181e40003060007000603840d0042642070302640c01e1941c03980c060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 697179802 1250 697178552 697178569
    0xb070c0812130e0901090816030f051606050916080604051501030c05060702040e0102160c080109080a08070903020414180708060c211e100e0a0906140a050702010b 72
    0xa011101908141003050800c88003080307a11280540c00020303103e420707942e0b0a0351034100888c92107484c607800380710204258104401480000c003a0400c142003c1c00342804c0104060b042e00700800c0c82d0784640110712580760420110700c07401000c85c50301038126240c0c0ca4482d514441114266035a05c14084c040d100301c0d203125502c1d03069940040f60807913850b0070041403200a80c400ca00898002c1d41d10a071046610f0303428070281200520700070b07400081d04054144411085440c0d080b0350705907450103901034001400e980c11a2000c0403142070010307650380d5007034040c3c48125042c0d101039001400c0102d0414480200d0000610800c44c8000c0c50240620261400e5a40d00850040034a160710500205918203502c5c009011080860340e003019510100c065541454101610300134103044484415000071029101e202e5404810340c002e01c003286203818101a8203450140c15062015500c4401500340540b0381c21100d400454400d01802c5401c000401800400301201c0381d40040d46005810400d81c500401d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697181052 1250 697179802 697179817
    0x30c130e0702070e0c0d09030f1101021801030b240304030305070c0506150424240207060c0c05060313050d0e13050c130308090432040c0b070c0812 65
    0x3c004030ba06020001400703d0001d00a0041c114051003500140c1c2c4082c0a56420303c0d109541d5050805007801015102e040708086668440e4014800800030307408445245c401c0d17000910f00440c004100101041c1c80050101c151032581100c28018014806d0000046010328482e0350f04200a41d646541195640e000100c000c10a07001000801c02151591109450070311000304001000f10b03140405245018a42200399000c5107020307400c100d2009020454142a404600e191202240c900320003511059540150070500103010034010601036040b0050303000c0c2c400544038903500d0810884410384405148400c84081c854401c032403a213a44100c0042d07445110151131b91009121610100000e000e00a0808088035400e0000003150114041d51078003d43c0980c1e04166100341031818803003a5040c0c1e6a10242d01c2c40e2000002c6d01010000c050004800d80003454484203403140e00d440ea00301030040e4001c4110707810100710301007800b151b6941042103030a51700c02c8801e120300d4111648810b000318034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697182302 1250 697181052 697181057
    0x9231f02010221040210080603030f13050f0a0303050a120908030705090a0515161a0f09010c03110d0e0a05010507030e190803040227040308090105100305190611030c130e07 76
    0x1d40c1b00703c0c005d0082e048113800540041c00da9050006e03c0300c20880c1500705090880001d91113840800148c141009128000c01c0c0903030382403c815045440203409886581016010400300c1e040000f10114a030303210210003588003541c02da40e0b00744441c0082c5540c02400c0b14610580041c003001401d03240044408a880035583c0d8042c1c10802091104030a408003580151340801e1482062091107141c9110700384103187c1400203c1080c10301c800401d00b1510700503403060905242c110214801c44001041c1c0b9038046107043e01240b030300c014103c101c0c00d1040d0b88100030700315800d0505016003950103400040d40c0600900c101d519440460010b25030b58071400310b0180c840801040400c0250404c1c0c0c03500e0309001d885650a0548051103c1140c00c1c221003220264000f950340380034000b28030020b006807078103c15090140d8882c2c03402d5071a5035071a0848800ca40c6104807280758104100b00c102c0d000b81605100310036210f501c038030302800c0b50b48440c0d02040301c2d40d0103e0141000402c0d078652000c0d032140030700e607a070307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697183552 1250 697182302 697182319
    0x7020f100c0903150e250b0f0d0c051b010207020a030201030b0a0e0108031308060601080105041e050c04050102120708030606071401090609110109231f020102210402 73
    0x300c0c0342a00400c1c0c03600e100d800700710b44004040086002c000c021088502080310010b041c1ca9100a414244548510142013032894460400316000f0822640c0042d501250403580d511104600c0310400d03481081d0010907000d007841440e558407904400500307007000842c2d40507450410b203c40c01500701e2148800003948176010010900c0594801d070310010722507070050007885000e81c882c4451110b09409070700010203a80b0010790b00010b00d0103c02980014030b20072008029604000d00040d080900c1401205d01490303503030f200031140ca05404489020320b01342c00003c021a052503855007001d03a100d406054050b214684070001190070703450880710042d03002500c031801d40d11000d042201d41d52050609483c24048074520300301485082c403411150030300c42d00c40011807240300e01c0c11000400c00a010744cc188182e0500c1080448500449019600c28284e40d002c408a030b0400001c084002160f00340d00003100c0c000741d00c01070300e4055008200505201719540c401d074040800c200d031440c0e001c07038000f034000521 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697184802 1250 697183552 697183573
    0x102160605160201030e07090203040615030206030f0705041502030c0114130f060b27010f050d300809010608160302040507090302040e010b010e0f09072102040303050c0607020f 78
    0x6009080000510505d004a8041c0c05100b600d460101182c2042071401c0e4004103000410141e4410707a45508240c20f0440701d07452640d000100d55000082c441b88241c081c2d0b2000400d040d220f4811140981032042d00004904240c000082d82d0780c01c4100003040c81d41c80c0c0030001c04038010011001d4407803450a04a0303d0707005480da540c5031805001303120840e02c00b174882c00006902e40e43c40542c01104403040c030081d0500400540070741800c95040e480912030010105040c000354507002584100550403141c0805250046400b9a4840c0107135650204900b803408107031a0001e0380051a81c3c081c000c0a4002e00019481d00b490a0320341c802100c03802c9000010b5002000142800d8100c542e20203181e0804e00041d541e6500844d003035801000350703400a65516a1103d081e5a081031400480c03100540d00c0f440d40344002c00c04030f421010040d04d450180201880f81d2540c00014100b84004841c28500640d1102d580f86006001074006100c0340050f4010400001c5202d880000d201e10381c40240c1009101c102ca2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697186052 1250 697184802 697184827
    0x60f170f060412021f02180108040308130f08070f03081b0405130e0106060203090a080c0609120a060207060212011e0b0310031703090613110108060d140a020102160605 74
    0x4000c0203c0b0a6024600c42c030180b510400c119810107000c94513026965428036110380301603094080d261414011b10105101c0403a60041324554005600185503281d940e5a0030031690a18400c040103220101c0000c0403410403a1030f80318582418840d80b41e540403904c2e01e0381000454402c40c008041c16030b0085c0000c200c14a001070600c1200301180ca000501c251080d40240d09440352a08050090390002a1120090030720840322070013010554041c0100c41c090000280441c40f50944180c801c00f800106030048090a000440034607611804c1107640d42110320b442d00181d08040202e402101000b8000030780e000e4250211166000f168030280300c81401c080845a15401c043c01038000f80f12403000c040700166800045c2102403407100070050b12072034402d12075841c0020040840482c94a0b0750709940c00180420140100c11109082048040d1b030f40001240a0550409018203040b4100c036041e10000c0c0003054450005000b81d0a48100c0c004d00402d42c4800c550f1340c80303250001001003014110803039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697187302 1250 697186052 697186073
    0x1d0406020901031805070e071b0f080f04030c0e0a0e0307020405101206060807080a150203070e130903110c010c02011d0a08061f050108070302030a0609060f170f0604 73
    0x141070000d540c20380301c0c1c0c8210003070301c44c0207044032680d00c040e1003030007841c0c410b100e45a03110105161046c0300d0340340d6204050100350184c0c0000d10081c0c80074174100c100314440e0300340e99a104401c15174507101c6613241442404807400d84038603000d030704c079142c0031420030002405402d84104001d002503107441c40b5903081c031006200003401303010303030b1126020081040010b14200c600b603240201e401140140c20401c0d11070030254140c0c0002c0407548200c1c5a080041c1070390181050b04c0e000c2080c01600c0e03036500399094542c0300d0032082c02940300042928401d4001425070000309218040da0343c0044580c00700d050b80c1d6440200c8101c1601203848068000015031040080350200300c604000010007010008c0414945807c83d0821015504000c007042075800320134120544904d002c0c80c080805030724110000e8400c07400908a1001c054001002455800d015008540201801a001c00c216590f480c60115880507600a0440e5550f610f51404585200080d1440c00951004040d000b980c80d00d031740c0c250012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697188552 1250 697187302 697187317
    0xf040506031005060309010c120b03070302091e07030e010b010305060f0d0812100e13170d230a0b010504030203061303021f060e010909052d01110901091d040602 71
    0x3580d4003c5038640350100030f503000d840305a002051002510b135014118032041c070034039401240f4100380c0901d5940c00085281c21282c05517000030302034541c0c004400c1d07154a03000d000784482c001c1d4003c0c420032642c03650024071515041c0707000700030760b944000c011000c1c1c034020389503258455485101413096143c41054022010f03c00c02155240020001e29109420001c80d20511161540c14040100a01020000d50b011180c02589140c840c1c07941d13103003051400c040200200c2403402144a81801603294800380c0781d1050580c441440d11351102000700f01c18001c68504a0003800e00f0211006940100242c405881d80103019041c030781c1c0e404da64104580030088080d0304500c112506450010700782c03580c998040c1d00c000004101141440340100d50844181d2040c1105440c2240600115001160310704140f040b840010b284509000d0400e50206494050460f240d482e05140c00c3c4001e01480042c038014200380c0740e41082c56a58044c04031092009035000792800c0d0785400113400944d06500401c410b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697189802 1250 697188552 697188571
    0xf07030c17010203102115090b070212031f030209130615030f0f05010902090a0e06011a070201110304090f0b190f0902160b040605040501141317040803121b0f04050603 74
    0x5011b9520b81e54110207803c142810040e82e502010800c1c4456696095401441030000305403448a20b440600ca900c0020b18518481000c003018202c0441c46440c011300640c0c000b0003202150420341103002200781d4401c1c1c1103d4103031901d084c0300740000f1034140c25030440c4d402010400c107841031a200c2c0340482072051011151551303210280d60040e5a06481070b402038200700000210f840e00c19001c1880d041060300018100074510855a1207020400300710f4803a140e0a10b44a08080d00d5101028550f000700c0c1c00070070b2103504004c803440020701c0720303030040440d080100c2e2000d221540030340041d0504211030150090794110550184407140307081d0007c0080004225180e18480040c0d03ea503680c101d13003030b01d007203403919180c00c280401d21109000d040840c500c0781030011410b0425502c00d40c400c1d0002000201554403110401408054500a5400501e00c0400b500e90780e0045007054080c106040340e2003001080c2d40c03000009512074810a83e80042c4026000610303160818040000e55040101910740707 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697191052 1250 697189802 697189859
    0xb010c030c11040c0c0506010603050105060d020a0e03060a0207110f0a060f0519031a09060603070e010507020a090c020f030705030f0903030c010c180b030907050f030f07030c1701020310 82
    0x480341c840d81302e00310264807203548020710850310f80b400b44d00301a01a8006010142001c005000750394844040341d07809664600c0040c0d03224202340055592611804899900d03006030b4003044130400440e0020003030148541d90fa6445845031900300038010f9000040c83d90480c800d0030090205500404140c05d120304142021400e0503040a03101019040610131100000e0706c4021031110454540010f48082030212007070800c91401d00e0200304c140c000101003008109200800d06166401a0101c941c200d40103000d00804c0d64594408402401942a02e0740040c411207080c0300a8110100564031b460b503015010b54648441c46200000d1900001d00069250004211014407401c091042d80001c2d802611100600d003000540c1519488281d40000303449001082000080030000c210101611700480c0ca00c0b007040f500c40046898020240303100c00452140b00404014400c41000540403106c07030b5004003100c0c1181401c86820b074041901c00d09040c10840106024070711040e029110f42c14800ca45075034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697192302 1250 697191052 697191083
    0x100216030804050f1c090b09011e1701080a020109060f02070e190212090d05180603040c050604062f06070c0201261009050f070e060d020a020d030e010b010c030c 71
    0x3d0030541d04940716048240c40c0c0341e80031161604071b8003000040404021050501d0100740010b05100180015414014808280154802d002d6500c884c1c44000c9101c10090968540107900d40e52162410180cbc0410b015200004050303106802010100f145a0b010304981751a00d00310b1117080d1406400c002001000038900c4170101c19a04c09080303035860742c1c0d0701d002c514240501752a082c006000496410071104010400f1602c000d4040d100c40034000741c402d00da070780c1c0d11800c2c001c1c04498203070409079101c480007400040b00f59005c00c40091000035040300440d0108000345000c6200002542d4094903000304c000913142900440301c070009580113050a19940481c0c0101180020092030207444401d0b4a009020420442c00301307001c0500203801c0d0402c0070342018080203003188401003001e802c00000320303840c50980d100c4030180c2d191080842c00070754407803206100117501d8003c1082510002442c110700c84030050014007a1001c07140068548a204603440c0d1000c4800240313000c019210b00c8134001110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697193552 1250 697192302 697192333
    0x203030702060a05030612070623040510080103050106060c0c050f010c02210609010903051b0c090106120b03070510050d0e0f064203191410021603080405 68
    0x3c028040482c3d641c99641d251810401c6854014607003100c40650011500f4082a82c00401200800c0101400700c840b8003d4407141103c03c0c07189800407608100c8a00c2110585900000201d050328441d5000380a920344034042103c42110707056010301a4403d0860801450406444483c5400c2c010324007100798514540100f45500301401c0200001001031000364200941400f500b43c03c402d03910000d01403100b081c0c600404c54081c0c9c48032100341d000e19103815181140100140c12407c80050031043e2590782d15038000d407141c079406907802031341801e0441c3c408a620300864500140c46005180c0c0c030a03051110400c452a0f0801040401c0d000d0b510b1005014014040004400003a52040107203610704d0440b40c00f140745409540410b450070342d21040c0c0001c0f9050130402d0354250036003002001c4810004800280707080520340380c020006003034039410024081c01c0542d10300c44000703680846e91481c0d4424030907400c9109050080b02602c4c0d1422404000910a40c0c0164110303001d10308513120781008c05500c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697194802 1250 697193552 697193557
    0x4110402072a180213050f12060403051206030c0d06050c0702030609071d09070e0a1d07062019050f0d05090109060914091b070c0f1e12020303070206 66
    0x1403100c1503030714076030401c41041d05003c0382145102541d0158100418842c0d503c030001014040d4500c80c051066016440d80c607420314500310b00c101d00c4115100c905140c00c1c080c001c0d6100b03101c00410034103114000b402c5130600051540540300007400000c44140b03542c84031402424060010b900143d010828840540d60400040c0c2c06511920013030300106103010001e0320f024440b44000065001403004001c082c40c400709802c012200120003200e4182e4440c6402802011503001c0054450160700541900c00d000050500581e0610349841c1c4551850024491207034049200500c0f0503802244c0c000c0482da0480f0b0114003007442142280c50f00d0540d51119410140407103502000035801190a44e45503030301410501c01000030307040581240b414004070300602c904c0580524001c0b420000841c1250a944205c0580c40c02d0507080e1503103c008900d0320100b1100345104ea0324001c001c2c1100400c0c0443c0d071800c95030726100a43d00f054482454500e00042c1c0341405002079a06000901610f405620740400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697196052 1250 697194802 697194863
    0x506130212010509060103110403120e1809101a130b0d0b190603082a07142404150921050d0305070f0c020a0b070f03080702060411040207 61
    0x152014190704200502484c04001001641018140070150303008041c0001200c0030b030b0750021000010400198800d80701007021112203034010700c0201c554007800e040c500c0e140b4000e00c0e11205036070050594502c0e1005030394100c603d0881e05400c1c80c547c000750745044a440c0c0a0080700000c08070707041580c40c00161600e03c90240c01e6840500030803c100503046080c02200e440742c4e290307204100c050301b1600c90b2003650040c6c4d1003040d440b511000c001000d02c0021032103500b05503885000c8450340b42d183c505210802030411850740c02200d4280d41403070100030440481480b0106440c16504280c50803864400ca8a01c03441c00c001804819000400da0300c07443c1001c40c5001582c00906102c00085290440c542881c41c0f2240c0101841d25060001d1039034401030100e0100031038500607000e4030880c00060760940340d90380b100103948400034881003002a980390895505000e6101c49000e6551844103030b80764841240c00510414032001c00c804986480c1d8003928160f401030203006450824144000030b100f14011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697197302 1250 697196052 697196077
    0xb03010f06020d0c0f03050f070c090e0118020d0209060d060f050118020a080a020306060408061602150f011a16051006090204061205060301090807081306090e070305061302 76
    0x35418425540c0400000d00c20300c585141c0b42c8900d04040d201c00a544081344001000c20000080010b030680c0442d042e12082c0e034000000c25582d5a84070f01d008020003030418848019400c001035030218542c0000d0701c44000c1c0d000303444401c9a441a50800c40c01010040407158010109207680b004906c00388a1f01d040c0400700d0318002825410000740e02294801110050103141c01001020101039110170b9954100320407540260322501c1b4007000400900994024030000d200d60810090400510040c0c2d80001500340c003607400c0c06910251030891140200d5007060b8a01d010f030010490781c0c081040d200d0805211000407410440507007548804010208800e4510b070340413024119008030544540d400030303c00401c00f1031800c0d01d09800a4100d5001800301d51204da500c40c0007841d19203082d000005540d5104a98980e6400d1030b1500306c03c02d80202d4000c0541101740d0704041442401540920203540700310110107034595407002c0441c003608004010503042041c2c18205028400030340050f09442c0d400c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697198552 1250 697197302 697197329
    0x1302130929060901052d0105041d010f090b091803090904151512030c050c04060b0403060b010203030c160515090a030e060f220e010b04030b0604092a0b0301 69
    0xd40802103c060107801261080058198840b0604e000e803508081c9004505124080745d0350020044e41c05004e95803028201d1286604080501c0c20343d51031386816581518204400b46442d1000c081c02c4070783d013806040d044904071000c901c4010110104000c0c171510f26044138646048200824852482079a00310f40d1104001080d8184803aa0f0003203151f44a801b50300e580315a403611681c2c100b0780078211400350a001c50320301c3c605c080c0001032107107090001c0040c0085c00565629100400706038024403090f035400345081c10303000e2550301c04401ca9004002d1922494180010091080010f110710b440498243c410b00c60845079141c032400301140714035440b5000c3e102001c12814080c00c4d400940769001d1107820200a4480d0070302c942d00c1940e540c0c0080183d00c25001a07031004c5d4a0000c602c1c0d030820041e0742c403d0000040e101d1160310003041a030b403090710130342c0c80c0303458082c00e00040d141580002002d44802402998803504810f03d00d40e01c0014040d540786005170313200540030032a40207030040140c54804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697199802 1250 697198552 697198561
    0xa09090e0307020f2115250912080d0c050702150901120b0607050708101406030a03051308031c0c0f08010b0901140d050106090807060f2f070303081302130929 70
    0x140c0318020b0100d50200c80707d0445070780c011401804141c9a000b80f0030883c0c5200440c1041c80491810381d001c01885003c01c010f000c00c20480501242c0000b03030100d1180c40b0450351490203000d0340781691042001a12000280d860b0111a40061b144008115400c5401806480d0100340204000c8000f000110054034070f801108240c0020794a0030200c2c0d40100305800103212031a2400500b00d96541d805180042d22118103410302d81035016507510600340c0d0304c00455400d101c1d500204100002e0346a0503820842070360040415103058641c4540a0b01240040004000d02c20006009144d01107051501d00203c045c1070207000c100703400044140102503030340c80042c4003464008906101401408000b0200700d480c108000b01f41c07403561035000c0104041c400f050402100350451001803c80c1d0541200e0340744581c5450950380b00d4907480154000341d20140864005510880e040b0102074001d019480700c03101e460000070280141d810100c0382d251025210031750341803400b02c106003040c14020360b29815080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697201052 1250 697199802 697199821
    0x102030a0b090105030106050a1a04120b010e160f030b120102070b0406050f010b071101030902060a0f0201141509100e1920220b0a09090e0307020f2115 67
    0xb4160000d5000768034041e01031245642d40303480e00c2c08641e82807120a4070154118241c4001d801a50300c4980440030b00304d501d4041041900e006416298100e02510f20b994844030b540c40c42d040d890705201c001c584510030400c41740303110350400f510200d00500040c0e00c3d0003290058500320790154800b5203d1440080500080110300d02030030b9085409560052415418504e01140c144074280c0300504c600400025070410382d0081e00041c4025030010329094a6814200d4007516180590380f140005501e422804032408420019150141110841340c2c0e54400e43c190600a1100024001a00c040400003000450441e1083d40901c11201d0340061441c054580c1c4001d01501c1c40c42d103d092400145001181852180d0401d50740302c1e85401d00798188140e0b6280e182d07102801c440d0441248040000340c00c801c03240c0c0008060044446250701000400724506409403079014190000350300440c0181442880d142c0100e452036201c0382082100b0b202103004246a04d462001120207462008a4042001c4240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697202302 1250 697201052 697201069
    0x30c03040515040e0f040c1211040507020d050915090411040e070801031e08070f030203030114010e03031b0708030a0c02040f0e0a0b15130b0a170303060d03110102030a0b 75
    0x20803094060b040c68280390002c1000c5000400240414034460005814440380700401e41c02888c500e2961003c5200301d040c240001200103014500450034070000c134811610000d0302ca2060039607950741c2420a801803017000101082d022014001d92803c0c0100140c6540b1481280103852618010f9580c452804038000351041006080030248000c0000400126203084000d403801c41c42968440c030300750118030f041142405200c10141c0381c4030841a0706000c064000000f0344c1030303035034000412604c03003001401140c07603030321900400d6015007050007603000c5840000021100d58400e00182c2c0d59040e1038071205440d43d04a00c0209002071a5a072803141941040d2082e00c104042e0460103004101d80c98003510f607502c2e000b5000515030340d8560001465071003d01d003176803102180100806800c01f82900418007038070815018070704c2021088000141c03040047c5106403064003600180d801c5070380d8a4100841e03048040020740074008490214030085100380300552041c1c0088400003826940b80e414000d042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697203552 1250 697202302 697202329
    0x2130306110c0105100602030d150e150a090c05070f030e030f1621020f012f1203090706080601090902121911120a06090e0303071205040b2205030c030405 68
    0xc81e04117000c4c00301399400302c2114800300030a000850440f01d4521059598031442d44035080c0c0c0d50401c010300c1040140500d9819000c041100d010344901c3e107441e60a0101c8040811074004184100114000174401a031041c0d400da000b42003950350403030004086400d00d481000499041c8d0094250034851244101112003d00b07041b000001d10001e190f0700601140d00f0000010b4810414031244500680c0304403049449030030302a40701d031141000041d05a13006da6070010898003501912071044a0b00000a090328440c040403c01030409920304030060b10095000340c401307030410481440228202945000400e20506022450489403410010903000129101d0760b810103141001304549110300b1610a465220910700307110b000d00d888090341c0300020101d582c0a110801d00b000000c3c80e20800210146116108a4513404d044d031090ba038200d401c032001290024000b608000100c3c6a00102c58400c01d4000d6404240c40007030300c01e40e15034500e1900036540130070141e0710000c1c0a21aa003845a0307070f038405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697204802 1250 697203552 697203571
    0x315040506040510150509090c030d03150b250303020c1b0102011505030706030c120c0225031e06091407050111010519022506230f010902130306110c0105 68
    0x2080030410b44003c1a00c2e0500c0303050b20074948071000c88c0740c1800910002d084020001c040750380c1c100a6420203030260910034001844901c108074006140280c0c142110700b10900048a0324040502121365248034501d14420b5080582c00d10035040c0c8084204015580c0701c03040041c0880540c0c04130002420b5816441c000700c02003034100001c0000e51400140c0a00f611031310308011444e4116000203c4000f14010a000f5503d8100310340c041c00f080d00490001306101601212840358101c00d42c1242038044c030341c80014052441d47e4002d100340a91a50018880b503c50100400c1c02d1681d40c440d127002402450040420342c0050404019640e00103803485161841c140003807102d860400840368810380c8410400003100c0d000a40f504260003c5584407240740c03200000b2040101c114103140c1c1c000c040a0705448504c0e140c030001041120741180c100c9100782c21401c51102c840e03082c5503e0b040030b074000c90b190300c440d604a40390100019440d405521000c880c50452300352254581c101007803d40794050498803e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697206052 1250 697204802 697204811
    0x91e0b01170f0901140c040611061306150506120f06010309020d021513080313060903110d03030209060a021c03060f060f02030d05090c0a060302040602030d0b0315040506040510 78
    0x1c00d00140d02140d403102c40404034508030341d02c0c0340f825800760035042052880039140404003c0321084e8030003e0400e40b04103070780b00e90840802c3c40415a42d2142a6001402032140c610401c001030742c17940240c142641020710451150340e841e40804c3c901d4001d2080b84607120a07010401c00d01e0400755950b42d620400900c2e0520090f0b0780e980100c4d0100c004800e010703004940300306070920703894452001c031000c100c45180d182000d2a034590016440b0381202c14805c02c405a000c1000403a14130414610064a4004040480d03505090007000400d1840d54411010315809020020140e600c01000d00000c0700d050b0098959030403402c100304052188103406406141c0703812020b108600d151a40501940c3c2c4504001c200200d04100c03d0b45103015041c3c120080605180412811000201e507061580030b041c2c2c0c54030303251502d584040d030a9000758007924006900500448034030304440d820014100c07c0140c02e5810071924604070084200045a00344c4603548640c06204c10850b04101652110300260380402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697207302 1250 697206052 697206077
    0xc0e070c0506061e0f061608031014150307180f0806100e0103030f03020c030d0b1f23120109020306011803120503150a1e061d0613091e0b01 62
    0xe90102c5031a030358001c10702c41a20078171603100c1400b194108900441000e001c10010314010700310758030880701001100c0c1c051000080c500c0c803200d01c01034030300c030001c204e0b6104e8045134100401c82d0300000c2c05c0b01e0070081a07560750060310f4550074402020f007103040c45850104e030905201d585087d102400500580c043c002082080f00c800c1d10109054030383c0340ca031003103041403101012006400b500d4010741c0d15003c0024600f01c034000651001e5446001078070501c08010f40502c00210030360002c0c26041c04500004882701004600b0440071001000712140c1c582840702c540003011540c0000d030068140d4650020500c81650307002a2114038100031080344101940c2981da0700300340a01450400c406100000c404a00c50074440103100c515014003504440081d55134034001c102107481c50300c0c449400c030700e51600400c1540c4100b0701200c1c0000004400508001007000b07014544c0c3c44078050104035038440e0004184140180908002c01d0703111505003041c0004c624980f03040300d00113020a070600160721080b9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697208552 1250 697207302 697207339
    0x90702010c0929070206120f0a0b06030708060906120102130e010f03080f091513090506061612210506010201060905040b040303050402060d0c031a120709090c0e070c050606 76
    0x5482420340c0340e64984d100d000074030204049005401c0c0c4400ea0f4004d11080003100100d80080d6440341540c044140301100700c483c20700c581480256055800a05c841c40054030b24140a2505900084003600074840c041d8294007503130032078011030180000150200d408020b044100f0541c070380544408a01c0340d4002d40381d40e85400e014403503202c18204003400030a0501690b550464520748031080c0c6082c6554a6111088203184103070b19028080c9074614040105030181440020303102d081c03c58050005891045844680300704481c40800400c003e091500d160000026104082d030b101441d650210361070411500190a4030095004440a24903140800c0085990016440e070403540600b00000c0359211400410458400c37120708044c1941002203030390010394194400c00c1641c413521800e000000d028010014421040103554110780d0241d6428000c0c0e202d154040220544146d5060a216a548000c103020120441c0c2403000702c0e0081380342506009051102d5503000354100c1d001e0180c45010001d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697209802 1250 697208552 697208609
    0x10c0309060c0f0203250804090b031203330a080d080108120d0c02010908033907080c0703020301060b0705011527020903150402190e07030209030c090702010c09 71
    0x1403402013400310704104621b03c0c5200c0060301894000049641e02c42c1c0b00e07242030004c5d000c0345140034028824007007010348a00c032030707000e07240140011000c14030041c80c3d21040c3d068204250060030443e1440d194812899625000040c00510100700a0000c600d810301025140d024140e20042d5180c004c892048441d0944500700c502e0980041d90006000070668401ca0050071a00b10090003400008103001080c205030304088070740d14040423600030340146080c002d04050034503010715080c086c05000c079200040004000c0c00754440160121030206940e50006429186650312144643c5400203030b800912400b80200a114181440c04c040b88600d00b21101c036140c8210001902e000d01c081d01030a00541284d0119180743c50000c040f40e0320703091070400355143c1150594040f0b1140115503003030a0310451810402045540010149a0b1aa2a00c909030003960005c48415890b000d001501ca50b43c1c1c0c0c40604c001d000d00190340c0001204c000c0c00754050500c0b400c075045041e0300705c40001001b440d01703000d030360 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697211052 1250 697209802 697209817
    0x50706050715050411030a0302010617070e011a12010b03070809010c08010b030c0409110316020d120f0e03120906130c170c0d05010b030105160c120e03010c0309060c0f0203 76
    0x4001603a40e58a082c44500117501c3d480185d418010b01c2408414540c0c150884019600381e05101284540d030844800c0d500c0c5c03498030811034400c9481004202645507002d0640040344c000b68940e1810034200c0c04540b880a0907081030b030030503e011042c4400142e00000b400c0d400380c800c0f8001c1100780d544050241c44a0320503c1103c0d040f4500000040e003030400c070b000350340c02044102c2040c080381190403064107098200f195075002007805100440801d034800103d40500c0c0c84141ca03051a034641040000f0080d20720916403110a6403110141207242c40e00b00f0091101200105070440181054490725082c80c4000c1c0030000b0030445046c0300008900c41086410455401d1074a03000001d0000d07240c40c0c202242c1e2080e01c0d910031000300c1700c9814000190421914640110000c010310307514803a2000d080d00c8900342c00d600244583c2e0482000911080402e51080e40034207042c1d200c81d14400000782034501c02071041d40000d45800200082109a0041500140050404541520000c04c00a6480c0035090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697212302 1250 697211052 697211093
    0xa080606040504050c061615020a080c0a0215010303020604210228052508011527050c0409140f070c17030a02040303020f012d06120f0507060507 64
    0x1000f00b03080140420496858072000340000b9107a04414400040403d0007040540c0c10464606071140039105c10310071100c04d20390507183d030351071520340b03510b8482941c0041d62050203500c61525820b01c0030142c5a0b42500941c402e500500c0c4030300e81440d160401944004644030000c01d0390100035101900031410a031582c0300c11150643e044881c03801040c041790912405000c074050f4602c0d4a0003a010400d02d000e48032055040303110f11680e03a00c50142240c03000420141d41028220007071141c0140900d044105030502d04a00e031026010b81e0343c200c221a4192030144504a00290401031440207000e82281c1e078400e044082d0071490101c642400e008030040c003174003c220441d88500100503003180d2030340071134004062954981c544001c04500a500a0104ae005442081108800c04205004911883c083c0aa60714214243c1c0c1c40e038801c4c0e40d04d000d0100c03190282c481c2c0000c100440300800580240d0300030b10a40b07001e14402e04003241081044d4008100b0000d04000c050301182c03c02031140b405079181d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697213552 1250 697212302 697212311
    0xc020a02100c0f0614090f06011d131a0709060201090c0b071401090807140d020c06030c090301020d09110a060c08090a05030f010509190203070e0a02041203030606030b0a08060604 79
    0x3494244400c8080074001044989442c5e071110600c116541c0d51403094507030310215110310203d020b0613960b03544244648411002d100d106400b6044000c4100b54004a071880d01140e984001c1d03440c805070345600701e0a8044042c032101000291075004000400511203800204035502c8240c8a18029040e175000b008105080004c0a208200d2240800741004c54100000c02c86d0311000d2030249559406074a05035031041c08904080d03098840411503040700d844580003009404134040c18401d254000905201c10548144444990740d103080c0000c001015140e440000c0000c0140f504003981b141c1c040c0c070f480c05002e14900600c4a00c3d017041e24442050742051240362203203101740000d000d5511503003001e074142c042c101c1056141c0e541508118004c03028001541c01884040c007208219051408010f941a44a99030030070540c94081001604038008460151800fa01c402d409030b220340c100601280000e5844408104503941031040c03440600f01120807028903440c00002550360480542454842c0c2c1d0707103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697214802 1250 697213552 697213577
    0x20709060f2603070b0a051008100509030d11270a0317070c03110a0b0f070b0a06151706010801051f0e043227031c0b0102010c020a0210 60
    0x40030b000034101ca410203c03a0348070f5040c50081e000b02d000359410040a804c04022480388540c40c50900241c503885401426103410261118020740009020b04069000800074880c0741c02280c0a00c003403907100c0d041b1050f0342c0c0c0c0541c140038041c8801d140e864038a80c0c2103204144855668108100112500044408031070052861114241d1107101c0300207007800001300c40002041104025041c022600710703010615030f42d036030380e04019910940b284203109102c1080440c00140020401d01e4000b4900d17440000c64544424180050a1003a6001300114211440020a9000e00c446666000710300b8a03001e4299450306011464410a0766003202c14bd1422018009140c1c0c0305643c0d21480f05e4009005002c00e0185c1c1146041483d541c01c10301038040841c07070781059400a80c50003540103003042002808040d035914815401118040300c2180d190104100c0c4244c50b000302c1c440303181110304d15000003078010034034400642140c0d91360040c0029500120300a1000d656291140b501c41486410b041c1d80c07602c2e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697216052 1250 697214802 697214849
    0x60f060f010804140316020120190606030c090b0a06021504030c03020f160515070c030f0f05030a1d030a020a060f050c0109050606030c0607150216060e0d020709060f 73
    0x70141449803d174800807030400c4520a5241c01144218000c2c3c0350f5014040100300b05451282c0c0c442c82c0c002480e40072440800a90100d0483c802495018075000102c2c540c6942d6440c9400e10307181d004181054a92a4140c03503440e060354008000c003030714002402e0000c0614404104100000c00203414482415024803c2c14024881d2200803424042070f5034084038650340882c5214200d0003024001c0c1c08156460200c034074207108451880b6088010300a15a255a40703400c40849061000c4800742641100000041c1e010409000c203020b4580f075018031804101e6140545507454040c492003a40814800c00250315040552000d5172950310307102280d0003000d18282e81c0c6116030564030515610b48a0342105101011a0050180c0821000d076400364508000f04074090040c0000503040c400301e03c05010243c41c0b164010100404995104510303c8519280d940407640326400d00c01c602d030085400d51600302d03418015030025180301740b402c1000c2030500130280395840c61030248805201b21000d141d0310045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697217302 1250 697216052 697216073
    0xe01030b10020d0807230c1203010603021e0403030c1112031303050f010203011a031506030c03040308160215062422060503041b0305010e030a02060f060f010804 71
    0x48015140d80325400ea00a4002e643e42c424a4515000901907404500b00038403030850b100c0007070070300344021488030221381d9141695440888540d030188642c01c00300721150704007070145008000544006803603041d516048a00440003020180180300100403d00003c1e40248429044581006140d03000742d0442d8040f40c0c07280c1e206008182c0500c00030410381ca250540f400c6440c03d903072190059401c0d01603c0100b0724281e000a018140009418200c0c0c02c08044000300a15481140d000c0e403d1a40410748c00402c825a0082d94505c218010000401042c1604030000d00d4120301c1c200c2c010b041d112010000213403201e00c041207500412a194000c1081540ea44125900900304c0032400c40c100c03032001101c0a5150b10030180061603814690740d09401654020303202c002c407411915000d1031550350f40e9802d114488450104180700032050f01c0800410400d1007520a4494100002d59860522030b2000e49003100040001c80e052000c0c100708003042c0c6a00104d0002c0d500c1c2820315a0007030f02e80c0e02d840d000c0794 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697218552 1250 697217302 697217321
    0x60f091503020d290a08060f0402061c020706090b39190f021209010504091e09051f091101261e180d050d0e1504060b0904050a02010e0103 61
    0xc0085003a208402100303503140ea00340350022160140483d46c5e801000d0744440c0101d500000440380c2000190150902c00000e01039086151741c01c0c5800403034071041600b2604802c03020b9800d5640c13207105c031041040113940607421001040417051851181000008008104801d05184610607125a14602034060035a4200a00b0425403218400c1e050402000c45001060f02c40052168210042c0900b881c00110380106038103035200d907c7d150415851801030070640402050408001d0f0080000e099540700c3d00041d00e100d0f001a001a0910400c0c0c1429003181784944681c441c980020000010200307050850711540030b0918920180d910014a022400c5003c03c20f14900d22110400c03840c1c2c00c0707141610361543d03000e88103006d107500d8081214003441000d4540c406650300c40d1046c054031a0103038010f8161200c4040b0003103017031020b0000f0f031801c041c4181e14041e0f2480030007042c001004001d00500c6a000003d89a002c0c83d4907043e201d10350344001404002c0e0502148003c2942c45912036040248003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697219802 1250 697218552 697218581
    0x915040b0a09020d05010609030515060a0503060f010e06031f110403080316030f0b1c08160c0503010c03020a0f030f0207081902010c02010b28091401060f091503020d 73
    0x66940c1c0e40302d10010390f0041c410140501d1424001050070340c0201081c60589400c0802016070a520024440c403509001e0704080e407000c083c1d80000784e0756400304074052203200b111443c0f030411351400e00c003036a03508030143c1307064401c0e000b4000c003056a0b03c40c4140c1e4070040c1d00d415000306a0f2030400c20070301071034411900080c0c980c074800400c10400509401003da5542103658041003400040e840b200200c600d0f201070b0b2544903a0140200c0c20b00c03024500c420308040e01644074107240800c0000481354200c01381004070f03a00c10300c00008002d1403500b0311138003128043c00d042c250320341301c442e00c80244240009a40d0f18207140c1d030f600040da003a00a56060303401d8268007207a006c1d5141c01c1c20941c4442030101030744510040d801e000003140a6841030082940303158028041c104024803401007144002c2120180001c17062007104000307891141400743d000c0c0340100d603120300c1c1c8950420100602c1024183c90620034007800010030001d001181400e0100b03961145001a121405d02d078440f0042e0803818241c020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697221052 1250 697219802 697219819
    0xc040b040b1c050c0d020a03062301030e030304030c0813080a0b150d0c1211030102220f0b12250203130e0411060c0a1403040914060915040b 62
    0x16900941e01c002d0011291150341000d04040e4400260141e0b6011110213940b101e09000c801500c40c0d5030340203446546e80e941000b08059071143d250642c00c2421211030380745425101e9400781b00c3d581500ca0320040d0340b01e00028518524041d103014011020508008101200006640c1c98502217140c009001d07050703070300603900860114101000c1c0c2c944180e0781c0416000c181400c0c40b00615000340d010007060381c40a000001c552901110204130740141500392000c14000010700303100d81e4203200600050ba05100001c007203180c01070b5049051201c0340c00c0907501c89032002d824882c88680c03078203a9007000d807507801c041c1d80e40d80c40700c0740c0030038140403078803010041c121948078114a40d4003c400780083e1400154090701d86540c80350300b03030b02e00442543c01410764408008070a4103414540010001700d00890211071100325140e88004240d0360601020f40303d904041828096041640107485814501c0412140319040c500006080301c40090514811a04286010601c03034445801105030b41c42c00400224 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697222302 1250 697221052 697221059
    0x40219030302030a0e0613050111011812030b090c030402040c0509030a0506010e13030503010e04081e07020f060322171b07050114031f18090510050912030c040b04 72
    0x295244c100c9418440403440288181886042c0102074510518424021a00700d03407600380150f81c080e24004144081c2e54a031030382242c20b03401120701480058803403003140b2040341000c1e400904407070725100d00910030100ca0062007101e17044401501d0b009070301101c2c001418100e1840c299024410030100c01c0d09806902c2d98041805000304005040b918107a103c0c110f00d5a0b07081c05030683e83c05164004005c50024001401444198a0050b9019110b00601480c182103c1e0460030200c40f0103583c01c088200c0042c00200314100084c004103040010f503059801d5040c025446408640c550b00d6100040071020340d902e092040102c14034912441114905640321403e50755204d4260260032412030520420b01c00048951051590a810310b220744201c0d415074a840c0994a4001701007094182030580500f030114407480380310960840e4207103200000031644060301d801e43c145102140f2402e2101d142a040105044c0007150180c1c140040b10500341e506e5690003c104094015a000750341c0e441d00110707020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697223552 1250 697222302 697222307
    0x50409032307170a030605100c06110403050106081609020301030b04060c02120a09060e190e0705040f0609180606080703090318081509011a0d03030f0924090215030402190303 77
    0x52940040c5503070184151515501885003904100441d031000031340c1e10603052702007502c80c1c0c058104141002e1000303240030750342e885039801e54582d80c1040724640c00c003003c4004d1100e0f1203080c603001040a61825400c56145468400883d00010005805030b03456000f5249005d1081c0140910210001c025584440c1c00713200c01044d068480c001c0b0000305001100030b542528013802e04842450224804007100f0f030070603a405183c030401424240c2480742c01d03c4085124190005001c0c00381c00240d0700d50810130729155080400750358050b0012507603843c000d418060654005c4005a0058840c02c1c00b14064040d403074103d5901e044480c1401e03007a03600340404a04001c0c0440c602c94600807403a001c451380d0f19071800316802c0b544036290403841081301141413281410703c5103401c01d06134064280000c44c00f0403851081c3c02d03a02c00c481d0489101c1c510300540c4022450180920308409003d001c02c018081c80c07a4081000075000300d10300340c44c00300080001070440d550604c04001c070400c0c4a6030400700543e87d1402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697224802 1250 697223552 697223557
    0x2030a080c0102071a15010201112a0a0303020d1a0102070e13020301050a0204151d0f120105250c0503090d0816150b042c1e0c090105040903230717 65
    0x1401b0343d079030540711021100d42c814000d0301011041d8202c031038035000707a0403414111407600e4850310f00300300c150f14911080d0307074000c2c450004810301a86025942d012011a070308102c5002e41c01000100d5182d5000c04043e0740c3c0018044140c628100800b0080d445040030360642c480031050007540740d800c040c03c010002100d13402403c11188141c42e01e0968500241041d51116440d80078000140300a0040751402d1919540c030940800019001d8205a43c11139505400e440049404070030340c5045010290000450300401c02d4050700510b001100401c0720f03603840e82c492040c003641c1881030440240210a0006c15012118407800c81d000e4944241c116281c003102c950420050030858919140c0c120718141000e01603450b01c1d01080502c1c3c60201d081030035413810402e520280c10300a00c2800c4004880c0203040f60704060b0500104020442041c03107404000c00d2001c160029401981090140310000e90400480718108c020b203e2640c000500e2001030030b0542c00380901c061b21040c3c24185e52035a10794041e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697226052 1250 697224802 697224811
    0xf0f0c16200d0807111c0506100f0807060815060406021f05040b01260d090e0a0e0c0d1a0408070605070807021905120705030415090302030a080c0102071a 68
    0x1032100460140004100b00c0015554000c3c0500d4001c01c002e40005614070031a05080400403e07540b038040440c0c2c0c00150500365200700700c4840d8070180500842002c82011a00146250000000c02c5401d184260b500c5003c1842850f05000d09540401ca8401c504840200313110405801e9070f80f22595090000d6556144251246068140b0020004c0000150050714811078200d031400000da46800320320918a404981059025101d030900c03d41108418001c19110302d96598465240380d04000b80c0d02d1401c040500500350940c5443c45013507041101090300111920200c1d182865661a030600300241e00c084210a2820040f070b408000070001c01074054034080b401007030304001c0307696521400d4801c05001d540c29409644100d400300c9518610440e00c042852158083d16000050b11401260075041440c00312441d410204050080c00ea011440e00b4500c403076860b1804035180b070344d000319440d41f81100014082274800916540385440035011580c040313601400102c0e122148440003901042c043d039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697227302 1250 697226052 697226093
    0x25080a030221040b0708070212060c041703091509063702241801050c030a0c02240406290406060f0504140a050d030e1005030f0f0c16 59
    0x100d4a01c0c400c81c2ca0000d407416640c81e54030703140c5070401036259405150440d250032640401d03c1d03201051207000900c6160302034040c81d030074161510b041005402601d40d6246030307418264810301025610395945000782d4051521580c8059580322680d010a2141c402d002d80d150040740a004c810240f200030414030a84481422080510ba82d4010000c0b41c881c903c0b00744460543c80a07049410010100184090304032801c0c01602007844400b0080e507007501c104072040e0ba9264404010041e00c2c034181d00901100d10000e02c05000404083d488080041c40050804081c1aa102c0001b07410098070307a0155182c4c240030b07060403240c0742184500c4005c2074004c03079040c0c0c002c9051100015003203000d03c01c2e0300280d6500da11020300309400e2040d107e003100d4410309100d900072003c07000010039850b0742031a83c244c10f000c1e55400d00100b84072014403584101d030403d4042002000c000300900010100c4d80240c00c1184141142d2107521000c11400c418004c034041441c0c01c84040243c541000000d5043c003290b82d6004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697228552 1250 697227302 697227343
    0x190303020c0d1112030408010f02071b0f0605030406060918050715020304050607080708040f1a040e060607020406050307230d0c030b0406020d051005030f010c0225080a0302 76
    0x40342845900509502c0c0140000020300001c00e5901c0c02000f45140a02c66804a80c1480d40d0380018500b511020301d9025103e0741e00041000134081003000700d0001c0000100f9428059150102c00c4403150644d1003040208031000c00440d04104140c2c1058000b007242c0141805015074101c102c50b043c441800c0212102c0c4181c3c540040d0108890f120030100700c0c40d64001e9805c1c1071400d030a00c56143d0100c902102d40c1c12040120500007200e0313402400203405203800b031442a509220a500d41c0e16400044240f00b100140010404682d03420005944070342c09850301d90300c0d010b90b0b20114024040075042039602d4007441202103118000d15509150100b0071080380d507004601c3c1014013070b108000302000380c04c0d4040c5820520100710720131030b20b68009104072001031801241c548002c00315a0160341c4010580c41c00b060410847ca0100b020715818000c18008011549401b00041e41c0c885a4804e9289120f519a031000c0084180c0464040188018005d50300488901d240007912403404810400c480181c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697229802 1250 697228552 697228573
    0x608070e0405070806060c03190903030f020613061a0306011410080906070804080d050403180801021809310b010f03080a0503150d0501090314120606090f19030302 72
    0x20b40107550040700180c841c080380c0d03140c1405100580e40090301456817484100031100d040540310b01c00690542c40d541d03800d0030080c02c51800408106403024860b0841d4132000500c41c9041082c4003a4880c01d51001d030018241c50045801405a0340401c0e90f1941801110000202895246c495200070719044a5211003422070341d00986071707000c00341d43e0201c1903402000001c0845004500181e0010300802c1514100701d020b1000c102030b540215401c4002602c4500c80303a10041c0466040f0000d019000002e5040101d012200700c4034450001d0040e1168800d40082001c41c185400240f10b454040b032006030490f041d5000c000300300c002c4181c04540d80203a140002684401d402000c0080d21381c420341840c6041100700007250590005040d8255404100c10b085406076543c10a14a500c0c5c402c60021515a80a08002c1d1078443c1516101100c400304012114161b24451043c40d4002c81c21a000c0e0340340d000d00d00200e005d5080300502c0c16000403044180d5071314520747d09503040c205c0b4031070340c22a2464403a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697231052 1250 697229802 697229809
    0x501030f020f04050d0614100306060609080c010e06090a0f03260f091f080712060f061d062718040f020d080417010e0c01020d080a150608070e 63
    0x140b10740c462160102800140038078a00060780b03030540c07801001c0102c1c410360802c0399840728030000e944041d01144528001c004000700e034028000140707460708140034114a001025921031481d08136050400c00440e04510071a5540030544c1d040c448061301c000780741601c1d5140010705e800203000a40d20304280500d2642d0301703001e001960151500401240c1d05000702d02c000e03104103400c8881c14135402100c90030811120038080404414004da03075501c0e00702c036091158010b04004501c0580040150a00d10b09110812503400c210003129034a203003020f4900016a038441400313486922030356220030b00280d0300300e800f030b80d80080c03100c02d042118164903804401000c102601d68480c40ca0340360800d20500140214100c00403131411f150000d041c0013008451560b640645a10503000404500600041640c1418091103440d008a40150003400c3c2000380c0c00c0007070364407861043c202c2c00300a80c0c20001107525006405c402641e02e000e460400d9500e444510141c00281c0849009001078041521030f80747c2d14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697232302 1250 697231052 697231057
    0x8160c0906030218060307050111010603080a0302070308100b09060a03021e1308010b090103020907021e01020301090627050c0f04030c06080a09020a03110d0b01030b090f071a07021c06060501030f02 87
    0x45d402001000e5051810005441002ca15000d9841c295030b01c080010124200c80000c4c4404a1181c0d0700690b10703c1946406062400054013001c014800e4000c00c0c000d159882041b00d281d5002150b44030f490b41d2840504030041e104503500c2501044041c1c0c01800e40441c1c840c050404581c290074910383d010344a10005080301c40303034041e050307010b010540100302605001a065030401003901c1510907010103812041445000c0080c0929240e600100400941c1100e1080401804001303808120326000e440d21115061070000007100318a60329000316039101212000c550108800800c00b0b501c071b554909001c00030510507c100d4002c5005140007039410040d5108404030154010030780b6800e5400d507214451984040c4104940090100b1420345c0442d4000003403500a52289201c40858503203c81c1c01070404c0071403a064621548041d00034002d41282d40810707503441d00da40c070f03410345c07a50042d000003140c450390400003e1048844c05083c509000c010740000040e20000c0c1c03002d21070b10407862000022072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697233552 1250 697232302 697232311
    0xa06050906280902030d08150102121207030b18070206061f0c08090406170d0e030a03030506030a0b04050d031104050f0915062d12010308160c0906030218 68
    0x10300450051210728001c04101c2c0c804084040002506003804d5010900d0229800e0320078010035a020200b2609090700740c100348034100203201801480110111540c00c600840c1131424403620010001680d82c0d220340c0c010030313585400a000d000c91070025640450300c4001900c0c0c2800502402002a2b2a81420701861a265082e20110030580c120000100d8555030415011100c0100400810441e03980b07034022007025140c0114142c18540e0715035011fa02c0d104c3d50b840c0303810a21992602d41a001e0740c02107291000701d501802c0201d519610840001c0c02d0200b174003001000d0015110078070051040004034010038100d103890400019549030304501c882d015512410350b000c0001014690541003002c403560b040b0f62031450700d10100e104900050007581001162890920081e10340901c24200c2e800c1f012501105d02e40c05604c2e1480d03100810348201d03014003000d4069000083c80000301003019110005803904150b42c4110b440d03c039045607002d01818030060340708507907040401090a0b4a0038105008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697234802 1250 697233552 697233571
    0x390b01060305191e0e0102090f04110906070c080a0b040b060a05091609170303070906080402030a02120a0605180f010509100e240105010318410a06050906 68
    0x2542d542d024048041c007910120400c9681e41c20034119101c010074041c00c100c1700b560800150302c03500300d101408404070f0101b01c0740f0301c92801d255102000819010071a81105401e8900999848207420110f11403606980074140c04d20460f15054280111101c0c00d6000307611030601001962500400c001300051940616607011000c00c02141b0807a148044400640b130700fa041509155990703041e0301603d14000445003549800004c03c1000a56000f0001c102416090030468500c1c01c0c943c0109545030317140b800080c040c1c0c60599014500480401018100310740c8410140105d180080c2009c10466031001c18002d644200501f469252606001d843c1c4603034003002c000c000d00304007a10b03420003402a10340c0380304250042d00000c0110179540582d4109501d031595446005500d010001011942d8503e52035514004c0e851050000485640c02d4a500880122440100044d01c1d8803458a40c0050b00010001c04040c02940f200e000340800d0254030980103210400099848480b101d40300c940c1101c807201c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697236052 1250 697234802 697234831
    0x1e0e04050f070f08060109120b0411011b1b05040e07060909020a02060a18080712120902010c1212020c061902040342021e0910390b01060305 62
    0x492113035403995485001450400b103ea80d44e10110840400c03e207a00380d1f10084580200020f0007514008081c2006003842c01491410300002d0000c06030b007421100400b0400300c060214103a2118901240103000005e200f0060000007800c6d26543d440c0c07030312403400410b564a40c0004c0701c0c90148280c0340700a4198010f40351a0341c0c0e020742e18004001c070b6002d404460865003406004210744501400c040340c0304c1c010f1300c1d5521843d014084c1100510104c44240700741007007000d80050f60305c52203544242d42e002100c612918101042903444c68051040440028408a0020780105000803014001d07091412034000719102d0750403003c1039224602010301812000d01c1c500b070541000d68950030f0b410804298442d0300d690080c410840c40e41c0450307060909070b034000c43d00207501038014021101580300e101400345000321400c04107071000940407000090080c0d606c0310180d8001e49141c1d00d0280551071281e400031000c001043c3e8001d0301c28850035940413154000100b0828040e209003406140310103030301d21 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697237302 1250 697236052 697236077
    0xc0d02120d05220c0303020609031908060307080f010b130b100503180a061a09190f02120a0606090e1902031806010b0306031002031003121e0e04050f07 67
    0x2000b4050181241110101181d031142c0f825800e00f5154a44502c5015030721010344c1307141002460484041e1188000303810130480070b502c90b000340c0284205090103060003d00c1d543c4941c0042d040144541c0201c105000740012540d007a44194804030012004451004864001d042d846084880008500340c01c402034440c000d0085002d10061a40304c0211000000c1007140c01110301d05203070240100300d614035282c18551074006480c903c908801903081d20a6043c51411124100c1c840180091070013000365507142c000400d0032181c0440b4581c1c07001030000c000da401d041006200402140c800c5000180400780e012948200c562a9603001d409148680403190101780110030003540090440b42c6104544000400300c0d480030701000c2e0081017012300c015100e00d401130906041c5455044010192441041004042044891081c090300d80181040c260405105015122401d18208040340203a00401e003c8025a0003420590303402000d60701409580c1301c04401e0012010140e8080c80031070001c1c80c840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697238552 1250 697237302 697237327
    0x1e030809010509030723090601050310090c110a12090807060906031112041103010e0d081303110313090b0604030b060d08190507061508100507050415050c0d0212 71
    0x10f00c081c90300101501c01855a80c0c0d00f10004014413902c1c08912031881016803041d1501c80140c40c1d1203e020f00700742c0d2461900c42c46418032041a402030003542c4d0741c1c4508110800d403144e20850076192055045440528950034102600f000003034000d80010350088001c18080e0001c1001012900310791100e0360101c0c14031310141d028024410300341804000c14401a002e42015500090159002d4181080710005801c249400d44103809080e10f001c1d03000c1100030728a25405401c255000350b940401c0380001c0c042d440c0440789080c003100c5824a03807002080e40c00540041000040c00c98000c4d51003082440640d805200742409140720281c101c002580c00135030541040651402d1082c81844c403e4a411003084286e59000321004030301001034000705003901000614490384819041c0c1110000f0800c2c58100d0103940c900c041c6646262164444020605d114001d40a03100500940320064031070b40758800b4000c0590304408a800d030f5a201c6d6150f1180c4203800428940035001c0c00f64085881c01d082034100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697239802 1250 697238552 697238557
    0x50a0b071502130611060601030608070b1804090b070e0102070b030109021c02160201121107170d0c05032712160203010c03050105030714030c371e0308090105 70
    0x40d110407030303002c02880059200280c07008010b019540c036142c900514041c0b40a140980040919052500c1c100c406e22020000007000805c4400414009640b254501c10445001000c03060081c0c1140c14402814200316601400314460390386075803031210031510a001280c2d20314075841a9080242d0410041c000e17052a0b400401c0911040d14400d0303038582038031103150b0490344001032908103002d00d440c11604540e0b101d2001203c601a08000303100321030790080380c01417030b2280b22001456084140641049a440c1c0c005498410b114441d0401c0944a809006441a401107901013030004074091007040200507490b4030300035064290014002c4000074209212030744c2c401e0b0352201d504100034401d000160b6007401380000224072584c020a95500d032034141842d01c4555040704544240b08500c03107c00b602c3c0024544a41c440482e800750003043c42412001d16080d14034420356410300c201e80c00d07091f032004c52400c10045403000c2320300c401048008160343c1101c003142d0000a0101c1810448284c0e950f102c2c801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697241052 1250 697239802 697239833
    0x21b09060d0f110301061a040506220f050f01110d0f0c050f16080f0a0201030b0d2a230405040311030a020a02043603031b050c07050a0b07 61
    0x2200440703010360321108107142d10220215990000080032251a04003805004000c04890115500704029a54640c0e124040da0003110f020316000300b0800e04201d1503ca18501c142a00d140c16040e80707840d02e203082d003015070501501c1e0140031029894461944518030390b00c0303a507403070201a03d00314100324003c4030b00207014070350300b01001008121381c00850302c01c1c06500d4003c40c91744001c00e00e0514035800150360600a03401407105e80c00c0401c1d54400100082a20001c0660903e0000f0716820303c0e4001480503415400d001c2c0105106010743c9450003c0c42e600149072004500201d03034142e0351805030f640d040e98158544195200300445038065420305030003203074100d0311900341a045c0da66100b0707002d03286811035103041c4010b0b4480021041941810f02c20f01d460700d401c10040e603011a840140e0007000ca011450280301d0080711710140002c0c14070a0340000c00e045038180c0107a04200c11484000d007035030040803a0400c24014060f00080c58900b05481c0c8048405504050342490802d4583e2002c0ca0b03813000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697242302 1250 697241052 697241059
    0x90b1e061c020f0d1407090806010608040501060f08030d140601020a02130207020d03020d140a090506130e070905030105090c09070c05070b0d0603030e0d08160303140a050115021b0906 81
    0x4120b00b82e03c0003100260500007a41a0006070b903031040100760140c03580151884046c80507445081c0300ca00004a802415114541020b2619458074a000c80c0109010341c040c030305100c00c40001081658000c0010200c080e01070505001d5030005440c492020702044c0d6505026070701008800005003015a010780046002c2d070780042c100080c50300030400c000c0c10300c0000c80060f004a0784000700650403000c2405103601d03003200035007400d4a441015100085a0150500c44d0001003202070324460b4140d0a54050606107240c00803500f00040c01038203c42150003000d02c01e50a082c0055100240011032402000c3c000b4280700c83c03900d5105003a907124004003403c1e642030203801c00110300b25110380c1c0184101001204009001d0380703142001420981c8004c0c1c03ca1242d140c072482e500100ea107000039a00c03420051140403010300100d00d000d50080500b4a106c55130751201c00c040000740703456644220f048a4030220a1000394042030400c0b03880e5440c04100824280c424040d4a446080c01880e10741e004d48040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697243552 1250 697242302 697242307
    0x1404230a0902130f020901021018110d060f1e090c091104092306040510091a090a09060e030a05030408092715010c08030c09030115090b1e061c02 64
    0x4520f01d001303540d0300c035030181c1046800180b0031401c0e5034100150b102c820045141001070704005000d04100144141019000612403081124a03558000b601480d5651080c030803c050310313131024480081d02440c01e10b07182960b102e5a030041008094041c0350f88055100301c200030100c0c10300d0541c0740241505540c105000405100c00f1440c00594490400e244070501d00311401c22450002d036400c07158000b400a07010714103090a01000c0401c003000c1b02d0669101403404101c11080008020001207180502580030300c4031014808180d07203540c485050b00303000d600284440c0302c0c501c0c0c0566030b91107100448400901304000043c00f050646001d000341020050440b1001c00104e00c45130010100c1d1201d8110703d11081091202402c000038090820003c28240402540340b9274403440114000144940a207900014441c11166002c2d0300c000000040c9150707420500d501e900781840140341a04041d4004e2611000301e21030103044031900c1b80d25a0000b1304140c0750030f0704003c1030441100c15018081605409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697244802 1250 697243552 697243579
    0x6150a1a19020c0310200c0a02010806042c01060e0609070f05070803070e040b0301111206270702070603020f04050105070312020429070c0317131404230a0902 70
    0xa101910646030b070450301050f10070340748842c0c29140600d01c4081c006d40500704400600400c011071106061502428425101d5480750b0100700600020800055421080000215085030b02070004000c0d41000e002080080d4031080c1c2c10344942002d5a0031540140b0398030000702e01500c07540c82d29025035030703603d461410002c43e41d641080503007041d1400b10108242d800440e4080c10a07100b42c42101c00c0c220024040281442c0350039030544504d01c014901e43c002c5000050171601ca482c011b0f100071014100b0070301c0e020429600e10308140720555004005004210000031000e00c00c0c0291444990f0f60725400d0303c0c16140034010340c0d05501c5108100e0a1143d2070f0190f0400c0381c61403000d80010a0700840c201c021390516015841032400200c003010000c132050000d00f020800201210099a5000c40b48003c15078441c0c15020550103060b02d00424036100361004a1703c00341280b40071030740726030030ba60600881c10030307100c0b503071036035002d8410f00449050300c80c000340a4007400c0d003000031014009440780800589 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697246052 1250 697244802 697244809
    0xf1e0621020c120702040c0305160324031b080c0108010b07140a080a09080114060609060d0c2a21030603020a0e01060f110307111206150a1a19020c 65
    0xf02c0c5200e9030781d080001c82e066041d0b041502664450304901d2030308000d1480d0102690481c2e0b44603041d8001010307a550740e40c1d40141d01101c4007400682c480009820038a640703161040e011044010261240d101c4e030400020b40d10000614140300e82416100c8510583c240380d04a40b440e008000291841d0918101d0b602c000c0805001c26514140540340c2595594030b100700151805810764010b842d0342e0f14000d501c0751071420141c1219000340342140c610f0351754803a6500141d040d008511480c4589071401103007844d1150015030208150032031080c1624200100c0b503601c52741040d40800900451101024281a050628410740c8800502c0c1000a04940c50380c001c07518009090700950f0701900c0c481d005001458000c0d40242030035401e40b0380500e503102e491902ca07480c3d001e0f100f001440c84001c50314000c0640d891007000707e41c20f00c14100311105443c11f41440e40c078109a440c0c03018001c0c0c03181c00010403a2110310300c0502d856012940554030303102c121405810a201d0540292085020b070f08201c20190b035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697247302 1250 697246052 697246063
    0x120c0d0e06062b1211070b0405031507050a18080a05030408060c040807150504031a0609091c0e0d060e06181504060b041103010f1e0621020c 62
    0x10000c90040c0030614100c8140200b042241500300628030700030078010082e1504601c08041035600604464440d20001d00540790724a81c0401c544081c042c14601050911420014208840089049423443d045100804545050035580f100001d5000c100342c0311140d001d001c050202030060701550b00025a45c0e00c0c0d080c240031560400702c8154200040801c160b1104008941d0854602822181303014070b0a0880c5d17a07501d600d8410000c5850b0b0054020110134043e005840056401c403401c40d0440d039040c1303112824110216010740c0301e04d0108022640c2c10100042c1d00404409040d03414800d034241280c243c520b040c108880b07650000d0008150000654907008800c1074100810040843d4105200142d141a6207807420758110390215110743c0b004030042d400340d50025006a00081c030340c5000004680508406950741c203400314000f0000895221a4202a04580080398854968003280c0940701c841c2d8082d20807a00041c0041071081002801504d009825003110500146030210488172070b800c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697248552 1250 697247302 697247321
    0xb03241215060306060901120302160929090604090c1d06010906081b090607060e071a030105132a02010605090109050f070305060301020904110d150b120c0d 69
    0x750881500500c295014400a64001e1000c0300509098500507010408031001481004440b010f550300300024140284440b0202c445590545418540c40d03091030005800c0301000300c4209800760710701c1c0703a20803c0b44108da8503840e00100303491110b46910003000040e2240100c00e0b2044e4240107800034103140c0031910007900001504202242e85410300001d4080b0280383d0055061121103c10014125200701221408141e5140701c03a49400b0001c002c10490b01929000404044c074000740034100d844d001500c003040f42c4401643c4503c1103249126107040d03000c280304240e0003036005603010342c0b200b6450300305540d03511406031f06d80300b040c101600c450991900c140d034845c0035035503543d07086c0401d003840c017105400351140c1c9070140860f08101100c03880400c4001d203040205682c50300800d000b07075801c0d01202d40b8458020700520010351100c06850142d840092200c1c1c402e0f15080c901031558500f892104c0440b10b0780441c482c20200c1500388907803c040001d000492481c0c013000302d280143d001c2e125540c40d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697249802 1250 697248552 697248589
    0x30e1203030f060f0a14041808031003050d03021e0f1e03010e13020d0b0403021c1101050a06060804170f03012306090f060d06030507170c06040b0324 66
    0xf81071850030f01140d0b100c01c08040e40036a840c04803e0081c549200d0251001d500e0544000031032916106102186400c6000014070f003203400030a1254480081400300240e034055800e8a51002481c8801d908078814000300040c885e000d1f298400040c40c071200580032109407000c02c6841c2025800700390340020740c19109800d07602004001406000d0951220546c82082200c00107458400e64000034801d0100f86030017000c11414100083c01c040c82401628118040e455081380317584c5030394001a183c100780c04d0114034158a000c2c001141180f06014581c121203e03900c0c0d8003060741301d5485225001d520855442d5082c2410001302c244600060004c600230720410020100c10080c0070000b5403154243c0038801d00c00e100c14041d02540f0798800000b070365120000c07503526594144850300e507805840541d0000c1c0003401a1403000410148004015030070100d940c00361008843c40804004c1240128013a09040200c240002449400080c0c048007140d6000646c402c645400040003804034a03003a25114103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697251052 1250 697249802 697249831
    0xa17090d0c0603060905060d0b0a06051002010e0610030c15051c0b09060a031101120902030f0a0c08060c09010309140109121d0303030f040f06050c0403150e0a030e120303 75
    0x2080358507110300c0303000e402d140c0818000c81c18041e002484d180c040e488c001e05855016008140c00c9900b680c0030030010000640301d2001c070240305074040e0007002180c925003118011000018070140c003110719034041e02d500542e5007103194103069240e403090b03c6242808040c403c081000414003a052102c15091042c464070204082d00554144524048041c041a026060a000900c002030000c2049085940d0a190a6800200000a100203000c03802e4029415014001801c018240c01044007143d203402007031040d0040780e071014450380d00c02c0d04842060a0050501400d542036100f038012448040c021601c1913014040c0c072401d00d00b110b0145c0c0c812240b029606504c0221340e50407007585a00102030013400a00803003000040780c0c0300c1c803004241c3c810740d51032180010200010031101247c0c0ca41c010f0420012490280e040ca803055000d0b0005968504440b08032409030030a60041181d90100100680b405440c580d030140c5030301d080c00304140e030301914200070410003032405c10203544280c201400c1040e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697252302 1250 697251052 697251059
    0xe0a0b2a030916061d040b130f0b0f01050a02071401170702160501020a0305041a04030f03030507030b04020306030a030e06040911041a0408070b0c0304170606011e020a17090d0c 78
    0x1030742d111aa1300100c1884507100c03180f0000d0302c0c040c2d44030506030019100407686600f404000307440c602d990401c007500545841c2d6820140809544580402d450a858610300610b40e0001542c050146110030700c010b9100500c01d0081c8002440d214030004018100301c4000c05041c528943c469104881802c01a0f01810720745140405091203e07000786000c0c0003521100351203440040542c4901d002d00001da01c4050400f0600500c0c003170807078006640082841d003d0317020a00d0000c002d41400e4400d100000d0814480c1c00491170144200c90040000400502c448900c0e41d0301559100324007001d4650042d4148400a4000414010403018800e1600c07080e5546003406101008660000b408242040c0c00380010300040d000050300e1302c1070756070410f04107445170f0a4040b06072a40c443e68214107074059a00c28070000d651030000b6114000c0c602600c445000c1015100051000010914400d0060740903445260215401c00880440d10a0210401e483c00c084a001319080540200080316044000d40080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697253552 1250 697252302 697252333
    0x1d031207060c300b1309020a061b0311030d1b021005010b0306040507020114011e1a0a1d04140604050906040237060806030f01020a0e060a0c0b18010e0a0b2a0309 71
    0x100050109d80c10100c4810000701c50040701c034841c20000400340804a2011070002400f00700703459500c84680c40c244481d412440344d030203140344a0050342e0301601c02d0070f1080c2d641c4907075400350364140e030b8842803454111b6503038804001c0503002c050032000a5550312a07000e03140c15015040389010346500d940301005000342f5941a00403000035407200e10501e4000201440342d081c1d00c1c0c200e4400108624080c100340c02c00a1b07444100d801d68984060340540381c1035402e1420880482114450302046a0070402590f0b00802143c90710070486000358080c08c2070224170201079100a104801d80e1603520284c2c002003c15280072442e8030103812030408100e050041098518040140112040f40c0d0b200a41c1400c0440b0b2025006003a50000c2038403c0703001040c0c1204241c49420f07880e00071a0005407084903810078200316002c1703407001203c2088035400c0101400010303400040c20250154403d40c0c10700103544400302c0079401d50000c00500d90300522102882c510b2801e900141d07020350391000c0649030510350041c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697254802 1250 697253552 697253569
    0x40b090901050121080912120315010f0315091a121e16140111010c0c110406140d080702030a05030c070e070206071d031207060c300b130902 62
    0x1d850480c80380c001000020816411b64015072400e46000034520811861107041030990814014082d50200c1005001340c401411400601c0003070703c2e6500c00344030080c0120107407204808000a80103a80f24104110b071400d910120808000329122001818404005842e03820f003109c00200d258000b075448100d07004480d42c1c0c0403188a41d24024400c01c402002040d001841c984520f2000b184003120902090b4018020aa414401003002b0000408140d90140c02101609010f403070410210380c800c0c900c4c1c14244101d07c00c0c1c80402c94480601504a420000242d5008004490f1070105101e90401600c04001c9803000301e100b10302850725050708211b124a0005a5441803040c0b0400805104e111500882d40b00d070407100500c0c1402120341144c02854900f80185074181c0c26101d5a08141c02907483c46010703049480c4107680901c41c9507a0002d0480781c41748081c0d004500c0f50b1941860044120385140c051003481c1d28084041488241d10300001c0c032084089601000707581d210301c0f0480851900410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697256052 1250 697254802 697254839
    0x605040b0a08060f04080f0a0807020c01030614090c070c030c170d081602011b0c03113f0f030402090603010e060a02090f0916080a18080702040b0909010501 69
    0x110301100510b0041656661400508070545110036040410180b0940c00200d660310700000c00e0a076a1540d60348401410b0b1881107940e900180207d08000486620902610040351611038841042270424000c1041020001d00607030b074411410804540024101881e41c03004501850300d044165144c2102001410100c0d10301e64201d0700040700071044140c02c090349582000382400b1000c003054902009074010013004410818108480d100e802c44954048000c048a522941d240303401c008804003495a0385002e1003100e41a85441090070b44460650400c2c4441c0f9038040e04c1c02c40e4020707107514011142c1c0c1c1c0071406683c0c0030f10380001040190706004401c81e400c00300641c000c22651112216180d03c4a0000d0300c401003803078001440d00403580e900c209030251520001c00400d00350a0580c0d90324a2568956000f0020420b0700300060001c8802c1c0c441d081c155050215000d004a9150761113188a80c007003102242d1283d5036020081c03254035a07010903846510f0304000080d265060001c502e40d996001403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697257302 1250 697256052 697256059
    0x705030607020f0a17070b091f021e0c10060608040c170c0f0a180b1813020105030a021210080f0d0e060c0c030303160905012d110d030605040b 63
    0xc210b08010f95001409a0703010350000030f2426000c541d01441c0185104941002d0309480d50700090000d442e1000c18a00140c81106d0710700c10818425030200300a902585a01d00070365101d580c441e9810800e03880c024055280000240e400401d54034021038119440ca82125000a01510400081114000024014100d0a440240c40c90701101045540390715400c116030007800c411b020340c5c3c0c075070b01c80c0507400b0060003030000202c208800420949000344078a00b1258850400d810364507020449000081e809040b202d1030000d03021030300390019a8154070140494000c0d60b400c2241c0140d000028004a0046404802100400c0d180400c1146421f1842c003516200da003004901d180203640104040c04041300541d5401d45902c2c1700c200403803c0942c070659154160000004205101038503084170035845080e9220034100988840044441c040e5103800303080080f83c010440040103130f0844c0b43c4a14212149005251210300b25510f07410074600300200b40c08691610414881480c1c076008107100d00c07900342d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697258552 1250 697257302 697257313
    0x608071403161203081e0a0e0f0a0312060b0f1207050910270f0302120c0303033102010806010c330f020906090d03090b2a0f0d030e07090509070503060702 68
    0x524000c0e58000506030301d0802e5662a00300048e00b90610090103000e4856068580007505070802800c0754481e034801d140f00c0c07803401c0c002264a0a00c1002e036061203000541c95420705900b940c2c2100a08800750045040c020140b242d101541d941c1c031503645094041ea9150b0250070605080b1008061840d05200c0d2714400c1d111040c420840050000c0301100c2d0104c7e420139100007090f0501c1c0c20145041083c43d0503020010400c4444c00e0004804c1c4c0c400032040602203181d00e44138403111500d880c469002400520580702240c095845035a50800321402814140000c03565902905da1300d030000e10100200c4a403074030042140c4411803241c0041000400c2c4158600501d240008407580b0441500601c0b4507814070400052620508003c4040e00350308115580d81d40345030401000000b45030100094810403491992078400011a040c000406881c4c000d000804010100340d019009030f5054076110f225440d8001340c4000d19009a42c00b8045620280241034107100506061000c010403c80170355019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697259802 1250 697258552 697258591
    0xc030815011b0303020c1005060a0603052a09030109030e011d0d06090507090204262e0b04020d02030109050903030702030d0506151903050109060807140316120308 72
    0x44002c2000c00c201c0d6044552000c2402d240550003070048000c080c081d48299054004000540c0c1e219074000c02084501c40140760361040f080741543d4080f101580300e11030182c2c5034031104103010350149500b0501c2e0000b03030811800c41c0119003110046007007940051202c2050107810f580100302c050205a480307142d590b81985440104000034036540d0001c280a64405010381400824005000034200c0e481c1c0555440c1e0f5112190703a0b10f401003110360301e40b008a04c0b052401c030300800a903108002d80315950380c542410200c64406d013090030349400d01c80103c0c1c652808142c980c0c2e85100500e224582e411340181c41e035040c40300800032104000d20713040c4203034410001e10900a0700001036581008a0100101d01039172454049000d0f9501510215503100011502c00c0510801c005102c0103801c055604021903aa2480ca00342580c000e4441c010a5030031000c0140000701e406980740029860280031074140071150b5400f0541010f0541c84400110110580b0b441016444103a09400104104078400e00070361 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697261052 1250 697259802 697259807
    0xf0c08160b0907121b0302030d0503090111031911130e160c030c1509081603020d08150d06060509181b060901030b0d05010c051218070e180d0c03081501 67
    0x31580409070041000d1607039420003001c550030480255502a0903950803180c276060180c0303545c20940da120446d500340b524400480c00203c0c203481c4180754000e0140108440003100038003c00801da80e01c084c0500030042c2c1200b640d0104000e4005000b05600384116107410f0700544102030315105003100300011501c8000100c1e85c444400700c0308540100f80260040d0103040044000c0850180080041002068400c0703000203c00d600ca5800303010b80c0030b4420f404620740e01195000c0c1c00304c03007aa99202e03142140b901c9600b403520f04d1040c036034402c241c005142520351000606442c01100c41039008a10f540713038803522a00a220140c4280100c40741600c045d00c801000800320700400d04140c0c1010303a0b0302c00c000039a0b82c919090600b1503401c20020868401c014074010600e03800440d9210f01c00c41d2101c0417030406506941000d01032154030010b000070a01b8220b10b60443e04018141c2c0760180c41030b20301404449418030907424168001e07220511308105510740039250101c01400010340ca0703c0c00010001c1640c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697262302 1250 697261052 697261079
    0x706150b0417150c0903061b0d0914032805030c030f0601050d0c080a060b03011a1e270906130c02031c0b09010e0c0a0f0c08160b0907 59
    0x184210030341c8a1985445407424508103810f1551076900100e002401104000c000007003a43c841e056090750000d64a0b456038404910f0340002d4600160000c0005000302c02c103640c00140744a00c511314541ea500301800c50b40e4910b40001c11110029040c00e161013504502418101101c94614200182140307401c0b039002c0e03024080102a0002c0e20b2900b40003802582c4900b044540281083c2c03403c121000d1034620040015200320380040e07003985490404a2842d07001d80a0303904840500040d03141441600c044e051154010041445541000564409001c40c8840207005840f95401d0b540c0801115840440942030717201130340314000c105620030300000d526501c61078441c1a401140c041140d280205c402ca1851050002402d140e01c0b1280c007080340402150425482164220303007145e807990301c1c1c4204801d02201900c003031355400403c00c80da90740540141454400110301e81040e401500d940e864104140d444960402d4a0780c542100038410041121002c9410262000040a1171418900c1808800c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697263552 1250 697262302 697262309
    0x50a050c040615081f03050a060e01050112021c02010c080d050703060509040201122c060a0b01020609150615040311010f210906020c12040e0601030b1c021807050706150b04 76
    0x34440f517004003108103440719500700556210013142d104607074504240004204030b0550340d0070755003410000102004243c1c40940056001011007000001000321604a210742c20012418081b0080903200450341550140c954803400a90204136880c0c40300c0c00500315400c1d500254401e01d050070621025036800324650080303d41d003503000900305040c00800b800300c184101041c0a0742c1941c100c1c001c50765030017054890041022540c1440002010001680c4032801101c0e441281c0d401482c01e0981481c4080066410220140c8842200e948450b9000101d0380590004da58034814081010032550b17220401a81c100d0261a014500303d122544401d43c240c0360074000203990b510f4143c800c007842840d40c100e59540e00380e441202c501d0308201007040307110b40040c403c00582c0c260700c0700040d40700e500034012400302c1e440080c41d03603620900140308500407a9030b01074144e070003492568416400589514130603010b0040c03502d0b911345414861918509550901c5e80814090756020400c000c0d403081e45060f503040c2e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697264802 1250 697263552 697263571
    0x6081b0a0312122d150303080c070c030605100806060108520906030b060913240510170a11190c021e0d02040209040207050a050c04061508 61
    0x1622101c443d500603000c10304c8a403120b070301ea480d505024010351100da001085600801400102c200d02c8280d10003914510001c1d0200300c074400020001140c44000300321252140c00c0607140140c0701d0b200c2c1c80481e04112808a0704051780d2000703000041b400c00078954040024600f16041d403030030070142e080300480c81081510303220080110640002200356140d144801c0b4030f040344420402d084442d82d0301000380c00010042800c190000c1a40c61207401507001e241c07400b50100786800c2915007400340400da11204c3d0345442e562030385083c03040c1c4212181e8610400d26400349544940c00c11080001034104c0540701414080728201900c042d601d51503100c2da0000da95240010100030851803004a4825110041e003041d02c001c1704c10824940003c40c03000b0943c000ea802161040400b00684422410140031540c45081030410400510382500101059034001d0005824039001d6911286000384482d0101c0d0306030001c06007203400381418400c2e240203015841e0003564002a421000e010400c014092808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697266052 1250 697264802 697264817
    0xb0901170a0e030304080a2d0c060b1903020a050402090a0e0916030b090607050f07110a09022a06040f110103150803030601090503031305120c0406081b0a0312 70
    0x41d464641c02506400609815265245441e140c4060320b90f21995141d40850300808030840c80b00e072a100890403c210555103040b8080e0b01d500265441104440c0c1100c040d41c45607c0c21030315444000c3c400c42d0345c40461502802036070951041158a113560b40000d0700561050101c0304655481c9400300c0c08507418081240c286440b040030303517130a0002a0100b04d95040400d8030000c10002c00b042e0840c841c904030301c2691115203c4601c11103251042c406104002031042c405040070482e40d81c0401380840004220781c8502d0b584040101c03d80c2c001c14000e4216031000040d06d6804408692044800050303030003d840c0c03502d481da0b01e050b041c0c1c80504011b0f00308500702e00ba294640c1d002c0d0340200d0036100c10f04910560181c0e103583e055a298011101c840c0043d2205d000043c05040020035111992410321988003100d081c1001d009484081521510480c82500c0b0485006d441d13070312a86010b00302c1e01000e0700441e0320071b104034100c083d40c0504003402407800c164104040f40b01a460240704400c28a011603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697267302 1250 697266052 697266061
    0x6011b17040b0a0203130f030c180608011e050a021e0313050604060605101d01050706060306050c040608090307050c0d03030b03340e07030c1107090203010f0b090117 73
    0x180a4040d5800084180c40c0001e00750740804e4000014065121401d81c100c1881c90301c860b0b070322404003014440200080b0440b841441100700b50300c0c50051072000c0a00018100e0390b40c4415a003540c1c0c10524640110101484400a200450249a41c408a0103000350720f40100d03040354241164003004041c140d5100840800e07241350106500d148012340120480d10142454140013004010b2441020300c103102c0e521401c08181e000b01000c200e003142c0341000c0c40d05001044015180b0f94484002115002c0d40e5007030201c0001d2141c8a02070259490076070b1a0f4440741001c101400094000e855000c05900c10300100000400018010349079950580e40f40183c401039207003d40142082c20120303039140c065260007048410280c201d030604070722117441c501c13035031082400d10203620101c5000e6440300c001c09800041096000760084141c4c01d01c1032401c0c03510340c003000b22420b003441e007143c02502c00e590700000100190301440e50343d034000e030121641c180e1130701d034100001034186441020100030300907080f030005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697268552 1250 697267302 697267343
    0x3021c050a080408100612020907110f03180f0315060616050604060b040b0a08070b031b2701050405010507060b12010e030c100501030c06030f111602030606011b 71
    0x701a1141e0001c05951a1511010b019484100d80860801020f2608400080400901c00f01c403185a070050300c00c0406031207550b0200d441c0750a81e64480c52a1051024906400e0340401c01800c51075000745421621101da007080040a80e5440740191090340000c110f800407001075180c071354001c4c008444003541c410081a034085144030040e40640940583d8040005000c51900440001e2004590400c1156012404c0144803191401444101e84c072201080c0800d41e2780310000c40d0030aa400e41004644501c1c0c01c078081556000c14044050380d200d028002c4154490340f079000c400c08a0900f0003504081c10140003e0660144440c003074840c0392240500d00e51034444602507461925040002d010104664603a50740d240c2c000c3d02c07004014490996003d0b004c04a0340700b114181e035030081d598580340d4a8482e0840281c00c5807820442c200d541c44480342460f00b94070000b480b5041c00c94101944158203401054200800200321a041c001541c0c002041c064120350000041c46c4c0c04045014801d0248929 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697269802 1250 697268552 697268563
    0x60504230f0a060c11060f0706050405031228060b0901050d060308030a091104060e04080c031201060908060901151701020f0a081009090f081b06010303030c02010b010903021c05 78
    0x4090700b00a1890380410129840b444401600e4043e89210540403404800d0000b6803145a40d880e849180601c0344c800050b645402c501d0b08580248100d904201c0545100703d110f81d01619030030000d0007028040030740040100302e44000c480e003803c0c00f0000700340740145201d61440f542d015a0304120000448050a200c00e61100014640042809449180050b0058020714290301e00390384c840c5582c1e540c4d242514081c0145001d0f9842d41d211840705031280c0d46c840d08143c010b11a02c0c1c0d07240c001403211540c060341c40c507951030080440e40d554010b034928000c940380c2019405001010740da414100041003120307030001610b040720420007048002d0001c132200c0500a01803010741c480d803010000764800e01c00d50302c4000c860080c802c070581c040340303e42c3e0303045640211805140c009109001007518a00400c00e60f0001e1721085024007220b0f4090111421810f050010903041203011940c3c904407031403d0343c0c3c244184a0702c3c03042070800b01c0030181036400048410030080d0320707402c0200d040c3c4030705001c01809105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697271052 1250 697269802 697269829
    0xf0a110f01260105210307060507090902030c031803030411011b080408011d030a0e09180f0609011b05040e0405191a0a060e1801021c0f0606050423 65
    0x1500d000b2159604282d05003007034280b2440e441080c0003031590260191410030010030071a407000542c0307003044a5407a01c003c0c000c000e00070814803d010070300203554141c50000b18480c41d243c610150b82c0b03240109040c03894400e109516071490784240100000111411481c04241c43e090030030100340d000f01c490405181000c0d10000741100b0000c81c00160403501500180c0940e0210501c2d8411030354411810350b0b490003645c03003c00008201e0943d000b01801e2004000d50800d50140344660001c000590003490100a0729031001c499101c3e03410040c5000007881040030704c00014890481803020310030010024010341c0100820362810300c0c04242009810400303510403103407203c0803c2c0100c01034148880c604081c2010700310400304480c00165204507038400d00054440395440782140da281e000039020086081080e9000c10365081205510842100c1c01503031389185c0100b4049104088000d440b0b00740ca0547d4040c100740708083c801806229001d440305031401070b0004030b912034582e41400107030b18001c0024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697272302 1250 697271052 697271087
    0xc0114010f0b03070207210f0506041b0506070206090303040305010c08040501050f0708040f020f0310020421020f0108040c1d01061b03021011040b1204050f0a110f01 73
    0x9048010844091861034122098408011081a03540180005520003101d10340c0050300200030621190240c03901042d20403200142c40400e0442c1a80c03480346035180340c4010341d2268005420030003085540700701c818051403628400b012107450302c008034945018004000748038450200709007810361000c04c203560003142c200c0000e104030b030742d80030018210080584054425500b44070005c2c82600b5800000c13801350b0360903900d940941e521070703c07044801c00c2e21500481e40415000f070188080e80c0d08000d0849c00d1400200c0041e9035520740301c6010140d803400000c9960b441d07951007840300035139600c1d0b5103e01d00304c0b405e007480c0b08a650b0340d01e001020300d00e00da0011001038070012114520310400c0e4000c40d042c0c45564644503090000800b001e683c0d032524100040059009203012115045541c0004501001078881e079810300d81c0b0350390030803125000139003901344480c1040108400c2c00030800010b00343d680303081e0242040000540301c0c00d01c18400984035a0040c0604500030001e644211030040c0c8030400075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697273552 1250 697272302 697272311
    0x2a061e1003240b361315090b010807090b0102010504050a020108041e08180405040b071412090a022b08091503070909050702030a02060103060506190303080702070f08030703080901020c01 82
    0x185428003100c2040c03001803000143c03190303148103030302d5080c000b4074050301c0303079801c501d4001126644141003c542c40341c2000f0421f49681c54140040c8250860314041e0401c000034040d45c0741000c4940d8112118002c1d12411a8104801d10001c030310042506180e4a030207280032031084d51b450600160380904651118410741c0c840714a0710911900101403c00d50707001c440d45050440004040109903181518054454460400032503036160148000841400304104414240f070007900c1d00f1101c4400071100e6106640046514008500c0c1c6481340e00300d1380000300c59607a14002c210000c2c41403050800c50081034558009603010700c668410240401d03156014010070fa072490f005000034882c82d400d12641c1891400d000100d10380074004401d440c44400701c0c2c1d0040000c0e07880c40e103c041c06820050440b41d0007840070300e0000300c407903404816075010718001d0b1039840742070412104c000d1a000c05980171203481828480240b26590002c41201c2c015601864030410701e03280e29020714028821051303100c080d903280 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697274802 1250 697273552 697273579
    0x200a0504030804030827090601200a080306090109020a02030a03020a0201090204050c09031219200a030807020d0203090105071121011a0f01052a061e1003240b 70
    0x900028101c0c01030015200034000706661110402c1b80840900581c404240400a00d0951040e00014466900302d89a440180b400d041a103081c9440110140c590f00800420400f01c0e0611802c0035004040c0d03107104514011003030038000d469000350f840c0c03481010b40000c3c41c02003da03c01d4110180e0550014800c00079401c000580d03c585034000c1c201c481c001d020b842e1842000040000983d4211000030740300c032a1801545100716500e825040d96410440051071b48200d036200104490007640d8880c0d201c3d0742450402c49000707464070f060301204404562041042d120300f030740c0c08801d0300d00182e030000f41c2040c2ca82d003100020780fa040d48441c485582844525a0110303020054000c02a0810b004a002c51001c0c20b103001c0c0310b4481792100d000307400718000701304030410406c420448006141c00301c00700d04548080c8881e650b00f8107030241c0d20416104100658003d03850f0100c07058980005c4c40c00500c44a0900d50340d140328a85003036032194401d0460811030360317045003080c0d04008009080100002c03e1000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697276052 1250 697274802 697274813
    0x702060708090a060515041b0504050103020702040f24080a050703080c030d0c03020a09050306060901151209061b0c0c09020307020307231e0601033003091104200a050403080403 78
    0x100302030f06c0b88114140700715185840188206003070319000076030328186043c0c24500150045e5011100498000742c0c1c9801c031105c00b412502c10603000764080900f100e404081c4516040110b001a00400999000084003a0003e4400620707202140e90203c0e0385629040c0d003c9800341540a01d03a922074600c0e0800c49142000e661684c020100c07100c8a403580c00b90103895805140d075460003120401e4014813004010701a181d4580c8044900180900c0d2002502020600380c800344c81055108079071503500c4451049142800e134812031220f60051408501d240030b26280c02c00c0c010418460b07100200ea0000220702414070074800c03110072030f4210345800c40165901c3e0900350030000d90911580d9034090308070036400c0c1d14050220780c05d040c08098010130b896400d5468030b064600d1642d1490750701c1ca502e020030280c1c0d80c000800030720782c0c030201c0c0d1000104502141031a40c0340c0510b84041c54410341c540142101110901c7c21041c558060180c080380d259038000c02c054509119540010b843c0f111b020800104014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697277302 1250 697276052 697276081
    0x51206040c08070b07020d021c1110030c200f07060503010e0106020a030203070b06010302121503061f1e09050c0406021209060d051302360702060708090a0605 70
    0x344a508200801c66562908a440354600c0c01640220303c0d082060700054901043c03c4d24440c3c0c002082c1c190800c0d05005c0c0810741c0000c00302c0840d03643c0d0000e2140b2005180c241645c010080d5036041c248030070001d2510080c081c2d140580c440d00c4000c1c02c4100c1202c40d84c800c000c1c814400c40e0410848080a0302c4c1e07007002e40140c01c248074401190b809040081400c038808229031100c075a060b001076051520a642d40007000000400c0b083c1055804e01c0207424010b10b10100314001e604100444050728032031028982400e000802d03549588425580d8035048071204081c80e030840c4c407004405088803400020046030488181d01038040303682083c0a221840200c00300810403190075800302d035420048406811014010105103e40c4083d052019106002068100b213078002c48288034174a401480c0c0d0b0014513840c01c804c40402044440c1c4601c0d0b0b200000d09415551603243c0d09502070068602020000d40c0d40c1002089042040300120125000200400c601361000e039020380140068a4170522440080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697278552 1250 697277302 697277311
    0x9090e0c0411120a0b09010501210c0c12080411100c0203010e0321010812030a0e0a03030e01140402030a0320030a020c0112051510090f0b0307030e03040f060305040c051206 76
    0x14100c3c074022520074501d034800c1100030800601001c0d0181c1c42c1c8801520304103400d05124012203009003c0310340705003951040c0800c010543d140e100c09080c0500301701c100310144540000074001c60300140703c08209030340c012440c10b80049a220203000404c0e401200e84282c120310080d010343c20300e4201c0c107014102002401004040150407076008407078000c0b61030b480030f0030b00ca055010380020b507001940c00c40800045501c00e184071408a9200010b80103a864000b078a8001d50001e5918060120410760a0094400c0040541e00d2601c15045c2500001d84a06000c0300040070310a90f00d415031032089040009a00c420b0070031041e80d45070300303050b800a0741328401d61501c6400241c804040c80000c41092040c1400750070b041c1c0c0c0c0000c11606200c1400b02002840003c3d41c1400110340000503d01403111010003d400703501e02c4942c403428000e2000d01542c49220000b1480c2d00240010700c0705040485203082160329515020909840d54100808401c030301d5002190001d030500e581209480c40014814042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697279802 1250 697278552 697278577
    0x90d1a040605092802040605030d030608060a0b031c090f030602090906010824120d091707051c060204050a0815070203310905070804120903020109090e0c0411 70
    0x440d036600d00c1103510380032204001d082c40d01550810420620702010130560081c070160000408a4a5800091901840580020000381c0b504400d010204c014000e00c1d4010b0600740042c05030400c4100020b07111032504c8807001100b040f05041008842c0b00b140ca0300001c040a5020980e110b4590034000c0c040c2d07101061160060342200007040b40c03035108540407403160350741e040d14201504003401e03544d24034a5402404c0e41d204d10080c000c0116207105010b4076420440c1307030310380445151414400a901c0708100000b5082a08200f40400c4252200c0d03218482d0503020940c003401841d000c1c90048000d0285812440c4c010103046c0c0042103003032000682c6a002c01c100d402480f0786036123284c03089999100380300d040501003125010004800540c3d0912480c8405401200400c0320384400d0880d0403203100b04c0740d490004000c0c80a1009000000001100c07801c00c92030304e030615034216000030344024007c0c4210661b0070399a01d01c03181280c0042c000c107681020700501c10b0081b0042c140061003103421003c0380496 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 697281052 1250 697279802 697279811
    0x4150614251b0e01030b0c07050c060a02031308120a0f03090503210a06230103020d0f050f0702030f03010e04030e0d03480f1e0c0e0708010b090d1a0406 67
    0x6074052603ea6030790491364041d98202d170365900d02d0700c2c11400360002c4c1400c83d2a031251851007807040e6034031400b43c14813040550003980c440c1040c11102c20548c603242c2c07207441c26811804442039020410003c665002c1002e05028080c141c00107c201c005200e1200d001d01140404542e0907500750011110504242108a2100030764440d90483d504440b80c03882001d59132600e8070020312003442030240110742884141030050410f949856420142c42086403c99841d6682d4010407904a41151a050700031000344015030034204208185800d80c4010701170150f4202941c4002010148240d09203403a419025084200c000c02c0d07480d0140602c05140d0320403403011098101540e04d4040616008504034045800c854000d070801ca0782e0300000e0b81d050003519900d90307d07038240c4042103203102d4845208210080041d0341008030300703000c0609841a00312000080628043c03207840c036805080181519143d507202c61f924841a00050700c645943c80004000c4d040701a019800041c1c41c2442502c80c9004000c11710 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 697282302 1250 697281052 697281059
    0x100c0b0c031e1311041505011214090d26010306050612012414060d05060f120c040c09030b0f0a061701060f09200903011e0b04150614251b 61
    0x1003a520703581ca0886c02c034034148404003c02d42c071a450344070841d88003c0000030400c049141000041000b140c503072255500c104049030205904c0001c0c40030b0b02040c4050f541c581c0741019141c00382e2190601c03014080e941c403070000c640d0b1030f6194615980d038140c1c500020401200100d20313040d004011024400c042200300702d070004019080c0c40c28005c102800510291420142c0300c40c0f4001044080d000942003201c81001000c2c0d40c4900e0088540204000001c003030344000c1104000945450000200421202c0c0c075041000a90034403007240c0110800045030070aa940304104401004c0c90b80c001e954040403030b541203407125019441441501ea1041c4c1000400d0b0700c501214041e501d4004064800c0c001984224100b00342a001500401100500114010706422880b41001d014581b07007070415941c440859581c0c0c5450710032092095044011742c081c584c500800a4600c411410440402e0100081c0700d40d00d00103c140501181e00f100080710541000c40d0a183c2b00c00020200d80682e40c1c0b007101c0012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 697283552 1250 697282302 697282309
    0x50d05100c0801180e0f070e1b1903051906060e030c0d05030a050a030605090703020d1404120f030e0105041103121305040b01030b031506100c0b0c031e1311 69
    0x54140e884c00d041e40c20100100310710031801425104449003030f43c0281840c1e0100303600180120700044c001031503029450300300a00b8902c55600b030060b55020f19070080040d0304881c0406a0455411321050500003015070398043d409810001200300c900c0c01e2450300e500856181c0d001094413071044e405904035012503040790b042c096100c005076005070540d8400d0041d00e25030b40c440c100802411645180215504d1340d1280402d81d811402d07111000030a4021685040741112071041c002401c80c2410400d030141041d450399090f5001c1305042504103e82c2c05450000075000c1d420071005c41c1c11040080040e881e290601515401da5140424441c1c0159034002018103600070a8816006110710b820380510304e01000c10000341714500d03041e0b042c15120340e40400d04d07903414000e4028002044500740b04604e4030030b040007074013012030f4440805c0c00800250b94021594082d80d40703501840c001d100a136070b030700d440e4800031086903030f0002025070303103c00302c00c0000c0000e5034902036525a100c1d000c1c18400c40c1c80d41040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 697284802 1250 697283552 697283567
    0x1602060d140f2e0e0c0f0c0606040c0c0c091503051501140d120509010c150f0b0406080309040209220c1805010c03082e14060909010b09030304050d05100c 68
    0x8414445514060900c08240007032411500182d807010103601e045840c2220000c030b904111f020201d10b401a100704421070801c1d0084030b00c0200c051900c540303204140d40c1d80c40030105c283d010381001d0700c0d56011070f00f01d0004c510301080061500201100c428070746c0e031451040402024081d00c0411068100303800400d09014150081c0309034010b402e6424081500c00c100c8858014a840504005800001380d010036428020a548500300c08008100102d004076440c043d1001080f210f801503182540410048802205a9031800341c11100982d59040200005a42030025070082e4081c080c2c003401010300034142d0f800341908070b03241c1d00c0d440016018900141681c484034030846002c1120001507200092007120403d500080350722100c03026207045040c8040300039030764860741d00b0303402101c1c0140f01d408010510f680c01450221415441e0142c15070105613903903030603c50310500c2d01010802820558090003907038040c041c05801680040040d04203070750385001d0460689406403502c601400050300c40c215 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 697286052 1250 697284802 697284871
    0x1212130b0f0d1a040603050d110304060912050a08030708180a08040923130b011e03020112090b07050409140105010e1003090807080406080a021602060d140f 69
    0x10001d0901c42000c4030240540000d5641001103014803d442c562590b41c0c1c40b61760302540c01100104030706006044090800030b10007803c0d030f200d940240000c0062030f030f200c9004002e42d50580c070403c18018051410300d10340f200c2307204000c02d04400401041030711940020b01c18441d25044c18402003902250441741d494220300e92000d031910801f0001031003d45140e420804d6503289407a001c0c4045404851190b140315001e85100c44110380e10038140c800d01840076001d902410043c0d0410280d6200c0380c0001e5002001e92000074140f001d01c449403000a1141c4e80006801a08041948520b00e000c01000308a580075008a06d4400c1c03502008480c2d032000401094180c42042e11001e01aa02d410204000251045034004c105a111942100040e000c04041c2c01001e1080055a403a0b40c1015805409004020460401d061050001107001f0301a048503819054040d1030041c0d40b1a00f919003040a000034185a03c0010311100c10301407140ca07540c140502c60f64075202032440085c1c3e4455011074107200da95 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 697287302 1250 697286052 697286077
    0x709020f0301030f110901030827031c020f101506020606010e041127040c0c05030703030914011a0406120209160c051005070905060301030201120b1212130b 69
    0x42c40014101440f03004c2082c0110808a40101d1050010301c040501740c100b2100c4c2000410700191035803041d096100d50540c102d0740e150f1031041c80e201003a038600e00d008051742504c0005a151100d00d00901c60114550000d0302a510044039002d103c2c0b001d07140c50301c46d0080381e108141c0300042c500d101180c1c4a014400581d2850400c5144000f00009056444401c035141d031820030544c0400c00c400904030b44980700480304800d10560712010882141d032014101400d000c2002c103c4800520080101e820999060400003150344147c101981480020780d401c0c0c6c0d0075072800f600d240307004454003aaa401244d0444082c003060340c54200440c10101701440c000e400014542c0403490710150341c074070f985a8204510300041002400e854240c80c1c2012900380700300403039031902400081e69003c1910310203004155000b84c5075501d55800204584000700d004148950740300e14070101642c0e0600081c0002c031701e100450380100348000141d0086e0303201c40803440c10f15030518030000714181c1400c02d8460100104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 697288552 1250 697287302 697287307
    0x30e1009030215090f0d1d03071a0a17072c0310021810050c07090b101206170d080a0606051c0f1409101e0c0203040506030412020709020f 61
    0x3442c003d00300d500600030071058020070621003410b0408100c100400800b650b2260406840f06000383d0890302c4c1452481e009801071031041c0b205917558540590a1a40300003144d0b07881c01a02411141491040d0b640305184940c0018000065440381d8400c4841d00071f15211a41c0100780c943e40b6416107801d01030035406400502c03100145001940c0503100125211147d03001c16081000010720742d00701b00304400080750004c58020500ca004002c817102502161000b0000081c5c0baa0000d00b08840c5148607004011400c110050218101c0c0c10202c02004400345141c1080d88114001307403540301d41841c000c005690200010a42c001c0c030300940c4110755032515011311300b807c0e04001c01c14515010442d030340043d0b19600c0d200b03a148460300c95042c2d81c019016030b0003154109054201d00384201e5038040e64000d805d001080e41828680e4010f020000082c00c00003800310000c0b0002e80c1140500d074001d6500840c040200020321000aca501c0c005210740390700f40c800c40c60b154044082280103c00055250140070b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 697289802 1250 697288552 697288573
    0x6030109022101020d0609020a11030a0203030c0315090c0c0c041802060304081c09032c040b0301180c03111206012304020c0a05010506061804020d0b03030a030e10090302 75
    0x10282e1a4200d448000141c50041c4410b0b4250681710340754400182580e00203000d10566034001c000440d03050b000e9014502d081d0302c15800959030b00001e0408100c030070b00000806c10207400d070000c80100c1a400350548400380740480314400303e600302000c212418001d809000e0301300e1506208202c40d4004945084003128038540034003c51350030041044403003190801100040a0030003e80c03c070304803088180480c2964040c40d009114800051100c00d00b00184074010511821030a24050851000c2e04c0018a641c22400002c0c05400c440e4081100034100702e0003142440b0000741c140c070549004035070391210042940140301d11422400c00c42056500f2080060140c07101908070010201c0795079402850700c01000c030001b42240d0246418000ca075105e011643c080010a001e40c6504c16800c03505903041c4560400e208034243e5050020300e2140303a001510303154081c4554404c0141d8900030341101d0700c03802a0078025004000054110003180b04d500301000868080d4054401740640c9940034000c10f055 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 697291052 1250 697289802 697289839
    0x27041b120e071401051b060106020d0503161809060308041e06051801020a0b19110c030f030c0409090f060f02070206160218070504050f0d03020a17090303070f0b0603010902 76
    0x10f500304030f28104407040016404001d0081541d041e4005002c002d480700b949401c1010b03140501070b00c0c0200602000b4010041c01c00c103c03007501c00d442056410100c0200c042480d540680409a0b041180c800c0d10b001800300c24000401c000c0c005031100503ea44011400300040350444e010703244130b0040022401c021581c5410503881052114641c180101d9a0580581c1d5404240341000c81c0d404200c002040c100313503100c44e0540a54844c019141d81c00c07600d003180c3d44101f49c0e283d10805021000010b4000082000003c10728202d40042007840d40c20003a1a000b0f181075240400180c10949901e401e14155001c3c5000da0300c200c0740940e9004000d245444145c0e1200304c00500119001d9a1004021b078030a00380795003028500d0b100c0d924981d54ae699560800f000c000b12004004c8416018590008404d00040e0f00007546e1290036030080b8048025200c1e070440e2034824400d0100da40e8250102048540c02c2000418601000d2403240c00d02e402c250744c502c41031600301c8030361550280d8801c15281d9010340451 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 697292302 1250 697291052 697291079
    0x2060f070602040306051914160c0c050907020a1a06060409090602070b09060610020c06040e0c07080f1e071203020c0a1b0f060503040827041b120e07 66
    0x41c840d2102504180e540e0301c440003141c02c101d071148501c020154003807070720003141e1141c040c800e00d0890100311310b0300382184981c5035802380101140134402d002342d01c0800d01c0180c640381001031074010803021080c80c04035002912003902c0d41c000c4805140444480101001801703a1f288621030140c0110300302490111404007070f0004120039900181d00b003024401051090300024461000c00008000728101041800f6100007407581300c0d42190004890080d00d5590441200c08071004a180d0501a803529802c07821141b14a0340000c1049a00084044445821301c000d0115007201034000305101c2400c007007251040c450303048000e2040c0704021003054103034000e40c090455102e1003012502c66561583d208000c20071100100071180501e0b8504204000c540320b810b0010344000c0c6000742c214102a510052180100780701c0c030142a07a041100ca44030307180104182a21040188140000d102120186407c88486003103c40010a101d01e2a054540580105100798941d100140507262400c7c15908000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 697293552 1250 697292302 697292317
    0x170d0c030e09040c03140106050603160323330108190e1b0409051504020f060301060809010c02010b0a090203060607061d0d0305071d0a0e01060302131202060f 70
    0x100201c0352295074440440840c4140e110700250201c1c181542081000d84a80202c4503405a061070014001c603112802902d4010f00c010058003c21903550106038040c04001394491400c3d20302031641075140720f03000348250003003000341d9440b092540b006030b002241c80d6002805080a20940b5075845140d48a103070301c5039011a050f41c0201c5c18910143e00e075000d8a0045450460b1948420040820b40c1e12a4016007005541200e0420003140381d80d41d100d031030741606944501c040380710704009400e6444445280d030904a0080c40385981e50b84510001e8000341050310070050765860861350201c07050051180c1400b0020040080b00890f01e410070003c0694070041903581c001d4024446440003601c0e0b40602c6440c00d015030643c1d0a151442501a032030164140310010801d4142020f0004903500075030019046c040c259102c41c99080740c0008140700b05c0043d03008014180c01d810000070b0b080c6c0d0542c00b51607443d00e44242e4040c3c482d91440e006401d82d084101c00307940716108001a2030050310403001407001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 697294802 1250 697293552 697293557
    0x307060f052e080102031602242701050a09140f1b0a080109051f14160c02130b1302030c0412020d06020712080105040507090303030e15040503090a170d0c03 69
    0x9850703c1d08615400da03002501e03d0394280d4440300700c1a003215010b000b01c0501882d600c40800100c0406249046c840300041d201c03401010302c684d1030f01d19000c1d15080c049490220440244800e083c000d0900c0010f041511007510000c90400c205101c10b10041b43c1d80f848818000c0040c50a25034800700308a2004a0b80800e540c00351000600040c0e01c603081c080c9411140c09000038040742c03481116514000d600f000c02c0c00118500d0980712000c695281c0d015507401040264820320301010040c0c003691012001540030f9400034034003441068900060f080845c85210968280204007505829007080c0d010a0382da070500360034280720610400090030800864140000e00e5550420903d440e861b08036400340b501a1060040503000c403112980000c13035240100015030b0100403a182c00c400040c0a40c0303107800014109600c0344240410640104017125904002200059041c280b40c03030010742d207500c400d08180c0101080307000080c42c656148218251143e01c000580742c8500400d208844040c110320f402c405 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 697296052 1250 697294802 697294891
    0xc010806191220010507080403170723010e0d0c1209050a060201150f12060b0a05030312060f040506030618071502060a060b03160c05030903030c0307060f05 69
    0x186044030311840031010703000380303403c1454070404081014400301c0307000c156051020810001001a114500b101c080741d401090b1440d451001c5180d07010640300f8004040d04c2908071054099203444140c030301c020031f181c1210080100c0200001ca05490301d140300d51040128111070200f5021031090900076980509078584001c14a464100040c02e954003a042000141e40d0350000c200b0000740301e4440c0700a0300c81e0081e40c50703280d458100c00d5100e1141400b00100880d448071682802501c400d002c15028040041c03d0b02c2d12020f84104035030400004484491060860318644180d50034030744200c40c0910700150182010303941d018520302c4034042d401500c5026205000e070000308441e0250030f5910100f081c0e1702612560030b007040603806444007071300030140c007103410030600c144c0e6a18421025289402800d14140500e02d03814290300350300a50301001d4141c0800103803114804030104c001c0c05041e1003810200080e0b03074100100405c40b48d040300c2400c01c682800804100c141e01140040c0c1c0d2090040c00e4000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 697297302 1250 697296052 697296059
    0x402030402210708060f06090a0f0b040f0213051906050f0c03070c03051509031b0a12030501031406010f181b02101a060910110105071805030c01080619 67
    0xb0360220300410020b90a03000782e141070003c5601404070301e030444400c0120f0166030038001c00007041504060034441c1e807240e85051b011208420358000c2d0419050092041000c00002c884000195011000c40110502005000315040c584504018130b90090b50f519401c4503800e109085e40d0130741c0b001d100064159014001414030100400c010300d030b043e10450b8030f12803052031440c02c1c52801074406c265002c12400807041041d010390000623105e82c280c04015058420054404e40fa00382400794030080c120310051034502141c0d80d01900302d41d049078410701c0322850700075800803001d03180c2e2000c0c0125015018854400c0041c2410702e0400d840e4030070900d00004440b0740395146030300c0c4035171480034900c0981c000c0b20284028407070a11806c0d2003181300310440520b10000e00d00181b19440b408a10034481e40b00b5070384100d5405d22a060000400c414203000308568200944013811051604940c1c1d1070070300c9405000300d040d040c0820091f402c17410684034254191294400c109075a440b2102905003190783d000d000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 697298552 1250 697297302 697297339
    0xf0c190b03010f0609081506150d05010b0a0f090b0a0c1401050405070503060606040f0b03090a120905030106090c051b010209030703150506030105071b111017010519050402030402 79
    0x5500a003404080f80002e1441c000004c0e18240d007584c0044220380142c4c442240780445041c086a0040d0115501d04003070840160301e410a0081001c000c0c0058941070000c0b82d00010f91004024004294079481d02115007142d0480300e00d055030013000ca036030030240019148117008081c031030a814030680da81504150401911401c60b6001c40f41034a459221403401c01c0780e800c017444041d40082d010381d402840c2c5820302d10f402c80740c10f0152180422880d000030000c1c06034100cc1c4030b441d844960050325806a001000d00081c145009806042e20135444c00307000069200e410302ca00b0015602036200c00b0306111500046c5219504c00c48500303141075400b00107170807042d039040c040d04c0c0155100304103048540d0180c0380700c08200c0e980100194083e80c5000240890107070450104901c811000340005802400c2c0e2900306540d0b0035041000350400c81c009500b038911031700420083d0500300c9002c1601030740e80e41c403000c1050380381e154804520001015174040c03085007400d030000c65009002828400c0d0047d90302d15a0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 697299802 1250 697298552 697298557
    0x6120a060213150c15060b09150f04030b0f0105100f050307020c040f02120901090b0f130507030f060f0515190b0708030412050711090a23180f0c190b 66
    0x34840040c2410f8014010004d00c0036810ba500222403501b04103103800c19440c03103060310038002c6a92103801c260084c0300e03014a0300e50480c0e03010a68884800d403941d0f900c0c501b003c3d071803c05586040c01702d200100041030034100000c19003541c1d0090341e64140310104555007903506500140442c0c045000d104000400c5444601a0710169500c03c900186d03540c00340781081001d150050079a4001d03034100f00c990300100b003031800340b1504181c405045080907100d03503080740c1c4488480d020003803c602403c01c00009001251b146080094042c00b02409440d04c0c03007080200301e030022150321032080119040310b451400c001e45d030664840218044445d140741c4440d103100164014410494030648000100720401c002c83c54807c0c1003e405003407407401e11400b41d851038110080c9500090003000400300092a0040310303003100350000280b2031004d030089d0100d2000440c0c3c602c200da00103043c1c4040c3c20482194038002070083c50040c803010180c03c00d40c5201c070800c10b0901135603004501c0c1c0074440201042c2036098400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 697301052 1250 697299802 697299839
    0x3030a1116170706141206190803040e070509012a1407030512070c0317160b09060105030d080408070c0510020304031506060818120a020f0606120a060213 68
    0xb01c18111a0211100e4940256a00050b0030492a1982e814000e080c42040c0c40b03003a03050807040d010700e45d103e10104140d44150710100e000004160300004144502100810540d00f00c000b400344241e4441005860a21030b60b5503480c00110120604070400098101340c01c421030151840105070112501c41e804804402201c0340d5a9030407036442001081010000020501e0207a01510f0400c82140c580000002e400d12015117201c5004c0c0b10382100404040031501d40e61030071100d00c2243c0800d8245455030010855250344607200e144008211480c00040907410b00181d5550710f102c5645503a22002c1c2500314040072581c00440e00c50102c1d50340d88520580088034801e41c02503403106d1440c04c041c2d9860130899440305140713140a000703100803a03014030310680c00000814016090114101458504000103000414044012901e40c4c1d01590100b06580344090500888015494100801081c488007601600c85a80241070f000e0009015801820358500801e00f841c070740550300e0302039050b68003198a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 697302158 1106 697301052 697301069
    0x31709120d051005040504080a0e1905270c07060f020301060903030e013e06010b03070c05190305071a010b0d02070f0c08010501150e03030a1116 64
    0x3d1070758003c00c4041c0040296103464240080250841010840001c400039a41c110340d10303195010001c038034101611441071600e01002c0140b14000d403180121501d140b4042c044400881d4010148a003c4444009a0f91100781c580103045416114500300541d10500040c02001d81c0071144c94180d03549800d102c1c40749002c54006a0b0600003407280c92150003d00c00600710000307041022510420041104149082c0422045a80360b038030074041c101d403806c01480000c1d112481800032080301030244003502c00080032048000e44164203803d0075004600c0001e050720811881c0141e00004442d01a51300280f541081c0007101240b0501240324a0300e60003180500610440d24030f06e070990b85d81300860b461205d0755500050f0180c00d00348145840040e44880d0b20304040d028000301d100e040e0009015501c0e02d152a8400e54401c03442c018100740c0c40c0b103840400e032020580441144094441f04 = true := by decide +kernel

theorem cover : BRFrame.Cov 697122302 697302158 := by
  have h0 := BRFrame.cov_init 697122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 697122302 ≤ n) (h2 : n < 697302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
