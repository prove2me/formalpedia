-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:24:34.400351+00:00
-- url     : https://prove2.me/submissions/04f87f79-aa43-4cd7-b401-4a01398482e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 602158273 ≤ n < 602338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 602159523 1250 602158273 602158321
    0x809120c090a0603060e21090109080a110a090e0703120c020910050f010503010825090e06420a0801060e1f080c220507030615090303080f 61
    0x120b040100c032030700007031601e4001507130349608207060200c01000000b2116035000804842c5005442c5401844109400441c00f00341005000c000c0010340e41c0042000d000300a00881d0032003010203d400420071102e4032980815811070800c006450070000200d58641200e4004459101c891148041181c00c1001d41d18025401140d603400d00c41140c14180546007610740941d068040340e4610801035450340024841c42826030301c800640c09144804501b20358070306802c00c40c2501e03007d07201c8040070280c4580040711680f9a102c14104007031000d10100400d00a0f28a00300b4110a840c905d5042d244141e104408460440b20307811402401d03240c10061038000c04020700204405500d4984000c040241500e00004900c030140b21811031407171912076003085800c0348005000d61040d020901c0001c004820164013203200c15898a0b42c1c560040c080c10f80b00da4501d580c0090683d0030040307000020100703000c00604010180009200082d04640c0040c0c1016205207200d9541d0307038468461454040c1c0c442c03041b403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 602160773 1250 602159523 602159539
    0x7050a08031c0228030f02090904110d02090c0901080a0204031e021207030f170307020d08070309080c012405060d0905010905030c0d080901090b0412021e0309130501030809120c 78
    0x950815030300100c004c0741c601c1c0c2d800d12450540580d500d0503401134202d02c90b4000c000002060005260540c075030b0540340301500d0035408009a40009110103811603a803402c43c240000d22034019a800a200303a4020f0007104114103040c1503888520907070780203460150a006d1215914801d5688000c0e030b000307000d4803090403110341da0303100d140001c200400100c044803035500703010341d0b0403042c2040340940f44501745130f50050040ca40f1b80311044a0f803040241034901416529107002000c103100000514080c1305080001c2200c0402108840c40d005001c0b2404400200c0d850040c040c55480604440440744070800c00320380030343c260500e01d004100d40f940040c0766110000c0c004400100204020988007044d8480da0324995070300019030309883c0520706c010055042c10000400040040c2c4c001c2d502a48544100c480038610004001c22407500d40e20664055440490f030611680362071140b81201150700324060025514564440c0b850340a80f80c80d43c0e22610410819100d401c4040002540d00900200b41117 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 602162023 1250 602160773 602160817
    0x30726150d12030606020c04090506130f020303032401090614090102030d090b1905010305030307052802031b010209030316030507050a0b0a0c1d060c0111190207050a08031c02 77
    0x43c00038215441020054061000401c4492410344a045070554208005c0d0043d131369081605409102120003c4510348240410700d00946c8042010714403d40c00c0c228800c4c9000040800c0c5030700600e0310780c0c5560406c00110310503c1707000d03801800c04800c1085003442070703264110400140c0c21070182c5070b10b4407510fa25010a11051090320f04049000300d00b883d80d2504030f451400d80c29025103009000140c200d500800200b10b40b14414001042548010300d02a0001039089404160100e0b03514520b100682c00450b81d0034001c91491089130003010700d00001c6142185c9a17010a40f0303805030700d00d54961110705502c4001814082c400300c400069002054800e01401c0d0f140c881204030741640c45007445881d00042c044018081c6e03d03a0010306610f0400c111101c4040c00030881e099105498003c06552500061003848030000041e00c9030b064041f41545841c000c11070000e01e82845030340b015100307204a8108100c5503d002c401c61303a00200390b04a20100f40081c8038010082d1207030fa02d82c420205080141c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 602163273 1250 602162023 602162027
    0x3020c22050c180a08070302010e0a0308070302010501090506010c030c141c030e390310020f1914030c1305090a0b01120c0918060308030705030726150d12 68
    0x1002003c581050500c56520b042c003d01c280343c0d0050040c000c041d88a40b00510156008014280800d000280000340320350316640c8581458100d400300304c0c0940e4548006101d0070303c05000d0309501050a2030090b0400c8040d46008119011025002c6c00502c0c48a6140180040901003803240541c040c00e50314001116281c000d005266150050038903004003a15400d88010720602c8680030b02403811149050104115080030111440500c0d40e894480c41c03a5400d20444a8009043d9022240b43d899403504101d02200c1c0d4220748490300c030810071009248201071046d8420599811080b01080c0c40d072505400542d6001000c5c041c0c110703e500c070203c2d03c2000301080c20b076000001880e10a0b23a920038000d21a0307048409565800000c00081014658280040c00c2201c2510400482c0710001245541d0b80751540d6409910541d00703100080c0e000000c0000c29600100790500360501c1d4005c0718030780151503100c89000d5501070000403081303000c040141c07070940c0c61006501405400000c141c503904002880 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 602164523 1250 602163273 602163277
    0x310201120b0a240915030506040605090901090c0801180b0c0d1107030f08011a0f09130b03070e010e06100e0a081e0c1804020121050103020a050402030403020c22050c 73
    0x6140103141074021800404c0c03107000d200301254908005001001010001079002d014010007154010b5074441c800100d40e501c0130011401000804000514002c450800321040f8185800c00e403a503a04248000c200c0c0d1101d1204a05001e40050b00d081f096162041c2ea0b00c040e2242c160f00c0250741d402d100404e1320100e002402800d242d4829107030141c000150703500586001c0803d1240055031400d10580e001d0880c940741c01002c001852821040ca44078810000038196184c050a03440341c42d60f0303001caa0b40c2a08041002c20080c0c071032070400817000d41c0740a80c502c41c02e680042100c0c0c020030403800c1c0c140e1510f000d251101000303d0010504403219440b1003400b540e50b149102e0b9001c4078601100d0405049034007003442980280044c100441c040d40096401c140c05d00003600890401003120090030f014074080310366400508100c0fa0210b000e514600411420314038940003103224520420500002a8000501c4540d000064449440c41c0c0038803900540e4101d8035026140d0902c3c24441000101c0d040880 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 602165773 1250 602164523 602164559
    0x30601110d090b211302010201110711010507080409140f060114030c1305060304080702011e080612030c120c010507260c070f0b310201120b0a 63
    0x618040300e002009603666a4140c80d005581c00318071a258140000c440000050400141100001c800000c0c80341c1004c480075801c9401080e840f441c509a5011981d0a015103c80d00002e8283c0d1824020f503900c40040d01e0000106250512500141d184100700070b00342510010640d0b45010003103032007000001084503100701c0c4d001d4074000a01c40000d0103903000f0b04000444040488016080d07903900f0010f8561540883c0416440305003c840000315603403240c0085214521500c003a0780c807039042d4800507000e54036010340c5400f42c02d000400600b03644c4e8001026540300e48125003020045800b03074002400d43c030030760100100340e00445004c00e003030f040400000c110203281000200040e0392420b80464218004000206d451600000807003041156104101d402a05045149140c0403007a0381d085141400300d84202c4404a550041083c1044d0041c2c034588a442c04120701d2a604c500480820720001420400034184005030090b8103401003d41e0001c202140064247d850140e00c0d1030507920311100d059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 602167023 1250 602165773 602165777
    0x3030f050a020f0f030c040e0106090e090304050603060628210b01020c060c33150109060c0503160503090907111e0f070902040f1706040308040201091a030601 70
    0x1a020030041c0800d803080301d54181000d1515810510001c1403003501d80d03c0500b0828065809210229000200b1071045000301120f441e40340280e4134159030703d91100402450560f2a070424003041000d92207180449502c00c204580b50759032000741420900c0d40c1541c0d08041500282d0300c0549105554000205810009080b24090013501d41c4041102c25500044040c03801a040814081d416040c0000a004195170481c2a55501ca01d610503d801202580c600301815042d4403000d500c9e900c6088203041c0e00040310b40c0103100e0780c2104000191000e07030507119900400001d0140c1d0030030b11105000341ca96100510094041015081c24025035a8014a0b030181c4180350200104518034082c014803c40705080c0d8025051600c0d0403c0d90100c504948600699180150314006840c4402401f008000e0310400b4001a00c2e41c2c180f00194804031040c1c0c0006210f4200080340f101342c440c00240255029a0500c1c01c00d400760b4503880100e91048595103d100038901d54030b89152905101ca0203584148d4003a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 602168273 1250 602167023 602167031
    0xe041e1505040b100320070318050103050609040305030c0909090c03190c05040b280e060d0305191e03090b07080f0f0a020c07031b0e240a0306020703030f 68
    0x20700070081291103001c0c0d0240d1002c280d8a403051054000d8101300000ca40c101d014200e1001001d02038090f0343d000b44011400035000402190010145400410182000386400c000c646040400314034103100c041c2c005001d0000100c000341441707210307408691172410003801904050400c000d442e80d0350a0307074111132440390141100751592031241c900205001c50300b08a13201d018074544414400145111102c0a400001a06400c203601d10ba81312207009040c40c80e0041c0b0861403a118070b038075031503102800884c0b00d103080040c0c030800300b80d1003800c7c2c030f1080c004102842c010101c10b00040e0b40001c4100c20030b507200a40b807a18105915050360003040f0fa58014070600b10726a940034404caa00400440d142d40100c440e07000403a51303030390b00d0500f00c82e8885202c603001490105a00c030074601d80002540204c80200111008030b10241440c48003800602c0c0030440c2c2c440908000d4400a8044001e4444c450200f0202d803a10b112659851900001581c20100c11555000b590800602406a84080f41d00403420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 602169523 1250 602168273 602168279
    0x19080f0d0207060f031107111e010c0221070f09111e03040f0615090615020c31021215010e04150e01150206160c02010e041e15 56
    0x80811445144001680600306082c14081e0036660628812100c10415941e040d0100c02c804400b40142152805041088061410181080480d81c0c498000040d00c4080204400030350b600062000c41c4107a0407115400e62091360b800c41e450b500c003080c1704288680b041078000101c07200404100703010f407440c0030b400340404d1b200801011418411181044107400020280408100c402c0d030155400601c030320161401d0030b0844d10f40b0416681e0170360000503590502441084010340501c2071100801c0d01c00365503602c0121007007000c0d40b00d12001604074022902e9131f01d501d141d044441c402039401541102d0030341c00d460740554441d00a41100700e07039071101c08007040820b2a07810024500c045042050303444401c55482e450501c40070308a11038072105d4040391100e01294101a042a09001e005a8005042e8040304504000d18114003d4008050707002200c049441856204002c5902c50b40c0a0905041a80044011600410411040078811103a8000d0310701780f43d40070380003a4030001d0454104010b4540b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 602170773 1250 602169523 602169553
    0x70204020307031410030f02150903010e0717011406040b01020a050a05010b012a11030a170a02070515030109020a05070f050105090616020601180212010f0e010f1809020f1908 77
    0x1c81e006c041d00300c103030b600700301001482d0103601d1410340351031010300c0c45c20004040040781c00d5038400700305221035402400d414080a800581280c2c40e83c28903c0c02030102e0142d403a45945005000703041c05024940b54094401030364000c01ca1019010307448000c03512920450704045009082c0380440174006112404050050081c4a0fa1896082000c01400b41041800d5503400401600b12134019094002c0d4154100450440484506550001d9001e00c1e83d59401c0c0000904104284d001a03218000300c16a00400408210507241910819400160b035100e6048061350035000b46000108042804141d1404000d419003000d409135049208031070080d1240d1a0b1000c90b604480e000c100164403140040000e40f40c1c1910354000441c060f0b07001031411070303103407801025042d00740c0101102400140d020410042ca94108a00504085034100025400c10940101d002c0010000e41d007180c0e1120401010f65603000c680f00071000d0010403080309211162202800c0300351600c01c1c5171090207220346081c907100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 602172023 1250 602170773 602170801
    0x60914060303030601030f06120f110603010f030303020d02120c0702040b12101a0a15141204020105070c0e07030911040209010207170106080105191503020a0902070501020702040203070314 83
    0x940c024040c60941e6210b200441c0200145401074006e191180c2e400555180d00c0c84e4034150440c0036440c0703c4400b0700d85040100410001120140c00342004000420112480f0300c03002c0c05896041ca40965244001070581000e80216040c1021040c81401481510021040100340c518401e403014030400000004100e111640c0b00d20040701c0b41c00203010001ca290503584801031a0054000200503580300310003066564000d9080054081a0054086c044a030021206803283c0e190100151500c80040c90070340204102400c024188040820801c0412a04148207406441303240030002183c0740424004000e04031901007610720300d00c00c903647c41450034540220b070314603141a001000c5891801d02e10a102c050000900d020071b542c1c030310011071a50428055140103a500c400418201181c00f03804c0d40845186c480d4006410180400410060719038404110481c0d0203c403005850300c140c1e04007a0b01920819000035440380c400010402c4168042c2d00c81d21540305040c86600075540c1d00000583c100e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 602173273 1250 602172023 602172031
    0xb090a09080f160f08090111070f170c040f020d1104050303030f0c070618020f04090b01050411070f08030103110a06080606030415090f06050703022502180109060914 73
    0x194404020a42610020700c00608102020303ea000400140c95110018010042c103000c0b14280e00010f18209250b91203404c0d0740d0040084800341c5030042c03901510060400551040342c2c05400601040c40341482c0038407465000c0500074205010301d40010181400a42c13221522030859450f2000b51198054540152425202c01030000e5203903889128980307104010040501c0240d0303104006080025940e801340101541185d01a0900c00d445841008407501a148416004518007682ca00106004480550460380181d400090b640c0880c40705181501c603d850280803841100312403009c007c01b640056040741d0050a103c4e8801090300304111200c4882d1041d2000104144081102c500d032940c015030700b0901c281070a40701d1901401a1006440c140e240c1511840d9000b4100418828036028140d4030010a04e030131803510a16950600c09200542c10306890003a4803107001c8215107d11909200c54000c401880c0720640e03503104510044c10030340c080c410b40c8508000d103822801a00409080c09 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 602174523 1250 602173273 602173283
    0x60501030c060239122103040201080a0e10060806090105090d090b0306010e2d040606020706050c01062711040501050301031b0b0406020102270a05150c07090b090a09 73
    0x8049004103aa1354101100706081e6400c032820b800c08541d00c03c502c03085600211406811042d5404950991242c09103900030314a940c100301b000010f0b03038400300b5203520081c0702070001346903089805070500d844c0030b00c6400030782d042c50940046031121000840031310600f0540000d00440d902c401d01942c44040120382c0710013092902505104400c00d00002d0740c1e01c1803040c9461401005580000b0386c10403004903001000c2011600400510203514081441e40725081c0c1d001e00555103000e400030340d503620301e01c520390401401050f20580e10700e003034001c2002000c105261420384603050755000c29948400340b2005006192003e400d041d24480c001b40c070122403050311084d04581c69a07d079110040d036010b40e10100300300b8119001c11a011440081c20182405500060300c82c204001c020302c01007124001d01c0c01040c00640840e42079074a101070700e01500c0080d11360506418001c9052a00d40c05a40c000050034000c042000c910307000a940110902d42c002c032802045910f9290307440301151140d030700c080c00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 602175773 1250 602174523 602174563
    0x61902010b060c3007150f020406050d050609040b0a090519060c3b0102030c070807181b030c2c0103290f011b0c0305060709080c010e040e0604060501030c0602 70
    0x1b003507031030700c80e01c05982001102040b0030203610741c100c1c1203130720680200c0c0124501190080b902045403041e81c1e80800203807092101c03410281c8898044007801841c429250b40c0b52502c070001c01009101d400b400340d1143e101644102010300e041c01c00703003c1c00000c3c0400a03005442020120401c4012601d0454134100700e060100c8413490302c0c0610040450000b81513100401031140c0c0808104800c90050a80700701900c0c00a0034549860341e000e0868240d11410343c100355641101d42031440d8124803031600c03820f001800700a1100b060b035240c6906c2c441244808810621500341082d1884141c04a102c240d804001c0204483c0b07801d48082000040c0440d5015240c10324080d506140001d051002c0c030504000d9000490b10358854410380469108998001c40712204004000c02044201c1e04040c0d9420045030803810948d06907507520740c0700da80d28104101480c00c40202e494070740c06080440102002da92617481e0605052025240c20301c0b044900c05550795001480340d102050501408905000120f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 602177023 1250 602175773 602175787
    0x150c080d09020a031a011401050702151308060a0f050705030f06011808010f02071109040302033108030c0c010905060a110c040504120f02010b061902010b060c30 71
    0x4030080180d00e50403608141440c4021001c00d6101c40d41280d003050031100700c1a0b81d81000082e980301110440d46c0740c18408207004040c0180e0b2028406040c0300c43c840714003a2500554035000c112004158010040c0340104001c0c851017404681001da440160200244240e496002040f5460f10003115101041440c08000c00c54544c070034041c4002404103c14050001500d0b1701000d402c48540610300103070b0341d40c00241e0a0401220400245154504445004503441e140c1c602035101d104451400000304070380e0386030400080c03d032280c80303003004d001c150500006600d0715006552944045841840361003010500301041d0f10a20080054a0b0080c14060400c55404016a1800c142c1190040c0602a0080d9080261264820380b44924000d144030b8040c03100d05603001d801c041017088201c0469041c0031310200c80e40c583c03000300c4003881c602e4040042c4809164401700d0040c04c03404881c0380c0c84100050a03500d0058000b60701d020440c00042c15001115000d602c04402007500795043e00c034440140142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 602178273 1250 602177023 602177047
    0xb04090209030111160311060709051021050106030b0405070914031014061003020c06010b1b010c0503061203032e0f1d070509010e06030c1303080301150c08 69
    0x6000a070720064000f050307000d0410907107a4240c01030780622100705400c3c920b190616a0028000d4031303003409040a0300c13003400c1c00703900204014041c1c080e1328018081c0801c52031100c5d100c1d1034426503903002d5092086002c2050390313520b40541000c0c459000041e05100d8404c0c1ca0b450a031060600400043d200d20b0815131410491050014140b51a80d83c18010203901500c020003600590326404c50004100f520703482e02900304040700741440e030b01070308042c030510030343c2c0542a00154945c15500c142c0900d41d1650300d0803014041c070800300e04540f40c4a509000e9174100310340d0083e015501a980c1190290005482c0f40c0b0019500e000845d20a8842e941c2440000841c00d02480c1b04444280d0600d5015030036515007521412459003030f07124108580c96028200d84001c0314100312900310381d041c40e0542c41c0130030b01d00008005010072205540b1603c2c0000208420140920403100030111454131000142d40e2800c0400c01078009200e0310f22031a0410041c169960b2081c1c00d00e5a115070311981ca01e0900c540c0c0610 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 602179523 1250 602178273 602178277
    0x11010e0c090a02090a08031e0a080402010c060207050f101b021b0a0e1e0f040210030509030c0a0f0501061a16030516060516140d150308070b07020c010503010b040902 73
    0xb01c600aa0030040c1880c191a081000f50251900c0310045544009409409841000480c0681e9103240c0c1489008440f43e8001d00c420f400c40d409103001c01c500b1701981401c1780240308440d03004000d403040c510300e030704410400300d00001580c881250030003041520500ba2584040d000c540706005801907201c91102c0d1034901c0200c110a0070240403100080d07107c10340194121800e4a01c1c500108805200e51030703d0b11400c0381e1130350010881210512a040c1a40407400141c000703000703281856155000501400780410a551268250404403003800d4840c0c10180140c44080100783c6880d4200000410886c009268483c1204041c2e6040c80c0f4209c0c0c2080c00084884113618120104a010040034462190340c441081e1140e015220000b01800d06447e0030008400003241901031013200058101102d2148050383d80000d03000401140c0328038482c0207a200c04069030002030820308003040ca001032004540c56184a0100d540856100451010040d6800c2c00300344180e42c40410700b08000d0200ca025500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602180773 1250 602179523 602179531
    0x3080306061b1f0626010e010e0a0b1302010507021309200a0b0408060c0d0212190c08010803090d021206070201020304150204050a030204093f03110a0809070b040803090111010e0c09 80
    0x400000c07c1380c9060740450945100303400c03c0700c1643c07061a0350030611136880e4a85401068032600c0b421200c1c201e41c0042c020740503114000e841010119030341100100c00e46c0054208983c0501c5803241101d41520129032043c109000b10300468900030040782400d5091f08480a40e60101c0060815039183c51102005610005044580079000d0000000c0641c0743d5000e140110b0821000010014094180c0812103a6904c203807410015124010404110044102c400450060b511108030b6440d90001c10b8962648801c48011445600200040c440e810350145009a20481744199103104c840d0304030050f4001c9010386940000466030401c01441c0590203640c4451261b40000d4030910039901140540882441d88225000720110344284010001d401b03204040742400c0420001d119031807002c400780241440d8800380101d402c0401e43c443c40c1082600700511030a00300c641e41d542c403060b4203074494020034440d6000c1891340e80703503403021841801604820600c0d4001443d00841c40000c11172200000b42c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602182023 1250 602180773 602180849
    0xa0506060f220507120c09060e060f071203050603070806010e07171321050301030f0203030f13081c05070b25020601051c0c03080306061b1f06 63
    0x2d40110100144a041c92261100c1020001207520b8000b00c060040c2030340380a2030001d1072502503241c40070707500021164140e6007a8603008400c40402030205045110340307032200c49a214081260030820110b0613844003801c507965000d2000303449040c02d01d039032a600c41c01508031942141005000203076604440c2c035406185032901000fa0041e091940b021a401502d07035248242454401d43c0038020520341d42d1260343d5111154440c50002e5400041c0749000600006100481a40803841590740030070545400492442d000c960b20408000303031010003515481f904940c1d0141c04507114043d8100c074503500c85242d403a101c20380b811961f03580b035402e905001404501034500100daa100d20392048207107107038220038540003400d0550503c01080400012a070002c1551340046000c00c00003080c0c2e107642021039510465080d12502c0da0b5001071101d02135040e01d5124000c4122074410112030000c2e0741ca403450442a00003d105094a562606031084d9010b0071414000c060101014010f41520111152040b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602183273 1250 602182023 602182039
    0x1305070306061206140105030d050c1203190513020112020a03090b01080d02061518090a061104030210021b1c02100f080106030b01080a091a0f090f0a0506060f 70
    0x1a40e07820341111100e41001600580c94100d0300100082841494205004140100119898440060f586089800c01c0c00c013013040108983e140c0f11410410b580b1a01c054045079a10703403130100885510030207030340125080300307051a001c1008807406020710511150181e4660a00064190480000c1d41c800310180040565400201c4080341203201d1113030203003040e0f074060601c20441c8000285400005461203280000001c9100c3c19962031205000c007803180245007008540c3c0c1e10382801c1c14284d80c040c002d0043c90034075820b5201c1d010355030002e20540c1e00c2102c3c04018001c0020080303954206100041c800c0101301023514034a03152a103141440b904549035004521201c5a0106590343c1d01c5c0844000410600020100307078076040120903024103101e16080010030b4001000070841c280c007030040c0c0c5a1a40d503c00140074408501d10001000b0712100c812026400d040c903070560444011036840b0040e008010101c0e90448011411031003540e0000e000700f1040d107175542089100051000700c540d000e040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602184523 1250 602183273 602183279
    0x207050c041a01110106080d03150902030408090a091418031e13120b01061b20090703140c0c15070314070309051f060b04080303150402030708130507 66
    0x3036002e44070341c044900310002c04412000c0c00140c4200040b52400d040c50741005003d1001002c000341400e054452441d022504015522510307164a045070030401e006400001000148000398005240b130b01c906071650048a941c8900c298210b80031105001d070803060100200d680104070840300080360303140d00c0c1078078600308a03100040700c0c500a001424000c110003082520100385241c20000041c10110004810b2100700da44901c0540c205014800610075000d07032054100c102d0310303491007540d03034040348100c0c441403100a40701c072a4109000c110300c1986100c0004003075501c20301032600b01202030120040d5035200c01c0301c0c0c1e0085420500054500c0c3c812908200d980d4550a03250391700624042d1400105410312601d80700d041d01c0c0c0200714030280340c10000030100060740020841e0809055201115001c42c960000c3c2e80075100c2c6900070f400d80540403801080f4400080000c1d4020019111502010b004410070f0006a000403201e44020445000c001030f040c060800c41004e2070342c410000d580395103403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602185773 1250 602184523 602184529
    0x2a03030605060d0608010b010804050a120c0b04140c0a080705040905030d021909080a03080402011d03100609150501091e120803010e090703051c09030c060c02240a030207050c 77
    0x3c045001e2201c1500c4070020880980b081c4214000b104082c6003039051490581c54055950506980c0280b40c8032041d41150112403060301704203132081d44211185201d0130641060805682c03128004000c90045460581e0305150115030801200c2042e005014131030700d00b904101c010402980252510b0004010202c242c001c9480141441280d4540030341d900c10034a2401461450035401c150070725400f441041000c04d40100420794469424a00141c8550001c004845464521000541c052044418104400b002c5422803400d680030401c007004654400c2d0940e0413180e00d5407280e03c2c042100ca01052084040424191022440408604070034035950312211394201901c04068400d55000320040c440c00000000e095003000d1003000405540d070450301e401e5125141c60700510300c40c1500000e00340515002e80030640046410480c1d441c0300580d620801303402c412140c1c0341284113504100040105040c540140790b1001c200001e8142040c0801c081a0300941c081c0c0015140ca200d0343c0d02c0c00805913 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602187023 1250 602185773 602185777
    0xa050c04110c010c030621080f0f07050a08031e0c0d0b12030705010c030b09190216050102031008160305071202011b03021e030708030a0b01110a11030d2a0303060506 73
    0x6101340e54002031240c0340c03491410569074041c0256250703000c1c042a0201141080069540d654401c280c02541c6480c0882c500400703200b10369000300300d400b5800060302070000320030103940310b84040c050911648c0825400c40854000c111031400d41c1e40c9043c404a800c20f000c0d0703440b0b025842c601811400101c0441009a403844d001880c1c112256911000d40302c0035503505010740c0b456844107864100e410306003404a46108502c1c2e60fa060005036001c903e41d000d95040c01c0d4182c0900703801c50002c640c0d909111208884001f190700815000f0710030a201203600d01049a01c081c00c4940080140c800c00d400c02003d00200c10145106070304014940088804100d1000782c0f40c40c100e0303c6034009102c0000744e20070030114440b440501c5c030b5017030700140070140104883c82c00700c0c1e41c8908044000140308a0100040e14598002c00c83d1400d980b2039800c42d00c08001c0515a4041e5426040381165007603151303261304840300030403103555266808000e119031260101c040c01c407400d114031a040114085480e140440c0c05a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602188273 1250 602187023 602187041
    0x603060e0f040f0c121b030521360f0a1a190201050f010501020c0616060e030307080a05131707030909110d0e0604050705091305010c120c020a050c04110c01 69
    0x400e44d0740955108004a4426021400c0003001b8a044c015195441d096281c000700d0400c030541500244402c0b030454030f00070484000c1045030390514035680300e0214804211800364207144400070101d81e800240c1c038180d9140010300e03030002c3ca4030a03c5030400c840c04a440140401c88418100284694081e030135481c0c510303119080cad05900004084c6008815141c904006a200d40c3c10764001c1406101180c5441003160302ca100c045255182400d910310b0140000e010a1104035203500001c41400046680846094000d00ea4503005100381e0b119615003a010007105100181550003240e9040c440321000c1d405400ca06000381030825449640d4816001595540382c00d2048901d070025001c0b490004c584548100300c100349004100d0791a140ea5080d640c0c410f240103842c4194420360005403250680e0502c1074049510038001c0c06400820341c405402004441000c0c0c10140c00c00c81210509480003641c6000560020002c0080d104007400b403100a06003458001000b050030443c0709000030b424000c4940c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602189523 1250 602188273 602188289
    0x70b0a050703080609070815010212160308011a09010c02011704060e074e0803040201031802010f0e1809030705060c130303030f02310603060e0f040f0c 67
    0x28076a1140350040451070000c1c0007034840e0548400780007940d80c0c00b00c041c55100b4214002c0b02008140200140d151022140b40c1c60414040091003207040d080100042c1d8455110361520011641c0f981100500c1e4088040d101034580002d01c400c400c40e40c49a28004034440c0181005c062001151040c6c4d03644480c111409c0da00300b031701c07103544c82e130b48900c20040c0d50000d148820982c0701250104842c00c18918400c90010b5030060301c20450050f280b82c1640882c42c1c0c1d4015a030b00902c5002500d0a44c0c100d41048405a02191034100c1907021650420465010300d0390503500d40910b076850000680d04034454115503a000022800140300403d5002c031617501551840e4011a210159031030018544080148011441401441110203022408254006495060502040304600000741000901988640b44c0e01c10881d170a051001d5017440200020191600c490400859150340050702680c040b840b0b0080d9883c00d00c00000c0100550324601500103210b910003c40541080d2202c42c51102e003074100700c00b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602190773 1250 602189523 602189527
    0x50604050f030c030306090408040e010f06030b101e03110711030c010e100807230306010f2109080409060e070e0301051e1015030204030302010509120301031202070b0a05 75
    0x10901600300700c0800300110240c0210b1906042108040d26400050000d0780904500000b103030401a100c4141c4014055001d82000c2d0707507a4030109040c4050341072284034042403030000e00345005d00300082c04d01a1580780d03172101c0c402a002ca004c581c540600280c03945003003540d1020710fa13040a06601c0180000d60142c008020892001c41c2010b050010a804960621120304120407083d103d4a410300340f6042a400c01402c1540c51900a6401017900c04920151003415008070440355450b60195014000c280d84845c2291076910301a1098105c05007952800030301c840440b9a149400d400002540e8400d00255060982e2504c2c1882030f200e00c0e821000e0300e60100320400100540c80594941e802d00114001e11990a01c0d2090450213544070441c1d0100b942900c0008170440c0003449448010300700101d281950389100b00004000b5009400114010750038140810300c00d182c009034007420b1040b0640702302d10b10307441e683ea0140d1615812030b1203030560040c48400605421504060685800682c171011707 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602192023 1250 602190773 602190781
    0x15200d08060402130317210f0601090e0c1c02040f05091302010806010806010c0b0103030513090e03031f030f030c1e031d0d050a123504030c0f0506 65
    0xd4425500206000d000714414130100390558030001c0d0350400c4a8021656403001246a00901c031135104110800403004254528404051400c103046440b130340050320040d0450310f4100044500315603034420040040104c10220b0001c00500004184241a00c90851940355218030500103a0300964440c4c144204098410030840c10490440f0341d020082c0c15041112000c0d50b400030709070f01030150559040000140000e51164050620482030700e8110000070381c150303964503000303180354843c0740390010000c800c410020b1240c0c454000c000e20180d90201544c02c581da00c100c10021b0b05000075480c0489d14841000102103500082c1c12207005000b940c4000315100d05080000c028624103454074040400764601d9000300354840c80c000d070050440743d0060008181c440000b0318280d01442c018016001e03018004007009000701d00c803590b28485458082251b81910312440c03401e629411381406841c031140c0d8010034000100900c5034414230a0074180e0f00342c0141e1f159400708200504044400c1d501040500c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602193273 1250 602192023 602192027
    0x150f01080d050c1504080708030a0f0e07060804080918010f0303020c100215150a120203010f060510030203090114010b0c1612020607060914250f15200d 67
    0x3107400700c0a0a00d1403502c0105040d0f144d03582d2070104e40000d41c45201010904104000c0e04517248203400080258407401c2a4400d840240b102c0505c43c072281c0c0c0b070070800105e100000300789a003c43c0e100d80c5a01c1143d5485484180e410390095010301d0303000d540c10100c10300b440b20200c3d40318082c0c0f5002038103100031811460040c0c5003044000525100e17082d20141d029005a001425241140e008000c50840344c56000008583c4074441600320340c000104100410301303c10840000020500860085c01455228903410003140c405003d01900400240301080344940607400461304a14004000a101034400140306841902a0001c0011020001d000228074a08100050b5880466031940103018500b05100c3c3c0b070f026204800a0180701e000c01c040090000d03130343c01b000f00c141c0c104110711800c0381036800e105d44510031411028140302c3c030300b40d80c0d4000c40f040c0b0b4020000d5601e07070610002d40d141015400c9100408065500c02041140b10a000400500070300100100104000030603211482c4600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602194523 1250 602193273 602193283
    0x3141204350a20010e0102090406140901030f03051603050c0f0c09160504030210081902040e1302030f070b1801050304080703050c030f0c060f180705040c02150f0108 73
    0x4011051124032110200c1c468010049400440090401c509014140950030015000f070852003030300c0d0b5103484c51007049464190010300780344108440c2001176948502c1c0364240c1280011940e50400c07421001031000a50446c511108540130b030412500300940c1b1004403032401003111040780026008103c10440300d10400403416441100806018440b1500e4007240c40e03040020501040400c64103025010f60380680203c601850300074144061031820050082c101000c1901e85840090440d06070910390300451003540c003955004641c1c91629110000415107040d03408001383d03414050090010303629403040090000a001c1c5d0404951524102c071032800c4d11034000107405040c01010401c10000039005011a444036915081a580b00d90b00441c0c42c81c0796009001e120444148000b0343c5038040840020520b103e20402d00c41320000e0350354044128035007040c0d03400740d800c03a600508060040d807806400070722204d4010303c101c038400c12506c3c0c1c407080b90603c180c0754540c0400202c0014030002e44184a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602195773 1250 602194523 602194583
    0x2030702090c19120e151006081909021c0b090d030606091815030305041415090f04021c1b0e06071205041a03150a08070303141204 58
    0x1061410030f490414107032903a401d0700100004100007205442411401c1d40e2010600400f514119101c860035004010448103054a00c1d10917031391007050006031984106503e0344141031006006c0300d81c01c41c0040e02000746c800450100da0000c0c51180c0b4040b40e0200d11800c00090703008408c001c0e514103144070800e00b025220f0180c40d00b00340c00c0003c103001d115048035032602285c468040d00e903c80260720180e2401440d18807161038441400d0403000080c0340d07008001c0e100380e890500700e20700412002801c11103084d000a601c0c07401c140c803c4c8000c1615180c482d100002c0c1080290015207443d1840c0c1180000520903048000382595820603c00e070802d0b5109194004061400d0500b071805e2503030000750300760044060041c0400d44c00c40704440c2d81d8ac803e009a41c01003401d0b0540c050b0403614070035441903c2c2c10403600300f0500041103080b0364040c80c11003150000c583d0700038081e04201d82162400c40e0a0002a1501d10b6550401c1040c0c100b03200c00b1400c1c00d8800d40c050074403522004495000143c80c07505402c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602197023 1250 602195773 602195791
    0x320030a09060e060606120405150c040603050106030b09070e030c0301060603140604061d0901090f060e0c03060c0a050f0f07060212090c0307060305090f01060608060a0b0c0c010323070203070209 86
    0xc10484c0d59101c90080740c2c4039540d000340c0300c00aa90346243c09468202d00d00750340d001c0e1070752b1102401070032060100030740103550b100e0300d0501841c1e0f214003048044413030900c0d2250b8004820700225004a0060300125460040541594002d007a4039021a094800d01d50003840026619405a440c41401040003a000b0900311400e00c00c03240b501824046520034800e02e00c03c0c0c0500600072a108410950000d007107203502c0004200130046c05d040010050005000c1580c060040c400c00c1000307440c3c0030881d1441443d00002d101d040c001e400000b2601c1d074110350707680141c50400b08140e9005003c0341c405481014400c20000d80c1e62108040075126180c1d0182012090746c0c40400a07900d541c4e0041039482c191440c0d40b070300207456550590400c2c603214003e0400910b65182c80da01184242c0d2000b00345204200607500502d19942d9061081c10b24400c071a14089141c00480fa41d06156100303030000304039804200300900883c0380341007a4440c02c1c04191140360250740005546821810200f41c0581d001030a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602198273 1250 602197023 602197033
    0x62520060615090604050909030705010e1006060239060f0a09060c0f08030c0d050406091101020708060f090304050a300f030c02220b0a0e10060320030a09060e 70
    0x19002040c01c4c5c0c000c2e40500c0c2c5c480e116550001e07900400402c25a590035802c00300a100700494200780c2525105408817841300c0c80c0c1813072408a061400002c0102c800c00300a0050965601c2261854103030101703a1020a00707502c402004140d044d5200405011000e065043d00ca03540d030400340d0060003001c15503019000384120745811030003003071031398060350b0b20550000d0060303a0302c0d541c00244d004240328101600b48624600400c0c4002c0c06403583c00f0200c8948208000034050740c00b10016640c0e19564465284079030720080028401b1217071002e060f9007001041080b2400d180c0c40307100007420f110442d0803100060360240480e00901c1032600700c80701444e07c142c91115264420742c40d1032080301d10000e0041c0c2032004400501c000c5446002100f241e5845c4c2c81240e17a40f03055008140300c00387c002e03a005d02b84036951800c0d021403100d00c60800d00d070103101071120f507641c62440c084069021b4042c0200d04080b807100820350800a40849004500c6218850320001e01600c0a18207041181c08250040100d5400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602199523 1250 602198273 602198287
    0x10c090519230102010b131e1a010c061d0f150c0403110310060f080c091618091509150e0a0b0a030807050303090d02062520060615 58
    0x5141681c4900c800107407001e10100c40c1c030b080181c0c0904010314284d500014080108998850241c0c07180811850011800b508400c0250450040d10440b28036807200f0448200607035030780e601400f213803115248108400b14000140203103000c0e0081c2030b1040b00380580c000e20714264690300140540040c5121800202009081000010102e8051030000500e5610121000032545e07808000044140343c0481040c08aa500c0340c3d241d0102c01c43c07900c2a00c0b403511848064004603d000010303e03109071490500b034001391140d424121400e809084945040800202c030124003426940502d8101c43d10480040b80c40070710f041da0041c00c45400c107500180c9803882d500140079800c0348200780c68102840c0302008c605c1c1e10750000021401c1842c0d49c0000c1424200151681c100304000c40514450b000d01007d40f03401c16030300c0380203907102e0504a0f1816040e455040411860f502e1000f0788218a00c0740b440c0504415907026101c4040450140040300b40382d00400404c031a51030182d04c05904800f20343c0e07080c0d04050b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602200773 1250 602199523 602199539
    0x3190e07050d060f06081608060103110907050f0310051206060a030b090304120c030c06051c090f050a06060f081f0c0c0203070b0307080c040305100518010c090519 72
    0x32150181e03612480b240c80d180c1080c09056004552900c0d501e21080003029502c0420750313659550000200c2c004000e00b03600089450300420014100c0750001006800d59001d4020060083d0b07000b08038100340714040c001ea1010303e4184000d94410200b110b4100022401d1208201814112000c5d1082962102d420083c0715290091076004613070b4442e505c01d00a0b15000e007030a0a6000d02d82108a85d0388400d01c20109115010110608890062080f050314541300c0c203084841348181440300011541e292a219001c20055000c14170b9280140112603040700c09a0300c240c1800101e00d03042e55803c1d16804140710030460740b40071400401440000b0311002c8050707c1c1c1001c01c104580c4003007a105640d000e90440082c0103120803030001e580281540c0e0404d0315010702e15116002134070100006020034000484417000304007210284e07500803006140214241d6103001c003400c80100540c1c00d480d10610800c01030300b824042c581e59406140c460814950510302442922030707898803010314070b4101d0358003004460703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602202023 1250 602200773 602200783
    0x30601050904110f030111070c150804020a0b0901020102090604090506010906030522020d050304080f01051b181f0309031403070e06031e1801201c0b040207050303190e 74
    0x900f0565203070140303080740e0000a0040080700d256030410301c400101082085840300e940340650304541450a02c1298a4408540c0c4035800c84000703401c440800828442c0451000150009030014400585030440c10380c0420f820717030010b0784590b0150341c64406201456800c19041e8019040e2031804010f00d01c3d021454050008109a00e02010562040d041043d03480c0c16059244058101c0c040fa0303038036541c0d030103195030361009000200615440c100c04508180e00002c002c0c7d134616140c05440c0d052840c0030380708a00809900c0007050344041d21b400712040d088114048003004407042d0b180051102c4240c1005040750546000b03d00c3c140b107042040000407608000f405803004800d07602c46899540d8040b00c004840c2c46040e1a01c05240704604000724070388051400311841240d40c0081c000d1020b8000b001003004030f0b880c008242018103000e02c20b1380300506c030b4010202400c40d9002055040003003012508a9020817801d0721300d0b41001003008081c0890100c00705066400c16410800c0d4041e00031803680318 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602203273 1250 602202023 602202053
    0x30302091c0c05060a020705030d0e120f15090313030506010602160e040f0201021014010303142703240a1b0801030807210c0201140a0c1b030c1202030601050904 71
    0x24413010441c1c818180c400c0081708080c0c40040c040b50010840008041c25228078400d004e44528288200100000c0003c100c8010100d1260014040905003900b200c11900c4018071003001c0d07110621118510034000b0305100700560040010b001d5650420a00078105003048804640610111500300603034000c1c1d044455006030050b82d1080b1895150ac0106e003815105406000e5160408805071200192200c3c5c95040728802c0d02d070303c030100451801c000c0081c02560400c100f64800500ca0464540d008080425090302c014142c2d0302d0440700b91204c1d00d00c0d5500741c00080c0e260740c0c50010030070400e50030b10800041804014052029a1304100300a21094050000406906011401500304042d0034021070b000c4d11121030b210b00080503420014841121030303030141d001a000d0030440725034180480c01c4403200c141d90b035985500380916072980c802001941c40c6800d50307103022035000404181e0b03086ca1080036001d441032131400c988582c01090303e40740040e004148518440c1080c13000081400b80da00c6070b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602204523 1250 602203273 602203279
    0x80d120e0c1206070e01030b0d020d14031b0f030408060114010509130b040f0506030c0d083109050c07030c14030c0d08160c1704090207030302091c0c05 67
    0x14804840d4881810050040800c41d00003204007041c5001d0100031410600c50141036582c0740c499022040110706856805d103003203400c080303803881c0500503040480e0000a81d038000e001c0010310b4030030440507501c0e680c41501b003007400c82c0400c29800c01e40c00051002c2e800110808005604141c20a9540b5480f0b000611940b0f42140100c148081182d0240d01a580c1c0480020400f20300042c000080c80060408030031024852458601003400151030307842000d006140140c0100b03585c05e003060a00024405910017560030120601c03811a107415a00407801c01001059280051401038800300384600040350014401c0e14145810002c0b8412200b086c3c64000e0340601e00950180da89040c65030344804800c1e5002c9440c0000540c0fa158031a0015000107819080e6585145c80c1c1e80d003421010400d0510314088001862004803100418103a85140a92035030f140012460280c0d18107c0c201240e002c124101c0100ba00401c1e03500356407600d82c030085040415500405d00c004000e60f1448103044241c060248 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602205773 1250 602204523 602204531
    0x2a15130b07050319062301110628020d0b03070906031110030b0a0b1b0604080906250516080105070804080a0c020d1401060b0403210c0b071701080d12 66
    0x80d01e0003001040845006240c2c0e03040214a4581031040c101820010200d801b800b01502d00d0105940b180d40110800605e52000e85600e8441c81d036441004403c042d1141c8451083c40090104812a88001c0003c000311542c00a0480404c0d03052500b0401d03207600003007060f46440810004541c5c810705600d40c0c0700d403ca45241a464444000b80c00a082203064a904072942140105519484c04020304500301100f000716008483c0084241d0f980200300c038000c000e81414000d401c0340b81483c0c07024090403106002070500032040d0060550035281d03104802e990a0b8403018213101c440c890b00c50b00e100944481c40c001e0140b440d00e241c024040d0000600000e0808070000356040ba018452081c10301c840e03900401454055105003401c40c03410003080d24080c3c0c294644203000540c402402c0403030f02140d078424501c07000d49070014045c203910000c00c0c50010a00601f84016000203110b42600d41c862482903c070740041440400c0d0408000d00143c000000700ea0082e00c0001c0b2441e00551a80d6038000a000045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602207023 1250 602205773 602205781
    0x12030617160b0a0509150c0102070b06120102090604030209060a050607060c0e0108070e010c150e03130b03010f0603270b090105070f0c06050907080a0f0b07020304060e062a15130b070503 82
    0x6d282c0b449104040946544042413100030070902040d5036004000c101c5819100c1c6c021503400745d00301d00c0390425041d40210100810001801e1031109182e005500074a160140d580e90804124964065141200c5003580c400291060f25008070103201e02d01002c1c03801020030318104001402c0310b01013806040c148031310700d450b00b0304100d0701c400c4001e080400310806100c4641c00391b607515030300d400c0340c0c220040346400c06d480030a8500d03072142502c2c12240050f002c010341d9441c058050700184680342d50b54695030000d070303a014070170080d6403c080c0d10a4419104124207240c140010b40c2103c0d005006a8100038078507130741c2c0842c9680400040645504410005070035103420101394031b41103059109040302c0c0030350785108052141807000300702c0310350003a603d842c06c503a9900e50880e00c030312642c0203440c081040c8800c11559420404e0141c541021130340d40c54500c0d000ca80428149542c450314607402583c1c010101209040b060424054129094280610b20300c112643c2e580201c92006217a134041240c044002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602208273 1250 602207023 602207059
    0xf06060d0b0316030510050f1b0702180105090a09020120010212070906090603021306030b0102010902310506030303070809070b030702030a030605010f090312030617160b0a0509 78
    0x4070070050001412a850640d40802030400314016210980c0c0070702484025500c112442d0280e24421407906640c094075a503010300b100200c00520000e42601101440090300503141c610103106031580300c03503046982d5858001045800d50000300f801442509055a050040c3d07040038600d03a64807081441841800d1030b10310800d00a00500c1402000d816007241484007241d0030030110380c2501c1480d9690100e49403265030036001d1340b02d10f48034018070340311061007040940c2c0703c0c0c3c5c010541010144000306500d2040d8000410000d441601c012001040c00d100c072508a13506007082900c0b0314048818010307450719070002a100c1c04010209014402d240e00010744880707090180801a245006c03805440f414102c800a5581e0852514000030a1800102041540c00743d50300b040b409860317655110700c990035592818002c0b83c600c509601450f841d0000460700da0210501c0947c80d01c01300c0d000784800c0c4800c103160100c074410341d4007a072480c080c1042280300980d440720803906002003d07200b584480c8040140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602209523 1250 602208273 602208281
    0xf06040b0606070b010b030103020114040e1f0801021305030c04110405130e030408012c0a1506050402360109270c0203070c0f182c1c0302030f06060d 66
    0x505070139607000040b80001150300914141d900030f036100c44004bd601d44e030499072481070303015003038007100035000085d4216008010f25003110803102011003000e50300c906150036600660200741000c1e40000d01800182801c1040010010007290107120380c8804c003c204003203114501415000f50314001c050301407042d05402c0103001110b2201200e1707850b80d55808140c000c20300c0108a030b001d8085803111812805142504903180140040034103030b1407445503200e9810240c2e54200060103030301e5000010707a655562014003000381c044034103045c184035544e503030420280e1202500981c00100d04100b10b4240da001d003000081c0c0f4495124070320708265203420800740c41422a58240518101080182c440c0c1d404000742407114440c100602c503058440c500c00b400464036004020001c914900c40140750112034100040c5a051415078a4604803001c011032100c016585216507640c0c031000301c09204404a40c00500348500c80c0c0340440c01c5080101d40c150758401c004c0d041e1481400c000c11280c60440903648 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602210773 1250 602209523 602209537
    0x13094107080a0b1b07080a05030403020f12071407120f0302070503030706090b13110f0d0c1203020609010b3109150c0302120402010809070f0b1b0f06040b0606 70
    0x100b01c4072050181d1405040c0c03401d08480850019090622441c0001840019100b50380c0e400300da900c0c03c00e180d56200b182c03550401402602148602d0f14041030100d400d10840102c0f20102c01056540c004074203050f112101ca070802d11f4100d52084004100100700107040c90405640a45130a0030030b219030034100e1404185411280c2c0c1404001003480c10040c82d9444424050310035140c0074000da4138046a080b038001e90800280c003506501a1207020b82c9010074000001c0380c0010920841e81456866245500b902608821103401040c038240c000d1540401510364007002200082c0325006241001c80c9601c088200030301c40b543c060804120180e541c05840d000b001c10465020084003c01d1f040100715a2010b03084845c100d483c1c5400150141e00c28022606ca54001c10103410082e15940d004440c0414018044003041c002d11070041011030b40d174940c00000304000c07070307000f900e400c85101c0200109840c0c907218440c5620414403101441d0000c01d00e5544150403440880716566880003040e9107200f03500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602212023 1250 602210773 602210789
    0x6080c210a0f0f0605070e0f090f2a070b040203060105090408070f06110c15010609060804081602120714060c0a0b0a0e0f10060f03081c0b13094107 65
    0x2e080107020340e402007c2c0f084800c002c8407400701d008912001d000c0f05003004e0303498015011800c40003d0000104026060400d4401c000210b00d0804408010a858101a4080366942034580a10080d86800c000c2503000d00303012a154141400c050b51407100520909000401c03905090010001340a0907900c050f0301c4114507654a5a210451701250b5281c5100b400d4040301c0815400000c00e03240e100d10f420310180c1c2c8054483c81d02a07101c54031a5410354000818640040c1c00309148280141c444405081c002468800200603942c100201c40c0b0200340b0751140607006800a00c1314600c60030002031540f801039003045090119031181d004913000350180b0510307400036200b48024200003100014510150400d604030401c80d080e19110111191000c40c48050141003050204645641110541101400c010107000030148104008107820702c0c0211807004e1501d540c3c2c00c032a001d0001082c1c49005920085010031118218219611104940c40c90281540200c422344010010803c12082020742400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602213273 1250 602212023 602212031
    0x3030b0a091404021e0d0602070f06021204050f03160b060a0b040f230f061602091513051006031e051f120305030601051c06080c210a0f0f06 62
    0x2c0d060141e251405640480c0a0400c081192032102030100380b07003d469400901e151440300e1240c0b2810040c2d04680c80c2950411f54142c00325000038140c4c4010f280c45100307405c03500d255140c90f0070514205000d40c44d007034805400401000303803428500c804005803a644a0040f200549801002c101c2d5804c15420500d00c5200021300400c4810088481e80111860401c80d9070192a208e1200003c10601420880d000480c0ca11840d4091031300002500c2a60045100c00c0308441d4035400181c017011068520b1660380d4103d4655a00d5410302c8154050f00d03010010041c481400c4c0811151018200351160408041c0c1d01c00c1d40d1851025292401c81007584e24a2042c4400d040240a0f10704ca801102070b0700a01241800c1e0024403800c0f007100c5029219059100c01c1c1c20b40c1d507904015500ba5015000007400b450201d0b044101c0c0721014841c40d000f034072009006251110021007480f51480c2d071032401004a4039902d6019018910000d00013480c0ca60016661046019524204ea03203027001a00052605041c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602214523 1250 602213273 602213291
    0x81b0a0b0108010b0f0f10111f06030b0c030615090114130f051c200303070501050f100e0a0e030c0303340f0309030e04241502030703030b0a09 63
    0xb054201d0492004200d4071844455a20001c0141907400c83c0d602d00c1e00b102e48521945031041c000c900400905400005860300d0070709600c3c43c5422407100c4461001e8841e42c0d95824014002c04c0443c03190b029000100705031850400000050302d100340c4824a890700d05000408101d5070740700c0c0034503442c0b0040f9010113070340b0f071070f0300f00c4481c180da00807409070a0003c480941e00184d5031500e0b150490781c800113001d18100c1e00003980c403170b00c01c480101004c0d22030500d42078011305099101080244031581c0500e0001a0b242405240f5110726039001d011400e440c40e0103481408040034031240103401a22110000442070110452141107001e624103448143c00301004000c03c4902c03001c040e103000404100b00414065003441c100314000d0400714983c0000300280c4118143e240a50b2199101c01e0080c1400304032072042c1e400003070a4032801c8007001942e0384141c80040c148080c14080d032018000180d4030803020f03114244002d40e24018000d0203000c00d51201c00b41341d40303a254076001074013030100d80c8024000801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602215773 1250 602214523 602214539
    0x20c0a06080a0e01020f27060f07050c040c0f0507050a1a040519080316210f1109060f0d0b030319122901020f0d0201060f060c081b0a0b01 61
    0xc8112202d41c509070800856110010040c401c80d031404200200c0c85080c2103007080d0541050f040c024013000c144032608500301080d03559402030607046030254022660b804444ca08541010b01e24800d240c051428041c0c4005490b8210441e82c41480d460f01e400d50301c940003424030900e040041000542504428015499101085c400c624030803230056003180d4080d031807141c1019008250090240c41c4d00b0707040c80854002c1017041c1400c070420074149841d4112490540e0701d242440b80c148031500001382e43e5a080080100e00d80180070705c1050000e0300f18284007a000100b41e15204090074400303951030002d4441b16081e20313903100d10b01c2184040d04a079211410000b074200c01318400154040403415100035401581424003480808201541c45001d002c01141c4000020840c02c1484d24154000c507425501407003c100070200d52099541d001280540c07402d00c21107461001c0750004402c20085560050101d441d04041f038000c2c0102c0f10b0303c1280f009048130020f05001322002c00901e580460800051424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602217023 1250 602215773 602215787
    0xe04150f14011e090e090a210e0a03020303040b09031c030903300509030c010906050117120405011409040504052505090a0c020f0604050601180c05070f03020c0a06 72
    0x402a210f005001401c5040e0303525081c0103507000390002d0b20408041c0610a1416505078000c92600221009164680d44200340404000780c0041c0303030003800c490800d5141d40700804442c980c40a8416407080d504640200e0b8492045000705403d0702000100d000e45038804016000507160907440012107403490220080150081680640001d00c01c1c1300e040c0604200f41081060154000d003001840550740344140014000050164106000500c00800712400030302484800702d2040d2000590b030741c1848441c00780c010840c0906010365118007581150350b090749080303a040c1c85007400d10034078113045505414014482c0c502d00756080350400052004000340000c10302d40300d910004a01818450602000030406100d2048540c0041c0510108a81c03e00c00d510031604080248140d40d004461070311301354540101030300c040300c5a510a4004021014000003150240c0440c100240230503405130000800740d00604101900011820b2514010103008200c0c0420550010304600c44566881c900a4802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602218273 1250 602217023 602217059
    0x1b012a14093007080c04060b071515030807050609060f150a12110405070201180204090807291015051b0d020f010b0904020d14010b09011211100e04150f 67
    0x42e11030382c0d030701e54071524040c0502010f40e440e02c0a19401c0427103031780303032064501201010050a40e0340c509680d03035540d01c4506208007840c007503410305030381c0d5074a0f2030110300d805401400079503950030101c180015a110600c0c5660005946200541d5601100d0300050030210740e0380c090740c09040105544000c00009000d00004048115010803103903643d000141d00340c8901c0b42070034461000351059040180360076071046201d103000f445220300f80001a942d402000003031f146242011880d040038810001d01d03900070f0030386c81650b0900c02d40095241690320605a1b00c5510340001b4000c0118080b00507030340004409000c40300903401c60310320150046010f902c82d100b4400640042d42445003910480c10548600d5018540c05800150302442ca40c0b01c3c51003201c40204444415501c818600300c075560f81d00d0000b80079040101454403843c426190840c114200300030030b01c0c05007001380c60360000c6075001a160361400d102560045100c240088240c5000e0160f0341280295201001020a91900b0b00104100ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602219523 1250 602218273 602218289
    0x90301020a0f110d08070f030f020c01200c0a0803060105091e10110d030c05040b03070e181302040f090f0807060507170406021b012a14093007 63
    0x7883c49a80307403544c8802c3c0d4400c00102155214011036a414030a960701c0c1d40e92401840c0001d1003101002c10401680e00c040f292154a130344502004044010468149000701c0000d9100c41c03429081000c0c0645550001c18041c01010003c0001542030340528219800042d009112000d041e00f00b202139440440b0316500e56014285105002c43da2500910ba13024140c48207070005d1290642003030044004d0a40760994004000c0140b0000a1106401c0b000d10b000c0c0f0950307140c105100c1c82c030700213001400b0b12007074100d9240d00b450404e2207202241c0c0c4440040c082d4065030040340801d4080c1c0014060488007070000c1c400071503200d202090011040140010901ca00c10910190711000012141c0d803090021054001e042c800200d00010155401050044220081c1c14414032000042a00f150404468a803242d0341c030030801c644408804020343c2c802c01c0c071818514102841710071182007500811201901502480714400340803c03090480c48640c2c3d6013a207440034181e00c0e01c80e049880312114030032019 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602220773 1250 602219523 602219537
    0x4060221071b080706180c121505060102070f03033b040b061c06031101020c0a061b060513060606050a050a12020f19090905071e090503030a0e090112081c02090301020a0f 75
    0x750248c406076608111504031410ba40541160351300e1000510000d41100d0640c4201000081c002102c0780980000713600a4564070a5403040050101c000004503071100141d0b00e01001c0c005144115074030202070060b050798000380203803240700424014424441000820460012154422a0b090f006403044c4ca2198605041d1449070b81b005990b6002d0881c0c04aa100309408403e000c028400c100c00c4007070448901c440c90b489041500d034113040701e40544034110b0b2006850850b105200d00750043e4402000c1074500646030181620700141907001d02c41c1e0420400c00c20004401b030600e0f140d0183c0e03070850708000b03000e580ca060305403043c04048144c0d40401c0124841c03035400600e0000621a4600c114100d40b154400c030302c0e15016003400041846951000d100600501081944003000500094005606c0c2d019003c44e0060811101d42d070f05038400f0b00c0040c0f1200d82e40c03000880354019a4032855079502c104071b003042850341d00e20181c0076801140380c040d0702c042425088250301040c03c81901e03c1c591240703d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602222023 1250 602220773 602220779
    0x9021308070b0304020a030f060207060c0f0809070e060d0201031b09050112021905090303120f06040f0506030a021002030408060a1a120a020105030a1404060221071b080706180c 78
    0x2210038042144d005c0d40c09407a519040010400305440d4005443c0b040c40b00518200442d03441c00100e03942a000e001c0091482c3c0401c0c0c0206804c10078041d00900160b00030700c40949401541c0030300c45801440e081c05003201d02c0c030b5a82103900a070851040070380c280c1782c0300b034450300940c00052410f4564451035001a480c07002c100e004440c240300303d8100c0c200c1865603400c1c3ea40001c0f41603c49030b104a0700c01c0e405110070030418ac410301603011440d0080c20041c5c0300c030809090a00400054514002a0b602a1403030541403100c5030782d0024011241540c151403031004000c83d08002e07411802551302064150240b44104034001100e907000303002c0303c0b04040e500c4101034055014840c4080206031840e1044d441560400d0240d8014805184d00088000d03001c46c100900d20340208500806480031103070340d40c0100e902d030580113242040c40c0b00314084107062481440d0400001b4004c0d21011140070010358409d240200303102502e0100d60b8269080001808040180e040d0310800106507501a6084e0000030b9001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602223273 1250 602222023 602222039
    0x10912050609011b0507030c0c0b0c010f11040807170a050312061905010c1b050301090302100614130c1b050a03090501050306011706040f3206090408130902130807 72
    0xe01103503c80e40d89950508213140d034242c8c2c445223144410707103500e18001c00c001440c0800000804400b086480080b4402c00403003041000c1d14101815400401c809010034015080005900c03c22106908c52a0340c2c141d01c103a071111309140001d10090411b0100080c09001c1141d41c882584c001d20041e100c202030068291003042640344c43d8050203002841e0681a440441e102d164812040b03224005100b50300c1e542d90700024211480813400310b015070840c10461000c554103200d52401000311040b940d001000c07010020fa400d05042e40c1c981000c90380c0c0d03189891110321484054044543d103c44000780300889041040c0d50303020001b011000140107440129840d440303141500e001e0390043c0c450082141d0450444029000014102e0b50055030f100a26803034069140170706810110031503012030702c1a0702012a259030203010459480000c5c540310a0000d030307403a0f5071a070f942d001f44c20680c402d8890359000c4887d5070110080e80018080750001c154007451403502d01c8000301b01c841d55000c54440315034948407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602224523 1250 602223273 602223311
    0x815090108160609060f050901021c170105030309090c070501060519031b0609050f010509090721021204060e160b040807050126070203120112031d0f010e01091205060901 75
    0x170300c5000451a04003078143c2c40c003c0002d4683c0b4401401507414003851140c1c1c0390b42ca1044203e0510000b01c215061401b001c0400e201709000d401c080d006980f0b0842ca40001c00c203180009003201007010400a03800061103400e5020300003409004041c1041030301030f08800746c0c09034141e001c10360f11a4404241c90407070003c2e003040e030030445005446001c00304d460003042154003000c00c002641801800c1210107416a15020410700c550165211213214400000001c00c1e001e010112003122241304003c06c0041d0401c0344e00c040c2e0301591040010601d680c290180c1070034211046140000340003145400329030344e002c91000d03100b610359031700c2101c2c9a540d440004440c040d00c0c102188603050405010a0381c1d0320002d46100394003d895004a038504075a0310b289a4510030241d11000e100200c002172641010781c44048103000c20f10304100d51040c3c0a40400144a60364452046030501100405070401d5900484a0000808041894030049496030400503203132182220044070b07075481c20800b4000e050560b86 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602225773 1250 602224523 602224529
    0x7050a02070519030c0b03070f0203030c03040b0c0c1b01030b1e04020f13030501020c010c0806130b010e12011409030f030106050c1207110429010815090108160609 72
    0x1000708842807030b00c1e061104072502000c2410606011030b5002c000304140a0148000f001c0645490ba900d140c9000010001407684035018110f40080003030109101001054980268200391849829141c941c140048c0c3c0c810b02510340f08a00414843c89101c07000b408226480e4507080e2028420800c000c0c003003048164551440d00042c0400646070140da0400758094000c030780c008001e25107801d440c007145103400b08841c1d2088940783c1d000a00c102d4100c100b805002e5610840b404c041803130b41461000903100c1016405400d0707400c0c1e0307110085a0a6882102d40405a0a0282081c000808908105806003191898108044580c1c23004203920038000000c81c2e0b0549940c1040c02d0469080000858059114440c103c51038891740310741d040c812035200c0c000e01c0a1840b40c8402441e050b1003030300344010b0344c5800913991600720040209a80d040a142e40941d0400003d20701400c0f1a910102105c03004800900120b80000e00740c1c0011940000c0000c401603407030704401e803550180340d4a81088990300e007940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602227023 1250 602225773 602225777
    0x40b03163b0f1e030705042d0b060901031815020d05010803030403020c0d0f0206040627080304050f0a12110a15050a0c050a0614060a210206031801090b010e07050a 72
    0x38004089410210f01d06402582c4010162405141d8441c001000e03034002c00600881c0c90741a15100003049580b2246081e500554030003800002e00020024025000340703044141850b4869100f8050350a502803d030b0540d9910005100d04070700d040448d14029000fa5086500b180d28140010480345000015a4410ba6042e4010200b0f02d04e494140304490003a10812941e113120300c111038005a480d0300180000d803020740d80300308036001a01c01002c440311801c03031a02100898620288000c01d004030440301036490655248851604480100d40810b40320340c00311246602400c403450801200440c00302481c00215800e02805441e07080e03607036030742a0722224400072030410803910403880d00513201c00e0b041c540142d054610071180c9071648401d4801d44018000604215020461b25151030118074000d800d26884550344103a003604a190640101100a0301c02d180102c0050000192861f4000103110040000d2100d14034500d8041c0c072800b001e00480010920110026190921500039210550741075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602228273 1250 602227023 602227039
    0xa0905010f0306020c2b030b1c0201140d020f1803070b043f02030708032a0a020a090c120b031b060d090b090d0203040b03163b0f 57
    0x42e560080298403144080825002d00074501b40344401da51000003040b204503058101c000108070b0020100c40c03210005511807030344101c0080011400c4142000340e41d60a080030008400c5640c0d029a0b90301481300034043c041c3c00061445103080c040005000e0b00c008541010451030307a88001c05031100018020500c4c2c0d05400c1c0010403a4143c21928618550a030740200c1f409117040c2501251041c42e801d60b1100d8403006020444218101004074900a1284002660410411020244200c0c0d2040d03d080e081c50388500085146480a0140010311980103040707079981681e40002d18050b0603c07148250100e203521a42c44840ba209000b070b007445041c01005050100900ca100e1409000c10002840c0c0208040c030031718140c226644a054003250003030240c2001441d1030905246480349180c1e0303020464000b40420080e103024501502c0c0c00000840126525000041045a01010040e0f1004180e0026854940e070aa130007100040e0510100d07900c0709200c850304052002d245107503a4115004244 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602229523 1250 602228273 602228279
    0x9180305070f0b010905040209090106050d0609110913140a030c0609150f0f11180d0809030610050f0a0e0a0c0315080c1206040b180a150b0a0905010f 66
    0x100d80001c00403107108840344000411591900700412509070028050265220144000c1d8644401c0c00ea41c0200383e00006d0142074140004200b0041c14040010709094540018404200c0c038801c0342c801000c0d000c1c0c0144182d140003d085a02000303208030640d0400d41030218000032071004681c680000d901a1140854222039035103120081c0031041c010b80c1c6010394000104c80201040c0225001901080380c00300f400c0d0301c0d030307014181103410411040c1e1510104001203c01c14841445080d030221046030520080c02c86400c14180c0c0d44125401c0c00d605006540400841111901841d01524800d5036040d00d40702ea214207000d41d04a49010f03c4081001c1c0d60001010f03016250012038035450b20f450041464051010b20f11348070a19500100a1500000d2804100b4244000d4100c0c070018584020001c60506454500c1c58200117003021540b48440d200e502d180c0380701003200022590303000c0041c00d2000b004044100007448100d0102d8803404c80004009020701540c0a140e050700d001c5a20700d810a86 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602230773 1250 602229523 602229527
    0x51509070f032a03061d071a090a08010906050a06050f030604140a06090602030609100e040305033610090c12060e07062d12050411040c09030606091803 67
    0x1649000b051643e50019608102c4042200400118491365020643c9408001c08848006451518038100c3d4001c020811010b01000050380b505168004810ba50b9041b01c00030801403100c1d908071300d00b150300380079044041000039805684500301122003003201d2034981c000c1140c0e540c203524045034543e1041011070702180d90110400d000c10000c80840d00c414210790340b84801d03210700030429117171580c1c00306c2080311500f4034942d01c0d81d012540c2d0260704441c904024043c006401d0103400034042000200c00214404804100920b403003003140001068481664540e000101c0d10f0304011509008004046100b24598055000e840d5401b10b940703c0a541082d428002511340c4030003d4508030b40380c0b80340e824066000d010420140503169288100c1d000280c942804d406020036007001d100000c0d100c102c1480d40d00c80001c942220241201085589403070604102001c17504000541c00703454580f001119681000381c1c0c2e01120b02c5201d0a0001c00d07034841a0314221b2300302c401c80800001d444042e00d00024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602232023 1250 602230773 602230793
    0x207050d033606050c0c0a0303020a020304050d050303090d21051b04060f0207051005070f060603140a110a03030f0c030c0b0a02090f0d150b040603020409051509070f03 74
    0x1036980d85000300d4010020302c2c2418940e0807890005540d900c02d44690502c2000c3c05100c1c0d1008850148030325058086101e030303a40c2c0900e02c0740070701003690105014092610a2084400400c40282a000d0310081401d02e01d44a0784295003521141c8200c50004580902810b400b0002c2c1c1d07040c506021243c3c2e04450110040c00008040100c5079217006041d00c00100620080d1015152903500d44601d010b6800d0080e2400700a030f004513124903150580d003c40140c1c07010440c8d400541c800c0503c1c0c0c2028031440c1a2020b81056000203148801c0d10304c600300b15640003d05141007501844800840c0b4003900d0910280c05803902020f00019280e4020b2142d007802088890500c0d80701e13182560045032240c0310b03000e10711015127100070700a400182d0043c0500c2c0002019604844c225264480b0b100d0650303178102e00c03a00703070317800e0710b81441c3c45400461055480741d00c480f00a5402500178007000340c1c6460072039141d40301c81a0620442c000c6002250310f2200000781a001d68217400c3c03000104d00c0c1542c41d003170196 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602233273 1250 602232023 602232041
    0x501030b31020c160e090625030b0409240b0303040306180516060816020c09090a02150a09080303010312200d170717040609080f030411040506040207050d03 69
    0x120780030803c800b4059420444d0252030401d400c0301080c01400d00403180812007000d040204503a010106000d041c1d86a0a060311840b001d00c2d83d07425030781c9844038040d030103018a03d0003ea44107252258030018402e0303600322455503c0c40000d242d00c03145000524402115489803a89406600c11b100c18070000b540e43d400301008034526000a60f0311403d81d900c0d146494844c0f0555020588950341c2040307140e40090f81250407409900c01880e13028100b86000b03688502d0550002c1c480c05081c40403545218051181704a00b540284c10303001c500c900403140c04403a82c06000c1140000d442c02c4c900041e401e2011094a040e00d41c440c14110103290f03029130450307198401441d140d0201c04c000a14a0780c0640070859601035181945482c030005820f5070200030503c1d401070205007409143c0051114649031441c01981c00303a0320007800151004a8140f200590261000108107114000103000a103c12190000b441144c229401d1140d641c80074240310a80c001c1e00e10003003103a070041d00c01c01900c5009800c50f003e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602234523 1250 602233273 602233369
    0x27030f070f02120c0a1703030f2509140a0305120306040f0612060c1803020603133207050108010506030603100203071d0906060712051201030305040501030b 69
    0x7540e0319800007031030014484088840c41d480480d50034640c2c20700e0300c4480001d080c00e100e41101040010042d540360f100080c540d04c12070000000080020030a00c486200710703076414141900c1074200d5100a0720346840c500a541e480031005a1840b03807440c000380b50100741c075070020190540741c174400b91401603604041c08903035100b61030700308046442040e48620b1740100340050410b035104c605401d00360200c504800c040b80c1040303580070f4580c00b20700e0701d1440d00048a606943d410f60320350f0340c008070390100d84002c2402000d1600b01c03441003201c1c000d0725a0300101c001c01164101c5a45045002c0c0d25030b10101441401d01251285004010f00e160110246600031000380540703100c204c05000c050200d920454246d4042090081090140b01c400105028142420340b0003031003c0c10610006116409200300c010301c221102900300d21618450010784001c2c0c2c002c0902c0c0182543c5038036025102d5009400313501e000916140076120703036107042d4401d5a0840c0c80c00385058800c852800140341c109800485401c3c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602235773 1250 602234523 602234543
    0x303140a140c0a050a0c0303030f110a050a02100f06061e0215061804120314010e13051509030405040e06160f0201020f0d0509160b1909170627030f07 66
    0x101144d010300160900710b204d8041c0803141811490701a044481c00e66001b0399040c40d009016003019144000c4915207441802c02d1a160400726408a10f4509001e184105e1b030750800c1c3d1006142c1c8200d400074020366010762224012a224181e03141c00c404041d000d1b100040c0d00c075144078039140045038484c42c1c10103005001001c805c0f100940100d03041c030081d030b411200f80e00001c1c03a620b042e651512900c42808c1c0c00d0289440554034100c079800d2101d001610140000045514000401404014225100c50700c0130021541c0c1c98821442a201e400910030280600c4c04c2c080d0310030070b448000c68290300c10444040848104911048101d4a60180410b40c00545d9030030460480203a15102c06042981858100801ca5103880003071982011748a00800f00d0022035840d061022600d101e0589000300c0b10302c0c130300740c1941d151000c0440b4a08030340d80c005402c0703c40400c80c54804c0345000c600b1921901d00640296070503045000281545120204003401e10b810900c0f000007607080120050402c0760058002c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602237023 1250 602235773 602235793
    0xd0e041a04020309071a04050a1511071203350c0408250906030215130b040801150e07020706030504080c030307020f01050f10090507110f070303140a140c 68
    0x41d040f039105440d5616a944420000c000c912000300c0c1200e10b02e040b00641d0ba0a29140001003034200b8020301800605490480700300c1260b5110781150f01042255100312044582d407800c020090704080d9505600040803021148a2000c590420541b0440204540780096004054170301302184003501e120307100034007040300080382d4208002800c0821591000b0151140807141c030149401102d038010321071203041040810240c1e0f92019070103c40c0400d01070710356903280010745d80241c0840d0398012420030140460007080b4140158000c1c42080c40c6852004c010035110308030405400411280e403c010b9016180510a4038401c0c1c02c1503070803a03c10a40c1c0c2d800c10210803655400c60300104c07a0b140041c0c1c0450742008911509000d415000003044140c040581407070101145004100c3c003401090380c0e150801320f0441403113016840b18400f0010252100381c41c07008000c68540c031041c8030a40000e004600000c5078000341104440038001c440e01e8007519040f08561000c800e41160403043e22502809180c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602238273 1250 602237023 602237029
    0x303070b1e430e1903030e0d0f08030f01050f0a030b010506160c0e190b09010302010f0e030d032903060406050403170403030f0609021911190f12020d0e041a 69
    0xb4030100455160b03030281c05080c0303003403011a040c0b500140c0144e4400320030030401b10750000b56280c013240701600d4a145000041c10030b901b41c110781c600300400c109030000c1002410a002c860040c140c54048910301d075045101c1c0c080180e03103041400082c02140e841d100400c45032908034001d050121540040d11300360706e10b42e150b94444014546c4101111131120f801c01020010302c403c1e0569030754034001c041040c25201c902154040205020080c140920a900d075101603001d00211400907600504840c6086c4501c00002e01400b038071140640070700001d1041c0c420a600314084e056880c07502800800ca03903070703940d1034103000b510b0043d00c19024414103070b854813003016005038018812400703034034042015982541e110703080362441e501c4540400d04c1800b40d09140360918000242c10075141c034200407aa0002e000a5042148001c140703603241042901200405c400311080e103041600614a50079032140e103e1050784c81d0f110746d55008000400c0c0d0015111503140a034000005102400c2d110340301030b5185804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602239523 1250 602238273 602238391
    0x12030c150a060e09030415092301140d0f0e0a0f0b04170d022115130e16030204150608040f05030f0c100b030d0504230303070b1e 57
    0x44e03402260000135013484115280ca99001116a103450845040c07403818a20742040c030810302800100d81c800c1c04542030b45a100d5114590201c103210025a6501802c0c41c0c4400145040001c84141c5400c0c582d140881e08400f01d0100280c980004443d100a08182e0b60088414801041212002914100b0305092180e510103041500c1511000595030000012244072200701444401d078591024010045215864131240040c00415520001010a500c0e120b03c00b904406c01c00c420140714401c52008080030142c066002c42e402601c0030009000d410100040c07030161401510042034544010a0000303151010310075000d4091025641070003400035071540207900480701114144d02044d1b107041c1c5000c140c443d5103000401100104020b034076510019000f03019038426203400640c3c08003480e181105100c1503840050004007503e580300c0051a01408564095403110b14000305000c56201d030140000c42c20380502c6484c0c0c0d450b0201d41c2c448800800c018228040000e0121220101404201d42c00071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602240773 1250 602239523 602239531
    0xb09190b03090d030f0c09120c050405130c0b03010e13080c03130510020f12072d0b0112020303160807210f021603020910080303041112030c150a060e 66
    0x301510743c46600302da008098800400b40c0c034140c14945000c1680c400c4d04007040904903807290403015030040c01030401401050f2070b50301c00d54000e07084c5001c02179492003003101004a40e100e0012201c80c01c0c0c40706014006400309000303d0100701c02c450040b8861080040c2c0088032140306009052805006510b180d0858002441985642410314424011482e200690380c6004085100a00041c65121002c50b070740c1e0800c5140c00e400c00c40002c2d140040c0140d088200380024060140f00d020409001c8000300071a0002c841070310040942c00020410011910103444015002401142004508180c4007203500300c02e20100c0b18100e0421018000800000000386031301d09e002107461071820040c4004d0480848048080c045404c03d050f1445040801c500c0c010641760181e6018071076070b48501ea040ca1490700c68100d081c0c5840040100001c000c0f841c03c2c4100002c0c015039000e4801309160340001d50324001e8a00071803a41d00490018040d403000b0307200360ba600c440807400200e6803564401035444e47c1e4500391 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602242023 1250 602240773 602240791
    0x100305070605090f040207050604231c0305071803020103151e050f030703081914030a0c17010308190e0604030b010f0614041a0f0a030b190b09190b03 66
    0x4900720100d45000c1207250154002a1170075807500550b5919251180781c02480107050301c1d95204d4101050340003034090784820558804480141e900b100c50003000d04500340004002071305000010310070600c5030810500568000d021070780c0450560340154003620a402c0503465031582d4250019500c00001401c0000e041107000700d000712420a01801451008240c4590180e03124404c10000142002d04485c5200e098818940c210f01107100119100303101e51086008480f00070040c00600c092581c0840f1190515032100050419080c00d441401d038803d01c0054404441401a640c1c0d5000003003543c0c025480510b03189000c030150600042c0301d80c10036042581c03500440e00042c800128440c0c0600050000c2c0d05008010003d86a0406940d10950082500b42c0c0c41c201c905151504010342610502694440000d8850180c500001d004144184400344504140404032440d80307a484000d10544008a192a241c204118180180d000c180d903484919a03042c1440040c9180c0440040c1d400b6001c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602243273 1250 602242023 602242027
    0x30109060513170f0f0c0709060f0f08010501051e03010b060408011e020f0417070f120302060612100e0c032d0706080403080411093c0609100305070605 67
    0x60708000f0715181242400a03903220b002c0114072440c407109800d03103414200400507180c3e02c08117103080d00c1c00c100081d400505058101200442d810b40c4600552050700c0002080d107980700e07aa04801400d8903000e100d00340e0482d542c1108540036000e0590320715201d01d009000402d8050090700441c21381e07405a884201c80365901c440c440c100c1054004400c83c002e03078a040a6003807400e20101010588190310592501032030075440c0c0002e030102802220000c0c2120050420103594030a40c01205020841080b40103004020005e00c0c0ea190160208448422800091071b14406202c020002861035440c3c00d42c00c0d21400e803004042c1d5034104919000c0002510182c110b14490203a002105074000000350300c1900a04028000203510006441e400381c0c05180603205919035082001b07a003c00000c40c076802c041200100850302c1587c2c00030740c07030105841040381c3c1e80d5007154003141d4080380c1a10803258240110004101c841c03404482241d0040c0b144544950066034950f901d6160126070390004010500c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602244523 1250 602243273 602243311
    0x2090a0603050f0c0c0f06010b0901170417090a0806090c010201060b03070f0336030f0c050307140c0603040c0312030207080a0c14070902030a05010503010b1c020301090605 76
    0x115008040041629080500403070511003181002c9400c0284448007510300030500c0f160184c0100451150501c0310816915256140c000d8031000d40e0201c264940894602c0380900c040e105540c01c41c03445560021181803c00d5042c00284000e58072a40c0400c0e40403103028004120b40105201d183d0182c05004001c0c40c858074500c0c00a07095407a0b51b400190003690602c1000000b5403c40113490401c0d94500e0000703510100120081c500019242c840300f07820090082c075040500c0070011820550b4082e4843c0345008001080c215089440a800142560410b200300c100203090310350101d0104440300e007500d2241c4020004903029402c1250141c641901c5080e0410034070030040c805c4005c03c00580303419803404500c1e8858003058895224224100f00075205100d040c03150421691611034901c030256201c295440c8072402c080e41007980d884140f035140078000600e5180507c50700d14440e5000e0080b40c020702940580014040540c0c000766015501c604e4507000051040c413070148214114140843e5442d0703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602245773 1250 602244523 602244529
    0x4240b090307151403040618030f030e0316141e03031918260408030d1a01020d1425150b0901170106030c090501080d03021903090602070210030209 65
    0x10309a0b0040f40064804040b400e01c10b54009104000c04c001ea52115a07240c9075880c1042c002c22940c0e944210b02444580301804066100004591f81d0715103540600c035040ca603400702a201d11542c5140c03031880b116911a000058450300307001c850700c541781090b5500c580d45001c0c090700c03840c0341401c002841d40000042154440c51910320114070307098080c0800c805009192808030b00614090060b1412040c0204004201c0104101ca03440c081303840c1071151150b540b04007480c4d40360452810010f494ac100110600054140c144200d141e0300140d004004080c1103403004d032031141c42c60001340c0307500c1c80811100e440c84030040401c1582c3c00c96000c2c0b90440741d0280c140110080c001c0810a00c0c100c0c10b1401d40070083e61110001c0b81544c011007546d070a0460401c0401c1e0040805900c0100300401c08580040d080d0856485581251000740640d00d607031002c010114101d226181c01e4a41d00400f4240380c42200d48607500c08001d0034407d800051401100fa0001405540030594041c0029000a12000c0c142 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602247023 1250 602245773 602245783
    0xb10090e2710020415031503021509030a0b011a0c0706082710060501110a060e010209130b0a0e1006030f331203020703020d0303140405060a060b0301080c04240b0903 73
    0x3000d486d0810000341d010406025100003031001920821041d0500000440c85e8802c444031144000d04480c03500b1080c0c034140c4541a02407240340744104800c105485014522412100000c02e41d1001c0c180a50618600341d90100c400b820b251404004000d400711408900700b82c2c0b804441422004103968140c02c0c1c0c1c1402601c82ca0b0300118100320341d4502d4545042000205800801e0b406400030030904240071000340240034684805510090041c0e2040c108440c0307034041d1035816000c1e144200e607035440d04500d00240b142030356006050042c004c0200a00c5200341d000c42c201c0d0890220210304034808400c4d000485040482d00c4001d810001d04400f030110744011080c0c001c002e018060030300c203005610046c2d00c038000c612000c2d02941280088504051195205041080c61812440b4140c241428007640c1c401044a83c003100c0c918014010407456071250a90741280c05110003003c00c140301c0d2052001400c17041c20071240e40b8280e00c0c004200c050a403c100000382000c0ca0041e078645514008240c070302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602248273 1250 602247023 602247059
    0x5060408011505060c0327040f022502010f08040201020c0901150e0a0803072009090304140406030c0b1309020a020f0c1813080f0d0b10090e27100204 66
    0x103000e0400c083c0020030b07404410394015402903e820200c032880107c2a1320058800321410780e0041c90070040915520069002d00841518154072584101f80c61000c000c0710884170380080d012a0701c50f01c6807440140308503070035940b151040c41030703c1c0c102c984a004203513031280c00e8119000c81001d001030160a26800465030742140011145000b400c0e00c3d1100094591145940190482480c048440407049080002080c1400045c140f1521490f10107001c035166042401200d02c1104407203801802c2d49094014042500d410103400b020503850904007189a17840701664410f2048088000a4010880d03c09040400b10503000382103200b18400030303030f800e10a016014038460941800c0849212407041030742a802260b160615a10200d2400d000416003e9841400c401c40d90005040c1e441c50b226800503841d200069a241c0000400800199044645405810290b11048002a2241034000303000a02e04540480c09005501d00022082c1405402c400b5820555000075081204081030806500d403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602249523 1250 602248273 602248279
    0x2a0305061302090a0c0c02031905070b1e0901120f06060215040c060e19060e12062a07060e070620030f0a11060a0504111005070204020d0605060408011505 68
    0x140e095a0000d0030f8100040d118003c00c41e550080740039501e00803c0d00da5003141e002800c4950881501f0419a80382d03080c00d03030840c0c4500a01800284112034503041d60500c81040414400100540c2c008903195007283d1005410061800380250a0306641e20420341078203a14030010401c9410040040c0c603008006a00641e001c0d403030020803021401094034282580e0952410305092030303201c00062041a0300c0010309a000c01c2c1c0f82c60000c1d0442e04110440d0922205035494420000f413a0b900d40c4c1c440701c013200c01ca0b0346020301d80c03d99071031100300507000140740e1404207010f0305002d182c4c0c4940b412070314000b41c09a40d991142d00c081c04515049400702c080740c01d4140381c1440702111382903d95124001d40b119402e1481c0045080d1504134042c20b84020040c040070102c880915056200201921050fa01610b070342d014081024507509000d810f414050006445e80c40c5085115030901000307500c2001000840b07541d40e0000310715651204003c000601c14040081090007000f45420744451690740146d01c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602250773 1250 602249523 602249551
    0x5060706050a0c020c061801050702030f01050a0b0f030a020d170a03060302030c040204120807030207090c210209010918021201031202010e01050f0f07020c03030f041a030103020d0206072a030506 86
    0x25506e1800b2510761034440442c000b8105800f40c01a5028003942c0402941801a003010fa58503110550000c0d1081b40026401d00c6101401020302480d20000c0c020960907402c042000f0b8094280251000350b020f10030108000c0c0d021106031701020b690480ca0700d041c00030b0380f03a006c2042545410850150b03299401c40d41189803c2c6894424145800b09150007031440d1004103500341414020f1111000404418505101d00030031100001d1410b1800250748031807042c000c140c1002480341d031007642c1030020107855640d010340c10084143c180b424080c040c500c18607000c018143e03001035a89800790017103100f080f03000c3c030241c400203020f0700795400c0401c0140d050b071404080009940e40d1024007600450b01101c241095168060224107007810701100b150548000103070f5010100c04d0078010002c0782d0380350a00c540c0038403035005180c4091100f03100183d48840700000320005850075400500c600f46c41610f248035400c80102c820282800140c0415035409400f110400600000748419070f40100000751002d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602252023 1250 602250773 602250793
    0xa020c0405010f030b071223130302060a1503050703060b090915150120061668030105040b180a0203070b1b0a030c031805060706050a0c02 61
    0x407002c41c0307040c0300140601a8080229920b28056100e07024041f40e480000c4c030805284200c51003000381c043c18041c0b01102c0b000001040d401000c216500355a916501070304594540f4030101001d0300450540c0780750541c0203a8000005070b82001040011482503101080b42a101c2c010032240009c01070070341c01c0640240900e50959501e480c80d440d446040c0c11041094409598012940103a900403501508000403500740c851030400a602d5101d034401102d1038403408503401c0110741101c0d00c0680b001000d19407440410000000c3c40c0115610070500720310b150880041881c0710080703000901c5500081802d200c0441582900d821110000c000540c0203000a04081c0e44030f00c030016000309802021074420142e1400314038107101e0380801c580c0007002c8400ca5520b4107864070302a404410400481d01801c42e040e46540c0b0007084440ca016016210740e40c07041259201943e5201d00541c0390104603809007004215680c03030401a06070140182c0c00000d4a10301600904222204c9001d0f5006641c403c0010b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602253273 1250 602252023 602252039
    0x1504050c07080d1109060a030905011a01020a151b0305190603030518040609091407091130010b07020306060303030621071502061b0423030f070b0a020c040501 70
    0x1103501c802140f000151007010058601e2450245510645e404180040c0c00c09000b54190002d82480380030380001c0182d00c12145420301030450300e0349094003582240c85294003040d407900425a1b0100c4103280480e000c0742801c10340540e01c9410405101181c3d0700e800f0310544d00b00078a0b9035242e2070b6800c001049058216100904039000f0b01440e034100061100001d01c054517250001001003110030f1040c0300b44030701450054000f500611a04500c3d10800c64001015919030080409006004800328900b510341016440480402c1d00024500c0c0603c491030882c8403d000c2d00d650003401e0a10400703449500c5841018140071000c1c03d05403090340140240100d6a5404095040d01c1c0e09019032001d0a402300d18005080c641e5950024100d00302004c0034018958000c00c110b0300c074141d068070905414403c0c010000c150b001c0c03401202224088800348101003051440e00400000005080300d800003084040130b49060400d41044d1102d6030003203203440049404210410301040212070910540d8181410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602254523 1250 602253273 602253277
    0xf090b070206013602030a060302151b012007050c1f03050f01050a12152406020601031104020a0219060e0106172112160905040209100806030c06031504050c0708 71
    0x180e000b1041c5d000001c2900e002c201da106100171039001d00f0403a419104a01854034540040f0a0403004412024807030100d2141131150300d140c09200c004000d40b08007402100c1c6816002407608491600c40c08140b808aa5100100f0440c54200d8002005030611000030090035104050304c28092215804014099940c9400e45041690954a0100d0411202e401c11b145440e0b05c14014400192030300303003907e41d442084102805c00d8039140c41451a42540d412049a030b8003001d11010304200740ca501e40e03080b02e181a40041000f4034903841210841071021014020840750120207c078010360b24601d0038200c10081c0128030003015820b60040010380c000c42c009450780204182c04141d8800560103000220040d41a01c010ba500c0d10248032261620404051680f244c00d100f41011520a07034001542d86031a00850340c0b82071000c2c140702840b1910080981e142013010b465160700d40144c0424203055241c00025601c41c440306580ca00c5558150130900041328070103406034451517010021580413620101c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602255773 1250 602254523 602254619
    0x42904120215190f05120c040503070f2702071a04020f0d020f0409170c0c0316060c0f050712050102190c03020a20210c010503090706030f090b07020601 67
    0x4c10748071040c0d186000316690300c01c07002c050014020131030510075801c910001600580c0e406a00f19102191520500118401244100d040c410a96207103035988043d80c5048501079481c410000d41022126035940013800c0c101c0321503500c45640d61f41040158a08146000d55a80054880181c2a01590041031940c25105c0700700340202c1e1120892820030104c010170324406a14440e4168544242d00750185d00e801c3d82040851203485440400801000e450400341c003110388030b4581c410b41c08a90f65a034040c1240d040b1068500d402a1000000c8007906100344402c401d02c40d100041c0d5480311116010446042061500d080003820140640000d4000403103421031904680112031072100c01e9043c004545500d14030b01e81150a418079615107210300360340c0090031031030001900c0c3c150098000444003400125080c1c8c01e1640f1203a41081954060307403050300194525003003c6140003060310313a0b4110100035525500141e214070010080700c0c4060310307107402546a181e81c507186c0501c81c8101c4040035003440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602257023 1250 602255773 602255777
    0x504170a2d060b13060e0403090f061b031202160203010e0a1112160b120a1e0b01020724200604020f0d020405240406050604290412021519 61
    0x20201c0d805680e07110140004c0c0c402c144824840e041d111004850300c80000e840850214900c001c1c0400d0300e9400b1082001980d0555440944464030080c00d910366281c1d001054003400040d40c3d40d40e0f12140140001d0500c000d18803140c10000d4001d1040c5402c54040e41e104000d0303504101c3e408800030726a10541650403e045514002840c0c65a180c00d080c0b0b9020940410300f503152040001e020512000902203110540600070400c0c0d40314000c0c0300680c0c110b142070141c01380764aa190000d000d031a80c000c104107401813048942880d21090061104c002402d0a8001c0e642d0701000c1d0158694882140030442c020a0703800c0e1990300d50990038036a80c6002809c024403600109002c100b40b6105c54071030480d40c2d03400800501c81810300000070503070400708085480c028020001820010b04040c0156021030b43c01410b12490f09180500c2202c00c0c18061840c1c4034242c19500100009124460141000d09951060881410014810800003021412a80100850a10420b41c03e4401200b202c02c1072a058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602258273 1250 602257023 602257031
    0xe01150603060806060d140d0c020916080402040203090f24060a120f080c1c020105061206011502010209061206030d140d09080f0d060512070e070c02010504170a2d06 73
    0x42c87c1c802c1d030341d40b17080321010360074803446000168943d40f140c0322011aa0003a201d064150b1165500ca4140401c5004500c0c003181c0c1020106005040c154002e41d4485c1480e4142d4001c0403c00000e241040d070740c038102001740703500307070100e00c2a0184015401e03800040480b0130080031481d10030708410348412444060084a001c0e1103500621144030100e0b482522400141c0b90040a1000340480030318000700624010740c0303024005525410318010300389000000c0702c0148042ea00c0c0c41d40300815080e10b2042801195000d00455a007500c0b458003402551240f0900ea8040d4608034041c103191021546a81c02048954520440545120750846c1c00d071104041e40480e250f046410120300601c10304868100101c80010b400c0c455000961212040c1c038000c40700003581000c8660802d07501d4070300c0c0c05880803c825000c0070588482c0034030600c071200c43c41030500d20706090b683c0d0361000420310610f008000903000905040200194074070240e400d0940c3d84c5403d1401000100e0100521221000c028100307555 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602259523 1250 602258273 602258299
    0x209090106050c01060506041805070318020913080a09032604140a0b2d130509070e040507031e0908090d110402030a0c020f07030201020604080306010c05010e0115060306080606 78
    0xb080d01701101406000d014076030b032180d88030402c440980362180c10681c0305142001080320144a4040c15040015011002c416040240c00700032030418058030710207854034270b0440c05000501490191541050070b4071241501362540c140602c0d062100c0152000c1c002d40d1340e140c6101e11840718284c909441c801001a000440800e01141d45e0061981007613002c0700000c21441d008000700d11521040040c490031490b030804140305486031502400940c0b0003001ca1480e0b0500160910f21401a4003001500c0d00300710404a000105085900c203480940000e503c2d110352041d202504c2c1012411020304410400c159001074644c00d041e4018803c0c10b82c401c1ea40b1a0914050080300381400c1d0400740024070031941d9003401a0203400070100c8291060141c081d442070000c004001045100440e50103802803c440e90700c969507600700340e000400345410b002c03800c0d03499008281c0034402c81000c10f5460700001358002594913058900c1040c0d501c0079042600b080003d1000c4203000c03a0054100d042a40d0449140304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602260773 1250 602259523 602259547
    0xe01120c0c0303020a1106190b03161203021005070804020901080d0903060b030106051305150108190209130c030c09050a1409040f020310050601090e25051605071701020909010605 79
    0x40c0b85045046c041c8076880c28400c003100c072003003112403001030000c04102c1110010203054a0345154001d00c40e4a042c4018100f100707100c0c0c800c0c07016102c0d20902c1910300101c64441d07440100c0e101a5007450001d00d5510030031045042210001e0301501e00d0500030009121f02d0007000301058910301004100c10703110600d80355136803005d4000310090304000b40b06450a40002c2d51170030042008445000400c000c52a1b0020594018511300e401021a0003103502c1420910030154007940c410040240c01c8120b0807149000b0096a108548490728a07aa01013181088218010280103454101a1146d072105a0401213038407009803043d4151b40940d9980115a25818000041415490080d4040c0202e409002c052a4140d0289210341426268617003100d8440010b860483c00c110385909070082c441c03079007403010b289000102500a64525045243c800f00300c40d0841064103205d070466242d40060341c18802c120001e006414480705041c002c605100071880080d42005040c4900b00921500056420101c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602262023 1250 602260773 602260787
    0x31e0b120316170703140307090b0711010f08330d1b09110d1a03010609020a110303060a27020a05210c030c0f070f030e01120c0c0303020a 61
    0x20046030650380c407a03074495000d00700d00055110441d80200e030294140c181c41d01c684140c4206035095618680d050201e4040342c5144e500160042091140b8032800184c4103083c02c00414007240f107150342242d032030700300341c00075141c00c0b140700c05a014464003004000c40c81206400050442e8083c800b0a40760a240040d020480200b8050b1190050016250803083c4807104500303102d4840300f40c0d03101340c0c0030365940c0d240400c5404400700e0303108481d410410001c5140380c81d0040d1100f890b03005a403218200200c00000d0031514240c6c03008c180160041900c0a40d260450f01e01d080d103266501c051807440c6000400148402d10500809200d00c0307114440c520181000d481001e22035403802c0c021583c4056010740039003581c2206032030600440b41007018940d8144065003030b50289032020f81540c00c6444840f880055600100f08035000d0060030f00103030700407030303204408510214000c0c1c4581052103004000101901c05580d5811040e5081410b6504441d03030210358072400e5501407a0060700c811900008444034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602263273 1250 602262023 602262049
    0xd03050702090c041703070302070e090c0a03030809010b01090f27140103110d0b0106120b090408040306180b01030308101d190605010203090f12120304050d031e0b 72
    0x1c10910003c0000740e91400c0001c0c0141c4400c4a140f450a80c45841c0d182d90301c1c860420000d0040c1c1040804102242403481c20319088071454023511000100800400d822060a41c025000111103000384203040c00203214401288030b081c81d00c4d840850405030402655403991140d6002521160020010b14104140581010340d40c0301c001d00c02d81321011000e50010380203000569907418188100f101c42e142008400d2100786c0d1024607143e041c0e2030300c44262a10201c11001d0000c0645a001820566980d0292341d845144500b207001c1c2c03541c0c1507052000440d00d000c4805003103641024002d2021848003a02141100c0d45450031700c080c1d42d54a0070410311580c107944980001c501c1c005280c0000ba0140744054850750900104940c0c000180d090301c4162580f40c802d06000d80c20800c5641068145008481a06000603103011144101d44100c0b91070700da00d2600500c91007001105010400005204020003106c840c0340074440b014940782002c3e04040c040c20510300b81a66142c5440c000d44426a8a00d14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602264523 1250 602263273 602263279
    0x1d04020307180f06090212041101050405030313170102070b24060307031a030606012001021308031b0309101b0c182913020903120a02010b0a0b090d03050702 69
    0x90814407500d080241c90400c1c0c10f000c0703141c10080042464185803080d12050581210b01c0390700c0b52030300c3c3c80f004408030340b0510650410804200116050b00d0820050000a82c01544250602d182401141d030341901d81464942503401080104081003403241030b0740d0085011080e100b42c00d001540320f1511603803052401600403402000304042d558142c1e01102021101e0644806141982010035440c1c079411070302305010070751044048000c80000901c42d00c08010b40c2000526282c00e100702441c101801784c0c0302c9840c0360f03c0000c1c600d17407460203102006150075000000310700304041a40015607081852068800704450001004400e03542c01584245243d0407440380e00807070740c98034030301b2021891007414000a20700b031074540c10300d0340c1410409041d0f0a8400c0f0360798190040007400c00c00e8504102c1504140c5a8003405400c3c8a40e8003403081420a061040c54695200002c40020f420360f40d907041d21900ca108003003802c2000812a0f0120707484010100e800c440c000c605ea190660302401001e4010350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602265773 1250 602264523 602264549
    0x102120a0915080f06090405100b0f0303190f02030f04060c080d0e06060a08060402060a050702060c1b04050a0e12090402040f120b010803070812040c0308120703060506041d04020307 80
    0x2d800c03500305440070300504c00440d8000140e40c543d010f00c0000380c41514018800d0f441b1404d002d0500da09a44401507a5200401c4500052005000285150020101c1283c1c0195130b00c0030900c01c613088801c2c0c0210003a09d0025601b06805640b030181580241d205800034000c01d01e40d100300700a0755404441c0b0b801e985a004000c40d5040b40344031942d070141200d00354000d1651103000701d0591400960301d84244d03402813840f450548200021140da0304070041c104e810513018082114903600510200780d03d03810321031510800c08000010001a190007501c100314a40c81c0070002d620600340424858910249164602e680b89115000300d8024130617503000d8030440c1101c2d18086245190410000205405001c94402c641d885010403900c074800d441e0000d04c2240c0c100582c01d201e20391000c0d440d52013800f442c692032003a0b55079101c052550b403080f079180150381a48010415000d805202c0d0401810341a145903040c00d0604000140c0c803004c810806500001c0c910000c3c00b10740c3c040240768041c1011a800722 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602267023 1250 602265773 602265809
    0x705150a060603060f030206090a120302100b01080f060904021f08040c0506191103040905010603020c100b060d021804020703020a0606050409020f040504050708120406030e0307020102120a09 84
    0x16014400d465039144a030401000040451003030140780c003600d03484428a20018507650070083c95612141041c0c0c1c000c0a24107000410504912078049101c0c02070300038282061a000b01003080350141c510403414004050240100010f96840d050f60105059580d0750141d01c1342d00015aa00c2d84c100705803403843e95110408600380c1c0e40944103500440c0303c0d1a003540700545460070010315004115000d20301e695201c145c3c5149030300c9a1080c0c0c20184044050340e02d402d84548412068900981200010a030006100601020100012030306400b00781c0341004403101ca0400901c6610a040261484580108091818000100a2040311500100115900e1200d49400783d02da241001c01521071925080000403181401d00640d1615507008203414440e01089003004000d0801400594a91198940c0404c00c0281003002c01015006c0071911b580b51031410400900340d0315001000e1307400e42c005225140050340c00282042c0c010172035070f942c06d444034120042120701000f1580131b591804140c520351 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602268273 1250 602267023 602267053
    0x30c020c030d0f0809210d06080633061b0c0306040302150a110702120313030602030613020f0d05071404090207140a03140c0c060d0608070e0c0306150705 68
    0xc0007001c00e0948a2850325560b00f01d001d0385854146c00c1e01052440c00b0304c82108050510b500034500c8002c0c0000020b045500d5410f280e00e041c01c101c4040300910b12030401c1d03100103c6442807020a48488201203c10280364001107420b0703001d80402d907065030700700360381010162200340004000320313201508560281c80c1500303001755034800614403015600c00b4180401c90844050048d013001840c2c2e0035030340e454a10300e50309005604000000d1491503000c01d0000382c41c560800030a8800540c061580541c403414504104103500401e06542c10300c2502c100701130365016941d41c0c2500c0006400800c000b8995481c04401e0b14030101051080a20880000380031803e03030001c1d40688280340c099600c1003142090509400c0c3d48240300207000d008500d05003070010562010324002c088507803c66050b0b402d40b94508012034150382010007a000c40c40c0d2910400d000c00e0700b042200301c0081c058161082101e050001240d2410301c00035140500034103007000b102a10440c0042140d1401e6070100c105c0300340e85804030032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602269523 1250 602268273 602268287
    0x203060c0d050906011a070309350c03120d020910020109050d0e0105030610030f020a0e030609060c0f2a0606091008100f15060507030215040b0403030c020c030d 71
    0x1500c0740c1c0e00e2600b404210758040000388541078801c0340704e0107289000e446500c041650820b0000314204040d0300400702d03060344198041e00d003030401450009940000d04003000311483c1b868202082a074040c0c1c02031a6a950005480042220069020f50340d40c100113251401900c5240c07480c83e0032901001903100369a42c150321000c8254081c000b07881c00d90f4080c540440d41000703804540ba00050080c00402d40a03c0c041e0032051601d00c440c100015803072015008141030f03800074010080801c003091181d150a080c18018258010713038000c017602c0301d45072208000a05000703560b1140030b003180c0814401881c404290b4843e03503000904825018040300e001c0300782d6840e202121400d00400c41003000c5407d503d0714100d50b00c00d8031a030b00c020f0403ea00c0468007103001000c40c00303001c9411903141c00c0e010f040d91607091504405005c12f030b9542c030f640d07080e0340c20060300c0c0c40340708085281d0101c807601c00c000c00303d81d00200305a0441d5040ca070100d500003006501300d19181052800c40d90600940710542c0d503164010310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602270773 1250 602269523 602269537
    0x71e0b16050316150504030503010312030e2d03120c18031905150108100207022803050613020d06020a0314090f0714061615020c0c0405161403070302070203060c 71
    0x221000d00070400ca13500000e80e181650024041101400184001002050039180703002c00e52500280d10500928200e103402c51514003800c9030081c0401c00b48140440d0304280e40442d60002c021842d20b1410100c007002e01c40024804111208049a6010900508001d82040c00e100a0448010031503c950604140f08280300440c0c00d40304014002d0070015040c10310904a940c0c42c005000140f0aa8040310044c0d8031090049a10040001090140c986015451403402c10b0f88428a52201d00b54600a45400f4018055861006031024400c006a850242d200d2940790b204030b0150301c1d4500c00d03074141c000d441c0262034401412158010800312400001d13a8191a812030003c031000642e40b02c45003030301030844030b60003900040f041001039804800c82c00403958603071240f0040680402e52000d00002c0307070440001900c07281c0083d1000000d0f403034140070305034014041400e1340001100d44c04019200001a80c02100c10310b50100004072407900990503141015005030030380e81580f80210007011280c2c0aa9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602272023 1250 602270773 602270783
    0xa09050c0d0c08040b0402090c0d02030901090c050a08210f0714071e09020901090803030907030302010c111e010b04020a0e040c0305010b04120203120c010905071e0b16050316 77
    0x2c0c521640a071040400351300480c0c11801e9030f0000c0d01c135a0207010f181c8100600c4114070344030070011a01c581040b84015032003441c486000088107801d0b403405e440c94203226440540f142101103400c1c8034117080070031030310860300010807104000c40c500d4074030701c845000e0030020482aa1000c1010b009200b10030200100011024050b81c4950340c50303c451b40b170a40300c000d90446242c4010390061203c0c1e15254002c01c2c020805040880100d9640c80d800303451640300702c459440b2600108020010550240902c41d842007450078107040048000d01c003156a540e01d00c44140790700110380510602144e0a60203d50300c000082d01c01c0d551040d10303450180000e816040070354010781c0b0704110161454444d02c2400e040e03411240842e841c2c9440c00e14841586940341406a80c14018484d459101810010080c0f0700b001c810b00001c544400385082442c103000e11a40000107042900744e4076403540319a20b03903480c2621896695a07444900b0501040d00e501d1041000401500c4001120f03000411500e00c12288035210f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602273273 1250 602272023 602272031
    0x31e0c030405060a060b07080c030c030418050a05070f051303170a021506060708030705091c02100f0207050409051e0303160e06030c030a020c01060b18040b030703030e0a09050c0d 79
    0x10f00c00b1481150780318030030200c0075030062000e2000524404010f1489e103140c807044a00b00031800d0052400c5901982c400c11828200f200d03d00c181c41100d000385984141900404c101d2480c200c070001d4001c03501305981608001c00080e84e01c01c0340381c41e40810700186030003840c6101908030104480240368000401400540308000d4004401e07491400307000d1086e003000e040c060600109036503802030740d000640402c05004041c448040e160302d0307a1070203441002c03450800021158003030041c40150400501e0721010081d851501c99003403500065100103c8000341c41c00141e508131418058280420500340c103a0a4606034400100040000007030b6001e044102d040f12603251003401c1c15100c0c1403c1d010072503049a014000182e0500081d805540c2c44a450b5502504e0100903190030340c00c4818942101c1c07924000404c99581c11003100585812648e02650104070300d20a060001c2c0d80c4003031078800141003101c4840889259110000854001d15003114248002d0505511a00b982e8210300c076140030b107500d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602274523 1250 602273273 602273281
    0xc1603020318090112030c080d0e0a06271b0504020d050103060b0a030312021303060c1e030e07091a061201080d0306060e010e01050c0a1b080601030512031e0c03040506 74
    0x82c00460341215000c0780c1d0801c850105c1d960a58458980003000d0341d040c0014403801a6190550003840c6150082d1409041504024607082c0100c503072410504110381145e18020b10300500e41d0002094032600555100402440000c000d81e403954140c011f150894000b02c3c100c0c2280c401908800d0580f4402c1e6001c2c008032a03080700b400840030f444c0c03101800143c10802005c000171019402030903985001400d2a00080d120740300c40085e69010641c410000741c5240107a090045156500403242c450f40c5400c0c03181c0c2d541540d0f202e6603000a801000c004564420000c805604000030001841300007a003c6c9850f40402e4401d589007460901c20700c50a4040c0c05411485107229200d401c0503600749890f010040c0010b80c00440d00003100b40050303070512034104101144440200242d00029114080700d134411aa042030140241c0c08030340c4107401c594400b80052000271000714204800383c0208044540342c0d560fa100d0610394280ca0342c1c444040420460074001862506d5000710301c070364001c0045450760b0b22 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602275773 1250 602274523 602274529
    0x30c0302100c1e05071502031902060114040e070e13030306050939040b090301150e0c03070c150911010804170a050d0f0b030d090302030a06050c1603020318 69
    0x503200c0040982c032600f107aa4180c00d458600112229003d0b40c103c440b06a03c69407007440e40c22402803ea030260b0f0011034005005505402c402480c40c03c54070191a865151241358a4240440e501991140361117405d001c1075550b0070030440004108a42010340c02d0300f070032404014035074030780700065000900b01640441d260401c5250315010f8108002810350842c18400420000a051040034051440b91509083c5c6d001400005c0c10143c14501d10301c60760303281101c2c105030031541ca8400c3c07140101c91002c4108040e5081946140d4002c11200442d0354a0382c84003000ca4a21101c043c006000400400c400081c900103903020600d2184119828000d00700080f005560000c1d0440c0c006104d80d50f00140d442282100c0405030050140c1410b0903402d02c01d24410b524152034940c800782c4c40350303a40d520b204005403908000c181c0d91701446060007244903080d500880d45a40425001411a948031004108607140c0c0340120341c2ca910707165000c80841c114910b0000c1d12948680d408552031003404440c003c0c4e5113 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602277023 1250 602275773 602275787
    0x102060108010b060d051509040602040f0f1d06010c150c1215060e0d0c03050a0b0c0a0801091d03191103091311160311070f080303130809030304030c030210 69
    0x58014556401c3c121061045e1001d4080101160b05442d00002914030039141e110406008500c101005600c0b5401c200d014a001e92207544850f20100320b800c010030103000003002000c0a034840080242c00780e62410300503106d03000c0740c03403004000030215170312190700701c41aa00001c101c4540b0360700c6002c0303038460401c2141903c9181c07204504900300d545041100c240a50010b484c2600060030003240d01d0025201c41d1480080e5034002e4403680c210341440004c0040c050605988220001d03a014281601c240d00105542030500540c04200c1c0e882c0504401300c9400c10780385005052040480740d80c0d480c407100c40742d10698403040d020f001c2a130a401c02c041030103001c01644da0b810310207400121803038950318070750010b40811150500d900004201c00b0640c40524a010310740d0324001c3d1039051140c07440c401d849203271400c40d600001e40380006000600241501108580c2c2111040042102c154518240400c1920945075065818400058004204400c0301c8400003101d008a038500643e640413503080e2584 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602278273 1250 602277023 602277041
    0x1110301060f030e101e05060105070506070e0105070b04080901020105090705010c0605040609060e0d08070305040f08090a08011503060e0c031504080904090609020f0a030c0512190809010206010801 87
    0x4203442c40c4107200d03014030990020b4840e40d00305081700c412000c801000c600700c580d1a041c802e0746281ca0b4000400480460245541016081c0ba0562034484903840d07464840d41c02502c200104103050000402e00c0c4c1c41001a20300540d081141581141040e1412640781c0d401001414055402d220014407403d5021031881c04440040e11040c100420aa40f030303800910380188200e0749259502101000319150b88255490034540c00000d1428148100300036040c000300400000406007407104200c0000c2c010748488038090b0b0710064040d04c80301d074140080c0c20700c511501715110030740c68445076981c0800300312820001c03240264401c100c44501f2030314064995440301041e82c1c055204a040f0740195041508031503115020f214041c3c01e2040b454002419a40015001d4420300e4172584c501040d480c2c0350051600350a000c940d20001311740744aea00c2c00f0020404d482128810364030050b1820b03000006001058a030b110410800b100d40e0b006113460707112a0070443c0440d0052003110b0000c0b035240380500c118401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602279523 1250 602278273 602278277
    0x916170603060c0a03060b0f03071d06191e0207060e090408090907140309100501050619080603070314210408030d180203191202031c0b01020a0203030304140111030106 74
    0x1143d54150350751140e41c0c031002c0d007001016540e10000540803864405403031003c140185842d520304005400415020504840410380c01c2004503103036031030303540c1400c403010103210100816001c0d507001c1069a200549808040c403907a4042c0c800d000155000c03911005642c0704c3d480c0c00503002034520174080c00d910110307001444401c00300001000f51500c400510750005c05441d007100c03404500d591a000e140c00603039108955a00004d070512a81e031030b5000e081d002d040f0550f0006e041c02580407840326100d41201000c000d00140c540130902c103840c00c2c0036030b0b0040c5400030b030501c61440c40070072915070f02c20b003421162000a00700381c0c3c80c0ca440e0840004540465681c1d0000710b0038042c802c0d101c0c4004004030000d190070030400c0b40d442401602d050055800310780001c10b0141e004400b5081200d03401040d0140d010464100b04100d40d540c0d4141880c0e6244111411000240c070071720400140c0c80c105403000040c0d41448044204800c1145401e4068183c1075a0402400444800c92190129010a01410380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 602280773 1250 602279523 602279533
    0x50f0106030e0703170f0708040f120203060601030c05131d0a05040201080c0c010914011d070b0f071104051602010e010c300c0f11030f0906030a0b0916170603 70
    0x1180d01941d410b0b16001607104a5480c6c03030000302c21004180e0151104468550340410200485004001c642008180540202042162541c00280c9070304000301024185980c640001954074498000d0768403070300140e1030400e211a101d0070512400d040840312108c9401c0d8540010b92003100900950b4055641a140c101003a2501a0a22490b4000c50401d02e001e41da59011840400d41c01c40c050102d03070307246000008820490902d03045030a404160301e802d2643c005002004590324420880d03019484480ca4151103054a141510341800342c940582e6015081400f440000e1648a401510f10b40e155002045260038201d280c2e400d03202c00c8144040401c1030303503010521480b24016104003c0b140f0645003a1310750900c2c0e00d840d003114440b903800000108051845070302c254008100740c40e558900c5000b5400c0c00b81959400d040e40c4204481c003070158802101240b50140c2c50f0f000200d44000007010043e45280003c4c000303a10700c050030184000507480e0421888503030060142c5034015000500902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 602282023 1250 602280773 602280779
    0x605130213030b180703110111060910090305040803040603060617010f030b091c080613140103060b03030708041e1706061e15030a0b030d020c04090602120a050f0106030e07 76
    0x34a03400a00004d9041c1c0e12440714a00c01c9400c0c0082400303140704041c15402d000981000401c5034491018845c22070b8480710612182e1007001403068458aa45100400c030034609160482c0c075801203501c910394034800400e020840c01d426421405c252401da40e110103040e450060800078200003803180c0045c1512500060002c605400f00065100410070100e038032500c4090070110403407860f002058002900c500501c00d1510303118101c00c00d01131804405115142000b04a0349050701e06210080020781c0c2c85410f4105902d083c002e494a881d00300e0001038a860f50381601c081c40c10003100e81141c10038401440400c1c1c40020311003d4030b03003940300340081100b90b0300c03207051190f4581c02c2001754912a203000c6400b00240c0e00cbe0388044201c0300c820880140c803401c1200300c10054802116070705e41302c0c2d0010a007107946150f0000ea90f011324141203070042045103980c140340c030081c070505001c83d034600e0070710b01000f01c41ca44981000c2d000310500b0b108010142e0369036501320300b10345065090010340d40000f9010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 602283273 1250 602282023 602282033
    0x1020a1e03140c0a060e0f060c03070306030506011e06050c0d030b060405030106090f1d0d121b0f09080c0f040b0f0306180706021207060f0915060513021303 69
    0x100341030340c0c070a00b8080480030341c80082c0301c0903800c007540d01c8066901110800c000c01509000c2c00200302d140c800101203100300b907512640c403802c00410303428031140e02000182065100303401c100000c40d00f060560307010f540c5a207035046000c1001c100d2084000c0701c401300000c4d40d0307100d1011980c1c0d203504040901140d000700c06027140984118800158850420f02000c0f41a90303080c403c0e007005100300b4100162801801e015403003a51441099070324a8250300480401d54a000f05a03506c04400900e0140c010350800002540280007680a800e81e904100c4041212140c001d03650201001041c2c0307030030002603903a10155548203420601c1c1a008182080002c00908090304002e211100c007c00c1701001200300310229241c06821103101300c22030070f00c44198805240c24040007002d40a1480603001400f40704240d0b404900c103509005040c0340c5e4401c507410b08404543e01101819500101301c0014401902c10740010304918004c0e07a11030224030906d040c07074800340c0c42180c44010040c140c0841c0c1034515164 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 602284523 1250 602283273 602283323
    0x4111008220b070203071407050f0625030c0b090f07050114040e040c050a141f02010e07260106080d050309070b0c060a0e01151a0705060a051501020a 66
    0x41000c00e16400c092500002c0d8400003041c49509564010343d220002410030140220751040e100045070010769041c49aa01c0328000308803404001d5a8040d520300c9110300c1c10a003092a002c46001007541c2c16090002c0540c4481541401402420310104507210407941c40d0322080c141201000507441400308002c194050f40f1140d020201c06502c19080039603841401320906001c4804643d0460b00000c00d00407890030450110240c4809016280340b801850003042085022a0200b103030300c0303081c0d154002414403d4005000302c2ca20382e8141c40c100781c3e89000089c103d22156400f02099a00a09808482241441040201e92165000308200e0030700d140140c3c0c0940c00980240d2440c0904600400c01e8042000107000d40000c0b0001042545400c0885900b103071402c0016800f07030390400c00e103045a2028455800c05a6900c0c00103222000c80d00903c01c5c1c40c621620800034014041c02c000c011654040344c0c0030601c95940710540624010742d8500498072021000d000501c240d1049004164400c102c0c91 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 602285773 1250 602284523 602284561
    0x3180b0606070c0f090c050c0706080604061d0609090c13021b070308040806010b0306132f040305010b030d0c240e1606110c0603090c09090604111008 66
    0x40700c0341c602180c0da1520f0120000e2500300205100d0001c0c410052400d0328803801c019402e00340f40241c100440d200c0f516443d560b86110303402c00c02881c407003c2800c40e55250710410042c10b1503141144800100c22007404040e8003200c240740f003102014005009420042404481d01100a200052501245416400179045480340803d59520403001c142c1555040010b45d010b1030145164a8459240894207031801d10142c00a00c4003c0e01030041c8001901c500c07000318183c0c00740201c0402c0c6456032021010f081e0304607204d42032440072030241d010710717a1886c0c8000b030007540d014000034002800c008041c155a02018100c0710300241e4048210340c0412040f2510100113031030141d400da6842c9039071041c0c400361095002181283e810924528048482c1f994850b0000c29290400d15140041d0174186030322883c0410005005210000000b104003400f40560301240700c009203034440c030b0704180c900716540d10700840301210140050492250945090034294200201543d12074000d66240c215001c82581048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 602287023 1250 602285773 602285779
    0xb04020f0412060603020a03080309160f06050d0f0203100311040e0a02101704060c03051003020a06030e100e0d0f1e110c03060403030c0906031407180902040b1903180b06 75
    0x404c080700581e030340b40d681002180034020054076800e0001009050086a04c803944800f030307025004000d413020f035003084011141c15040c4643c8074980f001080e0007601020340e601100510000410029403520800101079070300401000001548000a21044502c50072458109034440c021080040c80c1c031302c43c82c00780f184040c42d01c9014094880f45004040710247c130100c803060745440c000d00d0182d6061042e00e501000128890f41080c0c6180c0104610304081d01816041684802070440c0035102000b40086841100c0d0040000c084a59031481d1604002d80e010342c001019600ca45428510030a8a005c1c6000c0f0040c1c808440e03100d941090b036040100c04d500e41c0030790082c05413042c5581e50500045200324000c4c1c5001c9941c02e030804004117181d41581001052501e0807203004101190418015441101424401000c1e1241801e2010082080e403105540d2f900016004c1640d9400c40701400446c00c0440201c00705800700c5000f0f60664900941d9101508482900d803c0800c2c640c2600c250071030405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 602288273 1250 602287023 602287031
    0x7110604030606080109120201151a1b1c02030a12050601110a1b12030507060c09120503130b04050603070c0819020601080616080c03100504050114040b04020f041206 73
    0x242d55010a0322459032045071030740d54800904003031007940c03400460341982d648001c000c8502c440300d02038445420f1340160810883d03240210038010344081c040b911030035000c4a04d520065100b5401581d00c0d030f03081428130040c146049035184241d00000607145482810744540600080d000003100041c2001440381e410400043c443e100000d106001c4000d5081c0a042c025103130b0748070b80f840d4140c0549103610205a104180340082e011a070f1060588004690041000c075400b1144c450440c0c40c440175030048044281c101c0641c5d800c00000000900003400c200d048040681e9845c20010305900585c850190802c030104002550300d0300ca40709142c0290301c40d07040345042c0ba140390181c00f1054102c100000140e402070f0014800700307404020041d4040ca5a00307001100d800e4510303000344014800f40c00c000b0341e9040070000c038111111076440e14028000142080010390f0f5100d41c40711008410052a6014529041d00408141828021501c450445c0307a44180f5042c0f03003110000101004040503640d00303a032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 602289523 1250 602288273 602288279
    0x60b010203070209070c0203010515010f0c050a0b010e01060905030303041205072d06050906061f12020a0305061207030201021b061213020915010e010f110d0f02010e01020f07110604 80
    0x302e440c0c00703002e90f505e43d07100c5003a00c0c1140305041c0ac4800181c00714140641850b1900140d0f0791041d6221550f13403e0f0702c1c04000d034080c1403400c185006420b080c000d1180700960000300d09104103408c3d0724101e608a650b0082820343d11800d1640300d11050720003404103400700858001c0c0d81c1c010402015454030804955003001d1341140c03019845402c1e0f1585c01c01c1d200c04019560240102c50040f13542060766040646110300f40f2000146039031002440c900c40d203141c0b10fa4404a418011541d001c040b05454405543c0e8603508507004000f04000c464082c401c3c0f40d0405600310b012030000740201942d6040c1c00401881c0245030301108506000751599038440d20401c80c030011501c80b07500c042e02034407003025800c8005141d8410040210b60080c5038082d02c010709541900d643c1e80c0305810000c04242030078010703c00e110891040399140000f2101c0000341c400c950402c02242d80c460b40c40b040c6c0c0c0f032090f40200f10b80ba0744100b00d5401c0c2c1c030404140c200d00c490300323004030b80104503080f10303124609400600e02468035079 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 602290773 1250 602289523 602289529
    0x303260106050415110d1211090f0d02010c08160303060e060102060a02032a0c0c1f030b0f030303040c0f05181602011518050c070f11040b19080d1b060b0102030702 72
    0x2c400034002800b019182c9401f105240121391809580700103c0b41001240c00101d420398906040c1740344135142c1007160406690152000302416034000da03c15a0315070041c02050003102009604400007131814000103059002c20701068000c44059010344041d4a50a548002035007014140100c16040d42d43c01200e00301c180080450608408004551201b0702c10801d10b0500c0340072044640507065014402c1481d4201c0080c8459214843c200015a01c60b1000801d03a64241e12030465094030001040c441408800a00c80c02211605c1c002e041d45281c039034080c010101111071802a010160340c0c04248d686810611030b0081c40c90520000071355030304145400354501d00c25440070f4400c0c1c40010846075050301902a042e4002c2110013001d242c64a85c0c1e844a11b603050104e8040d22040800185004a581d1034010030394414000303202d20312038030210000d1101820144100105845420068401c0074020701c031213842400b90100c4070301c148e040e640300c640141403c1d56a160441c00308005580c0165 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 602292023 1250 602290773 602290783
    0x150e0304030c03050c19090519050a1418030901080417030403081f15030507110f031c1808030a1407030b0438040605040204030326010605041511 64
    0x18082c400b031400701c51641c1442c03030920050b01d445074014080e03100c1e20304c404605030003141c04035000c424002500c1d40c3c400402e0014690050b40041c216030820003072041040702604843c0b4083e844200c0283d0360f40b83d903a48401050031032042402d0030380061040d045c0d0366002d0780f00c16502c680151040c04050429640201e030680c001c540c11000700d0703040001c2c026040611031180107030b486401e41801010741803284440050050705070500425886400260032607105003481c1d00a41c036204120307500c600a140c110b580717a4101114003081c410031000c540450f0f403080e001c0d82c41741001140d0240c00000030ba8031130864550000700110f00098440d0074481c0481c58589035144540c0c801d60b80041c00880c00302c10001514003612000401c0c0c0014000e500440c0300e08103040131b0011981c1d004244605140011a01400241d0701056016202042c00414190081410700303c0c00d01554100c032960140c000e0b179124640085c01410009030060100740030001f0414500391802500c0c1c04d02c503503240752400c101d034501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 602293273 1250 602292023 602292029
    0x7120c022103010f170319120f0209030c18040602030417040806010e24041a0a030c061e0906080c04090c0e15040e04060b0609060703050915090d150e0304 68
    0x70300300000040184d40c95041076040981003108104400346600d001c0c2c17958a01500011801c0d0042c03180c04486514017802c91399000381e19080090141320301c3c802d0404002e401400150340240500072895046140c418646c0d00c01440f03407054000e0a48442e00e5290080d00000e0080326000b1074025081c10f003c02401c054001002c082e8010049503040054001b5002006444e000c0101003071360000c410004145181880241c8c2900d0000d900c14003c0e1020300144040340c500703078002181030f0020040c00004402d0000740c03051a100c42c0c3e1142e040c92103400c0501c0d11666902c0005050751005c1c0b00c114420210307140c10100441c1341d1403e19407580b82e480201e455048a41002c1074035180c28001070709010004880200d500f0089505192500d210700e80c4141004200501040e910110030040d030351164180d41580501030402030322050240b074050600e52014594520400a1444040a944010049510000c405402c01145148569807168181c18003003400d80501c1d210f5a07141a0200304001070402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 602294523 1250 602293273 602293333
    0x20c21090d060f14040209150a0b0a020c24030a02030a1409010e010c0906170c21070306050913020609120318130c20070b030a060608090607120c02 65
    0x41100f5001d801044a00302e00e03201c0911010041080050303030340c2062041d070040b5000d90801d104038855001070300c502e0550300001e54001006c6544403203281d0008030036001c2c00007929070035682ca07491000081000c1440b290201a00700820010345411507a801858200b0410113000c5142c4c1c07110515a0100281100d0100250303541e000c107600081400d0150100c1c04a581c140000168200800100041c8000011404c803071150004290003400c0682160313100000e19a596401a40000c0b40c3c11a2917011b90700741c4006400d10401003424503120700103034001c1aa0900b80c0c1c1c68103d0035400e00040350031402d02180e0111104065607081c0c10180014200030740e08242c41c07401c004800f8204800d1005600c600c9406a14141e9640c20164108040384100d9040415414003011001c90301864240103402100c801d15021003170001501e4141c0107d0260b46182c7c42e19a0703681d0b40e2038111036a803003080b6451000213414800c000301c4820140c0c400d241805091059a0402680d010345510750f451441903040c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 602295773 1250 602294523 602294531
    0x160311010902060d020a0e0a0510030225030906200c09060310151d011a0c190804060f050c0a02120a0c030807020f030a081909031203050405060604020c21090d06 71
    0x31240d44008520387d0010100c5201c1da10307609041c041081120301d4901d01c0c088c154001030180b4003004008c1900bc00c40024810341d41e0303844503890002e20307d130064480c8802007120202c51149940803820381c0d4600381e030000000c02034031142d841040040440a44019014000d40842c0d071118070080c060400151700c01c107850400c03586440c280e01d08a000d244613583d9544c81610051044000421000480d4401d45110030303243e1802004003801c0c01c45c202011082042584194000c01008101800440300a83c540b000c4074a034864080e41d2b40c0c0300e030641c12800c64002004c00790051a1041034145d254040c0021100445045e0b9074245020701250000c0d0b5207400c0200d81c80c01149003014084d0041c440c260058400c11030950b50703d444038029890800c1c0e6001d0303911481c505540c4104a004011600070210034030343c6000c554007400510381543c0c10350f014050100081e207581010f0084131260380d007000080100c42c080c8100341ea01d02d16004643c0c10004000c008002d1389a440452014030b403801484002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 602297023 1250 602295773 602295787
    0x7050306190b0d1a030a030c171b0c040f0501080a020d03030f0f0213060e0102120c0102250b0a0506060a030504210504180b1c2103140903160311010902060d02 70
    0x40d2134440c0030b40d20035200e0350103440100e00080d40700d1700406003264001c18801e5200300245142c400d50180b14118445031103800f4290b021350b2070001d1400203000003901c0c10002d4059048441040e030394240a0604242d1040c2588001420030404026039680249030004254040384440c1d400e0340c1d08a56000207994010a8a400c120842030981004141508140104980b840000303500d91448030502c81c0c0e5064040381148003400c00790111600c0d00070550900310302441025100b035401c007000700d0560702a100071002a080d4002c610506001b0a0001c003a0380c1070200a9504802030440240201c0c3d402044844017095100344030300d0368012928030b446a0b500c5900340300b6410210040804481e80300380c1407007004c49980c1c460600882d030710312491201030600d03c070904102c0790780c405980d00b942072000d03010681004690706a120144040c0c0e400c042c406991282041707666680142007840a04d06864041240001c1c0500d0884809603142000410100034070f400051580c2c0005051000340f03034000900c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 602298273 1250 602297023 602297051
    0x160f060203011e090606080712060308030408041d0c042d08030703080f280b30030309100c09030c0303081b0703020a060e070306020d060e0f07050306190b0d 69
    0x141c0f02405080704204009850144014221203025200000740900c804184203200e080780c100d880510740044135944c2c0d90400740741504803984a4401c4001210110a034007418000e81e10135180908213074100f60742000d050a03a4807100d045004d40b021114030300003072002d12a01c0035a00160081402d00065501c41200303041c040d044040050109481c4000d031300030498880040001040ea1801e0101d0a00c1240d12a4807594020600b000c50154400500e0703c3e50326415030b0520302c03030207200554602445205054080607680740015646140b09801892200d1500c90181d40403d032118120b2901c081e05540c0c944070403120800c650000d8001034413420401280303d044000100381d480b81c0c4c003155131038118a0789000b0f40702c1008140082440c0c1d01c0d114440c1006804120311400345402c207804540d42c8100c80c07880c42c0200954807403051401c0f02e2000088001545440c2e85102d07103801d0321010310307541d58403041081500700580c0d600600c1d2032403240841c22241c0071020b062044212140000c0d8103451421f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 602299523 1250 602298273 602298329
    0x705010806030a120804032f100c0c06240303080709120320030c010606090e0606070312020904020f19020c0f010507060b04090516030b1506160f06020301 68
    0x14142c0694003050144002800b059049000d10303010f458800010340341c9140460f5001c1815035491000102308401c484d41e0031091301021030b030f01c034014116107004610007a07500507580c1d11900034001c141e451035400d02142c070b15005013091f0508480803070b01024450681340498030050708242c0000c0c041400308410150024080c1000d0900765007064000b00a940d40188008070342070010500e01404501c0c0c000c003050030000e5a81e15900840203000058683d40c00412090051044a02039419080820b0303540c2420b0088401c0c9507055503a10710003000c0765180c83c1c0039603c4240b101d500305a00700094007420301d04101030592100381101080c40108211300092174244203c8042d4810380d00c00c1004c40c00d5a821800315501694410000725040303050300002001014000d0014200d402a9002111401c80d2264680281da04c40c04410340c1585500d00d04a412000318001d450f004081080040c100c0d4900c241c0d01c1c07408a105804075121000c031551100280d800c00e80c045954075285643d4001e8240490304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 602300773 1250 602299523 602299531
    0x5040219081e0601050a0909111e04261c030203061e1c030c0203070801020408060f130602030903070c351e0a0807080306040f090c090f0b0d0507050108 67
    0x242c10900d90002d06003900da2081c0500620b060140000b0307030000060041d1039410041c84089001c000c2030100070307151400c940c40880c041804201485550101e4046181500c055409820420081c0342200081045024102c00211803070f102e210f00c4110b81c1100c82c200c3d80001e0a0303a035000340e26401c1020922007407a222111402c02030003000e5a03803006417a000c50241c0110900080d1522001e8507040039141801c076068080d4142c064200007058908054005104030b0326200202d811996403260501205441920140003e10344070306041c0101e4696006150022980b0040d02d1400846a0751201c513810300790f1010020542c492041140b4882215001c1c102c20b448681104500ca100f00005860780440c0d02040042050840100b122071820801121001e50000c501da564041a003403403443d0750411a25144038600780443d1074a040d500380103881015174001c002c0c0407164140a40007004e0002c50404160300b03030352443c0ca0044c50b0b6034845007102e5503002c0d00150246038103040005104000040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 602302023 1250 602300773 602300791
    0x22b111203092a090708060411030c0315010c080304060c05040512010c020609033105100c0611092d06130503160803040b0a020111180306070320070c0504021908 71
    0x4281e500444c0c8540c90f1666000321285415a096514440003c0041024498900c103040c2d0110801c85c03002c02c642c00446c002e0b80b940290b51400c80c1ca4100455140e040880010040e000174404070b000101030384c02000308180c482c14168101038454002c1001070305940400030076603443c0d1828030881074041c08600d0b00034020002a40c6060f540703001c0c41d501c900014400f0022110300c0304c07140307241450940303880020742001040035840c943d048100074103030200804182c481e0b40c5400b80c030201d6620040d04071043c0e5000500420029070802041910760034030b000c10ba45542c03451b072086001030707038818004000c1c4189440c40e820380369081c182407502e0700200020550102c0c140c00402d0100d0714000041e102100e03403500801d41d8803289090200d0242584066603400d00c2d1020840e4200c210300c2d07035491100d50344154111401941c0c0d9400c1201030b6040e0b0300310507061070892010030320342c011010f009140e84d40c001c24140c0000d607601c5021608903400000d901c1991540c89501e04030f1282e100010540181d045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 602303273 1250 602302023 602302093
    0x18060c0c0b07021b011202130b0c01180b040f060e06010906090605040606090302090a180f0209070305040309120516030503220e010e13020409050607022b11120309 72
    0x140001040786032032108405d0611944240307015415925804649043d07212100c14114070b541c8511545007a00511a002c8565003080d96034031020b404100e0b085e180035000403000069840d203803900100c1c1c003040802030f600715442c0c1103400b850600400400d4000e10004000081a500d040300e410120364568002038403c0d800c00008102ca20b40c08680f02055a4046401f141d2a031034407904040101400d01c4000c03640c146159080003400f9152012100090095440c4032050346c6415007282159811980200820070080e000c0c003240c030102040d0240940305400311001c0040303e4064541c02c04840e07200311a03951001424070214104440c079508803220b5001820385140c200118100f8141c07050084601d2440e030040010380380c400c0d658662400d1034011b803041003200068240103450f10b008451850240c490814101c1c1c01c2d001300880140c084078802e40324441a512080d040300c0b044050070102c580c610507802210b40d950501c000a600400b4440c004000700e60710450322555550080d031001c500070050b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 602304523 1250 602303273 602303293
    0x10e0a02241b0109140c011e050903030c0f12070f0b13140d0201060b04080a0f05160801090c06030204150315170c0a0e040804030618060c0c0b0702 65
    0x45100026103408506034589a010603494022807a01445070314902e02e10740041003591000c4190300000000d0301032000202c02d42d560100851341d408100326032900040c4c0c2c00d8030300b41c0f02031990700003c10a00750a142c003d160405010000386583c0105049559980042009182d000c00030400e101306013280d201541d0410300c01d500c2e4080c103400980d20140130084404006809100031084002c21b10f54084603241900c0198840c285c0d44400f079442c103030099864240c010454688041c10390f42116107a400620040d076807130303035800030140d00c11404880c14840c80140482c80c001c1d280042002d08501000080d401e00f40d0306004e07070404007030380c03040c014144104030510114500380502c2d15014828103001c10425201200d4115807090307603100765408800741e107504451035030200303022a20140456014801c5925250000d55948040e134000341030325030400003000000c405d5005806041211406520070700c1440e00c1e00741c142e500d0f0002030b20004500c0702c601401c1101e46410290030503114030041044102d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 602305773 1250 602304523 602304529
    0x908070b061c062301140112020f03040807260406030b01090504230a0209032a030102031303120c21020f040e190c050a032301080f010e0a02 62
    0x816140003510204403240081ca040c0c640140c0341c0160286030001d480804034a00b4000018005409000d04c440d00c420f20369080000020314140c140d903030010603000e401e40101c005640080c105884075001907000d000303013a4406400070107944224025910107039035a8103803a1030344944100c842d05d1450220300d09588040c0e50010001d942c2070700c00d5400e00140b840451070060710f034149140d202c1ca510600f8000c8174810115403441c41c4074010340300348506889854062154040e4010381154941543c4140f15042076100170b50b2001050410f84260061281003500c0820309903801110b1202d40768114400110406500c07121704060302003451030800c10424444c2d8002c0038030f00807600c00089050f407604a03201c4e0410760390403207084030310309079005544568494441100d42412144503e065407585600d150030340c1180543c0c001e400f103641d6100c0c5001030101090b00241000c030322111a00612800800010340003081050107408040020310746d00345c1a5210710f0944540a041a015401c44048680161 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 602307023 1250 602305773 602305777
    0xa020a0801111204022805240d020a050c0304060c3f14070c1a0a051207030e0d0c150204060509040e0c0d0b061305060906010311041d060907030908 65
    0x182041c3e0035984140c13103034000141407009a6581c0143d01c0000c404041c4141440a2800e086076001d95001c4e003800003d880041030b28844058044003241c0c03c01009070609032503802441803c409042c001e00b0031032006102c5182da001070700030070085044c5008c01e0003031040401e80c1c40160380d98402d680107410703011944001174015800c2d914604030640454107540e41c0c021007c010000c25050105a140c0740c0ea418881c501e005c5a1240c40700d4074242244d412a00d01d21242220500480782e100e42e89403000c88280000c00d510000e102a0415aa40108000c8420180862801c2c0c0c0c0303c0384d5610304031304c0840c14030342c0422010304407180c41148100301c100b081e5500982641c0c003208080790001002c02524071801c0c1130000410400358403c00321001c48003006000000c8c00e00600d020340c0c03800d05901032102c0c071400b2218155800ca40c091007480c00a109903100341c000908003a0051506820560703108000050480b0034041d96104505030000c10074281012134210798001d40380d28040c400a01c054964009034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 602308273 1250 602307023 602307037
    0x807030b151c06170601050a0501030203040f0318030b091b03070612090602280806010201050f192004091a0604031b03080307051218030a032304050a020a080111 71
    0x2060120402820344402c81d4049401801c8050a5200c4204000c0459840b12402d00440344070b0301c0c8515000c2a694031a1003901e1007168044800900c0d440e03991810f131011012113041c0f0b805407010b40404000564205a0f40d03004801c074000501c8103401c84900b00210440000200e402640010010030449911182d0b0f610417140c004000141140a82840070280c440c40b1041c140443d6854a0309003446005e03100462004070300d5070b800721952607800c0124241c4200780c62044012100c0008605003480002032601d2301d00d0a0f5000007111500402c25007180708108030740a0700e40b10003040400004a01d801003005100c2c0740d07424801007003404400039407280500d00020700034030070141c1044c0395803e9603140e1801039504080003a17182c3c504408000c219500c50700a0032100c0d4484c0010807078403141d400c04c4001004003e0061800c05400003400c9004000c000b031090303090b40302001150224600101c065015602400160a41ea4030500603c05441c0c0236500c42103241e8500750016002c0700d9130314292454 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 602309523 1250 602308273 602308297
    0x1030c020f1015031e052803110f0604061d06220309081501050f0d020306060603060f092a04141c060f05332106070807030b15 56
    0x30440140100007a085100e800003010299201711541214144202c00c0b03100602c101c04a03511242426a40e54800f07500011441b1002c5602c041000068042d500d0800c0c9203144800f00c60203100702c140d80e540340c044281c409484050359140d60030080304819100d901099001e10081c111410081205012801400744020544401500f05010035114044523002010301c4400c40380c241030360003218000d6030020f108840c441d03c10200b465106003801d00e0403005660700100581060b41c0c1d0041840f0007544000c14140d4041c85248040d00150b544000e00c0b4004c0804048042844d4035030320103490010b1110b142d0301c4031a00e091008201d0404803152a1558030b00645160050a0000179051a1030034503000c024121800c2060610741c14206501c6184507081c000701001103501c1c8441002c2c0011428000e0340040c8020030401c034200c4c02c0c46500220000711041c1421903070102e100440f07041c00407d84000b000954924288141107506008200400c0e00c22564a0010030041c111042644030304100c1d050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 602310773 1250 602309523 602309531
    0x31103010b06071707080406030501091b02030a0e010e0414010305060903072301020f0309010504030e0a21140616020105100b030f0703110c070603050a060308041211041a01030c020f10 81
    0x1d1100303070344011703601400c3e404480280c80e9034440c0c2e40640584404d001c1c072403001c0d1a010074001d04c2c840c0704010440000c500e4000d5032404040507800c0700c0300140a44090305001092600c0b01030b03600c1c3e5100700309420014203030700704495040d85080c03800c00e8000740c20b040d02a4070a00802010500c81c0714412058813018003e00c503241d242da6500c6000e40a105480801d80794040f0400c4030000c0190000351240788203644100044204008228800d4494014800c080c3d0780c00d44214081c41e2080005100345001d6140e0994480e843c1102a20340042110f94071120355220b5000c0f0321240c1c0900949803c03451502c51035a40328200800720072103010017450402c40c1c540200c0800c80090107079208602160f10700e5640c503502c4003076030b440503511150351150360006031910700011011308241c4a440b0569a000413402d14251802c00c0205140400280c01e641c003803400207003008665103a10489555600f0280c140402c4c3d216040003501722000341c0c00c1c0c4030a40d040383c81c0c2c3c10a030760b02c003065441240303000c110005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 602312023 1250 602310773 602310803
    0x30309130b0d060b12070303050d090510020c030714030f0904091109041110020102090f0103090206120a06090608060402130507090b1308070501051602010c020f0415031103010b0607 80
    0x150140074030180c2240c018810003041824040350f60003075191408240c3e154540f10b18400b94940e82c4104510010300003410500000e442c13000c40341c00003140c440c090402c89111100044480c1d0417030f0700903640c918460f800018200200080e03918890488070a86000e14185000d07240c000394075106440c0294407441d40c03546c8078406c0000400f240c10a040c0c026007001c84920f01864845404c8128026175071085808001c000c00d0300744140212072030a0400b402c1304490050550064001d0030000c081280d10030780c1880309200c8482080e03002e6100f100e0200d404900140380c105284111038060304103030065003200c001c001c00360312030000001050481c880c2c00034441e5904d80046946e40303000d401c00b000760780000582e00d411583c61036440041d21040b0096a107003940d28001940c0c00d200340d030209103240c80203414200142d0300580d0364506c90f60000d820581e0f2284030000013011250045072220116030100c2c0300340705000384100ca0031484030043d0003c2000032a40c1000074041e00500c1c078028008102d2080c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 602313273 1250 602312023 602312059
    0x706020901050706090302060a0e0106051e04060e070201020a0912030f20010603060b190e0a150905090f101104170c0409080d051b180a030213020702011706030309 72
    0x210780e1207800030b008014035017080c6802500c0e4801541c2c940c0d401400c024200c000300c0010302c500c100700d0740000c0c500e11480141d805110713140e403002c0c5005235215a8900307000400341100441240708100b20303400166544034500c800781c5007000503000295040045801500025003090080424045c203080070740741c10806c5002d54105500840c9801003a508106000003001100d800c21031644400700c80c0b180160040510304c04149490384101007403124045d0204000324640d0b80110f801c440d01811010f6400d848690a0303083d1038040c0d504107041d50202d03801c034584640500848106004100c4184000116100c80704103074065800368500c2c0180040c0d003600d02800410201e03058480203081032042204038140145580c010100d03002010b8242000034085c149124184910b1444100310141006203403603040d0313448514841803035002201d004000c005a43c036042c07840000d00c00b2a0b40580c1d00d0a0500c0010840c1c100b060101d0351215240741427086507540071090320304c0880706403590090308079801c5c88 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 602314523 1250 602313273 602313277
    0xf0105042004120605150102120a022e0c0f1d030a0203061003020a2c060136060207230310021c0b0d0b04020405361c05070602090105 59
    0x206407194a00050001074189410000b141440d000300c0d0200003d9a8000b0030f03c0b02209013000d03070350060301b21b13525010400c100300001d0500b030710051044480c00c51001c012410003c00d955460003858458600041115059014405500c40c4a00d0031541c00030481c0c030050300203000b50f103840e50342c3c030104660014192020800e44d101650000c04070786090401a4044100a02c58001179001352102e0801081036445020852940d41100300454224028800451621480906110b04004020709c000c26640010304101035030142c184000155a40c4010098141030625030240742990400c6e0010014103400b801d546000c01d1031150601c0711010000002410405442c5910b0b14561012a8203440aa1459441c1d040503031f03241d1080098004039010040e562101d0720004041207584c20000340107042c980c1106802a03a110745c0c0700940020300204414400c80489580424041305400e400c03909406c0210920b12100b4440d020001e4144440083c0244100500900040d8000408410381d900c182c3c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 602315773 1250 602314523 602314571
    0x60906030a080d05160216231003050603010c0903020a090e01060b040f090609050c0306041e1112010e271606030e150618090a0f0308041205030f010504 67
    0x8880b540c3e40e559204404020181501d41d071400c0d6181c174203803003952400090019520780b62407002c0c04466142c07507a4900000f100c10414442e0742c40001ca82105511007500800001540d80c4000ca1a49000301c20b25003158200740407001000f814040400150b141c030310b5680c1c265904481c0100c2c500c003040d0340071809461035501c52052900001400182c0d000c201450809417a4048024042c8039502d0800b1130540d44140c03060060503400300040b62052038554400038200701122004000d800d4680c2d51042101c40401007222424000202018583c524003801409000459690819402c0c030560300c50001800c1c2d18150f503a00e40f4000381c0c58014800b0442d400d98031300c03206910081a61030340d9008000d050b85455000b0188285d0402c5210584401030b042e2040340c028104821900d050300046000c06030240041c0700030701075003162030046030083d6480c0c81070354002e480f1a0510305140c50040c4404880340b501e002002006d10900c800c400c0188440c50445604132004111210504413080c00300b10520 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 602317023 1250 602315773 602315783
    0xd1202031302040f021b030a03050106170604150f0b0405040e030f12100e0a0614041b18090603050a03020d08071709150f19020f0406031d07030c0509090a0b060906030a 74
    0x203000e401811b1001008001c1414155424010350340d07545802d55000803107640720b02c0010002e20015100381000c1d807100f0501e029610303214007030719070b101052201036006130402842100002414010380c1130a00030500c00103c608011458078040d8103c003505801800111001d107010840880d401e0074280790940041d1040c143c2568581c100900c541d0000c013101c1c40351404085000e80400c40c1c5113443d02c5840b6400b40c05a065140320f10484000b12040500c030000400540200e440114035520644981405148128010980542507040c0a0f2600580900709002c100700b04080205580c2c0c444c000505446414605001d6600c910301c000d82421101c0000780e07074801c003c00c1006000171100030308034000d00322450a030300c4000f54031300301c0e01c142e10a1034040d0000038001c2004000e91480382e0300044a00e030b40c510001c02c5c0c2800b500452400d00c0803541c002e4403803401741b4405214a02d04065029040301d010380003030400d0100d40da2200360310080145072038400c603020f00003d600d54500784070601010b6805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 602318273 1250 602317023 602317057
    0x50409050a062c0f15072007090b09010f0315060b130302100521060f03070b030a0b0103091211120a1d0102030c150916080d1202031302040f02 63
    0x6891540c400c030a00070034034403070790983c0b03640e40c81c500101069001e10b05261001901c81d40c40100861110f40801074032250400c00031060b01c14140d4410303003114000c0700d421805040fa0720300e03240708101a54803a481c414814510500100601051f5480c0f45040340d5005c1c045c9000c5800c41c201c900e004249550010010110020304007504a208001940035a1b10880f0008480301076181c04070703402d01400f034030041012118035054401800d400c1000303034800c8000388a07012607102100400e05148150340201041d02000c01404150300041c028010440420700c0d040007250340301d8854400302401e01c8698014000000b0407102d0242d030070700640280c0384400c40200d558400307003d00109030306010614607018004006421201c0e40c40401181c2d2003012000007098400544071010010b4040500288018031071510500c4d4400c0a0b040d0700e070020300c4290050840381e04103001c040c050300003034110960b60300d02c104108125046203030382e480318003034040e1000200d00c403082000340b001740305d00c00307440c0304040358 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 602319523 1250 602318273 602318291
    0x1f020a08040b03061509030c0108090c1804030809280c0308030c0a110303101a0c0105150405070f230c10091a010509070f03141021020604050409050a06 67
    0x45030095019840980f181440a105e00580403004e010300d40701c40d645500044074400980d803043c074900390010114001c0da4841c000140000e0b4030038560300340a4604060b6101044107140d041036403280c2c004d0380075001c0c2c0702d0b508034100b1502c0c1c41c0c1007460f505002c1b800c842100c0b0b0f05025200340340c01b02031941f103c40503650f400c094005540c00e03003140d8544000140c90013407a000c819000300c10f0301d01030581c4000c0203c249050148031082031651482c00c0805001c103002c60441b03843c003401600c1c06801c9203045a40643c444030280426600014156802d204082d0081102a41d0158143d00440c590a1040c44c0044a11180340040e20440d012300d850340c45007841082c0012402c0e03002d55445880b8a03000104110001034401100800b48166a8071000c50380000e0b0645004410000403c3d0303040c030300022211005141243c20100540e00f02280480c982d1087c418000351000400c80c02d0b41c840030208103c0d04c00d5001844038402d82c05020f004948680302c4408008080005403400d030340c031030818464010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 602320773 1250 602319523 602319539
    0xa02090907030f1802090a02090d150506040501082d03090a09020901020c090f010605071e0b060a0801060b181906170a0615080403020c040c0c0c0906051f020a0804 72
    0x1c24045084052071030305003090825598941051011a400707801d151680d80d842101000a40002c449d40f07030080304110f01503000844521140003401203101340000c0718281081407204566058020b0701003948896043c80d42c0d0401a034070400307041c3d2401c0c804011500426044c0c2d01f14084c1c03156035074118885440100b01c410858002c1d068000003a400c03100c50380c01e15810844100410fa03210340028001d8230041c04020b00c02e83c000d0032042e0007890454904919054469115041100240c80029414040c0f0a503071500701c00b00320041c2034503c000c0c000c050170101705070864818803240081c10010049925216103401c0c50341071020f060002c1700304400359590805002d500700700c00b0644a0101c2c5030002030600440d4420401541c0740d003100d4030b8524004600c08d540b03072200540150b055201e0400090350aa407607008030030190015550703041300001145800441e20116802c42c2000505004c410300c0142c840f072504c0110000c1d6504907528142160344164204900003002038000d000010f00892455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 602322023 1250 602320773 602320781
    0xa02010603050c010903020105340b04050708030306030c0405060f03070b1803071229070e09220b07050706050c030402010e030105011512110301060f090e04030905090a0209090703 79
    0x80c2c00b0300140e9002400304030045400211a0000901040c8144922034400c02d20102035000c3c11100e80c0b01e1582402c080840c10120b0545030421509405c84004101c03c201c014040c440060101e40002c50860514000180c1c8039040009985d004030b640740005070740351b41c1e8500392051584c40074060741d45071600c86845081e01e600c15049100842e00307080c9400c130f41d4100000c400d0102e40c0b4a000751a42d070b40c0c440d551100c6228542c0341884030031400704490000e9007a0504000d004074219102e1013200d42c005d0007070080328100240015002c1e035003006040503950900805014090340250742803441e50b210582941c1d20300a268002c2c01143c94072003040800403840c00114095030007600e401c407141020108047c01d0f038409004101c403005d0061001e600c124000e007100b500103d01c07a40e000c5030409040b0880b410542099010a000a042840b0356070541d4001540e0400340541d500c444165141c00d46019000600d240b1810340036007a0040040c00359245a4180d81c0490001030070034005040c5410018050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 602323273 1250 602322023 602322029
    0x902040b040e060115090b0703030c051b07060909050108030406212d0504030e06160f060c11070608070f120e0a0506090c010804060b010905090a020304060f1802040f0b060a020106 79
    0xa00e51045c410301706801200c80000704e5025440461509525a03030450241901c1d1038010103020061045c51612405400e051080001802c000c20740185021001005503069501508585107400014000e0900102c2120161041400c01c454546808041203001c9620103800790030791440c000d8a01680040542d2005400703012800135801c040d03155000c4011101c007580d0042c080340c180701c00354035103050900150509010202142150010ba916008446051203104549079540e40c48405207007030308031692414440c41c10005150080c01c10001410406005e0007160901c895088030f074007414405e50020344400c8002c00180007240741d42140c2544c494034048110b42600401c2c000400841c0001140800324105035200062030b01e942c1c59071001008501d4103941041180303000401e450f00c6502625000c1c007180c0d01c00603501d00c0c050501308100d03003405404410a90600702c062201034207880094440300e804440000309250481d0751180280818403046410210101d00e44d2021074041d4454001c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 602324523 1250 602323273 602323289
    0xa081e03010b0405150921030d0c031e0b060a0309060603020a120308090d020c15251203060b0a03180210050a110a080a050c0f06040f03020d0c11040902040b040e0601 73
    0x110160404000c1c04500850b015142c112080c048020303132010418010f006003100310401d0740c9c50000900041c0040e1554980c03200b0110b916048074004900344440c000006c0310210307904001c800700003000104184035903020001010384801c260401e00c44203601020080d41e005280850165680070005010340c0b400c1c0040d07000c2445840001d2052a0204200711150380f0350b8098502d20700c1d0302041010641006071a500c1ca030509010442d1405884c1c503030841419540460318420014910f801480c002d5400e480104040c1007102c104491405803054900d495100e00f0045080122410b8049403151811b401075405880c42052000c1d064000d00240305a1840b07507602c00d0a18112620240d541c002d01d03000034141e80c0100100890544110050300a8254040542d0b51158503001d10034600a0255002d80d2512900046502095010407040b07400002500305213100c1840e94840280301b4895605041c0201d48682d90b80c0d0441d0784a5000046d1080020310811800c0b44156029684a0090150400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 602325773 1250 602324523 602324539
    0x6030c05010f0c020307050d050a06020a03050108060a0c020705090405010f05150a080a231903020309040f200a170a09330b011b0609050706110a081e03010b0405 71
    0x280644600740c0b2000f0150080c0041007000e1401e400e024840c580c0c103500b520b540c003840d81c4403030028040740010a0211010703580410713154100303042d550070642d000c1c088004451600c900c5920440c0c01148500490340111b0301c0c0c4003d66100d060003405001c043d000158683d10f06800c2000d605c2c031102441c00811410b5840b50301a0f5282c0a020380d84414041018052070006014040d400031000a449109007103002602e110000d085000043d02c81012000c0f4007507040400c1e0000d281c00d007440303680c7c500f50b400507050100f4680b0b02501c00981810303c041c2902310f4000103c900d41c0314001d820200d481e4240002c00009451f1040c4420700404410004440005001c4006240140034128000003400780c2031105422000050045000707282c0c140400d8180030b0740fa4082201407001d0840000250300640e0081a842581d00d4014144001500b1610074407000308812051294001000300c0600da0003071046a41c3c0f40041701440014100641e6121f4101d8004004550003031010094011502d056038089 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 602327023 1250 602325773 602325797
    0x905011d151c1406160903230f0a02090601081302190b12012c130203010902040912080105030610030b1009020c030d0608070e220b07020a030206010506070b07050c01060906030c0501 80
    0x302c41700350103188040c001948001e0500204088030b6080400c0e5242051110f6004110000f4a00b0a5003402c100704443d00081d41480c198106103214a40c032041c24070b8504901c2c07070051400f00b40050a402d01a0285901000d8010010075021381d1070068800c11024a4807a189001100c1031b00703a003409616401041e0300d61002d81843e10340e4007060b0520704808403013855500c041c0081e85692901e0720a0780e05640703448103107003d40c4903131140d100c405000d03c05c0d07a403a03c200310901400340360041c0c7c44107000342e02c000e04120603440d81c1101d81058940c40080307a81c55448581181106880641040f00021320015000301c03070301400001072124524400303080c010103a4440c82c1c42c0e1140b60a00c260550b101d95240041c0600130840032444000741c038480125104c2500361102c14259808440340c1c00543e00002030070044c144c0421400d40108421550300c0d181880d2070361104406100680390005220010440c4c8061303000a4226001a00ca03040041103680c0d134038101000d141c1003074403a89002c01c102010603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 602328273 1250 602327023 602327041
    0x40f09021801030c0e04031806030204031109090607120b03010606050c0f07050d021003180809120a170a091503050414030c07032402040902040905011d151c1406 71
    0x200d030480750081c11203681d0304d2600704200d07011740c00240114100700390058102624165166214081d09103a6030050710f41d8110701e040041000541c0d02c1e103100310742100c2049041100001c035180c2c4014245010010034070023481c0c000150903064030342a4994204200440d0540c0c2c008080e01a06482c1390464038400590303000540c4400c02030080c2c0703412121000c0e10201504003484041c1c9082100d190000f240c0e10480d0100901200d401803c4521440006080b0a6483c054002c0d4115602c4000039054540d001e130389140684911a520030303070390803001c1071680c5c800c0d001e104070400805d150032401d5040005910010000d00c41150116902c4640c806a6804504c000007540c445601c1c840041c200d650840c0c4604c105184244a200040c20b608510b40d142c201c118000782001b051218409621142001c800f00103440050b01312f210051054041d890340d51035000d0700550008111101d000c4120b1010b4041112001c80e0590341e0f55015010283d0800c01c034032600554400f25400040ea002c2d910341e0405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 602329523 1250 602328273 602328319
    0x5040311191e0302040b0f010518030c1003020a080a09030806040e0c120715080415090f021507060c020303070215060301022206091d0109050a0b040f0902 68
    0x14250211204445000342400301400300750044034180300e01019581e44124406001000c07150180300354881d0104114146401091401303407044510098071074401340020994014283c0c000ba8101807801d02d11441c0d202805565250351024050f54031040404802801030750042c1c2d02d280014050300c000840505581c03042c2440c2a502d82d40c2c5048544412003084044d0031002c10b42c22907402824240295956440054100d025900740034100751442c00500700d80c3c0c0726401d4103500c1440311940801c0700146409050101c002540140051451340380c0c20100540c00c0062802034001c00c1e00588204a2201d00028140c20f900c250018461400b40040803a201d000580e610320160340001c4140001d00e200c080c05035402040a00018145071ba0161b01501401c5158608211012003001c00d1200c03980c0100745030081c04003c0c14500e45080400019a61703010144100e1801c19034070008110741075659040000544c6d00248180002240641040c000300384000003280f00d040342c15030601c007840782820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 602330773 1250 602329523 602329529
    0x504020f0d05060117100302090a06140d08041203030509011d030904020a0c020303040603061d01060c140c09090105061c1e0c08030408030d0b0102011e021305030304080c040c0504 79
    0x194a414114010031801c0a001d01074040360600c681e902500a0315207210b00081c1c03142d030b414134003940c90074a07500600901c00e40c0540502c00c9103003403640c180b2240880e4115114411020344400620082c00e0801d0941c9000d246c000c2c8071071220401c1c2080a15a01d0f400040c05808580020021480c1c010100e240340d803849469050250010320a241d00c902e890b0b03018044400182c2001c040c00c034942e6002a065502c5604044042541e8090501440110441c0c00d000743c0c001e80c00c40c8280b07506007400a41549144040203043c0c003282d20613402c2ca14002d02c4080d40800020b0001400c03424103105060181070204d0715940915003103400b110203913412010a4030272540024003000025000c541c6900c1e0240b40440030745815171880c80016101a041008100914101c0c02a40d2034406024034501079035a4880030b2030440e0f0412010303c000c000c3e03441502d40600f40c010030040e5641f80d82c444401d070445465000c0c650500020900052072100898042d2031903908940400000c40000b605031041d0180c0c0c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 602332023 1250 602330773 602330797
    0xc010f0c050607141c0c0201061a091302090405070c030f0f0c2d0b06010e0a24021002180a0611030d05070c020a060f0f020303010602120706090611030f01050402 71
    0x30108442030300400340d002c01213140001803881c040c1940080102980c0407640007030b406582c3e107041d01c10b613a8207200d814045c101c0c0542c170021000301211100050302035888103d20940a200d401040624039504580001c04003030000c3c1f0040c80e24040150501140c9842900891003962450a880f449007140d511802d07015140c20b00300c3e16054844044104410030301404501e450317446400d03d00c0781c01e20349450441c821410f054061078508001820311003140b0503070b80030b5191081c06000c0e0302c1800c0e6038181e813004070b000d95071000380c500c0c0c0c8100d00d004040c0340c4024074180300165140c07000700c0701c0c983d0510340b65061350040c10065990004a602101c4e00a103500150001d07c100c0580140c00c1d0403c94001d407062400750510340d00303500090280e031034540c07105000c10548070701e401c0130a40088510301421154005075080d0340c5011b01c041e4451004030b1000781e400d000015080200560344c0c0c407861103582c024000f000713050650704000260364001d0301c05215246440700000b130186410300031510441030740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 602333273 1250 602332023 602332033
    0x10606090510031d03031906050303040501081302041d010c030518030a050708040e0a0504051b100e01050d11030f010b0708160609021005091207050904140304030b090c010f0c05 78
    0x1c01e404074004c00c10040008000d980d184015501c00800b040038500505604201051022002a0f0041100c0d09a440380d0300980060204014684e000100f10ba03010311070f00411103000c405407002a00900c0034520b503024800b07107208200248001503110f1100c541d0141c604002035242c0c1480d820203030914522120960740700700545c41000c9c0c414030280500e40e204041d5181041c0d00c3d200c108003000c000310ad0301c0c04c0d090303600c1c0c0801087c024200a480ca00804400c40310036841c030240d02040d03284802c5003d2200b030002200041481342d101350221040003440c908100710001c02c0d800c0c00d80e155881690100600001900003094100594044401655122018074684040714040300d00c0d080c82001c040d10f195a80e44c08080158079911401c0d9680c140300d90350a03603107000d10801c00c407070803151440328925544241424012902d8440030350342c1040d00702003221403148944105d18070310312580d0001090755010b8000e02c0184240002c0c0c05002c403600b62652060180000021100c04040d6400544151300c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 602334523 1250 602333273 602333299
    0x2150f0402060705070e013b01090c051e0406020d021c0305060a0b0d0e0723060c0f030a0e09181510053102070b0c090105071e050106060905 62
    0x944000e2034100d210b041940d082507031b03074880c0c011000400d82c411035208581da40700024142c600380311418804001c0000d000d5280b03030350200c01801d40c014011003054680e40c1100d050098020026039090300d1008100180c0c907070304201914017581040c8030f9600036114080342d00340168001310342c10708031146400091107001900361048000e02409440f0302d030082c44400740030030404009c40c01005a07400000700030a0002091226070300d48442d5600030460202c588621201c8100c4c2c00021290710b0101b120921744800c2c1041c40c503410301850599150040c8000200345840b2504941e54601b60070007251030150554440081403980464076034903100039000206e018007488180000544c00101034410b8185150b103a2021170440e26480700b80c0601d148291445050380040c0c526009400c201c01c080075030600406a8a440c003004014142c817003442004120310a142c3d200742d0964081d50b810408450502088694a800300040031600392120b500301940451100d00a0b520740c3e01315100548010351040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 602335773 1250 602334523 602334529
    0xc02010c05071203090236060319060b090f0906060d0c0302040504050c060a050408010608150403051c06090c030e071a090103020c01060602070f060804260c010501090c02150f0402 79
    0x3000f50214014150b9410505000d40c481c820074500f580807076605098400400d0030b44140d041c0e00300445283c032a8048007040b2160318045010078030344035000340441401d043c03442d042c0013601c611010b4503086103e6108100001b0710391000c00d402034000500b80c1d6a20344450060081480d1409805402403807000401c02c01814035030700580c1d200740901c00341c62a00b03600e000040e03400c0d485112000700041001c201441209002c0c0b00d41d10041c4075000003071121581406c1c460030300c240c00070405814860045007912050940403541020390390f50140c00c01003140c40e4502a8014107141c0009000240390840c2d5200e118000581a000e660100c0c4042060890448017204194010380c8a241019020f100d05030980e842405050085c100c990090404681000f070400280c2420340e1246082048032030078000420030319141110700088441e44040710001c5190b0b10501840b40420854983d0f10f4880006400056035120201207200c585c00c1d0388441c0016070145c041441c0035039022418bc8841c10101e00145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 602337023 1250 602335773 602335793
    0x305072904151404060204060e010806301c03050c270102010e030c0703120906050409110712080a06050d0309090506040612030207030201021005010e060114041509090c02010c0507 79
    0x11020000102e1a95015044000d04403c180c40440d80650007043c00d002c140e4021501140812003840d000f80701d8501407000500d05071840c07501001c424a0010b440c503507201e00400c1c03d01b40012280071542c2d40080420340849545c840d41c00719001920745004a4003100401003103030101029101c0071f68100999000450040171940d2860b07066640e114106800703900184007030040307800c2d200060030f2101d20b1400c1108007541c4140d030840c10420030420038414250400c0c140d4040e0f45111710b00184105008000d00b2581c85440703c060152005405400c5100d940311b01554441d09813000140007942e510820b10090802405009000c03584054061281003103031b511903540450020404120f40b03950b4030040c240c54050400036001600501c6060056517010021080f60040b1b031031042249614150b910003102001803c0d81d81085010b41640c40302c090a80140d9001d01050503040c80505600074004d4007059182c801d480f40c0034145080361980500600c51a04402d0b01d0b82c9943c0d1500016030380359102c107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 602338129 1106 602337023 602337053
    0x20130051b0c0d0806131b0917030a2102030c0a0f0e0117090708010c021015030b01030b0408040f09050916032117040305072904 57
    0x410400502c2214a201c0f500d409111500d500c00001c0038408040352803c0c606052007401041200c056070364007010740032a00e03044065070713540c00c10090485c2c0307695580101c1e40003030000070002801141c800f000c02c00c600040410301c40c1c44044240c02c81c1c005a411104050780410601245a0008423618114215003000c3c410703458502c00003441d41007820340c4100d4182003c00032800709c2004005080180c40150b000388408a403c0e50000c4d80e558400ca20300c1282410070f22072008e2202c8030252581501d0700032826034426802d5172225191000041c10468071844100b00002d8801c0d20540c0000103085207040102e41c81c2840355609107896954040200c44110300b04042001550039541080c468070f401c4820051085510303030540c2d8103441c04c040030f2161010201008101640000107200f4a0320400910121035003a5620181103140300726400d16035040072010402050060b60340044c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 602158273 602338129 := by
  have h0 := BRFrame.cov_init 602158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 602158273 ≤ n) (h2 : n < 602338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
