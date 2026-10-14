-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2707
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:30:08.889563+00:00
-- url     : https://prove2.me/submissions/585c82bb-9335-4849-8186-96401044182e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 486690647 ≤ n < 486870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 486691897 1250 486690647 486690683
    0x4120206030a06030510020a0305100e2d070c0b0a200c0a0f0b010807080304030f030f120c030b010e040902101b080c0601030512040803091003110d0f180203030403 72
    0x1081d0304e40c4000d00d40d000b0140712117502400345d4017401a10616441c21711195890b2540c4013100d119034010743c1215951000030030b0740203121004500a2115000700701c40342004100d14450707003000c1181c030880080c00740c0542034104400342314410b402034000c0300c040c40480381b4036085003042014000401c01944000c24102e00c010010003208040c25080022842c60b11158202050410b100b4042c0320f0181c410040300003070001001084504590304000e000c4c82c0c3d00b0559174100c40c4110307100c8107101000f1f042d40a46c141f000562003425200010703501c00042c4990340c03400143c50300160302c49042c42039103407152800141e144e80c44540c070014001d00e40044040c0510340e0855070480c4a00002d41347d0039000c99451592503002845d079058078010300440b042c007102e100100d0400d12030790194001d5604144002da520b4101401e141040e4007250a0225100d07680380003d284035041403070103401030b940380c480d5049044c00394802c0c40c0072500c02030720b050302506940d0003003640c0348642c2c40028902440c84400e0948 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 486693147 1250 486691897 486691901
    0x180b060918090d140d0b04150602030403030215091905011d0109020f190e10030609030806090703150b0717070308160c0209180a142104120206030a 65
    0xa4040024810700d6080741c5030081c1c8401070002c0350001d880d881030000040d480750044803c01441c00c50044480d18014000000501614180c0c50141d0415211000c07480c103d210004904040c124982c025a202c1e441e500b0300900c2d15254181c071038000d135100001c0c84001a004201e0700d40d502e4180584039002c2850340303401801480d0081060060624001c205061202c0640140d0b90450080302d182c6000b40000007042800d003203400c003c90880300100010400c04880c49152903000d6410806046105d40d00d032501010341309699001c45c000780c3c45104100340b0303107409079550350410420f103810003402a5074100740510030094003d10483d0400400d01204022803648a03a07140c000e110819074035881c00d89005492440d05852452080010501214040e0b1040d80c18541940d001003203000b064840c22807040c80901c1c0103190070a140100f60f01072000c11407200400c2102a1044000c00441118400c0807071242c804800d60b40e140350f0204400c0144803c281c3d0201c01c3d46404490300c2d69651200c1b055000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 486694397 1250 486693147 486693157
    0xf0302070509010b0408010f020f190903060c0c20060d24030302340b0d0e0604200604031101140c1501030201081806070f030212090d1701180b06 64
    0x242c403400e100d0001c01c40c100400064011134040300c00a00c003c4028a1201c8203a000300421205903d1040c000c0615150b0040c1002c81c6040c02410607200d040e40b0794880c441a19140d01c180004110820f110703800300301910903004081c8141c05065210350f050080042c2c55403041c1201d48100075150b10400015a041c81860b01060746000e6140518550302e02c1c0194940c0001807004994501c039001030340a0000700700d090050850803401c4060541e0504031100d50035008800402003403556503c449031402001c1008a005d0f80c0520901060040c0c00012404031b2024001d25a00844041c0410030028103240e115403c204401d081500801504400c4610319000f00001800144240f025860420201501e2507041e81d0007179840c01c0c90380d0340d14040714400b101e001c06100031a51040b40001e051521990302001006c07410301c0c000d0300e000c002d241c01c625000d409844610103500103a006511454100c07400315035080c0c0d01200b0059079031521920031501312000c40c400e0807003921480c3c1060f17550b0b5403000700c1d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 486695647 1250 486694397 486694399
    0x6010212040e0702010506031209131d010617010207030801170f07030327050105031f090c0801080c19061112040b030402030d0305090d05090a0518090d17040f03020705 74
    0x80d440750350312454034000401c19500c01002d54078001c0456103605000c9000b03ca00091000680c1c5802d1442e03040c05281c1d50b90312000c58640e0365404034803a584d11030201c4050300e0380803200085100790a001032820005005c0d840d6003440c1c2c0c8104100c03000a50005009030440f400842400070705d103225160f881c00c045c17420210f02d0f03003030181820210805420001c6c2001d003000c800200140c0f40b00342040410303000d0040c0070f500c0c0030030010f00c0040d201201210409640400c50080d612940b0b40d0380718072505030350040c8102d03c00f0600500052001d03100400040840c450100c0341040d450b0961104291081d4041c002c41080000b0030180694180041143d00c42003650650a9965555243d550720043e420903036040744280200d4211030301e0103110740512801000c42c0805442c9040c440130007919168040c0e00300d1508000c103240001115540c5a4400e0311130004c52458007101d2a211100314140b14440c070104082c0148201104800543c001d12181c4c81940407004895500443c101130389428010703440a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 486696897 1250 486695647 486695683
    0x9150c1509080f03151512070905120109110409170309010b100306030201120c08010920030103051501120b04030503060d0b041b0e0c0702010c0c080a0303020301230904030305060102 80
    0x343c5504030000210300c50103542c40d006170b25200c1c100401c1001885001c116030140b20500610340310f80b41002c0c0d00c2d0340150207420410740d500e9031080490071580000140072240c0e5540c10032101030001c8618441c2805408840810a03684540c0e66001c4070a407000e00c4803444a408000220f030341c0800d40c0040d0321590001c22810074001e0b1660700502030966070004030300191032007581c80307084107890092868080f0350f500c40d100c0c560b0800c0100c8000345070054080c10701c58008188007422407910381c02180a1800380d40501965452403004184880044c1d000d1030844d03101401013408261003a03101c54000340c0c5840c0140d0389884180000b404420344000142101c01c241003400204800e02c240251024880d50029402960300d45000840d41001c40e0982d03400182008200019072060701e003001824403070201005440d0f200c070b80480c42c001c441c04c411004070740d0010050200c0e24103080703080c1d0b86204240240c1c0100c0c0c103050100340300c4a000740006040c581c65402041207070380203010000c0801c03482c41072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 486698147 1250 486696897 486696907
    0x14070b010b2808040209060109090608010615050712081918110307050f2404080303010306060f14010804050f1b0a050114070f0501150803070309150c150908 69
    0x7562110b5000d141542c18820480c0400c000c200c4030a14141c20091a544a11020740e8881c1c0034081c68000051401d4100314604502260303c10703a40c4500340203461040c2c00000c1c00f0b82005140d00b05c01c079400701c1350720601c0b01c2446101b0016004007580090014140350030001511050140d8807031138621010314030001d080010714024403116003c0444424000e0320641600c002c0c800034942c0315042800780d2500f012062046190030300301003403c061107016106500848004e038051140d4990015000180036420000042091024038000c400c0980b25014201d10080d00d05084070010041002c0c200c2d05101c2540006028003109010900949081c1c4054600411201d50341556090055180d039104500d80740001c601540300724000301250214004080c5024003513150501510580003040340c20b503403542100010000c04181074801403420500460f22000d01e46806020f600d40f82e0010f000461503c008054419403040d401c0c51400e400562610650409041c0c2c4405018048406000e83d040011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 486699397 1250 486698147 486698159
    0x60e0705061810050c07090e0309030601030b04031202040f140109053f070501050f0d1803020d081b0f04050d0804150314060103020313150203070207080705030d14070b01 75
    0x80240c2c404411146801080c06a40d419a0a0702030b00c03404c240b060748042c005000750012a4000316040c81d9a000b1242048060b0340001d2034448260400c482003954141400b04164000480c100482940c40d404c1d4103103428800843c000a8040c450303103900300c41ca1000391400d0307401410140080c0c800909826807880c00f0400544100114100c005152304066503100e11512008008050303c81034100548401880d24004543d1600800040500d0764020000c2e01403220a40c401c0c4203003005103c2024100b031302035050107030034065485e841806010501d02085003040301031040e10544543c43d01590744920080082a020f406183c0115400940075049079081c003401d54040d00c2103402d0319101c800c440f601e8150132415a010349107604088014103000c00c0c80703907000703401842d4403601c0404064030741809500c500340301c02010200307042166400000c2c0032100d5818001500900b240344000c00b001e91804000c00c0e51004040b110b5400c004a0100744900504c4141c219503005401036080781300c1d561100703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 486700647 1250 486699397 486699427
    0x30a0c080c0601031b06052712030a020109060c03090302070608090a080d02040801060506040308030406050402040f0c0c0203010615051c06331b0f0201121107020a05010219060e070506 81
    0x384108000c5d4000c144006111449502105c2c0f01c3c10054207501c060000c0c101e040211844181d070020380c04048201d03071150900c4104046c0520301029800425140b0150520108840d0300403404000c150a0000c0e40003c40c1c1c000071500212145407030080c41030390710300d1802c904041503e02c005010b504001072403800c410706078019006945680c1c00030840150b50341c041040e584502e11006080d47c205000140104203140c1c002c40c0c0c4980090b001048003020000c03c0421580100c01c15008104000101d1056060912400c0003500703246507050210036425201030801d00030b01024410708850b0658040f109a442d4000000420100c1030007080d4014000400c40c11150b6942c03a060b181c1c01c56040f070b00140703210300d8164041074124004c502c0110305c0c1d07841e44003007102048820303410b0006ca01801002d21545105603a0069001d1400f60b8461714030340b0400c000c0000d81e521850456108c3d2440403c14104140306c052040e5000d18001038000b081d0442c0340c1402c000c0d501065110401260094048150b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 486701897 1250 486700647 486700673
    0x601120906050613050103030237061a09011211120109053405010c2f03010e03210406140a09051009051c1701150215040302030a0c080c060103 63
    0x40f14000100c65055110800b112400d10012300182e04c8525180007449070740a100d080c0414100c0030001769145955064030041c407104048941652b40e141c80d02d98418902c1000c58642e4045606140c5035141146288181c20007201c06402030640400800c640d544d1840c80401c00b00c44d40c00248180249420300300d03100c5000789070344411421001044224404440c002d005228510781140389864184001110700d201801400c4804050354000d2045443c80200406009501c402004008002d0030b0149400d4810b1801044a50791062001940000f00d4000007082410030190600072503496041c0350001d02803203010741402c41800405e00240c03407990381120b00c1e014001d5046403469154000786108841c40b0f600080c0141e000740b0034a00f079990032a9800d080b00000e500c1c10295100020f00103036408503007a4002d070051010005246a0250140442450010713807080311702d11864151030203501d80c4035250820007004101e05420f010400414192400c02031080c0499025684928004502c6504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 486703147 1250 486701897 486701899
    0x50d0f053103080402010215090c0102070e060d060b180a091a040c0302060a0905030304080a061506080c090d0605040609061a01050409020c011e0b0411190806011209060506 76
    0x4111007a680000301c0300c031030100d280416072441210030082e2401c44002034050001c904501034901024042c2c0140081207025402100140c2800d241c190300180c5070403a160300c0343c0c0c082c0c0400000c024240d41c898400f44036840c0c00c511f001c5124524640050415580c034101c62080d54441d17410b103c0240071075806a141c503881001d050241050842c604542860201c800400b0241c034840248014242a005807484280d14100425450345420000781182c1054024100940c0580090750a0007864000c00181b8000480d004c81d095051030303001010050010041c042509000520200700e071244041c8000d615040740e020040760802e8a01103003d007405200586402e0309084401c18040b076a00072080008105031100c5107801d2800c00d482d800307900181415090f079581d40c0e242080783c0d0f40310380710140403500c105400030f50038a40504100895500c1050f22b44491824072040b41c0170b9002001c40802d025450608254940d52000100c544904064842d0015418031514508010b16504542c3c01020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 486704397 1250 486703147 486703171
    0x80f0d0e06040e040210030b03010e160e190902010e060f03040606050f1810030503030705030718050d02192c0c090901120503090307030b0919170901050d0f05 70
    0xc8210100401c0303000c1e0f40244803202440502060061800c0c021104139542c417800d010600c079070f80d440041d0031242c0362480d02c88240c00214405030b0200701c240c4a503010344500c4038022650304100640800000c1c4101d9640b100503607455148c07056a003e60700005843e40c00078a0203980d500d02d0400003000f40c00c107a50032100b0343d04040000c51285400d0085031440c0501900010110724540750703240360950b004d40001c603001410b081c044003140c400d1008601c540055190300c1e0b60780c2051000189002805400c03507003006006441401140d94189902e030301181c0407070340741921001c00c031141201e01039558882031511103580642c00c4012a000d0386000350755140c14080703155a484520700f506074403d03d0541c039030290000c0e00500c1140e8000c4504903406010740103c0b0b0070b00c10303c4400300f442d1500940040d0b508010080412800304410400307540a00b1166180c8114500d20fa95031598002d605131007008503001c081850a80d82e44a4000d4a0304a00150014460210013031401001410103854048140c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 486705647 1250 486704397 486704417
    0x40f06030204091a033705060f0f010e0106050d0b0a0801060510080c120c0712120e0d08180a0f08070b010e040f020904020609060a0206010f06210c0306080f0d 70
    0x2c003031506044c0310740ca0180c054442a07107003a4121503920040030005060310717006100502081c0f20795540f80d80051080004003003c0c2464490303e5400c0e080248600c4204107240c00502c04022141c0a450449400b03041c2103071101210070340080582821982e82e5002000c210001680741415040042202e0701074545200f215a80c480032100d0000c00c440824000711b04002600154500b600e00d2a03001c0d044000282c2494150340d0351807070103040c3d084001c0010341c0001418800003010321a20010101e048000c05102c2c406845c0a80b40c03a5004080300031a8803510f007012140d813400e2001110b1203900400400400d0f9030303442c10b80c0d8160025001038818484600002c18000741e9104103d0049400190081421000f41d080103c40750f40107004a8115000740607484030354071000e0141c00c880c5219000340ca1a0340c140309088880399200e41c488400c000311755a190031051039440c1040703a4bc140818010698001d582819405024507034429400d9201c4d070000c0d00141039011031582a00381d01a03880070404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 486706897 1250 486705647 486705671
    0x120703080a200c04050114010c12110d0503160509030c1003061205160f0303020a0605150627041109040902120d050a020105070302120a05060d0b09010e1005010812070602040f0603020409 82
    0x40ca100d6501f00d002c2011102980301180d2100117604807050b8914051703051603404c00d0420700b064100c07514a000f080c404418010520708000309485c1c195118a0054140070b10b400009581d40101c801e054096440d007214201020300c240c01000241c01c29140c99600310030a8a000c80d518849004900d03903c000100010a074101320580744011641c0590051440181c80d803120401884040c0c0000e20280025502c040a074071000081c0c6040c115140300045441010518801c0841c51045614811403400030000188031a1809a40f8248001d4071f000402e42d84610100315403421742c1010109034400c0c510744821039a0f000b0001c21580300164001d100580302c410090341680100154035030484008000135841c030108da031109a10080040585440d000c5644401060010a4603840c449035180d001400300f1341e00c100310f035046171000540e0410141d0b03d40043c5946810b00150080034880300014075400740425601620050000c2014992100c0d680c3c48015000354014843d00500501b003690102e44c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 486708147 1250 486706897 486706919
    0x106020d03150f06141624110d0911030102030f06010f050705100b2e171003110d140114010b1e0309070b030109020901080105120703080a200c040501 66
    0x4503100c1c503020f90a03c908001c0b003929801d1801000700a10a02800400c11070007a6045082000d8000d503100000724151000751300c1400c0e814001042c1160910b500c0e400c01d01042021150b8038050180009004000d51402d944c00586110300140c2c950f0001c01070041c020420155140600c4090b2210401c020b00030348281c503940203400c40070300941c200043c00d001a14480d0000100201d0040c24400c03a0b22684072002c404658118580c00d440003030a820304007407500880c440c14030300c0032601000c2c090303d0807215038000c240385400018540f180480d0701d0350180d00c0e6180d4404105d0b501003111303030f210b1990a080c94001c01e24070601d804010706200001469403249000c9488110b414035407a090f9000340100b80146500103050890148200d03400060306d480000061406000c1d01400940d580c16940001021a00c2c1a0441403182d000c50942184600000603250304030b03a40301d14840c2d01c403080034105860b040c4600700003400e802500900c0100340d840c00b182a00403008202c5007000243d88031250a01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 486709397 1250 486708147 486708149
    0xa0b030a0b0916230a030c02010b0a080a11040603151b0c0510050c0d06090e0d09120f0312050117011b090315090c060c050d020a020108130f0204050106020d0315 71
    0x2c0101c1440740b00e10861407007413085500201800001401400310140302114544c0111806000a9614006091940d6082c050464100c00403113410fa44281000007807610349082c50b4004261001600f802c140c00c0c3c0f600c1d00408002c50304040d501e041d80c2c2421102002401d882e56089490b40811403e900f007146c0a0b42c2001d0501c1e400c200100030100a5207820402840054072030040340703005026440304240c59010b204081c1507550342c046003546245401c90724156004c90500c0c103010070200184106001188803001303941d001b0205040714803050905039078020840c407149410354108400071407080814040500700c98078100003040710140d950107009401c4d40864046001803da10002c0010030748500184120700c41a001c0002c1c5440d01b0354070440b030b4510310741c4000c02003441d0081c0e5000344042070000c405e240c400360011b0b22150802c0d50008011120040c02074080c82072110700c4806210321a40701801071540174004120950315030402a543d00500e6840000003030801c040c881c00b1400383c3d00340c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 486710647 1250 486709397 486709411
    0x3030e1801090504060b030d030e07120203120a0507061a09060d0809130b03060a0902032a220504050102090a05060f0708070813140406090213090b06090a0b030a0b09 73
    0x218903420200ba07240a420060410759a454460070031190036641488080e414528680700010001c56030f809440c1007501540c054081c5100720204180583c4000c10358014210301140440e40e608030102c0180c410380205413014041c40c1c54035410340c0c4d40001008805804100845d19494580d403003e040050f40c0c420302c44010244082849400498103204203481c01c4440683c0e00815070f80c0300400400c0c030b00b0404070351b005501c5d43c40f00441401d40c01d0074420040c245140c070401400412802002214074120b5144041c042c80241143d5a03a88803580c9110490407500b030800e00460070036027070450107900942e1071144030300800354000841e850120100d910451040c2d80e58bc2c203151a5031903c4081d900a140103071516141003010403807444500008002a01a070003803401101c0e50341d8140030807601c0c9034000d080307001d2040101402e20000b01032048225042c0b1100401d04000c0c1c5000304032039014140811f900091034840100d20389005ca0065032180303060f100c0422164240b48200300d0007901c10746041e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 486711897 1250 486710647 486710689
    0x17130302040507030906090503091c0b071b0f03080a0b04090209130f0203150703110405240c030a0908120304030903031d09040501140a380303040b0403030e 69
    0x810040c1080d40005038410118100044c1a02c1c2c152505001d80b001088200c1b030315000054968000e141446101c1d1410341591008000d990703160383c07803405586001d843c0a0503c600b82032040b0b0112480421032501d5540b122000355840a1490050000602a206106400d0901503000030a080501c80c252074190004d01c0007081e9190078045201042c1c1061046d6079180c0b00d200c6840150720f040003d0520514000c03038500c01d42c900008000c00301c80b65043c103400516000c1108110030782c1c0349000b5440c01c0c0b100c50101c940d428800216580503214221014140340401b0891228142e000b800310070844114405407007001ca540a0403c2032844101c90080218030105414004284203120032071240e01c16003d141480785100c000106452000c40c0c045440d0f07915691510340d1004100021030308644c142c4818052103005403d20301d102801540002490341c070100340f01616080500340c4008800010b0700ba00ea44549816040758958081d010541c0072030034889180510742003a02002c40b081d04600c0072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 486713147 1250 486711897 486711899
    0x80c060f010e1b030c070c0602030a030b090118050618010602010c02070503010e1507020a0506040c031103060105030705060a120c171008030d020715050a021b0c03030906030403090e01030303091713 87
    0x42c200f01c0790400303001d058400c501071046000250511007150f002c0c2030103400540c1c0381c101d904001000c1da0b154103078583c045d8156400401040500926020f21507102580100381552070718007007a000240d444d1f0300484d1030702c0c00b000000c0b20b41c1c06501189000d8215403c1c0d50501380c03900b042c10700b0f94260b041ea910180d40400605a10058412107094206450b4415914205036940700c891402005440507105210100c5c0c00300100001c140b014085464180d01401c1d2941c940b40000b520b80403288509400742000043c00082680705070303c0d155020040802c200204503100100804546090402c0481901000003007840310600c000300508450250703008624140c81181e08901039049550119001c280703820300d0029291142c09050b10400705804016207a10300c00c003803000d01003001c02e042e0300950401200c58401e910040202c40011105481c1c00b0f94a841e245002c40c1c410710305521503042d01d0b44a000200c00c05615400c42c0d407196024068030202c100c20900c20940d948502d04507060000c40c0614 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 486714397 1250 486713147 486713191
    0x908190e06160213091b060f090915030218062e05090111031206010e01050703020307061515350402010c050c10020a06110406081f03080c060f010e 65
    0x200c800085403004c0d0010000c42003034003a090980300c03129012100d082d48800d01c00001008065050001c0842e03181034104180d585001403d08117083c01407200340c907200d8400000541001125a00465000d002c03400019200740c040e001002007601c12500c41d0244103801901c4681f4448c602d542c241c0494802040e030000e403a07007500d05600003100b40b4188840d20fa4060140c4000f4006441203040340c441d0031a00789014030004010318210141d0a050010074001c48000c60b03400002c1d580450350043c4001440b01e0200118008030500313074000015068109188002e40d6813002c3e4540580c5004441c6030aa0f05035048100801070884111220586c1a00700240c0990b204200341590107008509272265400b502d001300e628802c3c2d01500da00580c2c01070f5036900801a0600ca285500084804c109007454201071004282400c081c0c044200c0016409084820a01c0840c000c001181d00c40386840c0d5580f41141d10316110076044a001403000c41c0781d40001248041c0300c11091090800b601d41c03030f000c048141303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 486715647 1250 486714397 486714427
    0x303011503140702060402100f0509040209120f0313080303010612051806010b04030b0117121e04091a030d1202130f0f030b07050f070210120908190e06 67
    0x501000e04041e266a0800b8410060074052030041d6034940c040c00b410302d03081c018815401d87c150308c0c081c1040340c954030b012034840d40074060302c100000807900940e81e009240c000a90800c020303864022140200ca0392045200b40000081c91401070360111814103565500b880790300c9002c24410400418064625000c502c0d08990149603c010a11103c5900440e9960b2462425400340c000b2241d00c50000303400d0081c481300c8900c2500402000c0f0044425a03292111a615410702c1c850a803500c02c0049202c12070a0350400718900d01c901300300001d640b43c640d0360801d0300c0074010101c5010000481c06078807070b0440c00e0120b03441c00c2c042500d488030004010410f80c0303103009520010850244a601b40d002280c040b14118191000301f2500c0c43e40c91807036040d41002c5210b103802030192028403408024900304484110240c0b0381c0700b501240c041940e10000003041d1052154a60b101c07002c0c51030418080100310b0078402515103549031465a048218241c5070544900742c0f03030a101c070750101090107115003094900c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 486716897 1250 486715647 486715679
    0x2010c02040216080306040b09131103070806190c02190b0c210711071404050a020d0e070807050d08030a0905010b030d02060123100e030c060c0c18010305030301 71
    0x24000619207150f0302030651407540441000c54456070000b09004440c9054010035408101c200c80380c1d580c81c00d14440900b0102041c00740100100b4161001550540c0c05214010007000d40c80d0940d0418500045a454181d400d0f000c541000d91400d000310780141e20000d01456031002d0304400a0710590280c0301d400c4801c3e8000c2000b80320b84c00400400140c42c00704070400d0320400000100d102903040640003e4218419200c0d01d08080e480b406040051054422100c00d4070742d415900002c02e40c952500e00006440b0301101c20b0f45a034108440c00c4050340000440604a07400c0320161030201c1c1d01c80040052000c1c00c0d00c400340c4400400e10102e0204d80950340b103000d40d00d100e07100014140140d940405d081451014030381000d60040c9004000030321a0011841a6503520900041c24008410000c0c408043e44100c1c40200600e40f0402041c0d510200a00cbe181c81000425103900c0d0002c1d518299a140b1003603010070301030b0058045118584032155143c6060ba40c0c018017841c1180e0034078200b040b100c040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 486718147 1250 486716897 486716899
    0x301020405030a08120603010506060a03050a0b090903070201090608071d030a0c060c1203020a0c03080402040915021803070b090603070203040e0a09030201050603060405060105100c06110408062202010c02 90
    0x400c200000d40d07603408220070300c081445842125160013541e01d41884070880100074a0099043c002004942c2d91140122404500e640c00c0024003600ca401c0c040c0020954440d1540d0064081c0c406e00015880003c060807207a4803d994010040f074991108541c6040152007030004078200c08800480b0208601c1c030030fa150540a0201c6048202e5505c518555948036801003000c541118106000d01c80142140c9010030243c0c20154030f024075903080100712003007101024007006105004181150f1710380d00098074181d0041c81d010110186000190002d500509211031000f04000d8010703142d08000c00c0503c1154175484180e81000140313020f021481e440186070400314041040042000035080148502503070161000290841b80d501c1c0203804c450014007030320300c6980000b04000004400080d444d054917070640306d40d200340700e0b1001c06840f21800f10200404403801c05012882c0048507801034400c54408204031a0f9544800c0401c051000400c210340c80d0701d0399800c5031b000155010700c0600c800144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 486719397 1250 486718147 486718151
    0x9050616180902040f06020c1c11040903110c090c0301030b1b0304060f0e1b060c0c04050c0d0b100203030403032012010e070e030a17070c0e09061e060108060301 71
    0x703021070004401c15500e40280400580c0031a0a1000360140c806010152600e0300092494481801c0050b128284010280e07018004c80007074602000f19810380b1003048900a402404101c51030320300682161212502660980314161600506140144119008d03400034242e141c030f940d0840e00e4006000c0c40080c840500048520f0801101e8620303c4001c6100340c0c00307042e00181d12034003e554031b0280c401302da241229690010000c030422010b51650504121802c45641da41c65040c0c3d03c820b414440c041d03940c19031080c83e0504010400010000402015551442c00c00c0310701104401c0005080b1581d140c00d006034000e0000400090181d0b01858041600a080c8600341001b0002e020f100c0e4403a030030105170702d081d1100411068003440c030840d03000700041c10485018903024000c40d07070341c000351030001e40942240508040400980d904a560880c0c00c0074038021415194054010b04000a07240745e66144070345400612011450500081c0c14030810400e0b4038262a60ba00455000c50081c040940c955 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486720647 1250 486719397 486719417
    0x11060d02090d0c0816050f011d041d10020a1d010905090703020a110607121a0a081b010e062b020a111e031c0603060614030c010309050616 61
    0x20b6640e114100c600340c41900c004030403034100321a81e03061040d0340715403031100d2103a00400d101c02e5444100c0314070b19803003e207080e00d03920540d0361307407000140c00010055420a02d402e804035070000100c044100391302402d108992482c40350544040481c80703084512400105045031f166040800c0104090301e0410500d0402d1182d51100c0009885404c01d40b004004a9800202041c225400101052003801340b207010702520700d84a01d0142428034800c002000c0d15640701ca100e185000c0642000a410002900c0c85041603240c022181d5114501c0a03140040d40070f400e0310008c51742c400c1108210b040000307086141420b0300c0c1c003035031300d80b88031120044480710303000e440d414141d00c034144007038190130b00c4560341d0301000c0205410407400c00c0d0300310070084149013011003101c50081000040790382c020406000e8140c1c9014400441c002446250801021541054000601c640300c000c40201e01110880c151a08202c1460055045803011800101650001c0001419601c0b01960410510b10030b0f091900c805 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486721897 1250 486720647 486720649
    0x1d0307030b33102102030a09120201060605030601030f0e0f03041a03040c05040c02010f0c0302041d0903030c031314010504060b0d020a14030c030102130e28051e0f0a110711060d0209 80
    0x10360401c6403247d0701e403552461400701380020702030b030501c14280900081194904214000380188801004107051503102e90351480aa0060383c014aa0000d4000079906050091001d6030f440354818440c140014245400002030000d0140c2203900955000742106485403408003130001900108194105656076892006241c0100340079a841b00d80c05980d0040c3d86d6400c1c60700301c00039909441e24551000101c402040b07454080041102d81007200c0d608520b03140e60325610078100c00c0304c1c0f491004112000b6000c03015843c1505410140c020341c4214801d204c504000030a100030038030100780c0a540910000310400403a66000164800204047c0589210301c030000046403ea038800a0720140080c6200000c104802c945003a4076001025007c1c880d0900c040c4a2001400e40c80e54054801025515030109401004207110500283c10381c811040c45031401e40c400c1010b110080324001011824080c0100c200c80d0380f58215511301e1703406103081c0016a007490600c151500014114001d180d400c000706121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486723147 1250 486721897 486721901
    0x160e0d0c0801090c0302090106090e0f06030705060c0f100b030a0201181d0406050708070518010c0f06051b0f2a060408030103150c1d0307030b331021 66
    0x3075500075007110844c0c0380756105120311902c0503800300b03081107618401801004d490144c16600801024402d07a03e41d100c0c400081c0c1002016401190b101400140318901c2c0d80012548107014400c40090350b00514440b12504181c0c0d0081e1030740c90b41908420302500040d80190380402c1c1c040165200c620710380340c40e0311104a117400c00315200000406044200800c001c411301a50760300c08200e207021140c9040c411006403c50064205400b590030941051610b0307030344180c41c2800f5464200075200f030702c041c0b2400c0810082c0010b40c0c082d00c003015206040700b400c2c05070100701c564103c1d58600852500e0170852115080080c5415404003103001030181a0310030004014180c02a4010554545d50794554908680700841240e10181d0040c1004c0b10724400540145084148440030310924141008038400241888183c1d040101160154001e10954100c1c0340458140180f05d01c000c58141e541c4500b07200c04818004485685c0f00e010b100110501c144114070a040b00c40070b6510305100e5150000d08141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486724397 1250 486723147 486723161
    0xc04091a071413030b1e06150c0a0b01030506091c1b0c03060204060f03060b18010e0d031d0405041101050c0312010b070303050a02070203070e13200306160e0d0c0801 73
    0x503031000b180e00500c248107156035010b80010240c1c480590801c03c0c6e41e10569480d40040001f8030400b00c50200d032159010743e10031260703481541002d482c3e6103a030f1454003111918003030009a400f48034000c000b0b044490b0020303c1144d034a034802a003004181340d82408880d143c100880a405040034010b000000075556640c51002c0c41c4181d10142c0c540d41040d400804c8014400b032000105828081c0c2006600e0b0070408483c425000038503115445e40c44070700180d80004203d08403641251500b4026000d00d07a02c90b404959080e10f0710100b101800c400c0c4100010345509490203000c082500c6200049503000c0c1004140c03084c848001c1d079041420030301a9402202d4241d009103074040380011640f08050f4903105141c0c2c04503041c0e808500f80180ca802103030b5030705058015055640700030408a05000d040006214000e54000e402014003124541d00000b0480003d40d0340d8000d20078200842d00300c0201d00c2a2845103010356490031a100c40c5c1b14100400220040001c1d01c1200481e00d02003a004e2003070003280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486725647 1250 486724397 486724417
    0x2030a14011805060901060f0f03090b09060a05150612070c0b090d140c0309130209030d030b040f06060804080d0603081215030f070b03091903110c04091a0714 70
    0x40e4032041d140e203002040d0f03000182140c0c49910044014000340380c01040301c1b28499002e20780141090040b030420b800802c80004050301c41e03000d080c10010039410004200703115803143d070814011922030800d07001400075042d0b0348662010301482090015100c403501c017680508103152280390079585440d465044601903902e25103e800c11160740e12095000400c0740300928011403c24135000d030f00358002d516401072811892040700c100166200d40c4d641c0340c060b03400010008080d20324840e211341c400740081c0b80c4a0304145c00b03142007040d0180e82610610450046442c282ca90810996480d600c90441d03501080141041903603c100200100d10000043c0c01503482c85c10021600d0702f07050030700103200f801e20764107a0b109038070066641801c4407011480004641120304c84a03200d0b241c0b085e06600b86032a03400340101041d141c204040a140e03102040b41c07449003a41003580d200080040900c416500c406002030031041c1540703c50000000c400c1c00c3c0ca44c1c0b007111850001680120310312849107681c000c2c0010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486726897 1250 486725647 486725669
    0x60209030706320432090105090c1c0c0c02090604051026060a0506010206092817030c03041b030812150907080a0606020102122a0f031b07031202030a1401 68
    0x580d9140d54501880c1c00b800000f142c241b086503140c000007400490008042c4900d0000c04102c2c9076401c120506001e030441801030307090140414040008125041190041e40308101c070401003109820188681c034000e06010600c0740959041c54464806108540101e8403102c07044907080444450900c111401403001c035501007180c0c148a0700091400102801f1902a81c10407100c11b55a0900502c94902c0c8104081075642c0c2c00300d440c00c2c05011009804060092030000004000340c0c154954019032240e4803503007042482040902d42c904803040c0d6800001c007000c0d0100120881c0118000d841c96104480c000e05084041c1c080d0b0100f821a80142d4202e4003083c0c45c501400815122801035070060140c5200841c00c046030304541c900c81e0b0201600019868041a02e6100c001d08452200e01034601701c90440c65443c2d030f00018042d01c640c0116500e20342404107501c84510b0395480c0080720411901660f800c0c144448030340e50074009500141c85016020b640c0c0c943c504038010001c0c0d09500802c504480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486728147 1250 486726897 486726959
    0x90501030b0609131205040e09030a090b0415030b040f0207050c01122901020a120509031204060e0f0a0f0602010f14070206070311040b0301030602090307063204 71
    0x209a110010b0281882102420100300d4070409040c03929407000e4100e018001050004441500c0c0707071095411a83d050b050410030040000d400000a0802060594840b000d850303841d8000c40301402940514980450301e090304041c40791107030304445855a0010800151a2010340688080303030b004800444564108400c0f0800380c0d81c000540d031f4569201c414081c803804003002146020405a44980569205c00803015401d591007001140318481e4000e40c2c8140002510f41c010b040c03500b240180360b12901c0381c045070302c070400030100030348044440c2d40e20781107001d20400e4100b1172904008034410340c1102200c1300c00905000f640c0c80d560010039040e0000140349031508401c5c01520042c20141300008002410312a10b07036400155980e00421600d00050701000b0604507000c144501d90017a044028040008402e00040380d001340b00342000dc80454000d10b9031180700303440c00d500124040320143d04d40e10340d1004141992240505010701800d1852800703850300207d111000d41d19814130715061283d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486729397 1250 486728147 486728153
    0x120c0e060418050601050c0c010c0503090901241701060516020402030c0d14011202090403020a1b0603051b0a050d06080106170d021c0f0e0a08060915062103070c09050103 75
    0xf095541002c028a40f032441c0c44c0c000d1070742079500c00003110594104110144e092083c410117009031009818010002289565182d0900000344105803a000c0c0a02c40d9403401d030881401040c408440195107003914900b40c1c80c0403c1502d01c2e4000f0f00b140c14840b59540392100c0140e5940c40114400e03ca0503110544806007140100c040b00c1825107224681c0c020320006010701c842552008050a0b41120401d0850740c0f240342c100c1c241505004c3c020144840c07609805211000400110b041e100d43d43d8040050359915003003030303007458a1510481da0701401000710307050580c820300c0200240707100d03135001040d400d6840c20310500311403155100c22000504a2464141800244185000c00300184010121050444e01c01c1c100441c03c858080705018a4581490000b40500f500107000c440040145141940c0c50f4511601c071001243e01e00c010b0701801c410072840000c800401e6010328409400e110400030360b450140130b108250492a13400744004d000b0341000484c90300c03030b41c4050321400d100480d26524503d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486730647 1250 486729397 486729401
    0x2010e1c06020d0e0c03060411130c0504030b15011d0402070c0909060b0a030c0501080a06031a0702010f150510030e060408121b03040204050a1b020c0f0105030106120c0e060418 78
    0x100200100790443c2c2d1091002d690001107c3c1c4e0440d070080090b075401079a410005003003101d0f0101d5a076019041210070b42c4866046000f43c01203a0042c900d902d1555500182410241010071358107011551280240940c011a007a20303605d6081c002d00014a821044c0d15a0b010b0440282d00ca09a901c0c5c90310401e00030030882e40a03408a404040e20700340311050440d40e61174070912107400b526041184c04000102d099165421030f00041d600700700c002740b21041181309001412002c441c0c0001560070480c0b01c032031441003846914490035111110544950600003001000700c2e59404e480205130300c0c1c0ba685841e2840c05d2016600551066400036a0380d5241034216030b50b1900100004074801c0e01c0e604072100345c00c040c0d003141e82c8207504076000640d959172001e010000b00400d0440380216003000030746401003900001e01e11880c000446035000e02005450044a11341f000340528000140396aa120082203695000054250301034100030b2281d00c4c01c000402c2480c3c015171b2024030b100e00940940a1a07801c18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486731897 1250 486730647 486730661
    0x1507143a0305090304091a1f030b0a0503031b16060f02010e150c16060c030e01050c091f1e0305180a0c0b070c12081b0303100302010e1c06020d 63
    0xa0070705102c10715080d00b686842c1d014a1040b91609038544408103008078680e080041c9101c002060a64403061071251403140031080324550021a10f44015400d075464501382c0c0c00c00302d03000100114035180361380e1401e043d40000304e40645002d110b8001044039444511204101038003590f0340e07003a0300a600b040004d09507981c0d06190710703594200f40b9070320a42000700707070550380e211054001c1c1941d100a8548401405198808081c00b403c1c94505a10070141d41508503010408080703000340000d07114110701800f907115003500951301c1404240c2e828401140c40111710702c802850b003400c80713103001c3ca48150410512002101c0000071355130070400014141111050410b5052007000b070451608941d50180342444501905004260108000c1c08118001c808036003d00345180d45082070000c1da140c0080a034014602d5208c4106200900c03061900000080c4c0344101120443d10b4500c41c5543c006440443c91400901e4106012411428007980480d000d10346140c0b14043c0127036941814400350302246c41c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486733147 1250 486731897 486732013
    0x305071502070c06051b0105010b09041505060a2601080a0b071d01270f030528020405060607081903110c0a060e01021903020a080105150714 62
    0x10501402c00030800344405003050b14098201035907100c0d212500120040707003c00d175168103582443c0010900010040142410710710546050145402d41d2899640020300f500400390011028414405a280b0952401c1d05080344d00024454162500e80440d1100c8826041643c02d5440040c90300e007040b0704074000c02d07400681864400603004010034000060b0817002680d80c10800808a820600c1048000410886069103001826a596030400380c0300c80b4100d00c402e54960194030700b407141800b070710740306011a1810040100c01601e2503600b000000d02002d8142600f02405015240010705500c0052600615031700303503030010809082c402006d451f2515220140e8441c244061803140310000365464000341e201c00081080d092442c1241d009005c0c1c810305000d5021501400000e403500f40d401044406a5582c800c0b103540e0b00c40091003071204440360252403010003001403001281c480c49407410114410410340c0c8004c40080e94103001c00a81d00800b59800c02d03070014105141100850f44407240c1e40c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486734397 1250 486733147 486733151
    0x60702100801050118060f210911100e2103161b080111090906181e0105040612060207020307050a0f08150402010e010818010204180b12030301090906060b030403050715 74
    0xb046c941300524048910019030180041252061840c009140c84809501030b111007c210717080340d40c10f141000c5115007684a014500c21080b8254a6114411207214120302130f1182c00103407104e15101e189020002500e03200b600003072001c6000d200c40c5806501039a8004c00341c04020031000c06034028240410b034841c03a03a0f07a150610800140030301c44156a0a0441103c02c0101307655544003041c5014407890310383c0d40400c425820012040310b80006031000a80c5600d018289a03240c505000c07c68101d409140c2c40604d6801d01240081c425400800c2005d1000d070950744140c2e9500c022481c41c41c0030350404901142880b10038081e000040090042800d999495604a0305160f000039000801540e4002e0410240b940020440b004072401000c01c020008021952107030f4912520f2111961400f044413100c0c240745d600380c2c407803032b080c442d202c0b030825120091450740e440c003110f10000f840d000300201c2e41c50781ca840c1d0009120100c000070318807950080d1200f603a503c50f0741c60003402c48410140c070440d8481c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486735647 1250 486734397 486734399
    0x1030b040c0206130602040806090d090e100306090302030c1e010e07120b04140a080a030c0c05060c0315060c03130b1602060a050d021b07050d110d02060702100801050118 75
    0xc0c1c1c2c0000c1c0700360014015020480202c0031810002d000e881103804c40b400718440c0313205010044d40e0000340b0343c0a4440d0340d544d0044940d11002076048212042d40e44041100000c1e0701413010039460f6029007040d03031003801280c0c42c28200b01041418a07420550751102c0000c811030340015040203004040c251010350018007442820040040c4509041c101d01030300b500d144400182c10083d400001d9801010510100c54942c101443d1489181e441030b009200001d0402c0c1c04400494000c0105d810100e43c400d0140045903500c648049071034000801c014100110b030500400b0341d4072039400502d48034a549000d10703900c505c15003880c041c001e00e03513200741040c0a0030490754049441d4500d036140c2e096411900aa62502c24080031a00741c041e2461498190b440001c80700702c05a05000c142402a040c00140c90415903918104034462060b003801078400b5900c00b102451034509404d017882c2861009068a04000716074010500425000903140046046c03140148401c2d030f0080041c15004c200e09084440c1c80e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486736897 1250 486735647 486735671
    0x130c0503040f0c0e0a0207050c04141303090f1d0105030f1b01020c040216030e220905070306150609150c030c0c05091603150f0302090414031801030b04 67
    0xa00c0014000790040885070144403c03c90500404401400c8082041e101c50400040400082d480a003080f503035486000d0f100c42480c1410301898a2086c03000f00192000da48500b078034001141100812000c0102c445404141c0d0309211710154040d0281e905147e1280d030b80a00362201030881a00030b01c0c800d0303005d10518000180c0006006060f480c82004040d8031026020040c1c0c903110170510500c2c1d0050001c181071520055a0280c450924001d0742c2d603074141c404d12014404091108408007100400f440d0101c0080e03405500a500b907103205034111440f03c0c0c1d0f2500c80c1c81c2102c8840b00d036290007107000c0700f04012841c1d00128100c05020f0480e407400c46014121800f9100c1c103400340b8000c00b80304406017030406100d0040d4840000380f40190002081d450b00c00e02c4c403041c1d05070140c507960103e45031030520240c445181c048031099440303200ca451100c9003540c0800c40d010344024422521000482200c904101d01400640311038013a00d0110803080c03d00800241c183c5540ca040e45000b680341c40303052000307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486738147 1250 486736897 486736907
    0x100e031c06080d050c2b030b01210207020307050402070605060907050f1804150b13060e0f22090b0402090c0a020706030e0a0b0108060612070e01050118080615130c 72
    0x20031000340c1044c0c0c0e51011110740031030400644d06240720f0048646c1c10100a0008545072240741100c0607a010404411028015100421290b5200008225041c24204441c2496000303000250004044441883e541c2c00001e0030303a8070843d0100d4a203034640082c00442c2c1003901c0ba158010509061482c24009107142c5552036014224a080c0980c20440c11a401500c1c0e503444108011114408000300c181c551004c000e4590010b0000d001340b510070780c8005000c602c0355440561003003000b404486c0038129030080004e180040803203641e01e450741040040c0303441d250303102e003100d400e2050f03280b40d0481c80c06004108105030024a00741c0f407080c3c00c00260700646c1d8041020b1007500c10340d0400060141e040742c07a09151820200004061a13490702c00800c0350b050020b42d2034403d4404485030700204607010466515022107100e000c812244080050056600480010280c0003012404405640d904c6100902d0488107649868030121a1180d4100d80d08004c00394185080e1440024070943c0072282d00100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486739397 1250 486738147 486738163
    0x408030f0403031121010603060807120c0f0e010602010501061e03110c01090804090f0c0c030309081204080703030b0105180603062e020f070f0314100e031c0608 71
    0x14400303010001404041c026800102100070058240c0c0d10f8896080341804810003890071283c03040003243c00007a003244203005000907640458040e0907514a45144c10642013440c00007154080b64192780419101d11110904005100542004245514000000c1d085440680003c410400044582d1a068400c4840480b40c10160710340081c0d038551a080750385682c0515410b400707055080c03181001c00d0180703020140060f0b80002e0410803403640d080f5900c90485643c00c01c03032408240e21200810120b8025400790b200303240503070805403400c0007243d90001200b004480440b814140482d0460903d5458860010320050a081151800c0c021810741d0345401d40015040b4420900000010499100c001055807001101c01c01c000082ca038025200450301080030129006200e0420b802c03070750b03c500086c01001c54540c0c03040700080d207040d41c813032482c00540d5103403102e900e2103000c3c0ca80d14640301520446d07005200301d40c05140c54a06080c800a030760aa200c0c1801002401d01c58188001d08001c100a4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486740647 1250 486739397 486739411
    0x30c030c090102010b031f151d0c040f060801031101080103080d02070f0507030f0b07081608180709021e130605131a0a081806070318050102030c04030b06030303040803 74
    0x140c1c40386500341c0100d001d0019414620307050b0203040b41452240d050080e0015005820391000c0c0710032030803200c07100d401c001d141c420792007045850394100281c40d01c400409508a0b40b8000e20510381034507a0600036212840c3d5101c000090016001081444201104031b81a28802d28213151035500d0f58440b0005400b0b510b1000b5a4583d000031110f007088064052044030740e40c030206880340390b5a2030504000d002250702080d00c4c50400040001d050707503c20400c59118003414510302a8003190315804036080030000f88541c04000d1002d0105c0e02000040084400501480c1c80144e1386581c00c1d01004101550f03001480606071003230084401c509085240d04040e1242d03480d040f41c0b11005001028298030300c0c7c0d1702c507164048a4000380284084000d0003007450302155255130b51251140c2c1001c0281c44c43c2c1e02c0f203130401a0040030224400912035000107094920007298a0765507451922107078226842035890441e08000003800f00108070f05018aa54800d0040300038505625041d00c0744241c51000034100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486741897 1250 486740647 486740671
    0x20a090b0a050a03080705190c090b0a03050f0d021011090d02041407050301050405060a0501020604020108070908120705070e040807031110020301090e06010f060c020112060b03100911030c03 84
    0x26040944840300072400418005041c070b00c14035907908103065a6846000d080e41d0038025182e203001c42604080e00030003560b80c00141d0032605450841d001e4010018220f83c0c5501000420001011640c100400d0101140d04006082c1190b06040b0103460103920f4000c2060f007604140d611010b05058000341c44074801e05680d18030400c0203520014000b805042610b0f00b281400300c041c001503607803100c0518103a0707405840412050326074908004c0421501e116030f40c01a8030206c00a00194841d480c2c05800601508103007800c161640005405e101442c928a05032200c08204071003440010800780e00204005240d80780142026290f0403d948506600a420b00000300ea035481c1c0447c04101040885100e000308540b6540c4451042c0080c2c200c9c0c40003011203104510011072000d81582c00d44048604039220559000400d900554901c1002c010b03000c1026a00d14000500441d4040194812045035079010102420404402c003203401105081d5851402401000742071017180301200c4d0030110100d20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486743147 1250 486741897 486741911
    0x120a02030d0c11100e0a0210121103010302100309050c09010909230616052203032006060f010e030712030f020d0e0d081e09100c12030504020d050708100e0307020a09 73
    0x1e0318500308041c6d030003d400c40040189031190950000300300c2e00c2c1d490442000c2c015101d41c0b0340c071046680001c2c000690301c201285c040d15103040c0264400b211310344c49101618006244140003d03401d0340241c5c0304094864403402100c041081185a0705209140c1c141c0c6022581c4000203904e90340c98008180700d500340c44101c040c00746180a00e0540d0310003003280380d80710000314800c00da81000e16030501c0b04401040810103200c07040c0441400e900c2c4c07812070350802800b483da134a404214031030302c0d0309014505205c000030f1109420b440600c01c0078094590108506400909403034010020002490684115006040780808840d80040000500c1c4022070380300341c40f8001e9050040003481000500403036110300816581107400c800002d4503a8900480302d50300100da10030810707120703070005070030041c00800c800c408609914040c0d80442d0300103001906094a00020743e48091912035560006640e66100d0503400580b00100c1c0102e522100d04800130314200405580400c0d200e002c54090790b580c064440b0701d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486744397 1250 486743147 486743171
    0xb0607050a1205042c090c0315070306090f1b05070b041524030309080106050306060d05120705030702030d0914010f022e060504270302120a02030d0c1110 68
    0xd8030302074001c0300d4044544070401e10360350110049105c041030110142c3c20009440141c04910061001d50140140040c041c60b0141014000801001d06c000c0c1540c8003000304440c41240b0824551804000e0006401541c02000000031a00d001c150f0040180800c800300004c0c0003400481e4006070b00210030300303d01c01c01441c0700002d00501d0481040c05101c0703440c034621240c1030194000880707009031218940c1507282d01e2503500b41d41c8640100d0390158403c00103d0903506003035a0250016001e04151000b04041050445160b80056000d41f980d81c0049414000e614013403042310b0074501d9900b00918050b18004d04200d02540d80c004107070502149040c1984207a0003404101c0040100306802c07600c0040001d00408040c4010003045c0125180c0403002c40c075414503228018901841500440c13250b8500c03502d520100018140440031400384148403007084244401501c2d5207010760700a0b54444d1400f080a0044174413014000003040003541b0700c0ea0704140013084402c4010102d0f00040740c05030480c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486745647 1250 486744397 486744407
    0x30b0d0206220503120412021c0c0e090102040f090504050c1f1211070213291002010c120e0717010203100806040819030b1801090b0607050a12 63
    0x41000e90820030006260b01c2c841e80061448264064042d0404034164581c028140c1d52408604038107648002048144144140041031440140c4000c014602d242582a405100380c0d0500d0f100b140c60041d41c903000e0280c400c00304051036020f07441c04000c60a05240101e510b00c8220306100700025680d903000807805112090051001104020340106034584030401148a0403031040007003000505088078110700a074984c042c0800e0302c007510007801d003880500d030200140810780c0c2d044450081d81e1250329035072200d88250721280050740c100c41c0d6030320b4112038014071480400355500e510071039240400900c0c202c0d82103001c0300074090600d280041c40c016118080c9152100c181c00070400c09900d05041c800c282415001140719502030100307074541035505d2069540d03410050342c006220840a00c111115592501a482001d603401e18002c200031a00c140403543c4051001c090311503201c0f240c001480301c0320180c012051005004c3e41c0340d07854140759440f8151194480f040041c03010003180f201c485c00610078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486746897 1250 486745647 486745669
    0x7111b130501080706030b0a0e070e061b01050a0f0b0901140a0801110a0f140a0305071b0f0506010b070b0c03040c0509130209010e0705071502040807061107050a03050d030b 76
    0xc001004907507100d04000e81d0398413040c0f05440009050010340091400c00d12403210032560411100d80c010703190041c0c2500c0c030b540140301e00c5401075410b112031902d07d625403200d442c521114030000902420060307505c05c00d03190900100c1070441d0405910120f10344070010f1050446880311a17001e141402d1310700054540c03036194407494066013060001200c0c245500000e000706074041d201c1c0030340201d10b8201070340c0c10b49581000d800100f5040c0581c1d508940640c00c15640840586400703c00c012400f000707040c03841900d0b40c1c143d40004200c0414400c11000b000b05c1030140003110103131410111b2503603960030100c1d8014440c0c4040a00403010904112142c80341c0009460000c2140005c1d24060090008000500070b0507845041201d0002030b18199000b060b03405060255a000d180c10b070591218020a248204101e400075403c0000180042e0140406005004503507504007a018402020138544600340c2c1005108a444241c00c00c00110700003244034000041d0304010810700c01d1000024000a89 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486748147 1250 486746897 486746929
    0x260f040303090906050a0317070602040302150901270506090307051c05100b0d1e0c151404060e0d03020115140301050f07020d0e06040306150e07111b 66
    0x42408820180c205031a2025507202c82020030416664204109486115102c040c00e40c422034001c600c8010001c0000700241c0e401074001518040d030320340c007190380034441000e03a030448600855224030b80e42c0d001c10001c2d105203455906518040d4461001202095103220785032050b0030024443c080b5450510119005144c02844c0704000344800c443c003207002021010403a10360040440241d456a054418000780d240c2c060006c3c600082282e440003101c000c041220084003906040400000308000c640c540600360011840001c8a4019005000b0f01103002c1e842e101104244014458141c3c4031690020b444800ca525409540700350a069004004050303a10705188900b17800428418410941000c183d00150300030800b942d60442c4003e17101e5000d45030170005030801c10b840c946d0300c3e10a1020ba44d00c0d01008100030726140da41c1c3d491390201c0705456640b131050060420100020080354007565481051400c003140c0d04a000880035854030260412a1156074220002209548582c90741044010f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486749397 1250 486748147 486748177
    0xd0312020d05071107030c0909060902030a050f0f01091106070c0801020f130501030c0c020405060a09050901051602030a091806030f2a142e080106020c0d26 69
    0x1810484440182c0421100500801c40140003200f4464000a02030112600042030b140c01500344800e802c00740440d04001d4404685030b030016805a5018404660301034401c5000b403210b405241031a508000c075581000c0e030b45900d080190400b04060404001c04084100c3d036250343c1c2c01c01c0b4074003c0c0c5e0080305504601d0640d84045694a045c00700e01c002403000030519034120307003166591001101907441c0601c40e01300003100032240070018101600695005074006040c2d075a0300303481c1c050340c0c42210002c885d4140d0682d1a50248000b5030080000d000e070301d0100d403004d0b514041d100040034000b42c90a12644cd410291081c0e19814800180e04c030b840a1940074542409440090810100040c46111241c02d0003803038507010b452070f41c910381c4014112541011100610104e01c02000511270076030642d078240b410761444103240e15915041001c030784d8107152640faa0030750424000030721b0900000392007402403030700c4100c2e000450319914140340101900030744070b107504986040300c806901440700d800c203002d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486750647 1250 486749397 486749407
    0x1050c120306040609050702300d0203011701020301080a03180b0c0d1805100819091b05030c061b07050a080705010806181f08060115020f0f0c0d031202 67
    0x21140c44000d42c000c0604840501c9415202c6043c8011118140d9810001d40d11002c04055210011003540e80981d4070a20b50071810a4449040c250700e41c814260b20074041d60000042c0802c8041190500070032003490300840c15503040c4040c40b91781703500e098005000c0c040d004800c003450b40c6040503010054800c2440040d00c2d6100300302000e80e1a00c0380791200d008619000140c0c0320001d1a82012000c99030020800d0880003c02281650300c480050b00105d40560086203540130b901c02c902582117424400c3e000d00819451548040c05141c043d070b040284250850b0880c004c00c0d55550701511898018591080c0c07100c60703c00342c11890000c2a40c001038000b02a01e50004020340080760003800c5400c280c1307482d007081d42d841040021042400700010b140c20321400200e900a040c400036141050704c16880c2900040d110401c4a08e0214260f111810030760429010404841e4144100070017181c281006181d0202d18016490700ca0b944400141d00950003143e181c01494481c840c040d40000c0a008115910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486751897 1250 486750647 486750673
    0x11071109180a061b0206190207052a0a27020c010f0c02160816030b130602040e071403060310180605040c0f0f08060f070908010c0906030e0a02060304020d0201050c 72
    0xa445401c42d400e140c04d000e5202e0407541ca0001c124184900d490a5031211040490300442c002500102d2050300c43c0d00c228507400310003400016201183c1200000b0751050030030030f001004641c50964028441105005007103800c2003845200c003440f130003111400035888007000c44c4024011306412a2881010b82090342e8103603140e4020500e1240c1811030b045545a40d40c4492005540da81e9001d040341d581420924108041000d5501451300b04211010402140009403074078000e98009800c01c03058802c0304d10511140c3c640100e0680305071180826883d04524080300041d840d0030301500000a00f50300c4090058445071404100b01d0101d5209a0800ca01c0c1001d040900c09100517000300c400c418001c00c404181420000b1041c01200d000200800c81980c814520900921000e8054010300a0220010074150300a01940c0a002c200d60f4498060502c0c010b0024252030060417000d006030014030300340c005030321101e00326a0f2058040d1160010721101e80b004032014032401100a0103400340006501e0350b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486753147 1250 486751897 486751901
    0xc0105070f081b010506040e150702160602060109142401030f020d0e01050a02270307031502180a060c0602210f0a0e06010e01030b06040f020408030403050111071109180a06 76
    0x31800c3c2c1c80000f0070a070780e681010310003203504050701b00059134402c4403641615109281c1c0654440042d1040e501154455185010360414541112026070418070060218060500c100840c414a01d0812109814812050b0071950311194498180704010740070081164003981020400c840311000840d03894404040d00b00c000e1054601c0700c49107508001c08075030302281d00c3c02640c902440701150702c030041e411a200d14a8212103840d070981c050064060000125460040020101505030070240e60b038030600800007958110300082c40d00c628580803080c041c243d4810b500140f01644038800580d51401611101c0e0401c1c50300c03483d202081d40030300030800c0913000c022081d0b004a060745004c1c1310345482034401ea42c90f48801d000310038044201c00c004001249212400a801c244080e0000985001c1a0340304001e907440342d0445035695000041c10401c210092264044041548a00e00d04140c00307599008000c5c1030840111703115250342d0000c2103007084140d241e030368540c202c103048031042c031298603190b40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486754397 1250 486753147 486753187
    0x90d21050403140c0f0d0501180f03030e12031f050a060f0906080412080402120d020d0f020a0506011406040803030a06030218070f030e0c12150115020c0105070f08 72
    0x2403041e02e24140f036401040e00055206000da00108030340301d0103201d00c05001c800d204055069881e507480f2105200c0c1414078a1483d5045030042c94019220100c608002e01a101418107035280d942c0180707124801d443e0f21034142c035003141401c8039401d1581101d4043d4200d040b05600190391101c3d440c98002411500b018280d00081b03490384800d440f00e5035a01701580c0032041182e010340501030300c2c00c40d00300d100c0c882ea076001da11910007004011441414a2031a01c0c10203080c18200250380244808480d06030021080058003603203100420700340001d030351000d072913083c1807203003a520400c0050100c490f43e4034102030b5006003401804994070b03850400f8007240906039500c0140d0041c003440100d02603940000829030300c01c20040e140d00c0001c1e41008003c400421303030039100302d2031401000b080c02c4180da150a03280701c0d9602002d000340314101117040c000740441d606034003804010000501024034036401003030028141409007080c54480380d01d400e10040300148520700411a0f54009001c0f0300030048218a98 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486755647 1250 486754397 486754403
    0x203100e24011419031103041a0108010b0d06050903072901060c0209040f030909060e09100507170601170a050411040606091e0b07030804060f0c05090d21050403 71
    0x4040089500015104442a02c40807566030303c0c1046420f48141c82d5011204003510b0030f01d4000350a1002c4020040241c000740c80450f0601d051424024120104031502c3e4090f03e4054020081c0b0040b050000d00350803460031004120035110000038083c4407041c0f05803642941c00907100180700340d1a4841e02c2d03c0514104a007400d56800c40c1c00801c49511a140c0106030075070180c100d01aa0303d83c0d44840741c64141814040b401c015007040302040d101103c1c008c00b0014114202c000d440c03030411016960038043d009000080141c43d04042280c040d601003401800c0c0e1070304100d03d80a0b5180d880040390707120a0a055a04070180b80e10038031000122580c011032149000d50080ba524101150400080d20040c0c0310741d00000d00c2040c01802088035139105034800742101000e00d003c0e03603540d801100d03158121007425004a0703411400c1105003c080d0007540c0171049000d00810210040c1000680140a04602c080c01040c2d880700c81d40802034040613408000c0c4400075a50b40507511008010620303400341c00b0131 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486756897 1250 486755647 486755701
    0x8040305190302071a0d0209041e02090301050a0509120304080f0a0905030d09030c05040c111519022106010203130305063103180306050a0f0e1b01030203100e 70
    0x200340801c00d0170b40514244020000c0d140445044651019400801c802540641c3d03072a03958041c2d10304050155140c18400c41c0c050703211885a001c241c00c44000070503140313069003030000b00070592001040404000c0c40c4a404d40d41c980d26507040199081c000d1250b0300751040390001e070200c0a6078008500c0340488004038100c0d045240052403c80710034509100080c101e160204081c0041d2030660001d4005408500d084038113089041245450410181e03204000401040c00f8070811034540d840390120380d101c1d901700b9480c0c088050349003500c00345244d00e101a100c2e40640800c1e0540c0c428012a1203200d16081c60000300d0381c80f8180309441d2032048d207011013281d0350321402c0c011100340c000d104e8103c3c8400303080f5172640d4041504c00396502c03420301203071085601c240080440041e8140c441c4034060b11200784001a03840508080c04100c4400fa200f81c0c4080d44100391323f440c0301c0c0c440c0d600ca402c3c1c0d000078a0090786a40725090041004a0a40c00105560050108101c0021911981113109242e41520 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486758147 1250 486756897 486756899
    0xc0306080109020a0b03220f1709030c040c0221090907050a080a0203220c050907020d0914150c0106090605010908030a0309020f180412170a23010801020901030c050418090804030519030207 83
    0xc03040c09c6228079210f040d00754103d0b0a1985030341c50b003580005502103490041e6610840604c400c407505200240620504070408a4102c1c5682801c0078a2a031010040c00d10a00d08903600394041c05460004200a2101c1d40000001c0c0403c41c0078180b070f08000201407184040188185401c00d2100301c5805043e014442490004802910006405c0c02c100000c1c2c0b9811415414004c100045200014000b5000811030f0308000c1001c2c6104e0040c1100d07004c160000a10310304018000c0f00341d500d0303544220304110384000c3c14807030b80f1030100890301c1004103400c00007009807607440407034005000d0040701a0701014404021a0b49060800d00300d108034802c45000d43d580e40c0c1c81406940e040c00c1c7c540040c521644a400103160951690b012160b600c54400320608401001100070308191000d8100306050394022802d441c5558041c040e0700b9401c1140e00b411070030b060074001c00c05a002481c01c80c90701c4040d190003215060020345c0f0100c5020b10b401c034040e200c12506804c0e03c2d0305035464002003100188100f0340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486759397 1250 486758147 486758183
    0xd0606020f01111602060706092a06020d1202030a0906060b070201120513080304080c120c01290f130c08060319021f030b030601090c0306080109020a0b03220f 70
    0x46610070760300384c0129406808150240800c64022843c110760302ca0303071a545503011806106107030b0800b1008012002e10034140c40c240d01340d07280c03807540540290350105490442950f00300141c5030921a0391200107071640d03030ba4012000507007400305000e4425413a299010031202d42d50001024214001c4e00c9103150421007611400c21a0304c00c0703030100c0c0c046000b07090100010764400000c2d9001400f80c40305c942040c02e243c86140c1405040c1105201820f0001101308030000213000f620204040c483c810354242100000010504031420607803849040002c40e17104a42c0d990340499940103410003010416552903c0f07014108640c02c0c1d500754442e05c5038500c10041241840541c010459000e4507203072210485401003140140500b40c144185030700c622906880e07880c00c008050080020703201c041050300e09060050708440d1190000b404036410135841c480543c075a9000901202c4618103c5560b0b681c80303070449400c400018441507090120307540c16206100c4406004040140910179126000040c42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486760647 1250 486759397 486759431
    0xf1b0f08160b070f023c1903030807020109081231170d0c17060a050a0e0403020309060a09060e04050708041401060504020d09061b02061b0d0606020f01 67
    0x44507460b02c84200700044000100140300716039246201030020039850208070600098144001049112180304074178240c190380030407103400150320007591854a00944c1c0394100300e000d51140005070600020f0b10124203d20b10035400b00003100c3d0041000c40d140c10030300050800c4880151000c50001843c2c0c0c4603250400406140000c00707402c003000f01d843c4281282c0e52140102c41648041a08402c01d0008000c003507054010f8843c4440581e980d20b041411035180e00003440806059540214a045010b106c81d859100c0c45109403041402d103a1150b0b51070f440c08914605c84c50f40f50030303001080410404a500d42220b42e1809030780094483c3c0e06050183d01c2400300719007003100c600000561010108000c504460b600f8464100f00c100081601a00c1d840810240c1e0300c81100001900e944d03488080c01d000840c86207030140b040d00e1003051030b038000c0717000c1c002e5850a001d003183c00f951401c5010300e803501b00001d048a004200c80c1030103100142d80ca40c0301070345688420b0004e072155400c000103400160315807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486761897 1250 486760647 486760649
    0x90606010201060f120609080a02011e020c070b03100f03080712020c060a031808030c12090d0206041e0219080c090105130c200303061212070f1b0f0816 67
    0xb11411081c03132890140b481800000402081d03030340c1655110800c0100e060400284003206040d000411990000da081494070643c401c4045602c901c10312070002c180c5004500d03802141c1c02903051a0300c0303403200c0300602c00074085039029405000400e50008100303e260340152407941e01035840041c80a000500585c0c44040a01070241d2041c01044401c55244c0603a00854141485940b892100d45440d40d51449a610580d080013140102142890380c54030300c9468958020070003009040c84115070710000c0d55544016000a00000580020400100d60018192641600104405030804011502241410250045a4041c000d070004010300d810102d00342d5040365030103010260306c000303020301a130300414881d60078004104641c01071001032131051201e0800307280300101071542da003803a9080100150002025031103e800040030740c1203c460300b209030303842e940d00401241d5030807070300c1d01d451140c40504052848800b4044c5a011840302001d540c25001e5601c1d00341103441082804111040501003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486763147 1250 486761897 486761909
    0x1c14030a02150f0f0402060a180603050114010c05060a050c0d02030a020306010914090c0a02070b0d02130503060c03010b07060e011a0a06050f180109081f05070309020306060904051603030809060601020106 90
    0x2413501013001810502d000704a000484d160000907008203001c030350748130b4145603c0500001d40b140c006100d505c802e00a00703851720301c00f42080c56501d0f50680d2102d89410000b0800c8801c0380e07031000007522004c211402c4074507000f8401800c65a80c5400e0140100039041076809600241c00084041401e04446002c40a0f900c3d00500640031941c070f5003801c05180c0d020141e4035086009502e00000c100d07610360080d050303030715240e0b03405030326220a04100c0240b45040c0d44801e2181e8844400c0c41a048402d2003200c2c10b458141d0003032603513000c9500b0010702510b000d50740c2d0031056280000114001240040704086284100c49030b11403503907100012181da00030110314805040c420401c104e41078480e0a05a03a00c1e00043c14504203035655003120f5070402a0800300c400490748007a00c6074034a25528410136a100841c1c0c281040403e000d90040381c0c0d80c2c00000c0286009016050201d03080c040108503004803c080c012030054407640b2864020103c0c0000d94107161035100b08400307c1c1b66980180148015284 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486764397 1250 486763147 486763171
    0xf04060609051306050c040906030f1514040f170a03090c0e070203090f0a05030a0807060c08010f03020d0201141b06061e0904260901020c040b1c14030a02150f 70
    0x3003501e40700c0045c04040c210500c10041000001181c4202d8000c0000950082c282c2000d400c940d070800180780305130741511080d0245000b0641010500180100d60055040514a4106881031814511900402c800b0581c0b40a0106003482000d81c1504411401d034424092010341550b06c41c01c264401a0a581040168006000e4004c0030306114040d0501d030b01c001403189042540d200007082c02c110060000b6194031200258440511400303015181c0c40d0041480c0580382c942c500315074024000d0300c40c00b000b482444000007207000c2d68881d070711120040c0070881c1113070754131000a1100703120b1030529007203210a8001c0000040252071f2103032243d05095030154030042d00c822a42c081100c5118020130032110740f401480804400042003502051000a40541036654111180060310b00713038005221502c0745003010f11080c42c0b604c0344400601c0c142d80e503042c1d0400151300e40c50b02d1b04d8075180031100c1c004a840081541104030780d0018658034001445903030058280c440030701440c0c0c1454100e41003602d440b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486765647 1250 486764397 486764431
    0x421030e010507110a083004050409060f050705041a031b03100317071a06030a03080703020d0e01050a1821170711060901060e061c05060f0406060905 66
    0x54060b40040010b0391007103000d8006030f81554000f8249004942051300a98400310100400802e40c203a1641180c3d054284071070045580c80b01001c0b030384101c0c001d6502850b200c00d032030b10070003a66410040640200c40c1d030500035850070000080240d0020b00c144580204801400300c401320b184402c40703002ea43d011504039840700e4030700d0b0900c1c601e07400078084040020401000102003a60050700c84e07210820755441503920031041c204042c01c42c5190b0070640500c00c60740c080c041199000584030a04e40d0785414501c1c02c941d14484254000e020b49011039032040e040c034401d500c9000065009c4d80c42185040420000080301e42c0c80b1007001c0a00303404c0246807244402010721070340c2c0d800540c1a1070324828a00200034800c005c0404240d1310064446001050140c0e00000035004244070721640728880000030481c0c6031605a12a517224000707400d142c09400000c1102e0107020075a503041040e50303080411540c071414070319900d000e0b41e0f0045074155042442c0c02c0000c220640c10703010f42c901403001d903d501c25000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486766897 1250 486765647 486765649
    0x190204050604090c020c0307060302040302042d15080d031b030c02120f090d0503031602030c0304050103050907090203160e15030f180f0a06050f060a1502070f09020421030e 76
    0x300b407090145010340c413492803c6e480940e02003000034080d00203503802588542c65441400306540c001c6000f40f000064401c20020790801c1d484d15001e170200f240c080403c88001030450212529050782240046e070117410300c201d1000b50503030030a02c061101201080f900c82c81d411400c03000c403a02d0346210801a000f03003080d03a000c0005035000c0d2281e0b001c0b07558500d20700a40f54000400c840440b00d822240c84d0008020022442d010031034600880f41540040c40c42c0c4184c11100c9902da12450282c00d05040c3c0e980c000c201c005900708040b1002c0c0007035507400c40d030380d091482c0c8600007440c0391003401d4002001080380c0b42c1e80b4284030707404800000803030070642d00750b80310400d840a03451300c0105076035413498007111506603842080089540071560f090142c40302003d581800820354000a200f112047c8000c400c0c49580c0c0c60f1307900a171003100c0c4107a14403100c40703140a90032400d20819502c0700e034041d01c40d1007010a6903e6554010000ca450441203610140040c444821400003420405400305540750410b40b02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486768147 1250 486766897 486766901
    0xb032d0109230c04090f050d0801030b010b0705030405060c0f0d2318030d110c04020f0a0f0c0506010f05010f0305191508071508090f0a021003140f19020405060409 72
    0xa8410348109458400900002084c1103c07018131003692500e030700310b0b0a4000c0c080244102010001c480c030707000040c1c0d0f0468598a070385510600c108000a10300250032001c0c440b0602c160b07409040d00801c6603964141c801e070902d958019103001b041d05e034041c0d9048844000d0041d420900d05030007141040c3e400841910810000d81c210460312103410f80c101c440c65405560501030044018a10340310140051500ea402c240740c19401069180a6841003181c2c116405000303064401c2000986450080301c001418212191034081c44014454440c540000c1410018202c0c9001503c000307988000042c468607d08800307840080d07500003442d0102c000e91003c9a0301607003010603a01020644880266030303490700e05c0d00d40b24460b401040c1c040011481015a07581c0036140380d4002168030b00400c0480d0341211120b46910441c0c5000344070303181c0c1c03c03120340d0414020342200d424400a400c000e551850000c0e0b0b0038100303600445034001c204907509841e01d82c40c0003910a0300e041e0b590280c00036040c54204682440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486769397 1250 486768147 486768203
    0x11221020a20030d020d030501060c03090b0d14010306021903112a161707240905090115020c0a060f08040c0e1311030a150f0b032d0109 60
    0x9160b100710030b86401c45031401c000101c2c2d0300c4625802002e0070310600f40014220380045e00640c0030010401c00700000b0a0313010018000b600e000f42c09140d03982012000740401040814100c1c04200d00c0b0741e0001080c4400799025111460b0040c009200149600000710b0490300c100f070100ca1074001c00d01500c03407400600c82007040074074540c902c40c86640d580d0412441c5030642e07000404000a400f46000d009020041c0d1a0360b03000108000142402420500b0407516040c0c646240945c0b018081c041d052224440e03050b040c020100613008440958444012008401d61105004050320030040c0481d400c0c100306c0d00c0403086130b0017a0354640380c44901c1402143c00560280c41070f10508940600030030501e2200c0d1105010700c8003441b11016521040c50b2030304001c132008040c079101380c0021601c0e0000c5900c152586c0490481c80c88002052012084150002c0112080880d00b40c420030140c1c21103000a440c007481c0f10186c440c48800c5684408400c14240c903200e8900070440d88004070021f08009251822907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486770647 1250 486769397 486769433
    0x50a0b0903010b190f120201141c0c0306060206100308040b07051006090e100c12180b010305010b0a08070b1206181e181b0303090306011221020a 64
    0x3c14890010070000396030048440c0d5400851401311010008044010340c1c40008021507000c400190200380c0010f03081c8601115a40300d011400500080380c0d030340f5821041d158486604081104c04003c103002001442140103420151042c000403840a000d100198000c0b240e1000c640c41c901414000b16120365080150201c40303030f100d00c0003460b81103009401104013070407002000042c248011b810f06440e001d5010700443d59540f400a0318200d1550003602c2410028092402042c2007840c41f0310031900c417442c2c24000c0c00b030351072080011013042810b4221480b8a20102c0700001a282c4441c495502c0e40543d200d03604d5040070402042040c1c0c0002e010140e0b002c803000305104282c200d40300200700300140c11101c1210b2581d411440544503134100f550190052903050090100d82d00343c0d403181e65907148002c54204540d1750481410380343c0d40c00300100c41d501d90b00502660000d503903905840d0340b19068014225044902c0c00348100c3c0755403411000c001c000010798004d00e025040c1e900c50b00c982d101003800700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486771897 1250 486770647 486770651
    0x60a050d02030c0316080f1609080d080f010603020c0307020f04020403050a140115232205010503010c020a02180603010f06150305181e07170d090e01050a0b090301 72
    0x411012600351014501c204501d2030220781c0c900e010b0004d000140c0c00450035206002a440c107021034819546a06680320800c010401c5a882c5c040c01c1c203481d240f41030340c402510b51003034141558031580c0c0500005d00460000504a240f030340c0703a8030300750305a0046d1401c01c44248c7c0305003c00009460302085204292101401c0103151a4a940391a418001105003d4429000c072503002400e0071001d1080000c100f521308801d14142e81003400c0166114840e112840000103c69048000380d42c07462040c00f50505c9034003c1c0400d241400c1c10b000c0184c40244a818401d500c0d00000d280c6075130000c00e82d0354005034020300c00032a4659400140f503031680082c00e016050740d070301c0c0c0301b002510046208020107408840f0b18440312503c0c81c1401820354900411130341b151062404203810003540040d20000c001c0d00c80081d0b12144155610342c40c9403051690102d200c481107050348150f180404034413046035600310758070724050689400005100a4081c400d00c0d030000d149020401c44000d82c0390280c8000d402c01400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486773147 1250 486771897 486771907
    0x3020910020c0625120809060705040f0605211e13030509130b04140604180302070b07030e09040b041406070f200a03260606030f041b03080706061202030c060a05 71
    0x8400c5841a141c05c840045a0101c0c2480085007080110310b038000781602d4800c0c5410706201c640c641c464603a01c54034060080101d01c450b8031680481101c450070a103420941c1c41c51418484041d500b03000c0e1411201103084040c04549111807807014510095010f072034461400400c1307024081700d001c05c5422500d4080d41c0c2c1d400ba1140d40c2e83c43c040ea60600460751941c0e0020f040c80700800044801c100d120344d07540003500b402400042d80100d6407008aa0400600e00d03101c5070b43d0f040035a82441c9142c419a440080c0508000c10441210001c6004a0107001d59140f03a80d8140e005554409080e01c0c000e0204510f4a00d09158911410040d891459985200d40c810317011305c5159032a040d0080822000b00c1d6900405200c1502e51341d051000c95140703011200350301d080c40000303e03419100140544a82c600840002410b0ac84400605500b0302030502910140c245e4078280f079103554201c414100d98a60030007000080b000f440d041c05101b0700350020003500c0750700400b80403c1a16409103181b4003d000c0c041c88 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486774397 1250 486773147 486773153
    0x3132303030108060115180e0c090d05060103050f031e03040609120f0f03110409050c040f0b032703092202160b010510120e15040303020910020c0625 66
    0x3025500074041c10000305940e50600d0060380d50414015200400c06c4640e1840040205000380c5000072501d081844455584a9075a09480c610600829a07081410b0f288600c0c1080000607085040368001d2342a00c40c3c240d51221125100c4c400e2401c40c1c040c624001c08110301c00d00900b0300031500315105500005640d055540c45034005190340e00381304046000c2c240c0c422003068000702442000380c031a1808210411029441d64194019406102c000903683e00001d20300e40c50450448020340044800340141c143d5900181442e5803046400c1c1802044060464080d4020304416805908000014600742503041080c0601c076650070310440441640c903c80c141e403c2c0a0303440208884090b00b0500303090100e2a0411950404041c1c2c000780c01030300791840d000e200540c04000040d19401a41c130124a000c2c0d81200e00d4503004440000201c901076503400d000804d07815a00510503902c0954401070f0108a0303940a036210407402c40c0b0107800c001e040004000c0e004156801105103a1103081d0120382d000c0c01d031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486775647 1250 486774397 486774403
    0x21030f070c0b130b0705040b18030313121707020109030f0302010603060c0905010216080d14090a17061006021b0d050607080f15060403030507050309041e0605010203031323 76
    0x780303030b00c1898043c03002d550050044050b40a40d1000e41e50405500c3c044c40c1120100356440789500c10700340c46001460341c1030355a805101319049201403490600c0041d4803000284c541c00000a0126400c1e82000c03244070044100c0c40c1680e0007190161550b6055034510788511981c1001040b049045550b2810003000040e59807284c2007201d01c003596000000e5041c07c0c0003902d0450aa01920990710940c9810232065900081f42c1005c02124544000903405403c00034680b400f03000d001e50f0f80812281d00c082240c4240c20140c1110f00a81000c954040d2650301000300040300a00503600141c01c0504104600003000040130003002c1e0140c5031090800c00f0307854042c00c1880039a00390340018912400c8c405041011003085804c65555040b00d03010540e440d000a0141c481c1c0d1100030144400032a404041c0a403d0059440455000c1e2050054002c040c1d4108030100760400441d4040b454040007007206c0d4800000d4900c00c070b450f20941c181048040d151010160f80c02d80302c07420080d10842c10703241162418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486776897 1250 486775647 486775651
    0x3050703020720030d0201050112240f02092805012f15070207120b1008190312020a08040f020a0314010e0c100206070f110106140321030f070c0b 64
    0x380d420f00700c0ca414450416040004503c001c50840e0706000c010b100881a82c1c0f50740e9015507102c001d040701c1544941c01004414165210f0707032215880c1802154400126400804201c60202d495030071164010342039a607607407401196186000100c004c240246d5010340e840c0c4203807001c4103684407403001a0010100c00d01c02501806007060700582040c00143d185a080c3c0e0390019101e0003d8880e4604100b1110300c1d9003000d8001404445130840401c200d840d40e41845406030000c2c2c82620001d1000c80302200200710392a008400054101c2d0f0300e10300c050360a00c240c1c0c84c013241c2550303111815200c40d00c03082d80e031448185060780e0002e66910000300049900402d04080360050f030011803210f80c41c8001d03500b4482c4100c0d8041c0501c0015004800960380451101c1d804041d60510540c0d1602c85d920480300410081c20090641d071800401244804800b0303410107540000b10202c0b8220f00c0d104280c40d209480900251203036203810300210304403690030349081e907010382c203803504803004c402a0b121001c50940c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486778147 1250 486776897 486776933
    0x40e0102040323030702010f12020904240b040f030809060c0105010e150a06080402040218060a03090b0c0a05070209090a17070b060102060402010f03151203020601060914060307030507030207 84
    0x2000000f1801410b041520781c001000d080203542000c1c01030300060002400d440560301085001c4000c2810f00c061070341a1050f040c0081e0003040f4614141c00c11b56240b4508454464000103510000078480c10048101e806542508022158041c9960b07248201a0001e5403241c2d80b006c000c0c0502070100b1002d106141c020003200042c0d4080b41040041101640282d0103198041c4c41080d805012882e000041243c1181d8146e500682d52089a107507000d510702e15280c2c250f8482030015440004952580294240900072201c0042039110f0a0b203d01d0745124030050280071410601203600507107403d10746281d00c00d640c0c00541e51046580d65900f14120b84e0020f909d401c42c0c00c045a0310702884106400180c0c0905c0c02e0004003000c2c01c1c42d40010380388404600581c000c15441c0c00d0200318098141001c07100920492840c903d4800e03842c80c002c0d48640b001d01480300011000c04001401e4640d9043c5481c0542016006620b103807280b03038040380036040040546003811b0b0200103200c005000e00e64901901b0390 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486779397 1250 486778147 486778163
    0x5070e160909090314030a0914010506043909151d09060a1703070609080702010e030616030c1116090b2b0204090812060306010b07051902040e01020403 67
    0x140d0140080c002034280d8000c8002c841c584194440000e4021508844450141d07214036100d41e00e80d01c0e008090716103200010100c1101100d81c1074a254150001030041004803001c4c4001505015180e1360803081003115204201d80e80d10301c0c100e000d55041c000300c10201d18070b0b002c040342d92038000000029401541c1c010000d10b50944003101740351041420010325000321000390007070031704400140d6054414018a804002090003d0208110400c21a400941e100c1824425443e19052599040d0040c4009a000ca40b8184058510340390103e20684030302058254241e001030270348000c800500c01820600c0901c03051003d10181800c0400c1107542e1140c00400082c81c1d181485403460681701d5000b80180104038000c64601c83c48e07503e40504400d401c404003610418800e900004005c0c1250b0540a044400f001569031404400030340c0603482a00103404440080e40e0f50001000d103480390803c040c000b5002030b42d80c8590050403019a192181c001040418030348064030105089034000da00c1192005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486780647 1250 486779397 486779431
    0x70b09010212070522120213240305070503120a050d0b0603041511041401030f021612080f0402100f090503070801020d0b030d080c070c03080a050403060f0b0307050d05070e 76
    0x42a15003c241d85c2d14188110038500d28203000d54822181e07a10000b44601e880c444026040b00d280d90180d004403c94600d61418046294180c1d075401e880750005580070300507900007040030f04002445400502d003130b80d4114944101c0c06402c80e0540c0003036100c020141e4a440c01d60b025907840b074024500039070240a1030320218000810240440b031010b0b0006550400038802000120031014500714824401e080110b1140c001100c944001d1040000c128010701006252400f4450aa01c640040c0c05040d11413140c1a10740100546168004450095000401c0c400381d04400748501d8009207011070300d0070003100c1642c0b81c20000e410f100003904603007856075011401e00f00110b1940110300031520160003030407244900c000014202180180000410340c1d000a42c4c0303080003c5c0c282414002c60f0402d14094440545c4140244140e02901c4143c4445082840e402005207080c46050f06205c0005c00600c81e0714585018083d5894103108103841a0248003000540c030442c0703061881c030940200c04d01d200d4403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486781897 1250 486780647 486780667
    0xe0106030b030d1707110102120c040519180209060d050a0c090f030506010905060607050d0c0605010506030f0f0c090a030f0b1b0a0c0f060c02060f0a090305070b090102120705 77
    0x200e65601c04940c02c00043d400780010040108000903009a0343d80f41c429043c11b142d00d0400c1c06072041000b585031031410401000307015042c01c0b01600647e0400c452030300d101400413412080f003250500400c503d0300448030862640410f142c0c0100481d02024003401c1c02d00d4406502c0d101140d504541c0900300c0c6494001850003150700c161561301801029074070f94402d500b103881d21540c4e110f05020b84001c01d5510000b1621681e00d0406072007031642d000c811a5102010302304000d101504c500381c12110141010300126107803910f002070341e1040c0060501001d8940e038025402c6440070018111542d4200100070400c41138440004c030303a024601940c0d00d1050908285040d2483c044001d20360482d8003242c0b0b02e05000c005800040b50251007203860000701251181c200030001c40203404000304210b1908016968098000c030b12684504140d4080394210ba42d0000c00c40c0550319411002800114100b1010300001c5203101c41513045540c0700e00040c10014840c12221300038600303441300c10214502142c0341d480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486783147 1250 486781897 486781903
    0x12010903110c220513050a08070506280b06091306230d060b060405102016060311040518160302120c03090a0c09020a0207050a0e19060e0106030b03 65
    0x1081c0c251403400c4031094044041c1c01c5492102101510b41e41c588011801070017980740c40c1c2600c01c2c0c1041c10307109070390098a0486101da110000c03c84540c0103100004040c0f103c0c0075149448402150420f80300b1440c00548400280440901c0704c1e031220f003d0000310200d84500c0906184001c02d44400a00541403080c0c11f41c1034011000d44880e4600382d84c003003002e19200d16903001c207516807296022074205c04003c000b0300680541d412031900030601741c219000030b0782d01503108580c070044002d41080300b154003520300788c40e11282000340b8007207030f040e4000300b204520a40c46101c015010980d002d04007515240000c11010b000309020b1841882c000601034201c600f801c0b600c0741c101c15818110704d009502201c0c10100c040041c1b5030030081c4c0c030100005001c0c4005001c44640203a1100e2090076480c0c1714000c0500a40182c240c00b40184529100401d960810041d0402a40c5156040c2d10450703444a5802402c80c46815401000a4650701c002403080d050b00c0c5000d010708290f0b10046000b51f420824185 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486784397 1250 486783147 486783163
    0xd0e040509011109131e0b0405150927030c0304030308151e031c0815090c090f0a080a050d1b03080103080901180308070201020607020d0503060f1201090311 69
    0xa0380d9240910380c00c2c00040803400c03100c0aa0007074400280c0500c00105d0040245054030035540d02058030036240641d0b901035803080600c1e1004683c2000f094544150901a12640100d400d82020300c40001c540505410013100c81c102201d84550441680051b5509046401000084034281c1c0041002c0c02010b420102e065402454140c0300d1541240c0100090b88140d1040c802c0003580c2140100003810340c0b014400d02c2180c0510b268802420850381c80d0040000c43e0440e01012015101d103a512041d16000690b035001d809039000c41800c08048100f00b0003031036031141c5015400b054074000090103000900000d080c0d240900302130603403218040303c00f5000e1100580b060380150210061030340000e400443c04c0381544d400402d899211328103000141c42c044101541c0c0c0c1d001e5400800004100a550001441d0b40d42c400e81c01c0d240e003034407601d0003a683d8140481d62180410380c280b0003e1084d0809a0030515141402400d00504006511803542111005001900001e009600418220310104040b070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486785647 1250 486784397 486784411
    0x3010b061b0c19031e0803101a09010507060e0f0d030b011e020307030807210b030d020a02100e0301021308010504020307081c050904021e1305040c080f180d0e0405 72
    0x1503c1c0c1110344040303110700006000c010600403c9020480503041d0900c0c00056035a400081c4a0352424880710040c0340840c1032154246e20100c00c405600168000e03400d440141d6010b0b12440e0600140d551040d000d040300241080840c4201c60b14900000b108000341c1301060f4a50300c0000f1b05400407000103241d4031002c0224030307000803c030b00040704039580003040320001a05868010b00a4444150403601c0c004010782c0c10106000604440f80c903621154042c034a400c104404a40c1c00d043d6821003a80c0f681e1400360080e40c4201018007100c002130282c0b41e60001150010b000502c0c00c09180000c00344824290000003090703658808010450a00f04030b0b100c081c3c1100002088000c0d07804e050360903d00a1208041c08008021800034465215034058500919900110031240711000011501d5a004a06404040004114001001c2c24107100d40138a034a416134549580f03580300040c0c0d80307400d9409403003000d030402c0010844090080c140000041a0901d590b03003240f54041100304420780b10007400c00c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486786897 1250 486785647 486785659
    0x110a0908030301050603010902090f030d09050a1403070b1806180907031109220906150b0301081911120f070b0f0a111c03090212011a090603010b061b0c 67
    0x41c0304d00c0d41c2d0030f0306482c1114001d500150f0b44d0000a004200d84888481030a50180303c0c0404001c1581c2e0460741c10001e845058038403803801555403000020384441d41001e40c0d09600b002d00140a01c1c2d0f5000f000f0300f01d0b2581c0300390803c42ea611240220362254030001e0448010882c8180386001490300e0b40c0041d42010b101c1c5000e1004582403d44204903100c1c0c2003001d44501c1c582407501e0542e004166880004540344c0c1001c0046a01a0610f64040c0c040c15410780c0d00101584004034840481200307903030517580c83e803008024101c0f0062103203a10030001c84080d41c200000741e408031955a2201c014003044101280500103042401d80032520304001c64212403c21202440102c0c00d1807101001e403034024650f441c0902d903840003100c03580d0030650541d4034404410b82e0160b049018a030160003041d86640b0984440c58108503d28a01d400c03103451119010540b160082111400c1ca404c004160b044407004000040510b03414000480c65400803142c010280c1c00903001030300c0090280007405c1c558000342c860f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486788147 1250 486786897 486786899
    0x801051605071208060d14060f13150510030b09010e0c040c021c030e0d0203130e070f0e12070303020f0d031103040b07030216030e030f01020a0c0807020f0301110a0908030301 77
    0xe00d100c603040c0c540a0380c042152031400105c860b0303039607030404109036080130b0070240010b1407000f00e54640004441d0401049582c40201d03052202100400d1110b5030000d2440f40410b866459440181c000640317081c0c1146260000800031642e160112405410581d0001401203900a592800c0424100d0b1a070b11071803421a1a01c44c040e0045411840780805440030008101c0280007038000b0001440c41e03000324422424101e0360180c0000003000001c5844000c0c040e49940c404c00b48451481c1150320700c0000d1951414182024010a80001c1526000f0003070082c5900340c45400b0b00c1e00d94164010381c01039020030050b100294050210b205020110700d0140030501d19090282030303030322026000400c09001080010302d1548a941550311503510b21508200300c1c0140c1c00d0041907001c0394001d40e8428003603072090b208058014400c4403000328094850200b0b00510791030741041c58100140a903001910400c0b03a18240d5000c0c40360707020325080c0e41c800c1600d48140000c010052205900031080507402080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486789397 1250 486788147 486788153
    0x120a0b0d02090a021201120c0519090c1e090e090c15070303270318180b03070e01030303051602060f190e0a0b1f0f05010807090f080105160507 63
    0x40503080140c0580d56003549888146109000f8824400b018010705601000412040c9100300c004201c203000c0e01481040945031410040b00e44500400320500c520000010001d00025411098026095081581c61245800b03209a690640c4840030b0002a130800c1050091114655407250001c0e0f0f240014480c0c8415900440c0820b0b50203c410307441c0881c041b8031401014402d4200c520008148880d50351251394900900485081220003180410721a8590341c00c0c500c9e080401b4070842d0201602c0c01d2400c40040784c1c101c028244010141d4050003500c1002c500a0404ca450f280298480d0381d000171503140441d035650a0350591202c20382150010001e118840081010741904035203c1c2c0c41030240c2c40c0c0c0130521070b00145410074048890340907410710f1005003d00f81318494851058070311b0000480c1400860f107030302c00d0410300480c04d01d140808004e00055101e00081c0340d1044603818000030254076804207500909165101c080980c3d1540c0070440181c10802100300c06003954200b41d810325503541d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486790647 1250 486789397 486789409
    0x51006080120280e0103050a020a0206150406030b25021b190302040504110901080f1234020f060304080d1a04022101080c2b0204020f120a0b 62
    0x91100c2c6085001180b034881e8001c0703490601d19488294060102c1c81050340001510102c0d52400705070200345044001038004400340201ca0082c030740c6a000d440c1f150384094012075140d00303d040c0356410070b0b50760f0008800600403440c403c0c0180300c8508030b0310f220207480c540780f464042c80c00071039400c641200c50b1104e010018444004042c40301161812148150800d03440c000300f0f241d51002c0e600c0341c2000103010503c001110145043c0c1c80030746031200943e894401c6070795201410b1581400561004070f12590080e1440e025021fa90708003080c440095803504062007940d19454000454240d82c950100214a041c1002050901c0252502c1d815850203464880c007038014600b180c038409803a11420030726018040e0b81d0000d1004001c1c011515044041c140200c0c450002140b400d44441440020030280000944140843d0f401005d0b050f203030714168034114a00c0075000078511414086401c5d8001a92103002030800e0004040090352103001c42e01d140200300e072001c0c1201591500d040004510381c0c56030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486791897 1250 486790647 486790691
    0x40b0c070b0c0a032009040b03060c070605090f010908032a0919030c060c0506060303121f0b041d06010305071d03070b0d09150b0a03060b010c020d0510060801 70
    0xc00e81c06600c0b543c0d0400c080d40902076020004061130042000380301c845403400041c00e400b40e402e94003007001e880d1480c14036940e54400d0b030380c01c20034080a00c141c07000107210341c1059500a40400503580100301d0440110b09542c4038040456640700301104200b981040038807540d9201d60050071201402c07000210480c5244541200180586400c2d10851020360301014000d00459200b419038401503690013004082902907501220f9070300815012034114503000056903144072220005604607103502466508549102c0001461031460620029056001c100900000e1a00361000142101c840c108048c0300b903001004141454a0002440b801c1c5500003013014000350000c004d00c1252070130310002481c00b082075004c1811101c0008000000712026006107201c1032080d19129111800700e449801174580b600c0115410400384441080401d0184e00989403294040c180322020f803e071600414504410500140d41d10f520188800b890103450348140001081154002c12001c0701c002c0201d4904500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486793147 1250 486791897 486791911
    0x30b01030f060207170a0f020303090309010e210c10080f0703020d11160209061c0f030512070306050a06050c030418020c031603030b0a080d0f0e06040806040b0c070b 73
    0x15800d0800400c0381c194129800690417040c00b03c100705014105060642c050221000011403100307000000c7c900000680340110802d60180d8240010b00d4011170707a00d0b60f080c401992103403051400c4441e8442482140b40b4040109001d04a000c20f504240300d0910210701400081100c1c50701003043d102c40b1011401e401c10030f68030740544c0da013142c2d14420010f4281c0b80e0410394580700c0020038001c0d00d0000c0c04402c040750320a85050040740c0c1d0310010012030300301c14503484500d002c0407098200002d1841141c001a284641002c9041c1405039904401d03d2004540e44808030359075230000d1000d031801e40701e0200200298608180b27040048000540c69005510420302c20000c60b13034100d084ca11702d80d01920581506082140d8882c4c0581140951031010040b0550200303150009042c41820044500000e83d01d52000408040c0552001100c441c080da4900408000210014a03010780d5610000c000800481e4000c01c0a0305280c140303415001c802400d040584441081141c0010b4243d40a265001d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486794397 1250 486793147 486793163
    0x90f060d0308072c090705040e13020a030803040b0906090d12050411030f03070606050904080406080702011d0f0f060f0708180a211818090206040603051b04030b0103 73
    0xea0f20720036102d6034080045500c52400c0281521013206032481c03c9a1884001c440034045520390360400c4d40e6521480c0603000d8841d500301e0009541034480180c80004d41d1025191004060f920344405040da081500c2c03c94030b2aa50a003400025a400c00c130503034200c0d410388050b15900240c100090003407040b20b01c1660b140d40d00c40c80061305020200ac1c66400d80d14019041c0c442c0b6401501155031280e2003a80100d410f20300e00f11f070100e418203013400214401d5500c50b414600d4107080c40d40c00e80340c480740105107034119901e1307202c807440c1001040141c0d03160501e80300c02030030072241c1e91a0707050500b011100404020340c001c01c1001428001c81d20b805070070414a040109207500ea03800c607841b420440c0705e52040d442c1705102ea1082000209801825051b5814420160180c510311027120303d28001c504410344a201ca04050010320983e1040010a101d007060000d641300d0380fa400700d40c141e04954032081c003290f40e820400c42c040c0c14010400061300d803100c0320146070070b00310303681d4407060300041c000034002c0c1d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486795647 1250 486794397 486794401
    0x108040314270907020c1c0614041b0302101229040b032803020a12050318150109020c0102160b0603010c212c010b030715020717011503080306090f060d0308 69
    0x11f0b0106242040560040c07820300003c0c06000c1c0b451031915003070700c0c01c43e40b03516401c43c14102c00c4442994042038a600818041d40c21096001c2150305001e40704000405990340d104411179500403100300c40c40d04c005440c180b90030b548100100001c80340a0101140648c1003210f484402001c0e0800b019440424038240c466007440f039080c124549030382c8060040c049401c00500d2054a0f401c040610310611500060aa24404200541d42c840c20542015500c0c2e00c200001407002d00210380280220302e2a03000014200000c82030000c141010201d800e44a00074580184070341400d084c01181d81c0c0e8030080c00c21070003692000781c110410000040c6040e45136617403a032100a1000a4040c11340440700d001c408074401641034282c0a009003a0b41e08050320074071499000003100e10700109200c264418030380181c004581380a0200d03004c6030244058180c2d135566281d41100103c503e1400074091401000042d482e8070f81042484010000682050303082e10f410000c020681e510360510040c1c5a81c50b00d0100066 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486796897 1250 486795647 486795679
    0xf060c070c030206040603050f1015030f1b08010905010504052a041a0d0506030d020d030e0a140d030e030702090103021e0303160624050108040314270907020c 70
    0x1c030050390802075200400150000e078030707a859046540900e54103004080140c6400a5044400042d441400c0703001c003484501c0300116010394000303500c007105040041846070b40c0b020a0503008075180b04250114040e10010f102002e558822240540400e1350b081002c2e0404c505854130802324182048034148425a00fa80440000c400b40c900030511000c0440d01c030700c400c02c3c0114446e0091850a1461440c25000a100b46070014016800d219550050449001040070840140c00c805542d0f4081d44600d501100001e410b5808507000116418081c0c0021124403100034182c0d02180d045100d00e40c404c0c00b002000d41d850512141c11680d0488008003001c00c880c001d941c46452900009516000218500301150009100e001005104030000c1103207586591072800d810400d4071031881c0f05154034000780701550084a1081d00301c1e009041c0b0740403100100002010301e6204a15056440400b0340c2541a4081e0071000c00e40041c1040311400b10034540028001d647c0e0843ca00610310800c4280d50700c1501c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486798147 1250 486796897 486796913
    0x50904060609050c19030c08010b09010c051b180601080c090d050d08071803050c040915050108070f170d08070c0501020f070b092e0e0a05070608090f060c07 69
    0x82c624414288000d00e42035040d50103d4000f5200e00807242181002c01d24018840e118001c000459a19101c02c02e90038114000366980141804505200a00c3d0030000807070f00403c8000d0000072aa4406461140741c030f000d019080c4000f03910715808605400034820781c2d0703811581c69980501004d1540d51203800b41400103110307204c00c1c14040d000d800358084400159500c03c004621036001034847c1901c1110f45803002c3d842009510000d84182c0114207035281c2460560407000405000d0380c0c885110700f8044402c0e200310743c0207a10032085035101120801240c0c260315000e90040101d00f031364002c01070b01c0807c10380d00c2d40e004054020410400c00000f68019000750400800382c2c0d0000000c54443d0480c10b12809503902401c000d40e201c40081c00045c10760000000c046078501901c00c0b420b0100541035004480c0b4900a10100380c00d9a203503005440d002104202085005010b103000304012072915a0103800040d01900b4003c1c140c000908108d040440011042d0304280032418142d500c000d58104144 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486799397 1250 486798147 486798149
    0x100b0406050d0c09270e071a0c030f1801080a05192706020301050f030d050f070c03021c1112070b0702060f040f03060c03090b01030308180102191112040509040606 72
    0x20f000150111703c050303903001c205000ca111606000104442c0c1c502c05a100d40e1085d9601c682d08005000d01d040042c500035200c050b000c0c441c51003003100d040c0101d41e10740c0e0003a60001c0700c0482c482048200341140da5a44440e01642143c0718503000c00c8641003c0103940030740c01e0103000c80e1300c0040d21009030540044600e0022010440b9810500300c09443d24500360000e5482031042c54850740325a0400e140030b107004582800705400c540c5035140342081990548169070084002a101c2d5440d5100000144e21444009034110211094100f044080c51401880c0300078500c04050082d40e81003800ca07c5c01c0400903907c0107407a03080720703000e449480f24400111280b14070b003144c05e200c50000c24006101030031a8100f200740c034410103007030000846128003181211034801c0080c262140300001017002c02d00444059401194a40000500940c425066802e9a1003400e00c110b0180d2441c00d002c3c03510f0762212200700241494409810405829650350081d8062409500c0c80340340100c001c1820860b45a002e08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486800647 1250 486799397 486799409
    0x601090306020c03070201030b0907082703450f0d1509050d050712030c050c1c180f03030302091c1203110c070303030f0b090c03100b0406050d0c09 65
    0x256640203509003484d12130f0410681240401d007000340b1104d0a00d1f040085c80d2040101d41c4d00c4100315a00c9191074044420406281740312440d5025800c1044042030004181043d11800c5c02c0c10508250503075014405050780d200d400d80c3e05d488421803c842c440c03c0000c060700c2c0003200c2a10010b070044001403064001ca441c000c00007414045080b26510003900600310b414050400d48130380c200008001c0c0c07094403d0703240050400106d030040008190299110460540c040d203445410303c01c1005a45203400610101403410038140d0000e505041d42c8585603207441c0100305415580c0b103140480c2040e04951500000381415008140c040a60719013001d410700c2c0b52000090b0003000302850414000c1206d141e48040b0000c0c0c2800081007001155104840883c00c45400804c00d031441c40d101100100700d0000524030481d21642d101407a540c17480c1040d40035000b22404c0b20355904003865176805020340b5074012100c1038818001004110340201c140d9441d283d480c2c2000c10380c0e8440e403038111640f41498020b6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486801897 1250 486800647 486800651
    0x3010f05090a0b1e010905180a050106080d0908060a021612030212070c0209060f0111010c0302091309021810050d0b06011d03190606050901080f060703091a0601090306 74
    0x30050241c002041880b0358081d940c40080c540b55504107400501d94034011600030a11040100210065540003a0b07100280444507942e80c0c601602003800d202071840c059600c0da450711020312086d6401d0100b08480c003114182034500d02c2c5844411612100d0003018070003a564003040f01d4044800c044455140c06a001c1410000d07031040e060040c2c020f4000c11000b48091084100043d0214060030040c06003540040c5481ca5540d180020480300c941c020111604019811300080b0005409010303981030300006880158035940050f080c4255401c50215482e80c2c5801c149a25000d070301e0711600c0ba5a40c0b018102c1030505a0b03560b60f00d0031002a80750340a00d03003094040c004002440f110380070f00c034010301090340d400505d10b201491003525140710903c140d03455000405a14500458408440c11007072160b000803409aa8030300000c0c0032441300b40e110200bea00308165070a207800e01440210f50110b820704081104026603280c0c2c03010f2215102c180c0018403074600c04101d41340e0080a190000b0340e4000c4003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486803147 1250 486801897 486801901
    0xb210c0c0a0b091014100909152a0c030806030601030b0c0304081216030b09010506030a090507080a0b0601140c0304051c022e0804020d1b0308160308150a0603050603010f05 76
    0x45030390b010106c40003403d0160020010403528004d008510301c46400c00e0600b104000d003201c0d0400109026041c843c5140c1c5103452035219800d01c84500703000c070f101c551207101a43e4107506000c2e0040c200142854825040300c80144000343d004420307550458030341e101c0180c403030348e440c608141a8400d148004000000c84800c11800741d914107917482c001c50301a5414800c1284040a12000c0c62080c003900d588441c0c14000207005002030f0f403080803418001d00840b649c0c0c41e41c90300124101485031700150340e50a141c1c4108096035130000900130000c058040c04624055902c1c28480c2c880c081c5029482c0b0a035984a161a45804d5420f0180343c0290028484c0800840c0d00e11904c01500c100706850382e20480000714014480e00400c078a610541d0003602141481d169507032104c402c80a414800724900e482e0103000303c0071a081d42e02602e12401d540403c52030710f42c0c0b141030283c88580c000300049074041008020382e549072540e14103d021aa80c5080108464540d540028090508420307482e01030740c58141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486804397 1250 486803147 486803171
    0x604080d0e0a0f030e18130b0c1326010203070306030507140d02040b030f1903020c0a080c131118040c03050f010e070302040b210c0c0a0b0910 63
    0x2401085800c003800c2041000401c0710603250100d04401030403c0707103014040008240180b441005408005001c2105200301c80d8914075044415559000580d1543c3c0c00041080f4248914540000041c088142419000e0218400c070006500800301d2034101e90442007040150f442e01500c0e00b82407035009549a1078861002801050f0074402524140f1884400040080c032820034950410388c0544150b00c070714016003d2001802030140b189425111314241440118810302800a010580e00b410890700d0301c0d682002460418690500d620802250501f000501d20008504800e02d0003a9910705c41903251100300001002c1a0302c440a400100140c80c260008000c644c48000400441d0200301e0441000305c200c4c1200c01c111045081a103031480140021190314605540c0451365240c003514090b1141c82110540c1c000b5004200703002c00596940c41c02007045002e240d032005110354402d0424034ad480744030742d4828180c0c00c00b03044400039a0118400d58818001424a12001030080c031041c000d2034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486805647 1250 486804397 486804413
    0x1c030c0501020d0c1d040e0309012a0c030c0807120f021810090615050405011805060a26090d05090103060f150215040302150c160b0133080403020a050604 68
    0x217909a4a10000b40c030300607103403800348518040350102000035400c00b1400001990341c50b0452a90240045014070307155030034045000b01035242849080b043d03030010314602c1c02c6120340000d6000000f081c0c01c880c8091000f100c0e0703442c3c0c00035010340010072601042c28a0010034007007410020181040202c2008001001c07620b020344008071400980100310b200e03580c80d0300810b102d05d488242c00c0024804c0004000541c0b04200d0080c041c014115980c441581d282c0c006200c603882040b650740403818104454840344c0088950500c1c1c0d0b0210340d07038020030f860700c9055140c0741c43c2820701c05014403102081c015010703486603000101601e01400320300d00c12611520f1946800c090b9942c18070040c401e0b0450b24040c5c190000c805402258142c004000000924800d440900d50081444850720380c24003085209041e6800b0010300d80e809145d40c8039055050110103e80c500031040c402d24000c2400c440f0b0b08181c02030800303013141c030b01c41d9180114032a1940c1c134080f0f05102c80300c07501070070a20941c028001440180313 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486806897 1250 486805647 486805667
    0xa11071710090203060403050f1306030b0103180302100213080709020c0c0316060c141605090a0c2001240e0601112d0a03050d05061c030c0501020d0c 66
    0x244200e484640411881c50706544041c10025056003260f40803400090081011303000c03411403256041d01f07010b134102c034242c409030300e030307800b600c002074070f0702e400500c25600b511030301ea0310b003600c84007903a1485400d850195482c100f00d03c604e0300060380041c20501035107080800d803000c1c02c0c40310f095842450340c0b16800d10282d040f030081c0786100c0c010740014520900d80015082032103800c10005054451421000361210030b00058240c552a4460703c080c2c0d44000180b00d19044200d240e40400701090911081c05110326000b025085118078000c1c940b400590042d0000031100a4810b00400c28040c0d100345030b000d44090040c0b503401ca00c0b41d05030f40d034001102031140e5080e544c040c112004655586001126008008a1030f85055003080f459003203018440c1507a00d04003c246186a6501c102d100c03000c0345800703075190301074001410209064500403564090107811990450b078404841d0340350b10391040d2081e03a01400406010342a060701007000f00a406484d944c10350036404011458a81038003411341c00403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486808147 1250 486806897 486806939
    0x50307030c091802090708070e21010c0503190b030102070203060c1c0c0c02010f1106090d020c09060604120510050c090102060a0522141006060f030b1003020a1107 72
    0xc128000c1c803c0b8840915204030075400400884003521021383c1513078aa130740500307504204a13154444102c41d48442401b0110340b00c454425254500c061213129003107540301ca0000080003010014800f4135103803410002500c0508481c0021444041c00c002130080c85180d600a400d4068101088800090a800f44c450501019504054042c0d22440321088072098140d01011810013410300300554410030390302e0400300340741c20100100c80c60543c4641c0b51040031588036003140c0c40f50410014056051107042211582910101c4003401d068001480c41e000d01d0103400340400c00103c0d100240107040000d402c3c0588584001c000c2070400c841580000e602c80344510740907106440c0801e181d9802c500ca00b41c8250007048900782e05c500c0c9105240d0300841c80000907249a81b290380d403038036448814041a1202d402031800040c075641340110103441101e00d8041034040c54940b0b03a8206882d02c07030700f50b445034043c4071303160060365403007222030a40c0c0004d0704450203100ca11988001044000601c03040f5100011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486809397 1250 486808147 486808151
    0x1216051b15070804060c08090a03080d060801090c05060c120c01021908190f110d0f0c2102090418030f020601090e0c0d02030f0a06230403021507030204050307030c09 73
    0x40000080d079618820408001c045a000300301c01c002e41485000f07454002071090404a2800681800180005030190010380d141d100001d1511280119480380c4002000002d00a018440c0c01e030b00c8900e80494a441b80d14000c560029507400415024054202542c41000e141c68941c0707040d50040e0300130340105040f0b510847c424104982c0050040416a2188030040004104040c61130002070250114400480c00144c640801e80842420741010b0402ca10200c00002480c01c2c80c0c000300d00560380314003458400c2c8502a10701200c29079800ca2503081100e03030f040c8090796070440e41022400600408203894100c01a145403042055440180c41c0d040c00302a901716689662514149070459500070031417412980001601c80190500450520388640000c080c0c070000c4041601710b500303014081d28111146660b425103441003801c0310714000320405211000c2102c504d496500a0340d90f405e05075403410012884800211168401c0c0c0440e0054140a4141e400041e5a842d080840c04850b00440c00c00e98 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486810647 1250 486809397 486809419
    0x110306010f05031009060e0a0303050a060b0f0a0f0c080a03020304060c0e030309010e04180b04051903080f18101401120f021c081201030302100c021216051b 69
    0x400600740e048181c1c0c1c1c000380684034000019001c10005c011191044a9032500e60700034a550300c000b80541e83e641800780c5c43c0800d181c41d00c1c22003c0100c0d03000390022842c43c5414010f0b0b9045040d83c40c1520b6031901c3c2c0d42007080001041840680300d00a0000000740001e10004480d0700140c2d05030041c0d40541c0c0304050603c0904401c00003624945c4d10491a0340d0140d1081c4024081e56224030350400704d5850150001070b5000c0311000a03078285c0c154520503039100300c48030141320403c01c040202da135640c1d0440042a001018a581c01810120042c0a030844030351408045808424080f0f4004400e03581e8004035600e0020164250010740b41c1e0240c00091801d400707000046249450092400721a841401c0220144996003040126007500307521000442008890000240300c0c10000e10a000c1d002030880115895450000d1401c1c10403080e00d80ea007418010707810007640d00050401c0342005c10416540d1200904240510303113200509000d0051300c04c81d0038503420040e03440c521041903401520800561 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486811897 1250 486810647 486810659
    0x3030927020a112523030a30081b040e04050109030906090e13110907091e120602030c0c0a0c05090a0e0c060d0e01140702120a0206060d020109090504060506040506040e030f03040206120411030601 86
    0x503020b0002c403000310340c2049c0000d469034000c0743c0c01e0400b01d942e034003c1c81c203250b2504400b02140c071003107804a600c0d0707548203003040078142c01c541100d00400f401e2034602011410075260280031500075046103030203814040d0040030840c0b41a0002d0814002401e92030491425103001428404503106544894400500c10040c00c8180f00c10501a038800e801410001d44565882174029400103002c5044800305200c0f0f0454040305002c182420307401455640841410300003008012400608000c0280d8900039902c82144c0021403000100701d8102d07203c40c0c0310101c800180340945810008032040354a04851800c0c00d001760034142d0b01496a903030031a1070304807080c141803800d4445e85003010056840440090035a10341008445011031041c581282420b950340080d9058031401c3c1c0e0204c80c01d51700c8000f007042500b854442c1a81c4203504071406c1c0041800550046e1301c80c41010f0707001804503c0040000c042d0b480c2d4604039896030030300c0c234071545461400341001320301688184d00c1c00d442409801c00000d02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486813147 1250 486811897 486811973
    0x3150117030a0503040b040507120804180204050d0b0402040b0613030c050f0d0b190204030302012f0a0c020a0b130e07030603030927020a112523030a 66
    0x944001d0322028a1901c85d910303a0301e4106030081086034580b107040300100750301c411944080038281c4034880d02e94465050443d60551042d201842d20181e07031051104100c00d40c1c60b010314818140d000b00c4a1501602d80f400420060700c007000c005c0d03410100c0061007080c2940c11070344000449004165000c20790380c4840400080d81100d01040c2e80c00490540e2180100c6d1030b4415a64000c0700006600300208495110304090f170f0010b034001e8001d82d6550b208200500c0c0c04001e103201d92102004914800c440d8100301e02c0050040140100400840c07080344c00454442c4104034014110540380b1a4949a82e51951050983c05000700082d424450b004200324501a005000541f0352540b210261942814980004803050b08240328044c026003501800642441c0f0007001c4000341d40d65a481805a0a94414030704107601c10b4007622220b1302540c404140000404403c02c0d600704c02e450b0444603149421140b8030303091100e101681405900010000c002c0301561400c0840701c400c0a0f280141c0320303813140d804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486814397 1250 486813147 486813157
    0x28020405090c0a21050111070b0f01060203030c0d0908072f0312090102010f1a03150c0a0e1906020105011403030a09050f13092916030f0b0315011703 66
    0x2800100040c42444130b482a4121100c082c080d001402c181c3c1521515400e01b541d900b40b07050300e15074900003000400d00c4015240c05034042154804c0e1000b6514040000b562440000c20718450140c0203d400303600c01c60181c00c50500d00340c04c0940306031240203504100006886402440c07203400070018441c0e40058660303084120010006014124402443c03119270001e40c40040d0443c115562150301d00707514061417003003441c619108410400040807031820703d85007400741c121481e10f00507900c003080301c20041902111003c43d89854107080d284407000200d140b01860600f200440c103101c0c903000c5507480e41540300e1812106080e41c0003004c11040e40925469115001b03c81d000145007900c00d000c1800c00307488000b000800906a5010408a44101c10449100300c40c210f039041807a6003902040d21031a40c50740d0490071804580e1100b8140364043d00c00f100100000c0e4401d154071242107010300c0c601c590040e0114500902070300e0140c500d2180070f50740d0f00e009009401305841d10760a030001800000003614 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486815647 1250 486814397 486814399
    0x604060204060906021902190306020304060c1d030703060c0c0c0b0c0c0a1436060f0f1c0f170a09080d0207060c02060d020f0a02060901110d0c0228020405090c 70
    0x120680c0c640b0b400740009440c460888e00e07135840384640e0020000d801c520046100f140501d90010350384000e40c000903d460312042160019841281024445681c00310b5510100c80e404840020900300a032401c2d1660080c025002e041f204070001c1c005130b0403070000010018940920b041d100441c154200300708500169001d800701010300102069114140208120800031002c01e140b01850303840055030407040100030150024014403402c0c801c81c0e080c2141c100c500700300e0403030f56041c000f8400c501159459460750170a4100c0c0020f170004006208490003008107440d04442800d8542c42c4024001030700f50300c25a07100c00050610140000d6000001ca0340c0241e004d00e80d4040c0200c00d1411104450288215000342d0340300b42c00300528141018540300820042c100c40390469200d00300148003078204940242842402d905210310243d000b42224211803031444031000000b0540706a0707904a1800408903001c00d17002e20b910121120302c04400c24100380c1d0b28402c60b42071003d40d65110255490300c400761041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486816897 1250 486815647 486815683
    0x14040f08030a09390e221a0712140105120309090106030b13020c0c040f0f060806090f0f0a1211010204060306140603040b06060c0f060406020406090602 67
    0x50000d05000c0003590030101c0d848012031008501d449840c56241c20103e00110000caa950b0740b0150844864000e00b08007890807112600d515046400514076001400d100014948401c01ca0021050340c04a01d407458010b03510300035074156080d25a41c00102590032302c02050201c851300210041902801254003034000c580b0300320307910701030901c0840700c1424050200d84c0010702007840369803502c0820300d0080c6216a07022803164039410030f002e100801d102c0c10f8603109004010300c900426000030100b208800c29600010301268200780c01d40207010210b1800c403aa070608400158411001406600404025068600d000d03141d0f0040c40e41c540301c0a0004c000d80d0081d11006003c2801014101c201807031600742480c4103e004000542240d025403c40f40200c1e54507041401070008050080f9104142600c02510f0b50415881c0c05046e1140100414850240004d07501880714050041d010000d55000c1107407402c2c14286400f001940107400741c2000500a03c60000c4c20a2001440710300d0b480d002562 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486818147 1250 486816897 486816923
    0x5090c010f02030f0705070e061801180204081903030c0215150612010801091514040b1f0306020d05060d2f0607050309010905010f17041a090f011404 66
    0x15200720340307041200380039404140080e411056040c4000c185a43c03082c1c000c1d001150070b14640c00240d203806080d007030240301d8900701c210060030480b60721410366400540c0d03244004401041d83c00a8070441d0401d12442c003a01003054845042e0020011081e8801d840c03d000c030406c03401c0c040340d480154a1224101441d11808260124406500301c94030210150000e480c21458403903035200e50350280d02c88030140e9541c010b182c0902c13200b0340745500b200c68409824080c4001040301c0e80740c0c182d000381c0041c10781c040c8507011079298811030b1035080510612403400c07156141c0e2418008000c1d0805041001d51b241804001403403840c1c446242c09459902c00c0d91400343c6492070000298030751621125440c41080b620000d01103139036001c0600b1321544694000c6948100c8580010900001a403140d414003140607088000290025450107000034a14040c0000e50b03a541007050f20b801e21000c0ca2400072100406101c0c42c88004540f04803015410402440491188100520158400c4901802a00564a07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486819397 1250 486818147 486818149
    0x3060d1104090c0806011a130e0a06172802090121021c12030c05030a1e090c0e0115050702040b01110f10200a0c1505010b0703090905090c 61
    0x80601210409400028040c2c0035982c0d40503500195004001070368030100c01000041e0031340e4188110b0000506116042545c142000740758080c840c012070051500d80c90000b280000164000d80041a29958181c070b108169501c080d145d42e14413020401c00c124203005040da40508041008170603902503d444850303840d22107807000e07081e8009070b108204050852980d001d07994031011102981d44180c0e94a40032141d03868041c00041566460206160402c0f510400407034205068a80c040041c210210384140c40b0b04010100c219050030b880b1000f4038248180c8180715184031000c4c2910540300302050640d0301c2d480720401c003480c0d07483d0600004008100c644c00506140d0000c2035101c10604044044440854410f0305001d8026200d15643c1d1140030181c8c01c1025901881c0800120210599148a840891419076100311241c81c001c0c442c59048010400c07100040014075080e41010070455035031540240030a0f41e00a42c001e40014080f000c0c0442c180e512403050341d00810100c402060341043c0b45d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 486820647 1250 486819397 486819413
    0xf0103090219030b060111160b030a0f0e0709060501081003031409211c0c02060f0f040f06022112060a0b0705010506030708060601050307030509010603080f0705070b03060d 76
    0x5008076040b8400702c40300e046036400508414003071845454190700030b1070424001032a010761020340d0401d551020300c40801d500c500c00c840c2011b83e252401041c4c0d40c1d65640d0761a0010b89011260320b16541e24200d90075546c603501144200c266110903500b0700c9155034800045401e8401a2442010a0380303901081000134016100000000301d8811400c0c10b000300d10000407441c92202d20160b240b581c9020128500250600803200d002d4104070804408144200004200381d01c9511700a011ba4030010b01d1001c216030400603180703050100c0394010b9030f840d01d031a85010304130640e115840c003500c1003d5548404892001541c104525000c48946c2046500d00d258040c0341400342070250032506940d000300704420312230004c0082900a01c004900c4c2d0408905142ca0000c00354004c0001c1c2e080807003408002d0381e211003200c0e0015014038001c1040e03220030100c540107001da9400107280903400950040070010800141042c2e90040094510095807240109494801254000c3d0300c05801d00c0c0f03c0c40011081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 486821897 1250 486820647 486820661
    0xb010f0608010b28022104140d060204120309030b0c160204020d060b040b040503060a060605120403030e0706030c1b020f331902030711040b130f020301230f0103 71
    0x80d01051904244102140041e880c0c1a40f050040e040501c900d0b02d0900d07010351000020102c0c2c1c071b0480c601450400200d141c0ca0746040d015100b504614205411301040f60165400f40001c40b81150428a06103030107003406020b488100e40d560030f0b40000907801c050040c2942c42c800076541007804400d82d03540c2040000d5201222985005640395000715080c1449800361020b080e007207103015079440c104401c15290103001489080303018102441130040ca81d00400761281061403014a106a49a07464190301030a0399160300107092140c40000604c0542c1604030540480e00c507154a04000c411070b103a000c02c0f0003a042c020f50420006c0b911407809007003000e20005940b00201405585808803155101a204510080f110078a00400d48180e0184050f010300001607140c00214a0040c481d0380d6820790307034820f11100307110759a115078405c02d81d2128001c50491415000e801c200203000c1c02030020081d0000c4c041e00000000b0b900d042506204259801c1500c401d00900040364030201200440c040c000c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 486823147 1250 486821897 486821917
    0x1106151002010f1526070509041e030e090106030506030601060810050301050901140c1206040b010e130911010c03140a03061a0307300c05160605040b010f0608010b 72
    0x82d52a4841090f101c5100d540d41881c412040485001d20b8136100845052924001240920303002500700f41011001404c90100e400c181c5601380c0d41d90711030501c4282c000842c0140841925402458010140c3c46801400200000c40310141030346d0701c400089080780d008a88040e01540070400600c0068003400a8039800b40b507090f000801c10b0307100c202103800e544082e1072000c55691623030104c1500c030f00c0c070039144c5a011885400403030405545901d842041c030005044c16000d180d9490902559910540500031030f0040038004028455242c070001e002040410310545040d844200744481941c0b0400d228806260107690b90140820905501c051aa0028013000107141e50b584001680c0307451001082114130300600800e45030301e4502e00107004850b01030703044814903e040c8003441c1750408001d4102168080781000142c000d1400400740c0c0c0c9849480e541c0d410007614a581e000410000c0d800c10b80c40b80d48680021b40e4140d90b600201500d02210340140004541004e0060044809400141204482c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 486824397 1250 486823147 486823151
    0x1b02060903010c020a050f0c01120e03070c030f150513080c1c090f050d03090605071b1202150a020601030308220b07020c01090f05060a12020f040501110615100201 72
    0xd20010b400c4441c456030305000358101600314414440e0910100e80c080550030080c3c0f4081035110002040c2c5046407141d022025a09c5103d141c4141c1c0800a9840e03503075000a5102c2d4880c1c990520408138103c0000031034040c0707040c54005075013102501a00c2e0081203204a907582c40e28855442c610590444420513110703100e400880740d06542110320102c1c49071030b10740310401007e09010071a014040141c000b079000d894104050000203511071001070032652949405a2680c400c8e18003400e402c071890724068841c0190200108056083c94081d03018540b08544600c1d040341900b00e00320040c000e0001260258100c43c00410200340540c2c40c00d5401a048440c8a42c5130380101440c0f400c2840008040d12a4500c000402c45429010455241c0240b000d08000c200646410440d488850160203164024100401d82e082100c0c0142c06040c000b00c81007405640340d07803810101c070030075070018401c640c002440c0c2d92002c1443c950124009005802440c0840318000d1000701b03100c800446600386004540d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 486825647 1250 486824397 486824407
    0xa0309050309041103040c140d020d050c0306192d090218071d0607022416050309032b08060d050f0f07060f2a0206030a06090501151b0206 61
    0x1903a50302c22000401080c1d413015880c0d044c80c0c00c00c1c0c0101000e40d0070000400034941c100b09003980d02e0007045400c80354101d406e503145009910b401d508100ca40304c5c840d901449120309100403a101403180c0705441004100c10032284114480000c00b80d466840c40650418400311905003ca100e900701c0145036002038203424400718141d05813094407404417007400004035650410a41c69201d425265410441116218140440340d000180c82452403803e00685010690401400707480710300944048107103200c10308214400c0790138503580380c0d1310443c00c181c400d0164405e008038907031321079008104c062040d09050b1316403c0d00650070740b0011405840c6641c0580c090341c0700341c0080c00400002e003089503050040d140b82100b10703601e689000c0003a0004024880d0b221a0707244950b41c0071102e00180810f4810680c0710402e0013090007250500800c000c1c0d00180700108020104000ba000103040340c0030060100956a03a900000700300d04503c40018000034040486075251442550b54030400c00d000620041c902 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 486826897 1250 486825647 486825649
    0x801090e010603230d03140a0902190303120506100906180e09031c0b060a1809061509091a090711070f0303020f0102091012021912200a0309050309 65
    0x1013000307505501c1c150312800c600d9800d407043c002c2c01703000070490034144810209440102e80c100402001021b80b265030710250015565038004100040310b0440d0030714112038503410001c141d400d0003422007080600b480081005070030141501385c403035a100d40e10880044d040c9141220500d4404021894894107c080803c662204890850241c8400070086596000c51a13451f607032106142c40c140c030624544040402c1030b40300c00c42151410700d41840c084600304e04951040382c000031203402000c201031500c03e02144004510360306c0054988680c858046031030381c4802010948480000070885900b0100301c16034030b81440505203030000c0d02400c1c0105201001203143d49021902c4d03100700300c681c4803140c0c01c01c14035070148078a0743c540780e000000354a0080358001003075030200700d68410000c01054054100403002d455054030030b4406958058a0000503610f002030946008401e490000c5180c11540c09500740554a940304031092120614240700e0903520680090040e854150380e1400100a44411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 486828147 1250 486826897 486826913
    0x12020c0a0f03020103050604151401140d060e150a060503090307050114070e040b0d020d0311030a080403091d070509030312100303030b090103050a020f0402042411010c0801090e010603 81
    0x24000e0000c0314070540c2c0c9580001810794001500360342c003992400c0381441858001e03854142c02d13103c007202d4840ba0780c801d00004070b030b61698010b420002c040000c00c4030290b182d090f8121030201c804403404a041500c03040da546000707030086101c0c980d03c5070f046842046000e0007000910740c00700006003500e040500030f8a42d0fa00b590480010107601070080317400c0151071030b00701c0384006411005450810040324040d002c26503108030303048080d210b203214000150816101d24100c0000324007550960392207030080f08018100c4001920100c010031144280802d50b0489112038082040102004a05a071100d09003070318036910004140760540001c000381341a0300703c0030841c1802402c040d0781d84941c162460a0040407a801d400c01c0c035100b01d94110041006c2800020030425280d011a0b00600902081d00010300030711907a801069200d48003205241c80394038420403c500003421303890321200e54180c41e03012422500200c0c20140070842d5000144001f11a076070190f45c480c0301c2c3c0000055181d45036152202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 486829397 1250 486828147 486828149
    0x130e10050a1a2709040c180606120b0d0f060902010f080601051b030f130e060d0803040303050703021b010e16082104030b162607050903071503091a0402030a12020c0a 73
    0x3c40b03848118042280165407a031031f08200304101c2c81000b409044c81d03001043c46891034101c41105840d8480d4217021b07500c044048084130751058000703040041900c3c2180280560b40c005a000c180155030a80c000e0703008015142c0701d160140e441c98500342007200061001401d80c1d0040ca1a40300034007440301d07980365050050182004d140305122042d03151010ba01f00d00d80c1e0051510b030055601c115200c000a5000d01902c2d003241d40f508001c205650703494402c800038040c940950804c2258401800c14541c030640c40035104041c0b180980d901f4442040d00b4000c181100c0c85008500d0740015000700c074000c4100c0da00419524184003192821341e503070710341515013130060b0303141592821980c080c1d607002a041002410240001c0c48400f90241304c59402d00d1081400600c044240000001d002c11295001c0c00500003420800003041c00d0b0011780d650040c01031120a030102d900d0007202e00c15000891030715030b8152081d6401001000321007001d43d515201e9900344411542903100d040e5421005540b01c18440c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 486830647 1250 486829397 486829403
    0x3080d0212011203090b1b01231503030d11070606140a0608100501081909060203071805030d0e13060305060f01141302130e10050a1a270904 62
    0x9600d60800c04544201c010040e4081e200d1144402c1950700082d4220078900308071002c03c00d10350f0b110610b0640c50b040c000314803006c010760340d480c089095580450b501d031402207800003110311880c0c40e9140404c80381040c0c0c02e045011b80c03541c0180f0980c421002a41c20039402d4010314410142030885598034070094544c1074210654030510024610580d04015028400802c041d10300000c040c280340c000c41d520302c80e03207008080c100220030001502e022800e401c1002c1c14141c0c1d217010800c070520b6013000740007500142c0300c0d4400116100060480c581c000c12a040c2500d0008016010f42c01e00030320180e52581b50560b080303401240f0400703c40c0b803401207441801c005601603005840245410802c0700100700058002400c504808100d50421351070f66028880441001000165218205a0020a021400c0d849181d840740c10b402003285042e142001c0e041291010342d0445651a00c49503216000400c01a403100280e00900111034290405005c14a4480300002c0c6c103a06003103c00c01281420004840c29 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 486831897 1250 486830647 486830651
    0x1b0e090a05010c080f04030311120403090519051509010306050603090303071403010e040f1704081b0d020105070b0411150a020d08010f060c1a0103150e0309151303080d 74
    0x314140002805003100080780d61512501c0340c03800c1d000752180c611010300701034100742c4d0302c3c19900400100c00048400708180d01049031079034585450b0040103c8032902a0780d009200850340c1580c000b500b000510f041d03890041c80460b00541c01c180606c0c15801c02a0b004d8101a00d52100081c41d803540c1000303500445d0080040e41d664a04244058145c2010103100b51500e5000c10041015010041a00d40c04c80c2d4884a4240c0540b140e08002e0301d48522144031081c05030002038000390700d03440090109640c4000c3e00240b042010f4040820a1510404002031301150782000044001841c0c0407d140d40184120705120003002c11501080021001240250315001d0000d02c5940d51501084003143d0101d0f01c0c07516840c29810008268001072003403060344103128512094408204461020b0010b141c0304e41441d0040d0360792410b00250030b001000300014280d1801512850010012044070720361500a4140203020900400c812141d40c0002c0c404c482c508945000800010b440000800c26a0212440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 486833147 1250 486831897 486831913
    0x19020d030605011809020a110d0c05070e0903092701090203040320100e010209091e0109060e061002030715020d18020d0303150f03060c080703181b0e09 67
    0xd021286140c0060303042c080f91308455904030030080105000d40d80301c2c20000da22004d5205003510b410240c0d051082450040d50220540d556126103c0103200f400b0700101d59446070b55490a807503500080c0c480154940007040014070a0400510b00c0810700c50000c0c20b0a004410052a81d02d00f400c2070f0840f0202940010a000a265012000e0000342074032418001c6030b5881030721001e039117405900f0315003460f07500d40300b024030aa00c0a5064403650032014080c184a0724007c1d1421400310f09000400c2000d0700300800100e104249440780101751000001d1a600d2034890b40c041140150501c4902d0045200c10444000003450f44103a810500300d08150141e00c03884060050030070341e0300e14108500048501040d10b0050380c0e46a040901c000e405042c0010810034181400e101c1510b241c101e001c5e20b048a41001041101c0c41e0300031284414141c5d94100795803110607084080d540f523035038010782c030b902c030480d60101041c9014203500904100c8641c110501d966055440c14a0303400f04d441c45125046121 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 486834397 1250 486833147 486833173
    0x6080a05090c1806060409090b01091d071e081b010207080f120912060f090c0a0b0a080c0d1d060907050a17011e02070201030605010e06041a1902 64
    0xe1039000060980a0181ca152070408620841079561204200301c0030180860350366140c5404032409000500b100303001000d410f04003004080000e1240e481c1a518004005941101a82c0369421404044000d445107515208a00301d541d0940e4a00494410286000165105081003486a0045600b0700080d20344815000682170400ba944a014540c00800e40c0b000410004581000c0c0c0e101310304543e54480080001040f0301c031000c4203051115224081c103000c1d210400c0d40d545845400c0100403141c1840d1a8403d00003a0078491051280364182403000c684507a02030740704503500104401090703050949260405043c2c030704042c6065807a980e450200a07400005004085c0d119076010020302e452850300703001c140c00019521a0341c41d40440502000d51030717502900000084503281e20440034903500000504002d502041040780864a4014001065401900c600320440c000905041c201890310410107103d901142c0b0b00b0100729401c1018071501c520000c3c0700a0030070f110b54020f02403111401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 486835647 1250 486834397 486834401
    0x7140d0e07050415121e030207031707020117340201050109330b0f0c060f04150c030b060a08040308090307020a090b0d020409080c07050d050d0e06040f06080a 70
    0xc1c200078011420030351100ea4402003071641c98212178003000030342d03000101c0741001710b2607008064070003107143c584503c043c0506d80d0019419080c0c074028091540004501803c1c24039038400c80c24000d012078001040c80e4011090030743d25540c007028081a18640004801c100754409402840040c910700c0b04404002040340d09204142c05001505010040394100d21001000000f02090785508428200160280c400426894070024805c0e143e10035103903015640c1c0c7c8c03011a0404001d2041390f1291100250030030a800400324015508841c1145d025126151858003420100b801e8105160b00d52038080000c0d16a0703801006070720513a07526030540741020324000740b2215010b0200b908076031050200801503a980c9101508842040500290035882100402c9000d100004007950203881c101844090007e620014a0100301080035154816110003c001003001d0a00e0050700d560b014010701c1c1c2c0c1c014000c81d240c0354009d00080c030050800e40d0311100d00310815825000000002c800c41c042c851040b03101c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 486836897 1250 486835647 486835649
    0x50105070317180f0303040c030b060d0816060b03010912030f02070c0b0a170408161703040606050909120405103c0804021e010504080d03020310140a090507140d0e07 73
    0x81310246256047c140c481c3c016000b158000074080c0100c840104480d5600d10900c801c40543c01601c80d0344800c0c01a810400001c0e410000391000c6042000222107032070f040c403500403480d80c894141050f076945e6040441c01440c413400c0d40640f15034200304031310110309400c032820300908410392141d039581c4a0500081c0f0b1020624011604030f5810303400c0c040090040f00a40e5280114000c42c0880110b80c1d0600e030200104603164515269400802e100500c51142c02c10030607200300307a41c0c01410384ca0b407142075641c45030703000488409264207000500640c90300400d41c3c03240112904c0c00e202044026010903034174485134102c160f03128440c0c6004101d00003501842070000b0100d0705058900d407a00f5008100008110080002d00c8000c161240e5002d07030261054601805c3e01034100e8580e5412840c000d4025803065410030b04070100d044000801081448031061a5940078001c0c0034014a05421000513020140c0400144210040503e80d60f14086001d01602d620409000c1942610706107268100089 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 486838147 1250 486836897 486836923
    0x62d08010c170403020309150c0d050a0f03181a04050c0d030f1101110d06030c090b060901080903220e07030c09060e060708040303030510060203090a05010507031718 73
    0x400040d071404a410000080c2c1c04038500207110356580d610316003241148203c150301d07540000c400c54500b0380800c60801604800000c4800c81d00080e901c0342e0291210701404802d1f03800030b41021005c101c01c5c0c1c403036044061000714425003e10000f0f0b40c0da541315580030f0003240d00da00c40344d1034001704014444100810b00300150107640b84440b062540c4c03401401703a480580c0c050103004101c04804c13507009003580440c030048c0000018036110722102c07e816000d000d60348810313944118a4080811802d802d440340d07036071000c1d0091031646010140d00041d00d40300402415040140828410075108002100a40050340f0302d002001d040141020451050b8000180000b8101443d0800c000c0c0c500e030300000c2c030005071079440c102040480b44d250001440c41c8252940100525000300d8000201601504014041c222003010080c106446500480e034070f005640c40c6039484001c3c05400c00a80d4001d000521855001e464007100094015400ca0004107064407450a416951031a0102005081c4040150707526 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 486839397 1250 486838147 486838151
    0xb0f0a09060c050d0509030f060412020f06011809081603020c010807022d0316062a02071401052203050c180402060a1803030201050403080f0c0a030f062d0801 70
    0x490b441e070541d40d03440c4000c0384017448000100c441e180d98040114000310707401c260460b0040d1030240780242590f5402488003001d88500c860030048020302242842c16114a2501d010380000021994005441000429101c40320100401880784044801940085000303800412640a058000400d4901c00034003000031900400300344d00021b180c01001e81340b8a098100070b08800c20f0902c4081e0301b1880b65201c3d02c02441515002d0720200700c4550040200010380711110800c4064080007040c0e00e4841560a80060304595020f01602903003080c01342c0780900c11b0ad49541480056400744000c2030800d0700b903401c4481e854808008001e0304100d072103e00042a00c0e40c86241c00c420f43e03401e115000107040207100b004003240f9800d400380304520803505070740c03101858001c403556400d000c2e0003010155030950000d081d030000030349001c0e44500c0345800b076640303604464508a80c84004034020b0024020002c080b5898510000d1a0503281c0700303080301312070004000c41e40110004d051048000903540180c1c5264 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 486840647 1250 486839397 486839417
    0xf061e1d0f031903120501050102070e0f15090c1308010b031e1002031801050c0f030601180b0316031a030304030813180c0e012a0201090b0f0a0906 65
    0x125400400d99411000d8508640a00725040002e003810503549455035002c11105108050540c0815124940b1020100c10001c0e42d884030300498032041e01d40200c0608901c80c5c03002c80c1e442907603002880d03031008121040170041c20704d80303002400480065511081e014400701d08626070209200da5400140b050400800c40c0c03101080c0480d0315041101301790b42040d0003c00301a80318440074000181181c1000c0c104641e00e14080000c01c010740b0150409195039842d280001e420a4181340840b404c40c2c41410b2082e0640d611100111b034001600741003040803007030400c2c0005072501c40c10083e42c01800e4001400e00b040590100040c02c4810790702c02100e00e008598040b8480b510040121801d880d00143d2850b0f89060003107101d401041c069100d10000028400c000703500007090f0340400c0304540c1c507607111031818880c00e00445c1c40e058150480c115543e2030800706a5620310903035410340d000d80306041074071410350f40b000007100c0d83d0020130301e00c0c03201c610020750031200343c0c1d001c5d030420050401410610081c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 486841897 1250 486840647 486840677
    0x61e020d1a0a060f020f010e0f0d080f0a0c0c020d0b01081203010302060f030c0412030c030914100e0117042114030f0a06030f1a150310150f061e 64
    0x524240f10307200034014544089070846209100c8001c51a800708002c1c80400b5860054aa540800314124140390007150030344800c00e442003000e1400f03071840925881c0c268640075410760040c40c2c101c0d800b41c02c1c4805e490341000161200742d140a00700d8003c2a0740500c56140c003d086080440603c02c2e024100d00c100010b0005036031b480c09680e02207100b921605d84035541c1e00d25441040c40f0320f030002c40d4002e0307000c154a410164080c85d240312585c4282d4403a00e0065a607140408600440c606103a8050201e01a544445108417207540014405140483c540c101c0b80d0030850006106640c2504c0c0600d4410029441c010320740c88100f144c0601d442e108003c0c06201e929607400303000180c00d103890300c0c0009010034203585068011034082c42d08458040701910252906024034501c401c40c16081c82110340001d80449440340082050001c0503025000c031140c0c8400a40052101001004607001d400001180214a807960310000d000b00781c680e1403180e542c21600ea00d113460110719440030003601e0300c207030b9401c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 486843147 1250 486841897 486841909
    0x3040602031605010e0a150b010903022d0604031a0702120a1407140606030f0d0c0609080c0304032d0f0f020a08060a0b011404031e061e020d1a 63
    0x641c140b0a040310100c40c2072460300e035001d00000d070201d10f9988035040341b0030180800b805080c400c2c8040608200b01c1120458019240130090388806580240c0f003451000840035010b07641c1e0b92080010058800d0302812100140c1560059082518010030182d1080b560f6a07454400310342050442c001400b0518149108201c28840d45140d00300300244134541c0092580044142c980030781e0700c03045050350100c51541c019034485003102d440344039114588070103407076050118030b640c0105100c3c0d4804100341c4481d2030303141c00381c1403400c1c0485240301c041140309001941030001c1e20107035200c2c040e0800005110b2180d468410803980e15a0003034a48500000001513030000c0c0a038145601a00c0d40d4a000f40c140002100d00c6c50b1313a800000240522001c0000104482d48052040d036000d0301c0f8440b10618980449606000d503020041415000110003400e50f124000038405491051402154004580c00d400c4100e41c01e2581d0907454503004161569410030a021340c14a41d0044400190014006030009103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 486844397 1250 486843147 486843157
    0x60b03010e190f05040654020604030302250506030f040f050f0d0f020604080a1b06020f03010303090803030708070305071101110409050106080c030610030905150a06080304060203 79
    0x400e00c0030300c2c0014100c40c0160050300042c040c041c000c00442c940b5060803009490000428070100513020740060b13003410f0380d249000101503444440f6152104980b0840c82c103e0200b6607072404a01070402c62001603892070014405544242c5c05042e00d605811500131924403100505900b6821120050085869842c16a5489a940a101615038607a0b0074400c0b040286140c010f085405420000d00701c00711700048458010b100c0d9550090600003403007049031614015100106400303400c2000401c2c40344245903124241c82150700c8040007460546d1000d007241c0c00a64400840f1350040010410b042c0c01200c100001c087d260007a41c61072404010080c01039400901440c00c1c1659107011400d000c0c07041082e50708080e01c0c43d0082015000a45801d9004d802134446c80c86998200000428282c5c410004a0301426500c195a419034480c2810409440d40c0c00d008101003643d90081c91020070303030030010102c62000d200600d80c894240700c0c2c85070080e6141508000e8181d40204010050f0030b6001040712 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 486845647 1250 486844397 486844411
    0x10e0c011d09071b0506040311030a0813020609060403050c01180803120c09040c2a120507050a12080a111e090d140f0c0d0201080712060f0801060306060b03010e 71
    0xa0b19070b5a02d5070075101042104074070b899400c00028032200b003210004401d13005502075141c240a1426405030b142c0c0d2481810201800549490041035242d07401008000e1510f100070565403d100c0402c01003020f035000303988150380e1075120244200c403070350b04001c0d058500d40e4131500107881c003410720f10810b6482c03189a851000c1a00c08100007400c404d03c102c15030365507880041c4244540061b8044c000e01070300090740f050b1948610000b072110401b0401d500e00c0001903000300c00301c04c20001c10700705545c1d50b00b00581c01c3e034180c0160442440020501903011030700a00076180d180143c00c201c0d0625048075040c1d500054042d0041180e03800e00c903c3ca89911088005070084990341d1003000010452556035000000c10401c840700c0d440c0025040418030300c040490180441c0d265070800010840d00c6d180f06540640400e80c14000300c0e608034480d484542051142d4440414040c0e07440a81071440d841c254013207078a69668600900400c00103003c1e010007448500201808d43d41008041032415a019000b8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 486846897 1250 486845647 486845659
    0x40908210402011d030c2d04020c2109060a0c0b1305071a040911071a0709030f0807050f100e01021201140a09061410110d03050601180305010e0c011d 66
    0x3103800d0354007002108966200900300d0f02c024111048401c0c1510002265147c2c01c0302010070309410350400d4800c0d079080c100c80340e00a00f504d00803a50941c4103800b8899400c0c040c400304108442c02d40c1c0703405005201400e05996203602e00d179050304099006050140038801c81503501050300001c6070000862009560188540b80b40c4481013507495103180c03150784c0c8401501410100c42443d0070100340c0c0030385800d1f4010b64180f03580c114010203026042404458010105d07011940500c00b2030016940001c101c0c0c03141c8405403509020b91100d80c0303003481c0607940c0d48032a81314142c1d8075094010b80c0104484481c0c01e00096040400c00328402110810500640040e405000790007540782d41c0e4034207140c0c010955410200a040c0d158001001d200036089074a9000b2888204e040c151944540f002c02d60700c24114001d0591074100c15422405004060442410071820200003100c070618250301e80002e501c602c0c0009072140c1140403c03801d00e0740030802c0a060010f20801c40780c03104016020314255010440da2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 486848147 1250 486846897 486846947
    0x16080606100f17010e06030c0d030507110409081308120403051216170309010b01050406080f0a061d061306060503070809071a070b091b04020c010b04090821040201 72
    0x403070320844450098180300c80f4040000946100b11080340d030240d80b0036025140d5602c06030b010310800105100c0300400080c000c1003802c1c0441c0c03001c4007213505800c00501c045490b41050301d450b601504405c0c00c6040340b115503401040b8080d000c00c06512000103100c143c3e400c003443c586801c0c0e101d041c040800200801c0010f21a00d5940c2d8421000c89000d500c0a104454502440e4508020b41c208951710f940640c81d1051039051507002d98290307403c0300c240b65140780280e40c805084481e0b00c107001d424084025240e04011500e540201002c04000d5000b201c560b02c50b00d06981000842c515044083e2681407a00310280250340d8450100c82d84100725007004034a0b41c0301c50443c24070f42038241d88803000640c6120303c0c509035590020000d0402c1c0b400384040341d68540740e80c070000e81c55010700c0d40c040d69014150130104900f41840c0c1c000d810442c00b00800062a5140174010606440341c08508407680c2000050311480000d000842071002c1c85541e04080103450180d0011b44215845403401c81c4080b0240c40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 486849397 1250 486848147 486848177
    0x110a02040f0f0c0c121707030e0f0d0509011d0f1c0c030308012607060c030e0301060609030203150f040303050402221d01021602060f16051608060610 66
    0x100340d40c1100c103540300300080c3d81d075558004c00d48034010404803540d00c0384c6410380d4042c038403540300011265451001c143e15034407000000d50040024000750030460154031414000d80a003030041031900c0c1d0641d105e0340c0d40d03980c01100040c187d82e4054070054514500300d0095000c0e03281c014071b03031000c807000382d813a00501102c40c442d00b07103040750100d03004103000e202c02004020154440c0400b4102e80400c40b4503c0c0c50009180d13000c28200084030300d80c41c2980300c1241044468803c01441c1c13a254040d0400640e0043c40c840400d00f0b58090b508208041000010100300310305007080004038803160800c8040c1c030b505041c4107184003503002800c060304043d128000b01d81035596000802020005a14003508900800d0b0740c40c01c06040c0c1403980c800381c4a1006404600c20380306000300d482100c0d034040d284400200d50b41c00c201150f001a032035070700030171418080d4032101100e82c06020411405080100051075905141d40161444c41e0050030080c1c0004051001c0d9071601403540b1010003803400d0107064074840403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 486850647 1250 486849397 486849401
    0x30a1808070b040f170714010c0206061302120c040303020705060703020a020405100e130201020106090b1804031107080109170405061e0c150405012003070807050d230106110a02040f 80
    0x507501400e1311005c540600890944040248001441410380050348156000d02134200ca01e40d861080c09600213400059140c640038254000a003021480142800c4100703600040e0944111a5034845401c00281071003816010818000144401ca07002490528a641e009440300903040e0003d0041e9141c01c00308154050028045001e04a143e0340300a2624040205210740388500e482a4059480d141000c107079100e142c09450b003000d8014241500c4603c00f0f110b8900040b000030000d070100310391220000c840000500c40300d001000c1c10000880c910b081410000d0341d03a0304181c1e1034410f0080803c410449601d40d9070135540304414141090b804140c00d03c05030045440780124441d032501942c190013855405115179940514000d200801014a4001d86601e00d0344094a015a1010f01400020703003191180300c0495000c80c55192140c100440312407102c098510741410354010700c0806500e001c00e48448404c440c01044245040015420b41c0c84016456840ca00006806142c4982e69aa0b148401ea = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 486851897 1250 486850647 486850673
    0x1e1608030901141005060405060309070f0803040f090c0906120605060d140c0304020927032a0a080d020f090d1202101a041a0a0b030a1808070b04 64
    0x901200d55915003140030500800041022204540301440851401d00385401250161040030344914034090600d0204445034000411401d21445500b4021800028800d4010006c4c1640e200460f2030314103041c01030b0415102d44e000b00840d18548052140a164408541011076078a0f0400d211b166400d0541341020307113101d0704000e0f00401d0014003150340301003d500c5010840180103c0c0c0180b0313110b14522180d5448103032006584140c100c80810f041110f190b0906248550502100e52861100b81e01c072411a04006059400c200d1038001c08020302c00e42c24a00540800c840024020300c2c912a0b88590550242d2025011900d40c0440e5690007102d90700f08a0710014002444540e0103561031400500c0c640301202c4090050142d401c0d514903094550240ba0501036909100d54604120031042c8401800040d180b1690640d000b0349400b410b4480c14034120161040314074030f41d52449d184071070310241d030700b0850705441d682080030802d4003088440c001d90705c1695010f002c01c1841d0300c903402e00c403c2d94992 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 486853147 1250 486851897 486851903
    0x30e060a0902030c010c0f06111804060302100315080f160611070306020c0309130c090e0705070b2e030c06021501032a06020102091009080a02010e040f0c020601080f031e16 76
    0x2c2c2c2700c4108000c40c0410041c000b85420b10804c18072101d0000140403e542691100a401c040521541d00301c45000b5044040351a07143d2141c80c8080307945401951400b0135110b961304080d0400040c90603d00084c1014a01401003414640d041003003190300e1a0361400d1138407024000300c0e80403071801c054400900403a807c1c1e0304010914589180c45e00c0c0380c0c1c00104420588203010032030106002501341c24031030b4218442d02003038072500e00b0319625031220080c07800000c058114a11107910201d460200e10500070b0454001d904c070039110a801c62402c14110705194210311705560201082c0501140e1030258076041d01d034441d40d0f81002c03aa440f00e0301003072000c107540c0007141840c400c0004a0706550550103010245c0d0200c441500e6484e50340c0081d12694524000e11401e0340014040c240503500800d0070100140002e00300148101c0f40300c545808560f040d568201c016042030004001000007006006c2c0b0411540000c1c51404c40c9036142e14020062103d40a10314180100b006221290741d0701a002500350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 486854397 1250 486853147 486853151
    0x10909020f040504120c050f3c060712060b040311040f0204050d0303020d0b0a0803030f060f010e0906010903230f16060813080304060b01020d0e0922020d03030e060a0902030c010c0f06 81
    0x9001d00e036202c40c00d0004108403000405046003652489427501040120358240300145c600d5880380c060407171b90285148009996075403204000200b1910b10030040c4011170040c01da00c42c841001c542003000f5510b0780c840e441e8156005000501c815526100b55180c0c0c681c3c1428016540c95043c1d64110103800002c90031940030201c010005041c280100045110300c1150111105d00e5850302d041051600c2e10a10250005207002250b5141e82045601c89410035414144041603d50740e9076000c1c95a1022034041045403494105e96114000c1000300b8881144500054800071074048101c203000708a80c8100002c101141c0c0100e6201c01e00142c402c1102a007044803507640380f9160400c40084d19011010500500c41c52030101c681c036100b40040355072484000d010f000d09803a45035054030034801464242e9900700401e6000b400590b10702c0100d4500301d21070f440c049024090303407480ca811b00c440104010a41400d0040142c016940800c0c0c0c0c017000c0c03600b42070400d0900c016003030440e0140c800c900018080782c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 486855647 1250 486854397 486854413
    0x5032709070507020307090c05070206030702010f0c1d271308070b04021c2a090e010e0607090f0b1b0312092e05070c0803010909020f040504120c050f 66
    0x160b8000001c01d4110700940484241d0742c1d40305900d40840d40046a400d000803802e00c0321070014a0168019504541148004909515040360700002c4809011170f92010850307040400284403107ea001015103a811070300066030341d03030030034000080b00d045601e95000500d201000800359051560308032159500004003680300c081c10700d0b100010307900030341d4264030400229615040b0045001c1180141d540d109080061410b01100740c0c0100d074401140c0600c0c0380044542c0400c0b800030a100d0446041c40c10701c004a078299a8035a41c50070030b600613101804104c21880227104905140c2c44030310883d1780c01401c01c0e90710148c007040b0054000c1c060815859500002498011800102a0b0b040c0074040c0d0005540305007102c00d0700a02c100d1051140e001c4041e0b140b1160000c2884a1760040d40d10600da410300d00341094043e614804141c0c8260401c6030020341e0361041c401541071204c4880e4980005403070400c81ca0a098490400c02c11011a9900801c120f90403070108001e0103102003080c2800c060200c40c804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 486856897 1250 486855647 486855661
    0x100c050c10182901320f27161709100207080909060306090d0804080c03030405060901050105030133092d0c09060c0f150f150305032709 60
    0x202609683c140b61860400c000700f01e440c645030300c156800d030403602d00040c031a000e040454000d0300c00c9264240d0180011505c1e058649920b40d030904880c10031a440d81c0030303464510545c50b4818018090951003145102c3e41c900040d048070301e180981d0450b0b411100280d642c0800c0611301807050030152042c50011500d4000c11140d04090810340c0812254034800350340700001e15950303640441d00040ea650040081d428450700680601e83c005002e18030142c40d0105007010702e8a10b50041d20100c403658043e4040000450080c458a8050203044000f0300c00c664240c10140203240358a050311f005181b00b54201e1440b8014241414010426001309100e140401481c02c0380d481241c400d0341c46a00145070441c8a165264031901034108116102d01421a0410201700d983c602503003000c8824101125074071000c41d081c80c0080c0018202d110f00414032404522061066031101040c0c01c26508500009000150011042e10450024402282100d038448038803680905060f020164100c0c24403010300030a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 486858147 1250 486856897 486856943
    0x4060c021018170a060212041b0302090c0f07050f010b010906030203011206020705030d05090601150512060f0d08030c070218040c0521010e100c050c1018 68
    0x10480c000c0703072024000e800c901c4040c1c0701c2555514900c520402c40390020f004014100c02041e0082c0150001c0f16908149030b030380e22080b680b181441c0304c40c035440d910401003006035049a10754054041381407000c0b41403559020070804840502240b0550101088143c1803462403410350f100c1a03000b008641d101d544024005001300442e41d02a40050824140441c07124040d000300c1b4100ea000203111880c0010136200c180080d00140340c00c86080c01f0400000d2844d811502400c0c0c020840d150180c130740b03940b50918150405c0ca03038000720705c01c1c020305000f00c00701d031416080c44a034011070560b50318080c85801307000039100c0709500000a1160b80301005000c0c2ca01e103204003419107644243c1c0c000a0fa5182e61004804044080b20024010004418103004600780b031041c040c1c401000b2440040010b10072814182920359000d61000c55031700054044002d0449801030f070508000c142007240c50321180211054440c03090550400031a9222401340b0001c0c07003074920000b11a0303007050305ca000345038041c1d0110f03403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 486859397 1250 486858147 486858167
    0x60f0417070c2d21020d0b0a091b03023307050309010305070f081503120c03120105190b070f0609030c060b040507020d11100507050a1202040609141201020a050a1e081306110406 78
    0x2091540c0403d03c0c0c0402c0c1c545141017060365000dd00c1c1035810061048041c84000f048100384910350302c590070020800000001400394188600301441d2620000c00c001030403a880180b0801c1080b0620741fa5140c5590400b90054008403d40866050484c000d00070038a0180201e0801041c8a00082c500b500301c04040090070180161380400c00c49039a032801000713180d4211100400710b00340d2140d0208407410350000100003c6100d0041c0e0102d59a250702c1b20b10031162000c00c1500442c400c14900030800c003a61040f10103c9104403820007107030414480c002e6441c45050100c03014044090103201039503a0402c0050004041013506201c02e00d041500200150808051040466000c0c02c114015208a00940382603c000e503a50b40d410926190302081e00056450711a50000c84411101030740b02e03030070300040035681ea55441d6165241c1c0c108000070401c14512038021110300340107016101150b80300c04200e4011020a1408144418504054000b016961186460304400140000d41c86400ca801e800d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 486860647 1250 486859397 486859403
    0x30b04141606032a080703061d040605071d060a120c031d0105010b0f09060c070608150604080c01050304050f1518060f0417070c2d21020d0b0a09 64
    0x1001e40c2c856108810740c0d40c080030f5000d44000282d0700603120658030174840703580d00407a0740c600455443c0e914001c94040119114491058196003c1000148012401403507000280c51910102c01d00744c0c002c1c0800301a440c5503003030b44251000200c2003001031003a80c000400320128001000581035015014005225141220644426011100028940c18400d0904134dc41001e0200d240030f2011003c0d409541c010b010a60780284140301c20102e511041040758003908003904c0d450380754101030000030b940c00751114a0714405d410801042c0551303003002ca0100b001203000c1c01e00c692652218a0884d0800f0582007550a03288a0035424608500c0c01525142c050b40c00c507054010881100894281c0b540822500000d01c12081c10104002503001d00c1c540c0090b1140b92105400c10650b5954140410701550011481c0d9240d10010f07042c003a850000000e090041541c2c01070f09500c0d00d07a009407400051580354803000381046a090654132548611082c095100c0e034940340c64030b0400705041c001c3c000c001081e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 486861897 1250 486860647 486860651
    0xe010203060a150503060d0c090e10110a1e030b0618010e01050c0c0f040609020d0204150e0a1a0706140a0b01110a020910150203040e0916030b0414160603 68
    0x5010b6980c01007403107940c0b0f050303914146180d59650621100c04070303010080b030303401a0b01c5200180091540c03040d417681b840d50b00060302d049140c004d204020389000701502e40c2000001c01030301c070310203401c030910301e001d070407101044c0084410303101c4168018025401802d802210004000984d811710b90001c04c0d00752002d80b42c113414020003200440b0140101c0160710107580c4070b49032140c031500e4100350002001c2001440411080c0c3c1794416601039030458117109014a030081004d01a01c45410080030503100d4600c0c0001c01c42c4655070000300d00c41c80c5031040b010702981506034000a07046400031112820b4000b48142f000c544984001c1071400e40c01c540c5200f00f00d29100741c09a941d0b1103007206130b0b44003482900501c030542182d020040d248001400750085010761030800100742207004004440d203042c9030040e40d00c0d1032501d0144100560024140030b51a00110329609801e06103a6800707017940d80020034000e0340d5965240c0008810f250740300c401040e05c200e07042c100342511078100120a550281e0f8007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 486863147 1250 486861897 486861899
    0x714070617040f0f1b05031e06240a0303080403030f060303020607030b03030c010504050a03080a18030e121b130920150a09060f021908090a090e010203060a 69
    0x216210010141c015480810300d40100e00890305001c01044400e01480002842a0a907550440004003a032103012041c0803c07042041a4039050240c40c51840d15110341003840c1c40e41041c460f85540c0000d2030420008004101c00b40c604174441014408000090b01c2040015100c0c14080e1400900321070071030001342004001038900f0700902403001200d41c075400600b420348075214250080c01c4150754845c2c00d40b0042c412100500000d02400d40924050009001021200c5c2001420300c7d034010010310301c1030f04102400902a20700800d220090350945400000282c4d004002901d080018400070303400c0c0b00d035040d03d0110301010780c0301e280400001c4803d000320310610030444040d200140f001511b0443c2c200c107101c41610b40d6003003030180c90750014030228a40c40703001480795143c0c1000060700009118600b0510200d42c1001e0b40340001e1201340010040c0940c10324800d6001641c0c0000186880300100f4000b1490f1610707051a00a40003442c8180030048507180e0860007500100c0342140b0521003250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 486864397 1250 486863147 486863159
    0x50d0e031603050d09170711090108150604020c030c060a0e010903080406020309070b030106030f060e0c091302040f080c0f0609090c0a0e0d080c0c090705070303150902071407 77
    0x400c4038214003660034203900d015070603103054806412641841007040c1e11140c4100004010b001c00f202a03101c920005900d40d071090818078130050160788018007031380c1c1c81d030018812400001810030401406503a0b00405940d490081806030041100d0f40c8854030000c16000050b1101040003445407104060401000e81d080c0c101c00e00ba51171600c0c02801180b8008089004213805800850b031050110703045410b429698030000001d0b42c030903403001c0c00080d95210304000540c2d2500600d002041c3d2596981c14608007180d0499030317446800c010500c10039002081440210094040c2d0b03006100300801c1b21406942d0380c020b1922840c45040c000d11070404820303428103502c0c028065920450300a0718000701d0760755410151200d540710700c016200340304e2080030b2110b1903500c2e05007406508c0d02c6103a500c1e448440c2007ea0a140032641c0410703603c2482e111701003044d50765001e416500c00319098640030549003d0707062811001c2049800204146000080d000f061144145404104100c4141110310047c3d580c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 486865647 1250 486864397 486864403
    0x2010213060525050a0c09060e0f1906140301060b030c0a0f110d0e040518030d0213030209010305010c0908071802090303131e06020a02030303040204150e0403050d0e 73
    0x805412010305140320a01680c0e205034080c0080c0e5110307001d042c0c0d44526000f00030981c02c03c5200c040b00c169009280e25001c20051a90501c002c166401051044900340803052079103140081ca0003c0f0aa50318001071007004880c01001d4420404030000c00c07459072601c103004020034103c1225070003036080c0180041c41c1d049090840e03201d0a00d5001c90b60030510141070445203580300c1d08000c2d04000403580755a078074103010b11400c0b903813040d07a46605180c100b01c8030a020076240010030740e101c81680f510700c100c0072110220485000740c0d450000169070f020700c4240001018030540010f50003444150000c020004150300000c21004241c0350725003450344c1e40e24440d6541540b40100100000c10341d01c0081c80011300d4014010740340c0c00405403805d102c1e2100c28103501d04426448103d101e00a4545032444000382e0100f0030280c059813010b00b1407182c007a004030340d80b0300c8084c000074000e0340d076104813500d0020f6400ea11400ba0803128100340076810142801015a0050140c60200c00d1030580300c040307400400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 486866897 1250 486865647 486865657
    0x41a0304020f010e01050f0a0f0306050d33140f090a0510090606180c11120304080306011707030c0206130b0f060a0503010e0106030c0501110312150a0303020d0f020102 74
    0x30102404042e5120045440c004009201410310506021050581015070060110b140066890112018407044d005040e100140d001e140248406031201011a007d1000068112020140300000c503450040750b0302c840e414610001071451501241c048441e100c550040e0040d142d40048004640702e01c0300150f1a9211403200500f036a01c40c510b04510301602c0d4200a41842c000c1c0070000d034032542c0d400131003010000121800710050b5130f1034807407078015001009075201d00100f0009004403600d4046151031484060005000c21902000003265030f889100c2d01101040902008580b07070824140180103840250241e5015004060001300740341980303184007400c107070081300d0015a51a9405500300c000b0020340603d8000020079000304843e2001d001c1d0021031400d0000028041e89507040003490b403a496048941000040700c01024451400800e8070400a807242e1074543c1c3d6100e9004840711120189040342d003101143e0000400e240c0c0120b41c80c42c441c40c05894039520a000704600700d00702d203d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 486868147 1250 486866897 486866899
    0xa120b0105030d0c0b070e120604020915030d0e150a0914091605030403140c1b03010209010507120c0b0a0e060f04031b0c09050906310602030a1b0302041a030402 71
    0x41d9100800440c4640300301c2c0c6d4014215041c000c1c440442003010031a0720b4007450707240303800f603010a00780011400d00047c8150700c0300c1c459486a6460401800083c4c072020503d00030420000c0f21740c4011174565034140d80348a80c1c0403030320b00996545034426018181c2d022074031400c40050044039042800d41821f00c050751084552101c1e11011649000065820760809881941001040c0c01d411a500b50607400070401c94007450000c4c00d60b807025000c003030444d0100d4080b450199005018004060343c00100360b0f5542c130b5102044011000300554221840c0c401c202d07014080000700c5043c0701ca4203c1a9020380603d000800035100f00d41d0b1109102e2208202c15603004000900095420091403581840204500d01c58020200c00e0340d6a40c4107401503440644002c842c0f43c105101b805241891607080380e088200183d44641c1e40f102001045c0081d80700d4920145c032454001001940c01d1115501060500c52140c1c0a28601d001c20000203009402030b014840700c500100901c095440850020303a0310444d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 486869397 1250 486868147 486868157
    0x612050d170408070609061a130b0315090f1c080723030c0f0d020408150c0a1803060e06040309090603020d110114031e0a09080306010c02010e0a120b0105030d 70
    0x107841d5183e411a038840c0b20107031000c590303418640c0c000507501d00400202182c0d80f500c11058905010401c12200c00f42d010740712209192004d0000341d5100801e88201c080c00d207980328001503640c80800ca081c820004124000713030003110382c0a51124030310030022203100510b40e1114003d40d42c24206a9142c561154980024401c2c048203003211000300000390f502c1559030004e1414081400d40c03003811a0800c40e0b19003032454012406000484082000c1601c0008401800b007903810314601fa1074041c8101c2644104000c00c01445844440c0a42184401554421010407110403841c2c00103445000641d8200c0018400850007d103841c950f010302001e880e0020001f401030b510300d554060381c0350105da001a040c0464141c20341c0a421844000d5071146031451031b0b0001ea010001d00c5031050b0500100a420050f1514850074040b807040802d81e03900010078200400020520300050b41c00c0800440c0c190b40c096401e41001c030b40d00184065401010703114500c40c04a0703988a03010192581808144200011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 486870503 1106 486869397 486869401
    0x61e11120c060603010203011a0d0612050a060b12030405091f030c030b07080403090302040504020f15091201020a0f140d060b030f060a03110607060204090612050d17 73
    0xd94204d008503d150b041034056805603181249107603141d5070218840c01000140c4e0302c000060031244002c1000307001e4518040d84e817031610310000c075010350814000d0119401c0512104a2480010000d182030904140902c4107800004250352140c800000d541c002078030704207401d080a54094002c8c03000741030640c02c1c8030b482c4041c06450801013105071010080866804090f88082e030394100d034085199121400040d60101c81c0340d195a40c0202c3e0801c00c2080102801c0090140e8141907500d10083d44400ca505800c07400703907030801c101240401c03051440e45c6e40b054116011058644c508107081890030304100b1f080712416003014414810010a03c0508881c1d007550a5000c803040f541103201504555524100c140114100c5005038404a000700c00c00c50344d601601d001d440090700812001b90f441c0b402c0c0d03502031004e0f54240c410380210158501801e119024440c140c25800650031265 = true := by decide +kernel

theorem cover : BRFrame.Cov 486690647 486870503 := by
  have h0 := BRFrame.cov_init 486690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 486690647 ≤ n) (h2 : n < 486870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
