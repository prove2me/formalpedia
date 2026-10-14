-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:51:36.073982+00:00
-- url     : https://prove2.me/submissions/05c77c95-fdb7-498b-998c-3add438b100b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 80035972 ≤ n < 80215828 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 80037222 1250 80035972 80035993
    0x902031501210504030f08090d0f05070809190329040b07030207060608060a060e010e0103030809030c0d02010b040e0c0a09050a0b09100602070501140702040c0909050f040506011502 80
    0x4a000d070954602102d42c0c028a400140c03001c0060048901ca24001d840b0103556820070790004145100c01000b0303500d44c3e009600701c84a41948400900110704680c58020746030085820100060310a006405074000d42c0a86220003511491103914203c03030089001d454480c00700101c5141c00d81c0b140001c1e1024050280c00031f000200ca81c03010640081c60f0703280050420f04140e8031282100c455400c1649154810402c005080c00c0c079000300c1019040500c14201c040d403400031041e03491041030100400b4802c1150000d0400716040090394030b0103d4600441d04202040c64019008102205e9400d000e50300340070409203905c0000030091a51280581112801f5140039030240040c034001d00078a4002e81c81300301107480d0f17075540c04401c0e0084402d004403480c058a00318001c5e01d800420381c40941440721000104695a003c00141d8a800d901642c1c041604407001030201e5040700c640e004807001c11300d4a8207000483c07085401e014402d500c43c00c101c0d4404e0340c842c41320388902030a0b1b602d4880164414010807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 80038472 1250 80037222 80037227
    0xb09130210050705010203041b050102010e1009140303010e0a0f0507080a0f18230c1c0206040f09090203061b0f0c1e060a1109010e0402070201020a0c0b07030305010902031501 77
    0x110a042094500b41c1d0030140b8544d1200e003aa4010345013a991050302e0001040d41c4000441103100410090000700f0100202c82101921036164640714080959074191040500c100b104000242445150a60b9a41e6858544094051901340c4070003031400e140c181064140304840c41880e0182c0b0860301c450b9069134881c80700c40060801c082c5a9222039844500b40c0313210b000101b0600c00500e2060307500c0001405041610f1810503106c0d111010a50710050350a540c944070100071810b600043d2141901086150001c0f0b4024801d40d0322120058001c0c0000040502d081e0380454001c520032810344019407140030051201032484034000c4003000c400c22160000708800c50050840ea003180c010794032207001030f1b0480149050824a2220143c0001041000081b802e01c100c003440c4070100303103180c109a05640003c240c100c02103259409071758006044010f580c001c202c3d51420640c04219030491540703440e4440c41c16081503104a021034180b2002140c0c00c0800d0080d00d10401101f03803105003864400004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 80039722 1250 80038472 80038489
    0x3020d15090804090b0f09150105030a0207120801030501140402030c120106050a090209011106100b1c05090309040c0305040b04060207030903050607080106090506090109180f02130602010b091302 86
    0x41620035940715259000112002c0c00b078002040b02c03000001d02c001031502440400e004401446c2d11602400003007102c040c841c450b0988070782c0d00a01c4c249869598244440c0000d102d0100e02520304c0d0030006c0301858480d4400500e9058a00c80c600034000d800c0844001c8800f16410782c3c0082d81a0004d00506055007400703810700f00c1008007040003003142569100032400c5407074280c12802d16140c001891444550700003900c1050070307026800401b10b0b483d1008040801348071034082d0400b0028000741c00d070300d0229106290302a4101a4000300714600b01a0910303903a0341e111002c490301450801c40d0411a25000744500c0784115004282d0413525a595070741c400083d80b00b201c0850601c07410420100115408104961181e00b1517241c10b003040d4103020303001c1c203140c0255012601c695400c004160075664850a1a01180c90500c01088405009540f000252400301e407041d00c600e2002c11580c0844e0040ca6030344c8221aa00d4000300006d51800713040c010f0404080b076801c2e02d4989886014401820b00032007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 80040972 1250 80039722 80039753
    0x801090e0705150901080c04030503040e1518010312091410140304030309060501050409080d0b01140c06040c080105010b1209100501120b06040c020a030e0a0906080f07050102010603020d 82
    0x1514480380d12140001c2003064580c400c181c43d1000456002e0442d600000e000350420003000c0f446080524540d10103030f03644582c0c0100e60040c95070b140807078034040b01d180640300c503140001d0421804488000703c0c01c0c510380c0c0134030003a00d290b122000b030701c2319280c000c100810030b640c1d004c01d6007035260b071440040c00700308200312200c0802c001e10304854421607184180070358003a80c0f0956002c58010018103029090f036034182c12103882280750580d9a000900326008546d1003072840b0b1800f29500c0c1250005984600c441101810140000114000c60301000300e0300301d208611590721002d00780e03143c8604600700d070b00c24001c0c50058a010040d84000f030350070070320a9511090550884880800085001060750f000b0f030b10640c20703059844414000c2018200c0f020b036003e04242c3e401c200c100301a49009544921a04000d014800041100b032810f450706a07010014200f50982844965a1407602e16a518608104c1a40e6405542c1d0042a690301c1030190030200ca4009100d01d1000086480b000d00020300100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 80042222 1250 80040972 80041001
    0x207020d02041407031d0d18030605010b1804020324030709050c1c050c09060706270302190201051c0b030105090601050a06090317092202090312040e0708042301060f0b0703080109 79
    0xa000000210540a09400381045441e45038940c43b24001003828000d040b0113092003a4014410850015066100c01c95452481d2560480c140c401d603020a00b00b050396000008460704100800c9050314191000b00031a80d10214020302d030020454a2204036002650b0303c460100d020496062280f400e5000342400c80d0294074006040c4002c1002c24031280075072604500401090044402415014490300d900445a01c02d0114007804950000f0046d10600760119080000700340340010003103655100000c20071003c2d00030001808d01094180d17031400b0034400c10b88a2000a140454038a119000c4c05040341d910440b01021400c50b407210f40441e40124a80c1600540750004c07103180480c07a141c2268101c05500c00040e99240351000349401c11114040600030440104001c03c080f143c4100c41c2c907441040c0d881c0c000280e071110b2410951940b00c55907080380c0d0703080000c11450031810640c00308041301d05a420b04880240d031400e40c1d0082d406607640180c04545000300402403449140c020800c01045175 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 80043472 1250 80042222 80042267
    0x807170d0e15011403060103021018030602070c0f08030a03020901030902100804260d020904091a06010314130b040201020f01060305011505040603020d060207020d02041407031d0d 79
    0x51034408101c6046801d14095603005802c01661001c0d000c100c240074054003000d084c0c08500341c0b000700384ea4034010b01c0001c0c05101c1c40e14030558000e10411907601c0040307024090000c1c0d20303a0390030418040e41003c042510001c0030080c000070411540c1d02d403401100e03505d801950a0001c554000d500035000320700c03060b040c5902d60781c40100517642d104c0c64038500c0890303403a17404450516060982c42c0b40c8a40c0e01240794040e0b00d5810620f41700140b416241c2d0045403000259480280c040428041d202c4140000c2c50441b620302c15589140050081e240b00340300070391b410056003031104019180c03c001926a5a0310348008200180810180c46420343e1050041c011140c85513111424142100c0440d03106480e0359554100100024400d03106d00c2000b06001c0324244001419a0001100c40c040350f00020485540010341c01c0441d120009002041ca070018010081190940d00900302e420084031a000024079108a90510031000503240342034941540060481850301c1e030055401200010f0483c4103c0c41c0c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 80044722 1250 80043472 80043487
    0x90a020604080a060605040b0105040e0a0b060301060c061404020d020405041a07020c0901140306240a0303050c0c0405040c050607020103090507082514041d01060603050105120307080717 82
    0xc00c0010030060408034000c0690201a041507012940d141e00810f02c00c0e420100c181c0030036a800300549041d101005081000e030b840d4030614100034003080b0503a03030300a040400000782d00c0e508061050b0500e40661000e008013081c2c40c0c040606581e048400a41c0b01111003c4040035041c50b034400c0b83e11510071120b1000c1030801002d031b2030442d45c00b15002001070f800341468403d54100409031a005110900d03d02c0e82c03400c401130009880e60030040807000240c00d40410302030310051030300411f019010007a20785030405880b4140242107a02c00d540c80e120612648884240604051041d103101d590002c0b83c0721090350402007003244aa0003007400341c1c1050707110344d036130340c0403c0c0c092103450001c01b07a910060070110210006241d2618100c1840440c80d003100d142003014404a003040d140d1504100e034000303240088864000b0680b1300c41300014034103618141d40440c509070540d0019040c0c40c01115441240002100a543e90348102c1d68018118681402680b001502200d00c1c0040080b4005185050050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 80045972 1250 80044722 80044729
    0x6040b0c04120807020f09041506140303120709030803010e0703060b030424020702060c0309040e0a030509010e0619030507020f0c0a1505040b0c0307120e220f0c0e030c010e18090a02 80
    0x10030b8030249c1d41d6603c0640c846041341d01c2803160a008098003c03d1200100481000030385034084d1000c83c101c400840700024600324860b40c4064040c40c0c0c40120562030b542c4490211510460844861010a280550205455501c4030503284100d62200403c3c14900301e40060800d0080024624220180c09100c0800103a40e41c0e001780034281e0551000759114020300702000140c41c181159074040c1e400c01490b602c08664044101c81601c102800c18821300b031100804201c032445440c90345a46090010208021150305400c814041c810940c00c40311403001c1c0703101654031284100301043d440119080300708020031401c012906805e86a080c080d00301907651301059000e5000c00c100c10403680000401c4010083d4040004860000504d00190089004000309030b1055241e00c0f80c594284013921800102c02007038020351100c90310542c06105240443d040603003100d8444285900c640580d600e062510751140c524a120014028606404002481c14002c4404400752240003e8000d40b80e8001c0540c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 80047222 1250 80045972 80045989
    0x803031303050405040c1d06041206150302040e0a020a0b0c100509030f07030203120a14040f052a150c0601120f05030403080301090e0601060207140f1206040b0c04120807020f 77
    0x1005447e6102014541d06002001c1c201c50403840740b20356000d00050007400c40281e003000c0c045600000c005400b080b01905549401300e141e02c029806810204a01d40480011543e50b14892080c5d4104c05190740b500c0c07030008103000d401061020382e40030800612103c0d805400040d04803d2110a4a2030310741944800d04155000744010f40160781300184580702400a40116580401850070070020080d80300701102c01c02d00007510140c680e11150007010184242880b5603101402c2004d0101011140001c1103520780c019480204d01c144405407803400000700d548100d81000002c40e0160500b42e080580f48038007804d030042c05031400b801828207100040c1c13080005001460140558507104e42c07514029a09031800c000c600c0401d504071400400089400180c1c072000c2d201000d107050851401800450035649100f68102d60200256041d0802c02d4804203606000741d0140303c400d600780d41c500c4d060030407e208a2081c460b10784c035110809801310340c03c00050024244010500380024540700d0008456a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 80048472 1250 80047222 80047241
    0x60d0f0c03061401170a030c1a0a06050a051206070f12090c15050c1c0323040203150103050a0308190f0e0f12070213020f0f0a020c010801080303130305040504 70
    0xf070381d400704500e101021008150060080300d110840e4a02d2040015854051101d00102031185604070a0100034003000e0f2603051410f40d40c0350845d140b501e080c20340f01404443c454035004a482c00404a1103080c41e50300319803040300b00c1c0001c180c1501e80725012103189254041c4e901c10800304110196482c8018090425203070b00400300c02c89142c2c208402785450007030105000c400e0000c20404e240f0240c030007060780700340b00c5204690040b94802216058028014840300001c6000280b0b10100306c84000c0103c1c1030213140240c088034403440842030506c11440e428080500390780d0007440c040380000d00c20b000301c40d8001710449104103081c801b0300031441a03841c20200b80c00d800d51120001d90040c4020012540714500c2800281144014010820150b10034601e000c9d0161480c014a070304210084e404440c0304103402c601c91503498100e0412278030b0b01e40083c40d00380d0041c050720b401204076611508015059600c41e40241d4559180c0160f803400ca9400340b00d00b103090181c24000015030303964030702ca002100e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 80049722 1250 80048472 80048483
    0x40b032203020d0305010605030403080417040503010216050d09030803010902070f0609030809061b0a030b0a12050615090408030c2a030a110105090c010f030e03030a1a0a080303060d0f0c03 83
    0x841a503d140039040d50816081101008000d10070400400d52014030913810940159181c0c404001c8140035a410f4803554000343d07010b40c000640000000401c0c07030041007142c000e0781079032a002500d00046032000721901c0080c0080754180f005000c80c200075402402500e104241d220b0344107000d1790342c5a09aa203810b409a011501c0c1d03030200301c4084070910080380d0011000504002e102d99400342440d890103260364007410582c0c0c545030010b843d2180301c2d40344003a0800c0c81c2c0b601141c0103d460030310756612003101d002034102d40b942c1c1c00351401d06100c44058000c03079103d8001c2e4151703526522207103802d4100010200300103c0003401200180c0c4c41f80142174101081c0405540e4448850f54060540c212603904410f0982c5401c040101d001d8010542c0f00c0d04c0314007480c1180e48030009290890140071001c14842d6140030000c24840b1200385a40000d1441c4c950000081041c1d104408000c1100200e11903940517400400c0010010300e00010800c09180c440c074002c01a490b00781d03d03128103225a6802c210303031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 80050972 1250 80049722 80049733
    0x1a030603101401090903050c0109080a14040f090506040207060c03020306010e0d0210110f07060507110108060310110c03030f1012030504030f0809041e05010603090206040b03220302 80
    0x14a040922094100e4210104184882d030606280311071011014842c90410f1030303079250004205446803044506504d0036000a009030a054102017555620160070400490040c1c50103104000e0f0241c1560129840e110344c01c203001d440d0400e640040c0000901003640301d80d0070080c041c00244c95204503c036010160b540181c0b6413a14000140641c0c0c2015981071107450075401c880c2c01a590b070407444880303012900c0c140b503145110038141890301c0706e003a9040c400390240345008180340d030740440075107082401441b84090380c408d804011f460104003594400d8141d00300400342c1c00c090f25640c0104884c090f62240e410310b000400010141190015641280b0380b01e982c40c24007019040403c12000a4034075003001002500d000d0744c014119100b20b100007002c0e964040000c00c140651341e0140c0d40315601c0a40284588524040c43e810041813080407201c000e498800080b07411442440b82800641d405071140703280509029516010b41c03c0140601000b8006001c0502d0a141040c2100d1406109800400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 80052222 1250 80050972 80050981
    0x302060c06070305180a0f050c060301060c031205010815060a080d0801030b01050f0102030a0806130c0c030f0905010504140301020c0d08092b0c05120408030c0705101709071a03 78
    0x10240c400140000c540102e82c1404505c000002040140d86142c0c4070000c861844003a00c3c1075814110390030304650b4030140c00304c0001120f5805c0340841c3d800a00c60b03541c1654140941c030070b00701140d10a000e03844155000d403603076180b40c80b12600d00c03c0d04220010240407861b03648001940c0b1348110035421000182e1403800400c2048221140f10780503110803070785030f1003400c00a130000795240103281c0010304109050300418030a4454201c40c500308003c00d64140900044054041e00302c1e1040041140000c2c0b9070064100c61030320030f02040d801d440c0165222490705181400e4903000340504140991315540c00c00945071400340c104803800c61040d664a0b080d165290214069050843c0703540d28003041800708102c2c410031942411804048802814500d0307021400e814003074038101c0d111810f2442c0c240000b4001c510f90200001802c0102030b520206c3d04070360b072039a040c8002000100d103008045544411106031035000d40401680c40200c002c104c1e0340040d5144d4080c00b45195075000700c0c1da000303000810722 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 80053472 1250 80052222 80052227
    0x20301080c04050114100f090905010306090b06030607090b090118080c030d03021326060103150b0102010935030103150e010504170c0109150c170108060406150302060c0607 76
    0x984c018507142034400c80c007102140200b44250303a000b03038000811103102e0441c40c000d401801080d002e0600d09600300455a12131502c1802402541d00c291648021a800a5030524000031418429125640e85824051512000103803075040b081e0031a0500129400c1c0030250800c00c0140001054404010312940007104c09060070101d09018082c20140100051001d818102110008640c1e000420011180780d901614018100c4c1d041c0e11445805903600010601c07a59104058907000d641070304204540d1300d60016402c030740d02d25038010704200080c1045d01050118400d081c01007040460040c00d901544c0b10000d4607a4002d03001120822441c00309810560307001e200ba003140c050300030002c20050410b910b452250384002c0903612108540080e20200c80340c4290883d280c01c2e030744075a102800800002c54140900518a020800184c000f601310840c00d68981e0628120781d03030200500300c04c2e15291216030180115241844241b8502940000103840300c1000f4085903199a010303203038a08181900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 80054722 1250 80053472 80053481
    0x70615060e032803090312030501090e03070f060b0f0d03121a0105220b0406030204411f02031908090d0507020f0405040c030c06030203070c021909020301080c04 71
    0x1058000d522030355240c40503200e8a9008000030f0992410b1044407511071408640711a0903400082902c49940d06d50089607405820103816138484213818821400005000b0780c3c0e80c05200005003d070707180c00d4008004200359034021841c40a0240040001c050600086002c01e002d1040840010741c070014510b18a00052040521900740c242540c0036020038040020464012175240800c0c5203800a00d40c2c0c100e4117400d03c440018800e15850507111a903411000e00290841d100f01c0511202400480400c1410000b020751078111080407000c055841c0084040c04900800c0c980307401c1f41303c8500000d503a02445941548481c06680110382d2000709009030460b501d40240c245080c84440c0b000e1001401d0301040384a60100549440758489140d400003d40f04442c03d200140c20501c1e20080c031007400380e844100000c1e6800b030200080215a601d004804034841100e101d0001000301c1e040b00010326007200c0414904462003050040c186c1c540a640d0100c4e403080c0c1c0480030561040c001003125003801c1c050f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 80055972 1250 80054722 80054747
    0x1906020d05131707260709110a08090307020307090c021c1209030201060b0703031b020c0619020c0405070504050307061103040b1e0d050a1a030706080c07061506 71
    0x1051814850700c00c181032012045400b80c050721110484180c0d41c400020004e40c07009141d1252003540b80d810b40103078103110500242c20001140030710307500400d070116540030358a000d29000c1141c81c40c14040142c100e030150400340400701c0600041101da80560307400c00c0000c010307043d00100090392160440002e49406030319070840c0f03040580454610070700c1c1d80240c02007061600301c01001c0764154072413908900400ca01c2c2c00140e000c8401144410078146c2c15401068245001100c00b01304070a840000e076074412890007002c0d0720550070010343c1e05c203541440e4041d511a946004503440892040c00242c1507800803a003240001e2004542000b9514040001760700810403801c0c0515240407001402c0e4488c403950103140c1c0f8401001071b10302c120045072200c0c1c00e040b0300b04000103612080101600c0c0701500042d0307031011040e428052103184400ca40b292201d0b030040010018400310f4604001500c07001802000c81ca55120144401c802080c0c0a000e424030002e044071070940158101580600f50300001d29 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 80057222 1250 80055972 80055977
    0x11e0605040c0f03020d090204051f0b0408061906090c18050402070f060b0f03060103030903060c0e0102190c2310020a0b0f0c040b180f010e060f090406051906020d 72
    0xb50044100c1d40c0250b503018a1400524015994100c0c0100318001340800c050004d400a10b000100403203680c1512402d4006010b8404500c0c3c0c0c80e65900d45020305000f1405840d20f580c00ca00d02040304210700090300a1991418030004c0b40c400d544413101012075004200c10300100380c074001e40d400b1145940d05110043c1400311340c11820000310752100040400359080041c2260740d240b41000481d52030365040c9001d0100201168610b41c0c403442d000340400b00314401110050700301f6806982440c014a070f8800d4111040c1d0090040e5150321480ba0403c0d8001c10b4140d81c003442081d004104141288400d440038a4a800241c0e111003107401031000d0400c81d0707070103002150401040580014002001c0750b40184010103e0030098407280025075552246503c241800c80c0000b0700c1001e510082008911100c404640c0405c00f401d4140054500303100c007082080e0b02c56004c01440c0014810200604006400600000381550320703107003c640002c810b0318281c1c07040740010b44100300082e810000c09189101c0752 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 80058472 1250 80057222 80057231
    0x7090c1817070b09040902091305210a0c0c08190b060301062409120309090506030f030a030f060902040306060315020f120a0e15091009050c01050c0f011e060504 71
    0x40c0d01940c40701c1a5003d444a030800c0043c4e60070481d51103810001c442900100740d20840d080c10490090603000440301140c2c180580641c0b03800300100700130101c86d549400c20070076280c05400041156001c1c401c0b41c0403203007203021004c00b06602c0400c2103118045000500900381d20503070340c208000615002044144240e0600300188516019007034001040c0b4200c02040f0003841c02c80106413601e0200382c100b00304003074016090b40d05165022100e2411540c500c403040019441d40d406068403030030100c13001c6426078000c004144410f0301c01e40c0304c0d0074500e17075580300082d925032621003103002c0c2e9116030300981c2d80c42c3d1030340424400d02c8002e03e000c000502d001001140350220344920316060707004051140952800003000034000d10100e800c09125071b4034940a0b03400041c4420404030303c140b8165039103003040c405e100402c5549043c078414448001d40000050140c4018040116216488042003071001d004075020003001d46070900540900340941e0b6043c0000c0400038840c94100c2d2625401184a181030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 80059722 1250 80058472 80058509
    0x91d0307030e0d0605071706010c0b06130e060f0f011205070501080403090e042003161415070c0503010b04090b04020f1f050306090a020403210207090c18 68
    0x45500c250380c5400c0c00081500008000f4842100707162000e0036540c2448100250743d0f90200c1c000f42d43d41c030290a4089a601c4a20044a1100080c03034000d000c041050085416443c1c400c2c590b000c581c590764000314802c86010798082c00d00b98180c0c1c04e02c070b030400b6090030304c44484080010540984080a444110000c0a45445036075208510a075410b005144022074140361203244554040c08000081800500340380c5044d203840303511101c0b80c1d10325400b0104101e000380340101d854a00f0000700d07010307102140e0424a003521070b04c04501c5a641c2c0010030346210100f83c01c1102c040c00005020b81401e2008619010605082d80e07d4003807020b1107a03103001c0b01130380010b03526600240c0003501901c0640007002c1d00c02c049060f0b6040100040e0710804c12194440c0003503480380c002d500c81d42095400e031600d511510030900c01d0b070103a800b00401d50f90440071595078008451903500359180e070a2044421096944400500702c507041c402c035000041c080715070511b420752461f5280005003032400801c1800c211 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 80060972 1250 80059722 80059781
    0xf01060311030703020d0219021506041a0f0f04050c04090507020d0503010b030a0e0f160e090a0b04030c0210110c010903030807030c03090b0709181109010c0206130e0109 75
    0x4001c000c4004e241d80414a2002191507906036604500c0840403520110070800c0d000e0b5071010002c014400d080300c924001600340c03c01f40504158074091001c10342010380480100030400402a0a10381c01c1003801010f0001955140074240c0106006003001d981c07a42008404425100003c1c819400e550010101403900c40d4020100e071704507050b0381c84581c0c69841d540229000703008140c090b4841071242c0880c8000c8104049407441c100d00c00f240c5105207280d80c9074a0b2003442141281c0403440c42e00004101c50218816044c0035503c24842d207007101503d98554006814002c0203210540003030321143c5000c08002d02000b1040b102030007404d102403081e16642c1c0050448000030880301c02c0540300c001100383c040c00390b044080602d90040c1c0c440704928140300018602c20403845200f1908074181c80c0032071900d03400d2140b1000c04480c2c4200303918003030b40880107480304008510101d030400c0040150100100460301521701a2811411414555140180d694141c5052001d6107411400d8102c08040b80e94 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 80062222 1250 80060972 80060977
    0xa09020a0518011107080706110f190203030d050408250f110109050301090501020325020303040816020405040501090201030b03070f0e04020a0e09030309070f06120e011d060f01060311 81
    0x1c00b58680304200014120040329242000c0c404140b0510608001243d0040e0228805040c0c0e01a036891900b0880210f082d0340e034400311008449210b80141c0c0008014407000c040310003e680c00a000c4a1810514000d200100c0700d0071201a42c01c44070100b210079a0070140c1100800c104030144034010450502d448200c55200c1d0043d0007411000902d60281e400d90081c5109001004001c0007000081c2c25414158080e602c00c0356051101185010401151740c40c7c48207110010606500450469655507140c00a40c1d001c0c0c907070300c540f070400d0b05100d200690740c0b030048134841d920070030010941c0b2000b480003500303445000b003a40c1d00c2500009070501080683d46280403c070384030030031100b1041d2214008202406039680041c5940140d11007045610040080114040c0d0914011940459a5a51001d1804040c0c0c018040020721500486c0ca5035101c54000b0b86080d00142c0c00012103034040180e100e2203103501c1e028096540c20120401c4140512610306078010300e49820240444d5081980080c00751 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 80063472 1250 80062222 80062237
    0x60a0503060d060f0e0709050906040c0b0c122d03090307060506120613050601050405040c0603050712020307020c010806060906031605130f0509181902030109050304060503060a09020a05 82
    0x1036a09001c60014002113420904204a4041c410059044801d00c4182c542485010301284103040c07002080074900001102ca104a802c0091403121074100000061994051029080d2034846e0706402c0034407200b00e50040102c4000b4001e85680b6110054600b8135850f414090141860070900c2007040340d035404001c0300c41590b840400000c460b41c0d80c80000c0c1c0b8610074501082c0703d501c1000c0401c45a0801c03840000341c0d5030f00400444095030303620410081a104203c030020200c000140301000035074066009103400101d18102040c60f5060b06204030304036042142c00b00b00680c8680580545542c0100d20b5942143c000c3d034000e8500490030012458500c405802103408007070030007042d100144109c2c00e43e0000d007102075044400a0f80e0f5004450361040c280585031290613a07030085003194034181c803100400d0404c0406030805040c50214440b102c5c0d801c800c00d0382c0554980081c0c00004d6028001800036005035100d10380c403401c10703109021000c030b202c0d0014040c003481000300004854003e0f0a0f1a040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 80064722 1250 80063472 80063479
    0x160207050f04021608030106080f07020c010f020c030a05030301151e0f1101020309010203070f0c0f0219030803010e04030e09090613150218030d0c02010e120f03070c03060b060a050306 81
    0x408010114009105005441811030001c0c4c0e6a2000c105240e001103049900b40d07034408480d034450a10380c4080c20700a4448002507441103440b05041d5004a0004c074400751240145c8030300318583c0e0302103810108001c01c1110356402c00030050145003144a0320b5858030226141c40720b4400e802101000707c8a0f404401d40040c010301c50902c52a1621844003010040c10000095480c0e0801e881458080d420035258a0089a2804202600288181000340499802c0400b0150207070080d002c1c496441c40b800d5103000740e1090800044081b0300d215000b903008040d03092410600385001d06000b03010024400e00580700703281c03040512042080010341d00d504990b200042c1d0001002c145400c0c20724410128100c070760180003060810001d100040380b100d04840c141c0541e52010800141200e2010030418000d002c2840901c1004840c2410160f284084115100701c5c3d400c080410301c4180346401115084406428007a0b052041060368090002044c60517184103052014210000e4258080240100e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 80065972 1250 80064722 80064739
    0xf1a010804060b0f03031603020607111507030b12060115050310180b120a0212010605130b0604030212030703090b040b220f1220060702120c0604120b16020705 70
    0xf182d40341100e10b10724600007021203035510720f500c2c104601c107000b03884c096001d030150000080703445001f01d81400c00450f0840140040d401a81543c1c81c0c03052001d07044408061b903a801e001856211300307898036120101d00340101010740c540b0380851540c107419518101002414020300010300500703401d18041d5507d1000060b03a0415000c0d00100038011454032990041c1c641c8028642d042d004141180418000c0e600c400100e0f00040200d07091356018801e90b500080c410a4045a00d0156071061064020082805180c1075603900015245620800f035081e446d000028643d04050f040705590740201041c0c00401c2c1802d103400000119805007007418440c02011410400c0003170758010300a00070341258a13417101d01b1900c0d000107a1201c10604803c84100700030b03d440c0b07120300641d04445000c0e880003c001d207261644039400c1c0030008010032502c800c00c1c42822002d903415504c142c05400984028107042c0c200360114100154804409014070a14401000c00d14145940c0460848255a0140d6a200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 80067222 1250 80065972 80065991
    0x3020613080d1a0f03010e100f09050604060b18130201050d090b07021c030902031009150903050d0f0504022d06030a0e251401051c0f1a01080406 64
    0x7055109064507216030610308003080c0720540780d03007021070a01482070301c00340c040503486418142218600c08400303005510007072003a00d0001d041e0300090114468900b010403107452941e540303498a001994110b4400341c4035044d0030102c0c10248a030680004000101c0c04e42ea041044c1d207034062a10400d000307810014001012420f040c5950013011a00f03600081403001442c00303000c001d48403111010070100d075800c2d03172100e00b200310300c00d004d80380c0c1c125001009131a200b0103aa040000800035040c0403208842c20301c0302d04842d5242e80c814604010b00030b403209950354000038040070488a4031086551820b03d400240700240c0c44402d540313940b618154912255064500b540b80440003504104694001000800c000f00000660003048032241e400e812181d00c20755090691000480f2041041c0300610351140812814040041140c1a00818142a8a0b0039101c2c508002904030b040241212141c0700c400d49070600100d0720170032680403d0300706410580d00300800000c049800180c00a4109030b20703843d464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 80068472 1250 80067222 80067233
    0x5010905061909050c0702060309070501021915050a090c09060501090e011202040b04150305150c1e0a050403020a06080f07020606060924190206060604030305190309140a050f0a03020613 82
    0x1b200203030380082c420ba4407450003100a6641e43d08a0040a0060181c5404080340082600d900d404165001140349121441c801c10000245070040410501c982c50b00042d4010800320000d00020b404100d4000c5461801e1400140251003582c1c0030101da4801e09004110300300c01e2424083d9041d0b81201e001c5004030b54540000c001c0c1880b511010340d0f50006100001c00c120002510050748880348a0880090790f801c00241014041c00030320b0300c0380708070a00c0001c0040442c0c8008201052282c2421400c1c140c51f50040380150b00741750060f8005c205920207014140240040d216070080043c4018085440d00b000072420b103004000502e8020b6507045864590100280c0011078000e10415845480d25808000760020745458684180503004400c08a04541040811982600e03007646801d4541800a8103450442c100010760204140d924500e00002aa1070181001c0e1200240010400c145542c00c0407418070240d144141ca095008403101d40001c0e801150059000010385243c454590042c20803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 80069722 1250 80068472 80068477
    0x2150a02130e070c0308130c03030c03050c011503021207080d05070501020c12250215071401060603021b03030103020d060213030807080a0906170a0b030a0c030605010905061909050c 80
    0x1d4190744042e10401926a80c00740810340c4442c000e0743c550b00d454907401e54000700324803510000340c0030102c0c841091020078060004051154070078504070340790185000810b8211013500660b03804401c100e035030400551804000848030184a08041c00c107503031810400d690794116012240c0c05210303020a480043c84000c0d81520100000c0000361142c101c240310080e04035a03c188100d80d52459a00c040d00312074038170114419400d03580070300015a03a0071070300003550090b008108203c40318411920f80ca00b50850a0240d28020175080c1c40260b183d507102648501003841001d0407c4d01a070051004002613910040a2400c254100900503518407086c9a407465103012a000035080000c00100c00742002070440c0240446082070781c3c0d00c1c18540d02c641e4112100346c02c0c2881c0c0c0c2000b1213810085281c0485591041c171181400030220f8603084102e6540b8001810607620554015544400400604146014160b80024105c0303202c0301004003000c26485501840c001c49031081e581c0c50000f41e01c00b110a08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 80070972 1250 80069722 80069729
    0x60913050a0602030a110322140109050c03060a020a021b03030f0f0301180207050a02040b03070f090222050307060305090a0f080304030e0405090c0f030c0402190201060602150a0213 80
    0x5072403400503241403400103903100343d8800035654604550f012060200c001644d0003000c1a44003510003400f404481c0c2c4100380904410b0744c10103110788400d90310000034407941c4009486a03001d494020180010141000402450000182e004005101e40f442e40840c0c803810049010422840b54034480c0c0c0881e241d0300444c0c00f1f02c0541c147c0028404027048000c4080c40c1260300001e482409030b4007070106075080e030268020040140d80b204509100501e0b180d0008010200b0140442d241c40360b44520840c004c0e0865844058101d50000d180801642c00040008001c14020304030441c1c94600804642da4840380c1c420b05040555440100350300f24020320083c18034a80200013141c80e202241091100f039401a6401c4000c112040281c5003d402e00f40100e0b4803400107100034110b620a0300d814094411a8400e4440d8140110041014560342d0f81c4054855500c20b0310000506a000d03000203400c548503600200306641c0200013070040c134000d81c01261b074400c41d202c2e800740e190b21081c880600903145a42 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 80072222 1250 80070972 80070983
    0x6080d140c16032f090a1103070f03060510090e0703141005120a020a05040c0c050105070305040b0c090901090b0d020d060507031107080a27030501091401050f060913 73
    0x44400c07290024030202c52081e64060745034201065005510380b00800c04003002071181c030a51004105091400c041e54a500c1411144d01141b46113040302490a19071088600b800410144a030844800e43e0600c43d04d40941000e0b10348142c03032180044003510400003813141044036141800010301c804e11a0f049050611040300088225081c00019000c6040c0b4602600e03006200d1258080303030300000041c0c03000400d0740151905060508117003c0c07202909490702c8000c04d101c80800d414001841c00d202c4c1e2441400320342d80c000b4080c141442c14648091014040c12281c84c0e085c44100c41070346d9540803036130440b20901d400007031140360703400418160300182c0d03400303507200c80300e03818210622500e900000d201d092656800c1290841711103144001d40105080607008050501003024502d015000320003040c40701c059165190a581107003901911000c1d0411521039444103034034410400c40020800c0c5550184001740000d28104819049000005220764414a0800040f445040c08800032058468000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 80073472 1250 80072222 80072233
    0x20c030c01110d0f1401060e040204030506150f01020a0305030703180b1608060105070302030403020904050115030f03020606060705100b132c0102070209190b0a230406080d140c 78
    0x203070319012070f5041441e08405607030400c420046694030605c20703a1600b801c1d030a0300c50307a141d08000301101c03d450305842094105900f00b20110100f401004a1031269080c96105071080485030140442060404442815540490894000281c1003400da9501c00e42515001407035170068076084071a41e080000160038603401405010700804002c0003c007140c2900d44a050b65925607000449031841945000f9005800602c810f00c01494500b400c039401c24090400418210025140c5030107044880d4000c8a0f8001420843c2301059010300550741d0020b4111030860500840e0746078961150350b5000c140d20301665590001c80181d03034080580b5004c5603241c00800c11140401c031101801e10805481000d00080040180301c081c4050007119007031580030740654456182c440b81000c0042180d10080c40a90f11045010007907140c0c6003c0b10000c04002001d840c15020001100320300c6142c0303c0c0c1090155017030120034046a1400074102512100d945070150b00700c038080da20140b00c0d00070f4055035000750250 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 80074722 1250 80073472 80073491
    0xe04060b040b1809090703020d060608010e031308010507090905310c0e04082703030d05040b0f0c0301060e1f0c0b070203120a0b01030e01050901020a03060b04030f06020c030c01 78
    0x158010705400c03955103d5400002c880341c4100921000d040358801c1c400c1e8420b007002d02c014180110000302d000c2c400e900100344151210b18a60031348100c6c00519007154070100c1c40740803410301c1e00c0719200209050402006241454000249082c2803405416051070f224808516030120715400c03202034408200a1415a04001c4074890344d20398202425201c0015040011600d130002c91000760280d5840382c070701e030b140210012008060300751402c1c01e50100c020140074441c02e41c4080c8010400a4001c0c003000441d49441e14102030b00b50700c00b51000c81d44c049180b0401240340c4184080724103591840c2400001100c0d140b000034106403900132224503003031628407005010b0b90802d6441015a20031148140a43e60f1150101d03034034000c1c0e40c002c82c024444400403409840c81c0d5403050640d514103140100c0c00c103446140382d9080d240300b559450800c0e94009062461150706100e043c0c05400344440c0786207413a00d1602c071080883c458000c040c0080d82e0008001c030021004100f280c101c811040001d000d100b40c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 80075972 1250 80074722 80074739
    0xc0206280e030f0304240207030b01090f0e060403090303110304090e010501050405160206010614041d09061308070b070c021008011d0108060708181e10050405030a0e04060b04 77
    0x541e00740c2900900c42c940c0529007200000c070a46040c1c0e50803490f2840351400b04000c4c0c100e81000d402180066008183c4040041a402c010342c0d03010f070400c1000450302081c040a52000c0702c00001f10740f10f16401c56424040003983c01620101101c6d098a017500e01c00300c880f84640d00b1031080b580138030003452800100e006440f5040d003050341200c60840c3c08000c150368203900c0e0943c0c1803403441000c1c01600141c00512030b80d8001d000c04001c64086a001d1400d180c0c55882d20288800c003800c44256141c0242c017080f10f801d00805c00c641c1d019050000d20044568281d468614500a41c480205101910000034a24a2141541420507600200544000b460500740941544000c0c01041c0e00c602c01a011000340960202c2d81170304a81c2c0d041c0007814641e460728000c48000e0390140280f6024034417003a0000c072036030b802c2001941e210340c040401d070300c985860500c861506c0c50701004054058201000c001c08504040240c501441c0c00342084481c0001910004008280c07035002a01c01c10004280170a80340d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 80077222 1250 80075972 80075987
    0x305040801091506090504020d06090503090d03030209150a02150a180c06030f14060f040905010c030b090a05100501050d18030507030e0306010510030e0c030601060c02090f070c020628 81
    0x210103c600b0040e4903111042c034801e4440407900a5084072402c4001030000e200d80c2d21a0070214014426281001e13400400100305a50082040c3c00103a00401d4500c000c2c5441003c1a03050545e00c40010700d49411200080d40700c20890b0490346880022500241c02d02086802c0100e8440c090044090340c200249402c00c154240ea0007004000380ca002c3c583d0805601e1480f585103850000e0503268140c5e9595070070404000d07618154690019102c600702c0000032800d00401120107501d44000c901048004140309101c00c004003e5200303282010709000b00440c00100c0700068600030b10300250344400ca0082c1202800e03c21a18940322110150620203060380080500801b500c03030355903001705000d01410560f84980a0141941c8102c29100052182d4003c1c0d00004455202c0703402e480c42c5021650001e82040026805100410721000b0880211715017824500d501c0724000581c6d03116401c0c0068010042114020028041d4000080c0b4049800c0091504607808000c06020100c1a0701c2031001000390 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 80078472 1250 80077222 80077253
    0x61d01030b03030d05011706061e0102010b0d060b030111120103060506011407061e0b0a050118050409050a02030f0312040b2e03060f0204050108040f060209090c0307120b010516030504080109 84
    0x41419403400e0f1f080c807020a15900404005015800784100c0307481d40e0302ca1080c1181e46c581550350f6144220000d4803106900c0c4c07045406032000154242c000428507017519100340008640070001c228501e40714105a1b003613810b5030303080900094156102e00040c1e60700c0700d0440d902d0f000c26801052036410003100350450000a0030343d482da9414001100008001c1e11500d1480b0740d0300030754910041c407055200d6814001c214082e108025041c5a40b000850200c4600e01c1055031143c01070700d000f0041d414100155064004140c00551520807054032403e500c15000c4d0005040b0000c04011840900030103180c0458050013040140080028204000c4540800e1004031401410011a40c410b10094801d07582118010303110f14420f80c0c0d40755110700c42d208034290300b26241c550074498920305481d40c02442d0301c61540d500300c02e96a0b082841001d494001d041c01012a100e09002d4011010f0360b2001c2a5407079030072180060783e00344200d443c0980e200c0c003845e001080c941d8a09041001444074880215124 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 80079722 1250 80078472 80078489
    0xb0d0602090f10050a14130303020a020f06030405030f0307020c10080f09030a0e010c020d0804030507030c0f05010509040507090305060c0a0810050102030405010c031106072106061d01030b03030d0501 88
    0x70540740c0c2c040c04120b011016900b00800d5040c4021341307084d802404020804015040610301d408102d8080c10103461650b0400c0e00107a010034454411400c1c2408103001800301112458110725203541c0d880d42d00d20a00c4a42c201000b0044081000c00e8005c01caa82081c14000b055400d107500f10031001440c03014126007510000380801e0118141540c0401100c01d03c0a2659401c1c120652600041d140720310744581c12038115407051100404142540050b0002d1485000548001c1d450b608142c44082b44581218020403102030040007260707080022204a102d082d5404552941c4014095410103020f82c0081d03c9400b0741810009540c0d0707800024140d602c02a2905485900d4400702001c50020a014550142c1d0007000180314960140c85040300ca181f013440e00c241c00048141d80d550074010140d6214001ca251501076154002110000c5a1040985c000402006103007203001441d0340c0e19541028803095500c41820140e9109400480110b035001c1c0407242c3c0c5031190700c0f034039008050911071840c1c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 80080972 1250 80079722 80079739
    0x50c0721150b01120e0304030f1202070801141314010f0b1008160c0c0b0d0f0e150a020904020c0303130b07090303050702150d09050703020108070906170403030b0d060209 75
    0x1030794031091040e0b098010040e0b450300303040c18134100f100d0b004201d00001c0c9a0030b440140400400900400c80050f10356106400320200c400d88404060700c0e001315500842c4959050002c2102c000070603000a0303070300140b0302c0d01d0010351881e070b4100700c54044120b920100e4035500b40617030102d518800b070300440b0280340c0942c1c00c00c41d56280305200715260302082d00d070030340c1060700709019042070b40c0b00300065002d1502482440c5c4402d95036024000695000da02d00c07901240d00e81141903002c00d02c2d8031800c030588400740f0240014a1807002e120203402d0000b4401c003407559001c02d00c035006858a40c16103401c01c44a400302c03a07a80c104000c0880c103030400d480341280d100880800203440e80c3d100d0608481226456150641414141d60801c60000d400c4600080b52403414081020001424000c00305100d00803000790000900703600004203500d200400e10005c1c004131480401100d40c1c0312140113000344800050b000a5200e51404070042c14440042c1075012074628020020310038203500400600d0000c80d048074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 80082222 1250 80080972 80081003
    0x19081006050f030c03060f090702010606021203090d120b040e06060a0b0703081617040f05010c0822050307050a0c080c01090e0601050309010b0307080d1101110406050c0721 76
    0x1a018880d203a02c8070302165040c404100441d00103400b030f540151009249a80c3c000c04103010485041044131000c0050791a001d0400030380d0f8050200404500d91303442418030f0342ca800306c21503582d851451034610810248625001c102087ca61014440240060060001070740501c0715559868040d142e051081402810010f4404810b000302c6810700e9042d20390303e1240c0e580340403c51603040b5000b020400d0060116022402000840d509403240d88907030a14070782c01015051003401c60308016209400c0c0040b0a041c03003641d84103072003414010300c07000c458603031701c44550724000382540510007000300302d8469841080200b09aa8a011080d150b107031084448400e514801141c5010080c86041c10311341c40d40c2c0208816503c1a802194007d80030000861030103001d030042440c0c84000d5000324900c0d00286524808154020344240e0100740c1c110003400000a048420001c078032480c420030092040002d650202c00c2801d01200c4002c20409d950840102460428100e490f040520100c401a82c100c0105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 80083472 1250 80082222 80082227
    0xc030b0a05010212030c090306070917070501091a07050709050106020d090609050603060d050604050616030605100302031905041a090a030c060203060109120c08060f04120302030601030219081006 86
    0x100c5405900420403107204440c05442c0e984090058410414108020350141c8c4040241c503000301866940c145403a494a41d40942c1c0f80e04150001850341c020010800080e070b8043c0b54401590406d5080b43e41c4915400704105c4140b1503000b005101d80151800000c011880794403981c121141034099456041d1314100441c1c9500d024000c281c0402c07070200703082c041800d048014650180d4040c000c101032400720703101c0c1c80c945981150202c516601c030304204524503152492028009a160806018071030034080041c4c80c0c00c0080b102c6104055000c40007540c0e080c58005400c40c100000c001c104524145814414614076502d007205400050040102c0c10280000860b070380300c075816a44643d0300c0d0060343c0d1240060340c809040c681c1080b42091001c600d241454401408261107826101449460500124140240140040c0481c0103040402000c52004500443d01e20103529005959030384150050f002030080780b4400400c8880d0940e508a4940c010a991f8050004440c000740303441d560701001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 80084722 1250 80083472 80083489
    0x61a040b04140d0605190f060501080402120307140708012702040b121b0301050609070203030c1303080307020607020f0313170a08031311040213060e0a0510030c030b 73
    0x103250380000d00700020803602d6460404207003081e500030700032441460582c880300700759403060701c0040c207151622620740703c40302c10762003820309030b10088000b40301c81854040043d01e0702ea4001c0c00640078034950000d003410980f041c000c40701d50720b501203095045022174010040e40c3e42c0f420300903c6600d42ca80180900f0186000d0a2000c0721072a06076107000f8113149078203000281402c2c58090707800420103038032400002801d0055261280da201600c032103000f0044205400d4910140000f4000ca2071030061091441e4040116540402d01c185004d0341e916030703505d640e0801c03841c9501c0500441804000d101540e50302190403401861664210303918059a21a40f83c0c50b8450300742c9500070182c07150003c111212120848c002401d82c058182c41c1c6280d0181c03144d0b401030348200c41151601e0301020010303040010040309042658400eaa0031820320400e051a401d1020340c3e07009a000340701410762156070541c0c81c030501102920010300448420300702540d018020b0090505007001080c24500202a10708244a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 80085972 1250 80084722 80084729
    0x80c03060f070c020102010e030f250206070209042603090f010c0e010c11060c0a030906030209010801050d0f0609110103060503060c190210060f030c12020919090501050a061a04 78
    0x80c600800e403140342c002e03258888461030480c1595211510421100d10074006000c83d078442e40110382d0791b0702c812000e01d1011400c101c00d600400e508003400f50050b0b01d44800f030ba40c69980c19201403420341c44d98205005110b980b003413840080320f035040da10100c802c400e6003d18014440d02c4121011422504110b034241c981014810000445c204d5525203c0c0d0320480d0800c0c0b45c540260344203442c0c40d58140201c4c0035170340064a0405198842030402c010154421001401496145021030030011042c0008005400c10300c10b4034031444c1c12030103050505c80001d5062041651203001006580460328040c0e2441c02071100c02c1d4046458a40e0009050802041240c1f10309178003500d03e07241c100c020250b025220100c503080c80851060b210740350f03400c07003032446200091b00b070712f201c10a5898038515019442d002540c2050102051240361400103844426066410205491a14200514604180300185981507014003250f00b00710034411071510f039600000540d400048080b03003d0b00d03440f41c4210588120310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 80087222 1250 80085972 80085991
    0x5070b04030609030e06090117060f04090b01151b02040b0f130504060506040b06030a0507020118030207030c05040612020d021c080306090705093d0f080709050d0b060607060c020304080c0306 84
    0x5980d00c020407a42000240d0ac00e00082c421130a12405101080880701122000c03261090f0010040c00030714103d86a00356028920300e4001140c0400c41362031402d691003440024015a02c501e040e801316035450000d03885d4000040c00040060044c6c51440e00a072000342e6041c1c6074540780c40d0100361347e424a4000e00702c0080025201c24555100c0030200d038000c001c000c3c041411950b844624800d2011001980e03480c55000c1c0c0c0c0281602d03411406e0000010840754040e910542c5415010404803c01c607201440c22501101c80c000e0300e003846d0011842031159441005480c07180e01c0b403250701700904030000e18003030403080e920b0544070b0f602c0d00010344940c0b16510200d035101c050340b0111041c00002d02c4110b00c41c80103140000e000c9250456007040103417000c5c1e94810120744580b00c3d1101c01daa01c40710342c0340d0190803031034400c401c03501d080c02150700c5e0541d6070400f0f414000741d000040d101740c80302c0c4121420203901c100d041000c100c0c4031314029166001400b50314000d001c1c403190440c0324038000980304d01408929 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 80088472 1250 80087222 80087237
    0x1050105030d141e12100e01031407051005040602010608070e06090c0403081306020c03060c2a0d020312011403070b1b070f050f040504050303010603020705070b04030609030e060901 80
    0x2c80341038584000840c00549103100802c41c0e110181d6900c011000100143d1030703501d884441000d410b641180000340b024810408800c010405150903c183c0d60440360002140c0108000d0300015604010ba41c1c1c00150b000b94410050306d4045600c42c00420458816500812451351210724407a00c850a52194654190040000c00c0c0540b03000360101d6004900a00402d00e030594030307a264000c9070006125070b000140d11400030001c403901030084268464048014003440e28000e03a011250f802120550b0002d1404a081036000c8044d4041a0021090000444000618080009542e41d00014688002252800001402c1d904401c00c00c1240e00004010304007182c14501100d01e00d40000f90001012001d504480100d6002840510f015250b0031801035140d0341030900348040d1203005196203004070315040030400410000300030f981c191912440c0c051ba03103900d103041240c5400c00039040b40e440400c0c001800400c0000c207500041c14180f19803940100240a98208421401100441c5000c500320 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 80089722 1250 80088472 80088493
    0x61a03060402130305010504030305040b090f0607030c02071a030a060501050c030d020310121401050c090a1e0806090d08010614120c0c03040b070203150709060f020a0803070f0f020105010503 84
    0xe4002d448002120101c4502103135590b01c4041c01c3d20700989040d00801e903904144003c0c0081000352a501081410080501a00c150101c0d96110b4002701b142040540ea41c0e03510485034400e00010005181c140c81150340c031402c401d14240d03544c0c02610208400d91402c1000a0154080e0054803c001448000745040504121030080a944001c108040e031070400c10011480c468030220700b541c041d0003010341d00b06510400e00a1070840e400600361040038802030240292943d103005401080e03401c0c201088400b20b5003100b401030041e04940200216000d60300400246d0007002400d09406200b0340c1d0f1740406a41c2e1741d00203690b80b1481000194407004200301060103401c031072040c41d0700481810031240c035202e00081d503241160000d81190110110003d00790056103810070842c884a40c2400c0040b50070f061200003c0e00d0f0210900c1070400344508035402c40d030b000b4001d000404103d80c10402041e924a00f102004012400307447c07440c00414900d0042480c001d105118040c10f03200c0243c01000038200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 80090972 1250 80089722 80089729
    0x40608010b0105120a060924090b0607060f020c030a0f02120901140a0c05030d0b040b04020405090105090403030e01021206091308030117031306020102031e040c23040c090603061a0306 81
    0x10041c030b00f5176a541c40349800140e01583d0b106804c9484c100c4a844c950756040080c83d00300c800803a0303104d00707030b100c1c200813001c0d40340d984034400c8544d0070341e004c40002030718024001341c14003034050100740e0000d0b4040466040800c0d60414900c5c00b00f4807056003035a00c082c0c030445400f1064000c0000040c0015105051001c921002400801c09900d060502e00d02c01040750b81c03114030b9a80310808603070075181c07540720f40c0840c0e0900380a0340380101000c0b2030960400f0b0403c801700c0d02d5803605124a91196454402080070701d4000c1d0700c004224155080203564800c03001407501c00d840000c1d15180d005e03100440c001a000408c030b4281510544d4402196891a4070300050014465100c3d0307480c2c03110740410804120320382004007001008180e281c00143e01c0e4946111080c80c001903d8200e480700303030101410040041c2000078150181c80903070707030400d00c000c0004000f40c81c40360b981c1c1c45c0741c0e403c01e10700030168420607081641802219170540d4140134040d1101148030082c0182e44801111040c1400441d04518 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 80092222 1250 80090972 80091007
    0x11401030504050a12120b0d0f0b1b0708030402010906020a051b010215010e090706020d0512150907030e0c01090f0b0a02010e1c03150506031b0c0a03030506040608010b0105 76
    0x1401002110310703e1042d51524038042c00002101070100b48007050146c8107040a015000020504a640c2260101d940e220440c3d504107120008005014140024000d25016001a91200b00c28441c1c1a141d50300381c0762184550340152005d90204041c00c000003101440000d02d0703c0140d501c1400b034404003040c4030010031450b15240c0028158000c4500c807403003103111500254000c1c032142d91052280c4c2007a451403402c0540310303080030086403c140300a030b07901074116084800d5412851020030950b601e23040003958058103c16041d61000d130020900408640c160424900010030380c0640d210340f15100015140c2d01072138800c4030303c1d48042150410003040b95070f010f04004074260001207200342c02ca80f0f004d4109800e10300201d254645028072a482ca039811712420b000318080056508180e410100010740e0380c0401000703c0c01014881d44c80c44031500c446015221001d05c0302049960b081411300d8003a000c1c1c001200c0c0c190145191078000103a002c0705004a900d030080607100d0a2070643c480034800080c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 80093472 1250 80092222 80092231
    0xd02040b040b120616020a05030a050d0617010b030709061203200105130c06050a170907030203010e01061a160308041b030809130b0906130b0a03030302030610080114010305 76
    0x20740d035802008040e2550060340d056040d0b2100503009030b1400b80b0283c1c3d1011100390b406170843d0f0101807004c00189000040300e4508a10341803254031202c1d000c2c079610207030a00343c200f124181100000d81c3c04480d8150810b80c0600030403000c0e100f40310346848552080f00c1c081c0c451f82d60314040e41122003012a009800580100e581801c0052504460301c040d182990000d4505100c9450b002072440c00380b08103049040090822442c0461400540680080450321540c41a424400d00d0a000c14041e6204010041c02941d015000b800002d0b40021101c0c0201102d204008280480da11101c40a42a560858040d174619814003040349401c1e45044880c0e40005008440340d42052001d506450000315144004502c20584181d55900f82010321030307001c19410900b44240d041244c1c4541310b50755600b510f64060400e50300d1950180101d00e0140140c0341c008421a0000382811001c024154135030019072060405a0320742d09401d01c0f842003154158024451181c4100d0722408444a0f0740c401d80040303402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 80094722 1250 80093472 80093479
    0x91b062319021e06040b0a0b03030403020907020309030a03050a030f0902030d08041a04080a031a15030c070c0807141801050d2102010903080a14041b0f030305120a09020d02040b 78
    0x7800822402c0d01031400f2018003801050b4402c03c200420003e1119142d640700c0e500b000c0900001c5240d40c0130a5513809a40402842000c80000240407a40300f042078503003d00008017202d244007c030303040190440d408a4007050019080c000c0640240b621802960136a0798041c0c0103022101c2e4034201215001001f51040302d10604100c5640c040c400401500350007075001740f4030b841e5200110400902200ca2010300300782590001800242581d49011031640c114102c1072040d9030b41d950b02080d04900303104404008108e100c1c985000b2420510004030303a02036401803544036015207185010002c40744010000903203008106401803001d401c041c81c0e10203483d81b040000722600c0350010001081d500340742041c900141e40d181c000d0010316074481405604244255403c2111001206600500d00030080000d0440800c00461030911203040000000038210424403038800c944919000381141c0c4240250040b001000001c0f40d40d440c0c0c03031700c10390482c55030081c1600f0003d811a07091001510b42810300562 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 80095972 1250 80094722 80094733
    0xa0c021201020309011503051e010f091a01080304080d030f0b090108010c030b0603090a020607050f0114100b090916020f030d020408010e0c0907080406091b06231902 73
    0x40c0c89016010400c5021000056100e00c1d20440240c210352122804503004030000d4400c00215078080350725012001500c00d03da01c0310000c11070007805002c980079100d1005191030301c1c1809102c400b502095aa2001024281c050b99866002d180d582c086d0b4004c1500c240c101c0018410001e00950241f19a1440c42c81c0225007205d071400001c1c002c4409070703c09402651540c000340c51140d454824100005402c59030b0a007141480181c4581d03032203c4440003800b815001807071030140074040140d4540e40d040341000b070110621640e144880000c0640e412111115406070120700d8507442800e840144e140603000001030740d0b5410500303401b81d480180036019806104000c4071885418002401c0301c1e000c103413015903114589400717282194152000e41c0c840c2d0f0049410041c2d01d42e0742c05181500883c1ca807a0000e200e850385d080c03440085c9030a203c003d0a0301c00c2207540084002001c80001c08441c06605d80207440e03550305600443c4021940800580a0710030010c04401c8400040c8803100825113204850 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 80097222 1250 80095972 80095997
    0x7030504050d050708100506030c010309030e0f06040e09010e060a18081c0f021909030b1503120c0109020f0405060306070503070905060301081c0203070b0105090402040f0c0c03020d230a 82
    0x904001e0080c03010f80806e9190070801c04142001c005540485200380f03420044001703540c500a181010080c4040e1107920680c08086c8581c0d00c2d801600c014003c0000c0704505420300550f464005c11151904440c14041c070400200b800c1c095114001d50034004600142d46100b451340c0326800342c1c1c0584496840070305c454a00b0426a20300c0c5c82003480c800400390b401a03a9805240e0a8041c00140c081c4860802a24003000d10005501e03041c0c060f0802460310014102541d61700c00a420080714000b141d170200740108010701c0d00311054000c43d400724004e50b100402410b0210901060342e004841a682613401440442c00003445100250303488106440e20301c19842c0c407040010015030082c2d1041d0101d6011000590105124424401c61a2034038002146840380076903c00c40002d0051081c2b40c442e10aa9000400f03544840e0030085030004030701000c000c0c002002c41d024003640302644003035005200748240303140d01a029602e0030003901d1311440700d00c070418140814107005503c243c0c95030307040140d45809071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 80098472 1250 80097222 80097239
    0x6020c030705150105190e15030a0605060f0d0201050a0e030c04060b07050105010f0f0b09031005010603020304050715021b040b031207031211160320010b03010b0607030504050d0507 80
    0xd0160034401c2003d0451001034110100c80d0b0b40040e00824410850002c1c280601c1b1103403103c140c116519215421510743c0d4001d0046800000001d85503010b025251404042103d9a481203110f0001100c0302940d00d4001b40c00e101c03a202121000a011071020000e0040c50b6000701c0056000cc080102140c01894094004c90241c51940d800329990341c8001ca01e43c81044020300500d8050420f020590f80000d1401d103001d00460210b118940c0031500000c0e078400e80740c0f001d014042070303000107020501c020b503900c28004000b5802141c0580d518007a0001c08a5880c442007003500d410300507640180021000c1c0401d5400c0140c1c8607041d91303070080d55206079910300d03202807000d150030f1300942d111035480d46228200500304050096603010010b14281c41c8030b15088c1960181e510003140c03581e058a4061b418a400e41e05a420322151642d500c070794540c41c0382500d005400120b98514250024013002d5070b03182c2407056500882c40000c2c046034042c0424402d40c01c201d20b904070491300680031104130300d59403420b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 80099722 1250 80098472 80098477
    0xb07081f0b07060506040203040f0b10080d0801140406050f011103070204050c0c071401020a1401020d09200f060409092303071109071e050408010e07080607050301030b04020d06020c03 81
    0x1041e41410007003209020701100740300f403980c0150144c0b42549103140940c0d424149008400000301442e22440210701c0f80103220401034003415078082254080e00501101506400d4244941e000d01404e4002880c01c50405004510807941d024002000c840101401540c000c8185c1c82c1c5402980700510204025a40b1401101d00680c4070b42c0010f40c0e283e4840703000c1803d200181d0003900c5642140110a01e4a9a000070a4203582d500a2540c441c130b4480049072a0181c403590441200083c108000101800843d41c41000c4003c030752940007441450a8050080b008049080b0940c0014140010083c9448036001259445d11524542c1e030f50345c1e0742428410018801c0708290055500204a440030001050380e000381c0600111001c01042c0340000c2c0c000e003c80c0055095114041c00300d910f00c01c400e401201550003421044000707001e16469081040d582d014039108241d5648235000c080746805000f4011030b8181c94001c00030103a10343d00c2e40c003804140d290042d070403100176908002000c803407c000d002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 80100972 1250 80099722 80099729
    0x40513020619110712030c020d050d1116060203041a0909010f0f0b070221160909150603080f070507090f02120a0b0d060b030a06050907210b07081f 65
    0x35191003091800c00010800c3e52040f103070340443e500c4007105100c045418646141c85030b40c54608244402001d101207000c2e00403000300104144605010f071342c0b000780c011201e151400c02101c1158034801c0b1300c40310754041c0d6240d0710031000542c00c01c1101f17018207550084c001c002034140c1d6032040d1500f4201c60204403440d07400d0303100c0e5201420700c5a052210078841c50150004140c09401d070340c1040d03004d4002504c0a485e0030148505951150540b00c2d041c03d0600c000c2c01e80c5410101d4840d80190b0303409209000e0072030804110741d181030038819900c800da40c501c01d1109903900544410300742121000b075000a42d111140a82d414807038607000141c600868003644010180c14140581c958001d588021542c10015061044150620350586010780341c1e5011300c440c1c1c1da0400310109000810310082420b00c588003201811850910082009014001504c4030131070310b0707414070b2003456072030a144150030300d424480060080e0350300742c042030216211f0714240303400140c0300020045490504801d1114120160b2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 80102222 1250 80100972 80100997
    0x91707050c060306060f031e010815011502030703050c07050603070c0210030b09061302070204020307050c0d0504030f060b0105090d1412090a0b0304150501080c0901150801050405130206 82
    0x1a92000c000040c00080481801500c58034114104107000608500460300310002c002404000500c0c0118642c01d1000d41100040f074848195848080043d1950141002e0b500b40007842c0300006454240d400034145103444580c0910b05001080d5000c5500e5440485c404a0520842001080d04d86c0d824009501039400f80d1506162020144103120402898180c1041814500100441252a100303500c540c000070440c0c50b0130380f041c400c9806a0081c010194041c0d0018030100400864580101c000d081e807940d141d04644240007200740c22600c603c5140001400585100303032180018030541c100400644d0141041130410f000030001c64801a10343d40c0070380d0329408d2020042c0c80301c94180800140032098114151030f018003200400c1c58900c0c18441d101d28141c0000000301401442c0c3d8043c090030324440340a120b1540d5410706650346008042c2e00c5031040300760500001301c000740c0690303503480188240c07103820f0241e01c0d0004220052400428aa118565841c1c2620041e500d18004150256043d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 80103472 1250 80102222 80102227
    0x2030c0c1c033902070305121201080613080304060e0f2b09180603080c070f09090201020c09072601140a03031b0c030c0801051902090a180917 63
    0x40801000c3d583d0b10080d078a510342c265070564001c0c442210b510041d91850116480e801c44022104914103245540082d0150048890804403c210303040100301d81100c141e000300990341c0310004692101e2041d1410413614029090f4031001a0090b80503641c000d0180b000004c1382c3c842944054240200c640c908020b50b00107401c80f04001070340c509101c2103200c1885c010500703a040400c024042001501030368840741c0c011682010159055000f06020f194021402501c2d080140b0780c56607140074038015000c410074422030101d16000c0500c10307a541c0301d405074014003071031400d001480300e00b803c00f40048041041080c881c2c0b40c81c484143c402243d00c0306070340d9a10072940c03600240c04486030b290340105129480034441000441ea00041c06c4112080031210610510054039280074103541039440100312224119000032607072410b40c05144a8510043c05c182581030507407a080072803040356105580a851640c040c408282007a84007070030a90405400501034038613413109400e07a80f075102c100e107105000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 80104722 1250 80103472 80103523
    0x902040207150f0501050d02090a0e0703080a0305060102010519020a020c1906140309070b0d0609060f0608101a090102030d050a051006031109060a0507021005041a0403050c010302030c0c 82
    0x54420383c112100300540c100055414000090707030152503c0800b0344113000d0840407941c480010b5001c0302d020310f40801124101c9a4a2030f04040c2c0d9006013032083c01080c0f030080000c11a5006006407482201240c102040344405110303e18002e4020101610440c0310740c0c140c60015448404c20303951003522444c8200461850203000511841c50155a10000c010500500255202c0003400c00243c850305003c02c1e44034400c0022800084c04650b01c00c01e482810030000240c0300c40415444000c0d280565507103081a42c500840134200392143c0b15102c2e406800d581041598050f800c0a4078503000c0c1441a04e240c0a010110081a60016902c0340704503030742c0b9424441c186c1801d5683c0b500800e110f05017404503900c0420000c0703140c01451881401420002001e4490b60712580807100705c5903004002c00542044091300070183d8105014034a0403003035100035001c4003200c0d201910100d0fa03004006000b80c039501c40044000e50005026a041c0000602408202900911246001c2c250b0103601c000600d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 80105972 1250 80104722 80104763
    0x61d1e0709090f02120f0d050409050a0912081b03010f0602060906070503010303030b1c0606050a0602030f0906070206070c1211010903020d0b04021203160c0605090904030c060902040207 82
    0x3110707400384214614000c4104000b0701120a6440e00301e8040340c0003030441c40445034071810540d88a4862945005a080600003550080080e00075036a0041040003581d84101c0188102c5000d040003800350b9034408013080c2d0f004e2051400c0d0b85e014601d41d6181c03000b85001c10703400307101c0d400a8003d030505030312484c024001183e04001a65021000703900816880c00d08103c05891803106000c09005c0644135102c40d40e5544031a1240400991701c142d0782c6860502509164004103068010140b10b6041040b0000b5954800025034a17407000c8000654030340307194041002269401454100e8110344140100b9021a01d4840d40340c0c000c0001d0440c00442ca40145440c07420103a004191605215031114280050303192400c2040c004c0760f1090380b6207a9500c8070f00010f66441200794424401e803000003071071803010004600c6044160311458006402980390001511030340903c030001d03500205642c00050220388601d0340840102d0080c04001207450a030740225050740e00c424410340b1450100f0901441d00305 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 80107222 1250 80105972 80105983
    0x80109051b010c0f030c080307110f03030705120907050607030c0b0a05011818081317060103080324060f090108060f130f060806040b0106090602030f0304061d1e 71
    0xd4006645603100c8081100103400000c0003c40500007031190018a001c250144c0c10101c0320981010040741c403858070490060135145402d010002500071520702d0300300f1030030000030780740140d00b5034842d981041001905010031000c001d11441c824443d90a00181343d4031280020481c0a000342c0d120002000b46007000060b40381c0180454007142e21b020010001d1007840d102948a0141902d4007040586186407100090042c500d400f4103140000590054000500d250703a100300c51111101401140d40c50f02c42c1c6403100f0b42444050503600e0208001114200c042849090012600600d80096550361300032490541100240e0300c03e10000282490a56801050080c0e01410444030404440c800350042a00d0071012540c0d0001c4075102d003814007441c05d440d0420005000070000700e801c0b40ca030a040c110380244082c030564010400e00719020450a10100c101c880c48807050510520355140d582c4c8034401001605412101e4006081100e1680c0b201480003000b030b5201803c521051034000042f150520 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 80108472 1250 80107222 80107243
    0x30302010c08090303090d08451902040e031b01020318010903020a0605060604170c0108100e01030b0606040b16060b01020a020a090b030f1515041806051009020408010905 75
    0x1a4800d02c2000040c410024107007110000b14640418a030301c031003908110148020022259940b03000c611602740c040280715620101d82c912030481c0d4140303001c81d0416100c681d20980c01c140d146c0503803607110242c280381e00565a0360110320116032604400f80c0300d58138503500c090203030b10107a500081401201200742c2c6d244500c854401380200140303641550082c0d0b45101c0d503200180130b103869000207807a9a499a0503500102951442e503040c00d400e0b54040c50715000100d0381325003c6108078000c103c1c1d0300032108940c810f035414a100c010540e401e50f02d482640e808001d05055010b007042102040030113500018011601680c4d004d90050302c142c2c500a0140c91030714015030304550081811402603580e1f04070000031180020340000b552449500400d00300300c4003404080c00c51041059840050b1520903295102e10010080f4960450b00d440c02c010980c1d41d4104104240c0c80ea0381d02c03440210340140d01843e000b00083c8081420b8a42c1c0781262001d0342c0142e8001242d81c0d646400c81c0701408018800790b03031070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 80109722 1250 80108472 80108491
    0x10608011a07060f020913090b070c2607060e0c0102060c0c0304050112020904060305030a0306050402190305070c1b06120509070b0d0204031b050f0f10030e0115030302010c08 77
    0x4003008120600322030003804000b40440f5144c89802103240c00315030440c2e202d0000940300b85440008800d660307000d4100340d10100c1d0420043c1000400e041e00c1210130404050380140d641545c2c00406001d1b8080408100290303480721020400d003000142144070703540c4410580006400245003020000e41403050080c030071200b8880404c2000c07480380000c02201c0c1038403401d0800d56914071103006100000d001c1c07401001d8220b8035001c00442405070000240442040039941403066a41716401d02003030b4010a9582d142d601208030244008234041c1d000076500616516140701e0009250300e0704800450a1824051101c0340e40d0340600002d50322900d8030100d0031008009101034241400902e41d82c0c4070314480e0758214580450b10344905001e54049a00550b00085040600008444814541c806502c61b2a210307103410180300000c0c2c01e001c42140c101410003000410b100b0307440c80094000d446004904005556607550fa41c3e0b028070880700340d40c051402680001400d4501c0030b0040d004c0c4002034400d860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 80110972 1250 80109722 80109749
    0x50d02010b0a150210020f0316050a0507060b011b11120307020307050f0a03080a080601030605031501051c051516090e011e090207030e030610060c0f11090f01060801 73
    0x700380e240d01c0c80c0101110b010500d401c2403180c440e03804038140750300c6642e0108114000180c4c0000d0144500103107000d40c142114954a9104144e000e5840388594032640c00410307020711240c00420032369405001a0841030614080d00341c0c500c0b00401d81c200325020304580d20070346003198200509004801890030000752004502c4c080745900081d0b502c130840d204692103a090750311400a141c44100d400c00003558002041500d40e00442e00c060710304a0211a4540040c1c40c02400080701d1600040d410340ca41400e0b1103d644507400c040902c01c1d14a0348100009011040031400700001c6d5040101c0702040342420158070080c2080403c440c004141c0c19020030404c84000d030103100c60880075280d2030440d02c00d002016406d034113050f443c110018041d03100d00c002e9880820740100785604255a058404422019030745240d407480052005442d090091100041c1d4030000100000c8551288001482c0600600000d0b0400c110004100ea4030803909010114080001080302c96080040140504107101d0401c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 80112222 1250 80110972 80110991
    0x60f2a05010f020c070909050114073b0d02060f160204051003030504060c030309060903120c0503070905041a092703070305030f040c0b0a03091e0302031b01140f04050d0201 76
    0x13507444401c2e0051b00311142d0b80c3e420321b5081040c250f000e00d43d004490010b400092903d290050680d1007500c1c2c603034241680c160003a2000c114600c1d2019122600d60410307990440080c0b05220401c000380e40c08980040042011408003a000009420111342554942420003280c1c4140401d540b006446030140b04140041400040d4201098a0603540d0318030706011074a079a030808502034420f0110280c4041e14140f110014943e000140c02001514a01c1c00c3c451031050900445143c4001c8070001e00017440309009100c14038242e04121018000c0100205001c0e4107240081d00c5034100740e0780303070341140010003028800036052102240b0341030710702000c0c43c1840b4144d1001740030341c800200900b500c41d0341d12001900b08140341a00c0e40c0038184000c4403d44401500d00040c0090100031000c1e51250002d0441d4175a0b214144000500c803035156000d94148035488002d1950320005940c44900795481d01864944218a04482803052040d0440540c107401c0c14146030f400c02315002c1d002021a4180300262 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 80113472 1250 80112222 80112247
    0x606020a020d0602070602040b12060f0f06130807090507020d0203032403011d0318030705030307020607080f031302040c080f01170309091005090c030907060f2a05010f02 75
    0x540d0429010359840e103054032149003940091041c0a0020400f5102140c00f0411000c6100981705004c9100c5c4048040d8492004001c09400000381040c1c0c400d074000083c50007414003030080c1410140141d80d10134407030380300c140484c2000c0040e08100445581c410410958a50402140c2c02c4040d040c0003442c51410804440c41c07600c0c0481261100f0300100f0405605ca50703c096102c3c5904034400c4548520041100f44038540b640d11140c0d050b54540f02000c401302c0030317280118807601195402001140303007681c80c0c1c1c04c0c070005802c4040d0544080e10b00707001350604c0c030b0020b0000310301c100341868650050503c03910400046078491040b00d010000700e4001c202c10340c02202d0300d007419a01203130400074087c1c1240c4ad209286111340d4a4041d00b0104910900070203240b04141c807015944c00311002d0220303a6072070044c0900c50000b10b403201d000380d01a403801c0201d180580c0858000030b00038508004019880b0141c07460740e20714140c0e500e041e028000301c0d26051102c02c0c420790301e1000910303e080d0f01c1c3c41c6884404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 80114722 1250 80113472 80113483
    0x9071e0605090604090e070302010e0a0501232208010c031a1504081213060806030d081317030a0b04020405030c041109040e0d03060501080610030c0e03030f0408010f060602 76
    0x251001d120000409594994038407050ba40101220401444100644540291035000c2840120b012038070980314110b0918001034100d058801c1030392150340c401c2810a661120001c002d034088607a030004c0100207d08245040161090b860400810860030314007200282140e0400f0114400c0602c0c2c200e0398014154040301c1e400e6107400880320b440b070340550340c000461140b055a0142ca003500c02c140810030101003075405403035010020b0a00001456030f40c1d400303840d0310400b180c010b0380c142c0103152074404582c018001241c1052446000590b04403440d81c95103001134008228406141c40030082146044450140d54503c0e8429181542054900004240d4801100c05041c0c4030ba911101c091040f5070801d400c1d00c1c84a003005000384a07602000c3d8495840d90700e101035000000b030034030f100480d42d94059900d40e8094603001d001418a0a02404104c0040030b20303088000070000d0b0080014101d6038200080c0c280741d4090060340313545a10300104142111010304001e0340f4907041080400126802040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 80115972 1250 80114722 80114729
    0x60f0f250e040f05070309020a08030403080403150b030303070309140a051c0e0901060908150f06090a18031d0d080a1b060c02060601260a1a0d05010509071e 69
    0x28408080340c10000028090801020401d0003d8505002c01100075410381016411600940fa42d542c2c4a0b2640401070316885903000c05007801d00304020070070000d2008801c4103c80003000c680028504000303000a406c69000740c5120002a4480907800c0500c0704403140100001020300c000c0c08508426a5a03d0b2910000d48408085500962030b4414a030f00500e00c491045200601100c55982c40b488081c26070804c13800340303840c0b40c0700e4900c03503000702d031101c4c0001400350007814490410f507070304c06003000340400f402018200d465440d02140701c0c1c190310f60400c04a441e8403d4540800d2402c00b0301c0e110b40da021003843d02034405d00c4a02c0000000c6540902256507600852810300c180c121038000d000240c103c001e000800080c9081301565202d5404a00c80d40911002d983c2e40b004000f00c1a0740f0740510324460000c5516149000101c1d241e004c455004000400b40b048550301d022428100250720491f01d0307101510140d44600c00c0180e141d405000c86001307400a0700b0740d10950791054031600341c900711500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 80117222 1250 80115972 80115977
    0x601170307020a080604030f0207120210030605030312040212010c1b060b0a0807081c020c040506012106090605010203030f0703090f020d05010b03010509030906070f06060305060f0f25 81
    0x689004120050044030140c1d90081c0103882c07003c0ea140341c03042d030391802140c2c203600241c00c1c004142070b02c81c408980c00c4122140c850300344030044866001c0004604403a034240701896910400060395480500103045000304012a2403030a00d828018400c00300760250466001380d01d8080c1411490340c026045840d0800f000c03000c05a081442c0c80c043c4014050007240540c0908100c1000412000005410f1306540c907800507030301054100c03850220001d1002e1b0b0b183d80560060113461407581415403045d42c1c055014540018410700d812201a05036011000c0c1c94a1161200010300650340c0d1409604010003003880194a90b00e801d80d0760340c00041d405810582015111500340301408141580d6208040d001054617800410518045000b42000a5402c1c0a5402c2c03800180140101005031644480302401441c80c250441e40c0310400d00c581c140c8210f4a40d40c0e40c41c1b010020600c20001c0520900640c00440c80a0030840214415400018010350000007110400d11170b0383e802c030740102d6404400c4d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 80118472 1250 80117222 80117249
    0x30907090905160b0307020d0e0a030201050a020106180608061303091a0c03031003021e0306070f020f030c06011a0306060403080d0e0114060a0b03010803180604030501020309031308030901020601 86
    0xd240c440d061240310080c06070700165010303001c100a400d5000460280b61b5030707000c445203101c1c5400280d404611108100f50300a034044420405035001d00001c1100000510000503240e841e86c43c4c0c40010410103407840c61030780d902c8406010410080100039001180100f82c10b80600303855800400c20300013070003102c40c1d400781000810318440050064400c01f200c0e50068a0b102c1c0307010030000c06900c610b403109a118080c1d440001040c030800751515882000d01401500e85940ca134002070360090031081e130000840c4200602d5185a1009001a00170741c4a5180544515494204012040e240c0c50344403400e040400c10520106070f032240112000c40703500461141d103600c03d03000000010031002409d10301d00d5007040d40000584140600031481110102e881d140c0b5552503204100f0307140800d0041c1040359100704000341d0f28200e10301100e03a40620062640f46817580b070703a0b50903003a60420783d19802654408100704011440054180015180100c021070030700560b4030000303503910b2041c898085440c41c007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 80119722 1250 80118472 80118491
    0x1020301080303130507080601030609020f060306011d03071d0103030f090b12071403180105130f021507050304090b0307090c050901200f0714010504060804030509190602030703031103090709 84
    0xa001406c01000283c040d6040c541e50303420014007030603100804070702c00d000e0002106c455251840c2a20300405040e0740e0404000074030a41c4a41c508041190b05505101b4140c000034030041101821100e1443d8000742404c075455446e010701040f8000c0300c5403080c0701545000f0302030424803400f80c4054440e206045115a15181020f55000004880c9030011300d10020070450080321a1500b01030200b0b041008100d2540c3d004082d1440000d081030040c802000c8014a0000d40380c00c502200841c20400100361400c04c4aaa5403881c0d07034003581c8160441504d80b000050706241c1409900c0050500c01e03010702c000012504002d05501c00c50003030605010080f00003259140300140c0543c04c40196a04944248550308066569103005200b2410400308140d4650400d510910944003224025210001d894481d540c09440750381041042c5070308402251031089064240400210040900340c014550740c0c007803405d00409554036021040b07903900041007030220ac0e201c001107050894032040c1300024004103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 80120972 1250 80119722 80119733
    0x40f030306090507020a02010e040c0905090c090301090309030b0f06010807110c060d0902130b0d03050a020a02060a030e0c041104061107050301142409040602070303021210050a080102030108030313 87
    0x903800c981c1c0b07030078074107001c01016035000951040c981d4001d03295040000508410041902c48000d40704001804803941003000703090040ca4241c01850b003ca00314102010340e40403a0844140f14001c1d00002c211041c2001400448107900d904400c688401054502e0580000b1344510b401a0141d82008400300c60306c1d80c486410310052480c0c4500034903843e03540310810303071601c090701c3c40c02c006a04c0f8001100f1007650910b0b50b07104103a0b6000c005411288288015141a58541c01100e0307000d055000f2181040c00590b9000010b24442200e40c90000e50003040c0400c0a18100c007242e5070f9402140360011030740028201005940880d800c03403908900414041280505041c0140d01c020307055030a008040024100f42540d940c444d1041d10300605035512a0980e00702c815505584094012412101180100e07400b03800500581c0d000341805481c1600300554103003a8035048542c610b0881200314148180d00c0d188032080000c048800081d411541010f41d02c686030b1001800940c2d09100c0341d102c407406c011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 80122222 1250 80120972 80120981
    0xf0201021903030e0f240c0403060501090c08010b090a0311060d0614030f1c0c020103091a0405010c03060303020c0f04060305030f1c02210901150611010509010501050603040f0303 79
    0x10518400c01d07296010528015000c1c3c02120316002d00d5021324840103800c0c0f000000c1203101145202c4046070322803626503080322206009420345940041c100408030206955000e450300a01c0ca5101c0000c0b10350056100610020040e0080c420443d41004260840da95a1007240d00f540c0c0c203c540c00340c00f96640c00015104cc07041050301c08100b0b08110780001c0074141200d80d020361242c240e065a52141d144800f20303484200d00c4001a091903220b203c400480c0b407049031401c170203a20605000400c41683d0f218081102200c201001118100c00200030411400380103451700022030341010700c405800c541c0c001c0d40b18041c0c80300213806011500e800341c40541d985e40180b0020341d00803060741d90b42e0100c0318840546911140707419244107240303001d40012201c40c0c8200d440442078002407044803e0303107440c1c15203111409840e9210701e40d2243e4140489041100c4004014082500c59503001c201401d48542514001040000f05914040040005496640c116070748540c3c40b07801d44500748003914040d0000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 80123472 1250 80122222 80122243
    0x81b0c0d0f120203040513050603070302062701081006050c0a0b01170d1416030e0301020f0405090c13051002030c1617070f09020c0a05010207080316020304120f020102 74
    0x100c900852024090407801c0782404074001e034110501009550400d0742c1e40c0c411446680e4025080c2ca001202c55131240d8030860300800010240c030300059580d0001086a00522040c0d13180d02c8102019101c031440c0e000060107610420b0900400c9407822214a0510442c1441840223010f000200c11076590303424084810019030007010020312b5611500241003204030141c2d440c02c940700d01789281c23680c039006a820280990b040101d5034031f8910302d02e4001c0e1166102520440600c400e45484c3caa980d80c0070300181c040a9184d1610740c6c5c42d1407402e420840c0c0f001c07010f482e0001030b441c05c214040d80a00e0082d43c420584c0c8056440c5d4088070038a00040703185100d140001055402901c5422609011603c400c0c070840e0350f01114500764440c50500b068070341e400c500c55040b00707004c2e801080041400940150080f45020ba0644c0c00c42c0d0010784a0340d09983c044981111513800c0041000101ca0b441c003800c2500d0822440194207150811076007144443c040c02010741008281d8611908580c801c01509400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 80124722 1250 80123472 80123479
    0xa050717071436090c340606060503060418080301120305071a0402010806010201020910200111070c0609030305090123190305162c0910090f09081b0c 66
    0x8070540222400c60402240b0442c030b1180e40c6010110b120b600044040c6e4207203990742e40d00004200c1826420785001c465111440030141410229540891590300c01c0000070310061700c1c2c66a41c0d2810000300710448140c4c10402c9c81014a00d141c20010544020070781c0d0640311428032055070b050082c18180c9240c01100401803024114041801039011151101c0740640d03c01c0c3c039801c0c26500c402c40160b090740140e4082c241c02101e88000216000d215401080c4c201d92408118529402c0c00110282034500c4040c08000c0402c0001c4e00d0740410043d10490b8009007140d26040000b40d0030359500514512400c420340d4100036289014100c0d9a600c01c0c403010441c0030701020309603100e82140840c00090400c42400703020a19180010b2500048404c40092198046e030f621010400c002c0014074a42031421000480111011074400d4580c69030040d0700e0089403d00a0040014581180002680d00d0b400200c0074041c14982490300080500080d00c003c00003030b0a101d1030380f032440c1c0b120034503100f000358a582c2d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 80125972 1250 80124722 80124787
    0x150b0607020d060903090504020301030503031605160f05060a0c0206010e0a140703050601090b0f0a110a0c0305031209071a180310020c100504031407030e090a0507170714 75
    0xf00070301a03001074810f0f4441d8841d44510f0340d945081100301c2c0400d110103003a5410402c0051700178500c0c4d01c80512840720500700f42d03041c1003403035542d8107509a20050868011025184840134000104021540402080b400f40030356500a031000f51140010321130041c40400c8180854820350f6075821a1450b0149201e1008991801020090142c5004d0398205d000c5100020301290f4614410100c820110702103403d02c1c070307000c80000100c4130910711461028080c00360f50050790000b004d83c03801e040150301070801580c039030074000c4c5030325120070010300b94205a520001040003504640c0d625402046000b459807505d23500c08040f02a549002c0b400c0c0b07160b050095000500d50785420341e0113030510001803011100a41d00c080b24040440e03100341c2c6c1c06004680139220700c103c003c0d070150050058510a1400c405c00c584c02602007a05848162000b40c1e03140d03101d60030070000c03e6001c64060880018000401e107a4181a0809401187c2082025580c0c803070004842c015038850182800c4480304486040d003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 80127222 1250 80125972 80125999
    0x40b030412030b010c080a1d040e01060302011107060804080721031a09100e0603030d140601080906060d151806020a0906020706090918050a1103010b0607150b060702 73
    0x29054840311030040120703251201002c03180d44110b04051401b41c0c0881070b5841c000740e61105680c9098420800a043c5807107003031112464440d405916503c0354120b0006c0f03002825840094124200d1400b0b080440c2e0203018108036059008007183d400507003201001c1e80d1a961400c14100d031908002d00c10a081ca004c00c428031500340d00d07500c010800d40d0350300020103030070140c24200400684240c03040d03a660781072030409000c84071150310400c1e00401c0080071a49000d12108000050b1807440e4031114400d80003104001c860b507007182c1915400500c15001e0641c6281000c0000c050302504a005011003540d01282e42a001d0a544940c0d4071100c9a40756000d404507a10f820030181d800350b281c010001d20764010004416000182ca0070070344050b81c81c1d15114900f0840900028140d84014024840d80c00d40c2c00d1022a009104800b090307170160440c00f0722620248240750079a0071404405004100820101c07001c14180c8040010400d8241404692521503000080e4180034624010394800d4000340c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 80128472 1250 80127222 80127233
    0x307050d09061403060909011b03090c12050a06050406060503120705010606080c0d020d020904060b07060b100c0308040f0b0c0403170403020a150314011710020703170c040b0304 78
    0x41a02140c1ea41c07403101038407a5022504201d805841d040307001000e2011803400e140a42c606940300446000016020322142502a0005824005a004030350344201413828844c01c1000d1001400c001c1d0315101c0c4003140d654030725642d04000c0030003500c842d9892011071708104240c0c2002000303084c002e08441080c044400b80111503070205004036103541c07811034009000d0380600c0f13900d449080003c0100703061039143c0c1da40310040d40c040d401c0d0b405100c1d42007240104941d9a48030300c0380908084406551100c1d6245842000c84102c10801c0b413291151203035005085d58031038050548030740d16103441295038840d45040d5484503034007500140214413200812a5a041c0308000c0c20440e401134070403580401707103000e148490384141e01010b50004c89403039003882100450341016007004403d25001441050880a4001041081c0c101180c0d4500d0503803003100c010800c111031543d5240b0700c142145000303030580d0054401400000404080528a400128689072207401d5500030008140169624681407421 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 80129722 1250 80128472 80128483
    0x20c010c0201141302010c060905032803090503031b070b09010506011d09062704060b03070f0e040b060a15050301051e0a060e03010b0310201309090311030705 70
    0x500010b40c42c0410440c1c80401c04081c1c10b004d9480782004540c8500726400458080b00903600541c0d1582e25500d02d407000134001c000512810000442c018681c0304041400301d41c1030000c504000405092400c1034020070300103c112508001d00f080d41c61000d140c0e003207480203d4000d088018143c50315400c100035620a0642007188525030984c0d80e01c07240e50030820303464203504100c0305003504902903400042c0c0070f080080d1044100c5504002111505150456202c10840c00700e500702d40254884001c1c600c0390800b00301c1440600319640b0b280a005007002603240c0710080082003c0c2c113001d4900e0202e11540c42e01403001000d01401c82149040b0551000041c205900c28031509000b05031010b83c0072288809004c40e030141d80307002003400c030040b440d054007201d909441e0699507030716558404040c0c41d540e8040050303100e030311050f400c003040341c805801000368180d0241020408601c0104a5407915581110601d411b4a403040340000d40501281000c035100c65141317004403014400001c1d03e000340100000e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 80130972 1250 80129722 80129741
    0x3080c090109051c0303061a2205030105100801050703060803090d0f3f050d1a032b0c021320030103081201171b03030d021306080105030703020904150f020c01 70
    0x2400d006142d52411031980603003828950071668001407000d00110a42c02278000c140c25409646054240d40341c000003400c5450907258000d0465540004106100082c000c2580c8141581410002d5500d000d04c116103134441c800740940305d040000c4402c010090500528a4200e40094001444d002070a8400d90840049001c4041c0c0c40891006081c01c40b00e04144040304082c1651002d0403e682c2c40c102c9805080b0518000c0007003440d44001c281d0326103007089035115041c0c106804060408594064031031880324107944404000d0250001405030f200d01d2004402e24218441c0014046c030b0350403208081000036602c0d1109900300000010500042901520b0820001c07148140b09903a603d642001031460f184001042d80c00c603a0602d030500070702c0411030b520890090f054034030741506849484101d03480b408640150741107d00c1d080c03000a45c8064440c0c0900402e80050180d1800e68001490600b030081000746a8008141020300709200c6400200c0c0f0b803c022a010344d1070f030800700c9200d4041c001156 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 80132222 1250 80130972 80130977
    0x21e070b030c071b0b07030507020a08030a0210060e070c030c03020c0402030109090201030c08040b010b0702061b07230102030d0507020a120206061504140405090f030403050717060403080c090109051c03 89
    0x104124440e81091112400b00c0b170100710070742d2500c0c29a41d416103040d08101c5069070b00400c03107800051089010f100500a652941d07000d022102030604260040b2505034004c00c140c3c1c401c1500b040381c0c481e00441009041a00f605041169410707501c0d04926103141960a07a8001c1e0021000007560f0080f81c204c940744074403d0720b0030b02c040100e03501c00700e0b0001001c42d009444000030790010000019240c1c0100a220300280040340f8240150000102c02001c1100ea00b10a07070207820f08000040c05415101c158090f410703200c00450f034048000039a02c2c0507010f5079111145d40e40d00807401b018000c0000c00c0265070301c130b403600303950342407801d006901d030102203806a01603040c07201a103c82c03a8912048505440b0f004800107280c82084007408018200203201d180c035446201818000040d080010b00000d6110f040107041c3c0c1c50070160b5043c4200590100c4c1d0540b94400c8080c030000036003194006600c8417414030901e03110a100c03401220300d040f1543c0001e03000340b0b80609559a8400d10040e5024031400394 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 80133472 1250 80132222 80132243
    0xb3111070212030306130c05070503040311040e15150a1701050a1503030c06020304051509060115051911070f0b0c010b01090b0406121112040b06040c021e070b030c07 73
    0x44020b40c2d100c1c44202c038241e0384490400903411040c1c2c030607800203020034414600541480542d64403e0b00d5544a03810035981c509140304001550b2500303002c5c0603241c4100e013002e0701e2048140c1d6900c860740c84020749444201c91000c4080c200d81d40303c500e041001051503040007085681d0745100070b0b0007005c041e00d50341d18503070400c2c8100b04059050114402220b5265a6182602816840300340003500080d0040f62503004421114800b0044062100e0068a106010f01055494100051403140342d041181e004d1103401d1201078002460a50810200115800c0102002c0140d8411500304210358011008d0503e09003008204041030501601102c020400204401006240151094109485035200f42c0744c0030070042c0100e038401c528484d0032020580010416080d0301c1c8007020303c0c1e005101000c20280d500350811003801543d1020640190780ae4408000c2c40c18120402501c41000e04240b0300400e08240400900b41d1703003004510001c0821441d034540300d082c14a101011a1b01c03902c1c0640e03503038a00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 80134722 1250 80133472 80133499
    0xa02031b0f09190503101d071d010e0c0301120303060b0a0e090f0f04080f0d0c0309020102061e0a020a020c030610030b0f0c09040b0609031606030e010b31110702 71
    0x14801d00000c0d903000500519200c41b403075002c0c2000e032441e100721000c3c00c0701c070001c0e101002c5010042031001e048101518007610014040301401000140d10041a40501100b40400000000b0489041d5011295845041c3c0b03070038182600079003540c0d40080a0203100040b80c25102d684200032294a14017100d80c6000f42d20b80180d9001000c60980c1c041400302c440d01c011400181d40c0c000100000c403034000d25542090480300074a81200c01103489040070036112140541150703418400c15030300c25050304030306441c520103105030b07085000010031301114150700154001c1c80714000c1040c00d1142000038100c2e40c1c58a000c810000314000144002c0b202c1c2d002082c0800c030080c6589032018455640002c43e00d00303203008002080003800b950310b486608404204000c1441e6107040c040d1003100380c08040800750184c03402800400b00d41c041800c021159241c03a44101d401c3e0f8541c1c040000c010315141d2054071000b2090a00d05151400f0303e82d01c18130a02d4414a00312040e10304010700380590003141d803020001d42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 80135972 1250 80134722 80134759
    0x90a090c0c0c090e0705040504110103052a12071e0807020717070807080a210e04020c0105060909010c1707030612050607030c080402032d030406090305070f0e0a02031b0f09 76
    0x52703400825015a00151340c81e10751207a070007542d00c1101002c0703140d840039501c0781580391103440d501000040c41c80050310368400f1000210240d0400d849140000203146041406612071800900380d00030403503541c0208440313510801c5003401911400e035911003c905c07080f04644c0e85a8103840307840b607a40210040080c41d50008a58078141f640c1160f07460b54117a04c0301d450702c40f80c0c40f51102008184910301810f81c0302c80d221032000d400300703e080e4800051217042600c200101410010404040c5a0500481c448015841502200309009810910300191120a4141c2c0079041d280c002c403103074000d602e0440c41804400501d060040040fa01d003001716100d031000407240f003582242d0281d01540074443d0b155140052181804204144031240820310725103a2210341188d00039840540000e003400014030a00c1014410782c4018600d40d0307820b090b03c5243c1305100170f2070301000381500800c0d54088001032456030b1487d040140c3d07202c81e0700c0403555081d58211402083c0c000740c074624000c2e00341c215203201002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 80137222 1250 80135972 80135981
    0x21b010b03160902030a140702010b0108010b0910030506040207050109050a0c140a0509040f060c03060e01080307030e1215100303030b030a050606040e070302150a080705090a090c0c0c090e070504 86
    0x70003152800c0b00360f0030f2405280c007070741c8080e00c01c045140e40c1c1c9405181400d070f6a485540941c40c0340c0d0001c00c2908056000514445040c0c106c002c1c0d0301ca0810a45142e070340e0700345007100010154100130401d644c50200003402400b442030080d1555082c11596010040f010a00d890355500c10095030034060307154040080b01c0542c00321015080300e81e40c0070a0043c0d10344a2175450748a0310520800e916003500d5940c83d019203080c2c0c0a14004031f612010240207a4000d882c142c0c0c05800e21000440c1000905d0700c00804840c071721480b0328051700c0b2a45008244940034402085424540345e20580142071155215001502500c0203a0001c0d00d030200449481c600030442540f0f10360080b0007410251a5281000014041400031000c03600c2000342c00401615505c802d00c2040400711802c076110700e841d86003d08410f00040c010020000304118032089036940101603c00d5408040d4000b640350350108007a0f440c0c1c0114280901103907654800011480051340061205401070000c0d200700e10360f14402e000564 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 80138472 1250 80137222 80137243
    0x903040305070f080c060708090d05010218010c02090105010c020310020316080105030109050a06180b1005040b03070806040f0c0b0310080c040b0102030319151814130f0c0801021b010b03 82
    0xb0381008240d810303181b6008018101aa015040072807503d000400091401d000e682c1c000c58070f9940114104440c800625402442c0d07450038240201000d10030380c0060710300c1105010b42410700c103811000d101551002c00c0609483c0b24000011552410704100c20013800f107102c28600c0010b0607800000c600e909040c003810189507841401446481100c0c1d0318903014244600c0c8900c00000c0c3d0b0030100c4041214448194050503a403106002604e0070103062000352031211a80e40d00950042d0020419200300280540d030158100301005040365042c60842541c3d4007545c41180388030004010b00111980c500050003c549080d81242c0c00b000c00c96041c0001d56005000c40d81c05600140001440400304800800406200420018202500b084203500207c200d030080c0c550344c0740e00f030a100b2a0940c44d110b010302042a02c2016881843c0c082070848010030b5829004040c0aa1082c0c4102040300c1e10404001804a60000303640b22400b100a0780704c8201d294180c0c965640c28111410001e00f00491a071904 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 80139722 1250 80138472 80138489
    0x306050601170f060103150b04030c12020604060305190c1e030c020c0d14030c03040f0e1302062a0c04060e0105010903020d0c09020a03050610030501081f090b0903040305070f 77
    0x543d075440c5420320301040c0060045040c55111000140c0c600140f0460700041c02e00c0c00c800035159421803e0a181c90005e607080050201c05010385080035a480000303441c101d035400c2c6404540d030f6840700d48481b144545144603c6000341407100840030f0b00e80014000c10401c1542e040100f5045004400300d00350303070700d0400a40c0035800c40341408030a41048200240024051009405c0030b0b40950750892459008140014483c0c1011409200b402e1982401c40010b11241d10f01866509118803e5440b40071b036000700a1003207000041402d003120481441e4481c40314111603094020010880c0e0b40d840d600c00c0c50546101c0c03490b00c2d401040c01091040302c0c034141c4106a540c407080300e0440c0e01b40b2886100402040d0740320f155024000400e0300d000e00050902214a690100e80d03420400144132000c111400000107040c10b01005000480c0f00092030825141294007413100c1581c20160940100303003c03030018100406660820270540c60002c01442100d114004030b9107010760301c002e608941d4116000c0d2484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 80140972 1250 80139722 80139767
    0x160311120a0209220c06030b0108010609080c010302090f0a14100512010303140f0d0617150609101a09030f06040f02150c0d090302010e0a0501050702060c0109020d030305010306050601 81
    0x115a040840560080074514071140b01441e988800c60300035001c1d401400002c8d100d803401d001c0e55a01080e514018501428440c41d91803e10ba4207645034960b40e44160304040d8046001001541d403000040216100a0401160035481c0c1c2a5021031452111b8458015041c9031030103851580300d07404950380d180000c8042c10300c43c4d0071130381d044901c40211910003804490500c960460015440d00800140c6012500050003625241d40c220700441880c1103985660002031109421040350109907034030031811580e8030600d0ba9031810400d5030076540d81000c441c3c9444c1d072030b0702c1d8007400103d03005003a55030701141122000d500284d0f4642d507480c01150000c010407801081140107007842a01c0102400e0807100c0c00b4200012001e4541c64005011404000a100d2040400555802000c1491083ea045d42c000d00d120341820000f0f092485400c0c0028003032007002862000c1c3c07044c00e500030104070b54018080101d8a4003410014054442070005542c01442d00e4041040c0390b000d0702d98002030380d891151121 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 80142222 1250 80140972 80140981
    0x5040b0117060918060f04031209150c050d06030b182a0307170a12031a0d020607060c0804051203060d080a090503100903110c0303120405160311120a0209 68
    0x19603e40c0944902c009807042040061050000e004443c0f1038070000500d2240d510f0301c2d080080c80b0b282902e1401540f02e1400c1c0707801e00810000e400024105404002c045003001d07203000c08981d148140c1445e4940d60786004004010020ba111a06004030164902109200440c004c2a61581040316520b500c0c17030940d2024080d140354910401d840500014140c2d52100da0b25413001c4150600020000700940107503644004016403268201d020b00524942000041d40d6a000d407a00c4800d0501828840d05808840344119507522084a02d040d42c0242c0034402020b4030400034101e80400e0340c1c05c03504c0b8000c250b600d102110501007500e10520300209907140c0c00c0c040b030701d41011503848420321f041080402c0b18045041e45003003041d600d42030302c211000280720440d401d00401e0401142c540e6100d070f0b04211203040030780d50700205991040000040c9106d0b6503c0c1c51920901d011400d024960300c00311046000024042c10000d034001c400750640707072241504125183d8503220b494040d0000d5000c0385807808507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 80143472 1250 80142222 80142229
    0x203180415061b020414090f0f070b090402040b0a0206040c060f05040603090203100504150605040b0a06052d090907030c1d01200c010306050a0e010902030a09061505040b011706 78
    0xb101c541c00f248030501503809968010a064940c0c501c4002c0910201005001008404100d00400209003601504481d84001040380d103c021501c44d01009840210745c01810740e50700c0c2d041f42e00a000800c0195500c100c10007000e51a184c013103d007980e103c001c4080015115006081c9a8450366086d62018901800c0c0202a80100b001800580e058072801011094002c0c503441164005c0307000c1c40d41d00246200001c90300065801c1600010301450030281940c409403540c1007d2070a039052420180d03120913800340e0415072001030340b03a04a41450100140c03190000101c0c000c0c0b0f06804141e0386030903155528003003607003910414001100000c025981142c0e003510024a40d000a00d030514145800e482c281c05003469400b071821508078550070500100ca903940e0035110302c400401043e0348130380d041881e0080085180b001441002c035656000000208414060f52050061a0b4403041c1080030881000d080b40c8003a129020f460b0080d40340c62265105580a122940e503000c912191000983e52040d051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 80144722 1250 80143472 80143487
    0x170a02030a02070203030307021b03010b060d050c070f0b060108010609060c12020f0709020d050114030d0503040201140a0513050a0b07020f041116120311040e060f10020318041506 79
    0x5030790202ea00784006001179070180015402210164014140042c10700584d128485103400d05a119a2600328410019194503081d0b43c81858500700028240c0d891450407503607407041450003001c4040d4011030504100401581d0b81c01440300ba03071848916a29480306640b803020130b016050210350719607422400141c14800800801d891407040c0c3c5d0410809c04003072441c3c10340a810100c150b64010401602010191240d1401031040c14403100c02410741402003512160001c0c1c021080050000004042d640103a04001f502140d01201564540c2c0c1a0070041543c0c110308800d003400e8400003800031343d9207820400c03032058807080701e074191610440380c0c20001090503104507190802c4d04c0e10030034008502814080e0048450b01045d000c80780345c29250074602415401000c005040c80c140f0b0400740d245010041c0c4065613084a44807110751120340000da0045c0c0c0e8212501d6100254254075024554040058040c0d09460115030406454034010482552b1018403031082c2820700c05c0082104920420710b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 80145972 1250 80144722 80144731
    0x50a0606090e04020d0606062a020a0b07060605090c031905040314070c0e09010b15130302040c032a020c03071d0c0d0e0d0905010c0b0114040b0604091407170a0203 72
    0x4420941c161982e01c00003500e940c2d900c4a4046480d051a400c0e403008002c5011644007102c000b4540c0c2744000354001203107aa8a0301441185840c0850301504004940d40144040c0c640240040a9490401d101c0440755200310b0f580030f490040c81400590100147c0905c90103281e05817140700e24a0f48002d500c119a820070041502c401403400700018000d09010380303d42c060607100300040740060001d01840300c0940f10b061440214813040101110a049105000301601d904680100e50a10300d05002c40142a80600c0610b01d61285061b080140406004110310704400c0d40a80b100d0404020805450304c0e81441084200c503050140420915100c40e1425800f12020b5042c89c10300b00b10392185c074100c5200200d1140c256014015801d103494108510ba001444240b801d0214500d250b0360340350600d10180324584881940c1c035008055947c3d40d8201165150010700502d0701c550350740c2d0920014299500155440100c1d510128510394401e803e811180e4401c006114840c0c0c48802350300000750700c000d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 80147222 1250 80145972 80145979
    0x90212010c081503160b030708090f0d0e040902100309060c03140609090f06040f1b120308040303060b070807020f0907051b030415030b010207060207060c02010503190207120201050a0606090e0402 86
    0x142c1c202280c05807811006e8603084400725201d24040381d002e4502c0c14054900c5030325500029074411a03003400112680104014544404050240b8001c100540501c0100075440b030b5420107a07800d500c1d895444000818003416007404000e08689080c2c1c2101e5840d00d0194603584e50100103207941c1002c01c2e1039900800c81c02c00f1590f2001503413020314205042920300f12802e4244001071020300041c01c41c185507143e140003101001d00c0c500003002c4144070781700360000e043c4080c1100040905d40254484002451081c400c2552403403a40b6100c1415030054808a03c81d03000c4410000c041e0410003000e51042e24640c0742c0504e45101740c4a01038005041c09030600c1da6200401010070722804e202c441d004640340031303100402c0b401207140000e0308240c2550030a20844d80562803c003c134030391050040710b40796020300706030303949403107081404150b200c503440004280750000600904109285c500c489041100398000c100c2921912000400d88004d44110380003d40a0541842034800d11084079800070b2005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 80148472 1250 80147222 80147233
    0x3030702090705070b010603060e13050715020d020f0102130b0309070305010c050a300b0303190504061b2003010f0606021e01060f0e07020a0501090501090212010c081503 75
    0xa40c0000d10a50003200c03080c00282001c03445100f000320110b4080c3c09403c881c1006d01805062807014081514002d103181080240b051a1a0078441e06103d40700c0640310380c0c0d403501035101c40c00e400a1340d10030b10402c051005203d00207880030720110620076601c6080d159600a01c0341881d2018140180e0005447d0311040d0244a50003c00030303209124009100f01e081c0c540342c0d01c4003000c1030068118410441c010000814111158414507680c1c141000103640d4403c00040c1010b032040400e25500802e0200742c0d44016454124a800c1d80240103080ac684203591002c2103180080000c0361070340103440e1700619901d00b0240800741c00d0000b401040c2104801b0700002022030700561020107071049036000718050381000180016030501c4203d0b404080f0300e400028031a80d4a420300c03000121480b84107541a0780092404640190710900020403010f400200a000c02e64443c140f060017407442d01c0703040780b10301d030350000a0f1a11349060203403c04201c0241c8038050507907541030504464011190a40e503050145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 80149722 1250 80148472 80148487
    0x70f1502070b070b16030209030a0b0a0b0d060e0f0d020705090a020906071109130201120914070902191d130e030d05090f06061e031f02090109050f030c09060303 71
    0x702010300340d501d004601000135402c1506170b45080c0c000b4941010b0816004200d45066500c0c001800e20300282e02c000b08000d0b954500200c44014620186000d0340550640d90304c209002860300111045900d410548040341204800590351340203028044015802c140380420840c40c0035075103550b1241800002502c0d00765020006056540101821500c109110b600c01c1c8550030300300d42ca035601205120703440c0c00d1040c40f038001a00658840c8000c5045a4407420035104110a40d49034000c13002d142c204807900c0546440c1c5540c0a50442c1d100b45111640c1c603050361545600c2817118482220b051810800c91f54007c00910182ea4080c481c02c4a10b0354442503062140c4e00204003e02c1212602c5600142d00d09203c1a85d41c05e03c503058805042d40d030711480038801e40b40e40c1d2900300c41503180d4004541c03e03ca100017010a0808400145d00b50965601c460840200765080d0020f0580720003da0b1600000d640395020044841c009515464040c0d0120b0504000ca04180240c50b070480001030440341000c90 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 80150972 1250 80149722 80149739
    0xb010b18040c020f0c01080c0d1e050f0103060510031a10030c06020d0305010518010521010606030b0108090a05070504090203030d0606090e0c12220c0e1008070f150207 74
    0x104107000142d0100050400c442c00034080031789280c509103005901800c14200440583c01007201c1c3c140010381e038103410465102240d041e05039641d0641e40c20720082c5441c050508201400f440241c940c1c1d8200400212217121415100c415030b503008143d0154403070700d0781a201d2812030042c07141c800d0081d03090020010914440c1c0c44001803205a0040601c1d0201810040030303250103900450003600c50080720381d2410030594102c0e05498042c6c07a0100f070750404413602c000455144484131459440e04501140d000c0c0d26820010079404280c86206031a1101020760383d80e0442141d010303015800455080c00149400d800603007119000030122420300103004103240c203c801c1644a003002c116000010020034800058042d88071110b0f402c00c03407d1030042400d1100340c44d40280031016070200f400310a50802e04102d5800107882d007000c082481a40c4032a5101643d03581541d14103800003006000103650f01e400a921030076256580c4008510504d4001c4040b0b450203010244c0c004d40c02180804160004e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 80152222 1250 80150972 80150981
    0x21e01020c0d050c030d0903021e01020702090105010206060904290108010e120a0203070f0f08030f010801110c12030c0f0c0c04110705060601080408190c060e0a0b010b1804 76
    0x14450005aa072091416064500403403440b07100c041c4141404500f880c80000720540e08089078542020070380d03040520b400c07810b02c440c880441c02c03511040d1036408000300b81580039010691080d2070308045030340c80c0c0005903500d10046603856801911480010000740b580e07a0f0801f084044c0740b802c4001f103440c0580015401d00240c00c4104169501c001007a05072001b000503002d440e200307500040c03402d009030f40001d44a20540001030448211202c50f9000c108e01400a500721039080b003403083d00c0c0d04080005000c402001c1c031480040390b00340f15086039000e00a8044440c804c98403001044803007808404002ca0f5040140801e10710407061099030840f11203003005040d5624094040d00c40341c0030320000c00c01110318602c90107400034001c0c40400001030700060b4070741e00401d0908100e0016611440c00220341c6c86490301c0b20114140101402e6200d03600700081d00744a9121390000d10107c60107207245d640d40c1c694050b0241ca488091801080403c9001d801002204160030403070440e245000c022a0548 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 80153472 1250 80152222 80152273
    0x17100506130c050405180604060b070b04080a12020c0303091b130f15060f02070803030103030e04050a060302040e07170607020307020919050118050901050c0a030c0c06060f0e010803030c1902 84
    0x1030b01101f0825640f925200e0300c070150054204a50620303a15480c0c0c02001d0600900c01400a440014031092a900660a1645c1c140103454255691500803000e6610380d08255800c8080e840740f46208001d210341d42002402c04840542020f0b040c03d0b48528040207092120750a911255036a01c00030b03100c1100001e240c010300269100d40c2d01c24152803400902d000c1c0540d01450b900d4006100520010303a000700881403692040718042650784520950f18000c01e0341c0c0d03000940c4a40381204c6840c00c0301c07001c11002c0460320f09143c507682d40281080340c1502c503d0210703550030050b0410401880107180600b4407a400070740d00b01d41c0c1885440180c2d60b46003202e0382a04195041c5032000c0c1460b484802a00130790381c1c0b0003110b00c005d20883c02c18010b5040b2501680b10340301c0c141038460400c000494410b0b0440003c43e03812410600140707a40d064814030345210b40c011020801d10b040c002007005900003003241e001d9084607010500e8120031001d5441a445807400781d0b0110700800301c40c04640c01a624002200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 80154722 1250 80153472 80153509
    0x10311030a06061706010e10110106080f011d06010302060a180f0e07020a020109030b060d0c14010306050a0b0304081b010203070807020f010603080418020c030417100506130c050405 80
    0x81900b07009010348068403840d13000c0c29036502d2000b0403c460340e00000c04515080152003032042c003200e40f00b06440107145540510007079031906e41e00160405c17001418001900380e82000708036a9901c4841b0507094034260b140c0e200b0340e6105400420050a0140081088030940d00c0c0078180c01e010381001c040844403583c800c12400c2000d0304244450301180340a983c00042c80d00040c9449580c56001030b11a200c14800680f0003494000007030600d480d0507890f544415400a04000d48580340c94852411044400c400ca000909d0b020000c609800d03c3c0780e10b01d0030b0b20b000b405014110759031b40d80c481803590300001c10309041c10514071150402c1c00e03090010358082c2d090f40e1161081071503c004001d14240d100d1401c0b03c0d40d82e040c0581000410502000c50341a260083c030000329801c5c00f20134540103403040a8491847d0710000500096000740d8812014900c0c00b01d030152030702c008001c0307007240030b403201503c0301070f03216021403c1c16802c54a00da200f101c406015003829400d00b03945a00191030300c081007022910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 80155972 1250 80154722 80154731
    0x106030302100506030a150b0414090f07031e02010302040e0106021e06010b04030b09012a030e010c08070c02040b03060a0225030e1e131b0e01020d030b010311030a 72
    0x405405100e104076000240d0b01c100811320b8080000790b521850b2500c081e140c41e0030328015009200c4550450003e03040060400e0014070303988404408030f0101203030409114024150707a1520042d0100300d12086a0704121201181c88000001c0b1082e59495072040341459800c00000403c140d0f2201058001c0c445500a01069580107203c8450903040c440c410106400c80720045c0304011002042c1d030141d98100310304820b250f4a89094900410360f03200c00d0141d024040040340c07a500040c0080040030b24517543c062040101c044101800e8503100c49162003c0b400d010b0020f100c3c1ca00c10812444000d00044c4081051283d040110341007078000e443d150406a000103e013011111942c1e921550300e582041150042111350310010010000035103503610400040080c403492181d84940140c4e881001080140a203600034400b0740102031040c10848021103082c42d40e08840e01880704440c50880680181404001510048008105000c3c28606240e550040500c0c500021000f4520450500b40c2c0040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 80157222 1250 80155972 80155979
    0x501050f040608072c2701270f0c090b0a0605040503070504020f0f0a0f030b030a0209010512010f090c05041404170304030905030303040605180c090c0a09170106 71
    0x5625800380c40c0c280d004504200007006030b640c2c005012400c031030f86003c800c0d0300d00718052098031342d105108110440a00c007520910104840c1c410100c0200e900046840b070360704130340510084c240c0b003450b42041e502c1d0840c400c0c403002010b100c000580b0b400b442044680c030380320901c0e40c80c8a001e441c56000300c48003030394403820300b0030328101071031100301501c10740c01c00506141c030305000079645641701d0203050302894001c01e00400c407103100000e860100040c40c0e01e8546a6401c0d01e4000e0450400d14130380c00009050040e07801a5080100300341c0307800354020781102d1007a8204028400003a01d1251120029941e9080070550340d5101d106600905100b40d4680b030314185040100304c180d410304490203401488050612000900b10004604000c26070030040d6241d0355141402d86015103154042074042c0000001c000130030010b45d1010344143c3c08be16590084011074100701d83d684441010080c0c02644100201e42038a10000141c08412414909041c0e40c0f07403100601018903a00d002540c0c0640c1d122142071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 80158472 1250 80157222 80157229
    0x10050109050105070512090102031b0c040506040504030e010e0a080706090e07030e1b0f0d0303020c010f0216080702031905030c0609160e0a0f050903070201021c0206040b1810050105 80
    0x340e00500007441e00c2410705585880c0c1ea5140c10002d0b40840740030000140c02d20f1181d000b071040c1ca10324120011f40c09800c6103081c1c200e03078961303a5100302584518549800034042e40303040d03c40c1901554055036051481c0035407000540d080540300c4079196010ce06000c00189072482001150701401d01a500c2c100480c0c07804040e010914005003130b241c01d260074211200076500e400500d0710500f0f11600340402840941c2e00214040207046c2106503007128101e1075410604d901900204031501d04500200711441403079810004034060b0341b1608807001c0c001121000815000d001410400c0d0004068843c47d200301211007207a80341c26141115035030404102e412030460305000c0180c0c4400c2140180047c040b0002c3c0001e170864080c090308205a440d00003080c003803250303070703205020705000014100701c40d08003030083c2d941e260000c80040380144200300e19030000c8403420110f00b584102580040000351219941e262004000620080010b100100312540900c17080080601c43d5604210004d490350415060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 80159722 1250 80158472 80158487
    0x11070303050402010e0a0f1e03210903060f0204031407060e01120e1005191505010302030c09030f030c0708070b16031713030906210203150618041d030405101205100501 74
    0x4182300d542501d040000c20307000138440b0060b10100c20aa806010b0085083c0c5682d00e030358001510032403607c1180c41c01c054066000b40107403130103480040c1801c18141c1031213954081c2400341e540000c2680700030210550240f10006281840400040b0306200070160152400e020701015426441d1940240603000031417590b00c5125004450741031040543c03004410054414034443c8904060780007000030140c91054055071a040d034005c0503200080240b83c40566250417118480105014060b80050413000005101c4201c4025000303032810704401c00903414080319441c005405111000416200e20708140469a100f48031107488518403c0e05414001e00401c0590403480502a41d20b1640400d51040c0c003441c4d000c003800c90b001580d44e655401c1c0801c00e4480981409802201c04200060742150590300362407012001c2e501000300c03003001c0e80d80601c1c1c08080c092600c01508200420301071410302d00300c0d03c41035a40302c2c20314000c0340180042e00811944100d6006603c0b00d81c84000340400e6901111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 80160972 1250 80159722 80159759
    0x504061a1503010302100e030d0801080d0e0a1205031e0d050c03040206090d030318050604140303010b0d020a03020702090108010203090717030a26090601080105060411070303050402010e0a0f 84
    0x50300c40c0d25000d141c0018907144410f01020703100c2d200c03105016410f64840d040c500200e950241c140e80001e404454090720141d028000c50113603001d842500035829100b0244200302c190010010502c10349008030040701c01703c1102060311203010800414078000b80842c0001c07080e1008009080c2d40d001c00d00e150004841001d408110310010410600001d80d894800341c2d200c0031401c44096221460901d401c0d0001c1003070100340c0141121100c0c40700d05000d404030b100780c46a4000d1400e181402c2c40328841d40c1d120301c000d003d14084458140b01c03a2001c2c21803540a001140294180140740c41d43c00e400095444000340d0000d07105030340020800c1401c2600f8042e40c002420801c8400250b00401d6142a840b4000d51112070b0030130030b20401c8d041480c5841c1d1814130285100791105030650400b407140c0368a4100c240220748066081c0310200301039041034803503c081d101c140c000701814102599000c40203890050720a9042107a003409141c034654803104201d00400012031010905407a0480aa6100903582c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 80162222 1250 80160972 80160979
    0x40b0406030e0c010c0b191a0915030a1709030a060b041404030e040c0e060c0c180f370203060103200405011b080c0601031e0327090504061a 62
    0x2518003440c4c0d030001c0f000719034180c0c0484c800c0110754840095805804002c030245080c0e0f0b0074070307005411641a8011101c02c801040d2021440daa03600c030f400c0d0b5882d08002a400303415a01c0b008400011601c04040c094410450640071481c1c00e0000d00000d1400c4400c04082da0a59903c40e10540c071880c0900c5080045160082e09030390515003624050480000703006494051611507081c0b0b21550b104a0035004030780c80041801361940326a100c0d003507840c009214241e000c3c20407807030340803604049400e56600c184000091740c0225520491906410300002218002800c980020380c044038003045440d9000400e031010042e02e07450044001400c1d0303401280700d031569404071800c0c041c485005004940035030741c01b0f00300681c5019030b1300ca0480d09401c48040180440001141401030301c40f01240c1c01e0304890040e10b10000006500140381c021075a8180c008001c03c10540350310481082d03200c1000499820710a0108200e41c0d02d401000071784404a40441d15a659075080c51055610552903800045096 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 80163472 1250 80162222 80162233
    0x50c0f0303240f0f03070305030315040e0a050a030c03030b060d0509120f0403120c0b0a09032a02220e010b0405070509010f03020904090c03030c03030e1908030c0c0102040b0406030e 80
    0x20b000c620200e207025421405040004c0e20b08582d52000c01806c0000c44d0b01100712592492700005860440003c910101e00c41c07410720800200c458800542140c50381c0e04000549048051a6415209120300e050200e0616446401655095813078402607e031843d001480407805180c07810103e0300702007544005240c102828003100c40702c01049000d0f203095071f42c082e40c012029001002c0c02d0b1920401700344020001c400364401c0141c0c4129507000074000e2440380c0c0700c41c2e0621072014544044040220300f81c0c81a206000c219101500e03005000c1b0201103600c0700c0c1c01840e002c00d0214141a00c419030b03400e003c0d507910382e0310448242c20244138440e80103a481c40d01c542840c689000081240b104421640e04140e0049a0007115941d10341c045012150721019015a942e0780b0710700a01266400101035003c2498460303d8a4600c001042d031041c0805d089803038100207106591101620780001d80000203101c414095460308010900c0208064005a0202511145042801026900b200f14500d485801c031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 80164722 1250 80163472 80163541
    0x5060307091d1c270b0c0d1706010e0d0609020603070302040e1308030c0c1f0c0201050708040b0613090c0618080a030525060501180e01060305030307050a050c0f0303 73
    0xc0720400340010003807030500e0f04e0080910741310042440c03d5000001945400a186079548100080c4600581c14030303200c400d081c0e071030000e002400d41c0c82255800e01044100001100340d2030900c80f800881c91245000142805141e0080746c0190421201a00402c3e8001820311014021880e041d074411001e000100b45199a0342d66240c080c0000340018100340c40120b040c4841c403005010303491002d034030007040c19082c503240d4070558050040c05061202651074100406c0c5614400d0302040d12881d005a0070b10090740b16101800f0410080c0002d1925035940c0d20241030004903110811401031200f5640c00100031140d800340000c55000780d002041d070794400d00107400040c2d044030039510a01e040d9000500240a180c0707440301c6200107000010305007072410340041000e07181d811056504074082e150420040681714155030885d5202d006c068125401807000a540c0c502c1340006081d8680186005800e000c4280c414038545828488190b0b441c1d0408410418401d08007420150000d60f01103480c1d280c03103074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 80165972 1250 80164722 80164727
    0x2f03010b06032205071503050114240d020f03040506010824060409030e0d0b011806120b04030e03030c01090b0c04030308060f03071505090312040b0a0305060307091d1c 74
    0x1c0e21464080c0a418081d243c60500000340503000c010495406962070307001c3e081c00010300411003405924a40f0b120034444142d90705140c0301c80100c52001c81c0c0350101c15190960a4a890780000b6843c242c1c06808100c00300300d07640d00c40c02941c0503922a000030480d0b541001d4072242007104003420101c4040f1980c0c54483d18102c10704044d0740240d4180c03400600d400d100e050445210a4124a06411003840511201008100c220311412140c444a60380070341c241d1302d0240c409440c1030b40b140300d08003881000f014001c00c840406154002d4030904000c03c00c01030ba40040b80c1160800c4420062a964540400003841510f00c01c041c1d1090109465134070b00390a65070041e020303e40141004e80100f0354070007500c0c003e440401004001d00052906211520380d090f00041c003990001031164082e01406d00c480a41941c400c064805881221920b0790810701840b42c22402010001d20140e4035220350400000c82c12000c0c418000707080301c05071034048112034040240385001e05c646001450f00b460501a03200550303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 80167222 1250 80165972 80166001
    0x30307080112030903020409080d0605090601120e010204030606030f030e09060901060e030f16031502070b0712090b130303050f0c0421061b020d02010b1c2f03010b0603 74
    0x10b042d2000d034418800141400c681d038030060742001350421b00d4440d0304000d11061201a2411109000d001d0002d55240c005100c0080c900751001e1380443c904116407140251203030050604a1449400103003490b6591700c8005c02d03101c6030361059820390302100070103007499070200c001848400d081d43d0f8402d060034410080350b14140d0510419080101c140001c00c466601813040e4105102c03440112541542c18928003003103480c0c0d0f4801100e110004110200094105000b0f0311019504103d51407503680d1281800e581d1007000c1780007610001d58076844a40060644031070700c5d0040c40710040d0004400164074002d402c43d40041c18052041c500c0008202e640944002114140c40441e9811101c484003a803604c169110800d10040800303081c58240300900209840c95010306a040d821540c1a0030700d0042a400c0310002c41e00181c1006030102c28000a104c070000c1e11031b0036441505070a80401e0f2802001c2c203003403181940d1183c00707584031134420780a140034012060400021a4828910f00303005000c4030509 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 80168472 1250 80167222 80167229
    0x20d08040503120c07020a240c08030103060507050c06070509270106050d09020306180c0d0314070309030812010906080106061713020307032d05150c04120c14030303070801 76
    0x6845100c002a103400b00c01050752aa594087e0100385095118464608100c03800320700c60310480300c0e5000040ca5540700d00342140e0180d4229074958990307421a00d4070405032000624420921904014108082100300314042c4617460f42d540d102c0c2c881d006e5501300407010b000749141e032400607241003d502c1c246079254291811034455061041e51090030701c1c0c03000042d00501134080c2d40b50181e081044040208a01c6da110380004540954400d8441e0104104a030000f580000d00016803080c00480c1d821131200081000501034105003604941d25074422100d5880341040c00481d200d0100100b285800900600018100180c0244a05800c01c036000340305090a105212854442c0c90108805d001c0003840740d012580c018055654094a80c1000e0200442540100c4c05100b003101200f41a45104c0700d221000301d5210313020b04014400103c4c480300720040584a040c1030310041100003641a00606545100d9100d17414a1081600d0000590b000c00c010744081070080d0010020008081d6203c004c0c207055 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 80169722 1250 80168472 80168497
    0xa14151e01140703030902150f040303030b06091c0201090e011a070204020d020304080301030c080a1101050304030e030105090a0c0902090d031209050102120906060102010606020c010c240c020d08040503 89
    0x140c000400c0100e0320b0702640c0340c0d001c1c2c440030000b99240605516405ca150a64001c3c1c82d01207258501d4403150b10103200d103540c107401c0f070070060000f0300029100390420000030400408150424040000103890380051109000300104214411070031940c0007200c80703000f024032000d81c03100d66140a4108101b0400d251118034454400103001045558917030588080300c8031034408546034600f0703142000303081d03200703000581340792010320310024821100046080125034424655080c50440740011344154201034021801e002c64498010540e4a0900c0b9862007020700700300604910003070f03041c0003084d207030a6009907040a004110014050703c9a00d03080c010283c0c585004601086136a80741170090607aa64000e1203940001840489203419503000750158034408c06441c0c1c503403a0100103908a030414400d010250704401c00c003590660141075508051405020303100200072140c40300d5050f410445c4070310075501790349603660110290f04100c06034807403420341045100c1c3e040c00d4495566a000e02c010320201c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 80170972 1250 80169722 80169769
    0x506181b070b0114130606020304090903030b1002030406030b0616110105072f030118021201020408010e030310060207030f060c1101020a0e01020105091614060405090a1415 76
    0x21200c66050031142480d800003210b51941d40c40e00c078080d2413004100120362040000001900700c0c0d0b12030384250000c44580d9001185418540028580541000c010a409040e0343c1d840d41801901d400b8071000e032412265014681d0380b400d061001c1d046440700c81445001d584140225658000100000c2503059004110549154450300049401d0f1103490300c001d0aa020321490615600580700301105424030040c01c489030134810205241c2202c041c80c02d1740c0c02e01c10303d00041c4005420586801c502c4100c00c24000341c0b909464560540c00d5488a00090119500c000100b0008104041d40100a00b14502c041d0111520710b80343c0d0803440c0084a4040e050a40e0780c012040f4072400343c408010350021041c0250340b07494285c04040c191804e0420a24099404c100002c0c511041c04902c0c4650800141440340c800c80c2000300403032071418550030715070300030004000c04039450f0348841d0454800c1e1a141c1000c81e10808c208445055171030007404070510014030524100c940c1d0340b18524803040c1603080b8038403007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 80172222 1250 80170972 80171011
    0x7030c0609260a1e030806041b0c05010f02040f180c1224080a030801080d02030406050f120c2203020d060f060b0c01140c070c0308030a0902090c03040303050618 71
    0x50510041d0f0304024002d540519850900134081840d10307440e1400790721140025907401301440700f6903280b64102d42000501410a00c3c0050046005120b0b0314002c100000d10034100d0b040600c00c80c8d02c160040c3c0324204040c0e04c20820030081d09004440030540400c24054101d4816010307149101003907071020400d03215440c010442140d80000c003078042e611040d056003141ea510708e9a0f150700310007000b6000070b01c00ba00081a40000010302002241c4c540d40118601403800d01e080320190000c1020710815032082041c0a540404002054010074803442000d6981d031107001408505012008114251808414200003603520482c03a4481940c0011001c22074209000032400141226000302981c0c0a0200754046e0034401503100b07080b01814002c2e9810701d0745500301490321a00401d17100078580041c1110900000d1182006180c00c48419000410a21030034ad00041800d10201e400049581001c41084180355041c01041d8209805a4400314600025800c41020b090005c100d00340625140e440b04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 80173472 1250 80172222 80172299
    0x9040201080a0f020406050a030e010e06070c051509060709090c02060109020705030c06041101020f0a020a060c03090b04060c0b010509360a050102040906050a15030c0e0d0507030c0609 81
    0x3483d41402e200341150b40e00d0322000040c0c5950440c0e1142d200003860103130102140341c3d0501c50079441c44c442d00d00a100c2e5541e11801125920108201210b640c0904400c440c0c8071900342c21424092410b82020340211302c2c01c0c03100241181c0d1030360b0040500905150200e02499000f04c0c100781036071240d00c80542e82d1304050400b6881c2d842609064441da115285c10042807001d40c0003c0207444600340e09544460301c07010055581c4001480020350300030746007181040003600450207080210f120b414080c00c040d98403829128a5000f81d400710b008195001040410080c08803251070240004950004080c101903040c1c3e00010f540c00d201c004036164043c0012071608007000000240039603401100d01d050365070300d0458081c0d000f80c030845803401d003070a00c04101d52602005c460140c906040103c030000710f954a00324058020402d4150174800400c06081003900c98106000806010b4001403480c145075152490541c08264481010080c2d01c1001340300181d2842e40010f03440c150b0100201c80c440003440c11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 80174722 1250 80173472 80173481
    0x1a2e1206110c0a0b060604081005041e0b0108010c0906020606191a090307080309030631080315030102160818041805011a010e01031d060a020405090604090209040201080a 75
    0x1d626540d1404980c44001c01c40000b00d00c1c42d150b210700000c40c2030391507250a100b1140558001e940242e082144502000c07130319988440e9100d030044107043d80105841100300031507075200d102034514a0b8407000621949109002e03894041c40d1710b02d0324004403803424074000e440b840003038001803091a1011019a044100c002c1400140207031445205410001d5a0803e11a500002d4014084e0069010000301220003000303032014068090060040c42d900c1201e0b80043c0900784440680361691422091030845268840203115481489a01d50360b040103284003440aa10000c3c1d284071742e00402c07041c41071802945a1140703250f40083e49540b01c9100101c80040c0c05288205250810305c1c01c002d03008860606049800d4103801b82c402081417449a45085000c42141500540400d840d258501d419520a50055068000280d03040d0f200c0320b9140b0240c0d0030f200c02a10490000da401040c288002c4c604407102640088c41160104428481540450f003031078002400039040c4000240020b101d100550007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 80175972 1250 80174722 80174741
    0x40314150c160c080c120f060f090a060f0b040f0905030418023108010204060e060d0219020123090601091805070602010615050909010504020a020a1a2e1206 69
    0x507002150b0f1a0b03900d0b40c2e56a02c2032440240310390a005141d10134140041201d0164447d07690103009542c0c0d6288030004841c001030181040c920038a00031901040103403080040e215002040840c18020745d800300015100088103d4078868034000301030f000a9800070445084803c0b4017181c941e11404450030100a000d0241030481d642c1a08400c50b110f9403941018402500000005440301500c0e41c400d14201c1c0100d00841001c80d0018600280c5490894060319a98510340000351820208591004092034030100a0016039161540240302240804c504016044c0101100311185422a1030070b60b6500184220100140d41d440d9003403a5500008240000b113401034100c81342ca541d02c0600034001d040511600032501080d60142140d0fa10500031505920b0004195050703030703400c1400b0480298040c03000c0d0700541c407071420316000003410040751102d1902201000084d6280031050241c1540f01180303600c007540314034078842d4846442e009440d41514100e1000811542c910702c0c0002c001c0c0422203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 80177222 1250 80175972 80175983
    0x6080601110f07030b07140313020d2a0605210a060f06090f090506012c0411090301050105010302070201050423040608030a0e010513050103021602090705040314150c16 74
    0xd4129080c6900080d10f20226881101c0d41c0e5440c0c0d85081c81103d01004408462130390040400101b86909201c4007100510b6000400f284200741040c0e480300c800000420890309001c1c8030488003690031000c002d18000600807818160315120125140810701c040741c0e614441e0200110011540c00b100d5a03201402520000d25803562503074440001502500b801d03c0b442044070f030b2644001c60101014041c0900844040c0c40b40c0001c004981e0f500c1d40032001100180001e0212385410714905e50380e07409121a10b0120901d40380d91502d191062500752003050304000e0605004220190050f680710381103800b2a51200b0013100b141c46010000c0703008541041c0015031040c00d0000c0480c034000048014000c00c01c803a103411085180d0791005603405e0240100c1e607042641d040340d081045500a800408400b440560300054021840c1d00107180c05030107403106030014001160520801a40c0706840382c0d44a1800010840c000d88241d44441c12807004203e2540180d002c1100b8582d03141015a2225059119 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 80178472 1250 80177222 80177233
    0x1107030810121a0a06120f03120c030b04060906050906150c01020d0506100e0a15050d0204080a0201080a0603110607081201080d17040506070e010504080d120e0f070608060111 77
    0x41c2480e42e001c030111541a603400710f8820204a601d5682d22500b42200c140100500d10f1401c261107101c1c011601140a4007440080f00c00741c1c884900500c030740e103001400c9071400901580010140f004a68140d0460b9803000d00d0311000740565610030300b44903880b000c00c6030441401025410003007050300814411030410b60001c1110203e6103803d8010b41d126201c01e64001c04c445076912070803902c0034803490006400400c644c0c8288030244200591000418040c204540ba2681c4052143e00b03c1c0c1c00b0340d10942c81034103e048204115a030055290b50407101592050100508580301c1c854a031880e9200907201d80c03400158107040004800581f80046046000301402d036075900702840d120a401c18080001078205111081c080b401c03030755514040d41e0800700408032581c5605080e95403044111000b414030106100000f00d5840411480325401c1c41c0707031f480401403480c281c81401a900c00d0100390256401007440450f0003030002801c1422660180740408030b903114000141c03503094114503d5821402103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 80179722 1250 80178472 80178509
    0x130f050a08033c040311010e07090203010e01060212040618171c03090519020a1503020d1a010f1215170c0f01020601060c05150703050405010b041107030810 69
    0x41010310400401003001c40c3d20400a92284903e0000d1201185803003250000301140c0442c1c07094020003a00c2100b00e00016030341175000540c920301045644407102c061b800100600500100c05c1005004001e94001080140180740d19848103010351701502040106a000c45c6581e180102c2019006000d122031390b290102111001c107443c0c109504c55081e1508000401e025a07038072922544801a8004001d0300640704450140c41e503003044d100099034071000740070000c260f121003105d02c0004e00d0040c0c0c4005a5070015050400140c07410140c9809103078000708541e84259030415003100070901c1d280307006034000100580300d0b4005d1100714400c040600e52502c003c00d8031000032801025400c0400300326038804001c0030411641004025510340103800410041200c0c0d40100000e40e15144a80d080e142c4840100e140801070380022210500000d44074400d0000313001c020f100c6c840807042c040d9420f000300c0e110910220180e1181c80780007020807070440002142140660b44201c042d04880015050700b560 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80180972 1250 80179722 80179741
    0xb0703051b01091704120209061219050c01080408120603070321090f0503150a11070308040b06030609190501020702090103060b150301050d2a0b0309070608130f050a0803 75
    0x2005003089551004a524240b109604c0009550442c0c42815102c000d10804e5070078041c100d10040c100d241c0110900d0310f168803c210901c0010001e501160840340302080500f041850701a102403040e040c401420b0600c4046603900c4100c8607200155420244503458100c0842e180004a40c4050200780c403d41c003090110801240304e001c1c026155075190305060b214030020080b80210300c102a40741e032002035140f1041c000c00c0c04079940420b0000002075490074124000700e041e40a40b03c110000b8a07510100010854001030710351f0072003c1500208600e10f446402c1707580d03494107000381c0406d03004882c02c003800b00802501242d0465601420005003541d4903d0040054040c03201d07503c0c407448841e05805101035400381568102d42d402408200214a01d4403402d48a45d00400e00a2001280c191191280e04c9001040c2c1c00501910140c02e40c1d80c50005500c3e03060001503080036080052171018414207141e0034003e1002d050300444c00303050b4000319142c21131903c082d4090003080c21a001c01006417100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80182222 1250 80180972 80180981
    0x509040f020d050706081504060503151e0a0b040c020303060307061809090b1503030a05040b07020a080604030806040b040b0f060307090f0b0307090603060506070f0507120b060a05030106030b010b0703051b01 91
    0x31f030f42c0a02d020240158a0810050768114007946425521009c10036112007207800b10143c20410117059400000085000904101c00440355100704e5901d5644464a6091034401c50b03003900c41c103102460540c1091000a0b403a90601e10a610420060181e548520406201640c00900c0001420449095146000c400b422070840d20040103807880c0e41c0722404c07800c021084420940030340d61254a054100101c254298108810603a00706000722000305881e201000514011400b940301c82c0e08501d0584104400d88240c0a40540158141162512103840e5001c0e40d04c0306000440d100798603590b60f000100d40e5041c00b64468118814490000191100707a10010760041240e0340d65000740a8642e41c0540c20756049104240c0c00441c100120004600300c9111100181d11a078150745813680d0b40e258044a0720030031142541c03d400c00d030301030142901d0454000700041900b42c00070303c21a0310390740301c2d038008440501c0707404100d04000518004143c4034004030340c042c0b0400b071441145107410420890080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80183472 1250 80182222 80182231
    0x3020c0301050106080103030906030519020726180906040b0d030809060106050a09050405090c031b041b05120406200a02010c030b100302250821010509040f020d05070608 75
    0x1d500c0e110000c03581d244614040341c103070798141d00d480c1c08023494514114000e210080015100440b4030a10740c0b0849654002085001d0041840d444100820480c040300c4517680124110421000c000741203504003003019141181500b282c04001581e51440400e0180c0401c1c070607e81e1000716103950008268003c02802e00500504049441580c1c03520400d40d064401c0c1c0a060b40400c984800403c00b0740b801e50482c5600c1882c400035903184d0404000481d00e00001e02402408441c2c441030310381c2c4a0700f000d00c1441c0c9040c0d08060910300000c01002e018141c0e100d5410942ca0722002c000000d800d01c07031103400c402c1080c03105014182c25600420603c000341d030002e21207180103509205003036035010710074010518070b07110080101c2515564010140c00951040741c1592103807441c640c422640c0e411001503e5656406021541e80d1808004100d201d2a55041d25103030300c0700c408400510450715207110340d0754819840002440d0310482c0d03000241e80c007071030132100601a1041c100042210795004034001d006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80184722 1250 80183472 80183479
    0x30915020301030b0a020a0207051e120f011a06070308071b05030706050c030f0f13140a05070e0f150604080f0d0906030c05030406270f030215040317060f03030703020c 74
    0x1a252240b02d18180d104607507003040181c1c8922760034899443d00304800c3c241c80c0c00000d0b40254910070000420104400145110243d800c12950003007400003e0243c4d1400344044420342d07a55a03400c200190791809221005410400e2820026040c0c83c000c00151019031080c21407044c0029541ca0066036952006000b151700031705103004030f030340405200b0a4a00036461004200310a0759010401566808012315103c8040c2c071407190540840c1000d114103140d0040000588041c5a107410000d00e46001c0394031100e08542420300300840d9950640b61135030020008010840d91402c0d41001460301c0c000c40d04020824002d0b60040004c00c040003075040c0d43c9a034285c450203030150341c5610540407202030048103004600100009000200241d0020484460000c00001c0007107100c206808140c3c0c80c80c1080381e980340c2000c3c12030103241d010458060304409501c810481841c0c00c1e0303030040c030320154018400042649040402c0c802d5403500c00c8040706c0000642200c2c0c40300c58500b0000c0d40c6240d5080e902e4003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80185972 1250 80184722 80184743
    0x30c060e09010302091308090a03050a0c120302032704050a0209011d030c010e0a081c02070812040306020d060504050c0405120307021c050a0c0617070306180c03091502030103 77
    0x150781042540c1070b048035002004010a583ca01071840400b20501204458040c000c00c20114217030755108461000d103000344024030000c150740ca001e410060702da4100d81000c02c02c1e4101c0701e000983c0041280c84001d01032400744450414075039000800c0c44a4005603038803900380810089950081d901070440c9003402d03078810a8402c41280c02031202d0040001c0581c042e04402c00e0710032a54041c020317030f403880f4102800400456550711703182d508006150510004a0110301082032903154108100c0025000b600041c00e01c0701d400244540c000c4c03040f4440104690780204850103c3c003100e501040c000e10020b0414007042c03814411901840c1d0045c000d81d4400e03141540d0001c0107200000544900d6540505000e1007980d102150051507441d07184201d070b25100e240001000030341080d280500805ca151500b484641aa50004044041c0208408105894007404012004200c20064041020a00b00148898003980c3c00c8018120480c2c02400c40b2100d40550920001581d0041d81224010501d421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80187222 1250 80185972 80185997
    0x150e01090302130b010e060301080109050f0705091501050d0c030e070b160209091011030a14040b04140304081c020c01050f030a0b040f0f0b0f0a030f06020a0216030c06 74
    0x440303000990102a400140f00070300315100314480d81c8403480c4201e05040105203000c1040001c3c910390300907002222965102c60305107040060400002a4000383e500c09840c405041c00e01107254460010906410080007034144401c50b40580220760350030302888414001e03180b0740c8802a01419454001f03001a00c55003c001548a40038000e9441e45c0006203040040300c0e110b5003c2022907800500b1302c20f007602590b041028920313424480d8105081d0b54400c9181c0700d15203541c1200c1200c2107010044d040e507160b07900300000100b80d102c00d80e0b40300d0f5010325a07180d00c5a071b40d80307003900d50702494211848500c44d0300707040007059030320004002c2031820542c200d50080c4940030046405010702040360740c00c03801c00d00200c0c03070345040c40d040143c0d4150042c2000231030050403010807007928801e0081c10101075507041007044509143c40f071200250340c00e0f65448202d502d1a80c03400d40c844a492400b0740303040d42c007142c010b200740e1083c00060510320002d0b0300100000e0701c030304120072408154031034200800d255200e203c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80188472 1250 80187222 80187227
    0x20c030705032404080c070e07120c080a09050309030f031c06080304060c05030904052511030a050706090804180510060f0c020102010b0604090b0f1507031103070c150e01 75
    0x900750564101142d00e00f44524140c01044140103001207611640600000c82c085000300f10200041038001c10010160400440c0500b0600089807014859814074a41c4a8181c0c0c115410b2504000000800100c1078a581086410b5000e809482c603031500030344501d001411130000c040d001003c0c9140c03149204c40307101460724040350400d100303100390764009004c00c105440c01085581c2441d40694142c9141c5a1000005400c030303001201c54680000e50400d0b11004010045000c020355002d9007841c800d51560403261990701e001c0c01c1030400401c20001081401c200898104080c0191300c007281d65101c580324284102e4200144282c0803c10f0301e0b02000480003d0100444c008690241d02c0d24184440075241c01c4031042400700d0b06074195900d400000300d482c0c84110081005104090340090000042400c00184482d5445454402d000045075280881045030448100301d500d410280b1841d5001c818031790650180600c040c10784040841f0000f800300202808141d000c40a42e00d0543c0c0c4564040103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80189722 1250 80188472 80188483
    0x305011a01230d0c09031a0705031f0905090a0506070c020d0807050102091e0301060902040f1e08150604050115080c09010302090a0f14010503220819020c03070503 72
    0x1034600080c284448050030300724010b001034401006000e075615040400d242d1074250b0703a0900b210400500e2a02041080c008002c1e8110008020209100441d081591001384a4003000d0030030210302c410364207140322490f5205403802c0284800b84080c002e516000c5600380d03c1d080d52800641d01c41c010030000403a460320800107602c002c0d90040c8031541e08001a1036003156034001c000d04072000e47d8200a02c0003d5581c001450404504602c44117800c920307048249425100558040d401c0740f40107000600c0310041c001103110566144500344540a98000d000800c050303203036442410b13140200502d00c1017070514103103664841e000690342072000da680e402141e13403110394003031007100000c005101041100310344130000e10081c0c005140240c1404c001400046180b0880d5118a4018001240c2008001402c088811296009007003650461500320480c011119481450340d91012500a07030504000c020720996a410804507584600200b07180c601030b42d0307400d100201034464400c1c0c4e040002e040c03900007013 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80190972 1250 80189722 80189771
    0x110a0c061b1505040c05090f01030c0b04080c0402090319030305060307050a081905121b0c03010b0a031b09061401091e0501080c0904090b07030e1908071515030501 72
    0x80b591188a4209200b03001020040d10031203100500c0c110000c1e02c1e030790750341030980a40744a0a921285524501d0320848034110380d445040708200601007048a40c2004c1a00a4114029034000da501c1c1b6440000a080c0040c030b001c0d503040300c80c101e0b20b400141a8542d00840c428a4160100c6000c0da84410401038424100d01c0395100c3c07644004960840b4442640342d03400140c1c80780085420180c581c1c404a41c0d00c1d044440860405d23603080c10030301e0300c00e403003044000105078054000b04110000c880100d400d0843c01d002c040d00d0001c00001480c02000c4a0441d880101440a82002038588401044c0307a4481110206800030b11907040119a02c1d524441c01103045031503611031204a071410b00195940074004010a6000509000ca901e103901c035401020101845585401c07400c3c50f01480140031038100021181c4207911814a650444100c0000210160780100c512911a11149009031802c0c0c1e2032a100304c41715042803903864402c0401307959002601d00c0307400240010700702c190b5224110368083d00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80192222 1250 80190972 80190983
    0x610050d1415180c10050d060302031c021005011401080c0903030313031d09060d0501021e03040302070806010e1b0d0903051306031109060a020a060501060e09090607080a020901110a0c061b 83
    0xc51760710600e030003075005150849149201188459403a00000e00300200740c1c00540032007007281091040c95505001e081618601da10040005504041c210100100c1c900b241c02d050040301070102d902c9042c40300541c1d0030544001d04a81c0e8a2521f4455080b08805042c012408903101c0600c0c99901e0b800b010a0640c0c80c4006020030380969591820410074100d5030f40300f80c407155402c0100a045880132041e804441400c080c45aa480c101703851700911b400081d47c0031a0032074002e0740040c0120440d010a4a8001280c0403003181c05107502c0000701c145100310403800c004280340ac0340c620304240d0004060f000c460110204410311554030241a001c1e221044151a100d1808000c00c004502c0d003580a403400000e680b04075045e00c91540d9440040750003e0b042440411800302c03516203039140031509164441d94100c00b50889061a81010301603035000303001581d40701e8010842160170391181c0b5140d5405400881142c100c3d108905000d201121140985000103d03041a00141d0b8101802054240b55000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80193472 1250 80192222 80192239
    0x20a0e09100e1b04270813080d02060402060a09080f01090b06010f09090c0306031a0a05070519031a0402040b040e090c0901030b041509080c0c01020610050d1415180c 73
    0x110b04000041c60103086401c01d04080c6020aa41895a2a00324021901c0f91001c5a034a4401e500c208100401d2230b07004140507400710104d2034038181e01042c030580160303041d40d10395103c8003c5401a0b84290b4160031201b4148900790000100c0b500c1500281e1000d0700640400d081a02d5400044030040c00303041a12001c90760380442004080c40b581d0250320658010326000400380d499941d403848a000718461010b16001c020203000c001d0700c10b4822503401c010503042c1070b803401d10500c2c8260106a10144450207065445140b114400d428648003014603500030300466030386855801d566580c1e0841c3c01518850303001e9800081c418200001c0003504103d0082085040da861561003072100b110041040700d80e9130342c0708550031421030349014000046105011443d103038000c0113422481c000581d94035504551103102842540000c042803113081c0c4901303481610084689040808922107180f103044c030207100740000f203c101c44032045e007103008503001125498640200e40c43c0946c0c0d0101402c020398080e8a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80194722 1250 80193472 80193523
    0xa110723160e042a09060b0310050d03090306020f04090501081908130f060e092406090411030406060305100207030f080430090815070c020a0e09100e 66
    0x41c2c1c1140b0390302c1441800614034010f054109442d1101410b82480c210704a01441840005080c0c06100c001c3c100c441802c5055142c0200d8103001d2071818440c140c010507010042c00306140c0301c1e9103844051900000150340e82c045043c40e04145078881e1180b644a03502c4c00b000450046004202640f5540c2140c80c422546500b43d100c03225140d100c1c0074005e00c0d0002c4443c00207040200d034424a00208030940360302e41c8a0b0103000130301255000081400340001c42c022500180760500c40800c0f00c40950548800d03490703110044c041401000030302c520b964049070110400003002801d8110200f41d030b10401c00c0da071948000c62290020f901440d100100802c1c0ba445454412a210b103122590190050071804502594109001e8041c0b1400801b900410b212840c007007041e5800080c030708018541d0100500f800d020040d4001d085090242035841000348086040c410342d42c0311144903018244040761482541003400031a40d65060159090407030908002030512001c03004030315118000300e000306540d400ea58 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80195972 1250 80194722 80194739
    0xc0f0b1006020c0303070b250201020301060e030a030f0f0e0d0b010602011b0503061e040f06151803020f040b060a0909110c0a02010806131d070b090a0b030a11072316 73
    0x402021001910849060310000e85440f40c49a2400c230070039000103a40c1e5040c040001c1c1075083d5044407a000e60f10695440001030f90240c10248c800d02c0920386200381401c0b4542c00c0714101c1520b203103503902c20360a840000c10b010740c0304001812902030760000c008084004d11351700f42c04a4480c81420200c2c50510009019007003810a900c10450511142c455000d28200054211085090144c0702c103503036140144000101c00725400c031031611a06000380f810740341c528505e4150301e44c1d00000303000740c5c4024225030940e01c1c0d035009522003410007002c00d42c440c1512107004000310303500d106a003092820450030a070040c5401d001c40c0d13184405034004d046c84941a0b001502d81d0305010300031607000f1b034800801c90390440e9588500c40b05261040c1080c130628154500880c50040700d40c10808128108014400300c42d542e6820744002c941901585135240e0741c034004098014900d0303032030f8250f804600090281c200321017500f80000d42c010307440018000342001d1907100d5444805010b00c03580f008580310144921034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80197222 1250 80195972 80195993
    0x60906210b040515040f1b0503070b1c09030809010c03060311120a080301090603030e0907020c120106090614041503050c01030905011b020303010509150f0607030c0f0b1006020c030307 81
    0x10f009038222001000c2007a200319072070504480c255101261021200100182c001c030381200608140300600c60b150a21000036140d12170b81c42501440d10f030026181c1c800e078400b112800d4200e01044010407402c0c0070340c00c02a182c031808440700c01d40b6518101c08100654024401d80c0b058940024418003401c4481d018401c02c41c0d600600004107205240080f80010311400007107010342100040072a20380d165123400350075070319141503044c4907110344030800c10100d40c001011044000212001d040541400c40e1840c018135050701716400c41800c010380450300c1c800b03c5080080344a810340e81041007084101c100c501034943e41c04010659040245801c28940c8a600425607182c0035074000103030303002101601542254130310381020160f0004001003085207040d030100d81e48070110075841c0031980801000140c10408000d40301e88148004101c5005040c4200064641c095106202c88010003a41c00c1c84100f400781240c1c0d010700e01041510206d815480400d868540f070b8000750045062843c1c90340d0389000f04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80198472 1250 80197222 80197231
    0xc07030e0d0c0b0406020c030c060d05040816060501050906030f060408030c0405060315180108120714060a050108010605030f0c060f0910030c03060e0c0a12060503010c0201060906210b 81
    0x52818a41d10114181070b11003030080c10642e407400d980c0c0d482c140000e4100585004460322a030001e40c2d100daa43d494450403141c00c2c44d240080020140d56502d0010754074040c11420404052843c80c0070407c0051035488503040e5241103e480d0610f5a940080640e1080103801c1080d20390850030100c3c0002d8100d8018681102d20f4110046c1020748a4002c5a038681007110040c01d9061f0606000b07003107003020b05901d40c00135070b100319040180d0f050020503a0354107805c01e05070241b10000103030710051140c2c204030251207070070200982d04103003031038205070000d883d080c01460515483c0020025141c030f00020700342c40c2c08403100d0180190859200801845800890926000300780410103280150303100ba00c0b81c07800041c0ca48000825020108004040b0740c216006800c003512171200b403269080d005400d881c802c003114980040c03622034000c90f60018154076485681c00d5070924854010f200c0d01174001b0001e0700c12001042003241c2e40c4103110843d07910f0310404448190240700200011581010982e64030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80199722 1250 80198472 80198479
    0x306060216081528150506131a0d18020307061809180501020c0607110106030f06020307090801060803070611090603060d140d0909140c0306040e0106080d030203011802030c07030e 79
    0x420028424001c13031135418201d030041a607800c10031800b03624040c80701001c0c1200f0303682c030b604106050780154820484c600070410742e0700e10388103618183c4003514100c40d98006a6181400064011742043c07200c001c04100481c868010400041202031040000c03000304030304071458000003840d1000110013031051004120120f562a0380020201c1c0090009000d8021a807004000134a40300384000d0607a10301030804680c0e6410700e00100045141c40380d10780200d60700440c00503034940b150070b01500d6091031644400c2455007040c500050007003000c0050144503002d02c0e4244000f6031120402291403044841030b0340d01910510214006080070701480e20424401c10030180c1c600c903008001442c0180140c9203000199200b0401c2c0000ba5039800349004240b0040d07681c01c15401e00e9014030f11a030000500d02b5005680c0c40f44940311250f825081640100f4010043d41e41075007011100034069442405074180400d1a0212000c1342c17601c40c42100d12405d420aa444d0a02c2900d941c100c03802d40040036a90303070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80200972 1250 80199722 80199751
    0x50313050f0708030a020f010612030305060d0b010803090f0301020301030f08130b03101802090a0e0a02071712061002030406030507050c060702010f0b0105070c030b060d1203060602160815 83
    0x81c81d241040310001030400d0100850700e070300010340002c2ca807801821030760800d030b4100a0100440a41c3c0402c501c50781d603040c10041410b0780c072500480c00001e80c6140c0a82405040c2c40009110b040c003200400a08106a91048400344001c06040c01d0380700a1000600c1c80145005c0c5e00c000c43c008402414099500c0030310780c90401d96444010742d0580040da00c581161621500130010070030540c031160900380104009500b03080c403000000d050074003503100d803100013107002d00080c5800d03405904a8074200da02071140c0802841310341c682c041941040c0300402c60041c45901113210344c9408040302500c103a055005601d0682000c10480103894040c0183c010b00074103009640040300240400c03403180b02a6800060340c10300c940ea0050030707240003100c0746050050070400300300400d404400400549400c204070300c15540312140814601d1036840e5000d401d00c40703031030542150954140c21200440d00e55608a410a0f1041e80e00b4041400061141c000c40707512200e01300310741142c0b0266140d80074800d91039010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80202222 1250 80200972 80200993
    0x10e0109060b12040f02120c10030614040509010b13090209010905010503030f07020f0a0e0a050a05090a02040e07080a031205060603070f08040201091e170d0e06030a0207080409050a0f0b0105031305 87
    0xa01640d900c05044000c0d822401c881c002c2345c2000319406541255030301d400d01c4038034540b0070800c01344041034100e03a000c0c0e9240c030b00042c40d60f0001d402600c103100c0040d0507401c03215400c100e02001002030320012840f4071006000003401c0d00d03c50042d18181ca8008015502d0440352804c01103841e8042e60b41240c22500b00c0301c0000b00c0f0b54940402e1001003642d0000705e02d040c03034801d44050864000a0040000618103c140200100c00045520030154103560003d940d640003000c83d40f60800c103a100c03030428031030414800d082580c0240c51005598403c60140403a454140030041035000403a4014001088141d80604081c4900711943e0024010b0412100c2c1d03d40756458101007500c01052540018654081009040c50384060783c0300d225148000790450001c000001820100d4441c9a03500c00c40703002c8040390300b102252303045499641c1e0296110b6980d5541e10302a001800003180c08414540c60065003c0d00d2119078040d800100e001613694070310799503405408501041848100b5501c9118008621 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80203472 1250 80202222 80202229
    0x601200312010810060312050a020a08190f0503040206070605060d02040c0206091e0d030509100501060207050a05030303070c150b06071a071403010303030b040f020a08010e0109060b12040f02 84
    0x4080c0c200c41e12500140940c1090402c3d45030113044190081010300c0c00c20100003041c60390303c98410041c52031400e01d65450503002e0032840c04c202c03001c002c0c00800c3c00041c010314900c865682540d60301c02c1c5868162016850b5042941c190100716000780d0044810400c00c0001465540040c1c3d1048004100c0c00049010340c000c10700310742c2560081300150340800c1c28842992020080913140c44032901c400c85204442400c000d0700e40b038801040c001415200c0001c101e071001f06203c2e0000c003610034002001290781d1100c0003552034280344111070054000782d4000c16a410080112445681c403500c610300c49401e25500d40c40d90f900c021072281c0c145036845d260b110840d61800c0084c16214004c18141040c0350340350030f41d040c0c604070190071f0fa028401410003c00b81d001506048d00e0450b90541400654500202c1c0418041d049002040c0b03020752000400c0181160002d4003181662650490401c040e80c0b500000812502c19010740d00d40c44605201035504004954030695006c0d1003008502c0c10b01110780e020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80204722 1250 80203472 80203477
    0xb0307090b090619090f0b0a05040504050c2502090a060b0a1d0a09020d0c0c0213090c12030c110102010204180b04060f0e19110d05100302060c0708061e06012003 71
    0x1c4d20010385400707804c0204e041d44400aa000d0041c002100b86000303100f440140c09403003030b841083c2c0100c0d141c4000404039a120300c25112104010004d060300c0b15100b14400c03d06007102d84040740305290100205002034103900c00c4105031a0070128113071526800c6d100035100c40e502811690070041c420150380cc6661141551040103105404015846a80c0e802c07041064030621003202080011904d0344c00e000d651a81c5001d00100000c9400103684452030404000081c19074018856451020350007904041d80002c15038070841c00f94840420364400e00004a09030302c601e2066403042ea4041803003e01c011300c0e46e8002003401c08000c1000861650f9007900814403c4150b000c0001e8141440410a410400c1011900f010444000c03c000c0102c1e0301b010b2601c0380c00ba084040900ba0b0392000091011580b0011150155030001d00f89a00e925494250580d6500345001c4c0403a070b8003a43c004509602000d08140c100b4881004c6a9809503a40324011a402c03509080e184100d40411450800c2c1c40109000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80205972 1250 80204722 80204767
    0xe030406091202120d0f030e0a0b040b040f081902011a03060c130801060915080303060603040809010507140d0914060406051c02040b0403031b0521090a120203070b0307090b0906 78
    0x1c0d0344000070806e040250440310031004410407600205203180c00200c2c1c03001801c3d0b0150740443c1109058983d070400a421310169070300280130310400501200c00e041000c0020a03071070308030703402801a03103d8102c0440440c0480800940c15500000204103400c150380007400d1650b9001e00010400303030381d5001d80cde03007541c0d80c03130740300d0440700f0f82c0c42210028452140000c98080c000800c000c40ca181408400720303043d480014809800d80ca400b080101140c3c0c8140c089950b01d40e00702c4000580c1803003000035a030b150500119080081a500240000d400599088103201c0710380042400342454078010701541e1681c06014100c0200312030700c4a001740c2030080c1c405840504005481540c0701c9040d40350140402c0200580200a150002406000540300007030056007141c2d680d0f48c002c0d0450500d400d806807030107001022544410080d002040e42c0781280680c4001c14004c0707048401060340e0b0711980c4041d00c0700351413000014600078028849124103070000d20325440003512103481d10b60300c1030a000441c1c103140c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80207222 1250 80205972 80205977
    0x2030a09021c061103090705100507240501080c01020a02100c050708030d200d0c030f090501020c07050d08030f0403051204030806010e030304120204050a0609140a0e030406091202120d 81
    0x40c40c0401e220f90740c03040344186140403a8191550504200240d81ca0702284a514424445040781c0c0c0d070b842e4481c200750f540040d40001145060005000a10829182721000c18071081c03800c000000c49040008065801c43c406801406500c00d1a0b000d1010701d00442c85848280501c103d003090000d039007040003800624140000c0c5483d080c4d071000c080c043d604440311250f400c6000b5900c081d1800c500200710b500400300248001201000310f54298050302c00d4200030400c01e0700e0410074030300340070041d002811049806010b80f0980381d280d004010b0301030701044014000b18000d00002c3c000205c105402a0043c0c02401e18904007806105103c05203182142c01f2400902d66105020f840e58010510803074482044020b5030825003498400d0811210b5004042d2003241c503040403032224032056000001400b4140c00a0001c0032064101400340001519034140ca1031822820705840c460100a5030700380c8010f41c1d114000ea500e0400c56101c2000400b000b80c3e8024502c1c40f11480c0030804001c031000c540800d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80208472 1250 80207222 80207269
    0x3030304050d26010905070e090a0204061101050106080613020903030a0c020306062e05040305071d13050604031116030c05030d090b09011107081005060a230402030a0902 75
    0x1a0001e10030444801e501c1d100c0042000c04203204481443c005040d18a00d540004840d62045800c50381d0702400b43c0620340012155092043d0000e898000700207548094688202c4a900c9804040c221071091081b80c0000d030054009c10000c0c80c1c0042c0000303d28038a16000340c10820300e4000a0b0559000480e0480402c50002e0303607504505040c0203403944440e0480d16281d403803045c040003529a9420131010012100c100302601c2d081070042080c2c1c3d0156800c51304407680c103503c0d0001c80607a00c8012500e20420310070900010b0900d4054000f4010241c2c3c400b0141405440c1c0d80e8003502c1c480041c5680d1a100d01440c2c40d5036002817801c403025002175004400074070a5030319000c1414104214031039040108002003000b404118007000c21079200d00c5080c0b8024401c059240b1b070fa5820322450350410041c40c014010031034a841c046400143c0101012260003298907170740c500c4103840103209944640003e0310a20707913404030f113442c0e0f003e03541c44039001d035022030b41c2d404590024841c4410300e2140c8140c400007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80209722 1250 80208472 80208493
    0xb030c160203030705011505130c0c0206090301110d090b130f02010309060908070510060603020909150105040302030a0507060e0f01081b0910170f0714031e010b03250c0b150303030405 81
    0x2039241201500344644200918003894ad03008280c0000ae00020f80110000505882142c900b5840450b01c00301900c03516071628071151a0380c015181d5035000b580c00020701c102151080032105011400b07d030740881071421010840e40150040c04204609803082135403405020041903c3e08014042d030b40c03049010f071180501600350031088405d02c1d0880720030588180136812954407071024180c1c10010304040c0111401095004840d64811904025094011200103c08100000660000b0384005880f000000000d00302441031455a06900c50700003074000c008500c106c0c43c9085600f90818241c1c4890380707814448070115a03a406025031102c00500411084004061940106500034041c402c03000840d0804040040c0001c26079029441d00000000200301c52140b2541c0340100103101500303a00b140e60396404128002c0d00100c82d43d94401c008802000300d0101494201c4031301900f07030307142d90140c0b09403911042601c44000706080300070508400b000d1a1a64100091449144144010481c5010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80210972 1250 80209722 80209729
    0x70b19090609051302030603010f0905030d0b0612070e040b100504050114070203030405010503070215071d10080c0d0b13021c0203010f06121803080a060b030c160203030705011505 79
    0x2859032000c1c040100024060006035984c94a440c2c070000c4040c0c0c090b80740d0f03c6a1300002d0042046041000d90140782c207a80340200300d4080054010796840741402c1150f040c2030424402d10f8030a86403c10040f2280c8000035005a00600c407960b100d1001400000d916011031011540310807044580c040032980204040003d90780c01809208403418210000d400c0c00c002da030200350b480c0258000c0a0511801000240001d032081200c1e0010a40a0100c8447c83c100494094811002550040f5414802c400284a98104141d40441c101c903190360303c619035a200c81000207550440f2482c007134442c0d00c07030522000559400c002d0b60300e101c140ca0001a03444003103400c582d03103030001300384500d8500e03005100411200800c2c0d4001c908940c0c06007804000590400c0399a4001c00c190a11440002100719460b000e040d403007140e861080b031445100700101916030041c40ca15010464528941060400c010142c2c1244066446051440a000c07613042c10840d94816003940c2140d10400311b82a40d51008010303030f14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80212222 1250 80210972 80210987
    0x2061306140f0a1116080c120313110105090901031202031215030f28030e10020c030f030424020319050304051002090102100b0f120109050f0c0a03030809070b19 71
    0x130a240c03a458000201c10740a909892440050001e0b840440da0015101e800d000c0b007030b50750170000216556440d01c0c2603000c0d034580c01c0107402da5140e842800252403a5001c2d504984401000824541050f032940e5600418010340324203a400b1400103004c0d00981002020764030b07025102d06501c0055440b02c14080c075203407610311003090480c2d510460781d0080080003044416031503500788101c1110084135040c10340b00d141c03001c001c8076000118448055040307a80440d00e8070150804a050303911804030358004d150342c7d02070b6014124004c02c0515010b0f03645180c00640304981589030041d07a0034405800c100c600c0f211f50328a0110040f400010811082000c117100c10640714544500450808859400013541c2d91240390803408101e6440b00c0c210b03071301c0e6251a4010815180200310003000b41d0100105070203440d0720841218248a00644100c2a2001250ba864140c44c0a44204c0e0410704c0e584045400070006480d50116011746440480e02004502c02080d03030b030704121030100381e10810102c02080036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80213472 1250 80212222 80212241
    0x71401111606020a0302040b0f03040b0f0613090609020405012306041401080618130c0503030f0a120603050a0c05010206151507020a08030a0e03070602030a02061306140f0a 76
    0x1020304115041180003082040003039150015030058803201401c100798002d02c61034014004074180420300494555095000b0342c8600d107e0100e400b031035145c401072800070308015039003141e00c260500060300045189901402d81d25015030804102d092203500428100d80c070070b80004600c43c034180080040204440310825a00c001920418500391921300e03e0060407040082540c108100c08012428503580c00044500980c02d002110b11f5509141c0403502c500a000007044071006440000026140fa011083c0e900c490003800005141c02c0300c94400b103a90391a2003200c00c03055540c4800103c04280104032914010b40b04840b0440e0032420040007911300300e0000e0210b142b000110700000c0340c2c1e890310000d4202e90f02c0c004456540754043d5200040342c00302241c0140c000e03071101117101d468203541310300054100710042d01175507611512090201d803030744165075921001d07034403444c00300b0140025596188120360003200700140280021454140101060302c1d16800326003404113000c200c150510034080e46 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80214722 1250 80213472 80213501
    0x604030f0501020304200603181c030b0f040b060711060d11040e0a1514010210110409140f07051806190201060807120b1e191b0e13060803071401 64
    0x74810500087c00d901c00200611818802a01c91004000701005005508000c5240d1072200411503500100140311144c00c4512408a018040106080c50702c5040d102040181000b442c10003282c848402c2120440b1005030021020808503580072034038031420405981c04201c507a51a490040c68811040020b840c60440924000f48400c0700400ba81d4000119102e12210b9015a40c0c0440181d00b050081d0400c003031124181120a070400e0f070040001c009440c5d866404001403d10070700340f84e8081c40304850a0f50440d000c0e0b000300b00e00c0b0303001e000034108442c1201b44238010241d40c1c3c00440d0254000910504400030a52009546150203000d5803020340038950040a04a182c000401c000518a00c400f8280e041c5000c0454041c285000c0100900b1351103a0400a0a08040142241c108000000501242d107080030120f040c20030404400101c0660b07581d0320a03140c02080c1001003007508054802c1c1b4031540d1303440000b00507000b800036040c101c0c060f0482c0b42d041c841c0c04804500351000c0b50305c040c89 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80215828 1106 80214722 80214773
    0x20c07170607020a170d0b1008100b03070c031101020904051009060b030112031d03100f0e0105040302120a091a0301060219050c0d020604030f0501020304 68
    0x18980e00c4000c403980ea503035544040341c84e0710b928a8010000c2507807541c0312401c003481802419030005126000074100d142d410000c3ca0304a02e400c4c0000120340310100300840c00180280c103000500c81440360a140d40350552005000a941c0d1070000d06200346070b0182e90610000b581510b22450018100300a5030a000e008080400090b101e42802141064008100094600282c9041b02c03040207546850a030b541c2d8003607408401c540807001407402d41100c089010345c0d04100703807000e03070095001c009498003044462a040c3c40b01001000c074282c0c144000c2c40002540010f20741c0c2a0384c62140300944411a090040f1003003209075011b40d10619110f030392000f2881d2202c00450403600207030221100f8900200080c0540d0741d1031500504660001d20030311074a03003458410342c010948010400c0d4a4140c4a83d2800c41080801e01c0c1070300c060307501004001c20045200078241c00c010030b0360031609 = true := by decide +kernel

theorem cover : BRFrame.Cov 80035972 80215828 := by
  have h0 := BRFrame.cov_init 80035972
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 80035972 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 80035972 ≤ n) (h2 : n < 80215828) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
