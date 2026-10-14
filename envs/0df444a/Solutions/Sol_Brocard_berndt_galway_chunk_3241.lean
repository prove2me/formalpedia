-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:54.235024+00:00
-- url     : https://prove2.me/submissions/bbbac5b9-1606-4187-ace7-55aab55e2ffb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582733812 ≤ n < 582913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582735062 1250 582733812 582733841
    0x4061407091e0e0c1c0615080108060147042d060f050903060f100f051e1c140114130602130905040605011a18010f05040504050405030a03 61
    0x1e42c20400a64150122075001402c0902103403120811103c8494206400c03407543c0c4018582400440e448054541d013800b611402e6444d86d00d513030b0700e540b440c0707503101c2d02070240da2401e2100c902e003000348405079920071004424038203004c5950191955580180fa8042503e502e4041000c1410f0108501d032000f0100f80e814070f07a01c00008440c05188001c8144141c0c0070386420000015a00f0386400c3c0918121182600e02508544692600e0042402c600c0c0058481d08102840e441000076601c500307088003020307940001c1109401c01c03900100e47d8422940b000e0700541080000c0c46143d880305035030b0050342c400c6009644411541d103031b0f4004142110040350b40d03080307586d03946000d01084001070f4842c2042d2541c850700050303880c0301c82d1080c00151fa803150b1200607418203100c200410080709400460407100b0200d200041d0b00d42c0c0b403151226034050405003482d1240325180c26001503100305092a5451040d06040740350580780c80224060728000c840c00d4034030340e00015001c040d8550510039441c84101c4030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582736312 1250 582735062 582735119
    0x30813091b080f090a080f09210339060402030105010f080703060c110d0e13020708030a2f04080706020706050304030e010203130602060405120c0a0201080406140709 73
    0x1c01c8081d00091028050032036910001001500c004030070000c103401281c04c6503000f501c5a40d48061b80860f0350042201c0313402220103006215180c0211035040c610321205401a5050030042c001000d00c44650354450205114980300404012100101861036140e1030b502900d4180b9040c0141400e403a41a840020032201031002002420008158401581d611660104070204117420884288149240b0b00c080b0380100402c0b240b0550300904662481042a030301c03010a1044404940d04030300135100c3c0a010120104006181200c00341d1003e084510f0002041c00105c4544028101290358038205841c0034000140c01e100e009400c1040038000e0409200819280e400e0100041040c00b0181000b801e0090b0141c0342810f90380240300791502c032803094510081d1036554981c000c2d500c400940f4150343c1800b50120b010038a000a100f21351420740755000510f00303104241d004540b01140200182e584a964580002040000b152402d0081026696010081e81840500c080e1b118001c41200a020000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582737562 1250 582736312 582736361
    0x121b030b030c0109170a0b0c03040b0a0b060d0e010f0501090204030b010b070203030a1101110d020403030e090c0a0c060f02070803070f02030c06010509090c090405101a030a0b0403050403081309 85
    0x1c11429005d0b02d6015289501e4900c1c2c1d42c41c0c244c07510001c124000c0c031207003800080101540180018511460085020b40c1d01034581c030320810110344808011542100c0308120840c2c645400c0c1e0000c40080840100004016408040c110102c40080c0c024104168000030b0410601c0700c1c0d4038105015012215202d0b00d48000d44d40000d40e80d1141c0e018890501c2846411100c12940c2903000c100c504202ea140c1c29558101000384600035445030204401140781c807401c0407502d0600c40c0c02188134a0401544602d001e000000589442c008000110b8201385c648581c841d25a0903800600b0001c0c0c818045203440c1d0a20100c00303000c030412031079850110340c0203110001040f0000240076045440030340d50103030326071241050035050840074202160042405800d100c1040b00020702032a090740c1c00e00701000041804030f000212080901025540b580c81449140045207010650030b0708540b180c00c04c0c40c902039495581c032095130040d6105800d1800250b4040000c104035005c0e204080036101500c0801c8040d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582738812 1250 582737562 582737567
    0x240a0e01080907120804150215070e0d06020f040906030606050a080607050f0703171326031503071208270904110f0d0b160306060203030a0b01121b030b030c01 70
    0x11113204000e440310784c50040d201400300e036404440c003070240f49038031b40d42a010424000c1d54584950320b01111000f051070002340000d2140c00c0074920618001d011b01c00f20340316600d68002070b401172050381c0c2e100c60301000001a0340d8070602c9503100440c03140d04080f07449441d12042246010160344520700c0750300038008001c2090f42c484211004002001c024548984107810f003140d288060024042691400074240301c050804074001401c1584200e4080000b10f01e2031031800402d01c100440c07c0d00c80703101840444c000720700c41d21107140201c0b40a422148441e5075999030080040400d6010f59010000041c0c40803042a45007011003201142c07128400f045050300c02003103003800020307c00b5201d480c03820340343d4486980d00380307150540c518010a403030102842410480c581640950300b01c000c46070500f4500c03580c1402402800d040b070f03d81360051070542c0e42c0d41d100b4901500302150160304205090201005c1e020b1184222074038055004c0c03080b221449009406802c481e0746442e5070b0300c6a848402c810b11342d6039 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582740062 1250 582738812 582738823
    0xf0305160618120303061503090204050604020a0c0b180313061701060e0405150406170c0d02030c0d1b140301230c070c0312020d0f030c0e010c02240a0e010809 70
    0x43c0c20448449800d60582130880091140303801052035200c00c5450001e0695050300840b2169008940410554071a502000102d110707407070542000c18405c2282c3c50100d41c600e8030096002c2d008421002e84004140704150440d03015560303038030899001110a0080c2580b1000712605800740d101c01c41c2042d410004042c0070404814040e61241d0303140c00010f6010704200341e403210401e90180050001d1a21504414035503400f820043c0213030711803c1001c400c2d42c50005140c260554000d0003604c1c8540b02c0405000e1040e0303032450283c0720914452150401841e1786140c11000345401ca000356039040401080500303607103041c1c5403401005c075a14280b4000d140000a05c54100f00d5054404c0d64404051601035401070b510780c40075010500c00c610290126401081700d17488601c090341c640c0c00324840d142e02601103d11110101001800c120000c034055402078114580d0135000900e40b2095000044816a100b8500860f4404441000c50300e403244c05e07008005038107182805d0a10280c0740c90302070007031179591 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582741312 1250 582740062 582740069
    0x6070905040507030b040606020c13140a020c070b07120305070c02090f070c02130209190308250b1602070501050f09090a02071b05180c071202070f0305160618 70
    0x1c9994078042103069001c1c2c0d001c0c02543c24094014080d00360340390006501c5e40d00c65100103001e41080300c0c84540010152146003501440b20304c0c0340d8415181c06610f81c000350090345001a4502c170f444070100782d4603044406070042d10b03ca48800718800a8601c401001e4420103466103040c41320300b00000005903140c510b52035001e90b03d001d01800b961b642c2003044950051a00d00650040d028041400c460321082d0010318601d20107985a280b031100c4843c2c05140110503110103081c000c1d061203030306600d108011070707410b21510082c180201d468550f21820b48084042e503202c900041c40410010700d9580500091000305802d0030103c2c01d040c5065403540c0c1034443d40c4900d6200b205104c000071102021981039504150308401c800ca4582040000c1e458000b0050250314418800740c0381d5112340038081114a84684049a10300b82000d0007582c8050a210000d40c1c0340055004613440450721410802c0140002e50207440204041000e0b4014070b00c0f400a5038028104210f443e43d0002c0492801010030400c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582742562 1250 582741312 582741319
    0x120604060507090f1712070f0609020d060e010b0a0b0901050d1508010603080c0601120c05040f06030203010507020a0b0f0103051f020d02030a06170c1e0415030305030907060206070905 81
    0x30359494110407240c00a0f00d4000840003464100041000030110f04207841c1600d03040100d540310b000e030740103000d030034010800014000070014282c5000120303650040200316201801c02190100c05940f04c405841441082c00c6c401ea41d0350316481424602401c5040c010222480381038902108a800241a8420301e90080340d060b0f00c17142c424008000e416401c1d001440340b40003c00082d0340300c0c0380500c42d55110f000403c14a201e11400410010286a0440103c83e44600c0c0d0f480f940b03140c00c040c04007a040b444078500200b6914000040561428068148200c0302640a8908480540b800c448124006401703c4880040310005100040d8001558100344070805240030254140e403440c3c00103407245518a0804600200a206100250f40c1100c8252600b4041d40c500c0d01029240c100e031703240031b1006000e5200152001d285400345140500b0060a80003800224651004401310602c04006034411000150000300700f11b41e041e024030010001c0e240b1171003d00918141840700030610000303809508e10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582743812 1250 582742562 582742571
    0x5060709030c091e150312020708060414010207051e0d0e100804020312071b05040c09090b03010b04090809090c120c03060402250302010e010b1c05030c1f060512060406 74
    0x280c06042c0810079109840d203c9040c44400300d4480884242c2e4546e00c411205c00e0090282241c0442c004208001650181c00041025940f6070301c400c1800c224003201c002d060756003044800c0101d41d06000d220003018600070b1002032a002050300368074180f0340b0700984040141c120072205c1d0070740d640591000c10b140c55191048841d03c1c6c07030001a0610301030000000008c440000c00304100300307000c10f444408000704c0d140c0364941d590710401e00c02983c8015461100081c050302c0244111040390780641c010060280001500d143c40b00c001c0303001c82d03500800589004a022600444070700c1e2410748140d00a407421003843c2031802c41e104407202c1c21009810416428808000182c82c2d4403280d06907404d240706582c4081d801700b100000c0301c04508034618158015420002c03500a00c540502031071250b420b016110260b0703100f2a400414080d00780340b00032a92800104480702c900e80c01017242d82601c0400c00402d88046800072100c004544250b0300c02409284115039000041c44003141c001d60241c0c1203500400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582745062 1250 582743812 582743831
    0xe0312010e220b310c050f0d022e0e0a0515030109051308030f0405161406030406060e010e07030e0d080a0b0406030c15020106050a0e01061805040203040f05060709030c09 75
    0x1603041c0c3c400c1012603106868441d044c112544000301c3c02c10150060b09440300031510382091013180e845110b8a65004003111150900606245041c42c01540c035811480781d00c100c1190220f050561214031000014003000d0070018a458998180300003001e080390800c4921740006003090441c0414403a11180355a0b13500010042d003102d0b41100c4e070456101c142c0725903034901826602d9445000b500d00740c2e81d03446804a007507903194140032a0420b075110000d60500144054041000541c401842120070f55290a0000f50040c41d00b01418042c1640b5240c20714940fa114100808032002c0b448500c043d0350003050b0350145034dd006000550401c100340001300c0e01820120120f0003900c502d038030051209040740300018400c041506088103141c542d0780280f00003030340da40400c03810140d68000ca07a00d00080741c0040010038010807014030f48151002c601c60a4550b5080082e04903081203900307071171504001100800b001002c0c0320080e400b180504086003c642540c4400700e00c0c0c0064010414065034400d03a44 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582746312 1250 582745062 582745081
    0x7050d12051602130e1e071401020f0106171911040203041113050a06120b0f540c04020a030e0106090902090601050a05030601080a0e0312010e220b 65
    0x400140e802600140f80d904c82001d80100801d060004052507014804c409107039052401c2032030414191410080c25014241440f5040b588007807008036056105240104224180c00e0080070003c00b081c0b40700c4a917103404036140c141824503d48903081d00e000200308210018640d050002c418120544e0016103d5a60f0301c5c003213014680c2c440c4015880a49030420402d40e048c00d800003485851202c409004c51542c9901c0c58820401c034040c01404060790500141c0303031074482421154003500c941e4208051280c1d20342e01e403882540e08a034841e90920300c90510076a22010780342d403945820000314034000e2400d8060400d0b0312084001001442583c0029110003124400c0d080040000300c140c2c000c01c66503076100103060080001100880c090350000c0009102036001e0030699220782019100d0070b1865640c2c000456085400030034050703041d84d95600380c0310300032802c0016102140042014602d294101120a09a41d000503c01310070f200341d2141400803609218100a031076540521750b40c2054031010000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582747562 1250 582746312 582746347
    0xf10090201050706050405060a060f030206070204020a051c09050c0906180907080d210c0504060503040c23030c040c0e0607081603020d030e030a0c0f050111160507050d1205 76
    0xf4104d45c0c01c00c0140801e1080128860340103c031018810060280d544001c00211020b80c40040e50211080c4000d2015040a8000b00120005440c1c05454507400030100707007100c41401c0740c85002a40d50780d0707001b0811a04010750381ca192012621022140380c194000f412440c001e03042070214a11035004241800130030041e034070150032400142c3d03e10500c102401040c1a05a6000c0310f100741e40342810000d00303a810710810040c80c031143c0d991380c0f405017040000d541591010f8000c03500b0200003280000c0305a0214148039024411a040001a40450041624120340c03004060b00c91450b24084180154104807040b4850300b041e14001d07214402810300500728014a0790b04141c0481c10312078001003650100e0380c0b0442d041c00d41c03820001404806040d950700c0c05851b4000005c9800b07410f0307050204101485528034544140008602d0620381100301c001c40d000341e411500070301151601c0c40b0030000c09003c5100074003c162901d04c10300c0c0c2d02d506c0b0320000c04507260300f00c010b0100008010000481170b014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582748812 1250 582747562 582747577
    0x2040c020f010509160e2e0302030715030b0f0a18090506100312080603030d1e0c09090c0203030f16090e010803040e070c0c0302040c0210061d090f1009020105 70
    0x200154a03042d8130300341d00e40c002c0c080080c440c1d844d44400441c59000c1c221610703010310301c1e026190451000c641c0c1c40d0809043c843c0328040600015080002c010b030781c00c119070005011040200c0140349100c2601809840c42d54014a100381c8192a01040b90345664041c1d000b214101c012941041c1814070804004000300c15000c0c0090052000700080002e8a82001003101d01c40d0701c16103144562400f0466050b40700b41d50555040d0002c001060166216400403400c020480002e00c41c000c4a201e503503403c441c149010540458001072041100149601ca1340d140d805290001d189586002103a11030508001003980244d0042c5030189291a889050164054440400c40501c2d950319403010350b43c0d0340c1140c07282070030302c428a42c0040c000510980e03080204035480501c2e41d045a0869003007002801c10031030680c04500c10780d40500410700c3c2c43d0248038000c0c04507803410075503075071411000b082400b0001c0a200e0180d10600791005801c60002e00d1005000c000040080c4500181c80100e03000c0c429140c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582750062 1250 582748812 582748843
    0x1c03031e092009070e090a0204080f060106030c03020a05030a0e0721021f0503071101201312020915130203090f0607020c060d0e0304030c03050304081603020a0302040c02 75
    0x3803a07101044910301c02500b400c079885040d00c042d0038542041101c001000c5441000040501c0451280c900300a004503030000500f103009406c1030388030f101880ca4480071400c00b1030140d014100401c0303265011703c00c1111100c41e9203010b41c50003400420103042d40c840603003c1e4424668800b14800d0620b81888080064440c00e18803046a161528401074000d00d994820380c072070900a150500e000710b11000d2124040040d844560544d07a4102c4280e0300b031494000b44150954075080104c1c004140554071a940c0001130803000c0e2220f0034134968505a0541e904850b816242c504400d0016951741c00c001a80f004a441c82e1070484194000840c140d10b1001240f45071650002c014003100c144046140810038851100300c8060b030380c80000032a5902c5a1103142500200100300c41c0f031031011143c1083c40c400c0400000c681c0b0702030b9640d1b00c2100ca000942e00641c0d0719080860107110720072052102c1400c1c0d856840d00d1900181c150380000d102d802592100901c15991120030350032841c028031180381130b40000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582751312 1250 582750062 582750071
    0x8101511030c010c02030423180a1419060e2a1204030c110406050105030a09022808120307020d0507062003090c04110a0c150203090c0f1c03031e 64
    0x18080a50b480c0c201e40900c064404901c4d8036101c420002d450020003448e40100034460642c1d12840d1403c2003030f0060301904120380c07a000410021107064400b94080e55690300c040c3d290312501d03c415400c0f1152500b00d1b089520b8030700288103030b0340c481c80310100d20030309400d8500c00d0072544043e48103518440d01c1990b48040030307110100030901d50031070320114507036000b17822034680d07160302c20204011190b440c082c82d404108140003180f6050141d03800682c5840c4081c000d11000c08009088004200e0041a148583c2403082d0301844452824044080d074480480c210a0031802c4c2810065290411300020700304000340410801c05206554118550301d0350020307030a10340e0f512620034458299208482e80e880c18030641100b00304904080c46800d4403410500a0503082c048248002c5445801049042d03450b4104640c0e420b50203500ca10003107005441c107070014400090403106102240342043c0306030f88a8000a146c071a02c10060001030341c10036a241c9000182d0031810301ba201030b00140000c2080203185071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582752562 1250 582751312 582751331
    0x3070b1614010f0621060f020f030f0612190318181505010c0f0206070204110f21090d030c050f160203060609190207030309060e010c08101511030c01 66
    0x10b40c810b10000c00143c900b804966207070603060035081200a41d400701e441c00c0b440504003103a440d5100662201801801501d40300040710254802c0d00241d95040651420f0002d0210a162000c41e04600341c20040141c92105003c50a410303c21480c560301505002441500851080381824544050420003c090300300c1100d01440c5401803d21008481c14030701501e01c0860298012443c0d8100c0c9a8070420b12850600d4913800e10a0035001100200d03082502c540d0442c00c1c1d0590344000d044007150030740d40306851f0b088050148003050f000304050b02496102c1014025009804900300c1403440c0329040110b01505e0310541240c4503c100d81c6000150700011404100207a0140900840c0038021011114552540c0381007041249050341c281d20602203510098491400c1500680a001e000b800c0c00150745149480c0c00f0181c8881ea814036011f0b9646044800aa03a0800e9040f90030506011504503400c1c1014000115911448000c40c188840b04c41c1000320f0600400407551031412810007813010303011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582753812 1250 582752562 582752603
    0xd05030a02091c060509030c0a08070809030111030a150e06040203041112010e01060927080918060102060f15011803080a050405010909090803070e06130305071e0503070b16 76
    0x20440c43c11a100d6040030003107500000c0c00410b0301d24480f0390030040c1c4a800c11580c3c0395006a440590215602d070414000c40780300303075407c0c860003c00307000031108580d0380e2901c2c18460007240c01c100c041c0d21510311030b12414004080043c103000e50240381568010b07566200c900300301124214400849900c2000d01410245024042d00012401c0c0d0a4400070701c1516260300d8040d080e20309651a008200354400a559000d01407003545150050246901510700759910000c1044210140b1066a50b0307141c45040c01482d50f81005555800104009601003034280603c040d80c2c81618050018104003841100c90b44004820480d42c000350b0340000595951210101c000d002a08a441003d0100b40c9030000080d0f03040c02401188002e5074046181451551082e03400d40d095030343d504c0d03090341000044c80b16688c0001540c03001005980110010000c00f0b20380103140f103400c004510044180f00c0e064808002c0c58400080380d0702503803500003803a03844540886200288680030b04000e0b1007021100c1481d04c403c3d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582755062 1250 582753812 582753859
    0xe0c030a1d0d03060608010305030a0f09080106081b010203071113022b050c0304050a0605070306050d0f0524040605061206010e040c12030e010e03010204081510080606030d05030a0209 81
    0x140143c41c180041691100182c6260400b4030002c0c210f50030802c0b02c1921075100c0d2017003410410079401c2c8403440070389815001e403c44419401500b10b0794400f68000c01c5060603841c1748200180248011450f155040d41c4130400315146c825001d0040b5031000440350381440603015981040c0061002c2400301d40e4001c41e500d0792103040341c406aa4030745000081984255020b003101c1c41550400010180d2021940c0c91340018903000340090105992011301003400d41d60303220b404031528028042c1500e03254480c00d205007494041c0c025100c03103a030956603e0780d03600c0e400c40455038820b410030310004072560782d01c010526088400c82d00ea85940652000860b00c8800e821803a8003031030003103c0709000b15890300c0050040326203006020f00800c1d01030724918000c0d80b09001541301d8550290015040c103550f8100d007464840a4408580404420001c000c0c4852010800800a110a000038010b030300f448400700e038451400d04500400c000d00080054035560680d01210364040000d0072401d940900d0040c2c0c2c12004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582756312 1250 582755062 582755083
    0x2030c010f09110103051b0d091707060f06080a0f050307020604030503030912091f120518010522020d0606030819031b0e220204080313060203040e0c030a1d 69
    0x152550f0034403102c0754424464244188000d11814200007007140d000c80b41a0842e098074425142ca601000e8000f0300d0000c2c1c043e2080e92603c02141d00d0340c419140c00001c0d0b0340d522201c4541d151410a00b0400c0e91000500710340603541260401c0015801f5080c400c0c00e5206a10002e504504001000407c01000000030f6200d00a440305603807485c440d00c075000000b803040d2084258098041c511840107166050041ea80d04003480c200844058803160703211040e40c00850302e00000c20a08421a1060b030400e0040310b9100320030320b58401030403400e91001c401ca042c0002010703000d07108035840402004440d82c40300000d1500080015200e00000344910041c640d0110b800e00002c0c00d2103000100f4511052116024a070542c07030322800c82300240203200e107900700c064070300a2282c41000300140d110310038030040018121003000385d65a440324002d100c003101500da02100841d4000c010400485000022450300704001c01e8015603a82c403412168000b4088101c02b9015080c00241203d0030309100081d00c0b00d03003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582757562 1250 582756312 582756323
    0xf12011410030204050609040b0315070206071119060506030f100207031d0904020603131e02150a0503010e062205040b0912030c0c01180b010801060902190e0102030c010f09 76
    0x4a1070800007101079005522480303410407014400b403440303071900c1e8202512002c1c01804039204a808030209080c00302c4161442809a0401c4041c000000d500001c0e40700e8041d820b50040510710fa44070441c0f541460340b62400b40045a49102007034550b5020b02043c090020a0412600e8034041003880000070f600c0700a04030301140c0c01a4180c101e071030314055002c40c0308000500391003d82c0d540b6000d2103040d500040401e10034441c6a1400d10009424005914085041c02100c1d09622040c1c0b0502c18401e81d403103845420701006110117a895940a4102c9054038a11220b2201e079403076040200344613602d00081c5400301c0d03c8003150350000d8405a07000d10300c02c0740103413800e00081d207458408980799848414424540381041000450202c1a4001022900001c6000082600941281e102821800541243c05815100041002d8803090040b03901401106c40d045141403010a440610001100144030078800300c4c2203a0400c583c002d10507078407840c5480000b0300040100c0e0501030010b000b0130380100c65 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582758812 1250 582757562 582757579
    0xe0f0609060102151f09060e15100f0c06020d0e06100f06030b120d050a02010b0406051f0908060a020a02010e0114040305031312030b0102062a0f120114 67
    0x86500d03128a003940505010707005804600c0700c2c2055418850310060800b5035403001642c99030440441d0703526040003400c10450000e01c4038240944c080305160003030304040103451403000d00807944e03640380b08112a8001d0b13400e040809081000c0b0583d0302e060110f8000d0011032000c40c2500c1005015000400c1001c0b1801c195810303030741c3e128814030307003000c041c09255030750780035081c0a00040e030090b4008081100028100001d404034004d00906c0d16410000c0380c400641c000c00c0030040c00c0d80900850041c1141250706104450410700450000c00f900501c80000c0c5500c915490112406500241f02820726002980c440b4a029070884005e54841401000158a412000c4808010600c100347043c11303915040440075520303140c03000c5459800142640d410150000b04610000f066841c2001d81c910554074040b07041009c66001a050450040182c10ba05109210022822139604800f100c4101040354040e2107070100c2d51494400e0003905030301d59a065040d000410407200b5644001400711089a0300700 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582760062 1250 582758812 582758821
    0x50f0a0e2404113007050c030c010e010905071403030a05161401060510110c06030402270106140c060103031d0405010b130803040e1603090204090309030618110402130e010e0f 77
    0x80f18413a42c02d01040c07407080ca04007140845115500a010f071100c0c0400316402c0c8040e09520500310380780042104223aa65070480003042107010703c480c100800810121501a0b003541c070219860b8480e00703100004205c00010483d0706800045095140c035904402110340030070705030610a00a040e1401224800e0381c41611400580f03200ea1011151510900080d080e130300101402d000030f03508090000c980c4010420402e5450340e4000c04041c100e1035001c1e89034140383d490328902600004250f680600400010804860003001c0000d1060440f41d041c6440d6045414200d110b100388803115112642c003a080900006160708000c1c0a400101034088075000a60b0745c41c900079a8a100f20b21030141a01240c01c00542280c861004201800e05a0b0402180d041c1c40c69000408861070020300f1804601071010900c140602c910841d128140301d84c00b403040d07100640d1550250b50022042c4144105d8001900030814146060000d0061442e02850440c83d61200c07a43c2612000c1100c07031b00c280b5405803000a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582761312 1250 582760062 582760117
    0x4061b0f240207020105042303060f061c020102030901080a02040b07060e16030b0f0403050d06080a060b04111204050a02100f0e03070b0304080c0c0307060207050f0a0e240411 77
    0x3e03a02c0035416102c0c1407500349840200016218501c0c11400c0300f010b021f980d41451348041c0045c910514114040e80d18500c1c0100030488001401032079411650310340b40e45440181d80000481e18019400d09101c0c01c03c1e03039100404406481580c220000b1414085150390401c01540c20030112592010251401114414640c1001100b18071010b040c02d01618046a8000070f8450015001b81c02840d002e890700da2a41190303020341c1e04d142e21104140d40007148903014044144221f225088003290107011081d0308900d0001540295840d44c014021160080340400c40100001d442c403a41c050101d602d05000da90024000c0303844d00c52610301082901e00d25002c18600030a00c002a2041051124199250b039100c81e10710b030b007110b121030181d441201007200d0145e60412a00d8000d050390340c000c141840c18601031045482c0d07400c404501900441030140f0003c0140100d407940300a8030a01c600c5100030000b0703040182c00140c0c82d640e820601c0c18402c020f21031030300d00052809254644070103000f030300040d480307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582762562 1250 582761312 582761317
    0x20d0b04091e031416150e060a0213030501060b0405130c020304031101020f010e0708010e03030c0406140f0715110c0c01180806130302010510080304061b0f2402 71
    0x24000500c0980201108020022480e1110301a20384040d40d003004ca85000b03c41d82c00800d205440d05c5000d00705c0000c100300701a000c400c02002c01d10034000c0c50145010b15076504809401483d415402041908003501c2d02c540084c000d43c1c118000b8483d65558081602c113952140c09242e01840c03440c940a15200d400b4010700703007048401d90041d0b182620b540c40300f4003001080a0010b045000b1496003419003c424001c41800d90407060107028400d1034641038a003105c03811150b0440c0d0350410b10030000f0002c0c03004280c0c0d0880e40103040044c2d03181941c00111720603215058030040c542c20f021a200b003e001034031400c04c0160360365030410018107083c40d8000c0d40790300840c0f007414840d500c0224400510352050142071284286c40c6031408035541c58000460030100c0c00c170b5a03404240310355014170341850360900800d50080420704003800d10a04003102c3d584c0383d00c5036000b1075080c00b54405030000a1070705000e80703c903541d8010384610f41070364803490245404046c10150031480581204c13111111b5240e4800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582763812 1250 582762562 582762581
    0x603160b0d0510360203040311010510050d12050f39101a04020c031c0c0c03050a021203070e0a0b030c160c0e04030f11070e010902030a06050310020d0b04 68
    0x1c90261300b02d0602c261482c540c0c08225100c0061525900c020407284030703001640c0554403d4540711101000400007508560f00208161303041c0141400c00c04c03641e00c0e0709001c4100650800f03c442a460b04d05403098441e8880d0104031803040000007040d50032a000c2d0700c1e15039074000c14942d076001c40c0301d4100c1c900f610001280440312600d4000919035080028103610214050364010440305a510140740094101c0e0171465800215400004203111842451203551001c0ca08107a001c000004890302e0080ca260185000142445800110408800d00800c500c0b0404c1c10304030540c0e992440c22030780041c803107990108040d000d05507400340030450402da0010f803407040075416000c1d4144900583c4242d50b424920780260398600202201040713469000100c3c40c031650094460080202503928001c0101e14400c0501c1c9030f84c0c002c504241301142054240c20b04444001002503100d403907402c80400246420b40c0155407600c41c0c0300c2024540151a00134001403102010b04002c07000c551001e00c0252040d051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582765062 1250 582763812 582763829
    0x1c1109121c1707030b040617010c14071a04061506090303033e04050604030614010602060f0610110f010c031a0f01050a0c06110d2703080603160b0d0510 67
    0x3883c0f03500c44e60042c125110000c0007c102246d480e07110100091428030b429515945a640303001c95160001c2e481c80e11000e4a412903842c2c181c10303444885110450b210004442503000c00440e0a0003c0d40d00580300b004d910452a00c0090740d00e940141c9002c0441c4070440c082410400b00745441c1a102c9000c0b40e107621185058000070040c0c80c40d014000e610075503030b10801c0c070050001184a407120000340c0701452041c400003c1203000400c5100c40d12030140c1c03103038086600c8081040f0540d840290f2082d04107005650140345a40018400d0358003440301e091114141c82030182d503142c019415040241c00201d04d840c200400403408103251850045d490005800c04403032685c20045510450080040e000c0500d441e188030031316507450b01c0c10744e111821031155413000454156035202581c4158441290044007181101007050309010880e0144140902030111300c0c80000c1c40c90f00c082c8400150481d9941d00343c502c607521040c4404e042e07049a251180900c4c41c3c200080c045d412034042c1602540d8225 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582766312 1250 582765062 582765107
    0x5180105040b0f060d1e0218010f12140f1b0f06030f1005030601120303050c25060608010e0703050c06121f090c0f02121c1109121c 58
    0x5490743c645484080d00140e00413550300e00d1100801c1e0510f000f15034540d0f240e100301c1c803000c40500400680409500c0450035160360000108000d014900d400001c640718241200554404c0f400c107889030312108109000c0343e0243e80c07083c4150580c08070712501c030041c00e0b81c0d030700f0765003034010062050092054107044c0e0410810004038600e920040c8049911050001d680b07100300340c031240801d040071401e80c40300c0c0217032505800c91820150180500d503402202181081e042800b07081e06008101509134000183e540c000030440b00b8422290481c1016050b954003d00800d00d044080690302c40583c80241d6080c003600c4e824040b41d2034208100d41014444108560782038560071045c00c0408410200f2184428403640009421040c03809030301101f41da29100c1440242a0107406030600c030900d0300c1280b408000308041802210500c40c1070030b12080040c400280902c0c104984145071042808080d4000074105074403c020a000076120311401011003c0c4540c14642c00058030304514404141800c03d008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582767562 1250 582766312 582766321
    0x31e1509070821090d03020d020607020c090619031e1b060e1201180609110904020a09090503040f080304150c020f0f0d0c15030c09151b05010203010905180105040b 72
    0x90721008054483c10394500d490700301d181000540203901054104c1c00750704690140000303c1d405001c45640115180094680d00c070145001a040f0070005004620bd504901041054a8003071024030024692058500781c464140c00050020014000c1084541c01e04001c804444015074115440860b0215181c9100300e0249904000d1000b0803c244090b9641da6401008008400e40000318200c80c021080010b8950030307403c00d0140c0c90301c610240e50081c4243c0043c440141c4030350103003e0444403820400180607030315103410340c10741c440d560100394504003044020070300810100c001c1044078103125220341d000d001c6900543d14180102c101039400700c0b40600504060808018818010200820340c4200200541d0b8406d8102c2e00c64009144491080885200341501807084007a28921403c01c0ca98607845c00c0d950100d14515020b00004005400c2c4c4407421401a070700b00c8007141540a4005d40d125a10b0b02a44002480c0485101d22151580c0d5070f903001401040c03195a0161780c000038100d03401c0c2d48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582768812 1250 582767562 582767593
    0xc1b0708060a050c0c06070302070b0a0e0607140405190503240103022229220b0402090a060203070c050904050606090c19080f0132031e15090708 64
    0x402c500304e1000304015104803400140645480340101d9100181c4500e101d062841d0fa5030b000034050103c2a1a03e46141310000b0001480e950042d194944040c44085025030b1007260b002c2d5500c2a504200f420701c42c1c06611015032313208400c0d90820b800704c0e80e6008a030488242080d045d4043d82604607001340041c005030400d00040b2400c141305941300d0b80d065200200341d1049580d030703000c100d081c3c6c490304858a40c62240b0760032014160000301c80800d039890002d810622418100c0d4083c180c01030341d6001400711500c0759015501e110f80700805071007140e9950700029440f2340c00a40c00b2299443c00e4a07000c542d92805041750350249403c00020f00b5160b0f519414844907140242a1600341c00040c48403101c0480c001c01b907580c0189803952200810f003460803004519107010381040100d00c0355812400075107240c1030141301c404051060079030842c201c4580480d0400030481c03829510038015443c03a001f004000030741d141c0c507505500c1e19a4015580e119600740c55100d0f50090600940103040d02c0c184540c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582770062 1250 582768812 582768821
    0x10603050f16120813050d03030203060901080d0203180d1a07090b030c0418061a040512030702280801231b0f090f060d0903080c21090a0b0c1b0708060a 67
    0x1158285c0f107a082620b401c00901e1000f980f14003100041d0b0000100065800c0088513036005001e20002480103000c0104082d40300d01441440040012240a5002c1c030b5564040f6a02d548603003014440c0303072500c4031a004280310722046401601080b12140001030700f0240100326440f41122000b118205400e00d046046c0090100324202e60301a25518040790008000203a80761010a0500b210754592400050200c500070b07008451105400074082200035031952400800074043c44d031404484040c510707285456602842d08408901d6107405182180350b880d916000003600c2840702d42158136600c00300501c50003000d0b402c41c00815542403040450280c14030000c1c01111030024040d184042000d008141c1c43c6e040802a00b0900d5254070600c414540c2107035480350400c82c0c2582c4a07260590388411031140507488603001140503c004005445c505007445007901c03981c0e00c50b0000c5042e050564803214260040900d4148014058154166141c2d00040f44003c55080e440644441c0e91480d14920052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582771312 1250 582770062 582770077
    0x91d0106030515280816140d140604170a0c14210d05341202070b06030705040905060f150d082208100e0f010603050f161208 55
    0x710281001d102655807078482c104040c101940422458071400d030000c83c0c041d104d9a0000d012a040140345001c04044103c0345002d4809800314078074a00003130004520700802c2c07160098000b00d110f5803106035003040411864040c6001d4144140b5030705003c10344441900c5100c0c00310f408503142c1000100054191050111501c4a82e41517406480b12108081e80700304142940d80c6a015000a03002000d83c683d214060300f00314444491806080030300340102145111000070610300540a071404c0c00075101d10382c0b80c0c0000040020a549503003007443d20710a1444181c4075540300f0700503d0700210320f504191141c1b070f0186420000070240303602c5150740801341602c050460440340c11200d504034000c1e150b0b480302402040c40303415810350f503004c602248140441d40840d0b4aa0340541000104502c000009441014200d0940c0c005542400b540c500fa1034030165001e07034229942071030000000c2c000c010441d5060350300c0c410300741c0341e00318004000c14024025030300500300c00b0902103030fa41703001c00e140c0009403030304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582772562 1250 582771312 582771331
    0x40209090c03030703081602030c07090b04060302060c03070b0702010b060a1412010807080d1e08061909020903060906070c171317010b0d020109090209030a0b090d091d01060305 78
    0x4118507140401d055074050082940403e80708418040c0040c02c00400c183e0b04496880a10300f004400d003a01c646801407449480046a142c43c0307450459580d5501860003035900030700e910f40d1408200203280c0c603604814003e4403048880d00004d040c003801800341c0f82c0c950b0b000a10072868000e00000c25240c030b104850449450440501410440788071458696001c0d003903840091000328034104040e480e0644419421007000f10844524400240802034620003043d2800c2c1002250b803903101141c1c0c188071400c5280140041c03102d00180c59001f030ba0040c2003002054007510310583e5440c004039500e400c10b58000000458082002011400e8400c2240440c84900d5003185095009112014030403880c2d000550340b443c5404000340c1d405000d01c1107980c1d020060300c0e48111600560006032242240b0700c90303100350070740004121031180d80501c5150903095115040086900349903180344da0303c0e090580c0c80c00105840100c0482c85a1a2902c41c042d100c0c2e08200d1290141e00302601240501000f030000e080c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582773812 1250 582772562 582772573
    0xe0d0309080d1814071e080303010e060d050106092004241803050c010f021506010311090301111213080702060706020d230703060509061216091a01090e04020909 71
    0x5825078013404a0354000300042402c81e00b8500700118001021040340424000d00e90100031503003010040d00c1c112000f92940c0d1085503118004100d41c101420001080c0d5442c208000c07030a04a80d0b40702c6410720840e101644070662840303408002030310980c0104250300d1380f58101200008034211028040000c0c501d416080003003132203500c6942d003001c0c1d0002c8070581c004541111295074400c0f00f8410205c131030f01c0180003000b0306007d03000e80700c04040c020b60304040d21908610110103c3c00110782100101030300030402d9200e024600c01d0720380c2001080c03200c120800b201040c2201e003003011a50320581c00c403400c0d51408a2650812030745902c102e00480325035400340030011910303089214001d44004920010340d4207101d84003101044100c000d100d20145032400350103000584502115580c000410380303113220700c00d60070b03000310b03182248100c3d01a40c902e42c1c800022441c0c4071103800403091820b005184a0b15000d01c98015244142c0e030b40258004440310b4800640545040c03c40150005455801e464 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582775062 1250 582773812 582773861
    0xc010e060c1e01020a02061636030b09010b01021204091a0a06020d020c0102010606020d1b2102070504020f070605130501020d09110307030807170906030103060e0d0309080d 76
    0x1407020042e5500c800c140d42c04911140855010300c5000d42c02844981c0e641010108124041c00c035058440500c1c03038401c0543c8000315100e010400f5030301c003080c0f924405074038a6070300e24000910f030200301e456030429420079015588035400042d1a40c000c195900c00b0a040c01c3c1001d0000c002406948020041015944610212900c8180c602d03805040242d000d4450581c1e0382d0000b92501141180315411a80340220410001c0e034040344080c1c2164a501d40141d0383d0941d1a40d01d9030310340402070045c212144c002c201c00503032051500410b006034056001d1f240b03410782d16002c120807401030380c05410100408105070320001c0c41541c0a01d80c08000300c2850400c410701030b01c1c1d030303400c9822480c4418071260f511300c214000d001c450070102e064408224002c01d00369045d9502c0040d1801070307031001071550a0100c0380140d10301140e1f00741ca01e03828004e41405c1d103135a503034203100c405400042004c951a005410007000000d11900a8940007a007000e00c142c81c24290703008803402454154003c40c5540746941410b0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582776312 1250 582775062 582775093
    0x106030602040e01030303180b060d080d0f0603030206132018101706010b04171903020d08220314040b04030f0c0f030f080a031103040303060906080c010e060c 70
    0x40010b4010f0007001e0003198154617020b01200d0040d0f0501c0c00f56180b8000400001c0c2c0b0180b4050361100c4196102d4000741c109142034481d0b8081e48032004545800c010b540e2042d0b0b5003546c44032046030300035403c90b09181c44165062215120745034014041c4600301200d1300c05c442d41001000c40c3e6680103040240c2d60669243c0401d82280240c03400e030611822500d0810521201740c4400480c080990094119545040031040d1386210b20703c107142d243ca03117018035840524020320840440032902d20080e2592655450000c5d01d54000d0712000010549690100744008007145200c0300b4118086024011150300e80c03000e0f61a401da0100b400210712040001280503049040034000442c030401442d48948028901202840c603d5040a03603240b500ca4020408180365000f06003103141c10006145d598801d00c2c2d03045014161000320000019000010304c020182d040d440300c4100c5075120800c0090a80760103115840e5000300c1a01400039103681840d101d0782c0f80c0000200315000b00310381224042c5880740d040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582777562 1250 582776312 582776317
    0x91303020d0e0a0305031305030706090f12110d080d1b1d0415301a0618070f090e10053a0c050402040b0f03040512031302011815110106030602 63
    0xc40d07c80300c25600104814102001410b002c7c00190818680795030520309415800d12039032240c2040c19800c0c150600c2807103007104498210f0b1034090f1480103517080a08040d0210fa000c2004c1e110314130f142030f00d200b0214040f07c1d050300160159545403002c1c1310b544002102030a0b465901c482d4090b03503900f8010f910200c07a40045004185541000c201d0000c54252100102d0221070251189540c00050b4000640340d8007012040321a903100802258451801146800100140c0805950541d8050050382d541044081c82080c1c5145e0300d000c640d50701d690020030b4090017502c0c0107000007500708042c440e51410100304000c1138541e07a4601c4100440c1041700b025140480c403c492076550780381c1080d09001c40c845080e400b500c4245d5065203020f140c141c94402da03100700c000c020724201002c4003080401c1828080c11440d80c122820007502c9045c0300e03070400c15107600241c00324003085500d07080345100c07403541e4143e10803a00380f0f104180b121039001e013003510080c0036100b43c1c00c015540c4030b0010002882a102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582778812 1250 582777562 582777577
    0x4060807020f16030b06090403080c030403030209180109050a0924091a070206070503070203040311030c0d0c05040e0105040203030d09020a170a0303050105030a0510020d020d110702091303020d0e0a030503 90
    0x8003c0d5152075400d210901c2c450282c02e190044a40ea010440400c0c0c02241c070a40101012821a070707a0740c1c0f1401c04400a0007281482603000309550780c1580300c1e009089a05050b107544040400290b114442404101c0d090418002c1c1100204d880603642c0d24103c28032400440500311001c21401800e41d0703084961408040702e000c11052030701c24443c44036810444180e010040e8203000340745061610020b55240120300c80104000c0030342840321803a0300d007403007041300686000d000d82006c4e40551800b100f0f40e54881c0101801540b81130034424a40700140601030142e0b0f0060050740c90b100400a131980580032003141070f600620380000000c1e5604010541d5141c1007002030141183d654285001825500d042e400b06200350b000400f1040890b01c08203001c08814a4010016902c080c9151004060302582905401143c9005002e082c4c0c02d14500042854030300c01c9a100c81540e070f8000300c2150006c0300344406001a8480f42401c01460700481d035405201500401020603e6a00e0780c03442d00c3d56001a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582780062 1250 582778812 582778843
    0xc0801051501080f06062b0504150c120b061c0b0f0a0e0a0c210e1c090b0a1e020f0f06240a03020d030512060d0804060807020f 56
    0x400c104040344140071408a0507400d181c4581d2500300407441c44813031140034040343d2007614005244a082401c4200c1d940680088001d0800001c031001e80340030080c070003154141c0d00398070400b42054007449544030702d12261005403602004494240303554001025038581c4a03800501c20030a540600710b805100e20a01c450414000c2001043c1505102045410040c4280207200d10701d8180015805010b0266101038034000029103d02d0543c2d080700d08680340891244400030f0b0304141a01b0200701c0c1c0081c054141c04030f048a40c0c0c1442c641509544c8030028141400040b0380e150207000d00c4840700300400c4e0070b0703226151041d6101e0380f65444541c82c0082a01e074901682c808448c01110450920030344110144010180c103451034142d084800d4030a0100802c05802240e8040450f540d8403000100f0181d81c020300540001050b61801901540c4030301d0440584860070400075805e482c109c07203c800060781c0190540e0805140c4130060301e00300805002c06055008400100355001000c2000c07941c5515000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582781312 1250 582780062 582780071
    0x4090b090f071a1b060c1c05060a06050306040b040e070e1005010207120602091005190c0203191403120f090303010305100c0c0b0903030a0f0207022b05011509050106030b03060601080a02070c0801 86
    0xe08512250502203640c01f0010f4205800c01c0303403903550208548106da0140c20400c0e03403540c0d200e0004005103104801594407624000c26031440420004070300064520b07645464420b85c65070652003401404900c100e5005900c41c0400348411660060840001c40c480d0301c1c05410849e032000010000c000108070a00011404540c00c00c01c07182000d000718250744582030103c01d0030303100e401207615007000303040800b4049095049007041100c21500c42000c2c15101d020390340c9904a840354000040c0b426100e2100352200000441c950010100c00c5a0481390700c030004092500c408000740c8080c080c01c10716441404110441070000c01e8558031601d1244803890065580c3e031600f44041001c8440440051290034070511000b401038440d103c0044103a2a60407000a504451181104039428002d078010710950800950004160b043e001c0b480035140034150901c880e1303803204411130880b5070008815606520940105500f54010400070750000140d02c005460011180c4969448006030b40c450451031303544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582782562 1250 582781312 582781327
    0x801021219020901020d05030907050901030b070f0f09091a04020a0e031b21071802040e0127110d110909150d080c0a0204090b090f071a1b060c 63
    0x40300030320020721078000c5081c404a00b0000703664402554640c4207011000001c00c4d000d00b001c10513030000b007030020720646075980c50f8648440300140554240c030214401c10b9a00e18290b01410108400c010b482e9070308410075261403603050143c0f1500c4000c00201d590710341c41c0d007210380365170000b45880d800586601200c401400705161a14041400051204801401d80c11050740d80700c020200b0340701c0c40385844002c920302880d400d090205960100d401c1603540b08500360810110340162048440103211000282e036224440301c0038a20003110741c108000591444400322075250f0050456030103681916003020301c0412100202c4400c01c0c1442030016000c2150451032801810b110303441640801c0d50300c01c1d040c401010400700d0801401c01461250702103035034400580b08001311140c00c2d0300100305001e0003900d818140409402690224114000c03880a0018204001183c00464040f041c0c400000c0050407041403140c0c001c03000020b01c60109101d9000310000c1041028080c603c18240e05541d200d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582783812 1250 582782562 582782581
    0x3030609011505071104020f120a0b060307050d150305030a05040915050d03081504291905012a081306140301030b07030e0a0b0a14040b010b070c08010212 68
    0x4140d004488042c0000c4508110a030300500f600c03691a880540c84520524090028010740034a40744401c0e22407011986080340819840914010852404104644c1d58440288082d43c841141c0400114000300210b110104c0b903503014204605040b000b0090311a00c99403003a045504c0321815400084005c00e0034000700301e50740701d1100080088041241c88916183c04501400700c00f100c041d00b030004540001c0c4608230300c3c00b1010800c030b000400810040c0d59810030820f0000700c0000440e0301c00e1442441041d0b60400e000205180c004440d00159054640401124a4018520b900b400001d010000e6264841441415814540300300c00c10f0f602d4400e84c0e8480a1035003819400399041060581c504002e194005c3c007101c0c19250000b030f0301201680c030300f071003a405008200c4607580184107003281142848200100580159544241440700b10101c4410507481070050b170b000b03418610b100d001004020070143c01058000d20901004120340d03074410001e42260400040c1364000031582042088011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582785062 1250 582783812 582783829
    0x70c0303050a0e031b0402031801060b1305032407120f1a0d03050a03020315060d0b01020d030e07050f030a0203030c0114010603050106080f0a0612051609090b07050304031b05030306 80
    0x3015801800400343d22454103170600000e41045015660010200e0200100089125203410802c0028000141e0345c0101c0400c0b540080c40710322020005e0341010a09141c0843d40100e980088544a00b49842098034240c0c1c2050103004841400510400c202a5000e40d004030251648920340010700780070501030001800c2622081c0a00c1294003d0082d000a40c001c01034802d00c9100d40740045e282d0f982d22080300400000c00144a43c005000300785c0f10419001c5800642d1480020390a4440c1d000700c2000503402d0b146401030070045900b1807041800700e801c110400c2c8810b0000241102c298183c2034000c01e046510214403016184d444104942c440803e03035440741e0041c41203140c20803039989000002402c68502034401044c03100c1c00d00106400d450305800032009000080ba11a045900d5890410703500c505900b20001c09a240100000f00490580b1911000a8011180003220f036682c09048070903030310081c811410300140301e007940d550b070302c1074490010300b144118000c540e6800e020301000303c2e40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582786312 1250 582785062 582785087
    0x114010c03020303040b070903080403081b01020421110414240f0d0f050f0c030f010b0d15090609060207061b0e0d020a091103061903020f0f0303070c0303050a 70
    0x340202544002903000044070b521607001118803c298941c0c0f0700854501c041544060020503012070b01000340a00000203051000cdc207601004c190076446c0e240305d0f080c1e0140e8421580b80f411104007450101c024030b0114401d00340310b100d6110340d00d40200300060451b22140245001552450200308881c0c4e0440f245002040d00c00741c0220000001d00001a00c1c01c50f002c1e070035801846110904070400284e128107000480e445401d440071000400c50440d640c40c4110606840780c41444a0150341c12410b1080400c06280038040101d50340003600c503031302400c40d11032250310502e0b950a07030701004c660544503503102c9074840c110159841c0b540c0e0030601d081d100c110001000e006e8410b5102100d817a00480340b10400c002c1941c0c400714007500d40c000200c03850746550268050074100088942011031550086100300c0003290680144103444181400b400c00303a010080d0490042041000d152400402d0000100741c000c08a034508009991128204d200d1603000b18003240d40400c154034030640098041002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582787562 1250 582786312 582786317
    0x6110d02060402130c050714063408090a080d05010302040c0315090f11030a06061e0207140a0b07030c020a0504021201030b0403050c0f0c010206100503060414071508011401 76
    0x100c2c01e054000500e00f08060502641542d82c2d104002c030158014415604803540207031090b0796011802e00a80d894078021503107011002c80c601c582c0074101c08014400c5d144806a14a01340460400c2c0b80c058a04000c003801b041c40b1449650b410000244020380140b5400d0012200418154514410b000c19615801e45a01c00c1c9801c1000c4004042d82c070b03ca05d507080310141d1102042c1810303054680f200419403114051807c3c1800020041d401100e80c03c10403c8684a030b40d1200000c0040c00c9120002072550440700050300401c10400c15501040820204030400500b010151642c1c1c00c08101c05600480c1e04070b0100c0c1c3e0007120071095160051000c00181400da4055150002441001c24002d0381404000e091404c520042414103105109858015520100301c50080c010508825500d00241404a00610a000003d030b0714400d040e03440011280040d0040a40307442d01d40d034000d80309041c2291606140702e003100000303015155621300c0400984940b119a80c1d9410301d641d103e544042c29001905 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582788812 1250 582787562 582787573
    0x120803180d030911100f0324080115050d0b3714090106080c04180215072f101e0302040609080111070305070c030501020a08090c01020a031211040b0406110d02 70
    0x7546a0403900a001d2040c031072030005410300000340d10b82312074410107000e080344004031000402c46020550058450702c4000c44090742c000c0e0b0b80c108001c00c0c2d0110550046c0440135010100b07400681c520401c000103174088000c0c083e4819084080c41e00e00305c18400d1071203613640b06c00201840b4211009595002200c0c3c2d802448810b040c180c0d01951000c815140602039927440009171601400511100111603005018143c80120044408541e070003503c01510048084007031480440726900d0048222781503c0682243c81c0c04101c200200c20152030101000e12804100c200d1030b0084551040422170569100141c4603410610300038282c001603005050340760724100e004142003082805482543d61b2502c0d0040e6541100e2901d080072a4195000404035800845c1c5500c020342c01c0120a4425040c02044980051649004a030b48141005015003c10140c0c1403100c0c1c500c40c10340000390409260700c0040c1c5070070741e01c103600d10056010303034808000144111030782e41d022001400001c0000c54103100410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582790062 1250 582788812 582788839
    0xa050109080a1d031b04110a021501091503030302071e0308100801021c022a07060e0d0b070f020a05070e070809030406090b0706110a080916120803180d030911 70
    0x1d42d28842c042c07a00c1d8580300f81707a280300e020350343d90780040080b103240007243d0741c81d40b0300598069610440854404c58200e1044008141c0d1355181c481c400b156110f0407130294980d413071928258001d510400c0165031840c12381e01c01e110035203000f103c04500c0c24420fa42c0d40b040e40c6032210220360001001c0c0c004a0035039004120055108a01d8080d00e885588410001656910007099103d98003c2c0702040c01c0caa0b00251101144188020039807800b2a07074192281c61000e82031030200108400c044030b0040449401c2c001007003140b03100d080113038082e072003030b004a9082c0a0152511841e0200d982e004d0140781e00058104442076910160940d0044034080003181002d0508034064085055170054150b05400404c80c001400903035084520780d076400c0c0415a43d101201300000327004580c11a00360401e40b06400780b050074075081c241b4910032105100543c6001c41003da994590310390001d8140755495203101d142034500c00040c0100d040c1c45556890005a9000914115081c40350034050300d8440c145901080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582791312 1250 582790062 582790069
    0x50c0705030d0c1803080a09060e0907120b0d080304060c05070f080307050f0c0c10050a021009020406080d0807030501050102010b010f031e0f0b0102161d07020a050109080a1d 77
    0x140c1901100c240003107103c1405907801c5464094840e0390b00e00107040c01c0c40020a1007080c0c0c005194000c0d03d03680d4150103035125031003580c0c20120540241e412803c52000640c0f081c0c0700c3c10150006180142021420041c02c2d00061030480d000401076035004000814801000828030450f0400320b041e08116051003000d032500380403c41000030181c0300820001c000780089119404403004006e60f0020b59403904036002104c0d644e54400c8842d00e01840c856215a866280a041134502a0006074000c1040180d004052806009082012a00903403110400700c2c0840040c4043e4440341915660386406282c412401070541d00182d014030b05691400c894002d840e40c0c0302d40c10242d1920b40341404980501043d0050119008100600081524000c546a0220303525004404040402d070300720354401000d2289415840e00034440c0c100d05071001030090f401203072004020365220246005980840b2401c2d01d41a0948441c00380884801100007941d4410035003107040e154010300642034a0700a0410307035011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582792562 1250 582791312 582791317
    0xa12050307030c080c070e181b040e011e020310090b0f1c0b01060e01020f010e061602071203050306090c03061e030a05030c07080118110618061903050c070503 70
    0x103410414580852414131041c44112001010100d00b1510030b076617280050700480f44180c4d88032a802110362406070340c1010000c0e40d5076080707440d03000040605100c4410803006110758158050155200d19800c03104003036248007801d000c4a40e480c00f690364030340f01c503c44208103156048071038041e2800c00410a203441e074862580b0b01d03500aa842003500b5402c0d0040c03596070b04924000501900d4500000300d146a1b202001030701c40c10f020b03000c941c917404400701d03520f080e035070300d040b410a030781e4001070016448072051100700081804078015074241d00d440d20b41c40c01070604048025004500004280051410913a1000c2c1c7e1121401c0c0c1040c5c190308104002511440b000c0c00035031101d1991054081d0309540511a950281750300c18122642c440100d1035598440c825842680255440c100061004e90380c40401414800d0380040d40c507100300c07084410000701303400104180b03014903042d103500c01d0151110300040c4101d82106011383c29550381d0b04c50050a84900800482c2c14030b00a101600c00640000305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582793812 1250 582792562 582792577
    0x80c120708042108030702070302040c091d0c0c06090106150c0b061e0d0b040c05220509010609061409061e1c0203010c050c010b100c0b060f100207050a120503 70
    0xba07010104101c0301254028082c48000509010400006e21008a8001608030200d070300c290b9040c009400b03600710641302070f0303298407130034140031a03c018071340340024840d808a07805842c0000d03044c103004140c8039991802c0c20443d00950103030341d504d0050020b41c094040c00e042002c4546010141011282d0700c260700e182e0007804d10f0340143c40d034100d0824410304d64143d20700101005070010790a10750a0400c0c81c4680d2003074405607508032500901140a0614007005260300c20710154042640038400160001800c00800e1469507541c2c3c1e580108400341907002c0c403001007921b5080340010459000c1004400200506440d110b00000b00c1c3c50324203540304800c002c0f14000b044502d28401d00b0290004940d002001400039030651a003081c036100d07940c01a01a0a0140c0070b207008009c4850a00e061110007540c011410b4046030a0100c00b00001e007a400780554003903409403040b00300d01d800c01c010841007000440045c0251f04090700610817414580071a000600300c81b40351070f4034a099a221180c0381d226041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582795062 1250 582793812 582793829
    0xd23100510061b0203060903070309090c02120d020d06060f030e16090207030c05010c1106180a06051807260a0807060b0a0b0c07030605010902090f0f0f040504080c12070804 76
    0x1d841c040031640010183c2d040d0007400b510064034216503900c0d00d0380d024400407804129100d85c0881c9841c0c451103084000e003400d4004125041c00d42854814a4005402010701c0d0340d002c1003484103031000c5018900040180ea10f404111210404000c0c060711100112048030b0313413003a801d0038045050030f41400c0848951120059440c0d9450400b29416101d014025111390f092501c100500d40d44030305800700040c0541d054604070b881d9000140032411020346166070391761240c1000e8000c1031441e440385400c102c140707446041c0e24404000da182800a2903000f8000390350755084c203900002d8090040c0041110301d8002d840032440503910b844107406120f0014181030380d502240c1c00507444071070700240a8102d025a03d07407101c0c40c2c503038801d5642181c0d000071039200f0705000000032400028000d0f80c6409000400e40038600a044d02804541948020960790185000c0c1500501e5103952081034000c5008200c241c0e525207000754060718140b0500c0c84401105810040d00c404903003513105a405442541 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582796312 1250 582795062 582795077
    0x1b10050a1505100c061107140f060402150d050906070e0307080601121707050115150e040e070b0a020a02031b0607060507021f051519060804020d2310051006 69
    0x400e030480d403070450083c2c018043c134031b00452948040c1c8218083c100d424410090940244000e160f0075071140480c40303040d5881e50040d404130300146881c84104946080903d0581c1c10124500c41c281d050700c1e019240e4071030f150040002e008015030302c14048469100d05500030111079113046802540c0c2d240511892000c1003800c03860b034080107130700300c0d00c0c802c41c01039088486c3d00e4010608000b4005d190701864070f15400d42c00c00d030008003240c0408170b41241c481641c560344507042c2e902e400c2c0409800d80c0a8070301c43c136019219001ca007500e84400a00b44a960036801400026550b2060624215821004240c0030f401e8204c2640726075980c10484145c42c0c3e000c100450709031142d40040c1d00e170215000c104040491400d10322280c001059110130701c44c1c0e0202040c03885c0d503200c43c010b001490076115a482c464184041003803112034041c60134240c00c98800340c942e07440207041352501101c040100c1d208a00d520310010541e00c0030041080780c00081618070700c0400590a040b840300c0485011441800f090042c00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582797562 1250 582796312 582796339
    0x1050a09050a200309061b03010513270209060a150f02120403060507170403050412050a02041d0f012a17160f0203040e0604111b10050a1505 62
    0x1a41c000d218002071001e0f108000155000103083c0d0b603001181c0d006501e204d0741c0000303a4104203050000d10065265414189964241814445415406514246001d8840140710042c0208400c1b801160007024200101c40c6850300c10401d5008001d403409220707407280802440a41c0070b03c0c1d00400d1071341d504d0602da00f60090083d026401c0c0405045000c8103030401040c00002d1012a4001c10700c1103103107584500380c0c00701e22801c00c1040901130754041c0c0050014001070099a0030300303802c50607030f070b0195003280c0880dc440e9000805681c2c0b9038039400c0025588a4a54150310010040030020150f404024012003001650340da00c0c014000c02403840140103243e008800600942901d8001c0e508a03402030304a2829200c00140d039102c9210920002c6e0035036503400d40e010320200a84055a411840700b81c2a9261002000040c021042c15286040005c020854450100705200562405160040d01e04002d5041025046480040c07031452050700300120008510004200c46003502c500b00c0b1142140e928 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582798812 1250 582797562 582797581
    0xc07090b12060c0910080906063f0606060a0c06021b010216020f060702031e0f030705060103030e1507060905011e14010b0a090909060f050c03100e01050a0905 70
    0x12040c1c0c882202d004030020700c800c1d00c20701402408548400c1d03602c030608140d090022603580c08202da418109400142c003003545841d0604050380c00e194042590125001d0004d080b106211900345a00102001011160190901401140ea110f034003100c40f54105020643c001d84100e0001c13030300418240e070000c0d50031000d425030381e0540080c80c41c2800841d11031503040342110711501ea1260681c03084528241081c005d203001c404441840781d000d0041c02c1c01d02c0c0004c010b112201c0700501211032a00500200a00c41e090810140509600900050000303525506000d80208200290f4900441420705900c0181d1196006c86030f41c1584110f000481ea6403e00b001e50040107110035540304401031030642000c42c80780b07400c121080c40304012111291b1340e0302c240030161845007520040c04901d189204208030525588024609030050001040718400c0f20070000840b4011111903925034404000c0c81b140c1000060810081c24005490024650401c070003e60701c3d00c0345100720709165445a0000e052032a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582800062 1250 582798812 582798829
    0x50d060e0102070b0f18070b120414030c07030b060108010f030308100e09010603021503060a0501230f0a080702070513020904020c01020a0302360607050f1516050c07090b 75
    0x10f4020070702e0742003814200c5d5013200600040c0c51080224281106110075540e010410100f1104000c014902d01096104805500c2800401c140c44544100c0440107103583c05100030902c201c0010084c102043c154507065502440c0548098100410400107202c030540280d00c00040e250941008225a41c81012800800d107050f005041e4440a042c00c2c0008054150810025244212008000d00042d081026441d0200700ca8107980b20000303400801c41940290242c8080103881910b1100c0e10a42c00c00d41c40d400c0e44030b0840e8401064000565a010503840541c041c0c0088061002d003c105140a000a404006651181b40707425030002d0204525503c69040f1114031075040029500c0d1248a0409002034215028400f0b1501c4410703840b1a0f40c09041c42d040d04019800300003040710b0700c070348418000301d0f4200c20710031a014480c1c510f07159203141040204901251220806299501d0100c41c502400408070701d0420500200703125600104001103200e50540b600807000140c0f08040f4030000d511301c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582801312 1250 582800062 582800077
    0x1023010507050102280f0201050c092b03052106030d030e010f1a0301051b18040930020d0e0409030c0b040c06090506091305060301021b030c0115050d060e0102 70
    0x2c06405d01d00d11790049220b41540d0072401a04c07400210b030446241a0b091f900101c40c8826800010002010107142c860001c50390b04102c0036807180319980c1d03821031859414100d0815000300d14046441ea0b00d1000c1c40108603441c9026001d09100c5041c0311005c2540e5100481c005001d150301d440001500f058251b00ca00b200c121100307400c0c030a025880359400c0c41421a6a6520300a50925000507030103c0441c107400141c5409140b241c0c500342a22050000329103807960500d510544906403c0301048440038004201110440340341a954a958025110f984082c0303080d00554102c030410b84d001c0c0ea040451602c40d4102942c0216031403c20b0b20742101c0d0070380d055000030302d1000d20f0703410310081c46089007000b420303104036803160010356440e107040060728002d80784402d0b80100c02100e0860f0b0443d42e40c100607004070300a400035013440c0840c45606e034111071a0780f0840507a800480c04186090090080e48018283c00010101190a0401003a98200d5440c0050310741500c075400e04101d00801d60442d0402c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582802562 1250 582801312 582801337
    0xf07150b0303070b061f05120601180303050304050703060515040c08090a110a03170a0e030102040f090c030605061803240718030506190f0c081807030206040e1023010507050102 78
    0x10155517007005842c03038100010142030b00380301e20b0000c9c8441d400f44092600040c00d0b07405030302c4400d103103640c112040e030710040c82140e4a0064200000010f201806400d005413464035070521010b203031030107000444500c0003e40080000b20f1091180d20000032031407294544d04040c1e0010202c0602020980520841d403004103420441800301411000c031030050036011801d03a59510f940303e80715027014240e00441c062915807084010313080104c500700790310000c17004040b401d012809071355410001c0c0241d048401031a00d111564001700d078540c034040c01603244c4030030482c0c80c086002004041040e00c9140c020520001d000d1a52800341c01c0400404111006560180448881d4035107095041003021707900780d031807205508251030b9202c2118140607209102025507541000e40c0d9550404040412510258510718060481c0110268070380348000c00c05407910b80007941950170020000110340c00300d9448041c248000d0020008003903042c80710200d11000c246811911034107141800f500900c40c09030240c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582803812 1250 582802562 582802609
    0x1b080f09150d150608061305090c0a06030c0212030f0403030e030f07030c120f020607080718090c0e060301081209131d010f15030204020a020307080f07150b0303070b06 74
    0x10805800d80000c80c1554501c03d040034a00e907280c00030385a41e43c0a03551243e001a074041017028078041684029440034a03002140e9420f540305020070103494a83d00540c0010340c480c0720303c0540d607404018203004140d03042c841d18074610f800100c4a01d0302001510050405843e4106020304540030401d8075060030309014415900c590358903003e800c001c0c04000032102c0c00b4025640700b1750980100003030716600660b0340280449586262080342c4e850001030105042c0090580b1410614000b6510100901401d4000048541d801e10010b4124100e42186a1040720f0410051048280100c3c0c0b040e9029008101540c40300841c9001543c03c0383c550306a60069464034801c840281c02d10518000c2d0304240100030086c0d0a000c000d544c0a40e403280140401d0f1a420060800c01402c141c2d005145c040e0552050300d0030070301030356100c040760340c84204440170300c00380400e5030030500080b4a10300c0c4540e08026401c104a203c0740003c02c0c1c0342d010f20700000c2c2419000c0030029229451741b01008003818201c900044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582805062 1250 582803812 582803827
    0xb0406030803010b0304022e0309051204081011090307061b020907050304030314100302060309030f031602010b06091003090f1e06050f22030203090a060c031b080f0915 74
    0x10400d070402c65090307110355540000c900c8c00e50001f91800c0100c03a41504900700340010307034030298043d1481d6001241c080c4244403000c0000c1d40c811024101a00001c00984400310b001c0c09120b0540f400041000c0c0109020401c00644e503138001803030000c44e1124240f0b0090391000c1d421321007243e89030400107500200c03508104400d50707a0045c02075220700c1c4243c0301040395508520640c50040c000301c51004200b020a2000d20151030042c014540c02800c00040340c2c9030603036180c0c1412a46d0403e03030f2848803103003600201c2d809594080c05201c260720402d0b034009003040009800103c00302812520701041c13554849000c0140001070314a030100c03070b402154030000141648560a02e101d0840e00030350b82a40b501011590042500b20028000d0800304500d000c440042c241d0004151409001101544010400c030415a1542108000180345a8469212148090a0242c0003c8607841800565081070f00310100155545041c3d940074003900800175100e0a082011543c43c503040242501d07141404100e05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582806312 1250 582805062 582805079
    0xf030303050f100b2a010903030b2107090e030d09050303271510080607120c03021303060f0e010920010903050309040c0e09070f0e060702130b040603080301 69
    0x2140148809002541c10b6a15000308802c03800d0a8016410402001c004d09100400e00c40b21425900c1e810300c4100313150f52900001c190031119818000ca001c01c0c0c440032a078ad074034a4030f080740c43d0812021405440109101814980e1035501d280540c0c03032550307a5480a1181d164007001500d041d032401010400c0210401d08087e66070350001c8480c1c0d04a550105d001c503100f0703039400a400d01403030300076001441c6040071002d100010300380c0202585600d82c2d648100203080340c0f08010117400b4001680741ca101041d1988440010b8400e0921000249801040601800382d031922083c0101c0e9003101000403e136000a16080c0903241240942d022507003000c1d000c201b070005030110070000080c050540782c054000309006481c031110512000e8165042800b200750a0b0515801c44d101103682407a28980410074100000c01d1070a040d100040040c99174006010035641244c151018100d0464045003021300740e90001c2c501c0802c03120014010b0382c0700e1000d114181c4072500440c1c0610f5108044036169030b102c0c0c089 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582807562 1250 582806312 582806321
    0x60c03050f070203090a0b09011b061a0a0e06091b0c03090a080106060c1113090302010b010806120703061e05041202060f0609061e10030b010201050c0a21060f030303 73
    0x140d1686030308400860700c10b41c000001c41d0040d072000b910058915107444204000d07034001c8420503040c45003403113169818648104800c030006119042c00141c00010500c3c600c460507e5080c858043c031072103102404101040040076501c00d90403900f00c4c003a5074941e0014585010031b00318600611700b012035244002d21010024240350b03841981d504604a581e40702050a80e0f4583c81150040350303104101d140458040349007628a00301c003520b06820120412602c1042721248001940180d5440205000c0d83d82d0118089800a50407940b000c4614852a0426250841848002c01d52070b80ea0012000700c59111004a1050304800010441d520301800c008408421010010300140204030018807041d1780020107078010302000d803c06041e5920342c000d001c0d025540b05904405c1c0e402c50081d040c010303a00c40c81d00b45220b850658001c40e00c1c00e130810003e82580e5025010145440d000d200207003402d5800400c1010400c850413400d2128010584c01d038009200d150018010790300e69034804818190036411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582808812 1250 582807562 582807571
    0x30607021e07030b2202060d0b011b080301170c03070b0c07080318150c0d0e030c09041a100f06170601051303110406050607061d0604050d1407060c0305 67
    0x81401c118640c185580c82e0401c0e40030007424141e60388007140c061200341072030390044001250b2030441d44c03415170000740c901c2d0400ca1003ca00940c03030390407503401960700c040e1081c07008002c19680c0728074200c2941d4003589400705006154500441d045400b90b000d500304040d1415040180507518401d80701c01d00078903c0d030301020f000c00c401d00c51034000080012001088400300c0e9117070401030001803003d0301000340d2101404181d28142000b400a0302c070b1504188021070b001034003a1a40c0c078862004500380f50501115550f51481000000100004940324050310306100d00c0508410040366200781300da8030510400e4200c0c81c02100c01d0702002c114107030015402405810070000c00b0341169907150046605110b84440045981180d8104000140864030039801c0301c0d10041020506c1c03500c8a0218240ba002080b095174519121014003d0000302d000306c165a40004c000135050b0351030261615691000f41c1040b44042021750503200d00c0408107007041c0c075160fa5004100703119031150100014040d02c1c042e038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582810062 1250 582808812 582808843
    0x204090b1b070c060e180901090c150207090203180d08100909020612040303060b0f090910051807020c090403030e0105090316110a170708070e3303060702 68
    0x105201e01031001c005540c2c610342d00501140140f0f0400c0b80440d0103160ba807004035005101d900904480703403104418184211008800045c00701c29504091400041907445064440040f240b000100e44e8003040000a0710310300c410160342c0c0c1e1202500d45000e0003460402e11003e003e056140d0114541c0041101d028140300c1c584990032549624041d400c90b201e0441c000d60051080040c40322502d58100482d50180c00303030400050341d6641c1c01c000700c1301d0340c00204011000388001a40c845945011403445400c8441c2c51012440d01d030404006c243c0c00804104c10304890a5800e000841c102d200700850180500c014054140c0c600741442c0141c081e0400c5074101c074580d403c200004515503800415140c000118a02c503240420f8280c50f0320b4581780c07018203440d810000c0d0703070f1000c03441c0054801d080038180e074078000030300302c03076142049480c28005903402940b20450f800042c0000c1c03a031003800b13601d90b865600c6113400d02d00b0b20044495941c10410041160540100010400b9150f0041012840c410001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582811312 1250 582810062 582810091
    0x2030903040b0a09030c081606030b0a0306110a020f0705030a02012a0b090c091b0901021504081e0901051b03090a09020a11031c05060d060f05181501060315030204090b 74
    0x4c500c4c13240c4804623403a10324503141400800b08035039031082d0001d054a10002d00020482500e0761213640968034409000040f4a0b80002c2c101c000544c10000002051508000348c5081c1d81040006500d0744030910001e03040000803016164103052003410304500d040d03d9600960400071900d0401d001140443d0380c000d840c001c0990025141c00d100d14400d104800039040860001c030480c4c1c5803280394121003600c3d411445441c1c40e000750041030a010034040c41c090314103d61030340c00d2030210a541403000d816509503814107102c0700b0401d9800c6001d0b6003050310f60094904000306124400c83c514020108030a9108850410004440540342c4c01400c0d408095035440110601c56240b095070784c030488100300b010b07643d611010102c10001d9030041c1d4110074001e2a1106140d401e03201d000c141c500394000c00303003403641d02c606200b05200c042c0802580782003001c1c082c2c035207080300c0706210145140c144151410300d51200c8110440030501e07034804026607030080041222500d1410802c024107412100b988008001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582812562 1250 582811312 582811319
    0xc010c090501110a15150b040b0306030d110606090415022109010b0607150204030b18060f0412120b031b0901060302090d1e0b04030230040902030903040b0a09030c 72
    0x300700d01c2c140d1a0400098122162031904800091100030b0583c0086e503010440030660401c013070f004100070040c80d0b072540c0d181c4c20f01204250030601900400b1003440301c1e00450700d001c81070220381c1e580d102c6e0b801c07580f00400d075480d400c1c0070440c0f010503d429900d091001a00195800f000407070069084035521106506903500304543d400c032920010103a83c4504184840000210703140641803001d030341018058201603030b030b0f41d42c001e8641096502170030340c0f00e40c000d0031403071b12104015003035001d070700320386094010309050700d80e001007450f0a20054100182035002d8042e00d0359641000340b90550140c01c540c0002104040800c1c00780c00400c1c0c2902c5a40d5040c00010060310034002e90301008402414400b0300c110341d5407021008044155854103001020300104081604030030024425230198000d420056020703984c216034160304a007503031840c411075250440b980c083d6038166400e94041c800016540c0d02d0f0f000c0c2e0f1034514011070744401224003000500302c5080758041c640340c040307a21544415144d00d45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582813812 1250 582812562 582812597
    0x7140a091812110703020607080702061c0c0309030503061018080d0e0d02030d30050610080709140607020909011409032104060b100f0f020102030105180601050c010c090501 76
    0x200d24000d10691340070361010f001618003000103203622403107007000500c0e00a0b0703940400c4641d0080b00c1d0303142a4121038042d04460388550f018207a84407800d45005c000c1440e859501a142d400301030150741c082e06502c0f1550780d08034041d4805120a80310050010003030f07603580b018103a0312100081c3c1c6a0006e8020602c0201600307000d000a12240d60040c081d0900c4c19003080222507400c1001581211001d05002c00c01000720200c01d410006408004c001ca0145040c0c82444640800d068046041042074410001602c0e40a82c601065074000d18000c8010402040010000e00030843c01a506c01ca16100344070400b081540082c03139103211780c1802100e0340c0d18008115246d000d0b41c00c0821124543e0305030480c0a40250381d1701a4400d104440001d0720103008808150111030020158010422841600c0303c910341200d2581420080e41c40258074543c141408660f400040d0360340e14202c1041c190100d04180c1c080c9003034030421702c940c0b002082544000036000700040c1291040341d012031005100c0c40c0c910381 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582815062 1250 582813812 582813827
    0xa0b0a0e01150c03090b1c180f080f070b1603050601140f09220506040b0a030c03020609041410060e09160e011809021209010504030207140a091812 65
    0x542d00020142080704841c410355141e2407266046003080a80d2801061080110300a0013414044840d0204c558000654060444110500391141480c18409102c001a0355103600480301c0ea1102100ba21082c000c405a0310b01d0051510040408500004202680032400c0c210003034040c15540c08d012503210344005503409042100a80c196400800000381c1c81d25016006216030315020380310a01440f1101e03542851004900410200c458036102402044e00e400c0c001c0f640d03250f400311a14071170f1600c0c1d40d075140d000a1091000034001c0002242908040c2c0d184e6100b50240c6d10004803d40f01880d1000031000030203141e000311004905052500d990600742502c2140c4201d418840c404580c0c0d05240040d030b6690000d860325810040c00303001c8a0300c1b5240050203d80144903041c00961a5a500201084035000007000a5030760b070324000c2004042540056402d040381c401c1c60007804114000301c0030403222415500100d070080d00304020302e101d0a003512410440d2034003651a29a28100e200340c11038984 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582816312 1250 582815062 582815069
    0x507021c020306040f03090b03070c030207061e111216060501061b02120705060c011409010c02031e09042c0601030b060111100f0203040302150610050c10050a0b0a0e01 74
    0x10780c070070000034002840300c0465905c483c1c024101000c41395070fa0040c0c04182e40c81241c3d040001103d050f11002010b03010031581c070241c116810400d0084062503480411100c1840180d41003000c94120750003200070a01119803c0c000035100180d490123512540b0003e10941070301160420301e84000060140d12542255a0440c0070042c02c41401056400b00110003d54500140c3c590050140c00501c03951954000c102031030310200046403038001600030781c07a620002040a9016410100940e840c0d950110440715120500070426140c0c5581182031409400345011983e085850482e01c00c1083d855503100c2507a810303001c8110220407a00f00c0c8030340e8481c0802c0c44010b000b1940100401c0556004c0c5050071800d07000c80301214100c40910043e50705580c000b03038100306130650010520003895414001c2540b50b400039010b800c1a400c18402050200c0c1b103d112007000c1220114820190031400d20034103514400e504014002c034140407001900812050f0302d142d00c03a09040da0b0000c0e0138401802408c0c100d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582817562 1250 582816312 582816319
    0x4081c0f0e0d12061a250c0501020d053a06031109150a0b210f0907050a0e0106030504060f0203190515060304120519020303190203270c0307060507021c02 68
    0x1081c150340c00c0f140990700503008030f8120301c6c041e0841014010b010002c5078241801b074103442540c00c0c5400001390030441d00101c100100035040003140c10030a00d50300001400c05082d01207200c0138010b04444030004440c12031102c03c0604101e000401d008094002401194045608440c25100c18140d0b120300101d18012541003144448104003010307800001d001c4107409080148110a5132003a0104c1e00c120031a88083c218198506000382d501d01002120b000c0d200070b969521465041030301c2d850400d04148135160415480d000024100a107581000c111400080801c0d500c1e0f040001b107890762105a590b4070301141d454540003d801d040700301d8102c1c81100000d0819461343d1a241c03941c00000c3c40046118050200401c41080c00c684d959902175909070056016540b40d0a081003251002088501d600c1d05940c018404d2014600c05500c0b040c1c8020341c40c064480d008420b6030b22442c18031208561540e41030203290710009519070403070700400107107100301c40e404a4120b031030b80380c00c45120060002030341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582818812 1250 582817562 582817589
    0x201020a12020312070804151e0915050106020111030a090507030c030605150303091c060905060103080706050703020405150a09322407080c030403121704081c0f0e0d1206 75
    0x450072510f9209e1415441d0000c2c280b4410110302c8001c10540d0100c010485004180d11200d4041032124828a405403032648000e22200036042c0d502d020a0002400522503241da035000e080c100501044408003c0d580100c9451034941d03a420414020305c011101307486801442c250b0302c501407402000b15084c1550080c610352483d007601805440310f5402c0c4500701d4405644026174404914208040b50080d440b56001a554a500d4a040346c1601d80152071501414014881448640d8407a401d504a81040d0520182ca458a00c1001c855290240c1c0c4181c4450301403007a900e1a2074001c690800110120f400d0f00144a80003c3c1480540800c403050560008140151405e13a402c500c401484081d00404030f69050400700c005043c00d65100394401ca0f04424038039044501150485400040e032101003101d01200e2811349c0364060284034810340382100840400b0085107031426680030324030b00c0c003403528200180d603030840c40c25a86d54440e100c1c8a0101c1c4200a0341e03e500700c1c0a001d10300c00e48006208001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582820062 1250 582818812 582818843
    0x7090501050315010c02041d070f14060a03020d050103050601080c01050414090903190e040e0102030f06040c03021e21070c02040b1201021c06080d050304020d0201020a12020312070804 81
    0x525031804200444e04000c0c400e0003000c09030341c41c2d01600d001d00d8002034990700f40a02e042042031600d00c46502c840020304060724104820b4402c40304807084810207079009070303558880020440003885001081040503141000120030304c5400070303900b410b90300f003001101d04114003500156058004c510170310640c0c058032131a096060070311000c2c0b243c02c4058030307040700d0a00400e0b0380f5414031081031245240024440c108800350601c0c00e40100000e001000008510758100141d600c0c90202c0e0040550380215291307040300040500c01e9049403510f0940c81071424140481000460f4280d00c019180e0000d414950301c0c4a0707a054164450718010764164403030103c4a81c83d40c0c02c1c0406401d000d40b44581c006000e19142084078820300003002c2c0b01456031450b58a00006024441c115007207500b01c0d05055020007200482c1d503802000b281e0700990126850040c074421440101d01d0a00b044030010171140e2414039155100e600000507151501800020800550300c141007250391010840d0090901c0c080d02c807608 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 582821312 1250 582820062 582820081
    0x30801081203060d08040f0e0a0c03021809060109181e062106020f040603090201090902090307270606022a01050f1b0d050403110d1a100312050c06070905010503 71
    0x4184c140700d058442c0c2000e40d0740c0c6a4a10044250b80002c4c440172102081007030701c0f82c0c503200d410308410f01d80c202142803415260080890311480e03200a0f002c2c2c0d18510103d2000e81c05106000010083d0001d40344131700440b0115a006055005011400a07141081d10030300307103c042c0901425241c480e00001d200c031381e43c491030510001841000b929410340c00c10404281d05000c800805c045e003126280800e040307603144001007581500e640441c010305c2c03050000d103039160ba0200e40c010441d40800d500300d041800301c0c0198010840c89a5600505901d80700d00040c0454000c240e050007000450311940028810f040c50707880780f25640158a0006008000101c55807603c400034110040d00c2401e102700034091583c51030329106405d004000030440c042002c10400000c0b24100b04e500d8000d4a910320383c00034075610409042c030340c00d0084110b0b500035000280d00504541040004541080340c2d841403001c401c90250080d888955200d215004040c00207035203500403030100e811658103075101c901d541c1c0ca54004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 582822562 1250 582821312 582821329
    0x40f060207060c1d121b030313091e0507360806010f17060105043201031101080601211e05090d0f020c0409021302120403080108120306 60
    0x46404503800d1000401292080c814040d5560180d2211122084000d5142a10799048080d05205002d041c2000c0d00300300002c203c01c601001005240004e080c8202d000a0a6020342180e41c800311b9071000700010001d8051b0415001110854140c1421103121040c2005031038049075443c02090b009910661900f451448010078400304950005917407885c2c0d185c0100d0785851354050074031230f40130200510101041039901e40080034200d280c064402009030440742c54000500c10240306d40d9690008203d00004080129000d41c1c41404e811468103d09000005035002800180c0d056501c4403051030955008000b001d000340c3d0140c45030340381002d21110b41d150003401001c58044440d00c4030043c404140d111281c45800785010000894a881e00134042c9240101d81d40c0d03200d0402c00d8540e001110190080f480b8003440710190ba01203400d0b80b007800412116404c04079811201403000624500c802c0e24402464000e6100340d580810b180da0f03600c84255a1100105920041070042020a80610b4511074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 582823812 1250 582822562 582822593
    0x170304030b04020a26100e2d1e010b180a0908040b04090e010b181803120705130501050301050105091c02040203190c08040b010308091f09030c050f0904 67
    0x1321003001e480b82c840c03200d43e80090020302c10401c417207061441a1482403054a120010054081261140d400c54059450404440aa204030241e51011415568030510720b540920030200301c9a03000c81c88011115108403006203c103903546068070344091840d054450044600c2e6034400944c044d2200807401d001817051602c12a03205404100006a0180c87c9001e48020450054000f552a41e182461401c0d01c9000410304e01c21654607071244c0884024022540d0400b4828924407d8001c00207c82491442a034005c4040005000c08015406501c01d00130822021182e086004c060380d00c01c01520680420702485001c40e4040c4100d500e141000252080000c5203215614290403a50300071600304e0380302f81c852000d103244454101c1d1003d8002c0c020642114240e15203100180362a8036507010440c811300008050000000d1040b905d55581d19036204a03004101407065141e80c4140064144681440111505050b5910004680c500a2a00003054102421640c0b2956a40d950203010300e80010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 582825062 1250 582823812 582823819
    0x7060e040248030405370f03060c0810141801030c1a0f07030c051c11010b011409040506150d0c08060306090c040b010207050d0c0e01170304030b0402 66
    0x1a4800c2000400501d2458a060a5001d2140103101c000c030020003070310031440111036104020400c8903880d805564540514031001039208001c201000404001030b006540782d41d42d01e1a10041024101c001f004c5003124440d00d0108680d02d180c9800344c0f40207100302c80c2900c2d14095100104018981c0301440006290010312040100230190070744011203c080c0c03c2a2200360713031810305104241c518110400f840035014122070408145407040c000c0362145441c01020030000420b8503080003030410401404680307200300180b150b0750801c0014011619214500340d250b08054a0030015401030840400d01c42d01c00c038000740f42095030002d000140001900c42c0e60400038500c1d2591404a42034003400408080c03900101d5012041c0900a0034000098036041c420781186040c081c5041c8005080c07c92040107640119080b00d4800060341010b40d164416504104804500c40030000e061440c141650b05031030110b0a6a600c464000c4150040c0d00480c074141d52082006001042d031442289a00502c0103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 582826312 1250 582825062 582825097
    0x8040b03011d04031d010c150c14041818050105040501050402030124030f11130b0f2e0e100306030b0106020c031509121c0506010509030c060c031204030f08070207060e0402 76
    0x8e644e07140c246c1e051040110348895a82e03070300c176141075802403038078900344220407500d03040909014040302400c1c4046541d141c1e0583c0c40c0c92098448288000c400c4201ea0888020082840d040c00d286018050890b41240f081d4a01110080e40c2c0004507620450092488a0001140e00311b40e610000700b50300e00416503c2110811003844580e54661600c16005c0c0c015602080494a1400380a060044e110019101d2444a2404100041100d0580b8800f02040744000708820a040e010784107495140405500700d40d081107540720141d0980c1101080b40e104a02002480c3e0740c42c01d04a03241c404400086030b01d900429006814802001d40c41d1380c105242c3c2080d240702d840200c140160700e0744180e000c802014070b4040300351207001d050b110f0143d10680a003040741ca4a140d00002a86549828120f41d104802c0803502d00341c0080200f00390342c84400d00440ca94414109810702034042180c40140c0c46c00500400b0014040c10702c00b00d020001c0301c42c0c64540c0078450100382c0400029401c41900d05039a1240c3c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 582827562 1250 582826312 582826337
    0xc09110906130f0303090306051b031603060504020f1201080d0e01050705070b030117010f0501080c060706140a090510090b07030504140601030b01080c0f13051308040b03011d04031d01 81
    0x7030386810f0001d5204e42c0360122001c1c0b0b1480c06006071280104500c4429130f40c1082c02883c02510011a03a00080c1940c2c060107010303c214050f00100559080590450b10210300c906030701d0b2001000f44081c40300e14000c0c0750a80c2e45c0d280010340d5038030700c140c1c03001c009401e8030300300d000c25401034001c0c007400ca12903425220015201d900741ca010790801da209911501100c3da0700750860400780724031003460f4451441404150b047c02c07141075603010300410141c01240005420340901941d54011400307111161941c540da0b0600e509080e015001d04e4900399190b01860841100100b0b240c401c182046510010145007551521302c1131707009040081090724442080c100700c10070b0480c00d110160203107120380900c850703c0d414444214600b03000b2411590007041511441c4145070707201d24400061180302e42011405940d5490424000100c5180003400c081001c07a011684c504801d000e541a40d0340801141c0c1001200d00d00c144803480103442c044c011580e21106440b00c801603081043c1c00c0c91043c18103180e803158 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 582828812 1250 582827562 582827579
    0x714100513180f061203080711010b0603161b0b04060903090b070b010e060303270607021804052802090a02090a030f050c060f030c030604060b070303090c0911090613 73
    0x1003002c0d042010307540c0d43d900c2150500240b080e64040c066107550342c0c00c1800e1a6502034003004015102d0414003101940c52140d200c0c0940007013420103000f400090b200e04042c040118a80d030045d643da004207139a10221580060000408404c048c0c006084a040b034659441d40780003030299010035006c000d2809404143d800c8204010000c40740315903a201070307543c07414181032059030016082c1482030b0404c02103800f04900c0c1c4401c1a441c3c0882e10004135a00740c0c450001a000c0c450110000e4201c80b48400d210b03c1c5c00e41050f03600740700340d0090080d40c002d28030324030308000c06289050303829800821202c0303282d001d4100040d600f640850b01d400014600604040084e690416035482220701403c81002082000300c140f01c041c10340078054541c0d6051800506d460703000ea010060441280700d0300403000030b03243e54442e0041b5005019140001c2d40d10b1205041c010041c114107442510035860b1580001001c207407912540000b03142c068021410150b4103000c0008aa00100009442000420b4041461034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 582830062 1250 582828812 582828839
    0x609051303050c030f03010315050606160305090307050a080307120503060627120705010306091505220f0b100f020d03020703030b031504051005040201081909050601090203090714100513 82
    0x6011b8000c581c2d8001d9aa002c2c89c0070385400030032a40c00b8100521074504041408680c04441c0d80c4e15086c00340e19100101d0202e07180034030692106521030383c4000c0c00a90000040006d0060754040d0051a82e843c03150f04060b122171000396049500944100450f0b40545010744c0a04183c50001043c41040503120001a5048030070361156030307140c1c0000c3e02c20015036070541304460081c1209501446920048010000030445a20500f401814400142c2d101c081d42e070900c640450080c2c0c03800304003281c910b50f5810006c2c103c0c5d00e441e5000700c20941000f0034650103000380c11540392031603000b000d0441034504101c002c5d41000404409160311160030351503940c1c040c880d000171460845074010312450641030035032030082c40f0a01d003d400c0f4030b05000c1c040943d03404561240c1c0400810501121000c40716040c01c01004081c00c013600d14001c480011071511a25001517004140807021914280d46032012042080c0355024407943c8540b03074403000d0452074005c03805400212040303030007005000ea852400c3d03c1c184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 582831312 1250 582830062 582830069
    0x306020f1308010e192d1a04020f0f032a130b0301060e0c090603060d0501021209070b0f030a090804030219051e0f01030e07120f060609051303050c030f0301 69
    0x1070b51940d00340742d02d618040114012001d010305d074540c003200298448091402030b50454031802e00346404030040c1c0e103d40c000e02d0742c00554000c83c40d22070040202201c8002d0710066034200c2c410403d0000c024110326109200c4034003100c0003400740c2410741043c0d0303080d4112804194900000d032140810440107540c0c2000e0000c14480070000400d01c910305000700740c01c44109402200708900c0f8401440301c8040d200068900b48641910310301e81c1c0e9140d07400040c036101141a0010841e60000411007403001c5910300c924002c1d41c007607084400071910340044110368054000c9000c0218000e000003280316485e6005081d9090181f503495152648075004954000c5807110000f5074401c00c84c0301042036040200d2a948004c803021444001701180e0070000c2d88003d01403a01c14100b507224145404008414441310006102c40c0c4181c40200b400c070300d040c44290060403402d40707403189094170004000d400c5000b014802c2c01c240c40701c2a1070614507502500c09420207060b0030503c0c0300c180420724840d222800114081c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 582832562 1250 582831312 582831329
    0x2b0c050705030a120e03071514100306051e0420011110090807120810150503070c0615080a020103180317101805060f030a02030d050c0a1514100806010306020f13 71
    0x41c541100303c2c034058942c01032700610910425810000d858507280001000d49600031804a0551034090580e908090f807400c6011444801c0f100340f00400c200d00100c031904c40c0b000986424908c814500664008013003244144894201120011889126620045915208041c1c19082142ca03445a0994512925050b40440c204000b80b00e0030a1030f41e1022001800f607036220381c10350781400200030410b001c007418220071303c0710840c00300080151035080365030413500d0001500307141a0754200082d40c5400a4000360b0100346031034280000580c841000850054240e101c0d00421220741d1280f031041440141480c115001a05002c03030044490340b548018220820740c040b80d0b908168081041c400c8290a64070302c40c0d40300c03038060401614085a503913001c00c1d0b0342c201940c8452005112505008101c8002040703010f02d061088000042d80e0b00101d45069400f000000c0d90b990051403615a043c14042d1104680c003c00040000039815001080d505036480d40c2c6a09101300c810310b41950718590b4002000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 582833812 1250 582832562 582832583
    0x5040c1e0c02010915020d081911030604110304020a032301020c010614011d01030f0207210305062704030516050c011d0121022b0c050705030a120e0307 67
    0x19907a02260060250170700d101c82c0d10300702c8205c1001a580d02c50070035244d0284542e000c0040c2c440c080008007101c0c0c4e48801241400b29010001c24800598422554140301e18030b0712000700c0d841c00010b0f0a891155602910712034040b419502c0300c469401310036915010010070030210024060f02030000d403108100000c0003040450502042a0840c00769214507410001d9882c10422621445c00354402d50b01400c2c00d0000c2c080e0f5007000800c02911441202a11400038204103252490362b00403462800800c6070b40410042d2035070303001c111408a1900d00112525903900f181103102d005c41d020f141d0024400c2c00c0c01ca1405031106c0c2540c1200850ad4410b841c41e4100b10b90459640d60410190a40c0c542910a00154032001d1030003e4008080010810007040c0341103102d121070501d50b4102c81074901c43c400303d4000d845050f0060400c0c3c0f80c400240400a078201049000d549004200340d40009a1000255007040d03102201180c5404407840e40114081d190400c0c40c082050910040000c0c0d80144100701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 582835062 1250 582833812 582833837
    0x40e21031506090603040201030c091d15100c060f0204030f051c0305101415130828033002131a030103080a1416021906080105040c1e 59
    0x200444440c0c0341c410300070b0400b08a032900d40d0340c8010482c3d03446582400d00140701c40180e0300403622070344035800c0310406200754521a4000782148202c0c030310030501c810001e44040002c00030301030340d284c0b00041040410043c080142c0040c0d0030350022881100800001410640e0300c0d203510300e11919180d01600c81f81c0201d40f65845c48a0141c10044400200341401e1190707040c01c50b0085a01a003c0c443ca0340e00b210b03a0041c000316079036802c0a440c1000180750b812510360760740207021032070980a845401410b2003a59806000106c01140c1f9100e211a058084200340d09503450039544120080400761442d51000d001107001c800e4149042c8000c00c04107801a142c501c80e502c8a21008140d801c180c0d0204d0410500c07503400560360046a041d80d1b0b2040d551601e5189640040d9501281c529095009480c045074010b000b144800415103031078000c0780c68080c080203070050319516080c0360003401d00040440c0e00502c0717142000d0708035204405840c43c0141e035510001c0b54003c02d818084001200042542c1800c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 582836312 1250 582835062 582835081
    0x8040f03030e0f090112030201150e0105091006050d020f0d09060506040b030a0b13211835030c03070b0a1118010f0903051504060524040e2103 63
    0x1001c010003c1c1d480380c05509007440040d020f228148103410724500f02e0014001010700c01c0d002404007818403c102c0000c291203480c03050000009004150065100000282d2000800c600080803940d4a4840c0c074a020b01034152407020394842c03458012880c2c410010301d10004020701c41c020b0b001b0f003d104001100c0c01c010781000282d850138030346140b00c0d6010020907004502000801c0703030170030b030040d8090740d16004900d0a17040c1034084000c0400701421b103181c1800455040070035a114141204580e404040d102c00b17020308620b4017501d05041909034020001080070f03900c054483c66000e03240840b418a82020885450f47d0710060301110580b80c201c06001c82d80065011381041018280c0220381040103005c15440741040701c2008a0401111882e5042c01d140260100f1000e0f603002000d07924544420561001c00b40425901152407900d007100103000b20210703140320900ca8071071622100c04101008104406825940c0404050b030203414440403c2c20180041d10301c406001303100d82620f070300e03010208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 582837562 1250 582836312 582836327
    0x3030a0507140405180a0b0d050a02010219120f03201306020a0b13020a091113050118260604050a050f060c04051201110a0302180a08030406050c0a08040f0303 70
    0x40340e100d9038043c0814001555286298500041e440c2c070354003129581e4080020240c14032200c20341d00700400303034008020b001c804950070b81e405000380c00b110750800d00c003200486041c0b54850040c0c4401c10780810040c4184c800c4c0100c84203000c60b850049080401c950114083c1001302070350041c050000229042c03100309203a00c0da03000380314500182403602c1c002c0d10f47e1500d41400420010282c0164410b0404543d02c486e21800504000c000030001034203d240d20100039031002913007102d030301210280043e00d503100e43d1010800d46005041e18001d04d01d40075031042c1c580300200300c031007007030060701074100081904002d040d00c540d00810080501d0300d524185141400002c248013103164010f2010040c821000f030b0300b180d088910030303101501200958002c0768018211500e02c0c141e000710000340040505d50640242030107000c0382041201c070070070050400c81c03e0850b9204624545d003003404100301d100e00030340180c48464649001d4920244441da1400c281d40d00c20740190f42203910783c84080c810301d9071283c0c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 582838812 1250 582837562 582837587
    0x70501080604060b121306140a0b03070b041a0d0c050415030e2d06040605010f050111100510030b04050105100b1608091903080315030a0f0b100803030a0507 69
    0x2c0402080381401100b903654810a0411044030304400081019072901d91010104550000410001d480040355620311000c01560308103442c0782410035a009070310707004c50004200d826804010b4030307003850091010741600034000d0542c4105014006501076121500401e8031406a550301c5c0b550311400d020b10803540c40302c045110000c2510b014001c03070034188002241a6812201c0d402d601c1d00c0680b149580d4081401c2103100041401000248410442981c02a0b81600c0c020712940c200a501d84c4c1c0119212498a400703111a64010024660b440195074000c43e00100500c1d21442a1603c2e5242d0b05200c1c0d078180d07411246a95a0400c10039048030204115001d441d8001006160800803510094000000040901103100000780750401d661090741c00044071a401c69202c042c01c2d036034144038101b5042160480422040000901da036880c01080042140790f1000e1141080940364a40d000d414000030071601c5a44258540400c2e10001000650720885c907001012235580b40405000309141c60078038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 582840062 1250 582838812 582838819
    0xc04050111060702060f0604091a06030c1518040b061b06070e030d0810080109030c0203010c020303070c14011d030d0e07050d0303020c0307020a06050d0c090b03041e0210020705010806 81
    0x9051052441d13005c03444a411803683c0c0740f42c2c2080d4031002e000030010410004018410b440d07402c101c90070641a10303590341c8074110841c1511012140d220900903400b8a40e80d0051f80c101041000c610800c6500200c2e14030344902500010703c8014407000718182e503004030f508a44103106a901200d82c41c00401903181d0142d5185451003400044c02d0200b0303a034689250300302050241c034100207034104e906800c0160003407820000a00a44440d424003400c10340311180168025402c01040e11542e03400002224011035a0b03545085509246807241001d101018920850303654a41d0b81464141c5d82ca03444824184c149540515590100901102d08a92030802101c040e600086010400b540e00d03243c011480c10b405003009603460700c2c1640344034214400c00304000d40c421130360031010901650000150820084519041203840c0ca404015180001d00c1c2c403c0c800482402c200203000104040c114010030105440800c2c00141c941d80040c080c807484031050001a406000100020744e4801d481c59005482034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 582841312 1250 582840062 582840073
    0x70612090c1805060a050616140d27060906110c060a050c100e1b04140412080a0204080c0d030309020a0932040204150b0f04181506030b01090803030c04050111 70
    0x441d8141c000c8c00b905405010708a04094144004008010a50400c15060302c0038040c102c20090302c040c0b01c0c2c01c581080080d9034950300450b00489205d4005a034550f450b00c8001c07a00d4504221000d03142a1940b980501486a00c3d56150701e0741009412040c029860f010b44400c8011001490300e034440c888845120b04201c1824000d04012138440001503020104081e40c00070880490007501914881e05040aa030714200000c0c4544000020200c041541d2048040d450304203001082e400b450052072015044030031001c03d42d1901394440050144070b801d010910000b9900010701d082d540c1e07400061600c7d205c005426a92400745012503000308825203064468640054a901c40c0d08004c0c03000b4040d50f0303a203080c0384801a038045660014202c40d10016075807000d120b5204201e8009100b0140c80680b011403189030b03441a40a90320310201c1c00c10b81b0b0008645040c0d41100a09201484241400407106c40403903001004c0c0021446509040c1b681661240b4000006140e503000c40f02002280e0402c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 582842562 1250 582841312 582841319
    0x1308221203122003060a030507170607020607080a020304061b0c02011b080d021e0a0207030209010e061e0f030d020601030b0604050c0316120509010c0206010b0c070612090c1805060a 80
    0xb15030080f040407280141c5240c403540e40801003005c0b40704d180c001905a00c00c4442c00240045070069100540c0380c10000d448560b10b8110050341d880d0000d480810100c1c4601001032220100c80d405035600901892002c280030941c0c1d07804000c554081703c41000080c103880701240c1956046070202020064696040100240d1a150381c85140240040416029000221140120101c0e900c0090028940c8034582c0d076843c880801940d40c2500d4070049014008071000024012180c0c0c6541e485040041d080403c1175505000d00f403901c0ea40d04441a0f8030501d05480304029460410803c08501180c0d001040194150f042881402c503009001c03d105a040c0000c00c0401c45551007500c2d00301c1080354084181480c2d2500030398404d50340c501040380552522003004440401500001300c2d041c0e01d5002e654403640c072401d00503001d1003040150840daa0200c1c404012a134414629410790075841d0000195880c690303510a2010316065211202e80c2c1e00150410340016464490ba5412100c2220900001881c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 582843812 1250 582842562 582842591
    0x50d0206160c050a12050c0609010209180601090305071d15060405060d06030f0b0717071b03020309060304060b030f03040509010302040b010c0506070f0e09130822120312 75
    0x20700c44007941c10000c208190704100002040302195031030b8824140f01569040b000010b0150f0003a40c4000305900c41d175004141050011320880e00f090300081d29100c0303401e6604050781c0580e40b0191440c5e04002c010030b400400f191040c0030100c00f40003490b0740d039030502018545414103540301816144442240310221041d035504c66048500300c5100341c3d51540c41c0c0202c0d003c50f000400180d80041c01c99918a4091001c000204401904c681d00c1e139150810b0942c02810305c10a2804101c5241d8041003645854600500101c03c400e0483c600c00d1044074030308080c10020480303a42007034408984054584c03c41c501145000e00800083e80041401541498500000245002010310019006030340e1015100c01d564031a07040980b140340c219044600c0c5084c494402010240808100c200040702d08540000c2c0d858032542280c001c08482c20b42e01105515900d6484c1d059000407032104880006402003011351b180040714800900c0507480070030704c461040c20007800841d094802c1d400f55920f03004c01400d0841 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 582845062 1250 582843812 582843841
    0x1201050112122001020a0f030207031d0a0306150f080604050d032c0d080a060311060c0a0b0916050402030127110c0601030c080715080a0207060504050307050d0206 72
    0x260004082030148407802e1080d124000b000410342c070703014404001d200f1102015001000312094070341d1084034000c812071045003240200c17440200040e499200c40c140580d1070a0a40f020b10600812004e26159243c0d68442140c102c018202c2d001e0306618810010601c000001c81c0040101ca0f01924491601e0f0356510344580003540c1e12414507a50741e0788502e0b401508003064105a45031200c0941d25021a00000d81c6e800c0b0034100c40300060b20000003d01c112880b4016441281c0d4001c051308442221441080002d8018525181140c03140a44400100c0c0e08000390303a0007070724018081c3c8140c031030104414810f000c8a81102e4020350042004102e44488404c118045440068628402e031300ad02c2c8891018001c0a0503405000c600805d08508c0e10202290045c101d07441108480c02855803130b0342e1780e0740b0f401d07051180610b40c410701d022007905180201e02c0742e030303000d10200c0006141808030380d510401c640081d1401d95a1b540081490300410004006d50840c8980f50700041c03600e0b24100c0c10011615 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 582846312 1250 582845062 582845099
    0x1513140a0e240a2316091206092904062901030b130203160201051b0405011b0614040b0709030b0c07060608030309030712050a0f0503040203031204060b12010501 71
    0x81002c000900a4075480d440366001d1040c505046400f140e00054010212205984500220390200790703c1a02c1da010b01c405004880102150f03541401103900e4042c010030010005444c8402e100b469515030442c0340d214440006800003070390f4280c2c18541010411605915130001c41440b034008410034032415a0030400d41190240ba000c101700748441d001c1001d145401d140e4082a50001c8103000385c1d0443d1440e0400f0400107135008120300e640d06460b210301c44140f030304460705901d03082000b8441c9521034612415032120840044040320071a649050440b4a4021942c448070341030340038403082140e96840260415428940150308a045880c0d1605010020b011484010800181036003002415002000103203d10360950b030716494801c1036a910381c0d01150007142d8280042504bd6400b9000e00180d8400c28140d81e80e40801000d5034800360341c20b41c00034105a03810b00c404d10010f698000b011440c0341c4118480c02001c40e50007100828004069040099011181d040c00014400000601d00c0700c40c20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 582847562 1250 582846312 582846373
    0x21b010b0a090c031d06060423040602160f20190b090102011401030606060f081501030b010c1b0609050609031b040204150503010602160e1513140a0e 66
    0x1002c64a0f10154001d282c0138441d500303058124a84030310740c07001c0401c01070320402054405000305811810314103064400101c14017005102c1c50007082c0850000e5002c0d0103403482c0007002c005000900d849180c0010340c0e460013111103002200805043c08220a01c44c20f50600a81e0014000500c04403140358507940d6010b180c0d160341d000700345850960b100750003206030b0052000c00c000c0d10356100e09004020348294003034840419400c00015091500c15100f4512603401d4061084018403a80011405000c0001005041118400000c3c012a0020b4800b0700c4e0380821001c92051289014009085100603910071881080180700f21401e94401061081d000500c40495001c44c100000c0040c1c000d0285400c10009003811521003249a60000300441c180e8003d03401311106000044001c3d684021680030b41800010a003010400f0724200c081000700c10900202580038240305980c80d00f0445a010710f8100d40d02400c2c400b4001d9a40c40c5214213044650000064a0601010a01210912204005000d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 582848812 1250 582847562 582847571
    0x70905090c100c24060906080111030705190c020a140109140a09050c0c0f0303070324060c05010f0510050a080106030201172805040209061206070c060f0f021b010b0a09 74
    0x12500c40016200c0c1482139080b8040000b19100c0c04001c004000034040e00c1d104e90b20300322010240700c2e07080b0290381c070400c112350f6400d180000c013a504011980040300d000f028445d02c0304201d40180da888891034003904560150303020300d03034040c0001859400d160f88007100400c3c440e8030408581c0c840003401d400351602c01e8804070b180e4403100c1b90350340c0381c1c0b0801411070310700c0c020080fa590601401100960180345039540038003000c0703128140001084203040b80c1c070304011070707110003000f4040c02000003130346880c00f0b20000119800306146002c01e0f1102116096401c9456103c18000d41c60958030f408050146203008004090446d400030703100325054002c108030384145600259515001c2c501140700c200121136441080780300c0d80300010240c40d0a980c00c91140c03242c0320004d6494180301e07180c81c107140d15560040201b616400d400b03450308207248201341c607000d07142d91010b814100340e8003418501f000820310040c1e641c06841d0310040c1c2c0b596511f01070240340e41455804102c40c0d54652880041e0340000c6400a03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 582850062 1250 582848812 582848843
    0x40504020a03050f150a0b0f16030c0327150509030a1b06113406050904050a0c12020309100608060702060108120a0e01050c0d03051008120723070905090c100c 70
    0xc081c06210400c02780f0460844005081641c03100004007514070031785406030700e4101001c2d05d8403540085000c502207c1034000d0108502880800100b1030480c085c2021072518800c00082414070341c6805040d0b441603c0d400c0e0010680030485070a4004081d80d01c0c001541e4030409141503200e04421000000200c20580c480d40b031208184511400c2342d164100d240200c0703907034207005091030304000d880503c00c600c0c0c440040d4500c10b040c052054180c410f07035110803c0c03801c40515000203400141410000d40700e010105c001691b43d03807044101810a0b40002c280604e0440e000031303c0c010303058002820503044561400e011000700002c1d26140181b600704007000c0e2034950f004840fa8050300180007228441d00751078800b45901175021701c0c083d401100c6400310b000d0712036511541d20281c0e00307482c02c084001000040e020589611003400505004030880300035084416109280c65610b40207070030003a590310203000f2505000c014803c0c07a003c06840c2000c00c807a5142d40170340803000703000d070242c10202e110f036684 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 582851312 1250 582850062 582850087
    0x6091306182c030f030702250509041205160605180106050315131205090307090e0a03050d02040b07050d23030406090510020a0f02011109150a05040504020a03050f150a0b 75
    0x680d507504c49008900d03124a0010b07002540c0c1d6051005030400c000040301d81143d502150700d4160113589000d0020486500c480e510351003100720359109a001c11a040c0140208500c1071640c0003c110700407600031502d818503502040700e405100c3c0070001d0b9603241600c2006943c501242c0d6005d5041003e41419460f541c85112032014042204010f0207202d008034040306140c1c020340a4181010149c2c00c07229081d45444c9160200c8401078000522548403114a80009102d0001403050848950003d410150741e840c400c901a04000c008441c141c010301242140076921540002c0c1ca4100401040303100b5162500b107411500c00a80060b1a013a11100c4101c1400410821180300c0d0300c01c4001199140380d4141c00801c19070b5109022801075083c111000a020026402d5170340f02c81300285080102100d4200c000c0307507617000d40e8648090001c00d1000184698451029140781125a2400314503840c200040a45031030005028051581c00903115642c65100ca4005c2001c1d510301802c015590140720518 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 582852562 1250 582851312 582851317
    0xc011b1101121113031a040809120c0901080d080a05011203080603010b0a0b0c1e030313030c080a0c230c0909010603080c0a1b12060b06091306182c03 66
    0x100c3d048000009000010b440e4004415080f83d002c0e25600301070307502062011079490810b43c1d0261840d90103028646070307860000500c51a003103400084840011049c0c0c085074000609920182161300300100001440750051000740d400407614804022a605000c00f985558080c40c03005030400c034080d070010700031f91004d41c00700320f900c400100000138150740c0f940b542c000359000300007070030180c0136a0020f441207031030007215110b0040e011005142190b50752817801070b2104075040b0075010401500c400d4008a001c0c9001800c501300141d0342e50f0809121810700c000002c2d50340b41c000702101d05122201010f42000706460001344021140000182c5490710b280b07002d080c0c6030300054121400001d0b40f00c00d0140006407846024441d07031822050303520212602d10141054030a4445800804880701c0000d03241e607002047d000001030049040c49401030100d014440014030140205607208414040301165226614040d00a0401440070682a410101c11403605942c0b11100e0030781c60140100030b900910a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 582853812 1250 582852562 582852581
    0xa1e0c110f03030304050d020d0e03070e041a010b04091803050d050603010609020409090501051609091e0908070b0a05070e0603060a0e04051b060403030c0308180f0c011b110112 78
    0x112501c1e070405e41401900e0328000018000540300e10444000d000f030003a0000b0a0300b48000f809403004a02d04610000b01180060044812526196030341141b0721308441c282d1701030205004666162401d104002d001c46405c00038003290307503540d29142070009a124044481c41d280e001d0740030426403a501c2c0801c3c0500389582003550460b0002c0390200b8008000d44c44000301a00920083c0107948030300b14035010020f1b100ba01c40000070450f080611015620380c0001041c848590f03102d410f0522100050802c59885000844410f100080d0315820301c021908101c5c1c000005c1501007050307052011000d4008060070302c030b140c000c41000c0001111982c4428004000b810742005501d482c1c6000e00e0310705c1d124480c072140910000c000a107105014100b001c1510141c991607210005100115142900d0722480240b26052a42062101300085074090001412400c0c038640108201c040c0d00c0009440c51a880911141135810003080342e0108000785c40800c1c400c5801e08041182c04070070003004020b040e400e04c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 582855062 1250 582853812 582853819
    0x103090c1202040b1002030f0a0903050607050c1e280f0b10080c0d08030a09020a060906030c050c0721082b050f010e070e03070b0a1e0c110f 62
    0x40300003400000e05201481c0c03148210360422031042e08000304a40e80c990701403100c0040e44244090b6040425007c01080c5551160a0008001d80e4a6a6851900c1e208448041c0000c90100382110b2401d400c000c4e42c2d0b8144045202c14003110480c000c965070b2407503004a410181c520402c60101c1c884000400c44900f6500301105c0401414903061102110b40140c4000070266628035000a1946001c1504045804020010100d2503016110349002d40c2000c0c0c00300d1061545e40c042040180c1e101c0d642c40004012503110320f4184c5241c600b020f0102c03050340003114140300081001841d1020042200016620f0180c41100e01c000b41406400d0381007980d140080c601d00001402c1c4940305800c0e8156003441c40319014030102803a883c00c00c41c0545401f55002030610138a1001441502c0d407040c7d0b500d62000d00d078a08000c41c0344549002a1400d20180d0210701110000039a0b91442580403001101c00220103801d101c40c010090380082059414a02c0a8900954000a4462540c4120440c0c00c01d04004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 582856312 1250 582855062 582855083
    0x182d0b010e0129030402060d06170c0f040e032d030a0b03072c04020102101404060b01020304030c1a04092a0914040e0307020406030b0417032202010309 67
    0x11030010310020002c3c041d00f22501e41040842e40b100304800c080ca0398544100c850a4190346465081c884d0340e1b00311000d441140e40d11740e08041a5071011102054045008800815001080d80e00780050070029101140c0036030700b0f21028a07450710002046484200d10704c10031841103800480785450f270110041b050000000000180704095803280c012a4465800310140c0d2456075441070908540c40354241e403140c80c00c0c10604000b400250400090743d0290040c0151040c0b103039415030100484203030710141509032040400340b20070300c080e9218400c00c1c0034081c0021803406007161260081d407407461045480b440c501c03000503400c030b0343c0010648000301040039050142d03041d03103a1007524446044500c80000140364443c01c41e042e00c60000e034000c41c3c1044c90b241c031030402c0700007c0c0f20103070800d8040517041e0310003006a400142c0762441440011405403400c081c80e401d00745000380d1411103d030030054801e034042c000d0000107540454445811241400c6035044040207100590242c200c00001070710200d0344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 582857562 1250 582856312 582856319
    0x9070b04090938090d050715020409051608071b03112811060a081303030902090c071104091203020d0b120a0203190503180d0c032a030519081e0a03182d0b01 69
    0x54118137101a1268440760b040780d4404000311206444c4c0c00c8085030329060728171640003085c0190140281c4050b55802d803075007901c0c484407003c01050000d1800e1400ca2110181e0b4080c02a074540402040c441220f209282401903000100380d5413004c1c1605980c18909106007082601950200c0f0807503601400c130021500d0006041d4031150000320050301e0510310034400c0341542c07400b88034007003803594482290381041c189664101c00a4200c0c0e540b40a03000ea4400071200c0319035640c41082108800000104045156031050608207000c0103141454401046003401c0001c3c0c0c080240c56007c040d403102d01c0c00805110000800c42120303243e018121500c2c040010061001103200b041d80d0030440c802141e20a20341c900015200011484090b100350003c5d45801001814520305500090040714800d041102c418083c074240450f1000c00c502510740001c1c420542601401400004031088603c03c400840e5511001d000c0746013000c0044901d140c0001c1091480440b803807591140380c004220880c55a103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 582858812 1250 582857562 582857581
    0x6011508090a120c12080613020a020114010b090a120c031205041d0106031b020618010209100918020705030d090203100c09080609070b04090938090d05071502040905 73
    0x841104c00e941c1d00800c14040745010b401909450b015520140c01891800700c100100c0f0000d4201600c19400c65482e011842120301c0c0b20340c1c0c5517010385001364030541d03213050400401c02d96002c650301c00c11100d40140b22103000304061201b410300712a0031801c1000805502c5208403202e129680080c0c040000b40036000c014100d10b1182c00c0d06a41098604003e03a8504cd424140500c0311590000e00581c0410700140c000c40800ba000311014083c8400941081c0110300081d590a00104c90400012800c0c6c42c1044803d8084450120b01044c1d00e0b41140b0b0301005840d80c0740c4a10400c1000244035449a03000411910100554000442c549208121300c0324900002410381c10f442c41101018440c0002044031040e0120712602103c00f07074040140f40074a00075900740030b011090b00c20340303041049007a4140540e0741d28601d40841d203d5030091921644c400700000701703020400303424884103038094007241c00c0766070300201182c1810b42c0015240c4c0b00210074107200e20191140d03401c1150005c0c105001d000c0300f41c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 582860062 1250 582858812 582858827
    0x206030a05101a0a030b03120a021c1d010509030a0204021b100203060d0b13060204060801150908060c0d0b040914120c191a09060105100206011508090a12 68
    0x102c0310b0751150641c2e0790f5052008040c540c0e43c9202c0d14a01000c100380b0400f58000c1d80701a15002001d010360703d0a002e10440c94400343c02a10000000d43c00039195613502c01d40504001840036081e080208400c002802e185440c900884042414000009100015964100300d1011800c0d4010401d640d82d02c1901714224080741e2035007220f1124418260a00170884107070003524402c01c0e014003100c9965a4030380380c3c01301d42c64018058810398101c0905000115900e03000510150440f61503400041d490010365500400d51904880d0401890070414401ca03071000c00d403039400c0103100c112540c40341c011080a20003001540902680131b490714164100b0001100801c5a0780d4091605503240040c16102044680c4224a102c6035244c20005500c001159000140701490740919490b9141241c0400c2651640100391913110140e40104010401480c01c1180e0086520042c40604580e51604102061443e58028002d080c8808040041c100300401c000c290a01038100041c2c1c910f801504802908c2c80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 582861312 1250 582860062 582860071
    0x60f020604170922110f0f03070504240e010e0d12090b07060605010810030f020d0f082b1e0528020706050606070503030a1a0a0314010c030b0306070507050a0206030a05 74
    0x2d90418101c0038120303c0032000d440300c0c80311b01003499190606040d420b80c144c2c0e10041c001003d0100034400402d9512a040e8134000b040c1d00d0025682c2c84016103000603012100c640c07a541d041069402405006032544428140d2140d8854409a010300320290250780501303c0780c10240c0c1c401e60110b0624140320706600008200c89080c4c0b500c4c02140c40341110401c103501ca50001500c2c0340c0e5281d541200509050001c425094000c0b000d0302d03042409a039507103800340e21041001d490030b0440078903a01c070104540c038080e0300f03a80e404004110b80d000e007408101d40c2200c0d0003880980c0341e651300002020a4500d07858100c0f80d001c0c0000141142c070401e00f04c0802504011000d5840f135180000081580c1000012155a5a0024000c50960340d844040700e015110b505861041c8200e0603080b03050036140c11044a0155108410305800c0e440410301070341c00c6a00c80c4901e002003508116107230189440c0455525081030b42d500c0c4c042e0707032400c80703080061400015100c0250031090001c2006817030b082c00e60026018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 582862562 1250 582861312 582861379
    0x4060b0a0c140303040812090138010201020a0215100905010b03010e060607151509020c0724081303031e050a0b010c05030f091302160c060f0206041709 67
    0x4842510161543ea4041124003e140d2801048148007204ca040c0c4081d038030141031000498010002e030f06541c1030318a0040d2281543c040c02d1209851685071080c49080300d4401e10003181000c00580c0000c0d40c40b2103031000003501d840b82002080070610280c1040002c0e0040080901103540d4507041d44200e41d00c01d1007081e01803101400410301629000044508180d0003003080c0300084151621400148001000340458007000d88002075000e00c50f0000c5c01c00d061054014014680c81c1280440380d8030071084000d070350703600204100804160002120381d0807000c000d1205010f901149010b40c001c042c1500071414200207080112034003403d0b60040b500c19280858184541d8102d4001901d200342d214000030400e400a1140780c5407104903a001d0300340c110000b4004107100c2012401881245e03ca040008440069000640140081070f20104020551450301c000f40d05022a0001c1d00e0303100140009100c240c0d400350140e01c0c5074440007524042800101307542e174401c0d4844c204402e0100c0182c501c0d80c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 582863812 1250 582862562 582862583
    0x21203190801150e040209040e0102030105100c02030a1e0602030103050106031a15010e010302090901030602040f0f0b040b090609031c0224130507030b0a0b090a0506010c020d0204060b0a0c 83
    0x3005032090402034122800000c0f0030040d807100c07450503250b5241511004e44c0065080c41841f000750b0b5140140e000e011513540005a0300d50601c0140150b0115484601007440030203d15800103880010b101010241c21843d100c21a203030164010166901c10391020308198000700011040c04019440f11007200e110303c814961903012503808441d004401c0b075505542619a0031821055406144440708803c014900140360401c03175070010703808080a0304103461141e40403609007d2601110030080181c403c214117111703800d1506003009003c2c41680640c9078254004503120b8099102c490079500f0300d10f0700030146d03141101d000392601c401450310503003000188105c0c116001c89031645d030351842000d8840421020543d48007505d020741d0100e03141c82207480e44284d007800808601140c1585008507100c02c808200d5003441001c2044085001d0b040e0142240b070704060114981e00155415107803581076800148254031400014010120360b400819010784c009a10041c9c00e0380f004584815600c5a2002c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 582865062 1250 582863812 582863857
    0x30901090e0f16050f040f14060726040909060903120b1c02060c030a0c0314090109060309140706030209011101060b0f031005031b10020604080d021303021203 70
    0x2580000706a40d0507840030708060116910b14016180e031a104002420901d00e82410180b86042d13503401a07115840c00c500c000800e1211b45a5903ca13004031703410445d0982d041000981b00e240301c0b043c8103001000c0b0700204a81e880c41d80f60710042510000e052100040181da0700754245030f80504100d4004070002001c00c070001081d034400b03105810b1412070146c240280ca5014006e085110105107034143d07403100c014800203958030700401c0102601441582c0b42e4451000c145009030041255200b501807514080c0505003070341c1da2101071102119800d19001c99264141d06014404681b42d540c801c00ca40074041001c940b180d0143c0041c01c0b00003007aa9007811407018060503030308a43e0075008103548070034100b1440f0500030342c52000e140c1244004143c031460b1359403400080d1402846c0350707081295445071041518985090180c548090707415001420b0a80f6255641d0001031050001411001ea80881c80c078541002e0320980102441d8080c10b0103691502e170100c140d659801000074840840b2030ba05018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 582866312 1250 582865062 582865079
    0x12a02010513050709020f07060207030306060f050a020303070c1a0c04230306040f0218010f03020112020c07060315030512071b06120b0d0b0f01080d030911060313021203090109 78
    0x4048035a0490f0103041c1203400d10200394043c0d4010721010350000307000d01c844404604580b00503d000b91003a01e002a000e071400b00041d19a441ca519440c5c01d200303003400a11107407a00842283e501131402c3c641000d104140345400300400b01495002041c00802000704640c01c0501402131041d201441103010100c005c3d600d202c4400d420006c1030399019049800420f00146641461442962004140ba49d202d88000c840000081c0241d00034801c4401600c002c00640d40c1101014071a80072900055251000309511295140d41e188038107401c056480103106000d901d1080c4103030146a102e82075415040d00d0080400942d04640d0301900d03440f6100c1d0140c030035034540c81411005c41d450b9454800002d0740b41c4891000500c038030b18410b50003a40b081010300c00541400401403140b40b01c085941c0d40d550400c1111841c149540d100742e002d0602d000640000b1551040400100072030417911240d40b80e4450500040e0340000c880f0094120001c442000a0350300c022018140300780082eaa801c584903581c01c800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 582867562 1250 582866312 582866341
    0x4031b120801240527030a1208060108040321061502030301090b010918050603120c010c020f07080705040905010e0307030518040507090e06030a05031809010b040f0b0c012a020105 79
    0x44030b000c6642000100740c001002c01700841e90f0f00c0901d41c005003002260020a0800c66481d9007190000342021442000ca5009011590811000e2a14004515284d9030160000c00c04100f2003c11402d03ca401e4075003545950007a401800421440c1d00c981ca40940c00039650350000e0244c40307807060511803a010f96500c10803202c803c5400300604070610700c41130960000200000742c40035405010b8038410411072650100140b1181d6402c40c000a215902220b0003070414451001414440d00542e00400002c0c000241c0f200940b00102c0c3c0c006550031061070b003d401040740c01e5001030903000c04075544080c10f8011002e04181c0508010b25145a40c0c130b001044100c03201160224081038036030800b808001d0607280e5603584040040c007100c1317010266441e518078642010344103144d00003505011400500f001f1f0704260040400320503a40c107150400c5c0455110b140a4001e1a414041c040b5801200a1007500106400c03103032021441a4211460070310703885282d450004030055070801c1c1c00701d804555007d02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 582868812 1250 582867562 582867629
    0x150108030309070b1e131d01050a170307020a06080103020117100b0726090f0405011202010522092306030c04020a030915020a020f030f0304031b120801 67
    0x24103c681c3c209201302007a40c0266000d44400c241303840c40c04464160140003482420440c880b0f10481910303054012820139440040c0c1100c408002e001000180c840302a00010703a40344030564100040d02c0000c0d5403031805001070203503000c46843e0380000d0b4260040d039518143da0003030b41e80070020003224030110075100c070035600d005410740603ca080090410b0203004d040d50611a04040c41c22500d00c90800000d8440454086004400024a01d4451800c1c0280c1c1040203c2600d040c0704561403c6510302d11200c904c60045e052000c005085080000742002c007410061180e5541c1c5442515580d1900c010601a944014808401c3e1018081d140d0701c810214440da40080c02440b02c4403460003408061f4020f60702001c2819260800000060070400840c1048891504016118407680742e00a14008286144081075001002840203c0f144002141e03441501410645003840042300c50b840101c03907140001e08040d00c007440da8840705178080c0b05503040312400c0d000030000b8000e4400d060440069041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 582870062 1250 582868812 582868831
    0x105090a0c0b0a0915020f010f0c02030301050d02060415050304060b09060603130303020c030414030607050a0c0f0201090e09010b01030b030d0f0e0a091803180f0918080a021501080303 81
    0x542000440303002c1d401001d0344282840c0061146595110442c0900134006003c0056040900104000c3e5024860031168070341110061084810700b0101039103912060044034003840c00070001c2c0c1d082d5241c90044800520800d00109440005214000d005410a41e4125040703414800e01e00150b180c141803040c005c0303d0007814545917444203002c0c108030080c402012070505801b48050307080d030807042c0080d00040105400908500d011502014105400100303540c00b03220040c80580d061541c0416171502813580440c20150401072070006844440141d4070490b0481003082c10002e1148040d0010610704600707880900520042c0310070991201104011200043c3e44040d0500c00f00f031068074003442c10b10002e0601e040107502ca8541d0000d44071204982c0040d840090b0944c010540d0141080380181021a064000c1c142000c0c6280b020b03543d60f00c54036a04a0312006020484100101040c44a56006140e10f60702d142c15500a5207542071101500480940240002030110000c8201c038420b2a921 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 582871312 1250 582870062 582870083
    0xf0903040b18042703020609030406090302010c0312090f050d0201050106080a021e12010e150d02060a18030c140111151312020c041d0c01210504080c0105090a 70
    0x98200d4440c22440c041003c2d4825200e541101c0e0710824844225855130100007401c99890703241c100a490075030050416400c907403040000b00032080d440b12051069070783c2481c0c120720b0141c0ca4201141c0c1c04010301c003003243c0c107850110030710300700500035241a01061088090301c50b80d0500760003d9003210000d214030408144c1c403000141d807462460303000b040c01e04e40c0c0d83c01c0202c0310343c084000c1001030340200e408007054502c194018401036040004880d44a0851907995841620b204c0c08190702880e04400203019220215001c01e04a00444c1c220314000d0340b951541c2000d60f82c3c0d013452144e00e5200c2c499503070070a00c08410440c1c41e5104501d0b240401840b08010706666001c0901c0e01d0700c401c0c0c002e00c80e8400c103618490100004440c05442e10400c0c41940c001c101000e415000c020454041a07a02c414046203120300410407500421100d0342c0b41003d0a20300308818184944a0100401c0103002c9070350341c504010001004142401f0742001e00b421002001a95600b40419544400809014000f01c481 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 582872562 1250 582871312 582871327
    0x623090604020c010212180f1020070c0e010602010b1c08041e05010818340303080109050a0509150601140c0a2a05060903030912060f0903040b 63
    0x254089800c204050001803a144481e1102404ca0b004001d007241c580c5490020321500000c032101c105000500c140140c24903c80382d034031a503682d08942503040c642d01c0d02c2d003070302c2c0303007616885000f00303503107000480e02e107540c811182ca0191210b442c14000c1a0301100b1840020402d20710520031044000400f5203044131520300b149442080b5403100d6000c4691650070440803034480803000d21001d0402088403103101d020300b00340c0050501c8400401c070840a624142180e80320f1036000603000130407900d03948490910500c0c18802c0c40c803038a8640441c41040c1070020f0000c01c159105500904032035454600f000280c8078218035000383c400c2661007004503071044003000b148070118080703980c000c001410010702d10300c0084880421500003004280c1d194001c42456400d100610305444102d1b40c0010745000f4855020704c3c080703481c155601070a405800045030642980d1010400c52b9554031008100410f4036018461301e41d9620400c89403900109036490101e410503100000b580c0030350710f0307030780d00e450030540d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 582873812 1250 582872562 582872569
    0xf290c0d03020903011b180b030c070f0c15170f0903071b030c0902030a0c0e03030301061b1a07020d02070308090108070e0406081e060615070212030408010903030623 73
    0x480300c00d00e0b034155661030046050341c50780c2510340c106d03003401d80750103610303451100b0b104050440c243c2c0310381c500040410800010b807416038120382c60240c0c03000c4044209412030510f0300726180e80da0419000aa01c0880d0270341016009807880b0f0118211819882090b82c03030b0b00c2c2e072060101054802c0400c642c401c1c0b02c9100000d481c0410003451010035480050309950300c0c1c0b00d9414003006640005c804580c0001401303c5210f5901a064040005042c0071108014200101e80d0702e00c01481081c0c00c00440000fa0f5600b0300c07540c0200b4500940185440040c44e4110700110301c0200300351410310140c419483e441c070480740003003448412a030b00000300c103050094403401925102d02c010590b0081050444411a443c1e41d10f1251201800f8070800805810100b0307800c100170941c1d5070014141603409442088000e660740ca01c071000e4010b44e0070300d00fa21003035a40f0102d0750140c0c024000380a00d000c08103000c10b60040543c0709010381406030303406203c91030356042d000c480c22034500d5480c908042075000205a605 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 582875062 1250 582873812 582873817
    0x6020307140d020a1d0a0302132301090b0909030703030b06040801230c042105011b0810091e0c12150302090a0e06010603050601090f290c0d0302 64
    0x403401c100001c51184110312940d94012084045460340c08160903c1c2154032400c01c41080c004d500458103101c1c010000108030342d209110003032080d0190101c6201c0300150707070012218401030b088282d980d466407482d4200728040034081ca007000351800784681802c3c86c01ca101d49000b024480c000d18640300180d10704601410210759050b0b080001080001000882441281020300c0d8180050000b086201c9854444204c00390211108480510041c0300074566541403031103092180386400c500912514005014000c541da034402c002d003070650118240341c0c1111324a44102c0c44c00321031161264441b24560111507600110b0040e500b8040c030348020000c00d070344c8a0060304503103041c14101040601086400c2e80c69841120b100c14104110800441c140110182d40000b00c0310001c1c4203150306d000308079503150014850041015114000b00b81507901030111400030309100041d01892030388840c245c152046910030030314685120b1817480c030803400e5a00c091b43d44122120014001d0140c10301c4040b006034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 582876312 1250 582875062 582875071
    0x206030a020c0a0c0909060c08100e15090f01030b060108220510050901060e09121204030309050613050f010902150a2618030415050d1b1d0f0a03060203 67
    0x40c4504802100415014070030b020042c0b481000102e0a50b03d1031030140c044d230b0208140001444030b01c0c170600c810481c0c103c5209041c4d0346441c80d104141c0d48c601c400c0ac0302000385a44110b4008195100703018040617144c01003410703207004407801e14203505d41c507004503000c04e4101c80d80d441c006101c10380e044030102e00300d00030032800d40034600310b900850f2600c9140c01210400d40300d90020341e64480c410445000c4020b0210713480701028014100e94504085640c1c03e502c00c41a2080c0d119503194002410580030350700518840345c105007155003034500358030581040b0001020a441c01c1c440e0028004014805002e80fa80440c0c3c0504112400b00707000c00c0700740041c3c1000c410b58040c0701d041e0080d442d011140140354a0800c800f01c8250a207410101c0108807910002c03d82070300b650f0000c000c03d0143c0060b0030151904e8038440c1c0392a95540400c200341500421408c29000351102507a244036101640c0206100d040151044545104003c05410414560703154541e003034128450311010400328000e07a0195600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 582877562 1250 582876312 582876337
    0x10503010e1911031f0305030703081009020403050303104a0a05060f010c030806060304020402040302060c0c12010905061308090d05070f0f0e18010b0301060e0402040506010207030206030a02 84
    0x3001c842c0070590036902000340c441d101074404410000d08541503800c0d10103121001c5820501241151a01a01c9115407500a41800020b401203048181c817082e05400910740c1d0842191180d4984c54100c0d1a0f40c8181d0703213034481c194154800304270950f40704200c0312800903403c00c501503007155840c04480b0100d281d00c2c1c1c0c141c600c1246030341102e03081c454000303e200700500d4400203a5840c107442005202451004407904005080c680800002c0c0c11030070f810b8104104807134058882c1e44510000c0c1c06442a9080290001d10114203900c0342c030b6001035960681c49048680940c2100c05082150032942c103490040c0c01d50b40001d0110f001c44181c000c403031080500a2110344d2404801a02040b00034122140840780395203c00343c204a00d45d210035081003c0e105120701070240c14500744204010005c00751200300145101a40e0100d203110950002c1030110018000b0300140d035880710302001d42d890803541039024509100c0050345039031001c2811000c0e01e50040c11a4195158030008000940018048502c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 582878812 1250 582877562 582877591
    0x306060c0f1e051005160c030c02030a1410110a0509040207060b041d0d0c030905120f120423030a0f290703150e0109020c03041205150114010503010e 66
    0x51501c0b400c190210018020030044c861803601450002c11580d00501000394041140e14034034206a20030744501c0c407950145030007245418180000303801e00b000444001c1840740e5600c0b483d035a0100100c4d0740414a401c030901080381403000003400b2500c2c0b090703070203000c006401004210f03014903041c1e01410880b4081c52000a07100c2c5640d01043c00c58031800c0c02118005002c20460402c030b03608106003080e680d100c1c07400551500b00c6a0300600301101c140a1680710ba03a440041c1300724560f0801c94078400a00c001c04a6400d0480410700b900d10790703c90f00030b8000c2c04540002c00d001ea075081085550700c03d000a002031645260030f03150b07048881c2e0800012900341d08514a2025240c2203540000143c005058111001d030420040103011140700c2e440802d504802030f0000c000c51032184050710304482d01004050f944d0884240d081c0d007144103640250142c8610b07268141c0078424009801d50000154000d00d524030b03602c0d64003800c00006001c5280b40018820401401001c0c000040c1c83d030403a10b501d1394100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 582880062 1250 582878812 582878843
    0x503030c0a0e0a090b100309050307030c0609060510080c061206010e030f06310c03110a0806010311030f06090316111309060507051c0b120a03030504060c0306060c0f 73
    0x2090f1200540c051990281c4403c04c1402c140340c0f843c0362840c1c84c1042c2c10100a40852030303540035202e0040b510040c05101034000c201046c419960406d100e074070b074850010030941ca0410440c40d1060754034029070540c0d00c900c08000348a420301c2401c80391680c0380c81030104a41c0d40c44c2c03001110000314205020b0b0b010b000d0020103540d1004204800d0340a0034001c01980016290211806081108951000540d007510140b040105546640f02001d898124112016840419001c82c0038080349603c0101035201c0c06000005201c01c440420341c0f002812826101d4000b10740742e41c0c698800046c0c07802d15950b00304024000b070808111040c10107041c440d5884544c0e000c00c0c1800903003001c210080c3c207800d032078981220008020319032182e030b544550107041940c20003100c01100b24403403100445014151380d0b1840054a0f640e1950051b00f007100c0c3c45000c48081c00e907907160040140c0000e1350112002c40c00c18151020300d41c041d01800080e65450b42d00e40748102016125405030311382150069403c1e4010360083c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 582881312 1250 582880062 582880069
    0x1712040302090c1210330c03050c0703050c090f010f06050904060e070305250c030503060a21050d020c0607022707020d09090203042307050913020102010b0d0503030c0a0e 75
    0x2d1068410441c44504107141c82002c00c140120380b00d64076001c60380320300d4404040440d00c46ca100c090445103041064010a0302d401d981380d109510341254148140b00f00081004000646030030700f650141d07000d0b0000c2d224258034980c4002d0a002e031608140071014148070302071166000d89101d075402040810030a03a28890f920100b071040c0e41200010340c55404001e04400646044030307400b50003500100103603c0307100d4001c15002c9100401400c01c48008041020399807164220030150404040000e8803400c0195803000804d1100c004852314040d0192000e0540e002241d2011b00310000b600883c0350414031390070881c0b1000120094012071402c4810481448102c1c500075106060540050441a074004009090343d246580485001e1b07004104000000302c44900e013a500d208070507451160284007448030303800e003495508055002060142040114a90018203001c641d00070b070002c10550000006000d00e4808110001d0140c0d030080000c104200c2c580d40003804602c185140c400328480303015000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 582882562 1250 582881312 582881347
    0x8040608011e0602030d020c0f0d03020306091003020904081b010915061e060c050a06020f12161e020f0601030c141e0108040804051201061712040302090c 68
    0x110000503403480060204404100c103107200100102c641d00305080c03500300000d649100e8204441311903600440d00080a11080144421101c5440113803544441c11030340c0200250008c488843c4541040c40c0829480c65500601400380c0e0b4000d4201c05599840e0384900780305500c80c0c50b1449082c0541080301d00095805e00c141e000042c414511401c1400c044c515220564060350030001f00e40840e000c03940100082c00303107024122485c500b40100145281e06080b400c0c01c1100e40b003c1d00e80d80c000038003d100c2c5811100100100a07a07403184c3c10103a1254a20500c2d000030088081c4040b035003000c401c02d8902d05a40c1d41002c0f2003139620403256240c54010010741130150a070300c100d50164881c07005008200700800003003034007401660710312031081801ca030050740391103200107507814082d400001c13409000ba5501201c010b0700e809490b0342c8400c5044a0014001c1000d48907000c490003c001000c1d03501303200854030048010344036010030f0405041d42c0030030a0076140078102603043e4408201400004013007039034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 582883812 1250 582882562 582882569
    0xc220504050d02010b10020a02100201020c1006091d46050f0c010206131e080a0e03030906070602090d050f070f0e01060f030209030717010c0e0409020f10020a0804 72
    0x30b441401c8000c84040d0070750b48000180c17441401038140348070740301d50300203001c8000c25011101000a4400002c4c1680284659106000726001d03040c2840e40c4901d594106404481503c80104a0b0080c84c1e025a6403c0802d13480c034076020740004075802038041d8070700d100c00c076214014010400322501d1141c012050a91018032030480700c42c801000020710006000c8413041006005c05400c1040c03074400003d4407000001d000061116a2401a100784000700c4000410355001c407414a4681102d800c02c8116600506000300008000703e14582450401000384e68071660090f10b02420408180c1d14580607410540000703422803000510500411b500b048035009003107030131020b440c166040410480c0e0801494002c20002102c180040026640c44140c003000d40c4000d1a0051701c1e4a01e01d4002810000a50300c40c1d2607082401200c1081c5c00011740c040c500800032601c408025900160900055420b0044081e500c14520642c0500c64100304540015020551041d00c10100c01a40c030200c0310b0300540c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 582885062 1250 582883812 582883823
    0x8181306140109090603080405060a020316030503040b07030e0318030a0b100e0c03010605090f01030905060405030409060608040c050d05120c0c0a051806040c050f04181d0c220504 79
    0x64500e411560420f0411018001c0002c041c00301900f5900c80302101d00c1079108080c0503003030009000c00098401d009481c0454003052001e502c40220703003030051454009135429180c8070301e850085400d1901910901c90128500380180d403c0001103040c2100310f50301600d1042c2c2601400300aa03000400003407295100d00e0480011210445c105040540400c40013444410880350401c0148000d58011040c2c640c95401114228810a07030ba600490240c00317070722401091403050034103000030010048090411b0300c500240403c141590b0702400c681001040d2005004120380d04401c0c070103401c00710744050300703580036104946515016050007502984000001c8059400000e20a120303450720301000e00051030101c07115158100a2140c09540070809415a8419580c1e04820290280100d040d1003030400ca180b2495100c0380d5a4a0017030501c1601c00542c40e440f0f103800c460148003440032800020700034106006003800300c0c1200a200000c8112040c80c07481c0c02c0030304680c0f24a01d46500036248a6072044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 582886312 1250 582885062 582885089
    0x32c03040807090c020d050a020a1e05060403031a0d0f0605150a0305010e06150f120c0d080408060105090c07060c030609020a050712080115030902133608181306 71
    0x13250001d041010450340302d030401004000240840e54001141054190403841c10380c105220107002225808220070010407901581c001c00c024950154090b4a402410807a0020403003400320800c20708244d100c1d401031180780a00d401c503020a000e588000c3e8010b900100722080c460300304001580e01314151380106c40344d81d12680f0b038545001d01400119001644030203a4144200d0070350008541100c22408240a86440d000915552408101da92080b103c0604509800260703400d217001729610034043d03180948680000095181007912480d0300c1092002011400e00410b40e41d1800500050031004080644411003c19504030704e00c010404000c0307549075a0346d03070000c03403501a08103030480070644244182c21004020b401c20600b00201c0005451038006003100301840000c110130a1140304548041c98669030603140030060340e0b5403400c8419014140f0f84005800203100c0f0240c20361100a282d0714091081d01c6250141318030a21441100612802041d615032190b141200c5403540542a110502c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 582887562 1250 582886312 582886331
    0x270519080708010605012a0605010f030b0609070c0f4b0302121608030a150b09010c1103151519080a1b0918020907032c0304080709 58
    0x700311080050102900a004280c07a22001900740300d841c2040c2022481002290410342d0300941c9040003081c1d000c002040156181c00d1017206400d10780c04100c403410314210114040d4503140409520816880c0d80b030a404900703aa072603070240030341c80c0c008441554252200310804401203129a003070804016458201c40200c481050a10b000f0400350f00c0c1d40742100305d140d00840e501081040ca0b441260021135510b4035a12008540c3c803410031000740c07240c2004014000708071040c0d00858298049000d00c2c509031900c84101540611501541901042e81842b00f000002c0782122074030094100103081d07a6424050f94500000f8000c01c588405090b0180700040b506841c00e211401f080c45a4459002c408a0601c190b0a6071401201e00c060171507803003030306031040b000200b030b01020241101354800d0000003505600f001903084006030407840741e03110000103511184a4400c0c0368000c860355652400c0b0500c41c0c41c00d2998058500c41c041104d000810000c502c882042010400030403401c200003800000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 582888812 1250 582887562 582887579
    0x1308070b071110020703022b060e060601022419050f04120f12050a0b030a0b090111031501210606090509090109050303070518090c07061407270519 65
    0x40142e9800e1240000e9039441d600154006030320015a070303043c0c664400320340d0214620311100115860000155100300d80d0344081003096013003042014040421941c460f10b4030001680c440c12160f58102807000c500b42074910066810718140e40103044031103541d54140304045900e06440d8125030009100303000c801400100701801c41d204100e03000c40d00c0d18442050a4680091256041882c3c6035070b4242c544020078408038a540c40301240c108000d040380c01d030140b81c0c501b0070a1001c00315a00042c0f5480c101d216610700d00140103c80c03181c0000e000c521203070480c10006444800b04840d0701c0030044000001803030207000a20660015001136154260528a044204800c00718001e00b01000b0344d0401a00c1c000117100007055980008031414416164008086468500c1e005040016440740700e803002c3c400d440808000030010303140149020b03c4080f50400842402c4001500c50100042c0d9501c0b407924400007041c50300d4082808410131011a0380c0d190000b400300443d03001c03040c06020700448200001301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 582890062 1250 582888812 582888833
    0x7050c09090d050c0c181503030910050c071a1308030c0a030f050c070b0910022b03020c030d270b150103020715020d060602061003081308070b07 64
    0x45044500511500d800741c000c03522041c100c9614418450f001c00c1d007202c0c010040c00848207041c40034100030b51030581e90009004501d010703103240744800d40d06a25442d043c01c0c04011500c088070044c1c695030034038903d5407044481d540400000c00f80c0340101c1901180b2401913850413060940b441000f651100d0010200402c40745c165030050b69079a1007002903d5498070b0220f44120016010309140d800c080000409503520321034048060043c0c080c040d03021401c041448042c00941d0000d07203160483c90807640b07042ea6600706c00010141d43d00349481c0c402e03040c418203445400c05080245005030030910900040c0745590004041c049034607072130361402d01851042203003010b80300400072504401c01c83c00c1d881d017011981c0c014101c3c0303060300c6001c000019264002d4040f500c03450f03407040604a1521030040703140c0080d040b4441850708141000300c0058a20710000703000340103c400084100c2c40900c3d40d0b4440209034858420840c891f41e95035400580e900741405880020035110500650f1b60401745005400007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 582891312 1250 582890062 582890083
    0x3072706260106030f0b0c040812190804030801150219120e1509011b050f07031529011806080403031b021c0e0316080708011404030c030e0402040b0705 67
    0xb6890544100003050040400310b03801e0740c01c0301c507506403600e07134164011091046802548032842503c03481c480c1a06484010254200e004504000c110040d000803101120180d070007800040f4410010302c4403a41500210703c561140e40100c1e11004c040d20081000280610429203c01e009140b14075070030341e0065000d0300009000c0b5002c040070702c0c01c079415030018000c8244440c10040c070204403682113000100000409a002402c40d820b240462140381c0e034450143c042119030070100d02c800900c0c42880c2c05403112003018880d0f02c6041c490034015258054a01c0d005040c1049414105000328408850b50364001e442d196444110724038090034064180c85d0010485c141c10004020300090303840c3c0c00b080601e50710551240000d20416002130840303603c1460059203625004911500460440b0b07804a20304586258080c0c81802e955500c50500b00c818460400040c80c94600000b0006072080061020341032081c00c028499015000200d01260042d8000031f480080c002040018800c00708201c0e0b100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 582892562 1250 582891312 582891389
    0xf0333070521041a011211030f03040314031608030a0506010e0d0303020a090801050a06031e020f010804080403080a0e03100606091403030f03040503120a050603072706 74
    0x1040944030380e0412050b4a541e11003081560346010a0801106060185207240e0001a503c0035584403450001d40d03082001040b034402030f6900c0c100d00942404651070740e1400c210000755050504e10780321214841d021540300102d9000820060880220701c00e14400c220703000d510000d8032860b080113503104031a406002d25040c0a20000d031480e80750385810f600d11040d03500d0300c0d000d07843d40b00303d22003901c0e52041038205c4581035080001b0000d40f00003a5010340e040b01c4c0504044801001031440340c90414039100030107900b00b50100c01c0320b55254080e030981e03034009106c1c959840c03170a0b0f1b8986a000041e007185103400005004201c404082d46010032001a0307005800e101000001d24002d005010a09a40720305900301100d9801d08103e658144280d0385104120995503645e4901440c0464403a80140c0c2c00b081280c82c03401c0816119809846071718481c143c0940200281c6003040c0205280c60f184070102d0420f4841903111358448401e60041c030740105041303150110441805150440813450304400400c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 582893812 1250 582892562 582892567
    0x10c030209150702030307060b0105090d050c031216030507170a020d08090105091e0709020310090e0d050f031801091b06230705030f0a0903021c0308060f03330705 72
    0x240e50080119100d2560160b400956210b0b49e0005a50301e0040d0000b01c0c1d884407880e60100c052040c0400c685601040850958038503006000e01c4071658010000e0007100b942d0b5820407140000d00500040044c0d5025180d000700510018801c0030044e8880c0040000581040548040b026042522030342c00c291040d00034040c40c80c01c050680d5031342201410070541889100d41d40040c451050120a0190442d1803040d03640f442d00c0031058401400d244640701d0340d50b1810240210109001c651540b100f800307941c44525142d00403841403070f1604007501203840720a54008080d80c400e001d102d8000304a220b160312405800b1500d40c0c1c070b503594147d680b00500b40404102151807128107000500d0220310403004c00c944030201da040203131442c003800c100605298000111099800c1c1c00180e8941141d2085543c22071004005030000903601d502d98000b80841c031514003103180340c030b4409060210307104050200c9405244509000a0303844030b20743d4161040781924480e0b42c464101140740703640404076081c45032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 582895062 1250 582893812 582893827
    0x40305100c1706011d0a0603050610020d090e1b070302060610030203070f050310031a0109060f030b041e170d0b0a290405060f0a02010e0d0912030c05010c03020915 72
    0x90920b4001031141d0f0400c48100e22680c01481801184128000050a804003160326400003a00038201503802d07601c02ca04040040480d03e10024481182040c01d42e1382440d22468040071418802c0094600c5501400d07140f6031240003990070016100ca24041d90050090782459000c4c00b1001c0688001101054010400c20070b150381c020540c03114070f664a2501075030b41e0b078071a01c2081c00c2c4015034000030502c207030350080342405000649906041c1d030580030301000500d6542001021511843c800100310280800004004c905c40c80c07a40802c4140c0c0640c080b02d102d40d075a846c0c803500380d108600300f005804c000c910f8902c05256407054213140e0300b00392400c2084900b4010b00054044640e181380b100c21680d0706407282199030740c0c6e059800900c00502002d403605c0b060f01c0c001410750041c80b400c600540c604406a00401c00010ba92032011000e91581d0000c0d80c10301d048550214944101a01031040445009000407000d10451003c900329a50041c2c54141100030000641c0f000c40d0013000b01c0c3e10070700610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 582896312 1250 582895062 582895097
    0x30201030b0f2b020607050d0f0c0b0f04020d050d03050711072607030b0c040e070203190e0a0e0a06030b0f01032d020310050103110d03120c05070206040305100c 71
    0x104041e0340451005490f00f010040304501011220000d400130f9020803400100840007542110010381501c41641e4040780c840102ca42c1d6502c40340251080d01d000003c02c018010380c0c000680c2207030000d403074240840415100c5902d41000d89610000003541c1e00200400140d000e900000b10205420150541320300d03003060322411000c0031919a614210101001c6802d400c200008001598840c01c1080c0910300145502d12980203071152040010503c0002601588080122160803034084151482105520300480e4807040714210203402090f079010108a0107a807202d0103116210451000c0b95030b41c107524120101100181030f08000c0340030726005000080c5220001c0541518500f44080800e0040c4c06105010300d0f1070b10702135050b0256050355002c454441e0010707416203018203602040c0ca00124140070358501c081c0406000070340c2d180c00e180c00d000c07200d03000051009024607140381021103507000034907a6807142d80111400c1d400923400301407500b042d000700b413000c101c00e0a087d2010f60419092 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 582897562 1250 582896312 582896329
    0x509010e0318010903051009030f05160f06060807180b040e1b030102280f140403020d171902100204051302031803030a0905011802211c0801030201030b0f 68
    0x104001c0005211060740d07413090300c0030002140c011045410354414892440000c1c55280020307400036550f030031160609030240d000c50f030001c1c41003081d111128890752074181003034155070b0045a81030344509001458405c10050f150190000c2000354000908240070b407011695000d00440c040c41c1080c401e400884408200c1d503052050718113043c80704500c0b00001a00a04c0348070140020000078000807042c04402c8a0314260b40502c6440b49103000b043d06001392064400407401d14075080042105200600300058001d0f8881c0c451030541d002541e8107440c0c0c4030b036600580c071960503001d00c90868010650703041040c0c1c0643c82d11901d0461402d410103012400702007940060742040b507000030110f00340c51004c044c44034050a0060540e40c403070914103020b03400703002c0b0700b4000e581c03640c200752039003408140d200003c0d10840c0e4000c06185140300b01c1c070242d0106940003405015140503181c5491001c9600b403050360551451941c44000347e60641c40058112031040c4c10290040104041c415001d8407140034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 582898812 1250 582897562 582897577
    0x1060f15020d0807020c130605041406060405130e01090506060907031e1806090809030f010209090a0507141c0509010207031d1302040b07030e1806100504091e0509010e03 75
    0x10a280180d9613040140e251401645c21207800c00c80012101e03004800a42c01281903d0088900b4880305000060750307030800c001550019807000c4100300c100319910b041003000d54208407030040072810143c2c2e0700105007190010501514590041810885c0c14039018488692122040c00c0070002c1658004442c0c486040030100141003a90721300c0400301e5407000701c0c02c0f401d005078842001c0c81522a14507050f031740d6406c90701c0200e01912906140b02581001802950079030031020309101000c1d580c0c11a51070142c2809420201805801d10b240c46000d0300e41c0c001030040d041078411030100d1510704d122080860300000c18080d0103902c148175580019a012520008541101d0110954031300200001140030602201082100e8400600043d17011441c00140a14034041c1c0c0310714080090740802c1c000c0c01203586150515010321003001030000d02c0d01141003490085c0c170b45441802d2a4442e00d0030750864510340340180300e414080c420003142c40c02501520b81e100707540c90021b00c4414116060326680b40503001c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582900062 1250 582898812 582898817
    0xc0b04030e12030c16090c14090a1d1515070318050a0603061a07080d020f040506071103010c140a050c03070602122a0f030901150801060f15020d 64
    0x2140c112040d9242c40c000c903205034440c1c0030f032641e0712580ca0000fa80c03001d52403490000081403e6000600c101240303e12a91503281d511036296070b020102150317100394803003240716521240d0f030140801d013403241d00c0d004540c2e402e00015031845410420b549020510000400611a8a002000c030010f0240b050945010aa05080210030410464100600980035030041c81d00568032007000511325502d500600d084400d403000030000c5d4030900c00510600c0c462040040c104401c20450a02079210aa0042c580c0c210742441c0c0600302516600001c5051340402010780d4581c00040422030705180c28400d1001c010828109803400069800b00151680039040150081c00008030f000d1250b10350507c202ca41c0c143d4081000c642d291001d41d41ca807080d5505a503400240c45924008542d0900508003039107001c0b61407075006041111801d0010004d601c000c000d03200301e5494503100d95080b41c00701c00d5003014014101c0040f9409040241c10084101160301103050b0b04407100b03150a0302c1d5004120b040c160040d03403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582901312 1250 582900062 582900077
    0x60b0313140c0d060905010603060e2a0f1e1302030402040e1506040902030106150302190503010b070b041e0623060603041202150705090f2418130209010806010c0b0403 74
    0x504106e401040c003644098400c50405a445003d2140811450020406507001d00940c03102c0003101403424a41c1d5074219040b85548444007900d1030442404504841103455071017003d40c01101007105034500c224a10715031340c2c01009110441c42c081c0204071540c4601401442c200700d6441c0040d80d00e04002c1c00300c0d07000c1c0b50f6540b0342c2002d5440a400c510080d01d070f400c0c991355807002034100040081d449030b80f4441d40d00000c0030380c4c00000380c454411641250034003581d10341001003e031900c201d900300150003110b10086900406800c0040c18440c000c04500400d80015000801c1c50b21151110101000c044058055030800a03a81d50b64025250040c3d041594000303545030600c4203a00e009450000c00c10b41400030005c100319940c2c0100142504082992a85050141001031000f00d50707511510030122281c2120391541200350002802ca8002c2c2d4503c0380075100c14040106194030201e400401840c0d0700040d030b03000b403560000a2540c104c1801e2030650a5001240c07070310100071001810080c20459032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582902562 1250 582901312 582901331
    0x103090203120918090604110d0c05040f0e0a14070b070b0c030604181b0b04060c0b0c04150908190203060703090312020307210218010c0204060b0313140c0d06 70
    0x6a40c4c0300c0d580c0601c16120000d0504011280ca55100400c0340c00b10b420700e01e640080e550703905011584664540d030000594113600c0c00d1a08110141c118030030340e400700d19941e04400e81104010024010480d014000d0554000d941445d000c2c00c010064210844810301004103100181c1030300400c6500038110341c5000d449440b02d800007006001e1849180c6108800c2109100030710440c5c20324000c0d8418481f0401607070316034480210040d409148504030220301b2804042020441440d4940c4c1d00c00070f078030b41d094074290700c1d00000c0e00350040041c0c0c0b0030300003a508103081c003000008110042402c80410749036024002030340d002950b11107000300f406003015103496100d820540555144160002c0c4000255124640a40c3c002c01d40042801c6417042c840150b02031800440041c401c40e003c1a0300d8003908034088961100558184100881c02c0340c015507190030004035880c41001650140300308100101d0210b140381001e07508002c0c011662920743d04002582441d0b6075400070018900755000d0004141e0140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582903812 1250 582902562 582902569
    0x60507021311030403080901060609140f040e030406200a0f080a090308181305040507090c020304031a0f070f0507020d06090210020601090f1406191d041101030902031209 75
    0x2c4a485041840000c0244000c16400c001190301c80c50f1240002c11086a51f80421240042c0c0e43c4a17180f0840d1400304070024600381034003055280346c0b001c1c0020984801d5503868030702e07560095126100044103903000c2c090030600421001c1500700610014421141c85840321202e441c0300381d00c000c010f10000560384030314900422200000b150050b60700b545801d203202c1691541404602818410f801c2aa424901d2040758803985000355005001402c2c074900b04850b400c000c0500b0f00300241036100500c070020005000704241c00305040d0320b061034030040c01c010030410b100000c08ac00c11000d20078801e1042d09100c1c0d00c242511800381e011142c3c009281460f050102c010f104001c00a50017880041941e015135800040081c101c038109541006003505a024102c2103a0b140c0b024009110200c1000c55000d207441c2035400b100508a09504054030b984410703d00c08801540f0340c224406044100708400c0c0f00d14120340c40c0320441c0a00f0140901c184a500003503c645d030f070030906e0100c0c12000c10340402d9901c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582905062 1250 582903812 582903821
    0x80307030e0f010612060c050a081b0717040305120f030a050a110a1701090207050307110102011104060f18080627030a080604050c090a03060b01170705030711070605070213 76
    0x180c0c2e50300030411180c5440061a590854140c01e8071814208158164280d100e6021524062403c0c1d5514005498000d41880711008036803800c14503160030701c00c4001003059418000ca0b9848880c0c16195a0741c690f20305507007002840b402c0782200c0309084c40010241601c01e012a0340c03140b002c1d040080c2d55a83d9071090783c018080340300d450105840204410354a140c00c41c10b02101c0b24040341c0c914032660790390012241644161070000f05160010710200e000a950604001d410a10500002c10040d0307156080c0302c1150050f038030801c00104246004038051350004841350807809148040c42c0c40d1401c001100d80d4442c00600040c1003117107074526103440132600030b07002d441401008040d207564106005008041c0ba0301079621a04c118984400b107400548002cac21241142c1c0c000e0000349200b440d50304d50000401c0d044006c541403160072150f010380810b40c3c100103441800140c507195100e0400810081c4400010500c00e0b016500804003071019682003001c1e6241d1581c12540d916000703040184600250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582906312 1250 582905062 582905083
    0xf030712030615020102180f01021b030c041e0f020304030f1b0c0f05010305150307060f030608061306050906091c0c060509070512010b0109090504080c1c030f09080307030e 76
    0x1151640030403c2010381c107400401102035007004007050605482c0030042200c1b038111b945405070344100c0c075110764417180c14500611000c0041c25115003003170308808502a030310343c03107148001c0140310500c005012540d88507589e131000300c08904509528244d0390151011103040300000502900113a086800032805503a800e0032039004401c554515585e2140e80d101e880303540611800f107800e100000c0da401ea440b41024401407030040081284500d000000e649002c5440280340c200360300e881001c595008200300e00c030b005100000340c1613020b00481c01d00b0801c0760070203403070f040e001e40204040c88490b0030300181c0144410b0185d80034050180c50301c07000392401c044500d0300070030300340c01d00040202661000c01c681003192000c6d6905200803550000f154200e5065084890114540e4202070203a0f8807140e203d0f66000b80720301c440030303d0405007203c120324255030301c41c070003003080e290700080303400664540541140201e40d000140040c2c031081c2d40d09090381c0001802842056035910b12030072100d804104d83c1d07014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582907562 1250 582906312 582906329
    0xb0114060903100509150c041a040b0c071d0402220209030604060504050c1807030903050705030c0d0e060c0325120503011d0f060d0c0b040b0c0c01020f0307120306 72
    0x1100c18110850300948011030354080c95000e01c0400c480101c586e1a0b0141c86030300300c00151407030305062414108400c0509405203140c07110902010808104100043c0480d41d1440000c01000746854442040b80540030b583d20501005807040c4001a03d0b60000c0030706110302e0200e20351041c1761311100c1200900030700d062258980f0441080c4424400e9540c4400d00460080f0709584e11503d0380820302c02325908100d40d04140c00301c0400041c841c2032080c0d200c2c0801e14420301e041840d046d40c80c0c6030703a07186030403002c8079441f990445030910304200e4000524061800e003e4611030706000070f02103105d40fa4094031041421805090480004003414126107640d0240d111504031001407900c0401450350f00240580560100b04031240d04801c112001114801c80d0003111800590351180e0502004031403426085580844083c8046966801781c000b52014004903802945c946149444140c40c14207205880c0d4195000031204132000f03400401221025078001c034403901205c5003114228020032a55110804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582908812 1250 582907562 582907573
    0xa08181f03090602160c0f05120d0c0807020a0902090a05120703020d061d0619050f1603060b0a03020705160e0103020919021605010b01080708180c060403060605090109090b0114060903 81
    0x8110300800420269650f180d04010288d8031102071040307044004924101c80c0d4401004a059140314454171406548110711140c2890840e502003808400b00d5081032100a0f00410981110304003440c800c00140011210904010006200f0640361011404040e0040305501541828090365410004a03200040d0000140000c08920241c440c034060b50f0314164401e00d881c034840401d00314010580100c0c02d0300a0840c00340c490b942c1c201001210007424a0625403500070001c1d0451240d006090503001c80c0d10f01594400701850140c2c1022900403211144114812051080c4000c0b20b4803581540e50540310a0381a854510031800d0321654802d81c0c405007400020000c00c00d91541c8044100703244510000d11070603e050005541014048810b030b4000764440d000038071a40d00c60414410b000410005941002101c0317004104582c1c03054005680490329004100410b05180d5480d0b80140982c0008105502d165035682d0208041032062a14409003600700d401d1035698101299a0313204010100d61 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582910062 1250 582908812 582908857
    0xf0618031a0103051608030d020306180a0c0924180e0907030618021e010e18060901080f0601030210090e15040c050c150a0902030a08181f03090602 65
    0x348010742400100d607a4025500c02e51292190380f00c0b00300a480f1800007640c1811112640f90000703400007030220707600c40030b100b04000e0310141c40c0352428042c11115a0104611038130b02d80280100e9465401103940054800d450b5003181b20213080a440760400b40b61002c1802310781e000b0030305628410f40020036000c6142c8140301014400144920480344160010310400450540ca40c21a62503400043d4004002c84004418031048040c030000b0100141082d05003107080d0004901c034180c5164995441194010a0000514003184400d00400042e0f0060145a907030346030494540b00b0602c0f0090140d4100400b1200f501c1c055611340c0c0141c81351131081491850210410800481001d0342580107510703002c9500d4a83d40310388212500c20078040001c0041c0c12003040801c40c0181c000b4030122034507646003d28001a80d060000800103800b030302e807060702c51550349030721010b4201c582d44c020b10541c00c1d40c1d40300079024640c6020321000384450800107084261070030704e403029110781d0b1204107240c0c48c1c02010302e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582911312 1250 582910062 582910103
    0xa030605100308190f0c0b040f060204080304030308010e10030c030312020d0e030304030e0604050d14150403050703080a0b0d020d0311030a20010c1e020f0d17060a0f061803 76
    0x7031082c80707410345d0fa20100d1000890151000c0d0440c40c2c0c042c100c120340200040120b04d21003041c00b8481d01c6000010714180e9910300990568015802c11800158920700401400f96032910003900030031041460304030301c1d2655a0300441d00410f44401418029a0a0303100d11040b001d0b41034036030350072100d41b042c04200c01e040800e9449134801c6030101c020540d420540801401c0c858203880a5034809003d00410916a0319074101144202d000b205040c461158502c1c00e14081d051480c1c000c0344070b1386034103844600d68500035282c8140240f00c1480c61f031824a01500030b540b4800342d01d10813501075401d0b40c1000d10500b4100c424010001044841d031000060400080358409102c00d40c0034150041c3c40c0542d0100050982a00c0300c0082c00c000041060394040300c0d040b00201c210040d0001801103e00c103900101c1040e0418100c11b08040c0454200481d1000549204002e540e1101044402d00c0340f59042123140728900d409401380d030f010000c450403032440084000d400c2c1d0300510b4020548880001103800315 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582912562 1250 582911312 582911347
    0x15030f04060225120309050c150717030105130b210a020904150f060b0306120f010c1d0301050402010206040308060d0f0b010602120f040e0c0d021b0705010e0a030605100308 76
    0x80701c81300040d40c0d118032032910070310400c0c032a680c1c003401429500340c42c0c40400051003c21866003018001c104000e6001415810404a5601c01090f4080d1650300d800b0400003068480c08540b04941d0070064038244079940c800d0307040740441070b000036071120030840f440d55031400d00d9100c4000c0d04041900184001d21410002071020300101c00d01c18084280082d04e1501a6000e510500940349400e0010820781d1400100301c018000140d411a002400142003150130b4500045403840441c603041c1e0004170b0b2001010140c5031410058009204504280c4c1c0002c1d507408008002404004040001c5859a51101300c51a0341a802420207145031179035052440c1605400c3c0b1583c400f61150318141086083c41b001076412100281500c0c0342071038074020441800010081080d00310003400c2240b110b68545504c007900411070300c4601c0c52181e244187e48946000d5160304143e040c4408010300109a80c0d0b040101001c0d00d61188000c80c0d07a45404030401c81d0b44210340c00081404401190268900c0001000b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582913669 1107 582912562 582912637
    0x319020d021909020405011214060103050c040b21010e0103020d0305070c2d050a2d030f0311011b32220515030f040602 53
    0x940581651582c11103105158049002d0041f03581c0702c41c040074004083c5000b0490b02228607402d0102c1d0400520b060704268175000018001c00303822054400501d8605805501e482038100da40301c2007038012000c0c44140560400004540240980321070480350058405820711035940c07000c03101a880600262440390b0307da0b0b00018540381d503c0d4120b40501c04c60868612206030782c20400c00c4195144c2c001e5216005e028410b100e2640342054280c41041d51180e903100691500a1904514086a02c060031000c0e000000d8818150445207101c03880c503008000b0485185c0900324a1608000b1034014000580e00202a00c04d40748003032515221422080c00c85502225401e540341c240340d0000424059120240200064010940d5003c80262070200c802040e4040f2010160030540030040407032490070748680c0810207110066048807800c110707001e0a810403440a030a01c1d81c48440c40381 = true := by decide +kernel

theorem cover : BRFrame.Cov 582733812 582913669 := by
  have h0 := BRFrame.cov_init 582733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582733812 ≤ n) (h2 : n < 582913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
