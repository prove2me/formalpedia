-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:45:18.839185+00:00
-- url     : https://prove2.me/submissions/a80441ae-2408-42ab-8623-fe50cb42f565

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805575539 ≤ n < 805755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805576789 1250 805575539 805575541
    0x20307060c15020f0306010f021207060f1b2a0b010608180705030a0609020a0308071b09140c070201020703020303030a0c1d0d030c03170a0e010e06070f0e0f06070308010e 75
    0x1140800300d04c201c8002205070201800020030341d6001e032a115031960303814010344130030125421640900b81e10080049440994031038aa116984852160240704451518413005040e00140d014006a504c2c170001e202c82c1d46091040c00040240780040090301764007941607401c658440c40060800c2c1400c0300d286040c0d00541c0003200744520000b1b0030388119407014028103170101103070725000080c119110041e608031514001c00000101c0180042210390700490a9460412942201d81000c80340c41d8051501c840c1026010481801c1c0c002d40c80c0e4100980d900310300d0b60341c9464030041c0c0c1400116880039515000c08420071655070526000f846280040340e0315040500b05110348200e000da0448581c41e0802560303071030309000030302819200c50341717034080c0c2000c10340300b003005809104210003103d841c0106920f40426040b250401d0107112000302214024140524082000400314903800e1408800c0041a02401c0702940b175941c1d04540071000548400e83d41d440170300700603020010038441c00c0c0c64005000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805578039 1250 805576789 805576823
    0x1080a14060609010309051b180714030405150103110a0611191a0103081b063c1618030b0c031503030a020d03061a03160309020307060c 60
    0x4403900c404020310303810404950311040140b002903000320340c81c6414503665030f4140000c41e0041004a01c140380841e4141400c4071000148800c1117103123400506411078142c01d01c02c01c41d80040d203005464101d5080345072250307260300f02289069070040c03205c001e11040344000300c14001c010442d141280b1050fa40c0e40c8649a560108440c07858160418519540184513805401c807034868100031868080c0d0451110380d55480c0500c003519000b81c0c000c0b1687c66001404500c0c2a280c4025030021107000c0b0081d21280c0b0b8100c182c04c06901400342d41c455404c1050070312090300c200102c41c0c185845c01004002560b49800f00c03403015901d1076a40b00201050804091124030911030840500743c1e0352011460b10f003501d0b007520841054101a04413075105186031034401d50b980f000c0000e00128856940107100100003800b0240c120ba903582c00c440028100b00b45c802e03140001080c1125004450400d0342d031030011045404030000e0502002c000d605003d4003000069a50f40800c030050000c1c010506410a131040c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805579289 1250 805578039 805578041
    0x30708010905090c0303030103060902010306081f39020f010f0207050f0309010c0b311515030f02030313030c0306050c120a050613050a1a0a030314070f0c0e040201080a 74
    0x131a40d00d54198010070050000600c19040708002c644181004140c0340c0d15a0546410001e02d00035140c9602c6015441d480d0304169402846010714406100c0120304510407403402003d4800780d510740101d800f0010102c40c0398070805c4855980712a03a40200006106005e0301c0c00070b54411141900c1c40d1103404484514440003208948030f00074140c4950301154060303600e141001038000d00380e504031038210070070840d03005e002d0b4a680100c41449480603625029468071103800d140010b95511124640301c10140c0c080460030ba440d0650f80c01084080c0e140241d4400285144101211100428449200041001101541c000a69102e81c0302440325070360744910b0350558000c0f9550818000d41c5400460580d2034580c1c40ba07070300110058103007601240541c540d1825580103989090300386a44d89014030901d1a5061074400040c0c1c2166401c0511345107880060001e15049a416120078001a000080200031012007400e945e0100c540240709640302c207010031001c01190143d0108003000001035040c055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805580539 1250 805579289 805579303
    0x81c050709240801060c0807080414031006030b13060605270f040b0a09030c05061006030c110a0b18010c09060905040b0a060f05130801090203070503031e0307030b0603070801090509 80
    0x28640d940b450f0303a0f1070a0011182c45a100009890240c3d08000c10b10100f00104020f04c041c0242c255040e0070060341c082803500d03280d0a08038810040d854400c00344006a07240382e01701e4005000012500c0b080340a420188001c280660065600080031400f0a0340385c0d01c034202266907800007060120107a640c8041403c8181004c42c1c0050900100300d000a0715441654080c45400b40a0700d004002500f10341d88583c40d040003699822106010350750100441540350082c552022500e251010080e408400d81e203a135060404002030519118000044408071840300740f00c01c55078010000e100c403401a520241000c4141c5c024000010342d01800840d150034035018010708080054005103c0501c1d04004869100c900140360042140030020002c82d20300c082c4d010809000214000034180041d4810103213042100d40c01a8001d4100b84200380c0034a0034402c0303140c560b0302000007030350b80d1b5512981304500031300c003c42c00c0d13903409100481445580382d4402400e9041c0e680750030040015855040c9490b9407001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805581789 1250 805580539 805580609
    0x12150305010c110309151c0510090608120309011e0501030c0f0510030b0f0d06050105031c0507030810030c0803030a11040812090f04090807051018081c050709 70
    0xc800c1003c9005c6040043d41c842c07080070303504e003041e0820031207008441c108903091030b2264032035841d0340c00e100c95007401c404284010400c2060800000b440c00d1549511030360507040c000d14a6401000140080c102908083c070102c0f9214404004060101c5045c0c0084c4003c0c00142d401800c2a540441e240040d4050082940c00040034076800c80081c40e004c80240c40113504441e0040c05e161000d40060301d07140d110042d120301c0b558021825604200c01d05142c0401801d42501303506035a4601c4807507a81000c102ea01c240d80525006a060343c40101105e00003015a200a104e03410480740010301802c044040c2d07000300071442040c8900c2130fa00c0b051030628000c501805106401240c0d040e80114101c00c010085260081c1c020006500030200003070440302010000d85480000080c00001c101c8240700c4c1c4250981c1d241c5041081450b8000009100c030700b540310062100400060035000508140b503084003038001204103100500d020302004000841a1041d00c0d4060100144401450307840400c03100115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805583039 1250 805581789 805581793
    0x50324012903040302160909060f0c080c0a03180311060906010803220906060906081021021207090606170c03060922060b0108130b07080712150305010c11 68
    0x1c041d01e41e22803419071028008409501c1030200000071008480e240c20010300042c0d030001080c1a550805605880d00d81d2856140320b49070034982c00c0c0c101c0d08041a65007160705003c05075250300c18000160010052144010b078040700807c014410954804102c540380104c40b410394405886482c1d46c26510300b000c0c000c0ca54145c0003404500002e8520b1507884910b0340450044420036a80d41e40400c04507206500308a0000c0d42e420001d1001d01d811004194000e461b44042e1031400d498000000c40810011000da000803004094000c2599503000c000e00c40d210300402661812603440c13202c140203140c030741324410100e05002404c150250324012010322988000640900d07540e1003401b040709442c0001c000020320302c0a08100e8a099041e00c520014983c41800c0c0010000741440c005400c039400280f00c40b0b1818191001c4400140b80086219003200150a02030350b1500c0d0408160b618040144001c400c5524101d42c8068081c3c3c4500001d003100d004400800036200e180a045500c0c03100c80449070300799 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805584289 1250 805583039 805583099
    0xf06040b18030304150c14040308040f082e0605090f060a050303090108130203070b0301181b23040504020a021005060409030207060f050f1216081009050406020405032401 75
    0x16040b40c1150346d941640d444c051462000c1190303c401580c009820075269200e0114041c000340c540004030130080c0c401d50000b40094822102c03000c141050000303030110000c0c00300440c00543e52075900680c0141400034a01d10f950705d4041c00c2c0a414031012500548201e1080e01c000819013004000c85070714500607581e034449a503d02d4107442c1c510084240490b054810600d0004080d07120304051806000039000c0380d60a9000454002c0aa034a1403201003a070780410768904404a40201503004241c0c02e0341c0c200070440345070181c441003601903903210b660000c2c000942007a000c0da000c540c80064100c204000c02560f03d400040c8030403a00071080080c0940d10407403051006c0d9002d0307042c505944030303d80f6004e0300d401009004200e80c0d800031030302000e212410000748080c03105401e42c442684001c51610302100d1401c11141c580205061041301c444a940d0b2011505001080d01100c0c040c2c100501140e40500e68581304c3c80c5601c0c0302d400540384515001300041151400b910031b00011800c00780e202401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805585539 1250 805584289 805584323
    0xc0316020304090e15420d08120c030106170907050a080a0213151a07050304060f1e090b160203030a0e0a1d010b2a0708152401020f06040b18030304 65
    0x3800c003101c2d81d64008a9021585162031f40d0348500c2542281c1c030034400c40ea00c0b26120350f6024600c40014000764404003080c4010b10526502440380040342d10490200786003515030341d507918180400d070342015401c1a003000380811030b801d00090b5614800c2c8261034081640300c6d0340c500c04086031401e214089586800d44010090201006071103c24500e50080052400350650380f694038562140c0e0018003c2810203410307111040d00b0002900d0642d6050076458048156880000c1c00005140240385903440d02080305203000c1c0075400d0481010340d0180481e40e0b214426407014104c50600b0003400d1040440348008106084800b80c0d070028201c00441c0340c4110b07406d048078002203401403200354030840e038002071004180744501c1c0d10707050303e20b56500540411070910705150704062000d06130032404070040e018004050107949641c01c0380c122115284080040300340040342441c44280c0d02d07050a10a03101808180318414070f01c01c5c040c4880c03120680680507888102c2e0345900041758041c4c10404a1150810 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805586789 1250 805585539 805585621
    0x100213060516080c1005010311090105011e08150d05011d0a03050301031e050a060605011404060c15110307081006080f071d0402121009050c0316020304090e15 70
    0x4a0780100301305550b031403184440014101e03038007640b054890510010280d0410300301100c01d01e01500302807808400e031160052200e82c20710300119030310082242d0000010006d10420200c0604040c008060002000303480c01d2442c081c08003581106c42c070300c0684680708884513002031510422941038580b80d0540c1c0c07031034507000c02e044041c01c19020002c160b0748403000010814880ba02d600c1c0d01ca4080050000e00b8100010903090380503072405015001044203100094004000e10070081e4010911102850100300c0c000150540440b6502300d03d001000b032021441e08031405501c00d40c00310080b611202d80e10203007113460701c205541e58404400c0881c0403409051141ca440810031707080e011448000e515040c040b0b41203034030281d20340c0c000f1401da40c203003c1118038801e09000108a200310501481c00d00500c0c40103144405000c0c3c1d545100c100b115510041c1c003d1040d640201428401001ba030401d0001c802e40326501c0407003402040c2c0ca500002070200030000154002c02c1354054840321400e60003440ba08e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805588039 1250 805586789 805586797
    0x4110903070605180604060c0b0604020f0d0203150613080c06030c0409090c0803030903040504051602030a1b050a0c05100f050f0708040902130e010602010207050606091810021306051608 82
    0x80034084540040040b5207903040240007d0541d6500c3c10407003242820702181e4010068006441240104031282002c1c151006844401e00550350041e86c83c1c4940013100910120215844d410000105500b00001070000c00c4900300c98841b4161004859003404122191204440c86004035106000602001a8643c0031081e114442c1070380c0d014213911501c0540c61034108459000e4164000201402141098001d240c1c012002c0d02c006076000000c41c001039264000c840701c1307004100e60300c0701030209450100069141c0e0358100c025100307054000d0521074007001090090601401032003080401c254480c001c61880b506155460509110802420960320380c454541600e1104051101040c0f040c1c440c4001c1001c0e40d26030091100082c58411440c0410805034090010b591050bc51007002c00e801140450f4006001c817407a4885540740180510881880c3c4002c40e198840c02aa190b1809800c2d070003803840c6c602034817100312000d5840000300e40a210b44a81c42c0c03210100200780000250044000d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805589289 1250 805588039 805588057
    0x1101050d0e1011070b160c0611031506070c0b0c03120f0a2a030216390513053d0504022704060b071104110903070605 52
    0x14500d400e12140d0500159025001e64103240d03004400b44114096807403140941101200c16258200416900c83d0700316140010310329840c4a42c01e44400d176505100781d408070060359021500300507107413403c0c041d845140c0048502215403106600700c40c1003840d08000f41c8960b5070b80441c0c0c150001d400c1604501c85500b0500520200d803005104813040340e4000c500003446410486d212121034179010b8400d500391481c0540d0342c80240a19000d002c1c110301310b82e10b140c1d00c114280c04c3c05644e60107129443c0030002803101000e482c4c0c00395000716107050303619040324140c1310f11850146a44504605e803081c030760090340e2248070346c40740340b86a000e40504c20a421066001c030080030111442079481a450203a5604040142c1c0f810100e040340804000340e01e94950f0203420203903001c41c01c155000500e01c40c8c8811800040600f500102c1c2c1480041c0e5441c1c0082d0050031250ba901a124040e600c1c1100d550100b0745400b0303109600341701d80045180d843e4400da848403a401001000761526122080c0c0b4240e00106807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805590539 1250 805589289 805589297
    0xc0509010b0318030c0a050a0203060601030615030506131b090503070b04060804080405030d02060a06080303191518021803010509030a0521010b19020a121b172809031101 75
    0x5e0f400c0502c800c0c441c140400380100c000d021a0390040c4105420650000c100d07506041c58140c040c03143d0f000b00740b968941c0041e141000110790b154000018240b4030080c0000100c40c0c20a40044203551150a00303442588183d00daa01002d500c503001c054680c100c0e030203110075038003007807204000442c81502e40c0c64100d401008410324044e1904003090901d281c0c1c40c0240050b0303100100b4025051700a10404d0000d2200401460541c141191001e18800f00c80040f405041d444252054140d944041c2e128014160000550b40e01d18041c04246d0203508600d00b64039607400b074880d030030f061820103025141c85910000b01079441c141c0c100d50260b405800084074440790070400e07100c0c1418906c40004150181c0b00601000d511000311004908100f9072000400045411210348100015490000096107031040d0030040c0c01030f07103041e191800481e400103000d080001604c0c61403d65502d0580140100c404a509280000c01121400c0c0d2401c04c040e100c14000405c1c200f410004102c4043ea0450f26180500d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805591789 1250 805590539 805590547
    0x50a050f0d0603050309091806040f210f110105130f0804350c09010e0c1e0a0e1e060307050c1024030c0306110c0304120c0509010b031803 61
    0x107400c660311500100c5083c1c0c40060303803c0303452400308410b6601202848036921141c14450304151903020240000b0440a10194902e0401c000c201074084403100b101c00307104030039400200040810300340303441d030310301161555041d66803c03901030003001d20852008070400303000c40300795941e0407c0000e0030368103840740300e414800070032282e84040c0400c03500c078007210408955001d003408980c4010b510028091566105032000442900c0f0190417904407101e40c2c2c840b100395501c0d240024154494428441030f007030102c0200d1007070004c150016005802041d500c0700c4020b0000414410217800400500b8100114005481003d01c2d05900440c2d00c0780781440c1c800c0c101034442c142031f031400008907100c0d00c3d640d4a85601c0c180d5a02d0b000c0301000080c1c6c044007041503c42c03568441e03010402250002925a50f120244120b01c215403004450603842c105048039a00c0f5600d0440641c40d2030f503c0030440c1c07943c200100000d00fa1800d041c010341a9410041240c0c6142c48800341d400204044040243c0540000c1c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805593039 1250 805591789 805591807
    0x5010e0a1a070212120717090108060405040519031e0f02124e06132c1f1a100c080d1d010510171510090b0d0201050a050f 54
    0x404403503000380c1ca40300c0a98030b0300d0380380c030340401c407000d02c429400c3d01b194080c071508c065681d10a131400d810134010354000849490b28204142868660031044405040058a4004041d48120300c405504a9030f0103500d40107250003c2214044038036041c0b0300060341324002100642408100800748400d44e410003071845180281d02030a00040e034a10501e100a080070020740520410316016250344c4580b1112526107024800250124009150800007903541c0d0011400c154900300005814500304e0780c000e903203040c072102e03a070758170047d80c6210148905141400204145180114901d4484101505a030241154103000700860710000d44403c0155180c81c20020480301c10080103180e1701940082912031b105490940d029801071462603042e89010200403000a040e0100c0d400d0f02ea1002c0844600394103034840901d03000c3c240f81000b900780d503990f040c0202003203c285110700326589214140010400c840400007610305192029021440800c0501080c6201c0d80050880f805640304683c181130070301d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805594289 1250 805593039 805593043
    0x1507061503031112040909140a060903020712050607030903050d0c030b030708060c030f06150a02010501030c05060c0d0e15070c05031e0307030509040e010507030605010e0a1a070212 80
    0xc0c0c0040440c000d003019050080c180c0c0400e941400c08807000041000710b00d41800a00c4600c9148602d102413942d4913211030412055640d13840c1e0384100b00c4111000b081050030304400504401e0001c402601c250b4000081d2498a810070340005a0410007819490b074034803d0980191000d9001102000010050280046c1d10f912621a140c1e00e80c0d82c000640e40d10a070700f414540f050310b4102c2030180d070001c000c014402d0072420840307500c6080421030b1320740e58456102240c001500c507806001040c03408070300c1d400c14560550105040361700030b503442040b01d9668818841f080c411103403c803007075800c181040c1c8400c40c020310402140c101c0107003100300031802900c5000e42c150840282240e0000f0184010411450100a000389941144130018089040030203250750380e1103914001401d1050100707e400041e5266402142101e130580001d00051400701c500400406090168601041365600448080d0030000140c0059070895401c500e03400c4a026403c0009800860081b41c3c0300c0340d111540500c820013 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805595539 1250 805594289 805594301
    0x12020103062105010c11060412051603170f010608181207050f0f010b0303041e0512010902100305060117100306091b090c08060108040c050a0b09120d0806150706 71
    0x80d107031580e103a0190510b030013030a40f41e030907911404016150501161a2a0105c3c007150883d0b840581d44401541d80d0700196024016030110a044010360501601416084400311400301c2c0340034030114031b42d40c50081030406000c0130b00401000880c00c0c40000c000e040d05060f5608180d4200003141ca042039200034036071035030741305102c02c803019000742c6035045040d00c0c20040542c0c0521090020300c002050100840c1e41ca002d1803181c00c41820007210300020101b40c044800380a800c000d80040f042e450008407181c0038080d9000c04900490800240240c40c510a1048030701070001699041c0240c0f000c20180f80480310064907100041094400010002e10144900400740d48a0703094070300003141031800d40250040e180e004140b0b0500300321205038010760089896500c07590900b04002141c85a040a405481d960b4200c9504100040808128400180c020f0007203c0310032205c401d1842c00000219071101000d40000012800b4000418100e00c3e202c540000c1c290701001203079062010710f880d00303800e40c0d074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805596789 1250 805595539 805595579
    0x5040203310507050f0102120a0e03010c0c0201080a0b0f130204170d090807030807140a02030a0804150c0c0b160c0f050a05030d091710090501020a08130305041202010306 75
    0x1c01c0c014403004004080c40110b0081c40100c8024554415140010352035a00030046000240300000f041c2034818000c0d14400300042018000304481075000c04080e1121070740348003e0380850303601c1d40041c9000d00e2074005c8916400e4080d003429260305154041c00360040a00e144030b0310158007400f020405848407880d680194260703100820407040b26803000381010305160044117207a0041107041c80807c4000c002c98440340d070f10049141a048142e4a40c50402e680c05100a60602071201c1540c140700103613001e4401d0304c80001c00c85801014007078054800000e0f125008040081401040002d80102c10151084002c04011000c41552595941c040c00240d50050b9510500960003070203141802142c4a024000950080541282e00f90010340301c20814842c43c00c02d01d455400400a00800740700d9603a411004000c1402076803054508503010b90001c90031031001540741e4002502c0d030600700d00b11501e040e07010f840b0f82d0710b414185030941640100c10b06040e07040c16141c5c013001644101010445801032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805598039 1250 805596789 805596871
    0x90d0b040b01050a030b041115030703050406050702070302031c03021e07060b010c1e0809040207030201020d05060301111903060b07141e0c010c0f0b0c03010602011b0905040203 78
    0xc5400d180c0690541d0042c1c10840c0a1001c101080c000104c214540f1a00f0030b0304071000c0880c0d040d0030400a8846002003401d82d80c440c8020061000154143d0001da000e24440c1805018a5070340c290100e81e117140c684006503140c0e201c4010100e1014001350025200f4005280141c41c2030800c2ea24290b108603040d4501115480000d09801444501c0c892180308501c00d10705002100c6079600d46420040d141804907010300071000400c8108841d142c00c90345078600c042c2c0203540315402400c0184c002d4001001c2601c03a90308150000c0c04501e0b041c418140e110f41c1e030010721410b0031a42200c114008204034484010f160740c640c0041070003050200035180d00c45c4600c101c2003180b0001c640341820b1444840c0d060210f000c20820703020801c50042034640c160b20080c41c001011400c00e042c009041c0802040280100380448240001c010008004605071032154009102c10000044101c0142a511094000245070743d50240300c03929207070300115084a00b04820f44890011100306c0c0710850710218040030f80c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805599289 1250 805598039 805598041
    0xc0d02010e121c1113090504020a030204230a14060a241b141006150e150301030501090308010e0c0426060108030d060b13090c050d0c0f09080c0f15090d0b 68
    0x103445c0c4000c00002e00710140e0306001a084c190f000c102454102e0000a12854a41e1550309100004d0348140c041c0e4042e044c9199054240052500010400c04000102c10541000011340a04000304074500300c0e460000328441100d0200303554565a0303026424402007100c80224440600d00322004601c00d00d0041c04400f540302034608600b0300c0c00003030400c2c201a681c1800010041c1c00c500550400f02e21202d03042400c0e40710078180018520000260b410a40c0450200010061040540c0403d0b5102e100340c4440c00d8070398031041c1d011902c4104542110001104100501800051000b80010140404d0440000240500180d0304200d000d0700201615030005c00d01c00329800e40380c00340a006108200016141c003091580c1d003400482c0074004c881210340c0b503440c6a2405445041240c040001800c0b04101904011200801c0250600d000d02e0020b805501c011601800114403012100001400084c008240703509201d00010340704980e0481080c1440600c4081c3c23201c00d42c0600382c0344141c8801d112 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805600539 1250 805599289 805599307
    0x903090b2b05070c0312020f03091c020a0b0103120509041a03070b0a0c020d080c0319020d05041211030f010c0504090e03160809040605060a03020c0d02010e121c11 72
    0x440030801403000031050030300c828443d00e5500100c2d96045180c041c070b81800e13040c84944a02019110b2200d200c0c0c10b40034000708004226201040c1061640600100007004080c501400c990750303050711802030a4007910038010030005252030b642d80c02c685000e040c4103040c0600440050201d03102c08000207140b840d800010000c030f2909200303805c00303000d44003841803c240e000c0c2e4005214124050340240109410504a81405541e0003600c1d1400c0d051400c40366035140c1002402260303c04a120100544a958580c005042c060300c1943c0c1a80d801c07081c84140240c2d60345901e80e07404805020a03400d4080c642c50045c40c0f66082c00344850124150b21000d0741d89260450020841e619180c040030150000d0011040300d0614107460099540c001c2d4219440316080306c001030007082d0643c031840c0c0c000d10018032810015015000307008043e07481400c0d240c00c00407a0006034207960382c09a00c96110782055038400303580d04920b40541610354224811031013000c0400c60003012628103500e000d217002c1c008104601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805601789 1250 805600539 805600597
    0x100507020f031c030e030d060312121b1209050d02160f2409050603070804060f0b1302180316030c0f060c060c1b031d030c0609040903090b 61
    0x1011040c00d500034403c44610b9010b00c01e01007858480301d0101600e982d9050860f0f00e04105035036542d50494010460150381e890416450140a95a9808900240c080640203601849211000c0145d80300000c40d06400301401c4481c1c1861b5070b2008081c0fa41c40180c01c0200700100700040552503580c0040002800340e000710120301000364040c2981c40f6140f83c0603ca080c5140d80c075900c00c071428031103155008805040613245008aa00466000302020041248441e0700511040c0180e0040001b0400714030710310b42c02010b0b03d050304a0faa0304092101d84140200b071040d030007000da0388080b60315003001034002e00009040017484980208417200b001420b0051145101d040b5008008150740648001e141401c0030b01390001035403000d826940c0d580318420034240140c0c10260844001000c3c6a5000414540a41000b220205da07900c408a1481895020304001901041c6000c0003000c0b9801c0c0145041000042c00c1c011400710104000700800084062141001d0030800490b0310060401d100c01c3e0745400307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805603039 1250 805601789 805601809
    0x27060f18060e061210140d051b0307030b090d09051f05130f0f0302030d08010f120f050d0f0f020703080417010b06040b030601080a050708040b040804051009030512040e0a0c02010b10050702 83
    0x34820922000807c0c0020360005008180303210001d600300f801e05800b80003a0a0015a40c0b014000150f40420031a040070040744c3c0c840d0502c40340e101c0d90050303600c0f601405500c0f0311000354030b841e00b000600004a111b0041000d400716150800c1d000051945984589004c2820b82e40301c029a4018030302e060045140a00c0015001c00e500d142c02c00c002d44c0760100c5030154207840d1140b01d00805400c1540414402c0502c1681a640e07048411900e50260000000704442402030400c80001d049140282055102007540000ca03500502e03d9400c1900341160b1070110311038514000c03c50766030342d5411005a00ea55001d072004019131800b4685a240031030024010060041c80c0b80000b6152004000c8610f40101c10f960b001608a5085100d583d40c51402e0b09451185412595003d1030240010a115901000e00c40c1624880c0090310b50b00c0c000110a50b070309000d140a82501069500006210045258014958280c0d02d1001040404001000c00c41c1a504801210300084c0009524000d50074950684 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805604289 1250 805603039 805603079
    0x270a060902070f0f060216031d0a1511100507050a03060f15050c15010f080f010515010c03030219080603010b18070c0327060f18060e061210 62
    0x198a0b000b0507584059508100d0305008142aa00030421302c14440070b6810754400000d00005240400707028203003c3c0000600601606010030003200a4405003010384a1030112560111515aa032207509015250503007414607604052080001c00303001c41442d40138440c010032994541695603519003400800b55406504405003141c003c3c071040103106401002428001120302d0700c280c42d9102018081c1c00c00c0d4402c1c0b4000c00d600c0b815400030039940055121282200d803884110340001010141180c00c0c1c6d80c040382c2c540301c444549079000441e07500540c0784e50901c52003031400514203580412508110000c0710760f1000018480002c0000c07a0409225141d069241140d026800d1043c498000ca55014020401801c00440e0078004041500880c100c1603920010098150724008110744c1b80410103652017047c0000d41d01c1c00c443d0f408640074651808200c03c1c42041040d8450a00a050f10481c1c11912110b801c803100300100c05800d180740d040980150304210070f10907620714041c1c0d501c0c0250051014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805605539 1250 805604289 805604291
    0x602040807120302061b19210b0328140109030e040905101109030105092b050403030327110102251e12110118060c0b06270a0609 57
    0x190501103600017840c0c0360310228200108882c0001d24815100034050300c505000030a403108100d207005078002084004071680c1035003403c2e52452241c0d80d0001d4542c2c05402d01d0b010b40042c250042c0100301405c400d2400e00440540141c03101d21503440c1191000d44840e2007110365903d107110820154042d500d8481740004481c1484024000e07124a41c031540c183c0c040122040d1f0b2401325501100c40c103000e4510f18400100208003500d07010300c8140d228490742d01080200d03a0800369441d0408002c0844220010150390781390300340b50840d078094000346140c83e14081e840080c4d501d203d040150b40301c440840d2900c40c0000c81003400140b07002901e08050710f00302500310f580e11042e41604c0b400000a400464284442d4100c01c504801c1e8100c503032139038a4001070310787c20701c00d09400203101d1100c212102210302039980c96907400280d503103030032a58114010200000d109102d050086990000d100341c01600040400c0c86503803004522000403080000c0840ca52a00b400821880310316911408005102441d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805606789 1250 805605539 805605569
    0xe0d050307080609150a120c0b0703080714160f03020709050606071502092d0117040219080f071a070809010c03090521060601020a0510090314070602040807 69
    0x71002e40001d8009104900480f200f130009480d00700920690440600090902c000103511509010210f01e49500c0c00d80d9529840d050000d4100341c840d0407548540c3e0150703292421525000c1c01141e861020f00c14031141e0100602c07465050707140d0074174a4102180f10340500020f42c0100d1401030300305080c130707031148140380e00d4502004041c0d2540b80840b46c1c01c90b0b000b40760364000340d48210050300900800440356040103d9040c08142c032450a801512400d804071180c0045d110328000441e08421140b0303141e28404072303800120300181400e250720030b925a040d00041c0b460944071082c20f46081e05260100103580c1c001c0c0e07000c0003040b80d9803e000e01040f40fa051502d01d0301456840d8081c2078480c000940341008600d95241c03040c180b01d070b02100d0251a000345000e665030f8441c502c28620f6501c41c000f540d514042d00c00072905a40c00041c40d1070116600c4000307000308160340014100104407a200c150240324410154900108003079005100d4288105001078131181858022803070000a03030800040e120030b20b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805608039 1250 805606789 805606801
    0x9060905070e011e020a080a090513111e09040903081e06240f0a020705040b061c05060103090b0a05040311031e09010318060b0f0a0b19020a150e0d0503 67
    0x205040f04504c441c0c40300740001002c0c050032403130401d03c40740107005018085a521f03051907200d400700781258011103090b52400350184c42081114541030861114000800420802403464070202c09004121340250342400000400301e402d87d4111901280059151410010510690340740b14035640e401081c0c041240c94510301284444407010340c0e161118540005282c84403a009040302c03c80703004030a58907207504c40d0400180d074440c01402201e00c1035041807000030080c1058400d5450341100715401c0f040400c0c40310303150001448060009070415448441c9200403074081000706000352204500040c841c90a400c0050440503500c905075165013040040f040d00190102000305c559003450502030b526003901c1c0040e8010215004480160f802c5500c0b18014885150f00441040d036050706c034000c41c92503240401811001501a980031200d0a200000380c552203045440041706260048800050340d540303030024a0a030a055542c12551a491072003081042030002085007409410901d0842c2420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805609289 1250 805608039 805608047
    0x406240503070902030c07020a031203110f1902010e07030b0901050114010f0809190b04060b041e02090f060c0304141c0f0201020a17091903110d0c0503010609060905070e01 76
    0x2502c144001031341c004c0003182111100c14201d40f00242d005002c2d104056903172401d5280e03a40380d100c41c400440d2038522882d9004502c0400c40da408050030810b60701d40001c44664820384000c0c454142d08540d40c4801081c0182400c01c00032010358060a9120b4061611121090070744405800000c40d044008181e00d80590b000425a400c1c40c0709070030030040958554145a250543e01c058030f1101240501d410010b208801c1e00b59030044d0302074101400075055807010310042d54103c008070302803a083d07500344080c0038060394040c20203880300800700e03010b0184603c0040c00c941c1211000050b95040010200681d41000f85018040d21059136984038402c40140c0117004941c1404024201c0010590058216031081c08050340f034580c0205a202990b07006400d4052136000021102c0c0241d0714160b170607040c511070610b40c40c1285c0c0d0103204112541072803028001841c40b00304046071900303ca00c002040b941d81c00c0c000d540107000941c50010f10249400c1281090b102c002e0015000e00c004410340b18440c2c1d80c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805610539 1250 805609289 805609303
    0xc0f030406050702060304140109080903010c0c0b13050c06030a06170d051b01090b1512160306020a050d0c0e040506180a05060f06211803160c0902030406240503 71
    0x1126017640340c0d5030360305224445d942505c1d0042440e51808605200700803146028080035081030b402004000d125034000c0c0e8510381949009006562600000303844000301101034400b1910078415950491031581c0482d40c4ca400541e0800e04540e1101428400c085241c03243d0414509040e0003455199440e203070140c424400c00b01e41442c40c1a21f08480401c50000350030034160786070f1054a8140501e400c941d60200d040303041503201d10031075218415040703002c7d000411580c01828000312459941c5155500e5000b588071880140a10409101031300e5511501d109082e400810368403009960880d506c03c010031100020302c00c6205603103210503440e601c924050300c13591121420304001541d40b90040041c4240d240d0391b164503440440080d440310000e040607103072a48025072464040c11a15004268000e15110303840a0455034000e018550300355a821540208480c0200c8110600c20f44606058069030310468017511801c0e10395002c041c0c4c1c00c0c40c1c0c20300603804200d0343e80c00189060912001a80b0741d28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805611789 1250 805610539 805610543
    0x4060c0809130906060902041a0702030f0d0c1a1302131e0f05090102030c12060a050a030b1005101403041e030206150616121110020c0f0304060507 65
    0x2044088040410440364200c40c81c0d2280100111900c0c202016150060320003001c040341c405050040000b0700041600960f41500c0750b140a42040148030881040350303400004040e80e0600c50b007500d0350000e5006200203e9240380f2943e6501000e20942010840c1c810044d14416142c1120b0042081804070050b1211440d5412502007108910448104010b002c00048100414103030b1081888402520f500c86070b611810540140321304d640d46403100b0300700c0c0411914000813003004c101c1d020100004000050340820014607400050ba1140082588000340390000c070390700d90706ca00c20f21552548056a000050004840001058484240042180c4803c40e0000c41c2c522000c00030408128010307014038500320000c5010442c80e845c1e820300964480054801041c00c00c42d003007004460f030816104685040d1004030055481041c00e549a242c0c0040f80400401000600503032251350300414400710312540d82040001d40c840e894240503d04242ca07103203080b00c041c0e104201c2000b400750400180e0f22141c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805613039 1250 805611789 805611797
    0xf08040312060510050c4312080309150c0a0f090503120a0912020f01050a02251401080f1503100606020102030118090201080a050a0e060c0903060c0f0406 68
    0x80309034941c001511103500704030303440200380e00c0303100c04c3c1c66108024044801c0060101c4418103900300d1001c5054202400e4200294495a0011581002d101c80b05441003424452100b0081e40d071001040f44144403e02107840c50300000500402c12020000940111710844841d280c9040600b40e110052140340040790500c42607892443c540750045c101c04006040c05020750722244000c400c1c655042d449070140704003044c913480000c210340e0755400c1507601490340500f0740f200301c034034071f400542d01c41e00705405010841c40b4620300c5400301482510003404448802d43c0c071022050506005100b04015070f02003d04100440042111003180207181c15044022050303d0303030080d080580802c3c140851110803100c841d061450014440341c0c1507000b54100d410428410035801504616182a1039030314030064001400030000c505000b07080c1d405103810000300000000c401410040e01811705200712142d4490b82000b280c44040b07810280070555015a89100051404408001c0c030000b602803400380300100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805614289 1250 805613039 805613057
    0x318080f0403211224080102031b0a020c0103090c0302120604050f0f030405040b060f03011707050d0201080628030308061f020a11180a020315100f0302031005040504120f0f080403 79
    0x95000d0301104940e41710071003905440c5940f50070750103010798410760301d1980450108604100c00004a810345401d41c25950142250001150045014141c0c002c0300382c0f0340022030318000005a680503010804c160b0078030050602860603040843c14081c9040c2d03007010300e4101a903070748084030020045070213540d0200c03000605090360201150a600441c01c0300343d085803002001080032000171000444850308a030854480540f940e080c0584a42410760007030100d96040d01048051411000003000120b0419807d01e140c2010300450040b9204d5900640100310741c5002d0002a040c4040d45085c9080b80c0744c4000804101054001e40e21400c81b44068000c0f000414101c4156842084400088407410800013590a048145c20000c0d8000e035011850349548521028a03402d00380403403011030100d512540c144031404003080c0c3c00303940001c2021900e92440300c80403410ba50786108542c01a80191040c4030820218040030b0f0404450108013010f111001e2301e1a200c00b85d002402e29400b0f41e03d403426440e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805615539 1250 805614289 805614311
    0x4060f090f050640030c05060909150d02041a01080c0309031b0a051e0c040c0f1107091404020909120706090302150106020303060a170d0318080f04032112 68
    0x1040030b0400d00d100314024121320f03c0c0248455030855030166070040c070441d419039a80e1005c2043c14400d82c0403864102c0003a10005222401d034082e03880590502900008812041e0b50005088072141440c4041c140600c0030242025680003554a034082210400c451840c2031a1003015500e0207410b0300c0080c440440c15404800315400c1c01882d0010354480121100c0340c0401900207040b03c8042040f9207c0d11400001c00054905406012500b01e4140c443d02e0440b00461402c46507055410356404441c8180440094840518494103081d000c1e042c0c803080342c1d42840d104000c0d507804080d200d0b89044e88442c80001c1400300c0385d0300702c94040b54081c00003d0001014901607040500800c1a90048402070000007a015004001140304070401c5851003541a00d0384900d0303008642200300070b281e661290b003100041501984c40001d036035802405080318546141d0b5940c4140d0300040180c092004041000c00401904520314800c84130b00d400c003210b19890200b40203154402c12140d9103803454903400100c0d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805616789 1250 805615539 805615597
    0x91003080f07080309030301060f0f1d1c0602031f0305100f0f020a020609010b030a0b18070f0611070b09181503011103041a011503020a050d0204060f090f0506 70
    0x8043d03400340b212030b100d1401609a0b45c4035002482003001041001c542007211603c0313100e06030251040d03034582100d0703200741030121234200c084c082445400040040446010f80b1448129003805403080c007015aa03442d12101041d0751071500c03002480d0343c181e01d8009000184000c00c1d01c0000045070000043c0403108802c442014099440482c01e403d4800244c0302e10440c3e0100303c92707200e41c3c040c0f0000d00142040b401403595a9411342005002004040040341d1009003500d1519040c0ea40c440884120a45404d130880c02200154020000b1415204011030600810b01c1510020b21107081e00b039040c03620803400f01c1c44407100c4010f110a0f2904000010300700c2c1c130803464015550480078000b00724101c1a03a0a59600391300907101501e501c0e10074140201c0401040c01f5036816a140596025041000b059003540030390000103442d010711009008034030f20f02c0c3c0c01d4030190004040668034204500040c110281c000c0d0055004040040b0682d0414015500d44000302c600c0c00c40d901601c1c0e940c000200c45048 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805618039 1250 805616789 805616797
    0x901060906300f0605060313020103020904020c03120405060109050c030609042f0906030703050c060705101503021f051804090515010e09010506100309020d05100f0605091003080f 79
    0x1800d00d5081016039800b54a05a0000c0c1c1002c2e044642003000715121810001c02e0b0004850b070010200d150890800107500c6500600102e4502800150030400ba09501c5d41c2190400c0100e140038200c003c0400007030180070021140100881c40d000c0006040959021400703200003011140101641e40c00b207400c200c869060401c085420281491a480780306505076010900041d40078410110000810700e00d01c4c001c50b030380040380c0d03002005181c241e841200b070020075040300c0f000350340d81e0040681c0b00f0619840c5000340466000781000344ec0d41113045104000c6049907084151050159480142844540000403070b5501e010f4110020b803c1400e20740050080d050082c0010920b000d400c4902c0003240708803016074107890000a041d501581c42d0250701d03003262012900217034050085031301290903d020b544506a404d0010b4580e101c1c9801e02d484035480d04886004420030f0a641d145a070040f19018414400601001c56201d403190901c1242da40b000d000e980000b601031480002e014888140c40d074121 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805619289 1250 805618039 805618097
    0xc0304030314070c15030c02190f03050d020c011e0207020f010e030a14030703020f06070c03031d19020a06020c01020718140103140c010516201903020f0901060906 72
    0x11070209444080c900500380291602c00c0100b8245008940ea40740046940c02074841407107801c041e21049e42d101c403417075080e407010160103001d030400202e00f920280e4001080303132080000001c50314615040e0f40c0540c01c000410000e0006206115030301c01603680188110304000c091800d035040c070541d0750002e403c000704880c0051560316898821001d00d0804009414040d0203030b025544200ba00c02c44082e100c201c22101080000d40044c0b400c400203002c0c1e031261a0700c2d603a0803024401310036401d840c28680007104860864940c1c01d90514400c41c6060000b03940038040f0351014012249072200041e50760107550040890600d216090960068940c0d4040c1d103604541085550039565039003407a0f110228000403070b0320035020f8503042c3c0a8a50140044410203030304000b0551001250f5181e4041d0080c81031022100324580c90a6441181e0300c003109484481094880843c030030345903104100030101814601341c05200000010011650014000011241181041d800008800103070f40781240480c500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805620539 1250 805619289 805619303
    0x50c12060f090c0d200904080d05040f0606030b060a08120f03091603080d060605090f0d0f02090c040f0e09061f050607080307030513080a1107090609020a0906050c030403031407 78
    0x202007417145102484035510000b46039015003940c2001407240e0410100c030050480f03401004651200c101030f5020941c0708d030144050142c11003c03a644c0ba800d46045510590320b26040b01c0c1448820301c2c00d5500107006100e803000809060f45400d80302c2ea03c1d0300940045074264031000c80000c4022505000001c0d01c03080f01d0041213003c40c0c80307207000f03406600010600341c2d00525215011803000d00540450300e400000820356142803440e030302009445040340300c08480d070100302d200c0280161580081e0078016045104101d44413070134100320640c00c2029038071a03010b0003802418400100008039080f500b1182c02041220300c02c0d002030320072900141e542d200540281c2d001442009004201c1c1c0a103018803a665024061920b03042e0480e089030751140000f8100c03020401502d080f0500440c04002c94134800030595400f01d58940c3ca83e400c0706d0a82e4410725402d500010440325440d4004000780203809141002424003401082d0140c2e64011408020140600304080514555031070701a111810741c0080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805621789 1250 805620539 805620559
    0xf040906021309290d0b09030717090102190b040308060d0c0603050a0e0604111002161502010e060c07112e020d051606150b0c0a050c12060f090c 64
    0x4058402850b850100d80c1303a014000100300c00d00c00058082c0044030ba001000403d000c0d1090302c640c942003c000c2c0034042544020024000003030488101048004a6042083d85840301c4c1ba002900340301c28121429000c038042008400081c0344088600d030815018501400990703201400700f803400c9100c11024243c422002c0b0002115585078114a00c40c0720148001d01504601003070386a9100c00555000304000121110040d03242480c40d10190441f61610440d402582e06092104d428134040d00300070464550000342c0c900300da409000c1c59040c25986030041c5082c0c0707004549403066003e01c460040074040d5090081c900c507903540070900314002c4008948483d1030502c51007030b01101030303014030240540124a10300032000c0c003820650310903254000105075224901d9850034003c0c245000741100920300141c000c91015041c0004d07294400d003e40c0106a103003054244540b8040030b59010310710030490fa1901c9138400c0ba01040c00c94110b00b41c050444116140d010440b424810507100c0642c000f10459 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805623039 1250 805621789 805621799
    0x20306040f0c0b092206090c050d061508150301020708030f090708030c0d081b0a020d1101111204050c1e120f07030219030203060114011d0f0409060213 67
    0x1503078034a96188580307982d000c0141d483c14041801e004600c0300030b0f403090004a20144899550201c04084020f03110009000c5841d03a14540c22900114100c40000d140071030400d0351700006100707400280904a00d194081018030000030010b1400034140340c480105558144c090385c8094060f2502241e00a42c5039850789032550f03450452400848840300300344a00840082c1c00400402150051018000070700030b2100d494800b641c540c4400f51161000a50395007006c030074003081c003026111604069000c0c250101c944440108450110b581c059078592411000c000b8012654045034420f01024035070a803140d03594100182000340c01203900c1c1d0810108000c1100a1f11607001e55800e8100031500c150000110003203a940d40c24000c0f800202540c0802010b1000d0700c0c14a219021240c0025420800780d500c07540441c1c1444000e9214140fa503150700c0ca00001c940c1c009900041c1682c804984c0c04400b8a500d00281e140c2c241c040485000f943d95159072028440359404032010103c2807001014165614 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805624289 1250 805623039 805623053
    0xf0f01050a0203370905060315031903021c1b060515030109030905030d0c080313170c01090605090c0d060b0f0312040812070c0902250c0317040e1b0702030604 70
    0x301c03005142004c58912401d6180d8043c0000d03c0642e040a42410300b99929080c0100043c48803050070f03545031152403080380004000c03000c00d5032103d00c00d038007401139013084450040d06162244025014491081184002068a180072280e0300780c0026000c1941d0b2640c061002d1300e0f0708061009034140d424901c03100c080c180c00100e030b070045900c00c3d003c44d444640380c180d040307400310115600186002001c201060806a181000d403580502520701070310380d01c00f4000055610b6022402c0d4941ca030b5125680700c014802d1078803425901003000406014001d000c070000844c00012840c00500c0d0b544d4032135170300d0b0381031301d400c1c60302e6107051006400c690108109660b0b8181a03003040c03180c4101d601c543c00c0f501c3c11400420342030302c05441d48110401035090600d95044044c0d00400800d1a04a07036200c000c4400d101000c064051840c003440ba002c000c0307030031750400000d007034038418406121078020802000b00488520303200b5444690003561154298900000170518403401304060360501c17580081c8410700440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805625539 1250 805624289 805624357
    0x1404030b16020d0311040312031506080901050709060c032d090e060303090117040f171206010f05090409230601080d0306060e01080402041b030b03010b0f0f01050a0203 74
    0x319000c4520b50140410110183c07000100f17010402c1c9000d00003000001d1400d25034500e07510880c10f000c0703800d078040300703041214803280d512800025014406012950300b0a204007500440a460130001c1603051400141c4500c2c44503170000c0400250780e18200a2a00822510f034400b06402038034001c11945400040c856821170280481e09484880894018074000041710030350241030310344e114001034058415000150040003515105058420b4a0020b00c0d80005000c4000c40d600e069a1500ca940340e20203803c59004000364180310340c445407001301503000300540d2180c20080300c001c91108828034004416444903416030716000c440c41d0500c28902c10105016050328006d10882d40c400c10445000c800b5a1140e22420010508c40740150405500c85d184166209002030b10100c0d040c10344240200b0401248250140025a075121700f401c4ca103028041d00182c04000c03181d20f800c0300007800000d170342045801c00c00ca042c400d00080c1c4085950081c41514007541c2c100441d16403c00064200f2480204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805626789 1250 805625539 805625581
    0xf080d020f0105010e0402010c110d0c0312080c0405040e070302040c03091703070801090b03010b1201020a03061707171203010305010c0906081b0c010b030f07050a1a0702011404030b 80
    0x148490182000c01e051280a049907404945d10002e600d50340c0040d605051400f201390b403000c1d048641d4501c3c645405030080111032150141b6502e4034690b003048610022011044801c110095040c4a600305228040c0c40a4881c1241d0006540c0700c0101a9480d020140c3d100a40290030240701240140d01540705d07044460080915185001c05075509904900c01180d0807004916910300503c50700380340b0f40c0440880c140c0034000007201002c0100140159160019074106a034002412008840c0d060058000a0040f22840c0c040c80045c9031841e07446002501034442c01d0001450a4180b010040140e40c8000c10040300e031a40c1e03035849080c11030280a1011500c000b080c0440e9000a0441c0308030300b011300c01c01d20002000b00d02d001d81510440c5643c0902c00c0300e0450b64903821080c1c0160303014000c0f042d09205180040a8140c581824020348a80d2a4440b04400da240700080950f42d0f0300d00c041381c3c00d1aa092030702c030185042100320300725035001c0d0307800c042c008280e900104012815594100a4000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805628039 1250 805626789 805626793
    0x20904060b0310152a0519120e0a140312030411030606090c07031107150503011505070b0f06040f05070507020103050f0702120304082206181d0405070f080d02 70
    0x25140c480c1c0c841c80400d0703c0140c0000501940a150b0606141101700301140c1003040c40e0320001110780c070340e24034002d580c1c101c81002848045495040213409001460041c1c05030170200031186041e000a10010100e2040e0708511155840d91484c2d0340c0c0c01d0040450911682401503100d00b040d081c81e2180c4048800c0484c000c3c450040400d1036490b11614013840f50002c1c450f811b107880143d690071a80f51503c00010743c0c40703205501000c02e200481710312400c0f4a10003135071669125850400f200003074410440710f030b006000040042c0b0780401c42080c0110340c0802116503100040e122880844d0040c5483e0120508a600d40402e01214a90040003482c0c1d080c000d070b07414000c40c0c681c0d40d52905181425101c1d0005a44603c03d00c010141d82e06001c0d50b840f0307004444032410b004041c0303c070892405c041e4280d09030f4009404414041d054002c1180c40c03030780360410b001c0d131900e0781002c0084203518040b503142c2c1425441000007504100d400c11290020b4010403240c094181e40d2050510398038104003030284058 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805629289 1250 805628039 805628071
    0x2102150c07020d060c0306031e06050f100b0c1207061406090f0105100201020705010c0906230a050c010f0f0c030b0d11060325050706050a0209130f020904060b03 71
    0xd00d5200050325032182c0c000380003800a8450b95110302c010316650304400c05040c2c42e0b00d00000403505420103e11080c508011801c802e495034070780030301204c9000303044441031710b515021b000304a04e0103c030a03805d4502c0307191043d54030080c070000940b80045801e01c000c0c0c1680300298131010800d50f50850052080c0d03145003c2d089441c0c66040042d030010850300200940390a000402051400f4424043c0e0254a40001468100305440e40c07402e5039101600e083c08207801c401c041049940c061b000e01d000c41c0b000c560350b120780c0700c0c080d401000d60f00c43c0d034888004104020510032046072007980301d0424540d00f640c003004045000c2c403480c0041c080080035080401d19200d844802414400900c0c1e03e041d40c404024142800c203d000c0103130942024141c01c54443d08103440900c064003005c3c0007040c00030503454140e1168028500b0005845000b40085401c0c1d005015411a43e22040803071080445801d1000c12583c44018440d8000e0148001c0b0301d500c2420700b00d0004000864000860042c004140f041100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805630539 1250 805629289 805629301
    0xd1101020306030d211d0c030a050303070e120f150702070b04090f090b240d054204060b041107080f0909040602130608090a0f210215 59
    0x201d0004031826601500400079008005100d03660404400460000307100200030800c0e0f12804803140d02d03200108101c1083c0d00c408904108100030211410220010400843c03566201900d80c000a07016500b405079000d5802503556031004c090703510300300a2048506903803c0c00d102e90b80e40c82008800303100c0000e200020a00991002c1440c60035644404800ca00d030502c3e00300414004d0222141564600766541100c10000d4100340900303011b851002c0800413940c0e0f90600705001c0c1c200180d401c1d84541001010900003880205961080340b02091566454a026200c0c40c0800c8a0240c140d8040e111070428140c0740807440d03204030740140e01404081001003070800502088032045500071070400420701800b40051000700040441c100440012803c02940901240b00000291030803101e058001ca00044640f81380f1889400502d05481c2907011410080207580d2500d035400406800c1000c10f100c0403007880310700580042c03010b41964803000c5086180800944079100c14010881c0c0014010120311 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805631789 1250 805630539 805630541
    0x409111026090709021b06011d190e030307111011030f0703060b0708030a050a060f051512040506070f020319050c010f0515031603110f01140c0d1101 66
    0xd4540003040903041010311070210703101034003401080e07040c5510540501040e203800071300251940b5032640e40741e60071614840074560b0601d030050704040090310511b004000c40411068a5903007048245883c030b070340f540814071554090540c4140003030f1540f200005000640d580004008482d015240c00e0300c00c3c0b5000c1e03581c5101503c002141c1c03950301120500109101340000f103800c68100e401c80c1800940d5550b62281d581207070704842c1003500c110502004002503207a5074001c07070354811241401040b0090922900c480001c885002e0180034044e421109611480150101d4454055804080d4074501c2e040c54400e6550004580701c80004400d5140c524180d0b00000c1554907001c40f00402403607010750450100d9040c5c00200000910750f403034129030141d50000e481903078020314022450b00d040760201e206040ca814001061114050513550080000c14080c44d4620226002210300707840b108003d100494070f46c0190b103448020285c000865100b44140060090002031940d1905e82d4024086034540d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805633039 1250 805631789 805631807
    0x510110c030a110712120306150903060c11060c0406200d0806131401150504080c06071a180105060d0b040f0c0f06020102041701270201050904091110 66
    0x462a5000b400300c110010701840c010b00c181c00400085800a541e07031510b60005440828090b03035400d40000c141c00300d036035150007003001800aa9805441c40c2141d9003005101000c0f502c40500f44903500e002030810307980300e0280c0d01d0000c8070000c11a803a40c14140130346070983c0d1181c442c1e0700c08248007002e59600c5a05501040d030942d09030501510090b4040302059034901001000c46a00141c012081e40004202e88aa109100301007000e8004030740c1010803000c0c01042108050040c86010f00c010403515200258008a01000741d070300c00e03101c035110b20740034044511f00d074120308215208000700126000110901c400e90f00810740244610f4580380709001c0245d8403418041c00c1d8003481000a4040b42481482d0241640b04010039402d00780d648040d221180c0340740d040540142d400050401255010211910440340350600030001000040d070701038003404035030303070700740d220f100170984840941e03002e40282c410700308010b8401d00030508a40f41c50b4070980c0b40100490301c1040c1e51000010301c240b150f1555 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805634289 1250 805633039 805633057
    0x1050906091308070614040309080f120f040b03010e0a180210080403120608030405090a2c0703150608060912180d150509070e06030705060306010c0c03051011 70
    0x156000e03100c2c0c00031011041c1c1c0c007100c19107245000b000181c0c00110a0311035206a080340c51044007190130300707240040140c2041c1c0d0141d005980300507180800f94002041c0c42000140b030310703880c1d0fa80700d440b15031108550144d44d2104005181c0400005203032583c1c0c011452045410b808200800d617040b0a511900580031080603400c01100c0b503d05010754000c209054000d4040d05044000144a4203410282c8039680c1103402c45400209041140e4241703000415044203201c0002d0019088020b081d144010302a200710b010312514003040001c0034020f0060398040e582110320b962a031103000f29000d01900e01ca00c0360200500c03c603400542e83c4c14011429151040810b4600c51a101c846151406058010000558000303c0b1542c13000000e0031310400d1b000041c41d46480420341e80340640d000e40c14000d80342d1085889c480440c00f00b00071942c0200e40341040d90b0080303038000e449849240040300c02d041c1644008012004490000c824001e000600c0300ea030719201c400c24050075803500e0103034040d4000c0c0008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805635539 1250 805634289 805634299
    0x20d0f1212020a0206270709020415030902100c0f0602040b13150f0e03010204180b0f0111070e0a0216030c1704030b040803040212030315090c16141c020c0901050906 73
    0x104445140c40000503083c445035000c6c1e07280c0c1c510004a090300380a2135501c100342050f80081c0810a840c0c0511400c443c035005400c08004d0f594460300495400c001880c801810030101c2c81c1d10340b00f0010b400e001c0342c50054019a0031500d075a183c03c50b90605a0040307084802060407000c00141907030f0200e950a404403880c0d50f4828850818440c25680c040c04038040c503525540074800402c00300070028003c0000007201c0404503407201c030502440b10b50800ea054080c10000411650f216074400001c068003210340540481001c1c2d5207212511000b401071505000c03d0b0080c280d520340170b01d0780c0803131185266070041049014131030040c1d860349000c0c8114400140407468136000600820040f03005150b01c98000740181d5072000818003001c3c00d560044940d0403200005001060740713400c0a044070f0b58041000f030341e601d1030f0607003030182100c0c04001100c0051012440b59120394201c0303001d0000b254412901000855448030f038000107511080140240e80c0905a030800014151602450141c003589000e0b02e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805636789 1250 805635539 805635541
    0x1406180c0d05010204321203040e04050703121101050a02161b0801050408070506010e1504090203011517250302011211030a0b0102101512020d0f1212020a0206 70
    0x240141e1103180d070019241c40d5800d010001d00c102e01000441c0b034010440d07080041518a00100031052401196441d0080768012070703100c4d015400004541c161034008e05200b00e20703611450114500341e01c9410007801c811900b80c0c8a54060740021000280c01e180d24000d0006607101e802c040308074024102ca00008484041100c00401e00742e0034815024000c4001d1500d00341e40381e007034860945400b80d50890b00030100255440c14040c0c140312443c05860640d46c102a1401d000700d0001514591000d00307849a81e650f0380100445d40e003548400394401e45024005d80e00b03541c81600310914030700100c038000b40d401040c0003000c0011101002d000300300034180035074074424210b4004581807100162400c007000e6413129011304a942d034001951042c0d481c081c0100d50780122100090605150703282109410f804c2481c039070040141403083c0e01c2903e50300000a0207405d520300000b41001c080030b8010300398241c1c141c901400d10a44244110701104551942240003c603100260202d01c05c3c00460401138020b04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805638039 1250 805636789 805636813
    0xe16090e0d020d0f090f06080709170a020913060507050307020d0c050d0807051303080706270b090a060509030706050705070302031911030c07061d0f040b04020c0a140618 75
    0x7210200405261605e4100d0680fa890461411403058005202103480b01c01000071090340200020060300780e024074581c00e034040006059907261f103410000c1c810a4600700007030500a8214111014540020081c065418040c0b805007090b40f0035660039005000704800d84003518018003240010a0744131004044044071003c003124a450064006410881c0c00c01c041c1400301d0301c9808100c06540a0040b055484020b46440c3c000c4440c106600c0b12203d411201204079075400e0380c80c1e014003c0d04809145c0442d90344005103810f0a48409000703141e186010140800240b000015282c5144201c100300300d81d03100c28200360790b00d004044004005034020000c1130051107044001e41e10441c2d0b43d00340741c646c01d0315200406046410100da0032205500a0300108220b687c00580f044075000340c00d0300b803004074020340c02150908a80e540e10f03a004a03200e0080400300c3e116513044034811590307041502c14901492410080c62100c004a4050500c102c8001c11a42044030510b01c648111742070040428403002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805639289 1250 805638039 805638047
    0x204050402120f0705040525030b0609032406120615030a0c030819050405010906051c020301170601061e0315050301061d0a020c1f0e16090e0d020d 65
    0x10300c1240c0140707014480c202000c008000c05041600d484010b016000d0812003804101d8000400501e00d2405a25507201c2404a80500b80707822030300b070b190208551003800040f5a980c413500604541610846100c8440d030540c421000814104d1380b405101141c070741e2800c20100d5000100c0404103074200d48045440e801a0003015991140082c060b00c142032400d44a252002d542580700303440d0030f40300160b042e54008088490507c0d100720341c102a0301f02070a01340001c00060181c0610024807100244891040c2c0091040242c0c202c0c10b01402d55403980c69070300d01904025452884040340c8151400441d040e03000c0d1034801d1401c2c0001a0305140b690340b401d4224007800301603070005100c620000c4c4c0881c8984085c0601c001808007695801195001a200000d800c20b0007400e1801051040c459403109800104804441d500c24540750488040052905401004a01061041407140d102c901482c01d40380d400100071a54420810800311500b00340c550b84444204c0202c00050b0440342c02c1c3c205080c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 805640539 1250 805639289 805639291
    0x70807060f120b040515030115080d0f02010f0203091e0304050108130602190f02070b1c0c02070f03120825110c030313140d050c150f070303050106030e0c0a03020405 73
    0xa03030705010607003040f16404079040b11000e5415981e81d03500030030038000d1802c0034041c0b41948810aa0b41c00c06251401c41116100e0081303200c89000c2050841441103000d00c00d4000f681c900b12001402c56490a01d0b2140c2070b034032a0141c61082c482e03070283d803190003a140d01006880031114180c540c9e100755624881e4400284880030012140c080e820700000c0109641e60465000619003034a488900120a00029203003801a034051080c1c038004020340200320304030300300005204118032408550496040001d9040c0b8055410484103074540440c00401c1c401424207449100440b0344400c0c0054480d00500003140c00d48860341030505401403289540c85116107032210140d13040006565010003074400190540c2d02c200c020194091000000744500c80c611008002c020303100326070b003450300c03a800d50750306440705400c000301172246016944100c103000031141100c2500c3e90182110341ea8614038a00980203280a000350400a4506016034105c0140000d249102c02c400404d03040150380366500300005810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 805641789 1250 805640539 805640567
    0xf070f020622051c030c0818090a02070c050103060b1801030f02040902031005101211070b071709010b030a080d110705030301090b0f01080402010e0109080d020a05070807060f 77
    0x190400c00440001c0b8601000a64000c00b8007441c07498500e04001c2007921807102070840416802d071000d40300040d40044070301c3c65a40e8420400b40e00c07010000210040840150040b03038201001e10200050070022f6402400402e11a8000410168403035004504441050042510f100000c20164081c60780040084801910515002c10145100701c081411b07078209502c0a192141c0100611442c01004100c0d080075100948408240c881c400c2c0005046801d4110440070b071591319040780f807115200104990b00d568020320030190300c0c00d044030700a007081c400901d40c469180031302c0c010600c1c115040c080c90131070010003001040c040c41e2949421400d540800414560030ba61403500b8040d0307503200c00292454074010f01c081d645a40c9401c0004080c0d81410202901c14901e01860075816a040f1801e01e400c1a020318000100815010050700d82e10741940207846184902c14201c903000b68000b0b0a590440d00c5101074030001540c8181941d0b0700c3e100e9001d1003010031a6000e0304083c5903c0b0b00d45003414a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 805643039 1250 805641789 805641799
    0x14061e040f060e070902120a020f030c0705010e0109080901020d021507110a050a121b1502030603100f0b0a050105040b0306090603120307080f091506010302030c04031b09110f070f02 80
    0x448850f0542c40c122081c2d201030025038001c10340030100703c0305244c81c0707520004005065240001510603100c4c64400209002c001c4000454080144003095104a0f156070040008014a40d50b40c180814603401068445006204140c0a8008030b440030a20b103241c1c3d00889a0b880c4c09850741c0324142c03203004081140400c02e1091005050101c0e80c104171000c0900e004074a101c0070b4401d04140205103190041260f820742c400480002d000071035155070040311b040c82c040016120f03207030700780001e00f0200040b0710102100c0c10071140c801c80340d00b5036000c0d5000120071507002405540d02d1006544500881c07003494410003061001072170306d050070903210360700c80c40c01001e43c0c54000d59090103200b81d030004d440d008002051442003000100740c0c5080a50050100d00051402c08034400d4020f940010090905041540110101c1c0c204c00c3c40c881a9000383d944050a1924840c2e405001442c00c2043d108070303075545051010325803941c94020700300d83c103080300e00c22461b03e060002e40b83c1902c01d13260305030f00300d0b040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 805644289 1250 805643039 805643051
    0x30f241003090803010e09060c0a020a0b0a0207020607121d0901170c101107320a120302010506130c1b03050d0c0c030905030102090d0b040204060503010914061e040f06 74
    0x295040f0001d601030300d001c440e5924203050424505103050030042050302312480c20400040030b25000180b100b6803d60020380e10b80c066480740e8009002c0d0042c550025080700c804a0880c04110111003003d00d00030a0765108a004010015140001310241c3c2c000342d000694040140140744802c04a50640700a075000c68841c01c0c028408100307002810400340c0b00180070f6910030128428180300b00b0004003243c001041d480075103408540150a01d801d540940c1e10a00c01c0300b41301035110054100010110704101d0001c01d11503050290190600b1510184200e00c074040b4105060801e00c102c20309541709960381c000b5500b20428401e400802c400d8143c05004091100c0c50341d2030f5140c000c0d1040000325584d0000d96980307602d00504400c01c039400c41840703a401440103c1494039051010256103410032000d484d60b03262400440c0003403006800680e019400d001c3c1d000d0a004102c5070145000844008469a076914240c0d042d507089050340c9005410850040842e0200e1140040301400c01d00a440000351 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 805645539 1250 805644289 805644293
    0x903030708070503040f0f0b040e1008030c0c030114040812130507060c021819090c0e010303020303010f1505090111102c0606101b0611030f24100309 66
    0x540c02c6580c0446071540002002c1c810901c980c40c0440050501c1d94107201d03100c1c1040e58084040c0906d004401e40324002200052040094250140c001c0001e8002e4980d908125407005e44c4800350441f080c1c0c000e40c24051004c14174101c0c05005845a60015601030400c1408401000500310181c80c008103c841c084a5030b01040e8244030920040c00682c560344c0070700d500e43c4180201500030100300d06e1900c5800c410400541101d07038594180104400c0005140641c62801810105054005140f0301030400004020150004001d50590351a4545268400e41c0d62221104600c0319585440016000b0b0040001c10750140340036841840790f54054440d00012411000c080b96001c150385030b0031080141c00c00c0750688200c2c0d00526005400b0300904010700d0600301203021140400511000c000c100201a40c0303154985440038200780d070200c5d0038480c050f4542000307003464005407805000c0800c01d4010414107001500f442c0c1420910703815000a404040c2c1c10412000c8002000310b00b85034543ca40307880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 805646789 1250 805645539 805645553
    0xe0c240333090603032a0a06060306020919030f020402030c07080c1b010c0302151e07020303060f01030905062a07061a12031207020709020315010e0102061b09030307 73
    0x91020381e00d04854050281540c10401c4020700540a18000d401c1002144110003c405000d98041d00e0309400c01881c840d207640c01381ca072162420010f0011442c00b0004400c2240380d8000b0054502d0441c0c1050082540c500031018414092100030f000c841140c01120050401c2e802a662182040416a04006090703c64080603800f442c01419260043e5040792280b510720180c01d5910003080c81c09881000f00355402a40d00c60b000100f4250050f8520005240669140440c103010740c040d42043d0f21908080c1006541c030f400548000b0700c01c1c180e0694241c1117522070320400103a80d0700000107240c02d454202d405c0c03100c00c0483c28000100d59282001c000d408030440001e00d401c80c410700c1c7c0091811034000039100010855050107104206c80011401c4d22407000040d1000014240445030181d187d1a030103a00d8080300380d1068100c40e001008104403d20740c004107140b001c6081e240d100310706103850012030310f03140210b0f01d02c0502c01c40708041140d03211441016100010020303040302e00d80841134039002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 805648039 1250 805646789 805646851
    0xc0102060f1b3106110c04020702040e190302060108031903090c0305060c07020f030a02030a150f0510050102100b060d020f12010f05100305070f050a021f0e0c2403 72
    0x1e1002204010a400014100002e005100c10329011950705e96071074080d42c4038030707000d40740c0d41c869900440c010082d5a6035601c440542101e0350700700c4021900048400070b0042c5c0ca1402600913000b4000002480d0745e0100c102c07a5800c80c0c0f54103c1c3c900d528501801c0d070081010078411b64280e403a585000c00010010417507d4002d80d0b1140020740c89005500c1007000d606901c0c109580250001220340d00140ca000038043c00302e07940290108070403090700599500904004d4810641c280c2858184481d0341910055181901d2080c2e0a542080c02c003c542030302564060700d02c0c039420050401c006030680b100c5031b002e04910340e05410300d98500742c1c0b861803201501d1000c0e00503002044c0356140c10005d41c50401d0181c8001c80e4182000d00103032400d00809007601c1c103009018404e100c800540807400d01d00c20300803444a03880c1620442e800107802025413004280c2800780748543d108046000809240500c100c4c12412645c242e0036101c00a00011454140c00141c8600800292280c0d4165210b40d07102d090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 805649289 1250 805648039 805648087
    0x203120f19290d08180d0516090c1805060d1103360601050d060603080d1b02121603030b061c2009210a0b010302030c0102060f1b 57
    0x607240c03401c8040c03201e40700085188800e034402d03a80b10003500c000940c02805d45403100301c444003140107001d1610203daa52042c414000b0103d014250440142d41d81d07004903101547c510000401c0103414442c0d080d0b4038507207201d404103442c1c40c42850401c054a403080040c00952046900400d10b40d0b03000c402e80301c4a4009a0320b10315013842c510311100400d040c2003840d0b80028030b00c0560600f80314484820340c0d100d80060003480c1c000c04000040d4810b00505401105c0190340c0400d540741c2d19a1104881302c01000c120002e00082c20801072651800ca02c00184e000440d00c5070030b615440c00c007c2c40051059052100350403000d05071074050003005d6680e1036019007035000b01140c4446543c145004181c2c202c4d070160500b03410f52006418100d043c218400166680d1160945880d031310032110180d40310521020292000741841440c1c50141000164584281220b100742c04070f604000214006a0f110305040361a01d1221300d803880081d0741c252340118082030001400c0316880c6890403000703054089500c13510324 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 805650539 1250 805649289 805649321
    0x10c141206031f0516020a080414061c0c03060e07120b0f09010b03041502040b070201230406030609060801020711011d1f020d092105011118100203120f19 68
    0xc12505d0101c903c04260b4081651014011a503031643da0b04042d4082c5009007c52560030840303940d4603880c0e00b0304450001c0090b100c400e00c0780029015540c06494049a4800024205440001c0c915648842140076450b20f0302d48154608180c4a460020424900c00c00d07800316010501d2070041d12004802d50181c1089180305540c0d00c2c1c02d080039124503041302006010244104403c10132510990265802994246000c8201c0718015180001c0090108150401030341d000400003460760705a8040e404644482c1000e0100e150360b00e00a42c200c1c09483d1002d812640107071600b415a40c8030f0b03401364003000020900722280e07403500c40c04611007035151782d601c2c084950044070701c1c110583c041001d554442c52900c1c003401e407070381800c03040150340351000c516171042048807020000f0040290040a4826407084005445800b05400c2d04103012141040a002c0c0b0354203000d0414007807011044801ca2101020740c001c103510b03502c50010715180300910010f0309441403401c40f0b2540c980d6009a2070000102c1038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 805651789 1250 805650539 805650541
    0x3080708040e070c02090c09030307061b14090609190801020d0f0f0e0d080712020721020703080403152706050c0a021f020712030905010c141206031f05 67
    0x68042d2000060000000d22240004e0140140e5840360800da00c00040d03540c0342e444401d4035020038038500440d0001007070681004000502c0441d00780c803051303541c281c0e40d4848004050092120100e0300c5407075000c9800003002c0024882c41c0c201051808030540e50984180089030b502c00009003260086404981c0c1c0907141c40085070358010900451081d548131100803c40640c2800031030742e07121482c01000090010043c0044d400d0350180c040000d00d0700c01d0140941d5503001c0c624103c40b071005503d4410030603810401c16902d0751440000c894050b6940945113034a0b150840d20303410900740e081100c24038000d03100c1c484100640c00c200101da524011810003592088258900030080c0c036401015821034810522004600316400101d80300400f030740d003450310b10f50700b415100c10019100d5018040e01031803284030102125940340d070189100030b008000030800e490103410f00320b0703031030150380e039061030410003072026400d0301c6100a10107820010040859101c4440f000403409600b10307140c1e0a2408503a034034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 805653039 1250 805651789 805651799
    0x1260c210a0b0a0b120703020d150f0f060c110d0f0f050c040203090a030c0f0b04050f01060f0f0b09131a0a0b0c06010e1b040e150420130308070804 65
    0x200805100b2081128030f44809400d050301c0d000d2074024003030512480c6120350b0102d40b20300c6c0240c0c1240c401e049480170500c021550340d40c8035610298148184940c1e028501e1000034100c0140e000f80040e03c40c5681d0301d40c8490300e50307200c403006211103604003540075041681940003d501940c040d04036034401c00c100a0003071094100207091a24200009025030300401c20060a05400b10301c0c074640f1941401d003a0002c071041e00f8100d10b2102d6210340100b6402843e800d00040c410000748a4507443d46001c000e2000c075440309010050b0070100e200d1807080d80c101c03400510030000070602030700401801421115290365008008410388a014071603483c046001940910310b401d0034038028005d0103801c06880d15226003980040d555000501c45c0300384680100011030f03c42102c241e03103610b0b0494080f980c50749440d1036003504801c541094942e103502c001000c8210a080c1014000c2d0030340f400e501c40c0918454400692101e0081e030044e000414120080900480020140750251261074059804a03403518240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 805654289 1250 805653039 805653041
    0x6010e10270b180106270618060c0507030803091c0e0418020a0312020f0d080a060e131101030b040f0203010807050616030f120507110c01260c210a 65
    0x780d034040340030704142c04400310f291410a0780035044504c0d42c51310202000c21402111240c403c03180300114680806c03035000500d04c5c5e0152104403420600c448a0080ca035541c0c0007960784a228032002403840d04600030410104d030007007024590000c010390070f484a0007004ac0e5040218190000c1a4001c14866221425182454403070b48074030903440e20003081100b8042e000a4a403181c40c2c403000703040000314811000603a2007800500130104414003268010258100c0c09402e48004580040b843d41c0380c00d000040324801017a41d00d000c0d440308040c10f0901100781d114210803003111034005040c9512070143c108242c44921a00c1440800740c0380040e1694180f144840c24840e150740b0242c4619800d0144a42c03040c013202d80000d5580d4541020800d80d440342d4415031b1404004140030314124500410495030f1070300b0a4081c40d1019904007650302808020005440d0b4642804c490b030088503140a52440b255201c80c140c94101083c0140c5500b484a80ea8410306102c480c4500345ca80c80080d402408918005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 805655539 1250 805654289 805654301
    0x30c041d01030c270c0306080a030c1101030b06070b101a03010f0f2105101409010509010e030405041107060c0f0207140609010807030905010c021b1206010e1027 71
    0x1148102c9400b504c02070780b00d04035180d0380ea92815140303694509020a0394003d50002006129007001d0b5802e010032410060070300e11202ca405d40d6060b0601540c005d243d840780c0700e0140c802d24000c100e0707810a00192079403000d07814020a040b0403001c9190b004107403541441411120070a00b840116074943c10821248001da1441e8044482221000740c140180c280180d642c4008a112160110392100c2c83c0c01c2103860261540f070b003039880c1c1e85040c030f0410005410f40b524912641100009000c103403140d00c1561700300d980420070a05540c00900003800180791542082c03c2e80d698010f00181410380c50380b500e0089400e03030f625420110f00d900c2c8408038204d4042c8440002010041007000c42218100080368151080348004d90421407920b0000300d1090281c0e1018a405030000000c100925034110040d5450032074a8581c82d030044192045051403511428a00340490000050001a403034038150848151024102c0c900e51402071001050500310080880e01820045418010700e801c42200e41c1c0444103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 805656789 1250 805655539 805655549
    0x30c07033c1701060e13140a1d1b06090d060e010b19031a07021c0206190603020a14031905161203080601080709090218010e03031e030c041d01030c 65
    0x262034001003213102e070000a5903c0751541510002c401001c080d0020005010022001c07620700c80e40c400784503001c1002d912080e260760a6200c02441c1201003054141d82c0e0a05000c0c01800301c0c60450510058109000504000e00700544042c420a5041d5581415103e200c525800380d60341d50710b60703980b07589406e6945505480c0b5041019201c64150303181e0910071200141e141c40d10140c240042042d4038405c00102c0d2504a004040420210321004006d482c1e202c00e03204042c20702c881c01c4032006806514441c4000300c4e5402030a039803445241c02d40d82400805019240380c1d041c01400401240c4280d040407110f4894410300143c2440321134440807000405030368222000080c441c1c6c0340c1100190304007203c990400400d090030403607940c50142c02c0f60200c0080e0810310320b41e400414a4880354544005c400341c03080c2c090702c0c1c48134241032900a0640e28042c107650081c0140011507040d251503403010043d5040b40c800030450f843c150712804003800000b41014011070b60003042d0300400078858401a8080500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 805658039 1250 805656789 805656827
    0x5071206050c190f091e03030305010b0903030702090c04031b0807170a060b1c0b010e06010f2c2101050a06050a06080901150e04060f02030c07033c 65
    0x14000016140080003042e0951084c0064064140f150a0050342c01c0c44c0101110030888181c0d184211804007040d1700385c40120040ba0a11001086810b40300054928000d406401181441055001c011626402400008140404000100c045404c21a1980602488140301c0580c24540340009141501135888040300c218144000312003600045000e2025982000317020603020000070020718503048200d041000d10081c0400d100c200600b040701c1c0c604854105a03588070545d81e42c801901c03c0030b03400c545400049c241c0200801c2d001401510b40140941035100340300310703014000208410006034254800000d13810340c85610615003d00826610003c081c005001041c5024040b407900035043c05071809003d20840001c825080940c04503480250464607200301c0c0e81d40704071032030383c1460039102500c0081c1030400300007960f217103802224007407000c2c00e5489144c0302c2e041d00d049030354016250900e204c0c0109090b140c3c0841c141010790414200c50781015078004101202c018040b41401c2d0310440c054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 805659289 1250 805658039 805658047
    0xb2d15121e040204020913020307020c0a1502120a1b1103060604110a120f0501094b231504090b070e060d09030e0108011d01060f02030705071206050c 66
    0x5a4840c1489942055040c3c1e13001d600c0c0c89194000441504500030f102e4102032002c4100100309500142103e580c20090715141c41e00c0345c8410841d41241c040034180f1000da8088500c003080c0d000d0a0380200102c1541d40f8040d08400c00540ba83c0342c1c1400c03c4001555060004501007420b407900b44aa542c104804560800a404440c1c80c140a00e010b07070600c0d01c0500415190402e1140556000007520400c4c90008000e80e42c2c454542400600c01ea0b08441092507540301000380c100000019a092050461404000c4040c016068000c1c24104e0404152540c1c0300c00e849015549000c4140e842e440307500e801028070745004030030305008001149106100d1402c002850010550300d8520300c1d04820785151a1100141020101d4040d10481c2944404907103810700c4030741456030002d180b0304c4000c82640c40c2d140c0d42c0d0381d8803020040c040840500501d02d40007100100200c501802222581000e82c0c0160390404141c0c0d00c820b41842c0c510b9001007140d5a0342e208140130042c1c00d20469600000c810720113410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 805660539 1250 805659289 805659331
    0x17180a0302090f07022107060e062502071706091c08040204150306140a0e19020913080705070501020c10020d08040201031b180605030c0403080f0f0d020d050a0b2d1512 74
    0x41004401454681c08002f0180600707951080c040240580a5032460b400300d09294400741d035907440101c0b904400340c001c120302e08219003015140c80001c3d2486942e0700041c0e84554013004000c00b145c803074406000180d158000000b800c14050140146001e00c4117046ca890001e610f40180d401800d01d407030154000d01440000c500320141070002c6950155411040d6949101ca0803010100d480d4010b4070800010a51030100b12000515100b524070031303800d42d44020450b00610004e15045492600980c01144000026910510403d03505c140145004506589150084032451140c0c40f003840025003010141c03844003445240000050129103025403444c90004403000306402a400010600b9070f002a40c201214264002e440000101d41000c60703895441e02c590030000e50108100715031450510000840c0401c26108800e429480500f04102010026845498600b042c1180c009107008950f44c0c042c50fa1521003a428030011641c41283c3e9401034100355801d1060000c01d54050303102c410220b1f501e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805661789 1250 805660539 805660561
    0xd0c0e1c110d2f100302030730050a0608030408030406030b01030506090a050402150301120512070b0f0c04031b1d06010f050918040302060906090d1b03030917180a0302090f07022107060e06 83
    0x603124407274100c00540c54803064610300c007805507540608a0781c40085400320700356801200500840f00d007a2004c0012605074030054003514400c40f00542d00981090000340c030609181c11596009200529000402c3d0745460100801e800030f80004c1e644102100d0504104002003092202c8d0341c1e41e1140b070324101207041d51015401c8900a0248150071050f00c04240c202140c24140d0b030103164000102103081c40f9160b089031f02c24040e80700b031800c003004a0030061040e00641c60010300070038040e91400300b98180c829042d00d080d44a004810f0300884400c1c404841c001d03e821602c3c0c02544242d014041d1401c01018640c5418400340c07032501c2d0741d0003888418007513a4011b140740c20000b608004c641c00510703850400307800030040c03910050840408000d852118a004200404005a20003040c50406980c5414000d21441d1808002c2d080b55800c4049421092100d10866000d24248100c0c1c0480c3c000d0419081d0780221941c50b841d440c080401c1800803c2654040c80990117115070041001d0701e40140895 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 805663039 1250 805661789 805661867
    0x14010f09060e042d0c030605060f040b0108010e1008010905010509120a0f1206090c0e0a0f05010e04020c07051c020a090509030d0c0e1c110d2f1003020307 68
    0x8078000e28800138100c861144d089461480c2c07074005003908161940c030701307002c00076210480c2c002d031060903604860701c2c0d1840c26200c0c0101c10f4406035070306003090782001d1102801d4100071740302001030914850f0002c2c101400340510f1030890304c01e000102d41d0341000c001151501160b00f0f0252a50750701400202515540041004d24942451600a500020150345040100f42981161030202c0c00d05251030002500005400000340c0c0541e483c000082c0e5516020749000b07454020140000c001c0904800246842d030003500c02c00c6c0d200c2095481059666001078400e060000c401c0705901d2200040205515202c0889c0d4020b00d01c44905200f20320749011050345a00c2401d42008049943d00300d04200c0c03501ca071f007480442c4400a0010340d158001407510708100c46081d0000c959161013030408541c2d03800c1c0342410328066540310026405106110303401c2122181c401c2080b0b180183c4511001c5641c0e030390858a036206070701d00e40700181c1d41d0400910003842c45040039002010052203540100520310714404903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 805664289 1250 805663039 805663073
    0xf150622050d200112062405040803040504051504090c0e09010501030b010504090606031e0501050a020f040326070b040b09061603020d1103041b090504081c14010f09060e04 76
    0x291904042c481c0c0181d0305003038003600324017455140c5030b80070603e07444413002101d64044072660355051a514000c11142e610035409070700c0152300180000c201504007508200d03000302c010103800401e4190040803904640c00f044090b2260500b01d0410454a100f20003032940015602d8002e210750f40c10754440d89103001d0103100c1c0c2ca0080e559030303007030300207101803580068040c40d403001007881200800000c025401c007601340f09071515440c0c280407076401e1409100700c540c9007506124007802c0614540303840c2804041852401110308240342011000207441c03008040b1a4030903044100d40e41800e081441001714020b240075080e038403150500c1032a120540503040c0c0d0280b103150150f81c807044001500d02810b654010108850008420300081110028094903205500744403141410395850aa4041d03910a850150500d001041040002041d0001040400c802c20b0401b141d070404603110254000000d0303020081016828000b400190038601500c4010424610211210b01303150312588880e072410402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 805665539 1250 805664289 805664333
    0x3080a0c0305072111010203040b011a040b0a030603060c11070b0c010216050c100c0c151403160906021617010b100504081e060f150622050d 62
    0x40d140c1014401c41c200d5107065400140b45021650381005080d94810410101c00481c00594070816a51014405d8910076038001d5100904ae134a40024654a10140c00202041c0c410812010440804c407600602518555503000203c892950500f281114881c4905804200c20b407440300d41c65800001d1403105584040034595901d101100301c0f40c0c02403055203503001c1c1d00c01c00700d6942018480c021912600042e010748050962851217402100c4042d9803200007443e130410711806001d801c03180b07034540311840b22030704001d40300c82d04552110721682c008031600c04c81c250484401d80302183d03011801d400180b69a000410841c107065420040791041030260f420025152120403402d540c0c01d42200843c480081e005030003a400c039030740041c800e9109008030001d521a5842e05001c80604c407143e484003045050280016449a4944a90000000d802c6407041854000f1002255458000130026401c0c003400c0f0000c94081042e191140040f641c0c0014400d4099409250100c2c9100d851041000780b000307a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 805666789 1250 805665539 805665557
    0xb0a0e0103381801092904081204020d0237080a02061315050c0115062c030f0a0605010f03030507080703020a29060d050d0c0c1d1f03080a 61
    0x9078039003004076481003c04650f0130105000e06011411074000f070078040c03903407130300d1002914501d21030400c01041c3c070014591181001801003410001d46d041e80c02520040c00c00307410b0320054000078046c103054641080711600031800c1058841d988401c800e1540104c0c83c80c1101d89282141e415140d141000e006801940001861100b212096a480c0041c024008400061005c0f0200003001604411b181d210103602c0c1000d0b0b44180802c2049081c00c6030301669500580103e40c078600d0241040422840114a5903040851034035030307091026510681e0709800601c0c01c003800d030030300800313403481a80084148003030002c0910201e276000040310316064010081070fa694416180c124a0110b0050000e00420781e0034042000341c4641d106640d0102d21501c0f1703600855141c0c1c608000710740802810042640d488035841c0c0b640300d401903140c07200140c002d009001b00c0070340e0340198884507010580f001c011202160304114841d07081406182c2c201c556650030310003071800d60b0340f9010b940c4078020551051184ae64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 805668039 1250 805666789 805666801
    0x9030109050f0102031009140408090d120519080c040e0c0c01090c051f08061201060506030a090b07021507050f04081006061b020303030a020d0b0a0e010338 69
    0x504a15140c40d4400c0c201c60084141d940031a0007501305507030100c4010309003180042e0481060041c00c074900300380c03080c3c241e05d85c445540b0303001e043d84107030002600050007540d880049040014680501c00e03083c0c8495565521085140b44a4000602c50b10305110061048c40b0364850140c0554040d40e5078100510301c0340c3c40e8a184080c40d4045c94080180d40c1d070070048200300300207480c4001021610255410200c5681c0c1080002682503420f40c5000062080e100007451868100495070740b92690b03e00010304581c17103002160040c2e0048072404001c580f00c480c0c6000f085454004568020080d202074140380c0b188000035441140040d03d031800f00407011a05445c3c800c44942101c1c0107115a2084481e04404441c24401812051040101040040da141d01040d0300d14555541c0c00780e801800b541c650360b00d0b54004402500072074242c3c0c0034943e8820444d0842d0310755101c61005058110304800d80b561551414402d5210100e502801e42400720701e0600d00032103031001c4a0b8104107006400142a0b8a030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 805669289 1250 805668039 805668041
    0x3030114030a0c0b190f020c22022107020606090703270f0501061a0703031a0a180b01020d090509040213110909010b04050d170f13090c0207030203060c090301 70
    0x810280000e034100100056541440005041c540d00550b13403100c074034014104c11b0707039160042d044801c00760f00034200c030125519246141440400c10f032204400d40d018404005005c90b001040b013813104034040c1481880d0540544600303903003ea840d00c014041d5140850108000b10000340c1010145921480701407e458014502401105004d802c0100c245215040184011a481d5403ea466500e050f90102c0c43e8201c040828124900704042e040c40c220003550110b0042c9100041c0301c1441d8425010140d01d659003803100c030b000f090b11406048806521100c000c0c12030307a50300d183d14107643c0840e02c100d00b10b5800080d2282282c6003240e80100aa072030740040792922400d508035840c1d0515014401c810794041c4406000e510005681c50005a030725030203102d40d2031146006482e4016000c01c1801c001600c252945080d0401500307d00b0308000a007980750800b070b0040410450052071110701440440712900c5112200d5406200402c6003d2460300070a840d40c0001e0314251442400207034421240d102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 805670539 1250 805669289 805669303
    0x904060e0d0c02100c020f01120e240708060109030b090a060c030c0905010c0b011505070c12020114120604020a0e031507080f040305090d0606051324080303011403 72
    0x80c0ca003928000002000024102e100c2c160040f48182c0100d4044480e9900c542ea400c0a040c0c2d0241140048002e00703070054503001035103d2403005030394071030264002c48101031101c01030303c001301d00780c0111002e9840c1c07000c0e0400e03100502103002c100100c010000560b17406200003003241d8008002c060180c4514103ca0300301040100050211801c1054001d4800e0f8503a00050b01c11b4a595500e00b503051715280111101800010044d001d0105000103002c141d8211a40445201c80da041c050301d080c42c0d130b41d03401c1d000004681c403a14184081401d49002d5581165840b44007a08000c003051408e0000301030710403180300180c4102d00496000c034509864501540310918103600040454114088908000d005a00100c540400240ca4100407071140a82c1c840f0103801b4580c51303180c0714245010181400035070307480d1020540781183c1340d000009042c1c440280508148101c10004140c1d000c0741d02005107510143c103280342903100c0304241005030031804811349055502081d02c04d2110f62501000901d41b0325 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 805671789 1250 805670539 805670561
    0x3031014060405030d08040501181505061f050301140603160c06060504020d06031205030f01120206090a090f1a0a03110a0e01080303010911041a2208010b030c030c010c02090406 78
    0x100c0c074a1060800754201031021f215a208000a201f5429081c08800e42030745400360061486407019000740c0080d4045d00002d41c0302070080c0c4120b690b4030780140e0002800a04180f0303d004a4400401030081c1c46007410210342d00e60302034801e82e1a60400301c010f161410041c4060408200c03684460504020386038010030011300c6c000308159112070705807c01c0c1c1c00400b02d0303100450f11507000c0d40c5449038150180c0300381e174406c000c414250f5240c2e0b0728020140f03038081600c0c141241d0040b41000010720320b6840380c1120000d0320740c19170000f4000c21080111411211610340d00e0301d8401240500780100d5491714510401d881c0d002d542c4400800409001c141c60b4074898000250349550b100c0041000d1800101850407101c039103c017440014035058001200e4440d5000d00c582c41d0740440885d28900928000604030080ea0382c50740000f81d002c0c07280300280245284c1200019075103c50a542c42450200000114a0782c12000b0300000908400041d10502c40728200a000350121000101801165807044000703031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 805673039 1250 805671789 805671793
    0x901121e06050f0904021c03020a020312030703050f0105030d030c0909020703180b04261e0c0109061e030b12030703090302151e0904090615050306090303101406040503 74
    0x14410640140141c4040d024450149505520901e410314201801c81d00903500903114141c1421050800da00c280140c02c4282e09600c0b800c0304480c016201000700b041d45c1d5000142554032410304c6500201601e101038400d8072110410001031045503800f15000142000c1030600040f86003854000b40c2e0110034944c4010380440c4003080700800e064000c03a2480c02c441c0030449013160a5152070320f651040c0607500032018040405a0a4203003140c00d20040b200450078002240c8650810150703500c4511200d001a5000b504004210302942d60458071780c42c00b42009040090703042e01c0c00942c0401814114017450304064807159640c40a4846003881c0840000b050103a0303076240654100a480c8040700d1000324003401c0703c85025003101d44c0c1c2006030780301c1c0c3e0440304130942040111390614007036030803c10f6040e030710a5660310302c2000541d503441140200900742281c40c0203249000c04040c102032005108000d02d400030402c00268803010140c0f0002d0386c004040d29148006c20304003068090003140c118075054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 805674289 1250 805673039 805673081
    0xe01030f0c060e030d0e18100f060f0207050411220302100309080d0911060304030e0a0b040305030a0e0a0b0c06040b060109061e030617010203100b130b1806030708090709060308090112 81
    0x380780d80c1c02d800c4c05527107240d003880141c184d80b00c504850b0700d0440986040143c000301414021842c203034100b600301d0302c485451141060000701d8842205035003071644003842c0304941000c20840c103054101c00449501404c0030130000089440b00b0302c56210350700c104070080e65a19456001c00280041049030000c000d40303095200c1ca40b40c034000d04207030509032131213108000980d80003d4504c0d151041b202a80e51002c051420a1002402603600c5500007a082c1d510042d82540800c0b2900350402401099114400030042410325007031418880c40c000d4070309410031107580c00034800c480d04140d030703411004414500c0d1142d8469181c0e0440c02858660807000148d000002e054981c0c4105401441c0910350a0501c854440c2d82d500203440a4826045404104c0d08107507400c01c0720418410142081c1c4202150350549440c1840c0000c035254030894480002c9045501804440300b0100085406007174011000c100c400d0464503002c075140074907801c2c20b04000161036030300000e1401e0b801c11702100d502900c0d10280c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 805675539 1250 805674289 805674301
    0x1207110a032406120807060c0e1e0a050f030a0f0807020310060302031623010903080f030f0c0a080c07020d0f11030114010509060402070c0e01030f0c060e030d0e18 72
    0x19105000d0702010400e402c00c580400c2104c010000c0c1c494150b84103124a2070503032560785a030f001e00260081c40c03044c0607610003101036540f1195003504060b010042c00c202c0102c0040108100361084e42c21550007007078071400700500c0b0b0b207001515540154000c084e134000b00d0305a01c6c1c074449621803040001c0d01801000d0302e520043c440c5820000c20381c0d00c2142503c4480c0d19040c486080c0041c83c2c0309100c0c400b9410302d2007040d2065100044908004103140c68407440740c07a6210014030394080a0103184200d40001000807000e01e0b0201c568000031241006440e06d0b1500000034840c1d20003420070003211100156160456480301604150503601c0482c14031034a6441c1440c00c0b1407004041e101e4065428507000f00000400b8041c0207040c0e420080c0090b100b070b2241014440250080032040300e900950160200d03a00c417804400394000c500c503101c2c9940794001071800020f50000c1754802414400c001c1c403a90346030f40d0301280845140c03c0311f286c80d0913001c010f1000105403101e44509a10400359000c140703c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 805676789 1250 805675539 805675583
    0x310090e0a080c0a0b012103080c0c060f0a0c0f140d0b041e05150a12050a0b10090f11092b110906030c010c03030903031514010305091207110a03 64
    0x413038010041165142c1c0c0c5c69198402581c0d101241000d044424144c150020340a07000740d5800c142c0d10170f03d00303040007840c5940520b80303042035404242400941c800c10000701010301541001a94078070b4010103d2a4591015107500840b4428032001000072694213210021903010181294000704240250601d07540c8c1e281e44070543e002e44140903420500029021600c11903e0024000f010f0a08640d00d4603004800803000324580d000c40e5240140c2c07940130040395000b0f02d4a4041d80b11031007030501103441c0c401d004044800040000c80085d0174040ba0904007558681a144c090f502614058040031025603016495501642d080d40d42c141c26404040070f12115281c828031001c42a10001d0047d00c4000405030b65002500c1e085000586821900c400280310b80c2210105a101c0e040205031221041402c0d0136145417138002800b4143e01000a15056038136000b05e0b0380210a6001801c2402120105040070b03100d504806050a9012842c0ca1266120000050011500502002030303810b41561201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 805678039 1250 805676789 805676803
    0x19031505150a06050d09050708060708010f0f0902090a0503030c030d0506041b0f0507060504080c0d0801080d0f09030b041103060c21060f10020601090c050310090e0a080c 75
    0x4491403601000880004440c0d245007410000109a03698861505500311020703807040003013105030f68039002c00a001690400444000d007141d02e0160010340f41c4180c1c020407059050b0f000301c0b4512214001007103085a5111300809450140ea00940c1d079002400204030304211381d0f4003041d0188030002c1d45440400e07011004e00000c100c004800c1c00252220000c000540b61040000494880c41e02e0602e83c1480c014418544114074504049042020720340719581250000c56003a581e03e400020031049144081c030041c0005141810a4449541401e82c40d41c2d9034003884501c5400e00c0410203080700c01a0094840c04011944009194614034140c40d00910610000401c10f0080c03041c440440c4004050744180d895255141440200002099902c0c1145a03000741245030002500740103800c0030f48480e40740003040596038000700b480e940340002c0351080758580600102046400d00c14002c40250400902c0110b4902d2180411040c060000090070131070001d10081911400041001d4002400314000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 805679289 1250 805678039 805678073
    0x20f0a03060b1e130c091805041703100e0601090e0c0901020705030304152006040308040b09010903140703031118010905101b0809120102042904060e1903 68
    0x480f409160f41e00c002c0c0462a40e5440565210410003141041c842e007952216490500318541606956a54582522000748060f0038454040d1540100300c1402800c030203284040044162191951400c1000a0700c90603413801802620040000030072426881190400040c10720b0480203080c03410880f4004940f5803107500818003600407d00300241d00d1402105a804071546806e042241107120b0204990152400380c4200b0074407010756070303068808400c101c1a17215503c640c039070002d00e0800342071095a400008001c0306040c0e0411640d800023030f91006522071399040780c00c0040c3d25021145010740241211041000c010480458505c0072120781900701719050000b030300e40307841c040d484000384031032440c2840d42d8801280740032110120440b500c0750b0186480d4001c034805401d00d001c250010308405400c3c1081c0758280c2d00410300740100701580b802045224060b08800740494540001d0310700a010314031071101071211003036418025071910005c074103080c045182032912440d102c0c0392203e0b882d10b4040b96 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 805680539 1250 805679289 805679299
    0x2b0c05010302040e0a0c140a0c03090b180105090406171e060c030c0d0b0301110c0f06070e19030b0406052e09090807170901020f1f09020f0a03060b 65
    0x1840e500070720072901542c402200c0c03058075545007640c1801a085074502c00080040d000645010190802c0107082c0d2003245544a004948003410b005119444c00d41100ca4891410401e29a881c0c60341d8640d0400380d00282451511030300f148001400a003a258000d0a2412a9a248242c481d41c0070854900c0c8405000024098500c0a514966901c4c4c089400c64014141000824a10342c81180900b000c0c20078614045080700910012a00750b609440c1d82a00c0c00e10046007194000a09020301e096401ca000b0080c05241b900d400b0040c00b14010400c0240110402c0da8000c4c2c00c882c064101034003640e00603006040d5410a4030304580246002c0303d99100c00e00312007584003181e0f0280300c145506d1000c00120490094185000311009120303419040750101800c0050b500060502900c604500c1705ca050700503158003031300f000a41041030109a84c591500124940341e20383c44540102a19820112400141200c0030300c04200c9130103410f10880e40c0700d003811000008010081c3c0100b12016403d5031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 805681789 1250 805680539 805680563
    0x18050f060403110a0f03080a02130b0310080f10050c04030f03050a080a0c091a04080f010e06060114040b03060f0d060501080f0c030a1209150503040524152b 69
    0xb520f9500d0f000a208018110002c0e543c100c008248590307000c2d43c1083c0c3c0702100500d0211ba034800e0f4030810301140d01c8048140d401004000312082a441e6480040441e4130140c4032803c3c0394480e05448201d55240398003000e9440010442100c0c56005540145130303c0782109282c00058217015242d904454030950009018400095102c00180140345201e180c23512400b1001d8102200f0042d60000c5100e058507280301440006841d1800300080d0350080c002800005001e0280741900e400c0c200018001814828400e58906108180e0f6084404031000304801d40d499032201800654030021604071558072086103c014414442d15034070a504a40c0d0980484925906820000d80c4a4101041460707140d0030074214080444c1c0082c001050302e41d114900b0075000764940c0d030500a032183c41c40402c0b001500c0801048200a0204005002e002c00600780e048006d540054000c0300d02e000810400c10b2007a0f26501149a0310b4001e480d25070102e1030640b24a600114540e4540c00007502402940c000522407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 805683039 1250 805681789 805681817
    0x1e070b2101380d381002010b0306160c0204060e1009060501050904050405120301080604030f0914040911150c1c0804260a030b010e180a18050f060403 66
    0x384040c0707081050b881803d081c60002003414004007000c000d40502c0d000080012114206922070304d40c442200c00c01c52a80c0500c441050090010301c5a0f940300c19a89040040c0340555400034000341e010150303284d9661112003800c02161401d16000b0020f410a090050208000000c032141c14030524031100c030444031079030341c80c402d0302580c195200705404151300f08130499103414250132450307006000c2c1d0102d41c46103501d604290800d43c0240e0280110340c1060082c0300815600c282c04402450941c6000c4200509004041d00809040c14110344038940c4d419900d030400100403210001c3e250300802d1244102442080c1206540c02001100803030b0044030ba40010b00c0d60302d540307002c412411903614040300d9030f9140c1d1040040c0c90006003401d210744c40c4200d60b40c00100b9000003000b507075906503804101150342c0800900b100304030780301e51441900f01c2c0c112030303042d080c600c10415400a07081d00023044041d440310803400c0c005501d910241c014042c3c1c4885107038021000500c140590703c203a6070744603110410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 805684289 1250 805683039 805683119
    0x1e250e03010b0a061d2b03020709140105090a0b0a060e12061902090d080d0614031504030e01051e0705070b040305061b0c010510030201021e070b2101 66
    0x18003a26005c42c0103500c2e50319200700d42d4000c03101d8141d00a4081d8030030264001407429454514100c58071000d09a03d040e5082607414443c03e40240105030080c0050700d4907002c80312111005004060107016003d002400c001000d420200d030303c0a018000c949215110600182549030300209580298103c803400149803800054403071045020800d134505a03580c690074000a5440500c146030321020000103140883c0d1004014200380b1914100012103900d040100102c00c86500e01c50751003070b0480251100c208040e017403109c3c1e215a0503d07054006c0742c0d4040050700c03940580e0218007407540900000460500400d00103041d12400751086945007030b5101c4034085070384190302005055400400100d400b000c0003079050700444206e0041c0a060125206541e403c45004903400c007071a042c0040100b0a5580610203818a403e015050700459040c500c3c44c40e80e521400e204030b450158001500100064143c21040513074074a4411030005560360300642ca0181c1d00381400502818041c04104a2003010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 805685539 1250 805684289 805684309
    0x906071e0c0815040f05150705090f060421210903110d0c06050a120207050c120616081f030b0901181a060d0210020d12051e250e03010b 60
    0x11021075040d0f1581d4507551038100c000d40d040200e69500c01c5440a01e602c0141506141c0b0551081d0b4495441d001c01d94104500300d00d43d000e140340128010001846603240100c040304007501c482d010810b19000c2403624000f5615012030f40c20101e8080503441d110b05601807812000c681c01901d4048901c5401e5040040000480c48014260500c2940c100131190103100904100c80c81410202c00c500501071400e420382c4d100c03110841e61600841e40c040050f2820001c0e1030030032004c8400a0074145030014150128146079084030b41802012000901380d00e10440b401c0030350100c0b0701040108650b803031608509106c415a82c900300c0d54204144400d4400450b0301c1409050742101c00c3d441e501340c251182d11101d00010b003d0720b8003c81014045400f585819040d6168030005034024843c02e001940300030545c03c500d042601039241000c05020690080d40d6080d9402a0040c8400c801782e00e40007040715100c3c2c65450010219080c1d40c1d09050060781091520305400c100303070002c1c00584528020015000c1c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 805686789 1250 805685539 805685563
    0xc090a0f0e160608090c100c0303050703060b041a04051f110c100813050706110d090521030d0603030201090c080a35030a09020a0f0b0f0906071e0c08 66
    0x84141c00c01c100300c0340704602c1c003074100d0403a0f81600c46e01a405004240f4440360b84038040049518600c044040540c9489407640c0710566280401c403c0303007041c81c04c040500ca06d12030000301100c0c1000c41103607803a4070f40c215401405c001b88403964603442101040166619002c2a1012031103143d40c448800d1001729900701007c6d0020070300412801c049100360782115010f0071950035800b600ca02100025410441c400241015450740ca0751040428507852418034a2121503080002d40d010030801c90726850242000c032540c0d40426101c6c08080513015265005072003814400c0390400c0743c00000d158065200080c9640074210000106891b02d0710307990744890401009040007564141040100c0d00b007100d907035040b000e001c41900905222002c19440e60800c0d50b1801c009603441c0c4c4000218540800d071103009100848090500320314024102d0030381e001e24840c0c0c2950500000e440f0300f0395600c0c1412a51100c0d8808040307000d07084c0c5070060a01d98840b40c0780442d2081d501c3c131800304800b0000194042e840d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 805688039 1250 805686789 805686823
    0xc0302041d090609072121121b0e041109060d0501080d0e030616091d150a0b031306150311010e03030309070b07061b02060a060e040c03030309050c090a0f0e 69
    0xa00256007410039000c2c02c0c4003501d44405032032034000d00a910309030043c61f907580c035030b1781c1c00142c40c403440e5a6007102c03e00301d001c10f02e2501020f1120301c0203412800c00d1685201c1290000345680601da22150640b05035a1141c1c1d01c00340001d4030300c40c07081e802d80c4002d060fa00c09408441041c21001030640360741c18071414945e81644003500045d50500400d4252003084041c0c58a40342460b9154055406400b0040107946840c03421000c12081220510303810028400403584110618070780b0300624800d203c0030701201103984000c1e071498140310807a000150001d0003401802840c90360703030612640890342c5003905400246a20505181c52500105881c0101c3c003507005000380d0351804205149a921456003141e0315034503400384410200e261502d004c000140e9401902c070921302034058004139002034020210341c0c031425040c000414810681503060766850700b800a0100d2440c14098039004010700e860758490b42520400c409030f6616041500071800740e59042c8580c40f08500390549480d00d099402443d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 805689289 1250 805688039 805688069
    0x70908060915060d111002030403060e0303130813210201020c010c0c0902070f080403060c0f090b0a050306040f09061d06090c010315031712010b1305040c0302041d09060907 76
    0x41c6000081c1c138903901d10030001c9201844522000c81c8074514520507031000740e00301060400c00e00905000d000d98807103a20002d5483d615118280c0000b022a803000038284035008503445450800c0c2150800251072155000d0301d81c102c88100340300000003401422401402400002c41181d40581d000c00347c940da000d40e8540e5030a09140210000b50060441564036a0b042d05185001c1ba01d8107004002641c0540d0000c2000903001f4006090302e00038050a004000301c80108205507000c007000e035000e40300c0c94903210784d803611f5a80009001d05440c0d1860440e4603d81040c80d003c011070f940c442c1d000301d49107110306120010b110004a131036a07400c59248400343c00600c1c030000079610a80c44107540c035440201c1c1d8145243c8a444802c8203108071200c1041d00c000c00101c204d03480880001403070042043e145502d2412200c4070f148001248036124075801151144000710855000740c0541e00500078030f9060751100081c00c1c00b2441000f2040c0d94190490280b0804030304c000d5404205401a02da070702035003c0c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 805690539 1250 805689289 805689301
    0x30a09081c0f03020d0e030c0c01050c061b04030b0a15050406061b020402130e0106120509250b0d0204050406060c05070605071a1302031b0d0303050a0212070908060915 74
    0x1c590141d507040b030401d40c3c00c0050600c0d900301072181302c1405c0e40000003580c6400d90050160b20300390010281a060081c140402c9494040001700c169004085104510036203183e00f000c90390b00d01640e00020b060001107020000c00741403543c801d00e12501c0d5903100d56511955030041c00100c0d0703d180a51000644800b8058012240b034880e0311114a20240c80140f920304400c0c1d010b44076450326000f49905d103140d180100061a44034400600c1d10018920422035410130040e0780d566001e144000500601a51410310a45100400e01a00500b8540d198a588080056814000354424003e0500c5245447c10200703989104042061000394000002c0140d2814540150f8650300010400c49020000c005040d05d99402c00e0707100c50080a14420403000c6110510405081c4542c9000445140c04c01c0348030160a59551000c81a0564140c140040c203602c1d0b190a040c082c0c442c064501016400360360500c080b55602c6000a03048030302501c00c1e1342213503d90340c3e661034641e00250f001da0000c40540c808180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 805691789 1250 805690539 805690547
    0xc060a0f110a0812190b06161a070e0a17030f1b07141305090705040f0e070b07030f08010b091302090306150f04020c06070309020a0e09030a09081c 65
    0x19030344864104950300d1242d9607541c5051540b125403e0340c4800302030010b2000d110104604101001c148510501c80c005408000c600b441c061480b5613118225480489000e0002860002417818217460788001c2078503040d030028042c130500b1920540198000c42000641f01c401e0780890303050f0980c0350701452404103110003044194110310760305150342e00f989031540c00382c1504010490041603040c0901001c4a200c00c20880d005000c2507404002c14181401c1140105020800328140d6604450000310089030f45108402400d05414208040c80349600c0441c0140080001d4020759110381c0e40d0600030100410308031048802803052250328202030041d600940381c1180c841900324a510001400c0c180d4190000c6d00d0b080701030740d00120340e651501c0891030380e003401c24504080340c5d410b86003985080160030146039910f000030026000c0660780c1000d0003c655076800304038024480c0d00800d503114100740001c503480f039003c17071a5080031490a08000640a00202d03014030f200d01206140d50390708000c0a0151 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 805693039 1250 805691789 805691807
    0x1051018090b19060f080603010207150c2a050c0d0f0807080d0f1b02010b030c0906040603080d020d050612100c18060504171f150b0703020c030c060a0f 67
    0x5030301080c5400c0f001e921040848904000f884199a180480122040007501410780909941c0c041d03401000004082070781c1d5604643c0c000d511500000300a07001c078204070340b0190695092440500d60354004607102d0044d1280844a41c0500280c038a00203984007088000c0e642c800703000b0b1580f41e06010b040081180c400280801a0095420a1928924000c49400c450110062001842d035075500420b81d441c0058200389421800c0c002000907000000c0060380e20407501d40f80364405c440c2e60001860f1600d07660000300c02107600501c03042e21030000f050404040c0d00504003943c0c9082c60000025101d02d803010718811010282b001500c0b4804039a58403030064044402d41006005c00c04d0f030a104000d03d6101031030300502103603403643c1d242c0c0d007401095000c2540c060044500741c0c3c403a182da400c03591814400c1030b58161918500051404501424084034112540185002c1c0004114035043c03680204010340d014030220180c6644104141c100142405a80c2c070000001d00d9020a954009006000301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 805694289 1250 805693039 805693061
    0xf1509040f0515070c03201e01090f03050406170402061b0a1b08070e090303180a02031f140403020d050c120a051c020f18130f050105101809 62
    0x30300da40300e0841d83c0742c2e02032080a40741400002c81444012003803681c402d030305412884007141c801c08140e0000b2040c907a00c00c280700f9105603400c180d0400000102d405d500840c2c490781e0040c03a131080c0c01e16038140500150068802c00011600741c40c000c11904a00d01d214034410740c0d0040881d4104400e1003403101803122050b07032003280c920940808a0205080124040300c0000880c1006030032410148554100303a4943c1c0500c26013030195060005401d0040305aa5201200030f500e02009100104020f1400d450100040d4050090088041250342c0c1141140482c4941140c10300c00686070002c1d840301407204039000360060b041507050024440c1f21300000c102450082040310301d441c10900c01004154403000c244400320b00005030000340d42002246110102036607042c00c5080118400e0041194481c001c18035808002e07124031114903582d480b8181004580540e070401c20040b8444565000304000c0c0190b40c1f04000350107503400c40601c01e84126410700c9220301d512170740c5481c2040c4840600002061 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 805695539 1250 805694289 805694293
    0x6050a110105180c0405010e01140a2714060906091b0d0b031e07031203060b1605010b06281b030e0a0506270a0504020d02030f1509040f05 61
    0x3004802880900401d03005035901008240c1d80c900c0e0070110742c07920300d0700043c8500550034080108012040f00142c18115190b044001d011084140e0001e02030340d031745400007409100c01c2107408006c2c180d0660040144030443c00200f0004034045003586690404840c0c2030f600041c2c45000581c2c5040440005401851107010000140100d14884400e40c01488400e035499a4460307001d181840c8c10482d21902a52440311103c8003104091a1610307008503000203802e503039042680950326440b0b64030113001000700807021034560380442031411020914080584156003800300c102040d2402800f101d584d40c000080c65150703401d272982401500c4100765103a41c00d000c40344100c071400d1000944041c0300b240c4250b1b41e80c81942003c030100014800a90805802a030b400e01c1449007000f101a0003c0c401403400d81e03510100013003900010001005900150381060001c0f0303840f270381e11450750040c501962009114249645d46c3c60328158005650700c2c6096444455000401c01044480144012442c002c2007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 805696789 1250 805695539 805695557
    0xe0d0c051c03090c0f05030601030803040f020d050c01030e0105010501120f0605102d0c033903030b06030934030b190e071e090507090f08120406050a 66
    0x118804100c81d004000d40441e803141100f0040004120140300601254076141802c00d003024003003640e6050501000f015001d0001c085000e004400c00c0304850b095005017900084401450025143e4000400e030502003400c0843c484403004041c043c15040c0d0b50181c1d2585d03407804641c0c4a500c0075280584d05c058a0310764a903004203840c2c850101c0780850b070303003645c4402503900020800d100303000d2040e02c181880b071a01c020440400c40c0c0e0095042c2591030301858203000f081c0c030f4a141250b18551408280702d0184505056025400008440110742030280d102088586454000d00a040c0320880d11101c2070740213000c100ba0081b0103502d9404c4041021040c00304060300090751040180000c0d00281c445020321400c0081c418a034801a6801800c80c000a202c0d09011816075a9a00240d0141903d0f202e440c031104448400e40c0c00c1c81314002e01e0400000e008604002c80d0103030401d10300e40a1007841c40c590050100c1d501000107155205006140a8689810b26181c4103d0342c40d0801c8075880200310a1038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 805698039 1250 805696789 805696813
    0x70519031b260f010609060302030103080a110313090507020706020712290915011d04020907020c0d080a0e0102070602030f09040603050f0f010612051002030a0b06070b01030203060a0e0d0c05 84
    0x41d10180c441e80c520140c2810f25410050302600029a581c00302e401c145c0100300500007d80e0601c143e03600c0351400e0900c001c210b615811141c1c20f6009000b152221040354107070004441210380c00c101d0042e8000d40a5641d000d488100c120703250000c038000c42d60044050b00c11400001e04804406d0540c000e84440c801041c1080c50b09058480810ba40c0064a54095148031a01e0412810350030300611050741c40d0f9068030b0006030340024205000348080d100e070f00e5450000d41d4540c024026084250b030010704a4001c0c1c6100d1800c068603804c1407600400251000701012829400020040c4c26a03189400843c10080300030b04181e10b9520034452260825201c200c00170000e002003107054500b00450019100c0a000152814215142907000c8000200943c640c100854070220340102001d5000c500940d507550f8102424020740070140016422460003d5140c2c107000e01e0080795030503684203d06907040c40c0c0365100c0030015a56030030740e109010b400c06d540000506010b0014108900e2103841170301e041c0a801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 805699289 1250 805698039 805698107
    0x60503010b011e0917070302030601090b09070e12010603150f0c12020304060b120d020111040b12041e0807140604020f040b01090506040609080f01022b06080105070519031b 76
    0x1184254050741c010f5031b051003103141c1800518054a140281045916280800604580409480e41c01440b0011180700c0300d6485480c0001ca0741d0340800000e010f8250781e8540034040c1d40300300d01c000703102c40d1070130500308401c0f03650b4040c1e1000003a155075202d04500103005580000d41c4042c100300e40035a6100030408041d101c4006401e02504140054000c413812144007034256109030142441c01a410001400109106c005940800c0d40310b148001040d0340c0c1d031510742c0c51903940459140c0c0b051b00000224040100e072130014a40f1910880c10103d031304000b01e20413960b50800b0b44000303500c114071000071000b5040a6100d00140030052400724411961840420390644c4140c0003800090201242446000c10802c4051600c1509800862400d0800426141c405048036a01c100c2280c8003042400420195000034020701240c10080000b410000b00143c0198484105501029101100407000d58041e204e034507d5280c4403a0614401d450501040310042010050b41400d20380100900d080341e282 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 805700539 1250 805699289 805699319
    0x106080a0b030c03030d0c090b0d150e0105090f04030507060e0d020f0604020d0b06010504170c0906120a02090c1c1a0307060f030203061503100306060503010b011e09 73
    0x1a1602895030a0100c480c0080c0d800c0000303000d000394003141d80700e8800e03200042100c040005000c13000a001409410803030702d003449940700420020f80803500b41d04c4581203902400030620f0184091121035560751041000404c240b04080d070150000c80003071502446c80f00d807507600510074a0203034901605030313403144101d0b02d007268000b44036400403180051150b010481103010910843c000d28403485d240d400101c401ca00500300501069181c000700301c060f4016401d490240040d9400207401d1800549119550700d98081c040340305400c3e10010503800d080c0000140100070900e4080e02c0700940e10307000d00041c0200680303402c0c40004200600c4050306da207440e440100700030800b0301003100c1c185504001742d04030054800c54841c4d04210010840f27681c0080d03240101d10040d003005030301d0340d5681002070300041461208101d801c200000b0465500c886006643c1528415181004016181d200b850b08903250101300a0124445607840c00c103160480000c0c140030b00f03141c2303040b01030382d07803600403410300f00b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 805701789 1250 805700539 805700549
    0x61501050d0615110c060702030c1002010603080c1005070c1e030207180e0d0314010303080c070b07170702010204120b150301020406021b01020321040203010e0313170d0e120c0901 79
    0x501040803a48013409014400d0100030446440c1d0030070301c0a0700060340702e803850034844bc4507840000a448449000390056001982c101c41d40381d440d6411019110746654a01c1410741c515407800780004c202c90700904400106a0304202d110706441e9180c1c8101d8110305d08082c0070340a501c41c0002c0040da51404da80b4084541c1d00c2170001003400844a14580d251100e600c0c0c2c81d07000d06007000205050b0ba043c240309141102d41502d0803000a0b01c0302200f400d0303e403103045406030803126914104807402d500a82e6442241407101c00804a03070340d84100403401c0f0f004034002c6039640030036284404080740c0c011000d03607004081580b40740145d00300040042d00720781c02030f807211000d81c001c8000b03000100c00000d007000b031008003070016510301840c48000020541d44100004400d1748014003260643d1001d500c00d00454003a030045958420100030712002c1d14156200324003400c540c034403c0204420001c14080755a802c2030b00c440309a42c541c0c3d8208251109520f08444d2103205000140d09541d50f10240c06000380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 805703039 1250 805701789 805701797
    0xc090507020a14010207240207061a0f0d0201050a27090b130501050d030503090c090708180f120328020a030f0b0315130203070f0512061501050d0615 66
    0x20ba0345242503010030010200c0361149901c180040400f14814810300d03846007413007801d441141510701840200900403070710041d00132868802003400e2110b0100c0304079400c144c03c5400409132074002040210807409014003d0016806000e424421801400e03d8a040031000004501261a42a0019010b85640d2009011f05d4854011031346c54200000800c0307080b00210000d000942c1045e0110b0100c91005c0801010000c0020000e03c440740e06001e84003603000010070106450400c1c0d200140081015508820400766152b407018000c04005000f45590b85030401402c0c00410400c6060604d030001403410602c2c1c80c4482000d0a091500d41c815170381a00500e0b4010703114400944000c040750400740c0180341c080d10304105250584e4001071440301440f8888100b02c519547d041c00094200502100250941310300400401d9034040204100141c131004d940303c04078a80b141032a10741e90b51042d41c40521401e03c2c0805014a548194002c05d0301c0140310f00e0208800e9070381c401d02c0b1400100410994005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 805704289 1250 805703039 805703053
    0x315061201090c0503090307020910031b150327020f0d050709060f0501170a02091c060e0604031b031809020903010b04021e070219030308151507030c0c09050702 71
    0x940b45520a280c585009454003600b03501e4406000c5c1e40c0e901c14408040d01c1072803a07a000407030000b14005c105000e1544800341503512006070790200d40240f041d00610026071b8141c000d1980542c400d10584031070900030110160b185111540031070340d2010401040c0e070006ca166210f01c090383c803059010004180b10f0f00c014403002d490700340d03984100e0380250002688184014020880d580e40081c102c1c86400d50b003441e003c07850b1a4000da1000038031542821a401c4a400242e8400d082c0040c402156550b004050070300011003400c2c40c040d111030007101c000303000c560702c202240134442c060901c0c4a80e491103401d001481c00c0f030031241c0d4072070146150302a045250300010250018102802441150070050b40d041d03003000c00d4200181c410014403c0304201640010039004195030b102940002d03204a14441000385684a040081604504541c03507120306588070308640050a0100614134142c00c501161400c1490f00d40d812904884024002c3c2d0740c80c03000d840f0200d6907170304511400c0e0240700503800410390 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 805705539 1250 805704289 805704299
    0xb120313060314010b030f100320012a03050c0a0818130920060702060301120317040506040b060d0516090c0816050c0f011a040b0f01140315061201 65
    0x191620341018010f00b40500d0300401c0f100000c0000c1c0c03030b040000240074178950359a6601404d1000042c0d03202400c404104e414030a07211080601c0081503001c280c0e604180384c10500d0001440102c400e042e02d00c01842d146e41540070a10960180c0158040c400544c1c45031032a94075a040346401004140b440c1e00600085141e103454018200030083c2c42c080e10a00100c402c42e00c074442406624800a80250210000a43e581c1e85c1c4204076181240d0080407281c403941c403215892a42c1c4265802100803500004004528101030010f5600c81c0d07601c00010401c0355a2540e6005c4c40400140c8240d411200907021040080d00501240d81b150300c1c44d20400170002d1034200305d503040c0e510715510301c801c3c0314a0300240305a120800303076062440380f12401c0c19582c2d00e10452185281c5240711041d40015440c0c1a40710202c0c260a504050325850104c9050150b444408104003525420f1088079020074142c0740c440502c54500c20246a0200c003040341c6004640a400100345a90311184200401000400041c40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 805706789 1250 805705539 805705541
    0x5010603051302010801060323010312091d0c1c14161112030603031c0219080610080424051911391c140405040b1203130603 55
    0x29100d0460710a4460502c0560001380460006010302002c040d280c02c8a02c10003000d000d202801c801110403011199a0342c1e090000384046242c80c0342001881c41303440080d83c1000d16082060035054000181d400c0d80300c90f02203003499404504202c10140038041d1049450300705d40300e0311134180b5030144180501d1030007900841c024a20380e5811000c0c445040600c3c02c080400245005a409003404d400d135894a501c40024a180146194240181d40c050f80d070448484043c2c018044414450303042c0c01650948020035620000115031030350708005400b01c0c80010a108002451708203000d0020a09545042d0b04054440524070b6a04469941c4640501c10600c0700001e0503c0e40101d03405040107107012500000d0201d00c04d2030301c800304120703004103901001c0d0030100300c50400029112829a407200d0484401e91034071401c400c03d08a0400320040402c00a0042d19122800d81c00c0e018168541070400c0104001444900d0f40b60307030800745041440182c160100000c041c14003120600601c8035180140042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 805708039 1250 805706789 805706791
    0x61a0c010b09190e0102090303130602070905070f03020304030306030b070c0b060609150307260402010206090c0f010324030b100b070201050901030c0c050a150608010213120203070909060501060305 87
    0x10b030044402e2020421805150700b0061000c04019802058441d8504080c2c4d01901440c8851645400001182e000b2800802280c100302e514507000d0b00e11496545500c0c804962040300d10001298091700c0e8816807521980c000d40d071203071003420000f035010703100d44440c06a450201c85110101d0300c00c041900038000d5204a85030301c9181181e601d40380c000e84001045804d1075200201c4010384011011440c100e001d001a0f0004101480000b08081141134144003171b00c10030340d41030b4003501400c00803e03648071000c42c012001e11009020091050941001103004011401c40a03608541e8518049030180407a9000c400540c00740c081c050042c02e0440c2c040d00e003604103a0103259104410040e00380140d0f046010b0750350070502403d000515410603e4165480300340054020010301420011b0410041808000142c101040f102081090f8680d4017084c01c1f4411040c199640c8000c0540070441160700c5503001c000ca51015098450031a5102ca80304152618140c04880d100c0e211801802050340c144921 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 805709289 1250 805708039 805708061
    0xc17090a0807140d0f050109030903020f030f070612020c071502120a020615131e0e0a0804120615080a0515070507020f0f1306140904020901060e0301061a0c01 70
    0x280070700307620300f00601c501c00b200a5251409402840924021301c0740340c003540800660000f000307110307000191900422041d42804203d11451203005040c025040c001000311010071150020144641042020b0318044a40c1c00a1412607408005440d0b9684042c00044000c042d441d088400d854800304010f418400c5d07040240c501c1943c188100001941d00040c0c054102040006140c01d42c001e41d00415086010602310200c8a800c115100740c00940134550855100c1c00300000f00195100d6048182d1200d02480014102e88001d01c000e03c011507d9402c4401258407039480042c0c2c4001041e0303c40500946e940c491221600a08030280500c60f041c4140000d0f003000004954092401c56005030440c0640400a40036038600710540710240c442030030b164030500009240683e1040ea14013a400075180318051069540d040051111442c28070510843c003035079006000f4801a800c1c00030072650760302e62401013a415074903100001034400d4500d80f1072210140302d8000607030311805a40c000c1c2c255030f04a016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 805710539 1250 805709289 805709293
    0xf0e1e06010510140919060c0b0c0405010f11031201060f080106031401260106260d0804080a18030b0f06090105030c060901030f020f0a0f030903021b010c17090a08 72
    0x41c3c0711803039440a00d8208406502050f5070b00c1c0c190b2640454400800c0c2040000610207003417010503903a401407000b00c0e1203131094280e010650748815203500c2c02e0040b407144902150303911881d0758483d8040e4540380e0011500c10101e90400030200e03000400c1410070390002000c40d9411031420110380e401640316015081030b080031302500c1c02990b20010014414800c0c07a48a151a009042c0c0400c1e5a880282c103144100000780a01134451448400003a030f510321104401085006c01075400d400411108000c1c04641c41d40310481d511900c41e00465489011001c0c100308141020048001c0803641110196002d92043c10480c50300c001c0f507121506000d08034912482060004200e540e13000107145150f510b0030384000c0d88852124005130f010741001d65946070003600104960300440461400340c0070014403a51a010204061300080d000c45540f0240607005800c50b078440080f00c035040454101c1c1013018034204040840548a40302100e500c113620b40f113a544000790070610b624005d02c20300090029080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 805711789 1250 805710539 805710559
    0x20316020102250501022802010e06010503060f0405120703030c081e010b130806010b09090609070c11010509040921170f0901230a051b0d0f0e1e060105 67
    0x28550340f01031140100c2102451010018040000c2901510b40f220300c00b0f181140c2407100c01c00c0144044000384828001076203440c42c00c1400d14000a02903049900c05030143c62581c4810401c1c8090600046c000d49a46c42078140404014100f180103108240c00f9941c0044c41c0002400010b000c0307680075200d40c018180b0807080c0d10b10083e004444a0441d160b5800e62a03546841c1c00a109e681300031540000164000e1800008840720010005d01062204030303003000301c0d0740da000e003005806081130300c2c5e820000d6900f03010400010310140c600c00c504401410814103107030720040001c05841d020542260304660303481c0b22128003006030101c25541c40e5142026050101c020100741554180101441004641040130848600003035201140801030f28090000e03030800b4903c85420b00101741c0700d00710854a40342c005900508556081d01c030072851406550300d084d200032002000360100300520008070369903141d0044603500070070007210404000d1b5088134030304005d400b64500b0550140d000d00c0c05048010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 805713039 1250 805711789 805711807
    0x2203060b1c081c0b0d031101111201141f03020c070b030717100e07020601030c06030501053102032d04020f0d0309030b010b03090c040e19030e13020316020102 70
    0x981943e500100040341078000c0c000c4540480c01404009054640058022000f1400c0c580c0c0403858503c15403002c1c2c021300c2488600d414103141440340004540c9032203200e4006010040c9800c800100c0c041c80145148410003100a146030380c0704141299501281e40095500d2454070107000c1c581c0104014401641189440000a00916205414013500300149400241c111b0020404100034007071001401500389080d0750003955425003804150385c000c0d030400f0006202d41c07003402154166180038000803515810b00600c44000b80d0b01c00c81030300c5c0800404e844c4000d018100d10181d442104180e600c01200c13491441d191704c089210a0000420004113810040507072a00e8034410908074040e00c00380306280440c10304940c848281d401c0184070040e410b00018502500602940c05a6203500940360009559010001121080842003640d0b030403000342d00b14000400d2864070040d40c040d0612607102080500000c9401e41d6007040b0045040d804003c0c41944210711000d51042800c6000031450894a2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 805714289 1250 805713039 805713053
    0x1215171b060a0e030a0f061401080a0515070e0d030509150906040e0c16200303071703090106030c12121403060904030507020d03030e2a062203060b1c 66
    0x1900c07074000e00850b0381c00c0d07450f1a102084403003800e0b9044040e1442c0c20031149405d8000d80701294050102c00617103000441c40d80d00101d44c0c050851351040081c00c44041400b00f42551a90050459013800161000c004841d213800074490510761080c7e8540355221001c13810400040c2c40440144a014404c0c840e02100f900d820088409039180d000f400301d250307502d0400903070a0b032084000c0c400300308082003442c4c0d0400182c04902c040b02e0744903504007005000b40b801419038078004c0c0a17000c0d10f16001e0740008505407441c02c0c002c54016980c02c2c00410b0641c0c4075110030841d0f822035441200c3c00d0000c61080d0051100801c43c200e4500560719209100803040c1002d0780c158040030302400e00c41e80c412000b10741003500940031601280c0e40505500e0114010b420090020000688107074041d001e0b40200a91502c0c0080300f840412480c1103803070003460449014801d054010710701e54801c104402c59017685040c000d600b903500562281e035010580d200d0200070b01407492041c022004900f0710100d50700f00040c0b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 805715539 1250 805714289 805714297
    0x40e0a0b03070302030a0b0402150c060402041d1f05010501020f0d1805090a0f0f0b0a03030809121b0f0a03050a030f0f0614010311040e071215171b06 66
    0x401000464100030040c0060700304030140d4002981449802c04c0c1c241040748040074144601d000f00d0316951b0600004000c203803031b8422010004540d411040c00100140360a0340301d6001c10303029000101139241003050407403402000a100c0080c514174400d42c1000c00f80c690198a01410f82880a850f41c0e04110800030341c0c5d601c0303e01c001000c3c000250841d00b1401580100c140003400010141000c41c10107020a5000303160321400b214159090003520f5040c502c0601804482c000042d000c85501031441c1c400701c0d603180703025180c214ae0307001c0c0f0b600b551422103c09010f088900e10f8001001081e030484c0d4200f0f80387c0802c0174195040c0713401c03285c0d864001c00e404c601501c60800090902050a800031401039004111880c0001281e51a00701d0104101c3d8aa001c10000701a082c4c904004413409022031156500a621038448100c82200001c1c0c00f9512590766100000d81c03c00000c2205003000d02411143c1c1c4082c3c0000882003050040040c001008100000142c01d480c0240941941914003080042c41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 805716789 1250 805715539 805715551
    0x70225151115040c06020d020604230f0f0607170609010e0a090f03021c03090c2c0f100b0a1706010e04060b03010e0606161e060c0f0311040e 62
    0x1541ca2412a0915050041d21014403200b152140c1c0c40c682482c00d8a124130460144034014410403202010450002403202d014070780080009030040f20658040a44410421003440e80d07001390365122103441020482081c80c00314500203080c140c640400b00800244c4001d1300698528148400c1c001036071106503034a8199401c00c0104803c43c1c4d02e01c2c121101503c04100700600756010074280c0414540d000c101030400384500044440c0c6c1c2c00044004400b95040303080007500f04843c0d068200060600d80d50307040b444c0c0800303880359000901e4000c0a144040d800311451865218001c0400002075803130404400540015545e20742031015103038009148500909415001001c0c20011501c079030300070741d60842e0011000b0401c3c0466601daa5408015070402e100d072102e40c00c00003021801a18000b0180c80b0390405000c008075a0600d02d8807071600c15004038441d00741e0344002c1e03d40040032501c1030290b1004a40140c0b140401306c24610402002c45042000303200c0044400d00c01441042e00c02004150444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 805718039 1250 805716789 805716797
    0x60d1203050a09020d030c150204050a290c01090501051b0313140d02010204050f01030c02030711040f0603060209031c020a0809040e010e0604120f05040320030607022515 75
    0xa62030300b008100a08000340040d40c09000700000034109544103144216803032158403540117511440b20500280e00a034060070340e001e907026400f48111925240725105444400203501e4a40d0405104003100ba40211030100441e51602c48090a0040900406410072114420345045111a061061543c080600201c090810701d2011800340182c2c40c006c9010004228107503004100d034214064000c0d8030074481e240c000e203285107410b03001d0b40c0244101c04d4400c1c1e858000e945488110fa840d15480082015100e612640c0e03410405100743c003a11565002e103102c0ca20042c0da6a42d05010180b5000d03602d4013160280300994003440340f266000c030300c03d540181c0c0039180c1901c94000710005805481150603104180d0b1030701101a42405000035050700441c0154036a40719510700441c11500300c1030328902c4101054007001304000044201211103400449500354080080150b00020704040c425180c010059000c202d82400c58414540d0f0b035407400d0b14040e000445540b8145c101c8d26003d00400041d4140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 805719289 1250 805718039 805718041
    0x80a030b03030306011418060307030f0b150a0f0320040608130c060309080706150f0609060503010b0d2315030102031941090d09030204020c010b060d0204050306060d120305 76
    0x1e0031201107e8807000d08014002900c030b160003003000b8018081070302a40015801e00d4407000a07410404080c0403241d03280d03403c040c5050200b2205541d0242daa400040c20583c1e2498142c40a00c1440381308044040a4600070355140c2c54800f0081c655107000e406500c51100081060303000400c0010080d040b1800d509000c0303800c00d000e04004d846401762200c081d00d07681c1003850700301a400d240900442501d640b4000d9050164407600708071a04151401950045070b81040180300b0001c00340060a00e000c0303810340c042004000010480c01c6003090b14800e0440c01c20b207200340030100f8410716800544050540086046142c004c503030189042c0c503100411003491391440c090131503416001e01c088416494400c40494040d0000001d0701c01194a070743d0f502040040004100d8000b03012840321059801ca564480801d42903808010085d07100004260040d0350303c826440700c949640b40a000c107200b0003803005894030714210a0508000c00200b08500c1480e8000042c00010384400c0e02c1c841401a9280000b03103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805720539 1250 805719289 805719307
    0x9191106070c0b0c120f0d150305011a090a0207030e0d020a0b0703080a0b1e0910081501140307050a0e040503070b1602010e07210804090504080a030b030303060114 72
    0x441c40780ca0005049901c608101143d0041c100740180f544022180031a40e08010054100a9a009010440342c0703810040007008240c89450304402089801c0303c10801c00f00b0395a5546500716120b40800b0020244050390413031851801420b43c2d40c6c0280f01440651800d482e5039402001e0784040101c82d8881c0030010360312810f544030b8115190240c1140101c07269505442d08015150b40001c0303442c0f2030020b0801e40081c0d0b9900b4401e030307035840ca080c400300c1c5013044001032020400c0035400105440321910151740d0008400d1020000c00350b80c6000710348056441e5042c020300d10080305440d5030042c0254060b410820442d21a0b881c546c040320b5042c10320080940340c902c0e26600b14480c3d03800207405804c040c014042074108880781c41400410580007006503040e200085a04c0d51020300c5298040b5440107001b2180055000c04c1015036031081c0b24240c5011345681c40000bc803541917409403480100071034400d400d107400d88110305040200301c00450940c9400c00c0000c205a20a00342820100c40c00708204079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805721789 1250 805720539 805720549
    0x110313150605191a041208070201021f0606020f060103030f050a020c06070c0e090105090c0609010e0907020609161203110c04060321030e100b03071a0a08091911 71
    0x151400030f0001c83c480c0b0b1030140081d030407a080d000e0003041c4140343c400f0406802c2050200c0342240e41842510001c04015220282c4640002205030b0660182c2172400090100c1c104801150764201301000034940d05100009281c072500701c8415900d0390000c801480403030f41010141c03444c2040c500e0300a685080d1200102c3c100b110386200580c05c21008a0960200000032103004161380c0003020710b155507030310400f407142607030300589110103a90003000c201c03001810044003c080d03515041c14a03180940c541004190325950445030040142c00140c10701c407000d001440307485282454118500311803030030b000c03040750441c81c001e8000b414011031740900c0d41d040b034080c88402404403008108100f41a561700700002c400811500a15602916107010380c0c3c0d09020b44249642001da00009020620302520701c03e00030002d03480703c19414411080006034101c2d44444501002d806491210f403103001482c03024203d100003508005942e000b0760007000801c035550904c00d449a4202c031316005020f00300360100d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805723039 1250 805721789 805721801
    0x30503040e0f090a03092c0108030c16060e0f010c1a04030210110909100e040501091109060105120c0c030706090b16120b030c09040b040611031315 65
    0x1052804041400941c4404455059208500910318032019584412100340c5a141001000f0082009840c0601c0410910500d158803480c0c4641d4500c4095600a030052800c1c1c0d00360310248141d48001030008a246051010401140e1410342c80703800e03281440005400e04040061a902606040c1c03440000b5a2003403245680e01900448001e0103103104003802310748c00500304d0703069005d4446da006004a5120070700c5803503440038400b100b043c244541e032000c0000140c0083d2904c610244084000f007900004a54020f004a10070320000508000b980b07040641010144002848ac100034010413420340d8014080342c124280d45180b240c0075540e66607034038840d80101d07050705200748000701e101810846554081c0104070300542201c1c0042c1d03102016a240b4607882504c1e00000354007200161061880b40c2c00604084500600b902e580d07009000105603080001c071b90540320750f007845041c0003c0c403065220b000c8010b07180281080c51031901d9403001d00e42c070384500d00050502c1d11581c1d421654018a40c040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805724289 1250 805723039 805723043
    0x4082e0e19140601060807140f07050d050706060504060f09020705010e01060605090102010f020a090605160209040b0a05161b1b0602010e0f01091e0525060e041406100903 75
    0x140c001c940604089028200d5000c04282c1482203c1c00401c0c11303402060360511071903841c3d844ca140404540d00001c0ca43d0001d13407031880600028030206001800901a01c6002801c03961260388491040c00c0c0141034690580c0550b0246151200c10b120704803800c5412000ea0b404500007607a11900343c500b59004040b400c80e9800785510b0000e0106540b07500c80020510321009900070311580c002c10504070100d01c964014480403950100d402c000c2e2a004d20054081045001076210100301d0b9500425041c0204460403a541085401004010302036845002d07040201c07900507641d8104203100242c21094001031024240312103031600e000b0420400341100600381c22690740303085255120006406031540c000b40a5030340c01124030340d100c2800d05120fa6000b07140c001d02d0204119890501b0348001c04c0590009542a01441c0c0500d032180e81d050070310107111021901e01c1c2029510b05903000342040c2011100f00d201d5400e0940c48103042c241c5e4000160404070444229070440080310080e611000290701c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805725539 1250 805724289 805724323
    0x12091005300610090510080405031e0d1d0a15020d020c0c1c08070611090d1104050a060e010519030f150b090105030a0b10120804082e0e 60
    0x31401c8410030940e18024070041e80d411a000c030404009581e0740c00c181c000c02d9000000d02100001442c4200314054106004000f0349142480800c02c26010303160090954001d66400182030480b5a980c1c820050250880881038100004a02c01503803a1000c81070080c04010094144012580290b0304444541d550107504550715504104240d4031380d0a4901d01c0c07413007030941c850000500143d07408061145c561000c40701d072800400b90f840d800104449005025a4034040c030030807210342c60704005030107494090342600c145442500c00700800e84000500c200c2480d410114204a001d0341c002015065403022107000b50440ea04030401a8005410b60018058560f1007510b18180640c070a040100c0c868010400e000368010b0030207000e450b101c02e04c1407540640c0704800307280114500c401a0f0380c0001c4550000c845143e9255003156003480c3d031040c143c504080000d010040d0030001c00400c030110204485007a45044102c14180c4500d9600e46100e140341d888800e40c0110520503c02c52000c10780c4140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805726789 1250 805725539 805725607
    0xa020a030909020a120e0f0f060a050a090203060a15090e0a0c1e0317090907080f0610081906181e06030f030c06270201031a1f090b040e070212091005 66
    0x1081d41c62402b42d5541488a140030301140040000c2e0141c4c24005401400900068075002c210500901e8614400303210494807000100b4a01518010102144142c0c0d004012600182c200600e2118195110060044211040040743d8290400c040c01701ca070040310f0050641c0f07503507055500500c01c1540c5158424030308001c0042e4550030031384040c0034142516450f081c0d95170320b80500c4a110440c0b68a03d001c0b8181c4000901e039108a034250082090385c50348089185550ba0307140720300c840f0400340b04480d060f850b4a105118040c02ca592950f94003a55a030602009143d1340305e0b0039404c0d048500c0541000000d544040500c0150b400201d00442103038410b18131440750581c001e00031901c2030f9040340000c0c2400075941515400710f0103902041c1009052260754440000c1e4403001206c2d0030b08527400d200b1700780c4001404008030380180000b0102e00303203c20310a14100800a0605064400400382d104007804141c030107450380407100d01081410f0500507940d4079032601e500100c111340d40d005000d48488013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805728039 1250 805726789 805726813
    0x1101050c070b040f0f0602010204080705060c031e0a1205011406031806040804150c030909180803151801080a0809012a150902031f110a020a030909020a120e0f 70
    0x25600c1120011660174920680b2003008038241d00c200d125a8002d54003080c014041481c2810042c4507210007176003100d01e0030031036000b121603040c05000821488000490100079140c0c000043d02a180e24050301040158102020300c00741d032002020b2103004100c00700c0000c0385d94010310581ca040309043c5c0104c601514003890020065071150180c401c08402003c02c07081418002c4212001e0b15502d80c81d10070405043c103e8450007850008650711580c0080050000480c42c01c000541c0911013920202655070182c10901070006c442d02158511886d8100040004c00703008501c0c80031544c0d0100b902503888072001c00403a08800503221090340d5182a0484880310304804060031b40c002d200318001c0a20300420f507900001c0b902a41d1000c0e4041c0c02c416524882c0300392038460700e200c12014000002c1c07041d4401402607620740110320500c01580c0300081d04030525411201500052410100651620215000c02000806500207030004a40c880041d2100b017401801014190b80c0407100310380c40e0070800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805729289 1250 805728039 805728059
    0x303071407081002032211040603030801030605090304152d0305090c010203031b030415020301230f010c03110705130204051201060f0b0313020d08251101050c070b04 73
    0x644501240b510aa400d0b85400700380328001e8a21074480307030b82c6007690180b010040d52400d14081d00100c0d824003c08140c000a9070740c40c880c0e02c0240d800780d6146142e41d810b51515104550015005540560090001b0003032920b0440c8008031241092800312486030a01000760710038000c0282c441c00f00840610300f00c5680f0b5061344050312a268070411901522903c100590b10792209807144400b0007502e242034081c00790000015500705120b40c10320796920019035080c80480c0c10030b030040d520300350382c8099003113500820544911070440c00701d4500346c400c3c1100c0000782c50020316042c0101030025a1501b15841c10061110030010000602000e240c0862022140d00950040c09462321401c940c0c1e8203c0c2c41c0c404144030300001e50ba180d0890700d0f1b01500b00b11081d481ba0300018000159911045040320041e100c1d40315130032403d0721800403913450390140c0c1d41c000c01030544072009c1821713a100c1c2c40001c0c0104800310440ea12040080c01c01c40e40e1101c002e1000380c1800544e80101e07800d903000107030005006001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805730539 1250 805729289 805729303
    0xd060e0a06020d0f0606230c0102070305070b09060f0a2310050109120c03140307060c031a120c150903061003030f08090d05130e0a090615080604080903030714 70
    0xe03c80c01c018010401c090002214894020303e0009032980400b0540040391107552101e0748942c0c18650300300580c10300315501b03907801003408400040707000c0303409410070405400d003940180e40640070340060f150a00e08042c02401c002c1c520042551200c1e40075106064608042c0100c03004810407611614140c002600303208000e04c078030b5001420140c00000c5c0d480c0b9a00c0ea102c02c0581c000c3c0200b10b403d10b10349a50100444c1090003815900040200e14005007082c0700e1640e0318011501c0100da42512210311100c84c20101d91164026000c11716a10400c170b401248403450108101c9580070844030008200762280901005a80c05109940502ca950404c4501101c1160f1081e6a4044010503815084a06800955045040d548201d02082555000e40081c100c410003120b100b05c440b40d80d131100001c01c04819200908495503440b118000d010300e42c0100214101403400140c1d05610300010242c8d50800204064500c0704d003c80d2001ca555011300458070115005402c15198848201d191f50311152 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805731789 1250 805730539 805730557
    0x112090309081b13091106040303120c030902010f230c01020304231b061306210b010210020f0708030f01060f030501030309050d031404120204290d060e0a0602 70
    0xc01d10038102c948900c200c9030310f68450030140c01c1a0340060750104c035130080d0081040866003424a5104540291500d2000c1c1000b14060341c0c1d1715060150310b03030b1010129801d49070400d0806042c481b40d5001750f600503605c0410800d0600d403020505018a60000b409660045480354000700004c0018450b08150043d600685c0107913403503040f00342108601312400c00112815400f43c0c00600031040e13031a0100c046e80e8034503070002d03058503e4140082c1c0140d4040006801075000304040f0056441d0710303c071000020504503040c0310b041161508080020b0b41c0e5890031518041210340006142c200342c641c0f00151142c02d80d220070301035100d0401541d2000d01c00002d0180340d00040001c421000d101e8420301940741240e416440740e100c000c2c142024403100c8910410160b041c0030701c3c02082c02400e80b0840090008000b4105061051401c510400090301e050300c0d100780603051410700401001d425070b80120365840c0d08407111030440341c25180c400c0c0a0030350300307210007100d0045200340c0c401c1c40a00c0d0014a1600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805733039 1250 805731789 805731793
    0x18060a02041403010204052107030f140c0d03020319030b15070506130206040612230601110625020a050f0109030e04020a0c080903030403050a0c0e090d0518011209030908 75
    0x204003030b001e1500301d0103036110b0300c0d40c007180c044088140c0460518007049846028025580d0b4503840b9201e03107500800400e07044403261203203045101c4c080c805201e07c488018046914034030760302258034000d58030700400c40051244440c0307001e04008903000b175015020100c0040c0066002d8400c1804445003900a84030a40c1c03030703006101c009182c04011042014110b94010300341820203052541c00c90701c031118528100302981d80c0f0451225010318150300308241e80d510941c210294500b003000105109600b48641c2c00c41c2d441301c0148807050840540c00480700d109403505e001c0c3c031842050f00700c1c54034005440281c202c1c0580ca00c4119508010340000c520103009407180200789800b0001d00040340b00c2e0f002600d0000b95000103000001c1c290100803c9c00c2070b0010102c13824180c0300e880301030601c0c01800c4111089000014200309425001c1c0c0303003039071112151001e0040c1643c4480094280c1c410201e10440725941c401000019030300030703200404000000481040300d10f05c2894064a602000d0207186028 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805734289 1250 805733039 805733069
    0x70312020d0c0c09020d1409010605010f0e180702030918060901050a060c02040504111c11010801030506011710050108100b27060d06020307120608120f0318060a0204 73
    0x940148039400082d540000f14500c114641000035009401c400d038807942c0745031682d8078020006a101c025901802e410f50002680034540800903150856003a400018442003d8100a8641d50a00c081007070303071820315162035190740d182070481c254800c2810b4654042c491100c0801c441c00740c1c40c07229204042c20303103060125989074000c1101141d0b040c46a840000c1000442c0c100500f420b41205810604c00c480b6080e134240e8210014680c02d02c0954030a0b6170310031400c451002d000c3ca140401d980f204003828025541e5065481d015141c1005004402401c2c1175400b507549502c03400c005103000750401002c100001d584401240d03407200600900c1014003420075040c00081e01d00080010b03284111440301107426581c4420304a0501d8008001c01d90104910b4542000309445000540c4030340c0456035800403070480d0f00300703078400c44a03184c100004a901040411042c1c1340c3d140222001c1d04450001140c4a50740d403c41030f10b0000060702d0741843e501030700c1c05010a001c0250007800546010f15010707024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805735539 1250 805734289 805734313
    0x80904090305130b340c120510110726030f15041401091d0f010203071106070e09090109050f07150e090114030a0b011410030513140a020307031202 65
    0xd24096642c0d80e844c6002d0340580e9401d03291040c1000b050744280e0038017443c4d1041150710b0f4401100c1d140da0200c044080b00d114480c0410409128a007042e5500c170604104403502a0040d41d9680502d00c0014000c03030620310f8401c924144a482d1030182c80940840c60707540e15103803a90011003403090f03420b03030b01452070403106002901d454000c2d501d0030000206400280ea04e810104005408020040c1343c0c0c00b2180109150111400d021014a200e8000e0016030340342041600101707041038864280000c0e0b0031410038003600d190700103c014240c0e003044850030307060303182d403d8210b0050011840080052151900e40003410001040d079200712590044101e042080303e410940308401e06801882d0300c440c90034010721801e08281001c2c10044c4014045903198401a5101c00002400b030300040a854880051000e05151081010811f081a80350501490030000c020786080801b104000740007240002d516074510008004000001d80c0007800c555401d0342e45e00309601001000e000c07180c0103008074240302d28 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805736789 1250 805735539 805735559
    0x60806030105090c041a04020304051c090f1217030a0e1e070b070302011e0b0406050f0f0409060e0703030804020a080a05120a02010f09030509130b010c0204020708090409030513 78
    0x2c4201c03d0075000d00700076404c880401008120010740380f4000810200c2061058940d480518480c03840b0b28020b200e00d904405248040180d40180d940c03c010b42e5143c10300001d82e01d48560000c40764000c0088074a4441841e1500e04201c001c1020b0a0103140401004012000340d000b11004000b44019200c0240c001e086070003800c1a0020300fa2401c1d0b011590405c034010f80100140b000c00e02034400041c038414040d1010150f01e03501c0c82d00700016170301e40b0103885a503d4548240001414100c4215080d04240c4c0081004104078103003981c400d50341c2d19164000c0c4109600054141000300c1b0a03581c8040e280e2801900c1007009070303010303406140d102c03c0102e4010303000a100c1200301d400800400d4500c2000203c4030f4036030701c0100d10104554841c000104000410b0050b00c5032a80f20780c41d09912082c07811b007881500005020080002800c0003601e0a0701d98101c000421b0141d015078001d030742e40b40b0504019000b13224038104a5005490a40c0441c1410780c494058070072503902e086481030403983c400c02d070b070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805738039 1250 805736789 805736791
    0x219090605030114091306060617100e0c071103030f0d0b09090601120303200c0616080c1e03010b09090f161b121808060408091002071e060806030105 66
    0x1481c5995203007282140c2d4589881c10703582c8405034090481c0310401c140c0da0707c000d84101c0d03800040803c1800f220580c0c04951803038540c0d4004a00400c5003542842c00700544c10b046070103400b0442c0d0903000100c14090048075442000c825a000d011617654040400401d070721b40e03000d0b00c603e0610529184058103285007211000c0d0141c0d41c0100180210790070a0945291401c800b0400c900381680e5980c1c41d80e400d1092031b50010300240800d000342d07e850728444bc107030070514000c0104007240070b0000040c1000e41c00210441c0c002d40c4045006441d072a0440700c01c48842514500c1c820841d1020000080c201500b8005003c00c50041e03034a15008c2d2039a2003a200008400d40341c0740e413001e02c040e1041004510900424103500c900c00b004007640b110540f06e0164412015956000055011842038800105070386407000600c40a40204003a00c1c00740c407046c0e490b0040140443c40303100324407502109603208008203805040107101c1e0742a15503403418543d040c5c40c2d080c41000049040c400c006489490706124007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805739289 1250 805738039 805738049
    0xe06030c0a050901060f1e0203070201030e0312010e1305060108010504170703021002090f04020316020115050102070905251701060906080a050c1908041b03030207030305031902190906050301 84
    0x1050981e420f100c406d0700c041e1004000c0604000350442408141400e588502081c1c00703d0b9005141e40b82001c3c0001000d4030514101c0900c1035002300900c00910182c2c0d0165411103c00d00e2007030384107031100b8100b030001101981c000340c080c0c8501800030514072419804640550710035807800d601c0f50344800c1824030034014140040c02507000403041c4510f0100c42c0e002401d0303004000784207841c5103036448002409c80c0c100341c86511075085200a2400600d80900c1044204c8000032001c0000e00c3ca0140002c3d40c41505000c3c0000030b036260702c040340c0035803542244030290104a410701e000305040040f00401100380030582c0f203029605600002443d0780541c001c00300762803c65840c88901d903106500b00e4040c1c5800380c40c24403803d00030840151903458001c800450702d581c1c1d540324586402c181c10034400d405103600d801c101110004900300002034001a54108036a07050130240d0312961243d00305c407031405c0041e85400c070580c0005206080040d00c040c078100300d55087c0d10303181c1ea02030315204102c0d000d00090040b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805740539 1250 805739289 805739299
    0x50c1525050322080f070c08030921071a07290103300c020406080d2a02060d0e0d020607090b0f160c030b07051315050c06010e06030c0a05 61
    0x4150b83c920007034140341a15940110803030001c3d245030381c0c40c0e0865100d034102115031100800c910040185c01401040109030010081d800c00302c03002c0c00590346d40c084c0c2c421000303241400e0352114282881804014010088040383c0549000340301070b40c56056110800488070700381042c11000550106a840d0010a20240804003460f801c6a496901100e4141d2039240300c0800d0f91841c0034408543d8909030904003481c2e8602810742011310601c001d80d0401d070081041900030308500705e060340d8422103d00c3c20418141f01003071441c001c02c107002d81d100721a10001e50440c90000307200d64404580d4202e84030702d42c0d01070121000303507021900490716403205484120001e62031035004c2119407031900213010441c10380180c940c03038000c288070014040c1e45003000841c0e111914002c00c20034401e83c07640c843c1d440604d5080080c502050b2400304000080e86014003c0c5000c4004108031020b0301c51000c2d5500795654100700c2d0320700c0d43c569110803460300c82181d0301071003481514007208940c204030944c04110392020b04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805741789 1250 805740539 805740541
    0x10203041707030e12030705070b0408100e0c060313050105090321060904170d0905071401090e0613020705010e07150504081b03010b0a03210801050d12050c15250503 73
    0xc00c10007881000030312105d451006202e6030f0041a41849000d0050503104c05171a42c0340d00d00f071400d03414078a14184001d149440d01600340f8000f240440d24030081e81084032600ea4030b6880301d00c000c080002040004d012503103031600704000102d0010083c0f804412500c0303103010180010050100841c0119055500075000c1e0000c00c0014508881903058040b00245150503c403142e210036013190b0324924151442d40c4080420400480f08424200c0c40d0b42d070038a02844020f0411807914017980015084600400540e5040003d003001d40d419580d00d640c0c031400900ca0300c103002040668510041c014056000f001c00700c84058a40618200c5040f2246500a40381807414407480c003403001012140c00d901552195180c1d003d0741d584011030006144102005008007041e8004103060341240214001808110b400502c80d6594150340c02c0313184e40d80b0002d10074440c4144127045549016983d0b441c2c01d81d215210b03000d480e0200350704085110b0b81450f0065440c26126070103070780c00c9070009040700003c298100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805743039 1250 805741789 805741817
    0x30c052707050c011a040501080309010f0e0301020f0412050c011e110c0315070314010302060f030604090c1d060d0825051c0206060d03020c040b011e0201020304170703 74
    0x60101a480781c001d08045080442c804030250030766440c2041450403400851810b4030b1890240b140f41d002d032004c0d0b4000c40c100301e5850700182540c1c104a5882050282071030103040c855800f501110561400f1910558a0741d5607804003c0402030250400c0b6014007503200c4003103031548036410300b0340c101c04550031150000b440b542080c0d590a5541c1d481d04054080d01e8081c50180d1402c006004034031101c26414102c034505045c008048800500b210801155024010405a9107200070b46000071110340a2039542d0f20f82000240091035013103402001d011601c140052032154901e003202c0b0455201c40c200380166180340c1000750300896001d0041000c0403d000d00301211303111081c003215404101d805103030b40124603202c40c0d103014010b41442401022616081402036414010590080c805840c1c01c00c0c900f90f07a940203500c45c410b03030311170500941d0344d586103d0325a842091074026240e10a5942c850b4452140c400a000c1d5108071820340f90742d23941e068401000743d5001e0483d121240c2540e900710001800c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805744289 1250 805743039 805743109
    0xf12030f190e04050601081305010b06030f0702070e0c03070807171f05010c080409020304050703060207050102040f05060309100b012a0507170703030518061b0c030307150209060f03010906030c05 86
    0xf1302082c2c03000e65a0b00300324032f1640c448a004602410140307901b06201d03c0c15541c02850320300250059481c4010800c107001c0b864084005403078100005050143c140ea61340c88007190b0805400d016080d00f24022800e0220120b084001807035070001d0b16460161241d00e4a00558011002c0c00006003aa002000100010501513010716001407281c810f445c03e50b5030b241c44502c10f036001190705a903580d40c005000c0000074128107890b0000c01091381e04904515200550f5612041d6004010380e040f51176100b041d85d660320400c040000312807032f03202c02c04140f04c0b103905100200350081c008807014815550040b0345581b1000c8520001d8103218020080b01e811036808840c075401c0f40c0451504088490050b0001d076941502805100c03a15080e15848049030848041c6040b20700502d00740290010084240030a0700007010840410b80d803c00503980e42d40086c08280380d48200c600400105c40084000300e000c01142c3c11000450380900b110314031081c0c0310310400403034a50013504070300e4820342ea0700c0c003002039030070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805745539 1250 805744289 805744321
    0xb010e0108121e0c2a0f090a0c02011b09080601092a0903020405041505010b030c04031707060203160e180a0906112a0c0f12030f190e0405060108 64
    0x116244942464413807244c29290000040d61650030058048190340d403e0350b140e20040d84001c044805000103481d20f0007180c0894805800b0501c05034651500d407114a000350403200c090841281002907144d0b036046c0040c80d078030240c06144458000c0c0d900004000c002406070110512a20010780b110194408241ca22145004960350078080700d0500000582d44610545110744d0042c0c3d10090380c03190504c06601150016046101040340600034458407128000a9505407513001d2550650601c2c41c6840718068040c00384000c0683d800001004645003c6080c1c80116014548900148000d02010031010621144001070200307032040009014201e50f030003603601c1c00d0060b80d0005041440c03c0c0350001c1680064092149603000a040e03000d81809a601c01ca108030400c00a80000d501040010703110ba844003c00c18400e54441205080191061040301c0074543c2400c0003075520b01c0d40f19541040e5034118440900400e200040d5030800e800c09008281c030890f01690b8001c030a6507202020144a28 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805746789 1250 805745539 805745587
    0xe0c0a0f02160b0c0f1b060705010212090a14190809040e0703030f0e0603040b010509040510060303230c0d2a0606030b060d080409270b010e010812 65
    0x4185103400c09204030303403103907140640f03c03e00c0c006076642900a1000d103407031180842a8080d0303014010541003c1112410400304c200308a585c540d48a042c0d0418501902032440d48100c00800c20041c09440e9400080c0d0785092881030341c1070345900000312403003a00c992840a9015000015181ca5000100e82000074540c07400000d10010f00300d02240f03152440c220f05c1d60002c9020414298220184a42000e00284070070f2045400a1461809980700d0141400601c15140036403200c001040c1005030600030b0060f09090700e08100b195039581d0500500510282200c0100e115440c8a55008425000201c82501e0000c00c001c0c82e10017482181140c0b9044402243c0c58604000d0007580c9080c111040d404000c10300a0b4004a941411814100040040580050700c20180c081109000030490303020340b0115050402c0c0014141c07455000520a03102d2000d14101c280080350140040144d03542c42e06060b24404d0303540b0b0804c1ea898400c0a640c40700407000b0000307001002e0111f41c0d140c6000c0811a003940b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805748039 1250 805746789 805746793
    0x510060e040b0d05030c07170c031c021e100614010215040309050d0c08010b06130308030c07080d0c0305100f03170c0d110d03050c0d0207060608030301140301060e0c0a0f02 76
    0x640f180e00d032030341540c204d48000c81c03254014420402c041d00c0440300414255074100003400c100391040000a9407884a0314861085030340c2003400d0300e050b81c0203024a00c084280400e030030342000380705002d00751910051404004283c2c6012804101e400ca0b040e0030204c000310680080080d0341044510540b10b080090003181048a00c0b100441c254a86c286c060700f07143d104100a407001c904100d207007402d5031003664142c3d0060342d00b800a0910308220850450032241c10000f0550b1b2500e1b003203507514083c0728045002d0841240003441300d4080d2000c2d03000381c550310020f582c20046500c030b1a40d4404c4140c0b0602c00c1302c0d10385c0786043d01440428561101d514120f520024402e182c080000c0d40e170380c2022003901c8200082070000301c14100001c001d0260904074011841e04120f64a40b5040f08455405138140c0000480e0307000c2190710401000b0b603c45409010184110707920703980d540801401d00001890b9184c025400c10301e0001e46a028802514010003000e50540d0519440c2c0743e04607581e038200700c0654214 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805749289 1250 805748039 805748059
    0x602030c061003031d1f0905090f0405070b0c01180308010302040c030614060d0f0903080603060f010819060e1203150307030f060c05370206091216240510060e040b 72
    0x3107500d10031074800d00006c0d9141c810030985000104070442034010b11071120664a5020080050400301e100c105070f64140115680b1740080c0c40b04607004107003076000b007200c11403122084400d15820085090480e0301c01c5505101501400e41c0071010b4412911400c056000000c0444403945000000ba0400c842c0c1860f000030008019540a402e80b68490815000308441000b4000203080c1440840d80c0003c40509081071545030011207681c0f601c032000c01c4a024a850740100007008016000020305800c10000c99820803480709451450f50300035030301960a2845914000010306010511004a980081e0601d446040d503031101c2c00079040400c0200104101009101c0000c0c4004d800e24901640144100d21441d1042582d150903511070f5004006544c450303130070045540b000041e040007a0011362012504c9400411f031409010088640c01420f2880d51400d040540008096146600f1a410b00a101c15100c1d036540303c1e44409540a030100050b0101c02800050500d508045080312000d0f0100701c01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805750539 1250 805749289 805749319
    0xc030f05040807110303281116060206060d0c05062107051c0212070f1e0804021504120602070c030c0803030403020d0306080a0b0a060b040602030c061003031d 70
    0x11035030112400c0b100000045000401d04c003101d12000c0d40c062007540214602002c0004040da500101c0840d80c1483c101c59006440311441940c06940100c40202114141c54852819400003041d40c0540030040c81b903200003032260700e001009075001c0d54019450b0991a81400c05001544e44440d801c859001b510300001c1480504403d80a48150b813943d80312510f031030302200030aa000003c0303c0081400e81c0184622220042c2e00080290080018282069803559415044d00c0c4600611911300403009803021540c0d030345800001c1a07104610841c0c840b03549948824103402c6600440c00341d045814203403014800040e02c1c0f5401000c20354040c110100e0318036903071341e1840e403030700125040001141c0012080c00f08260301000308000319515814140440d07418550b1860340c034103150001a0441241d0004102c6c1c004a42d03100c040540a20000940e40b9501d07010065aa03602c00d0700d07880c1a81c49503500140c02d10140406140549034140e941a070900c00070944c8003000b48440355900d40c000d13406100301e0351b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805751789 1250 805750539 805750541
    0x140717012603070237030b0a0506131b090e10260d03060314010915090804120c06020f0f0607120e060703150e09030f160b0a0617010b03100c030f 64
    0xb0224040c500129515990b40170b5520b49408a01c54441d0f800c240d00506000013006010f619074096644a0000390381d940d81d10000318071807a800c4040700ea00b882c06a18880b04502606040080142a2180c0501760350b550902c01d03040c40100c40354070442a40350340502203110350344540c01c0d802c11581b03050300d038440e0242103007410a400e10540d1008250307104020404c114036119000100d02c503080c0204030b98281600c0d406489041e001040c050256038200510030480c001094070043d047c0e8419140e401401443c00001e0316889005000c0588218400100c0100300010840d1030000b44e031000d04000d4036502d006480f170181c0f0304540451217890300042420b0020400c4603500c00d040c1580d021841c0c0b040b0400858840034190000c0c00300408840c200074119800108603210a0f805c00c4a007a59405400c1d40c0c104001d410f0000100004c1e90701061060065030360300214213440011650003d402000f0b0740b510b0880d0300d41100350740c05070400c0c00c0d40c030241b51a0b81d1107403070003d6803801c02241d0610210b078490 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805753039 1250 805751789 805751809
    0x1d0f1807090f02030a05010923180601030c0303080906160c03030f1806110405030c13180303020903010c0906020c0108090c1002010218100c0b04151407170126030702 73
    0x10301c402e54040100940250f140c081c8a004001b40d107020000c40440f11001c0240c01320710700a0901d070103d2031002c94840841111064449c144038800e136001c658503450181e403c891030344016800909010081110400e010940340d01410800940100269505c6025030715043e01140580c00c0c1507403114a1044007096009403140c102260448805201d038601d00201100e1000100d05080c1d00d00380414040ca803000900440c02e000100ca0b603000702d04101c900c2e01f0140c030901c1ca22047c014490b501c0c40307040603050740140842d00d03c114020700c404200c060080300e0382100c40c400c1e00c005a2201251441e554003d40c0c0080e0414126000d95010714008404500c80c07030a0b005c95200180e500050140558000b2000c410900c0002c40d041e0a040a442c10000e00d20f11019002030514803a510100e01001001c10828500081f201014482c4110084e60268451011034480d8007040310503420083d4801d803102454180c1e008100d2158040145079120003c00d00340140c210007600c020801c04004d6035942c2102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805754289 1250 805753039 805753061
    0x60a03060e0a082a0d02100b04020906190e03010c0f0e2412090706020715030905060c0919030816050a1a0118110703110a0c030506011d0f180709 64
    0x4c0c002132121501c070160b0a01d00200040c030341350080150000e1441d40803801c0c0c00595a9180003003031102c01840010300030b103d058000d550080c00019006445e900b414007541911050fa1243c0d4030070b4000c8028542658500e00040d4005565202c40c04415070003001d403180c04050140844005500c49080510810300c0310052844003800800d102c00b42c0000c101d21554055602c1c0050709106141041c080e554603103c2c000c50006414441c8031096007440b0740d000001103078006080303484600304410b0a43c11079001000840c0a00c0340303028844002901c402c1a04100c80e03204084619100c2c810142c10b17a0009030340001c44040c0203424064010602d00110b1a0b60101104840042549030a0122400040c00174078580b80310304007c41011000c08001c00d55080340e4160a00e001580c2c8101246030030003031345a50040c00500212804824040700084060680320b030103641da070703240d08400c000d42c0003440116104889940c4101c000f449008042c032440d040f44003031130110340c1e4441e110642601a40c0070fa40704 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805755395 1106 805754289 805754317
    0x150702030c1504060b061602060d020c030403120e1207030f030e1009080d0203040308180411030405010902100c08030f070509030d030b040507030203060a03060e0a08 73
    0xc607440090503900b6075890307001d0003032224412a020b8800365040d82c41c2540c98141401d200044810305441940043c1c4041d40035800c0010340e40c4001e901c480391980a00004e4001c6c4010005007020790f00c100751021034480c00d858014840e000400009202d100c2c40005100b6038200402c0007410ba0b5004a034210010507941026039800c1f02c00d99039960811003840b141d081c00303513002401d1010380740940d0070350302851180e4400b00d82d640158003001d00003110800030300d4a00c4400c3c105074044507001610220b040c520802d07141150750411102a540c0f65142c0d20104e01318586a0621701400b4003900b000031410f009034848043c40e001c014211040c90b402180802c142d603019405981115200508550078402000f5009018224100400c3d0241e400c140210f81242d00038000d60b407050f4030103400c180a80b4610745a460240c9480c2090100d20301802d40800013080c1c0c11001004030b2100c1081c = true := by decide +kernel

theorem cover : BRFrame.Cov 805575539 805755395 := by
  have h0 := BRFrame.cov_init 805575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805575539 ≤ n) (h2 : n < 805755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
