-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:32.052525+00:00
-- url     : https://prove2.me/submissions/84ce30ca-dbcd-4f45-871e-3ed60db550db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582194244 ≤ n < 582374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582195494 1250 582194244 582194251
    0x230105091605221d030a030b030607020a020913170f0a0906090302180709080a11120a03050d0e010207020a171b060f0306060c010203010e01180504080417280c090e06040209 76
    0xc000c2d8004090003644e060540d044001c112000ca83d407812450f4150400b48030042d0302506500c083c0121400c9540006c46501000d01881286000b404c0305100304011450350180b0010103c06003a103680004c007901b00d00354800d603520760001e6440000010308074060008403007501c1d40103110245031401d04500010a1034018807007001c21a80c0440001c9100c0c1c1030200e010001d00402c440a480c450b20302c00d00184100c14106001c040d4000031600010980c08410360716540b41603031000c552a510b98500c1406409040e070043e41c0f05034a800c001035050745104903500300118020030355450f10041d4111552510451006941001c0c0c07c0003a0312022499400843c2d10900082010f420540310034221804ca070000d800c2681082001001070100b0350701000410071400002e07000380311502d0150344909290080340304064225144184442d50000e0900800e4400030300d070b400105003026209886105900482c2e000c2d9410300300303441d000c03888807018000c1c1420085144010800d588071582030103103141006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582196744 1250 582195494 582195521
    0x303090e10090e150703021308061e040507150302040603050601080705160203100911211e101103060f06040302030c0f01050c07060504060e010e0a0323010509160522 73
    0x26444e00e0907511444a000340200b0595800603151803204200e86c180fa041d9401c42880c3d0303441641040b0104414103402d40032000030698104843e1114a4103515000b2250003951401180c0c103606843c8c140d1550250040b1034207640c05020b152205001514800301c141c500c80c0010744c0c1040302401000c120303444148454805412900c821900b006a034088035001007040b900f2000da1102e0703000c280b0740704d0360a41c8807201542e9500c2c0d100e030040000075602d1511001c8a04900390b2100a84203108051081402c40715102c0c8042c4000c426010a0009617401202c2c030501c19451108050440e0800005075400e0700d074060b008040b40e07804c8004010200d01034a200c83d041020820520b0810a800e00c4504002c0415032034068541b070502c0c43c0075105103144850641009034121040c2160741e50700302030004498204c0810780d003100d0401c4286608401c0c2c0200ca181039800c150501120310000241100300e044000c504404150b00c4004000441c52003056140225118a04a6907140a03951103c0a4600074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582197994 1250 582196744 582196753
    0x14040221060c070b07140d050a0b120601060906111002031f030c09060905091b0111031b06010512030a0f1206060c110303030603032a0105010f0303090e10090e 70
    0x403031086190010450780d5500c2c981000c12a0410020081c80712038122402c0e0511000e403500c1d250055849000340c83c81d15040235150700200b14032449590140700311140290500390404214844c81d5a07600003881400005404c01500003039035407141100100c441e40c6113000e80100c210054420b0042d4001074550013012864029490205032131134170410096104482d00ea184500d0010341d9030846815511000450741000c007000100c80e80890244d0140d80064103000c0d641c000d06004031419000301c40c001300248000904080002c0b0700324400300308010400201e41c0746030380355000e02030311070200300309845180d10a0021514490264104824040701e500d0030002502d0030b001030b00c05480c0694800404034040c0e08411090002a4252410f00c4005038021407460500e01c010135980c0c070035200d440004242d81c843d84100b000300c202841c00ba800d444c200a02c11940c517120094030410a40c4800c1340410880e480009141d1006040301d0300c10450030407450055803070003c2c048003a000286244c02a4081e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582199244 1250 582197994 582198049
    0x302030406061502150a0b0a03080c0106030602030109021e07051c020c10120b0a05010504091802030105010e090d0e01022113080f01060803090d0303240914010603140402 75
    0x4002c985003084040f81d90042c0a510151001c9403030212002d400541e0140c100100c240444d00c400b8a01012681c0c00f20550f952280c40d000e43d1401881c0b41d400040030741c2c1c0004000162900f41ea000340c68440004001e100040d41c0800c121001e41c418446d0007031030758000062000b030055a03240d440648444500503100046940310010714208001c00702003000c61005074901e003402406e44621007050704190f038044d60903811300b00045c146014500c94060115154150045403107125034000c0c81c19030f0301400034031155843e072000505c4454101c2d8101150320442d40b4100005110301001e04050304185c02600c18061104682d60740040d800720703003000c1c40d00104401b16003031280d03001800081c60488054070344607001100a80c251010f991010301c180c1d01c2403004a100365116208000501e07450f044c001021500500c0c40300c20454000c050785d028080700b540000e020300043d0044100c642d8078001200311031784c0b585030079030860300302c00742d840070400380311000600500300021040e0b14401000b108046024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582200494 1250 582199244 582199259
    0x1b0516060c2304060e12060f2a030717040807080f0708180f0607051207030903020312070303231b160c0806010b04060807052101090209030d0e010f030203040606 71
    0x94004100b011030480000c0c2c10441a5407080d017141d649002260507840400482da202d035520800130301181420141c80b400300702046022a004280c60242c641c0822211215008111058101719412800b02e058000c0f2110401541c03001d00344141d50045407d400e0002a41b41c00f0640d40005c5100c17002c00904100c4640499905406401c2c4c4c51801010050005d0101d0f050181d20208440c0440c059403041c4842000698045401c42044e00d03406499512074120713080031100310308150300103034141c056074200c0f00c2c103400580700400356070740251800d106143c0e032011940d42101e210911340c6035058040d004101000181c944901c062a84600c50905249484061071891780784400f08849a00410134200301a140030300840b4018814048841d00b01480e01788050041040142014100000058802103074405e10140340b43c02900412450015a10749044000039484010003920074460908107c040c68421300c443c0000da02c040e9a041c400709500101070b806900b02a100300c8001d07485050214182e03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582201744 1250 582200494 582200537
    0x5011206090f0c080a03030b040b0f040b030703020405100609080307030c02012d020708150405150907030c0f38070c031a041202060f0711030c0601091b0516060c 71
    0x4213001009082c01021624000d0211136401a405000d98102004001a03a0b540344180240040654001c200c0070155030020341040c1040d040254414500030a01450b42c50044070782c000c0d00c0007526030345115a2182070b4290380c0c0c01078150003400914010100b00040d486811200d000391a241d0f182d03148804440c3c603045880c507817464980d0041c0e201440412040c00200203e101c4400b11507030b03030005824507869064664504400740440d80c144034005c100c40f444204401c0d002150803c0320710300803980320248a00b558441c2d2241900c0e4038408200d4070700703080c8903e030320103060708803030965103002c06040d00142c5090300005e9042c1d45035180c8010000100380c1d13001c03801840307480f4404c6d0101306261516248428200b05040c1e5411544541c003048405824801c040d50400100d043c2060b025504010043c03442c45030603000c8120b401a18000203020b41c4a0300058007442401007408003050098031304561500800604000036041c0410003404100f441d84020490300c494684010420040c1300c42c147054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582202994 1250 582201744 582201749
    0xc142205070207050103090b01052803030c1a1e060d05010e0c0a1a040605031005100e0a231c0b071d0d1a0907150206010e0a05011206090f0c 62
    0x80d1110204040303968103116030300c003400302420100000d84e09a1500a441041400b03441e01600303c0e407020403c101c035000c0795160384080208880017101c2d181e14004004000c2c1d900e0841e21310404200d22803070042600c44c268404d80300486442c080c064621108071131200080c085940041240381d0400c04a03800303010b05e00d405c880000040405550355800c0c0f1500118a9000b0729201e8500c5201c141e120100e002250300b240d950340b40483d02c0340c41e0913901c921460000c0d4003065004145803864080c2c50f800c0b47c5c1115100c60b046404501d004d075101141005610001c4407020b980c600d10048040d9440c0c9043c0d454400c11015003542d62900c0ea5540d000c10181d82034a03a0008100011050105800c0d4080c86800e082002d94107000c501d5065511180c01400303200c820154802000002206400d04000798001403600c910300009003003480c1c40282d1174007428020a00034255400c0060009541c238060b05048138031a1000e411209aa6101c0e8001080425811555110441c2d0b03100c0100340c1c41d0408801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582204244 1250 582202994 582203059
    0x1107061d0d0e100203041d06010905180f1006020706111c0504090e030a0c140c0a062706020606060a2c01030e01050606090f040906090503030108060c04030c14 70
    0x2d20b14200b4204080941185404021507104000900018200190400d01001c181c03034111101d4444100588441da000d41049400019004005a41c0100848028010b04031a22400e5840d01d84280004010dc1c0600078040903a00600c41000480c0c4038401c02c128044003081550034030107900d054000d0500c0c10194200006001140602080443c3d100f0019284280c50041d45090081100900403080f01203000e007940c1d80125041a8244040c0280200c0010044c44202182d49409000c2e00c04071040e01c001e00d01c0000301c403880603215124042c1e6000d07500070fa002080507075038010401180e83d000f40400010801000d119a0409001c1500310031110512560362034544900c00004049482c951031014107130381401d052010fa9104c2208440044405584075080700d6140f030f0114010300283d460003808a031924003010709129010000e181038071100d000391995500c5260890a0342c3c081e1340000b5103d980b11240400101c0f02c80c0013210000200035040616015982000c1c0c011500c000f0003925 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582205494 1250 582204244 582204257
    0x90204060311030706050a170a090204050109050a060b0715110408060f0a0507080f04030e06041a2a03270907030c0e100504120f210201050601031107061d0d 69
    0x3403040c80c081c08040068603040c60a0380c10201f800310018003488141d41c4200605545001085644034250840c0e10401d4010f0800c0c495540e50b0103064000b4501218501c0f0483d21700080420618030450880700e1051704000440100c2c000301e4030340c10082036950000c1e004901d0030040041e40710800e2002038801c0d40e040100c14402e140c84000c40f02a24801440e100c100304180040000f658808103010390425010725140c0080010000407a0280c4503c0d000003580b0356410401d0480d10f03178106c00800b0481203e00420f0180b444801d103150384521070550840d80c80c0c00030b00c003e000480340c05d611540c198001ca4039032140e14080101150036418244d0781e042c0069144c45a61075002d4200b803060040c00003e88280549443e010002004d034065801901d20740643c1001140c280082c2c00700081215270410400400008200400380144105850040141d400c210015806600074803408441002c0052228036001c0b0990348c0c140107242c012b082d420350400046044090f0a400c101345a1180500c2c2c9808 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582206744 1250 582205494 582205523
    0x1090c02010c090302181f080a05100501050a03030c021503040501091a070f0c060e033705040506070314180a0e01050307152d030c0903050d050c010902040603 70
    0x9094908510002d018004081402c10040c0c4540c00c142c92194100c42c0406c5094460f414140071212002100d0490003c2c40f0700081a045001300d82e0440c400c0c42071049488000c854007132601076480910955034000c070340903400c1010a00405880031441d10092481c0200700c05201d400103250003d0701c05503400d83d07481e00c40e6010002084050700400b1181c042d028a42d01d003440c80140100aa01c003e481042094007a80c0d04001017a00086402040e580a40c6c1d04c610b0802100310800c00500c03014060026880c4442000303020100e5552011441076440516042c108800e12401da409a1011010000394002961700c1c0d50744c41c0c024084211034004099800c01092040200c824079581203045106500c10040015a400041d01811204036013400340b1048000d902c103841e021004044031000c4171103c03820110300c5054000c50601000241c030204003441a001c0c04584c40e009a0200400c00d600420784804128080c1c006841a90070080c00800c074190994086019a0000d46c41101d200d001c0b4003a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582207994 1250 582206744 582206747
    0x130f0c0609050915130b0d0b04030f020706050a050406270f080111033d030f060608010b01120f15030b010608090a0803060904140a0c06080c04050102060109020f04050901090c 77
    0x3160000f2558036800741c03822806000030801d243c0d0300281c20304a41c0d5490880003a40303034082c403a03140d2500b042340901c082c82c0074203026261000c019175840042c0036101020030094002c100b540c01c0e8a55590f125410281412400d60300144401031604d6030102034801c29500700c00000d00d12003c0c20005034400e030050700e000d00042c00e4a404a00c0c20252000c12700410021004044000141318644c004046a424070039120460403040310240c0c5428103040503010041c0082c1044c5034011511840f010030680f03594510b0b1600b00e5201c04e4150740001e14400f03020110101680102080c008004000111040c090100c1900300d2520340c412555100d02c80010490540c20071403c50f4080c60200103464101c00d5075a5480d4148070042c4014031030143d20f400728003841100e2019004040414007250140500c1c1e040046100c402c52041c05e00055030b00380001c0d07100c1c50130019603084a0341030b0000d0155908244e032450103908017640c80c070270000081c00300148603621410914000c2148200008084108400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582209244 1250 582207994 582208009
    0x902031606270305100618060b1c0902030601060c020118050d02010f11070f030b070e2103070b07031d1606081b0708030108010b04020304020d030c02120d020c0306060405010806130f0c060905 84
    0x40200c2d5143c0030041100141c9c5004950340061611103840250001c400b091004010000d4007030b415201c0c160000c43e01c1ca4000c80900f6003107000362100d00005803482044086207141d130003100d800080c10f006410040d400303030341403144150503802c00f1244081060003091601c1030690011b0545000e000c4204280710803d80096003042d0146041028a00d030b202c003144e034610242d1f0020180f48006031095030f06502c14400e0b00c001d207510191118a0b403d120b800200078180605000e45191030602030b06400c0400001c016242402b4040b604808c14544070003030b650528020300400071034000c0c40034405845001c42c001c11005100e202d0298030795041c0481c0c182101c11003c80302d4040c902c104144400750f610704500c084102e80c5441c011400c1402d074800703e507841e903000f0040c400c2807080110140c0e8450b00481c14500004042d022110280d543d20108415103c080c414450646c00040100d0130b021414107152288502600b8076601020082d0780d644880c0d111603128038000f5011000a1002d40741896 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582210494 1250 582209244 582209279
    0x714010b0f060f0702060a03020702120f060712140115080106030b030a0209090c0a030501020c0d0302090a060e030f10140114011d0a0e01080109020316062703051006 73
    0x40080240d0880800070403120101d6925140c41000003141600c41e000c00e2100312400e1603030152009803900d01000c0050042e400051049110b54103100c824080c01400081741c01e00003000800400b02c98440e120184c0c1e241060070f42c800f0600e6140c0c5101380d0381c1c0400a05860017403444581d000700b5110600c00050403440103800c0342c1c08050401048444d640e50001c0c6480d02e00b60121420405504c690124504d40003403c1001600076040c000c00200340306066019041041025040d140b8110341460101d00324414074a40c1e5501c07407104a4140090340c0b085040410071000901102c3e00c40407226811803070811000d002c04089901c0b0000f0141503141000090b004298985590400240220000e8040d03c8021410300340f6513200301190076a0b986190316030000307090301c0308440e69950319512214043c010707044041c0d0207403182002d2008208002031103401140c11550f1440051002424008140030796000300b88600c0f00d4044021000c26003c0c0201650604101e000166140c6421000c040d0400c219 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582211744 1250 582210494 582210533
    0x1503060609070c0303054602070b0c09040b06030f010f05090618070302190302030604060f0e04080a0509210c1504060c151404060e07120210021e0307 66
    0xc02d00081c0d58110000d121503540c0742c100801d5542e2002c0148000c004200416042043c01200007482d184199201b07109850950415881e00200c5c410f15038141d00c5541c2000380300c2c001202c0000c0e000c590b04001350901110041002c200c00c00c0d040002032494009581d41d55504142d280108200745c4c2400d13034000200300580b1a440e6a24010380011007030503129001800c254000c0d00010910781c03090341191168121a0540d00440d1110304c00100250000c41d0868056440c00c0800318081241e02c00034400c6820031216800140c0d40c40c1e03114840360302300381140400d1000510540003070395506001401424580e00c03100c0076006410305454608502100c91a0207203c039540d40740f002c0c400d00307021207042c3c50b943d05100c1e103c0d0001d0f1030202c20f49001c0820120fa480c3c6050aa440d440c44400a03050040c0d0046505015000c203142141c2c3d192500e40c401c10840542c00540381c401410a021400c00117900790040c1c03444038a8080c0c00c161643d02e82d00041c50740c0d0b040010000200503d03000019049100d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582212994 1250 582211744 582211759
    0x121e0c15180105100b1c0b1009140a05031c0507021f02010c0e030309010f09050603090106060f141e122e0807120f2103060b090a140402070b15030606 66
    0x801400005c14850b601003514009a04031034500907481642040791010b0300541040d02504880c0d0000b009600309000715110540744120207107651030040081819600020040c01003805442a100320503403516411206010051104101694480c0842a50700380d5140c012141010740300802403c40d0950b441c8075041c800310300221051341e1030000c1501c1c07071400c0a0802411400c40304006540003142c41c6d000ba940840001300308220440d040d001401111142d44440d106034000350026180f00d6180f9801d20740340c10042c0842e8000354060004402e1400083c035880b0f107005280c1c00c88000b24070040740c55060040040b400807a0300a0103881400010301030020496000c3d09001c0002e0719050389200e40d01d0b10300c003440841401c0c00000d05409600d80d61180c2010000c81c9804552940008c18224010100b854442c00142c021100300c200d4406483c0240301100f013909101c03410b6002d0170b8042c489a0020342c240207010001e00200b017401c0c086d020150705c01c4c030614043d100701403826400402103400b40e1007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582214244 1250 582212994 582212999
    0x3090b01120c150c0609050a02011b051f06031e23060406050c0c03030a0e06010905040809010f0207120c092003150d02040903080603121e0c1518010510 67
    0x2640282a015542c004404419900c0b0240080320083c40c1040c014001d40d250a0160040100008594011314400e2f03c6500f10319000c24100040302100040140154104d11031904255803102203078031844100d110001200c0e0349944814603c181141d244084001e2400006002d004150040403141d00e1a4103004a03555200e030400c3d41c070b03480c4c040c10003040c158666000c10116000c14003605c2d0010050021a40c0b2490800e5024000c0c014150084031103000300c50001c90046c001c0d010f1103214940080c10076203420000401150401c000e04556400c60003a150041201035007024081c500901aa24145049091018001c112102ea0f8088408500c000d000341084c00c4090080d0b1303900c495071640c20340d00e01c0c0c00c1c640411070201105030300075031240c40c00b07048104040d001160180244001e070f04960031071555681c090b07024404d4944900501d5100a10944140091002048900c12a03001d8590801000c00301031040b04c020f0350f030100146400245001e1000b02449503d500445800d030181c00c02d807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582215494 1250 582214244 582214253
    0xd171005010525080a030e03030c12070903021207050102061302010c150e1002120601020120070204020408010c08071106012616032301090809060c100c03090b0112 72
    0x14103403241605101c4042121031200c1e40401c1c840c0d4210f460103140e2034040c0c68516010740164480710f030140c042450b28901c0300c1110310010981c0e20500d2800c00131031501c22002c0d000e407030a1000034505001c01801c10808030042e1107026200101c8502000200301c2a401d1000281c10014000c040900c001301c00d440510250380c1c002000e59565800c0250f0106040401000c007003d0b0145c0080b2500611035290460030f0f035060b550080c19800e004080b1340c4031076100c030b100480c20785400d000e480204800c400c1e0743c1e14201401c500104170152001740010701d883d56802c4c41d6400d503901092904049034032001003119080e04826800115443c0401600403581810341d1140085c40188442401c00b410340b0464205510400c00c901c00e030340f131a1000031616650791400b202c4120f0030a0502e04800c034650401c48405005000381101c00d6031110383d450816110340c0a00110b5080800342034100e106071181058100018801c2000b0142e156034003041004850030400c00340401a0311440d01134006c40603640124 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582216744 1250 582215494 582215521
    0x307080c0304020d023307050a3c030f0302090a0509180a11032401120f0503071b0506040303080a0b06040f141906020d030902060f0f180103050402061210030f050d17 73
    0x165400740003084029086040640b500309500c0c20886490f8100c9040322010ac400307074601e58040e100342d90300c4110140120b4128140d0107080046904254103a0303051146d0300d060800305074804000c2c00207505100c0c00e0668280b038048504010f68600003283d0440303503241000d11a0000300c1c0d01000ca480d041245000490f944200140f04292801190307021000c100700300004003202494108003181d40741d0b815811300459460400308141581241c80100080c0d509122080e2011607405444040580c0d4604040101805c48055481d5101c64101301c08a6040580e4120f1400784c004040c600509034084414000c00c07000401e8072000801c001c02c010030120740d001443e40c1032810607103030100c2c035540321340f002c0703004c60103141003040d914200404d180188203008800b402c02e0315440340b00c88000c0c81c0400e0056088840548019401c25020086200b80b04424030655400c09002c02d00d850303c150740ea40310100d004101ca81c00310303000d030021101a0501036010003810080801c10380c140c0341a04141710070003001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582217994 1250 582216744 582216763
    0xa0b070c03060507140d0c0e01180605030c091c061802090408160c080d12060e0c1b030d1a010f120c1709071a0307080c0304020d02330705 61
    0xc2c54075840003a409500c1076246901000f15414029210340c2d00403c14006070a4172040c150000300d0001200300c0303d41c400d84504e00354082490780d000c031650900034121141d900c01000803100b00c50030040025203450701c3c81c803040b4009100b042c0b610000b61510340503003500c0080c5100008100e2172045407000da81e407032240d141c0041e80031071081d641f40c0000102c294803001850016040c4990140300042c230b200c2c007061860445206580e0240703078403105040c1004980340d82c02148407a203203800000708c81d00161001415841c0320074140e48003c00d9940c08440c91076004e4411000e0603610369802240c0c13080d16035901c02c0081c1007400c100c00c140001620041071807100f86090a10706464852034114540624030f1105002c004800e0082140b51100943c2e98400b40707403007000701d96000540e03041203950b0030070b050342d004241030360311001d10391604010011141c002030400e0740d112510003034140069658400c428113800c260400700c04404a0403901c00e84805460245500d0286c007000082d000500c04a02c1510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582219244 1250 582217994 582218003
    0x604080706020f070e250c020409050d020d0903050304090c050d020301091401090b01021b01110f06040507210f1502130812041206090501060e0a0204090b06070f02010c240b0a0b070c03 81
    0x402c03d22200100c1f1099036200010390000c1c90b00b4038000c2800000300342a80840d120341c00f140e000c0050024100c40c1035034a0f2101418940040c4820300912000ea04480e4a007042c500e84103040a25280111080380d1003a407144e280715a5420f844000b1040c0c00a2160040c84200801c000c4503c20600107900c50303000030242e43d401c0e00b0300c2202c80c240341e0144a071150860280c80840c0c4607440c10081056480c001540c0a4410741b0620300002158200c588410030703240d500300002c5040d078515603600c802c42200840d0880d41c0e442c0c1c46000c14000b0185101900c00c8680c0c4900714911a03181150b1541001c04003070b0f95013000c040800042c040c01d02c0340006010740ca64013407000181c001545c10481d0043c8195080b8455030050042031101d44a001c0c1c0151044d0b8400380020030041d408941002240c2c41403800050901d20400d4405004d58051810020030a02a04280044040c840042590b01075900e13141840030350360344000002802c04bd101400a004580101071410525484d076820b00c0b00a40700040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582220494 1250 582219244 582219301
    0xc0804060b011b15050c03040f03080603070308031911040605041208090a15030c030519150503030a0f020c03070b1b0705060304060b0f03120d0b0604080706020f070e 73
    0x1d003541d10035200c0050448055080011001c0e251803c03608040b203044034607444508010225617910184400c07640166032010592040c8100b5603800c2c1c0b00140c0091080740d141c026002c0000101d07014400840c8114904103d00c078401c032855405400311080c40b510404500d2081c00103101c40c9402804032425602c40c44080302c1545001d1900020354841c1d100c40350381000080780e0006480d246020307103c0400815031400c0c000840c10900403800c859040300c500d280e0b0042421030380071010456024070015500c0c048150380d030944620220b85503a206c5c1302c0000009440d140001e000d00d6051051a4000d10114007609000703280040e482300c0d07130080d4690110202c0d00102d40e4030690008028440090002038001610b0703140c1800c2c000000c002840c0307180e0080d06022900c004e145030109490219500c9003441c282410f1603420440002e11a05030a1034004104100100b1004001c1001d080100b03c3c5500034100c000000d002d5906107081c42c0d100030340c00c01030401030010240c203603146150420300354961030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582221744 1250 582220494 582220511
    0x608090f0c12011b020106050111010b010503070c081308061b03101406041d010302090f091527010f0c05040303020309040f09060905061012050c0f010e03070e010503100c080406 78
    0x5500400000d650884c0078207a201302c0c101c0c0d554041d08180300b1510709032110001210081c03040742c00c0c0e130308560b146800100f040002030714490041d030b0001030807402255810b04160304151484206001e54208103000c1c5d10042c1008078541c24407040c41c88850310b0088241c01d42c14283c03004007244c0040d0260301d80c81c1500e521080ca207a26103c05030740047c07682a2602030f20b526400c0d06070300805000c0c0410381c0518045400550020408e151980c02140c030040140001504a1640c01c84900040c1007040d20481500c40b41c154015100800c181120510000081c0075250751f0f107010884000100050600006000400c04683c000c01075901580c0c040d078003c80c211111903458002814003041c0244942c1c5000c0410341032100c00180076204850340c040d60154180c0f40e240703400d810070000c071006003542d00515200bc0703070b410b100f0030020205106042c420f90f80480980000c2c100b14458101c0402c62201600410141c80d04005400f4007003000c140c04c202d40101250010040f20005002410081c0c460001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582222994 1250 582221744 582221779
    0x18120604140d083d03060b0f030c0d11130e01050a061a030403021002070305070209070302130306020c0a021c050d0c0c061b0203100b28030323030403090608090f0c 72
    0xc9090740207500c4210300c0724010b0010404c254151600050707840e00d103861051450b07428591412624040f00600510f405001107040201405090104807070020070b00e400300c0220b40f0352032101404031840c0c1e0310100d84052001249402c4540040c001e5580600340101000320202e00805040700d1140b6410840d07481c0c0c2c1d035007001d92806000d500c0600700300340300248290a040d0301c00c0152161601c00c07201040c2545030307018210141d0151105503000a0222070b400c10011301c0d1030340205544c010417070a5072024011500000c1b0790340c03900c82400c15207400b4004200e042101c10f00c8210f02a015909194000d60320949580030b0203459030140d402400490341c410712b050700c003208543e100e050307009044032200c1c580f801300d04014140d065031417801440e12141c0d0941a2035a550394490b04a60a602c2040307291031030b14221040c940120303e04082e607000308100324500390100002c5216601a8641118191070502c0040c140800188048001e41145003100849440032502070041e06088604164010b4900d40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582224244 1250 582222994 582223051
    0x605090a060f031b030b1305100525020f160e01060207120b04050c0d080a030b0d0203100510030b04080711041b0f020304170705030f0a0305090618120604140d08 71
    0x302603d03000900b0b082001213601c7c049071640f034a1045041d901c003100b0042010303080d181c06a90480c0e00d850021042845c005190404101521040c81194103000c5140f0905080c40d00070300714007c12030a05102881351447c5d0200c41c500400e564401411030303d240500d4440d0002c500c01d0001c003a4041c0038041801d105082003000343c240c1000f001d00e19140b6041c03502440c0d07039000c4242200070070300b40080c6513040d1400001000c009600a0060520160300d00d041500825000b030560000141e446804008500c0f480710403485240314a0070942d680000c0c0c2090842c0c98400707610248554142a043c000d2801022070421309640103003440300c03072950f80d42016404c5006942028003011600d200d440350800780011260200c640c19000d43e942240312104003074583d000c04a0141c0854001c200302c0880d410104000c11038100000000400e45940e01d000a80300c0300c5c10841c0110a40c8418244800e1140c03d5100c4001004044010600c8492011000c0c0013050010000c1d40b103403601c819060080c207031211 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582225494 1250 582224244 582224249
    0x7020f0f0603090d0e010221070302011d01140a02040518090708101b02060405030301060e03190515071812060b04020403050604111008010506030603150a0605090a060f031b 76
    0x405442e124500503207855918002540392000165480c41c1a01c40c1d54008950910703403031450140307000d0300882c81003124125881035604404641d80c43d08a100e0030200c0e502c0e40c48500710b00b80f002160b000b200203840c0d980040c0c007400d4255414030400040100e962202c0402e2022036041c2885900c6944d070030046800d01d034055001c00142e005014004012544e00d41c03200d10114002c00c00d034401d9044909080365160012500107005900810040c02041e00400101200450041c02c860702803c04124406a003414210121003941c096400b0b41c41c000c1c0541d4031961300c850300e03103004411410618114005062688110503603840829030707205c18040e0940050a4000d0050801e541e1150340340307006503854004440a4071b916032560f040d605289000e18600d4040314860b950004680d0034041002059400504483c0d0300d413081d0107e00d2400600001180d20860000e013000600500c0c01e818001082c01c02800f4001041c6801e106022000840742001c0a880d084541c0c080542e148852000d0000411b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582226744 1250 582225494 582225499
    0x32a12060302031b09011a0703051b071d0a0e07060c060f09050705010f03050408071211100c030c020c0303030c25050d0314040203060c0a02030f040f0303031b020307020f0f 76
    0x41005800e6580140c114440c50740c00e1700c81d880b85070381e984204200c42d030f414840700800030000c00a070000b20b481000a00800d100301240d0842c42c0800081c55484c109959110050f4000e00038036440e0000255030505500244002c024801801d84050301030300c80e1f082d8001c00f014810700b8502c8000307000003a0301c4081088007491040040c10b9140c1015561990341c6d10071540000c0e4140c240a4040d4400d00506000703552182e507060400720f460343c0b000c0101e91281d00c140d0030408103807200480b504040118101407100c2c1000060361a821440c001c041e100d00c240180199441403001120a41b00001102c0d40400703109106074690701c130443c04034034101c40390120b40150f20304006000184000414a890020600c0e1800c100021094103030110680f012a000780d8150080c10015220b41c1155000f842541c072248192464002c60620b803450580164000c3d000c52082c0c000c3c18001c01d0303058411803045480000e600c0d0f40c0c24054000095030380c49880b01c0203000700c0c80c42c0c83c072214a0300d80202d010703d40c0c1d100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582227994 1250 582226744 582226753
    0x4080309101a0307050a060801030602030705072411040803071b050a060306061701121202010b0607030c020f032a0609090a0906140106140c03040f030b0403032a1206030203 76
    0x20030300c2c80ca0308400c0c00d10805100b401101030000342071801e0700c00c140c06ca5445e6100c1142d00c1e0301c1c58407600000d4000501c40f030709018041049900107280310211078040803d902c0d104001030000c054030002c4606e4100d50800700d001c100806c0c408910004281c0d0102d680c045482c281c0c03000302003611194003005500c07040e0080c2d01684c0c086032540d09174010406840303050b610240002c4580075451711401c001c0c07250081300020f540b41c04010400041d40030b08130810700d0002007218000305004c200c1a500120302a400030700780b40300721000c52820040c0404040e4084004120308003a1001c20000c1ca03000e25903052202607090410b442c07540340c00007541e82c0603500808030719003458404482400341c04219001c41d000c5103050407101c41c02400b05401c506842640c1c2c0c0341003020100c5070041401c0d5112144902c0c2900c018800002d44550490303003071001d036118107848400303410a071401509460410b5007440c0e04010398060807090b008100c0b50030031691428a0640c0d46844076074a058020616500041d416008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582229244 1250 582227994 582228011
    0xf07020f03190b011a0a0c080306190906030618110d0f082718130609061a011101050915040f0b070203091c0803040201030506031006080c10020a0b0408030910 70
    0xf840c2c50440d040f2141c1600030034601d0b003080c0024545118440061001c502d003a41c2c0003003c10100d002555000c1c4000c1c100c413a013070380000342241c1140104c0d40b1040302161103020600800c0000c0c012890728401030250302d0032651041c0c0e200031400918a08485c0540440b803030312428041d000040327044840d000410140ea551103004e107284400c0380e20201c4039406036044180c110714100003500c80c0d0500c21402e8138011545400412101c041c071000d1042c0c0700319880e0241c5401003411440380d00c1107030042c5052a80f240d403205c4009449203440d01101a8180d24020070054034003808136449040f980d1082d4982100c3e0380e1031425040c00078800302d000d054030f282c00c01003144003900000148608003041f59101500c2c000b0b0555100c0c43c2901100043c5598800e002003401940070350401c641009005045d11501d494090094044a241e035000219641c400c0f1606c1a4a040403444141c501c8c0e001d00c0500b00301403460316941c0c040c520103040103001c0000003001409045060282c105800c1620105116062 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582230494 1250 582229244 582229253
    0x1502030712050702070e07081b09040f0f0218060f07060f0906020a0c0b0c0406230403020310090b010e09060f06041b0504050901150f050c070302210f030f07020f0319 73
    0x2505c1c0c06401d201440c0480420310a07400750802030310500c445002c410b40012041000000d40e0801142d45170050386419040340340041701d004040c03100c1150000103803501181c000c80b0040301c401c926000e00072082000030b0961030440b08102c1d4201500310101213203442c10341442c80c0081440b0000a0050b9101151018a141d40080700800701800b44040940301c3d103a0042440091055104410104213800030030691070241280c90b100b01e030444a903903810a13540790003090510541c60142c944240e902e404950400c022200107074050b000c0c131000c102451801c000125961030303000d02940c81c02e000c140c00290040e40c40f034106d03802c2d41e0780001c0c2c0d098001036800e030003a0180d0410700071140320740c204400100305501c40582000ea50300050351000c4010305012016145a0300c0740304c0d008114040ca070070200258440c1240400748410810701d0341c211000d240209410204c12480300c4010707410811041d110710810074261007a094046030402c00944003040020b24020710143c407600c41c405001147c40500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582231744 1250 582230494 582230503
    0x1205061302030a09120e180c0c01020307050c06100e0103020607111c05060f060f190801110306130b031e0c040f05040510090503040b0a0e0901180b0a031502030712050702 75
    0x1502c0751401217040d0b80702d0001038880b201c07901c0305150002c9412000301c628801d40701c1c0041c1c1044410074890310b0300200400041c2a0f92003291000d001c5180001d032100400da081254136403024401c01e0410183d410543d031951828410b102c042d10405003c540d81d020b00035000c42103011b095001380080101e04000010380c001000c0c080341503405000e0200094030102030000442d11800e4020315421006407170310b00704a43c004030078445400c202803205d8041031940e0240714811601d0075110030a616840e0500130402510a5100c0031003031241894051205910001640300300040750002c0d0700c5081c200170024514240c4035201882e40a410b02c219001e41d400c55501580c002d40c080c4090750710003d1a0a1f07c1d0054840041e4000c0c22540100010081c0c0174814024000358501c9160548202d642c802c00506501d4007a001041c420003c2c05c0b40c1e00d0390034030710300c26100c5005042d02c21500081c81c64a0b10600005015421030b9201d800000003000541315114030b0f010f030410200100100e0070040d400039130780e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582232994 1250 582231744 582231761
    0x2030d09030b1b0706020906210702010c03020306030607080417040905180a050c01050d0b0a121403030f010302011b0209190f1515020f0d1806090e060f030f10020316050a1205061302030a 82
    0xd1f51810037503c03407181c4a40212841900090014046916079080c22140807000a206442c0106084034913200b080d03042d0020401800d1800004c07032181007101044044c03901c00c18205070550f000710030681c0003400100300310602c01c8090038960b03117584a030000326010348001d0b41c01540c0444003d001027420300c44403108450f810b008000000700c070001140010795170b100c250f0740040700c2542600100b00542c411018940a41c4d5424035400c4115400d42c00f140005e6070541d000e0106107000c1c4500300c6403891612452680000c3c2c10b60030700c11b0001214082081245c1c500940044440d086c010701e50a030300800054a0b201052421641e0350035404034020308504c0d4415800c0d03c51080420005070f040e200361215819600c410351650242d442d8041081020400040642d8140c00752007000f4009080510070300d1211825803001503039a2400e0420440f891014642600c02e11400f40b103a80c4016a0094004041e21456580010b154036441c0018281441f0041003c2c1031500002c100025140380d80c009040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582234244 1250 582232994 582232997
    0x30c070807051207150c0c0b0901030b0102071208030a090c08060a0b011e0e0d0203060106110114040503070b0702120a050417063102030d09030b1b07060209062107 72
    0xe1585810400c50540c003443d00912465002100922051100030525a0014694204070013650500c0e690010052940d038071000c0c441c0f402151000d0f495826000c2c010030070314244050003055050018031500d40c00a014090198400400002c4590441e503012510080c0c004001d071a03010b030741c0d4050586c0d603101103074100c81840c01c150b0402015400b46100b0310064030100e2001d10f03100e8214004544884000e40801e500240c1d00d104c6c0c0b8003503101030104a019100a95580d0422410001d5060964108001180040408500304800300303c011080e569641d501030700c10805134680e60300c100e10b8072084141d00241d0800c0046c0305008680c1100c0240201c403121001d0b05d80c45440c200740b090720f619040315040c61584907000d441103040c098407033981110354551042d40e00d00e916074002c04d00c0e10030050050b2011524801c4140309100340610740b2030340001115280d10324a01116520710301405600300080090340c01060000701c0d075499405961209a14421a05600c200e90440d981c203080103071802c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582235494 1250 582234244 582234253
    0xa0e09040c261e100903020304120203010222061b0210140408010606090626061512100306060b0f1603030902120d1e270b03090a0209131121030c0708 66
    0x1154144c540210101c0e190941c0203582890300d020350001c0348410005040340e155508010811008040824808404001e5448002100c0c02d040000c2c158030f4103c01c42c5003a40000d40300420040e5103072450491828010300c0c00481d90f0820305401c4d816030040b9040341003030b03508000c1e02048240d070000007403045804d6540c60040d4070030400b2189000002300c94080c2c201c4189003001607602e04207030107242510b550055a8030700e050120400e640c030800c0195076009001c01071400400030701c031140c0034801c0070308846c50440d4544810030401007840e00c10003881c60f40d44036480d203078501494003d40c8200c41c01c90b00a42441c0d00f5a0792003410946501d40141d00d032001c25440e44044916588c040b0341c49020f10319a031103104020b601002c9180002c0640403400343e0034500c480c804100c40c280b00010b140946544001402180c490b44100480500020b01c20176000c003115a0140220b0b0500e4050008404180e800d13462210090310301200710f03049480107103680c2c4000292038004040000300d107011206800d0960307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582236744 1250 582235494 582235513
    0x3020d0b10020d0804020a08070905010305010c050a05070b19050f0603060114030304031410020a0203131202090411031c090503010509060f041b1503020a0e09040c261e 74
    0x301c01c07000c1860000050b4071009107100d0040c0203002c420b41140c0020040110b446d039603c1c45515000c01900a081c1c62511140104104002400303034900d40c8406e810000d04061035901d0040ca10b000382d180103001d840044c0c010600d10103d100e9008501652500240418a0402c1b001507601340243c1d0028000e02c5800000941003e0f0594140d0b01910002e016510f000c0c03440d280c201e24804074501c184240e02446416075643e4080e84000c01c1009960b4000e1600c41c0402641010344540c1d503409071001421001000005030f45542c02168401d03482000d189500749200c000c2071805450881111706140c0c520b041c51219038001140310200c5030300301d00034412565003811144d141c20081d6601000d001d1010007050002e10041c81080030064003103546035803a81c2c0c03103034061038400c6540c00b103402103680041c96200c40c1c2e610030300a64822a0541d80d003a070b141001e5a400502125600c6190910000d500310384001c001107484250b800c1c03685004940060b442c05489005040000914103164800c3d002e04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582237994 1250 582236744 582236749
    0x1101121b03051806041110050405180720030d110706060e10050406030b0c070203160909060501120f080a0210021c14100501030506010c05010f0b0415030203060103060b150a03020d0b 80
    0x4a00c80d99216229205060b80c0c00c062000c4007500503147e1051110900004ca110b440d0260350f60109080b220114002d410648401b40a11824a484840c600001209101002c80020071240e01c41c0792a000007132a030200011020060044000c000d04450914070001900d00b14a200315000307c030414811550195240100000c175029440010110948903000801d8600001c01401c0317160b00103019100d145462901d2514a440550415001d86985035089801c0c010244902400340001c00d079103401c0529580c841c084800580d034401001044005405001a442030100110b000b603800c0d8190348860b9981c01e01801d00d01c800304541c50704c0c0d00e00b1a4416940708540f4080b070040114000b001d201a05080c0110080d06005010b68140184c0031101c0c1c000842c24400c2c079440100f40b10002846406c42d104000591741c028107602d406004248080c1f02594000c035105046030391100d400540341e46400045003141151030ba10030381d05200428040003107509a00148504400c1000800044821104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582239244 1250 582237994 582238003
    0x91b060f04083c070905040c031401050f0708060303031b16060b030124090f021605010209010f021c05030901110a051c09080a0c1104060f081501031101121b030518 72
    0x3448004c0d0310038403040080000c250f1000350058010120305c05800e4480e2a81a1422007000b501e0000c0c0c0e551b081041240c1034541503107900000a441d001120741400000240c0e80d00000d05000030f10403182d039141d0001d402010403207503103640510b466081c409140c00c01c140289094003e0a0003542042700d840081c0b05042884002c0b02d07800c049441d0a141480b0342d100050552650500030642d003002565000c1c58220325a1750560b220308009681c03070700e0400c0010007480a59000310b09651045140c000c4c0c0d0403001403802d85909140c94215202c0c0c0d0707802c41c024007520401103910004400050451030180d4800001c14000100c1000c2a40b400480040320003254041c14001d49003100610080001600c10500c4181031406582c621180303000080020302242c00d10781c0150345208803d601084001024011003601d1440003c00a0540d851070b02c0d01c8600c2081b400a550400400d40313510003005013141c1c0b002e420000003146241a007085060043c00506055840036000381e101c0d41e545884060008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582240494 1250 582239244 582239353
    0x3100c02101a031903140720010314160207030807120206010b0304020105090402070213060906090b1e010e060f070b0604110c0d03021b0a06050609091b060f0408 71
    0x18020070180041800140d84204c5085048040040342c003024200442110003030a03074a8011000c007141080c82d03000c3c894000745054001c41c14141490343e001c0b5108540c8002d19403051035845000c240c04000f0400f2170810280390401002d42501044401c00c0c000099031410b907080c0e0f80d400b10746c5281d88503070202d8018081200d0003800108108000607180c14590041e0108601c0504910034043d171903915141964800d07040b15038260b41d1032008010b02c1503280a0804030403020303502070050900e040e441140302c80c0691044c40c18004440c4da0242907841d0034013150882d01e8100185600c50706685008c0c140680207403105c1e032245d820300c110f012001c0c107080111740d0708489690080100704407480043e07019411040d100e8901c1e509000b0701046c032220500040400f180304900008103441c04104105035014007030400c0e41541d201e6103509421710310310041529010001c540480c1c66500200642c400303031040380c0000085006500e52481100407044145d1030208450342d0700c8058050384c5c140b0205640980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582241744 1250 582240494 582240499
    0x207050a0501020a031508060c13081b041802010e0402030c0405120309180c12100f030f0b0c0304080a0813060614090f0c040614040314060a05060a1401080603100c02101a 75
    0xb0540032007420002b0f100707090310308901140081c1d0701d0781040c2c10b04138031002007041c0d0451640501c1d1030307142521038512040c00e041030703604007501c3d83c0d00002c0841c2084804c40c1d01a950000200c0d14100c00c4009440c02030500030712914000250b5117426450381c0110b0740c1280101490b072404c10102500072840d85c46a13000404282c140303000710b81c40c180f0009024020307002d078040400001c80d00004140c0c0c40405580942e0482c10360b0b48031490011036440c0f00030041580d801c0c06000b80400209a03408035181300025203407180c000e41307511219101c80d426940d00201100d1402d10005054420074140380f5451008854040c40c40d902d2400300c201f190011602207400c500200000d010440c02992801050395441d42c0490800340c0320795400d141d944c000065442950320920405ca0121601e00800e40c6c820011b41d950344180d171502c0061241403650014181c107200040c4001170303450300c081000540c0014607480a001d90b003584000030b515000e00352000311702c680c00c080025500002218403444443c501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582242994 1250 582241744 582241753
    0x60b0306011202030a0608030d02070b160e0d0c091a0f09040827061209100212011818081c1506080637150f03020d0207050a0501020a031508 62
    0xb100c10380d00095000070009100a40d6480001c20004000c0002d005040702108006907107900d58140074030301601c01825020007240101580e00711075400007440300d44000a0b1a554030000c45c82c60407090b19491504602c1200d460310b01c01e0102c503c2c441c1c49c1500002d009071000034110715010284217000c10101c030041c11110080250b032841c09024031503125000300c140c0c400142c4001000000f1440d41c07004c03a0350100304444009001c00da80c001d005030040c1483c441001c51134042c0f10b0388140e486100c14800d1000075041c0200352140120780782c100020740c0c4145885000b00301030501d03103101984c1001c561500c01c0340c02c00c0050f02204030a0702ca02610120040c580f1070405c0c0c90104101d4003010010502074219611800b651004204562817080b11048011f641b14802d0b00440101c02d90000e6a000030700301e038100784200d880e20b6082000305071612040c2c54056600c846d168100741c0070380301d4908000c10900c514410f400070b0003410f6015140304151a80c05122101034000c01c0d0b070f0b640c0414000c10009400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582244244 1250 582242994 582243017
    0x10c0c050909011805030d0510081b040605030102130e01091e0b030313120302100c120c0e180604050108060c0a052a0303040204060b1e090f04021c060b030601 70
    0x1c0c5140140d41c4803031a0400801e01400b00702d040041000340101c01c030355940c80880c08101e0783c145030140300c1c3d01c84028540c0d031000518219280d0307680c1123a03201e41c07d807003d00b243d60440162901e80204001d0a0301a000b99aa411035100038082900c845c403928441585880000c0703581d0384a4011050041030400d0000d0003172242c50303103200040200c03c129661500c401c0241c03400014890050200408507a403403030310520424100a4144240752408460203481d0085100405801c0040d50780380451361680061124640c45080c0c1c2c040e1044032807298440b01e0382704000e800d0340c11501c04903c00c10054a041c003c40e644c40c0c00e0a81d842d40165808080b481052022044480c49007000c1e120f211307100400707107650400c40f590880d900345201d030349600c0d5600000300b08410760800c1c2c040d1000034040c40703152910740901b040c1e0700c2030750342e0311255282819880003c9a16460341c40c203190780e800f4900140115640e403104a0505400811556458101030a00e900001c41d01004010b40784501810b84400f994540c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582245494 1250 582244244 582244249
    0x1031e020c0106052223040f15050a0e0f0d0519030204030b04030e01030c020f060601050a05130b03010602071d070305090f1b0117060d08070309171b010c0c05 70
    0x10000c1c941842199a5114001403175520250400b10300032040d000403000c1943e2000d40310586260503400c01c00c0c40019a9008401007034985403582c080c1e080010011500d1280c68025001000e04010540749801d003010b0060046069000c045e21040c40400c407880742820141d01c54481d007400700c0350f0300032403030500101e1000e00391041c124662021a01c1c00500c1c01d501c84d580c01c0b008010079141030740058290b21002240796018400c646001c2d0b094001070003c8540c540c800c59480c007006080604202021034101e00c00c41c010303002d484100d02e007580014203e60f1280c0d8000b503150000d12500006215040c400100504005c501e00801000500c52414a5480200550160501a290350761510440c3e100358a600c3c1d0030702c070009107082d6030381c2030b00c0921140300001400584c00c5c03403684145003900e0042c000d150352003069021501c4c1d44080003070b0701c80510341010380c0e41d96042da101d2a038400e00c140c000f10115002184055842d00e01c850305590704540311004481c00d401400d401481258061414050791 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582246744 1250 582245494 582245497
    0xa050706030209130c05090901091404080a12090609031704050c0103020f22050909010b01020304030b060d0c061e03022a011b0306150305060d0303020c070f081b01031e02 75
    0x3c00020303010021494030003001c2000c81d40c0101c29a000030380e02007104a0b00746040c2c480e003801010078031420b008201d103100629000600151009281e940c000a4015641380200904802d210303090100b045179581c41e080200c050f154102d021030010703450030742e8202009910030300540140d4106000348102010b40300190f000f540110000c041c03039142032000e0150030060003070909034140b08140c20502540742000340700541402a02000e40790b41869810301159900005440c00c61b50400544c2c0c0d0f80c0d460741000304050a82c6100d000d018004001d078082603068100040f21051303030300300c01c07040703409500c18004a04038016440c1c02040300b007022a004414076400b00103a80c072407001800010b401c2c400d5030206085086c3c0d1003840340201c0c0e03c400040150f070307005d0316500041603000d040038090340c03600b00c000400800c02c3ca10014203040c0d021803c0e0641e4a01000000c014052900e0809a11900d030241c0c2c40d51111080c0d002011303075843d00100543e55100b40642c0c0c1c441e01d14000000581e10341480010040e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582247994 1250 582246744 582246757
    0x10207050601030f020607080a2c130902060403050a08030f090313060804140f010905010f0606020303011211180f06120705010c030e0603040804050109060912060e030c060a0506120a0507060302 85
    0x681c14044540403400000c009d21070f0304140e40b030300c0100744a40c01036008a202142c0c10005c041c0502d400c0036243d40c0b604031200c0c407070400113803001038040d07818070010b0023602403500090710b0742c45804521030401c8800c01c0158040c08000100b03140c0da6444070303042d070fa03a440b486251500c0110100c4080000030b004074092070b00103110b0421403620742040b094407443c2c981d070001680c43c1a9100c0e5055400d01c1028451042c550039150001d1004508008012b5568401889620ba80c40a091401e80a0000340318459402580082911079040103c0240c00b00c11407040d22564203c24100000c206545096080c0c50b680241080103041b83c64600070064420fa03141e058264148412207105000a036030351002036200301d1068403c40d856a0400c40014004040da4200b4000d01080324402e0240c8003c448600c003080e58403c5003c20700a445001082c19401429244a400d2148105001c4202d00304c1e0401c40c881c14040ea03041d280c40c01c0d11440103644840104014103036811904042c4002c91182e002410b8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582249244 1250 582247994 582247999
    0xc020301020d1406150c03040510090e15040e03130501050901020c0405040f0501050108060c0d02130e07030f0c140909150607151104051c151a090702010207050601030f02 75
    0x202000302c0044415030380b880400c0349508100c1c4041058500d0300d141107598190344441aa800c002ea4000c1031540e034403c0c0e02038a8410800201007800c25842103000714043c0c502441c008000741002c48151076402d4011700340c2449a41403a8121036480e50010a0f18140303000202030050b1145000010748035030b4009134405045001e18001909140c036a405580d005038420440ea5100c101e550904070b007180d0042e0810843c507040501408403036801401070702c16064a61b0401650703041e859a400c100710300235510192421300d00394104943c7c40e42550011350080c41c8a2414015020505d0301250099180c150208005006003c502601d0030a6003085078060200303080d0030f414076502030020340540c00400382203614042c626181034030466980103c540420007056a1801c00d03052000190300c000c034003000b45000e9500704044d1b20038880c41c442a1484039030031250401c0b00382c240d050383c030a005640b105428000c40509010800c0f0078414400c0b94505a00036000d08910707400c55690030303606205141301f640d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582250494 1250 582249244 582249247
    0x507030b030f210301030215090d0b070e01020106141e06070c0b0307030c0206040c03020111070e070c1403030c09120a080d0504140d08190f0608070303090f080703030c02030102 78
    0x101e8808001514103500c0d1500180582d007100d800b014071030281d00c10100c0800200744010401600c03030341c640d44890441a10350740d445151800124010000f0b00f040940445540301c24011003603080010210340c3c0000382c0c003d020380354992004440e191040d5031002d40101c1040001c0f46440340c2030f0645a50a40000c0c0b4140c505a0030391501c1d9454191034000050140c000818801d080d601449542d40031012400903006a2603e5140d0b00c0e100704440c030000c0c0c140103008000c1c82d041c180c00d008000150140e078940440904040c0c0c0d00621110200d88101d80f0080240c0d010000d90000000b928404c42019071520701d408032a4082c07126141c111001e00249210b034580040000300c101000d00041c0300703e1031000030f081c50f0608100d122040000d51180d51504089024011180d12030b2007290300950200d4001312075005011440000c103030700030100003414546440820881004150541200e0099945014041c0c8031850602025035a00c40c200c01503200360402c01c0001d025402100c41e40d0700040005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582251744 1250 582250494 582250511
    0x150f060705070914090a0201020703060b030c1503010f0b190c0c0b07030503040c090203042f0303030109090b07020d09030f080909090f1002070302100921120b1012050703 75
    0x7585003103840c0d0400000907481e43c44013110001d690520642c4010303c28001c029100e101d80010352561031034000980850b4607071200501d01d071410040c0c000a480d0190a1240321500c14031401240e400c28042c0010b01044100002800014001950040c49100740f0000242c42c6800040d02e00c064809004c07640340310507040024407400e031500604500c501980320035a6074603003450074024100040c0c121200d06841801400040385900090440c010700107804da0040502c0074230342104074450b81550300e6041c8030000000c1a140d88642141c5003051190789441c840c0d80710100c05903100c41c8200c2c039800c00604200001c00100e600511140d034000e0003070820703d150007450804105464021115030764a6444880b454481440402903a41d914049000c2181841d2065400a40310703800d2031740e4101305a49a09161080c40766800c2075030283e0861041d0348410102041024118071032150100070f455182040c1c05019003061044159802c129903104460341004010b000014070700949440201569040c81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582252994 1250 582251744 582251753
    0x405150c01110a09140a0e070c140f25050105070609080904060605220b040b0304021201051f060503040305070b0a110c0309130624020307020a151205150f0607 70
    0x7002c80704804e03035660b04200d08101289080040340380c1103900500341c0c000104a00403607d44040e8014401c1d240643c4880300a00b040184040e1103406410b2768001d0910011540800007640451808c108410ba0104104e858103d1800880c500c0341c00d010410130001c0500141d00c1382d0001091601c102001403c19002d140407500f2182e1941061010a0b0001141046483e00000d02040a0420a1070000150501c480c0d5a62409103105480c10410040041400c5580e01081c41104000d90002003009140800032505808002032040f5414407840c500854400d204104072886541c25445140c0361204503901c5400b0004003c020040d242d03903480c0801c2a015403103009146002d0300c40003c60325220800100032030410040150056a803a1480c100500c8d02c0c0101200101d0361814002010601d15000c103a0030761042000c025800810450086074160001d202001c0401c074a40e128440a00d4000901c01110010388075a41408802d0039080140e281c0324450703c41c0700d10050520f07400c00085030748 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582254244 1250 582252994 582252997
    0x105010b0a02011a01050a030c03021908010e090a051c0c0c0f08070e0112030804030207031a01150c11040e0c0d0605060103050709030812101503050f0a020405150c0111 74
    0x440c40da40400040c480090729424011100c0c04031080c94070809401c450f500280040c800c4074004024191100807800c1c0860196060360b040c1032066040594910302e195005061610074014101e81e00404004101d803400000b82d20390841d58040b004101c0084080000411401052907080800c468502c2960010b4615510311000b081c408a40d0700b0040d0a2882c02800c1901035045015a404083c0042240314039491a141c020380d0103003030900140d2280e040480c24501c0ca600b015000c0da00e40c07800c10200b040c400c001681215145400c101586d452860b080311a640b149501400d6600309030740000040c40c0175440358181c0401603040b242c010343ca00c1c0c040703000341c2c2280d1425940701e981c40e000c0102c00d503090b0040b6a07105400e80f4060078030b6411681c030380001c3c1c080d515000f07003003d40510014080c990300301038000240c100c04069000b54582c110000b00502401c031036003850769407180c000c2031601007a8025502070328802003000000c202004103051180c1c215030410700c000d648030340d40044040f40440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582255494 1250 582254244 582254249
    0x1207110414070207210611040503161404050f04020415051903060501120b0403030e011d0a0203390d021f11030a050a030903020109020303030a09030e04050603060601120608010501 79
    0x507100402454944406401c0112650082c04580c60100d08540002c140076410050030f0ba20800c0021104005040d070b250a0107203402c05078040c4600154503010100e01000700c0c0441e082c0284644c00c85000c001480181c98007640d01004030b86684020800618040d080b20102900010515074401d1303a803000a084141c255000780381e1003504542c04d101b802603d0007594050010782c803840d98a0f03151590b03102c0a40400034030113810941c0d5814000840182074110a2134280340f110386402c400b0f075100000b40c9400280310b00301e100c0c0c4110141d101d2008442040390715a022484101044072200308011281916100d00b00c0c0ea0242e10f407041c0c44010395a10242002940401d04d41007044010b598015124a60132110700702039034000d002801c1d40c3d44d130001c00c403400c9198900d004140444d00323103416405401ca40900a6050001004000e91019640e03c0296103078003d90750003400301d00407014482120700640c0d96a4068008030300142c81e65001720030351100c580a0030000102259640000d90840300285c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582256744 1250 582255494 582255521
    0x5040e040f170a090f050d02010c2306010312020d08011a0a02071707031509050613020102240601123c09030f08091b09070903080d02030702070e040512071104 70
    0xa80017408000b01201e01c49016100c10384600c1590116500003034031021500b40014440801c07a00c81e1943d5035a04191000b43c80600c008a030700f996101d00d880b8043c10882003446006100c2d00942a07921441200f03024100e0746040150155180409031382102513001020f040150300c900e12000a40e100c80c52685089565500090b00b070b40d5066160482ca081c60300c6040744c43d840d041000600120354085229908200c415284034240c0c0744910060382001d201c0304100c40d82c0690300402000700000e00450500c5490300341e030f84040301d0100d010030703008546c4442c100f107a2403008100275042c1017080c1c001504081115445c6007501c1210000311505490b076039901100001c003280c0d81001c40d640c022000c25000381c0c08002502d0b00c0d90302c1c031000608030150340d0b40b640e10540e4058085010306004018490103142c01c4500640d590303451f060311002940c02600d001c0014400c160000444030f000440141c010795001000d400b070180c1d841080310701034008513029620007a02100404140d6103d10030306a248044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582257994 1250 582256744 582256757
    0xc03110c07060e010212040909060b030303040308090d020f03070809010207180b04150503100b1f03150503030708040b0309010204050a0305160510020703062a110d05040e040f170a 79
    0x8100700144200f050003140c0e410355000c81102100041c44e0707015601034903020304000503468190304040002e00390706030009405001c000180320034954444880c5208651300011901061224101240d644000c04030480715600248010000204800000c0c040c2c020140b0484211a803035205c42c101c51712130321809400c540e40d6118403c1c2541010702175500c07500c1c47d9140c041100c5181c0000709483d40013106c0d40d8508140d40740c604801682d9284040484c900f400c02c001406c0103801e0b50060002c144054485030b40c03820b03106000440b0724002044035401540080000e0900e85000342100e0246c2002e842143c0039502440081950745031104510000c50048e0018510140c080c6200302001c0640e41000b07000e060010100581e413600054444101c0c0e5110300005001c810b842005950380c02da8803d071540f00300320300403a4000070f0b50043c0c421100070121002e9510100e10200251090310aa105040909c2403d00009000c103040407040360f081402104101075021848100c114917a01c0118030340c010990 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582259244 1250 582257994 582257999
    0x10c080d060b0406080403090902030c0a05131e0303031a010c020d15140f06030c010905060f0912011b0f0c030c050307170c0708031314060f04080c040e010b090403030c03110c07 78
    0x380300b0400c8c0c005140f554811803940c1820f00328142c6da482269035a10500030005203801010010003048070060819040d100705044244502e4100507445100990010703040c8000c0340c07844409900200d0f2100016102e0004401907079003440030700303801c00b00d05541c031180000b00e00302c440165000305d06442090303000044640c40e003021075110f260720203412203003c0d501240740c00c031082c0d0b00501c81009641d03003154940d4884503041d082113128400c04c5040d640103400714408212400c815001061480029210001c8403901014112002c0b580b1003080000a00c84000f00303000710380500d12211034107001c2c01c10f881c039114564462040c440354011407410400c10004e20344860881c1070000074064817040300654504a002e4000b10043d05040c090580340001c910400144c40d03a0f81411113041b01444150705491700d6031207644d291141a8800080c1c0a142802d5907000350f8401071184c12007000b4000c00d00d0700d180e120307500e04a00a141c444144400d0503a103d0003403600c2541e802c05020981c155400800c030060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582260494 1250 582259244 582259247
    0x3031207092303152205070e07140703030b130c02151612020306060903070b09131404061505030a0c0801060801050c031311040906050604050f06010c080d060b0406080403 75
    0x640d14102030600b0340c00c0240700010750ba000c20860a4160514840810740e11740c007240e0024140700c0400010f480c2d20440e10902000000f040e40011a10000c2d01c41d4482c0c2d5030702000303940c040c40c0b1101c0051401c1082101c01d0019000794002511140f01a020038003a174041880541150405c14482c400350b070007140075803080039101c40c039168014449a14810f00c20f044410141c0031194101100c41e8054001c800503d0310349030300c025280701180003011100300075914081e00c4591350007100035034019401b6141c00100d1038528014015042c6140e00815042ea03140d44403440100081000d0300714403040340c4000070b40f030703035042200d02d41950141d1302d0010028035020303046003100c001d40d2014019904040802040407901d90a8a6100901020a140000f694a00a2030fa000c2c0305010a5000b4941641c02081c001c00368070503446624140c40c100019122454040c8040c041154030500150281c90403070000707030400015144130080120041111621000b246240f0340094121400042c0403504000a06 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582261744 1250 582260494 582260519
    0xb0a030207080f030a1d0313060e1503100807060f05030604020304060906021b06060d050c060a120507030911121e01110705010e15070503061e040606030c03061a03040b060303120709 80
    0x144500021454031003008231118250556210311000c1c00301c1010b143d01c0d05c0d1640c4083c0106040c100084582e20326282c1d1a0424403403940c06100b4441c883d00402083d0035008240140c980140d40e15018115550142000003a51000b8021078825858140240001d11140050803078a216800041c88985a1500d01450007800410891055240140c03d50100d1030109554980000660303031641c1d00c0440030410b407004109040005141f03858201009038140d031540c8041d4540d4400c50100362001c1e1030404100244400816603809a04684c008aa241c9010745c2099240403905001203110318040d1500407450f00580002d8542c2c1e51680c020f503002039014801d004050503a00d200480d18202040c000700f650000030718240c01030419030301004c00316039150b01ca046840c9000b80117004030f507240c1c14000d02818240d055007010a00f40f00021a0403a0b4a03880c40760002140124035007103690315241d00c01c03044030203008a5090300041004082c1c061015040d03034460145d40c0c8070700780307124039129884848 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582262994 1250 582261744 582261791
    0x31f0c030510050904020117013510050a0b030f2401060e0405070c0f052b0804150b100512060402040302030c0d020301240e060105040b0a030207080f030a 68
    0xc05262a0810100300790585200050311002d81d1800e00503030301d034401601d10035034480e07101c01120201e800000700940c40c800a40807042e140c030041c54288509610070f01001c400c001140d040c0d50003218401d10402c0c000c0d40080d81c402c458010200311a110000403a0414501018001e01c03504201c8103051100d1044800070080c0d9400300c07030190950300d0190028418011540800d1095480d50081203242e03104000c80c0e110035400030300e20340c61901141340255640b080c20620079202a00740c8007480c40e0380c00034900e4150b9054140c94032007840d5115614507003181c07076a0400b41002c0d65240040b0300c00c0c0d210f560b43c0000840e40c0e03460749959141e012525050105000b44207502c62401000240011b880c0131640c005000002d4914003d141e1a501c00280034103144681c40e465134040302c803c02001120b4590200480340b002e2265940342d2a0300c40115450301c941c3c0a1840d07240c030100003001e000c912940c0108000c40c02440b200e0706110924285143c558000d440b4280d850342c5411400d8000b1502407185802c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582264244 1250 582262994 582262997
    0x2070801060f080604121806120509060105030a0807080d0e030307020f0106030c0b09040905121c0506090c0c030d050c0d0f09170705011103070801150203091518031f0c 74
    0xc0b10b403400e6162541c3d660020002031488014458080781d4034000c0e80600c03402c1c18080c040c84016034139418020b2490303889400e81d5400a0908000c620741850210b20941039a1016000d400d803182d240c2c40d841500c0e4011034040750503034410803425070010700324850140819008009182d0301d0410b108002c0c0381548450b0300c9482c42c6d14283c07003000007600203402e1400703d80c040c03451070307440d12500310010300104180d14002c2c081d4000c5d0140745c0d945400c0039005099003006c40302c50304000f662141d064011184111603580c2c1242200d401300c0c440c080c01c00050703c40c04a9270001c6920b00091004400c0c160382d000d80f183c00c900e0202003584065111140141034020030207400410080103142c40e8081c000e42e2560f041c002080c2c0c00a4813178280a829000b220000744042030f102d0fa00d003003140d00201108002d11504450b01007002c106400306201000315804028010b00e10b0499103071450852a055001c81d890300c41071171481045201d40e4400b40845424521800321030b6022088006402c029110749800400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582265494 1250 582264244 582264269
    0xa030824010c030302130807050a0e0108031623060a390905030a112b080a090518010609082406010219060903031a0f04091e030207080106 61
    0x120142182000c000480300910380503441400d14181074000744034070004e00c081080200004991010002031000842d107081da20b120b086a0356078044010000c0a00400c019500108080010a1284c01881d00c2c202c1c002c0480c000902840007010351402010580c043c3d00360000c500b0010840380522800c1c010102c400c82003195942a1021080d8071802011030380140344141c0004807446e03200d000a00040c101c081c1c119003610388641061100d014041e22028030611948440c24016007000034403250044019002038600d4540356668040ca80103004a01c0c00c0040c071100000741541c0b07100f1080311440e400d5040102e29410704200418041464111211035400001213a840703812030780e004e115001003070702e49040580301c03040101c0c1005041c02c0c0c1011000b5220303501c4020f1160b51b600410100b842902e0801c07000c2c0380c500c10b1007400b603a07070b118003507100c015400354160a0074950400c20409210380c894821002c068a80c1b80d11400301c0000a40c0107030b1101c9024058031209204080c040c00743e8a4480 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582266744 1250 582265494 582265531
    0x18140316050f10120c020c0307060e180a0b0406120203070501030c090905100b0a0203120a06120609021201050c12010f080601150c02030316030e01031e0902120f0a0308 74
    0xa0745003030028591400380c41c4a07041843c60500c2030081115000c42c841080c80301e0300c3e80050080d9100d41c1e0700e4240e40b1a0003190380020f040750050426128240000d4031246562400042800c00d0803001402c3c01140c40e140d280801c4150f035030380300f40c0001d041c0c100c0f1020141c2c051401410320301515030708410b05044c42e01d100070349002d800101b0302c170031a00d1034030000c2002c1e81c0c0c0d20505881420306600038a9800c401040d91020f41e40c0100c0540725440400a50b41120b03a070341c00d200f106484039441800070311000121307060042640c0c1c2e0440d50a1500107810325003241110320031503003100c508035640e90355490046111109921807030040d500526400011004071800d00300281c1e10349a0620070101c00080941c2c28000442c0614101c1c0b00e16500101904e4031070a2011000746040d1041004030f0000b141403010644960080c8550b400108a2030351240e00c0c00d10b00380118006028896050307a01034024040745140280c03c00502e044200c108002d440c4c540c60390301d03000c1d1004001070a00e40c655403403100007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582267994 1250 582266744 582266749
    0xd180b090a11060c0a0218070f03050f070c030e031209040c0302040b180d1401060e090307120302130b0c2805060610090e1824161814031605 62
    0x1108405103003103d0b07155032803040310032091412190100c001d40061102c8a981002c40d0400003451140c882d84d21031920300c40004900b01c01b100d07021660f28034105003d0000c141458404c40703154204600c00d080001c0c0c00c07184800002d142c8082c000003110100400241c08050342080e024107440901745e0b0406504040c200b04101d4034900621001120900c5034200122084e81c8440e91145001d41103000c1581c0f0514031411035000c1c0081e401110164440840443d40c2c12800008540340e480c0c100c0d528000f0051841c0f4102e0182d807207900250500d405008000c120101b409004215502c4090003e0048004c2c2d050340503074000c0d5034000408080302a40d4001e020500c045071b140ea015200701c0e80401d003282c0e0f04c2815591001c00e078002d07070751207036035035041111401e03045510300000e20320041115800c0302440480070100b0b905101803404620340d40c1c0440c0038681c0300c91100c65100c0c49800c120140080c1080c1011581c01a070740700004140c040e80e4040110704041c0a01c2600110a060a44142d03041001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582269244 1250 582267994 582268013
    0x50703081504060e070e2d01030c0e0a080a020f040203010b03010e09030f07050d02070806130615050303130f09110703120b04021809010b180d0501020d180b090a 71
    0x90710304505000340c081e01681d6507402a405030252841c5510765040c220402080140c3c1035a1050007020461070180c84040010015655100a1102c0301c1c040ea40039401100609a11840d00062007204202c8ac8010f5a504000b1809041c03031000804050480703004100c400080c19030181e00803881040117000c4a400b074011241910a49014500c10340c5a070030102d0f141d44201c0142d01e032210780c003007500340802401190289200d880e5508555481c1d8035818403c3d143c40040d282900c6c900640b80c03111000840f00e03080035601c1d01c1c1c100180049159158046419035000f0b910161540503546003c1c00001c484c0c103010006000d40c400100082a101481c10415124000c400380c1400980c1c0b40c12109540d41350000924884050300a54807800205466990060b601d00e005110300c51200000c1902c5544805590200590038292854400884107001c120f001e00748082d01c09540810920100d012180600c0c1103140d0203c0342c0d1041c1700c1c0c240c01e00507003002024010440d550007114010010030a10803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582270494 1250 582269244 582269251
    0x513020a0b280909050106090815060102060601110708030f1c0209030a170702041104050f0f03060703090f08070c0f120f082b02070201110604030f050d060b031609050105070308 78
    0x4030807042c0b8035490760040c2e44030071860344460302240c1080004a03400703907c44e0f100412200e108041303420240f81e403042c412440c03404a5201d0b00591220002442c50f44c032500b020f001d00303a0f181c01901e409030f444181721429640582d2002000140c0054044500302e100c6aa00d4000c00c1e40c04c0e421030904c41500e00280e21400c50210140c40c401050200802801c1c00c0000c40d07210550003070040088180c3c407040c500507600144a030394401c120100d000e850038240300c2111004044014090148c59a0303054040e0028031650f0b4060310542403694035034000603422801810318074012040b907288180b0384000081c0540007034201802c00107803000484d00241c50b050044458030f51050540e5116018480d80180024880b0900c0c0c0040716034036000d2070481d60070b82c000d0507601d000380d90743c901444600c0b500ba9590801514010005030740c1600140c640e52089000d840d43c0300412002080c0e80750744080c41003240d00240c600d0380e503051802204101560b004003108004040a090032420030002d610040d1809030000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582271744 1250 582270494 582270547
    0x8010e0103030507060e01020d1a031615051e0405040b1f200a0309030221031204020d060603060b010f1e030509010905070e18070e070e03100513020a0b 67
    0x2107503070400c1005640240405c4503c5030021522220b200602700040d041000c00249074a502c0071050b0464107000c11200c074000401100788580b24681408061034881342c2c002502044000c0c0080b4104480b00c09001e800c100c550104c1d642c845042030108001c543d14480c4191250047c2108045040904030040580c00c1d22402cac0111a00d00320ba18090003841d9121108020b401071500c113200700f507000402c0806590007501c0f05c14040850341c3d05160030010f007070343c4801940d000344104054080c00241090340180b010300360a65005035030f910b031020342ea400c1d0400c035807070303500d5805205503035a02c00301a517000000c3d031419001070210a400e10301480f00c10b1041c0d4003055207400009041400940125030516440003c0350f0400340d035940c601400710390a65035003010b401b8403298081c109000180305030a6034504881441ca40d142d861040d5038050034507203074603058011020f00845ca59440e2050038480c11482080c417240c150644104002400c44d5080350b01307155410710400080b032602c1d80c41d084800501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582272994 1250 582271744 582271747
    0x60306040312020c0f06070c140a0c180906050414060702121801020307020d0c1a090604180902090414010f09120c0f2f040b031203100803071b050108010e01030305 72
    0x40f200842d0a000382c140e2200d17014821042070021050b07100700944130090203000a250844032540c100380e103843d43c040010b0720307a40d0176210500511002d4810b50480b01e0121800150303000b02c956902050314030466051f00c01c094078103146000d10f001400650303400b0b0142c1c0b000d401d1234420500c921002e80560324131a03003031100a12640032070364000c000b21a03050790010548041141180781c8240e1030072441c05618920000c1c5d640702184040840196407103240014020fa00f842c0c100a8601008011640d401900c1e40d2620748000c09620b0320341d200e9008600404110308007943c505503180c00d54440c0515110001e14110480022620100040a45500c0e5141000843c40d0a05206204010034000541140e480d040041c51030207542440f280407007909004000d4009601c0304100c03c8a040c0003202e50184c101c1030f02205200c0c182c2008590092000e410401c107952140d00861454100d55000c65091101140c581c12080240c44801c0c0140024606540d41c1d6041042d01300708100b06100040a0040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582274244 1250 582272994 582273007
    0x121509010905070c320313050a23010c06090507090c0e06070f0614090a0308060d0b270304060c0606050306010b190e0907050904062103140f07081206030604031202 72
    0xe170100c1c2c0840c030800003070090704118006040d12a44101c8101510f036005c032500045a08180c800c85040b039603d6040400075641400303040c4d50b00b408030b4005170304000521211100007100c40c810162502c0c080c0c0001c00180341040b291504440030780401c031051010510200000e51740d054100d42016600541404c092585131070400d01805240e206041c03000c02150420124000001d140c85209009607540e840a844107428444107008090018001e114900001507200c400001c03003030203001070144120012543c500c2a281990819002080000c0c02c0c1c020100a21038035004070009000110050b002d80d52421500b9451440b5001d884d00714500182c3c49900301901a4040b0701d0301000103000c0d0801e80c031b440700008146600c1059954440c49c603205010880003105c281c1905944044030410103503c00d81c0e1801c0d1221080106035282c0c1040c208080240703040b182d40a000074034800c1c02c1580e1541c87e14560034002000c01042140a030340100700300400b0a44c410140c0740d0001200c1c40050381c806 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582275494 1250 582274244 582274283
    0x140703060b0d0b031006030f05011b1b02011829090d030c0609050a1a240f030f01150602100e06060114130305061f0e06011103121509010905070c 64
    0x400c517000050740c080c51318000000340302c01c040c00140300500c258001c0115501700291a1516441800f10900080e0307000c9070000b2101101e005809054014184101d03c1c0d000d40041c08244982d581044001900202000084c1c81c20428104030307a881d2100d4542c2040d101c2004540c221841210280c100f00300d14075000b0a101c143c1d132000708007d4100702038411501040c1406044401d400322a0810208000c002138146003034041c0001210413507214040703041c03080c60300304a0030307210207041e60340d240c0901455610882e009110300700c00b07002031405004500e8500500030f07003044980000510b00c40d00303101c5114201320000c41c480d0381c07164090034a4155006c1c10900e11016000324120401c03c500041c102005003c40042c680d03208401071018801c2000950080e400c040c1000d103c0c00c010049c0000201c1c1041d80103450f00754102c0d001800300d034203004049000c2c088448007070b60b9501404461070055807240c1840011070b80036040000050016040c152801040030200c05e5025154003015103440c00b801c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582276744 1250 582275494 582275503
    0xe030f062206020409050f0606090f041d03040f080f1606030c030e01150e0606070206070602090d0c17060708010b1606060b04030309090e0109030f051303020a0306140703060b0d0b03 80
    0x40703400400454032140c03100ca144004101c00d888502d00c47c2482e400203822840c087c000c40c3c0c030b1400007a0103003200d103043e002480054404019007849140c460150040c680808102a00c01130100e81202d6001500d0200c5071414154010910b01454018481c0c190307920340315507104400c40360141390028210140c44012401403100f060701c0950365081c0381ca000500c0100c141c200090ba14a0342110203a9152101001610321402030003d4002e00180100c03070110707401c3d81c00342c184500f019094a002404903900e81d0001340070b5401030325428500001e895002c1d801040780030fa1090480c00c003d5025410400c0c0c0d04502c0c01011000300060550a10300d0041100e60b810400003003001c4003039683c54984900e4050031142240c02035540b52450700c04030204400050140c802c1468164403058028074612500f126a50b003c000e44841303445998100000585450311800c0086005a000183d40f600d2102c4007025080050007013810182080e0040c0f0583e640c40007155030001c02d082d00060300c0701c0480e0129091 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582277994 1250 582276744 582276811
    0xc161b0503190b340e0109080a0303180f0c0305010c0512060f01090306021c14010302090c031b030a0e1006030c0b071103012f1c021809040309060e030f06 68
    0x1500ca00c0b18501404980035086154a010640342ca414071743c1520011140b091040c400e0500690110700b82e0404070303000b40d21911031a81c07803071162803a41c2e050f41c480302846081003100301d40c0c00250050030000d201080c4501a010031003880c000703241203920100240302e210007500321441007032240e004405030ba01075122080103507800b1009545402c001d0700311500c51800401448011800e03c158210380700d00c9401035a0580340d00a20b8440192911000c400190b00010201c854110107030000112451040d009140f080307507020804140d602998480c1800c0c1241110100026800e2500610004e18414000c0042d550080115a103030340312818041c20244851119580551038001c1d40903141103600e42c00340040d030154040074200d40b106e005080d01d600c40d40c501d10503445c08540c291107050045400500c041580c020340500311140f0800000c9849600f13a80440c0031135103101080007616040000860b141c0030403005001d240141010386a110440108207546a5000c9000a03a004410458400c070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582279244 1250 582277994 582278041
    0x215030f0a0f0f09031e03200918090106031a040c0314030d0504050c01230f07080c010f090506060102010207030e0910030f03050a1206060c0b0c161b0503190b 70
    0x1240301542005440c01446d1084100200300894103644801d00900502c003080200035004a042c2e60000401025908540c8816921510f088555030900c440c01190703034052011a000059014034601e07028064401116400f54182901c6040001080c100b604540450382c102c02d1024070f0489010100d0304500c104182401464640001c1c001440000a103c0440340002c1e203d035200c1c4908042084c450802804035400d101c40100a8004a0903001021b0644d09225040440c1096551080d0a00751984d811003000b52035600d4440501340101044030617040082800218a00302d800d4500030035042048010f6801501a6000b10b458083c980390040b004541010039102c0d04529840d00800b1540010302c9007000031a8010120000f00e100d01c01c803401c41e0f4003501c50884080e5181d4034520403090040190399805002d110a48030140b4582d44450b45600c14268a00071800340440c016541d212504418000c0e07020000081c2c03890402d049403004070b07400c20b052105503601c0c11004c54250000f03002e603c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582280494 1250 582279244 582279251
    0x30e0d03050714030c1f1e0506010e0a12060209030a0503041205060a0b060301090c2f0601080312011206020f0f070506160203040b0c0a1e0215030f0a0f0f 68
    0x4080c1030740038010b009414400c2d0361070608200d030300d1551a80c07070240100400c81a001001002510400c5014a419080107120301041d90461600c0500110410204482c100c9482da42004a10f683c005d070b0013118510101c481803569070828006640c0302c403041500404942c1e00042c201c0701d0f81d40800c1036140c0c1550200403259201c0d00c1d0380340d040a12a0380d140c119200e00c03c0c01c0200e03a1110f22809081e1200c00064020b40c2168600042400901606009101401410181d00154280c41d84509201c5100e07103000141c50808001c00516041050380300584a0b04240034418030105984c80640c1121411038681052100c2c90505000030700c40c0e004007400520000620819030b01030240508401d90040301034905903038500c0c04c0d845806e200c400384040140c000308000c0c8080d00050b40501409180b4000300c2e141e84056503603e0130b2001e0b81210030340180050600036000c6180c080041c0000364626421541981840d1401058503100684000c00721070300c845480c4800403040e0300c05444100c0900d41070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 582281744 1250 582280494 582280519
    0xa030303090308090304050907030b0d0b1503070e22030207120c050a12051c030b2101111801082d090105161e14040e010801150b0a0c030e 61
    0x40c0003805080c0c0304401103000c0c100007400c1c1400103c241e070101c600181c0110501e6580c07640450007040301d4070000380e0185414000c00045100001d0b43d6104607211035001103400840400c16145c00841d80c13011075001454810416000b8069640c0300341c405031811924107240c198a016800c14070990002244401220500c10031b03c110318880400b100e00c26141c0900083c0c841201074000011044050310680c05200c40f000189411800070b80a04071741e00e000034601c2003503c00034150a00f0000c94010ba0324480b4401812181d00384203104600740d4048100340f402ca5401000d10804d604c1e1104070303044c41500f40c00142103110707001c0764401d40106907c9100c030b40250044005010081644c0040180d803902001801092518031946080f03100c1c2e0f200d00044501403441c80b01199110706a55080099549819002c00450710141020b0104032078014050b60402010798216605891401002c0d5090b100400c408103005c821161b402d641840c0c00250703440a4101541d030242c3c05115181c002c0440f81c0e43c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 582282994 1250 582281744 582281747
    0x30e1006031e02091807050a03110301060801060f0b0a021e01142a07021206090714150f0306030a020a08010207050610210f020306100e090a080307030f06050a0303 72
    0x100301580d204407034200600c0b094000c41884120388a1000703400400344004130b141d103003004840104107000201260030f56520740713010813003074441c0790f008942c0c052902451b84000d1800780100f0014052020003000201d1611401e0b8011003101d00c101003c212001603070901151007401030610306c4525079a0310308c10305d200514150082000500c034110720309026011620541c000041407211840c4410041c5060415042e5440036600c009400ca900100c800c2101e00388641c18803100b4425000c180250881c00c0c40c0008248258110b0004a1310502e0700808000040103407101f50748a925916200d15200da5858002c2403401c4142400030354081b148000000f0344a0781500108100c510500c2034407540e032100700c0e800b20128414002c28400110b8071004070b06d2003da852846141c0b40c045c00390300c42c2134800c81d0040b03401c000c1c050f205800d0380f000140b000d100b89c003032800e041c80c1c020012030010b0242040a8944100a01028040d4810141c4a80740c0303000640407074111501400c001040c07204416aa442d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 582284244 1250 582282994 582283001
    0x30b1e03010f060506041e08060c071509020310180f0b072703020607050307060f0f0b0906180705040923010b0c06060f01050c0a03120f0b150a030e10 66
    0x59961096003041c1c8040412102030143c3c2c0e003100e00c0541000d0405007810034000c03101026024034000f82a0030b404c0081c81c7d07142006001c4c058920081880d0780c400060602990800109110721822400c1004840c01a200007030220381d001d001010000709617000443c041041c0d110840f02928000341f41c8444030500c451103200354000c80340c0342c60b100c030702007000c190b402c3c60b4000314a0b0700001041c01e007004001508020000b80343c000d01c01c0c0180c9141101540e075240072188401c10400350181d5850103030036000e10500ca0410380500c00c5034051510714100e4001205650842c5042d140001c1a4001c20745c280e01620070f94000e401130080c14800c9070400c10300d00ca503861650500b20f00441c1180000503890074080d04440d108007010024000560350304090090700030f000f00c00e80381040010000c2c03105010b410b202e020440ea02c40d544549000c0310480030f10007aa030f140070f8488c142519100c4003810f5a664044070603e154029002076803100080d95054006041010000d80e06010310400032000c1c030101d60 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 582285494 1250 582284244 582284299
    0x203010e06180f03160606050d0c03060609090807140f010c020303090d09030203070e15040f0b03060604020306030309130923060108030f03010501050d06050616171e0703030b 77
    0x709111500621182c0090369002d1110320a40150800c1044401d41071030300074204c1080e4000d40b404500300384c3d2500803880301c503100d042c182c488490075401801040041d006107401801000400d000144080d03d660312a4410088014104078010340141c03c10f001c103101d0640c80510302402005145c0050002a44a610444a07440b1502541030346002144c0030304411030542c2d0300503000380348440c04e22500c42500d0002400c64180c1c9080441d104400741d680f40203001c02c0401d102c0740492040809410300d40381002c05404180310754014410441191000802c1c0c800c014022201c140e945030160031804018900747e04003a0241d2405000e0030514032118182c0c5000350130210450390f482e0303030f152611512402428020440703250b0070801080158441c0001d044001101100014850b40d6400003e0b0f0aa01c142250310015541003448000d100c1100409a03a000258064030f19000c50180040302044606070451802003012907468141846035100703951012020703051035000c3d6090740c10544030344601d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 582286744 1250 582285494 582285511
    0x30714040501050619050a031407030e060a0b0f01210603080c0d031514120105250509030c090c0c0706050d0506041a060d0e15060114040308071e0203010e06 69
    0x10700020315410084100c43c6404810441d990a20b900740c0c04c11546948480c042d0400c154451122501401b826030001d80528110748000a0203004014003e003003800050114002c02d290150210741c60b181e010350300107800740920b0310780b491070070002802c88041c0e81c24008102075450184040100f05040c0000d00030140d581c403c8030040307104081b0403415111016258098076440f03210801841d103100341d01d020341e0000140114040080401a90300b101c82c1144c3e801c0500d1036400344400034175031054121400410328a8030b40c0c40c000210703004c0382c0d8920055031540c3c01281c00d4000107420700708a0007a19450301840c401c1c0c5c1c1e4215902c0200802640241c80c0c045401c52070400481d0441c0303400e01c1000e4844103070800c039105a20503d01080340d550001c1c0185d8520b26243c0909069500c0d040c862102d00d01c400448079062400c0540005007010103140c001d1815403401c00050002c1101001594a516409006140206018240f0b00450804000025099804c00c030360301d16203940c0400d034148943e80c1c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 582287994 1250 582286744 582286751
    0x1903080105090714090a03150f06080f1e03040b180102060a05240f06070c031a010602120d0b060301180f271a10030c1a03160201090203071404 63
    0x30745081010310030007542c0140100e5500540b441d69809013001405c481540281600422562a00c1d4064207101801040710419500d600d00d08a00c042c921418000d040881d000300641da0380300000650359020548212241101003203685c208200030400c9030003a00c0e00b680c60503207400d01500385c280040b1502a2480c0580512400100c424080d8482c0a11410141c440d9a044e00201d89000b50300411070507e80c2e80001030703600581400e1300c0301c00062544521a042c1c01203030390321314200180e1020501201000e90756400004005483c0d0018000301c000c42611003c6542c0c240c1d420941c00103100403a00c1640207000030000080e4070074500c1c50116541e0584170207105501a490300182201c410190031000303a61440d480a4502c44440d4480e4001d41c4251104200f03012092009600e0200884507241101c4144406004101a2100358001024010048019805503e010350618000100810b064480c480d0040b41083e1003504600599500581603510181c0ca03000303103220481e10441254000d906 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 582289244 1250 582287994 582287999
    0x30406060812070f050a02220e0d020706081302130e0c0a0303050d0f09050601080304080d020d0c0305031f0e0a2a050c1f020a1704030c2319030801 65
    0x40c040307068080a0b000a000358548051980e0390318095003407001c1518580318035400b1000580700c1c2046000c11444030740c01d5a43c901080c54a0070309407004c1092055213900174000c0040b00350b400249050030746286041c40700c80c55480e05480c584c0440341520103980103016426062149245521414108046000340c078842c118801c188594041d0604c0028000b4004108501c00d180042d0720290000a1000001c0742210f0a501c1d95442c104e000e80140400e6000010104000f00c01001144000212400980b400303140310070001d800d6810103c405001d20400000049002c502041d480c525040d000580100241d12150b0b81c94850800321071040810b49003104211003444094034030708404860680e120f00441d80f142003111140c004900c05401e51092480d5202c00c88100345095005036125500180c4818144a0040c007406a41c404030003002d41a406210220354001d15124406030071490583d03031076802541309907107403802c2c40d40c81000b0b000e82c0090340c0c240108241a0f0704401d010b5594241580d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 582290494 1250 582289244 582289259
    0x2503080f0610030b01050403020a0305070e0105090c0409050c0702091006111b040c02010209030607030f0b0f0f100905100206100e01240c02040f050406140c0a080402032103040606 79
    0x140240c03403803940a0398552241c00c2e202c0c4280c102d40a0514103152560516a46e076002c00d40f0401d4031341080722680c00099081c052410103246050042c2400c172011000381c00d052219940f43d118500401d020030352078000103034001c00e480301254640c41c0e010300240c4840c80c1034895003c1e02010340c09040c000031208035514a00f071500140408041c0e00805100410141103401c0200030700002c0c103245c081d0f540034040080140c0d0103000c4584500c002e501c1c040303500c1d160241003030308541075140c43c948901200c3c464250551100401250301504c00d035400d000c2005511420756100d45c1d07547c0155032000707800300605183c0750b01044890242012a011841e02e9031102561001c801090248501c84060103800c02c045040e11102002c10b11142d090046c080710254000c0b40544820101c0d5222140c4c980c42804108485481512a425202c800c549400c0c20072440c1c080c564031400042c00e0810005901090940d50705000d003c141c160300b5200443c1110400c00b00301c0301c0d600200c0e01560160720b00140041d820 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 582291744 1250 582290494 582290521
    0x6010c1410051602070e1003020d030f0f1412060a17010b040e0a0b070c1412030402011b03021009170d1b020f10020a120509010f0c02010204030b1506250308 69
    0x5000fa4024124076400c001001d56021401407105079034002014000000d41c48400c110280c0502036914508850400c1c2000fa042c040000700b80d2040299200c0c00b60242004072003501c3d071082040d0603800c50b9481b0b00d00000d0540400e50001034142e00e07041203046240c041580841c0c012002035030244140e081141c0015242c1c03001d0f0b00050118840c030000102e4040c420fa02c82c143c540c1c030802e2012004a0303801055845c205810060f02181440001848150760f04007000550700b088034a07802c00a40c0182e58000d40760700200707840344d16042c0c80744101800c00c02c4100e100c140c4109080021511403011544420151007412080c98140032406000c01502c1c0c0f022948001c040c18500060031450300b050741010080d0b100e4624201000b808542c507506481e81401800d0003000703000c00214084070f9250903c0203c40005104038150381c07041200b000000c00041d82250301c0042d00c8181c409003801800400c00c54410000090024018140034440c071560406514482c14060360352000a48c1c2c900c81502a903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 582292994 1250 582291744 582291781
    0x70909020d03030203180d0e0f040504030e01180317120c04030f0f15091103240103110a12060203090d080c03040f021504080604110405070504030b06010c141005 71
    0x862101985004a400384e001550040c0e44842c10250021000071100d0801704084066400540c1c90404407020740391001034052201800c039020071042c03c1c55600500383c44030030381040c2d05001810b110300401444542414008640000050b62003140b90100046140e0005600c03c1038480460007181d02c807040841a074090b0303544909040c8054441c2c3c1c0b500c51165103003800032281c05070003003644072401000340208070406106907940841100d8140c00c05040111046485c1c00302084541a06c1c039404010f50602c1c11241c0040c0c0320404540d810021800c108a9500182604201c8038000c0701000100d074002c520610b40202541c1c4a109036400440302c00300d050f07540c3e511440c01480403d000c540e071400d601825510051400007058241c040c1e401194020f40e00460243d081038040000f44400003400c1c000e850303c2100c041005c1d1901c3d003000340c103601070350101030410203201c1d00090740360340908011010703a030301301440d89540320742c410007a81e644031101011201b050400001c124052001c0605012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 582294244 1250 582292994 582292999
    0x92a0201060f1e0b070303140901051005010c0f0c150f0e101107050901080a0501050a052a0f04090618050714090310050f0403020d08010f0303050f071b0807090902 72
    0x500324a04014080800d00840c01207070660b4110303c000030040000c1c1d005103d1580310340c0340807600c01901203130541c03140da008000180c0c5034144401c0100d140241c05540095403402d0070400074003041401c04486664842c100148061258040858084a0401704821111080e900c0e00704003103440e14200c5540b941802c0c042e4004201d1a88001c40317a00916242c841c1c80240c10171580b100b541c401c0000c05d0f20300700381e2000341c450b0041c81105040c00380a028059101708216014401410070f080d200b08081c075070f00038565081c48000410b0318030584100845500e283c2c00c800740e1b07480d5903c0d03ca0782e07002031070a8499001035507950a02c1d240c00e650307580900d0384201100d80720500c0070b0f030450318170030201d07031041c1e82c0c0d2075243c021190340742034540080c41440c1c0a10920342c40000545010300d0041c0c906911101c0c04424004032000411640d04c00d62180750a4a615241603925210070442c140100d0107a42c100801000217551445080110129910102c8142008484000b951250b04108840d28614040d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 582295494 1250 582294244 582294269
    0xf05130c1b030e041113120506070f09080f15010806190b0105040515031f18020a0306030803180c0a05030319090f0308120c091f09092a020106 63
    0x2001c0d4035071a0714500014000d00307003620074403155000142101d0310080800d400d00400b2401c40743c99041091a040640808141110044569107502d65a080018800c404004660141d0401207114650f060300911050048032503003039030014100d49070a0301d00300524a014621000290000c0c0c00030700715000d21072800e070700301c0c22100d01c140b217502801001819605000c010040014140c03180001c5c60070021803900c0c41c540700c0c00d100200e030030161555050880c1041c8a54014000034a81d480a0f4450140c819030041e501d000c07525081c1c1c054140d40d800a081018080200070581d00296081c0c00c1a000d42c44c20b07102030782d00c48000c1003145815030040c50b8144e80148409e1840350b1400040245525003400c00302206980c85210698030200c036042103c07015008612007c23500c84100e03d1a41103a45100c04034101400b240219100c0106a41d02d0740ad040c481c5451803091070300600840c07000e414403850510001440b51541c0c0f0148650701c061f440032003001a0740521051040c458031058401581d03500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 582296744 1250 582295494 582295517
    0x6180c09061012020c1f06050603070503010b0c0a02040603030e10020f070302011115092a0630070e010e0d030504030b07020709060e150d020907140904060f05130c 72
    0x49403c0b0090300d5209840310b07800c210800c0701c2c001c10000c0390502a10802240c0003224050011000d0398802e50200380076500c24020702406603003060036241500c0c000c940c0d035500c54803040c0c0c540d8609011400c01039001441d00e1008010b0640c010b80d81000c1003400d60f101c4e900040800340881e03840495010221041e0460710003403005600c2548106440314800b0111401480d041d40c99641c0c59100740e4140c41140c0c05110702401c0c000e030910f2008801d00d6840c00f10700d8100c41500c0480d0780b5106092501140365070007500b1005400f4a001c1001c3c000c100c0303102ca0f0185203040800540080c140011441c0815000700c2c0d961480d1405540900c141c6506540f12803d041c9181d549601850000c0c292800791700030b4031400f09400d071240c460b500007800115182c200b1401c290000660f104a040c41c100d000c0e050210b06040036031030300d02c4a1a0407120a00e040c0901c4a24010034207428020400c5059005092840028035950112401da0680b00c3c01c070744405916044140d000701b202c0003409200080307080060b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 582297994 1250 582296744 582296747
    0x90705061c0e070819020111070602030310080606061b0f06150301060b030105060a0c020127170d020a080306010905090114010201061508010515093c130510050306180c090610 77
    0x285140d2503c103040100888004c892128208403840e00001700585c0003004200c1c49141208cec414000b48980c401401c0903050100102e1410703c59a40c41e1111050011407044517008108608411007060031305440c89401d059070f9240e095820a84c080303210390f0814030f0214030300840e8001c0345d040312002000c541c5040b0700c41c1c106965501008605905111420381d1003070780d0030841d03442400e01c1554070b104481403d040c000105c600307420032038412249602c2074468a050640004110034400d8004420540ba0740d98080100c1d01d8500503003003a07401200207400012500a0f02441141c01c0f0b50980003405002e807130b0481034440050a00380c440000d441d1000401c02c3c1c1c00c0890000340155181881c0070728000118010412000302e82900190201050715900200903011030002d48540404402080410300880000c0c170320300140c20f05c40c403e6681d5401213081880e80007007800007400050306490543c07500303600c04107000b860315904900c1ca02030310380128407910b44010030a10801e402091090b80142c036450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 582299244 1250 582297994 582298033
    0x10f170718060819060f0b010c0b0c09060d150b03071e020a080309030c0d09050a21050d021c03050c16030201090b0115091a03060603090705061c0e0708 67
    0x1009080c03560b40d82000302d0700090034050b00401c0200320300c0442d4074003000e2510104555000c40030103103007854031090621907a440507d402e01d55801400461007a143c0b0f02d90721915100c0c180e9038960082c0c0c00039050a10403502c3c0c100d94074503660002c0c024081d03682c8102c00041440116000400544201c20040c20018148500c001200d030b40d2044031449011607a503409182d005484904260344045081c405038002003003104120001c0785005004a444d041c042503841c0c055000d40903100c06070641c803000014125a83c80480c5800008480900c001805d000c0d44074801c0c1c1c025410344e101c0030741d000010103000b0300485000c0c4001240540c5040303050388401d000e0401d420801c034219500d8030f01d02d01c041585420340c18003030031022420142a44012802500800340342d0320013400c40400d954034a200440680550f42e000c0310550b6402d03900c0e41c49103025410820750350019030703000c440400c095800c2e11044506682c11002e007070b800c1040030800b0003900e945000b28495001c069000f03440b03030045510000c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 582300494 1250 582299244 582299279
    0x12051621170d0608010b3a12050a090e07090e06042025111513060306060305090a050a03030f020f041811070b07050319050906010f1707 60
    0x4507041100518040082041d40003903000654a0340b030b070070305000d00714080c4190422100110b601600c44204200c030648a01603940901000896000600e160081d90208550b4503550210040c66802070355070005e045900704a4200000078840302001c100541e07140d00146c001d44c0e81d9200d42c00e11902d400034440345801c001b01440d4010351502c000d10300d1500d0b8240401d001c010b607032a620341c8030b442c02c880d0700c03010320a2070b600c00807003a00f400706820203e103500b04035600f007903030036a140c0c80103003603a81c0084124030039039406510031000f100000401c19450380c026019200c0700d650500c61505c4510b1001e649045070b030030203840b541000c4903580002c1c3c0a6406410b41c180d00c15005424915010840440342e0080d610815640c200380c4c286421006042c4074071061966a03d80007400c1c0303501d540300c0e09080c07400146201d00344040040410701520381800300300b549941a040900403440c016003030b2a01d5420178800c03100c90b1542040e0100342d08038640e00c6c0c2d8203680c40d20001480c43c030781f812100c1084801d510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 582301744 1250 582300494 582300503
    0xf0c09581103060a06060f0203090a0b0d060b0a03090c0f03031d0a05060a26040818030a021c11010504081b2b0b150112020c070f12051621 61
    0x4146010790303803410301c0100c1c416610f49800050b442c1c5011805400c0091000d901402c5400411505843e641c0b80340aa00c255507210300c03400d86485040030060000c3c00584c200b82803506c004100c90001541c542c1000124030f00c20b03410000ca442d40d411611303403000ba0f02e01004004c65240904100da42c0d0074461500640b10000b806c9000f1540e540c030203e000c40d4000481c07034000807c48038650058010008490042c01c41c0c0c491000c0c1c07540780946070f902080c000c40030241c80701040c19a00d501c09940030802604c842c0d40050fc1c0b203440101348a081c4c2071a110001040b10340440301c00f040152507000c0d01c02d030b070f040f5a00c020150410701d813841420030110024601d0550b02400d143c04664043c08500d4021004014460519102003003c0c105001c0764007000300440100030041207000203590740f243d0080103076610003901684a620449a250605500e50080e00c02401d00a41c000380040382c0e40b0002c030b8010301030b509480788103020b0300242c02d0145035806129082c1005101d45a41310010060f01144503014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 582302994 1250 582301744 582301763
    0x7060c0c0206121e07021501170d0807050702041d0105160f030c050c0601060e011d06040b07150f0b1009031137090606030902090f0c0958 61
    0xe00810724800c04d025504500142e00c54044070240140908245002d4100d50310700002d12071205501e00d90341c9503400000010046644041040e03940514141c41c41c0e580d000b4024000d6403048092600400c0c20001c1010f425824680810040c0c45941d6480003500c0c1641d482d5202d044207100b090300a400044050000c0201c100f0100315070300010321880d800380103a0380c2e507545503102c0034000501414030f181d40030807458a402410301d01a60b0f18800c031002c680c480001d064a8400904050300801c001064030200035052407041041c40015901c000484c00c01244c01142d14030300150100c40d40303085404000c003c00448845810580740c529264031200c0349013030304403030704104001e801c10402030484102200d107445000f091040810030b014140c05070110345810010210340d034000414000300a00750170300d12518a070210301040c0504049541068000d44407460308002d6200c6166030700b0480b04403e03050b0401c1e510740031850403803d443c22110603c0c81010b500300d080c070911040c0c0441e041201117075040030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 582304244 1250 582302994 582303031
    0x180c1e090510020c030111030103020f0604150818030a09030506070504030213050a1b020105010e011d060d05030903011404060b06030403050a08060105090a18050903030903040b09040b090c07060c0c020612 90
    0x1c5c240900502040014801a220f500d98810f001c842e502c0c80641612410b810f100034480c1c0a094a200e61010b4000d00d061802d03078545410300d00c045000800903054a000c0000c02ca124250010303040004c480c492030844507a580c2d00b4108940d2801603010007944181d036101229043ea140341c008540069141e4400680c40315042102e24070100c1046880e0050703515070340100000c0307501d5451503006004c40d680310101080941196a588000180b0152013030140100110134041c0805c1540c5c89150060001c0102031601038401102c02c404607170807035415060840424840c100030081d41d01843d07050b00c0707071400c0c903d1001d010707180c101000b004641044418020b8150070768502400000030482d984100c5004072503001ca9209840c4024803040d21070f40200144806c0a0000007280d0880324420a080d40300c0040300c0c00203000d0142c04045c02d80c8660402c0911590060010041003454070410301000500701c0b00f1011380303401606d4400a507014000f030203200b200d92030210f0301e20f0340070158001c581d5403400b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 582305494 1250 582304244 582304249
    0xa051507061103012c04020d0311072d0b0406210b09010b19030b0f0f010201020403051b010f0306030b1506090a032009010b071b180c1e090510020c 65
    0x1002640311700c42c0708881c1250300c1e0f0020751312031202c03500c0390341c560340001a407038030390041014054581802000c1100203032035040d142109008140241c906511909034a0250540742400301030b0790013000781542407810380015040c0402088a0486e0f103991500b610400328040d00624601d10204115031468486480d1100c1d40e903030040d510302030710346034001544a24202014418882001202c0302c01d061508421464075601d03124a9003e4140840741c140ad017842580040b8003901481e48014018410308980c61206a02100c0442000700282e845200060691100314242c075103900c0013626110458000c80d801c00660701e51041c5162020b041c46252140c1c00020507504182580706840c2043d507940300c150102a541600701440350304454005044d4100940043c907441031010081c203103100c0803021108000c0c042c1409005207641c4d8415400b0401c1e0a210703401428404003520001380a0100200c0c100c951035241440903035031581c800d0b0443d420322042c0210408001c42c0c240a40c441c040042c400361703 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 582306744 1250 582305494 582305497
    0x40606061d0321040317190c0215091903050d1106040c12020609030d2a030504050402090d0f0804050a0e01060806130b04240b0702010507060c200102180a0515070611 73
    0xc040011400d07074500142c1e11a01844500d100304071f040000031040071000d84e407190081504407440d41387e16131381c594501000641100c9620745052503c00c8454000080c40000300d26400c070100c050311171691744544100042d842e8034040360001d2030002921340500ca03000c0b007071251181084c80949414070b8007003503100107444c00290204817030016030108540c405940100a40f1005d8100300440103003031316240ea5000e8103030301440c050300340035660114a8a104c0d03503c02e1307070440f4201e4000b058000046038901b007100e101e80c450f00501b40a4150003d00081c080710440c3c4150407104159110030b502c1e02e0700400c00c1f0380c4c000c124001419a81d200c1c0a9121942d5a92041c8514610000d20342070002100744040c45490800398091015070005000080c0981d80000c100c2e0107440c0e208900050003036450030140c4143c0d80c00c01101d0501c1c581c4042080b4140015030042c0500e041e203018100391440e13074a0800403069458080c141e00500c001c003801c0300d00c170210006032070301d10310503040410411130103441e44629 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 582307994 1250 582306744 582306773
    0x305070c15090506090f0904080d02040e0915010f031211030d0906061706040f1e08030601110109030e0d03050d020703031e05130b041505040606061d03210403 70
    0x111541849001c0306242c10040c810001e01c02903e00c5800c0545180c0020300c04410000024044c0d007021001800300301c80241202c0c0301580400b411500c031a202d80720070341c00000840e0a400ba80c4a0052803607041e90b03c04011504071004010701847d054115582c00c0c071040c6c0c07940000c07402e1000540c121104088184041d1020904068000421035403900b400002d5441a82c4042e03000c41c00003d8007241e16030003181455020f42c03c02004102e106180c6040b2080400e0580d904441c020b442031070b2420010308400450041030241da800e40b0724180b030304050342220820280100400c640402c0350f90300d82403884070340c1701c8540a070a02c2401c00000107048000c1c1c0c0d01014007180001e607110100000f0310072020202003907030502c3c0c0e001c1000d49000e900c07084544050700070191403200f4140008042000e0701c100540621007007103090011381000e15011300500150b000d4403020884401c000b1640700560008010f09540c020001c0002c0658030100b010701d0303d011418400044d40411010002c01c1909207007040d0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 582309244 1250 582307994 582308009
    0x10050d0903180504050f16020a0c0e040606080105060315100503060f0421050d1e0221010626040611070803040615180c021f1401050f0a030b040305070c 67
    0x40e90002c1c61005070182c580340c0c0000344504e10b0304081c030900314100543c080d4841440700c1801c080c6001908283c2c6031520060000b08694880400440c0d0001c444003810702452103035409100da9520342c01c0b894240c880c219030b090340642c04450303030400d107401c21680c0941000c01c03c2050111103440381302181c2081c2044483c00040708089080c0010000c0152000000b55503002c14200808a0080c1c020541d110312950800307850380390f21040700c0c0c0075128000d544681e4020b04045603a90b664803c00030b00805650b483c4100710501000000c0e9007801500181100050f4448c200e003034281c00b40d842c0d07107000d80181003a114955100c024100010b1910002c10686001c0d4000f6130f180c0c80e10f4075104041d168000508805080d10708010011a00e61402d08c0900440c8041c002c280c554500d04224a004010080420100d070800502c90300b16566520006490200b41c851a8050303803140180015a0084007c1d20b402c609034031410000b0a0883e00f180f0340161281c6400c41c82c1c100340e915940080840b07a0003c41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 582310494 1250 582309244 582309257
    0x818120f0307170301030308150423090706020304060e01050c19050a11010e060d051509011d0c16170f0708120f0c0a12061a030402010807030504020f10050d0903 71
    0x40500451031020a4042500503883c2d2556045680003800c0410180c0480b0584029414124169880307030081d00405003081d80c5904600480844040c803100161560703011800380131400320710a403000c8100c0c0c054962075201d00001d0108100111050f40c41040002d2050080074035001c0c014058042d038410445c05600144140ca40314148541c8030901c5165040c14010349510320043c44d200d11080c3c5407001302c0d03500002825550b205040e003014144010b0560b001e501000042207075184c4500d64241880201410b100c02d81d00e00e0700001c1c0d5440303080710075104030741c0142c94240050801c1c1d0f810304508042c0c1818608103e90651210416000a9000c6500075808584a1806413070503490b542d10880d480c203c500141011420000b440c81595191402c105408865104008280d0880e400910111418030311070500074000201981080c0d0b8100d001880c3c0b000844e4002d4804d006d80c50161750002d0400c00e02501610401c58a0b0301412400e406200b414400b802100110f0700c141140310b8001e88485 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 582311744 1250 582310494 582310507
    0x70309061202031e0c0c160612020c0703140316030c140d21110d090b0702030a0e04050a0b210106082d120720040204030818120f03 58
    0x649854040070300ea0301140e10502c20803841c0b014450076812013040c80d4210a0b026190001184031911441c3c0000307010b440b501481411740050a001c0d601100e102d99100780c196100c19000c001a403007088115844e540c0f15801c00d0010441d01084841200904011a85008149070603400007000a58042e0b0104100102e000c1c03d00c010005040e1000c0da200010740b150310041107020b000d00c60000d0581413a21114001040c54440c41d600460407405008941c41d25030340700e007660310040c01802504841e82400c3c10013260900380000142c920010898845d524080001ca06010040c10001e0004011540701c0b00c840000d501da464006082c500081501f4803400150040c880c2522170030b9000d002240d00c800082544a0304000076615170880d0300715060003202c442046a4540f070401c0816803122040000c02c2c90401c81884086030303003501d46450ba41c0b0008001001c0108034003540c0300240c0460000c00445810703078898014403a511900038200d910b0a40258400c0c1e14090551001420580c07000404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 582312994 1250 582311744 582311747
    0x260703050709200c101a03030d1b1103120903040f080f0106060912020402030a060b1306030b0105030105010f0e120d020109050c0a0f05011101090609031d092a04080307030906 77
    0x4581d00c07030b0070ba444024138003180020910b43d1821005001c00300d07181e55114030310040000188801035008001c0c2140e031038010104900000340380c051442000c2d85040c800c4401458020320141001892010165052034452511540403110003004420280002c02020503e9054115400c010703222550003030030340b52403684020b421214141c01140034000e44400070028075281d85620b0303080c1c59050304d003d0b840380c89500910740507086c03540002c1d071205004103502ca00411080300ad54111001640c092004071031030001134820348001e01400d40050303d19024540d115004900c0704078612006042c80e4142652003500c40d0070885001140c41c01030351110350721414890100206a50070400b29805901d03e4501800100780003840d02c00c2905012515140100880080d48000202c6402030380038040e05ca181c0c60020490f60728450562065a41090f02d2103481c20305030300c417a21581d1082e808030720100e884c00000c1101000c3c04c01010006008020114400b0810320203009001d10030b0700c803c014182003040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 582314244 1250 582312994 582313031
    0x15080d11061819030c02031212130f120306061d0f090c0f03090c09180a060b0607080c0f06070c08070b1905070e011107260703050709 59
    0x808100511140c400c2a800300c08140c01da00a5002e101c440c01e00c00c07880302c601d0f00301004001107103421504405588107264000708500c030818401c80540c2c464400c007005483c214040d0020000102704041e001905c5000307450b00c000c15050080c01c0d020514030007640d403022904640d081c4000029241c00041001c15041700c00c40d00b000c06008035411003041180301248541c26041c5e0414407520452020458001d1204100c8040000200d9955981e24221003500e80d6144011000c1c2d015a600000103001c40d07104034280842043c401c0d0180a007580c03a6215200a0201c564103964004020001e00f000550072380d000b0b003070315929400503241941540c071149040040c0184060144041c1c0c038000000030302001e00b12003034141d0080440d0000e840f032042a510341c0300b20254076488549800300340101d454105101103c0e5400984c2c41101a07603407014540c0d00c0c0c41d002d1061070303441d004a000142002111580304d10b010301c100c0f8100c03058030303980707484441c40c16a003035010810080c3c0d0707200d016040304110720 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 582315494 1250 582314244 582314263
    0x519181103011e0c050c03040b0a17061e1c0302060103120804030909051308070b0a20180f06031e01080d080601080601030906051f090603020d0b0a0209041508 70
    0xd008100ea60a80701c141c07041515001c101e202c100740d95070b41c26002e0038040c90071b40c0c9407031383c050003101d440390748030340503c243d6a02458400c0007080c80018110070510408d18428490403004c0c140c0c2c400c20344a2034001460100010905521520301c0510026101070b1125610311035000794014442c0d5450f50a01d0588010040c40710310030440d00070100000b081e00403003c80122840e00a0004885e035030160000c0340301051a10041a0b030100040d084c6c1800480300081e030040890030301c00c02c0341e41604410041c050107000012011000240401d415450200311614555180070700600c5600044000140706030340100c43d8120500c0d440510807644011074000b00d405000010700404400e404510701505c499401440c82c1e041284000008038180d00c642c1010610903030014003409541400401c003904088021200e480000c1c00c2c030340c0003c900440c0e008402c2181e402400d94040c0520f00d8030f0b550302d9807400400780e100c00344c0c00700314640c05500c1d1823181103000b10035600c003900103030b09109545040000c5c60 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 582316744 1250 582315494 582315499
    0x15050f01110c060a2007050d0f03030905030d0e011404020a18020909090607090806090705040513020d0c05040b18040201030b0d14100507020a020102340803130819030305191811 78
    0x83e00c041c1f00c0b58840f59a5840080e0700031613454900105881d0841c0a026003300c018258040400d50300000207141c1c0040c890340042e480244100c0000c52008585010200c40181d8040c13020503003088140c43c801030389911043c1c003110243c9444040da0102e43c82400585044800b540a01d04000d02954020b11079000381c803000f40500b500d81481152255903110300e0042520460759840412200e05078040c3d042046a4043d0840300c24500a08048240d40c00f58890240100d04121407455070345800325041c81c9001072054100c0d910703200ca800460040c01140031458000c00741d02c0000010070305103985444e0207030f1520001c240002d20f48900c101901d80c0584041c00359841034035004010307a0007050b07035000030820980500980c2c0d41882c5140854120003c0031214190300907020449410100040c18540341c2207d21000c86a80d414401d5910a0f501c1d058113003c4020f0145240040e10070f800080e040203003c0b211700503c0903000101070072200ca6034880c0480c49180c404003c200024241d2643e9054000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 582317994 1250 582316744 582316753
    0xf0a17040c031e0204140f0105011704080a02030c150403020c04020408030a080402031e07140a08150a0f06140111060112030e040204080f1015050f01110c060a20 71
    0x155035000d51003165804010288042d901900c000c02e40952200f007049a00100203100340204a04100314119055680000003412080040b8980d401400d015040c0580c00c01c01c0c01c0c043c0c0d1a0703114200345822900c030710f2007140000c1180221240081200000c0d52180341c05005d264241460003925110600101c40c0c003590062008102c9c1810200c10341e0018902030808100035569440040c1c14100800d801d0003044520403146241c03114000744c500290303041d458a21001801400400c50203904030f2081c1540382e40f060780c8480017450314448554100f0030125002c50348032071101248003510b006030801e407030842c8416100300302076a00121600c40d1140300c50180c2020350504007500c1c01001c0101003c2e090104e1408400300c59242d544c121402013503401c042d10501d14410301081d031070320400750860f00e05a080c0b00a800e205618250381030121072004003d070000e00c072100015a5040d160402c03084050061060303030111034542000801d05c0d086140e4890010759406084940c40c44c1c0c010700c03401e005502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 582319244 1250 582317994 582318001
    0x130504050103110f0a09050a09020f0303131211060a050901032a0e060906031e07020c1804080c060109020d0c0804150e0f01090b041a0603120d020c030f0a17 69
    0x480f000b5035040000c1c15203005403d4403040d4049000da60325544800c5419140a00300001c04002d6480410518421100c41210707803001001c140d41e130302588021541c400300c0031500f00031242c0e00b600325107100e52090b0b5040d0840c00400c6d002900a8010081040100b0301c001080d04d1250ba051113030605800403003900388111040c050320244c51a0411151400740003001e03c1c1c810155403940150303010710900500840c0e9a1408503030780fa000d01403040c881d08098081c10003142d45d903400841c00d41c001da00007038183d2051240740040404200e4000d803050b240c3d151b00f040b15806244080c082c0901800650070302580d202c581c400ca000071583c849401000f04004803081c4400a0104000344901d000c0e0010040340422440c02c02d64140000c0c1c00c9400c620750300c0c1070a20400c1006a840303c51190740600246c01e21034400d0540d0312042c207400c8804c030303915802207050508001c5201016000103910054014142503071900300d03901e035504c4840c040c802e10b000440c00103200c56101c1c0c0d02c8030340300c0d500036030805d441c1c103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 582320494 1250 582319244 582319253
    0x19060e07230706150f0e010b09010f17240a1406030c04080d0806011209030816030f1406030d02010b030a030f0c080301030602070b010e1b070c051005130504050103 72
    0x85041da80d65459075159844501c1d0408003a2407189810000811211880200c000002c1c0024407801c14140f03031001c0005004a0455003140c1242d130048440c0c0d20b4034030b08400468524283c005802c00344505255020380004003040801e2080713185003034a5016401902e064a41d00a044060303d01c1074070402824000b030040300300040c4150906840b101d40726201c40d61121864080c54010862501c04c810420203071960001d0800d0003244280c0b501c1034a01c0d0519813100540c0c4583c035014000c10444070114020140c0102c4000ea44012071400064059201001000341e5035400c081840300800c090a00c040c030310b8140b041e1107101d105400208105071205020a40307508014034054148040021071a00046c02800040c0c1c0d81540302002e160351750703100d00d003400080d00b1140054400418010012600042488900e40200680c1110316038548000206078140d5120320380844070410345170300000300f03902c0740c40c400c0382201c1d00c6449440c2c031140c0da420380304900301160340018451402c1000410205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 582321744 1250 582320494 582320507
    0xa0203060427060515030f070e0916030201051605070b04061e0f0503040507090507120b0a2313050901271203020a031404050706020d02060c0f03060109030b19060e07 73
    0x455100401090f107558155900d02c8142c9a00b05c2c550f0580210111007100310400b0030f5841c2681d00289040600c0c2d1900b0840c295100b251080c801802c0c00c51010901c0590700941c06010340322000100090605075650b50035040419a510031004d10310045028000700c0d4010301d5000161200c5031101c030b070203204500000c00034404100c1758001c0c420000b0110741401810300a00c4064041c0b220240f03d141018000204030982c0002c03500101031901061a002d4500121018222964040000c0c002e8a04008403210030002155950307006068008000035492a800303014450007440e00001941e4181c0700c5005450490015005c41e40109000a0b03400101c0300c543c0404e5449982c82c0050720344110b40c2c001e50080c5001e034040c04204034840100010490b0000d904070075105a075080c0d4038a910314131f00aa23650079041e910030152000a20441c5082140031003c0c6070721600501d04103107041d40e25180d1082c03200e0706442200e045140c5007010604c0250794019200100074114030070805140410000344503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 582322994 1250 582321744 582321821
    0x109050607020a0504110c030301060c150203150415090f0b090108030c07090c030204080a050a0302100c0c17190e0a151b020f030d031b020a081b10050a02030604 71
    0x1c3e61b807094040c2c0c00120403029101842c544000300c1e562940c44d800007401c01c891002d0101c4440c00b12152019401d6240c0c02968081c5141700c01d03028000004a08200260480c00c0000030700042402000038140b00c64001c5010340c4484070000200d007140c40e028003150074416000b100c7ca40c0d00c2008a0303008404000380000841d02c4140001401c14000c50084020348518ae0020a5a00c612030408041c81404202003032810312940888140d10702c0010318005a41103011a038020076428010300e00801c060400100c0c1284801d42618500404080b407108150340117005040040c5c4c29080341505828030042c40c40241141c68a1b524215a00718401025903a070142040c1d0201211240c150440d16121244004032000a0543c0e0480200c40c200500a00341d50100c401c40d0301b410402c1c0c01c803c5001080c14200b0395088600700e4604030342c0160504a0405121401e81e03644601d4a28143c880c0c0e051251340d021341071007500940d490426100700021350b03500c1404034807000141200c0034000f4420b407922540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 582324244 1250 582322994 582322999
    0x14040e0d0c03090b0d0e0c0f0a120507090203010e1e061c151a0102011803141308030403031e0206010521030906031006080c04080604060f0b0a080106050109050607020a05 75
    0x30903038900c2d0869803410380340d0281d546241d02003040001421310344c110f8071707180d144076084030140c082150401c520340c05e10790700c5c06401054081d802d100c00401c94150400c182d00880850f0120342d9107814100890340241e1001ca101c29500042c0007003249015a0310482c50541c0b060b09089041c8500000c004802c1005c3c0d600d001c41e000b421040401c1003061030844400401141007000d00076406001000000008042c0c1c0103510f0000c4054075031801d0510b0301c8184c0d4050341e07540c0b02d45503110800c0c030341f0360b014590034500802d950a002402000400050020354400d41c0d80a0202502868001403141c09122134002d42d007140c00140080e84980c3d600c08031441091101c4c40c0c401030300c0344425080d407095601598002d04008100b01441e40203104550444000e40e070b03218069a901442900c0500803405140c8154011601050104845401041c10a9903250317001503120718420000e9490500e603402003010380d44601003000a0742e04055090000c2009546191074032480f0340c00161030380c1e458010f061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 582325494 1250 582324244 582324257
    0x60106050436150501200a060b1810090509061b09010309020a090515010f120506011b0c0303080a06080c06160b042d0305070311120703030614040e0d 66
    0x1841c45400b69100990881c10401c208251803203a0804012070801c0d0044d14007051000f0b0f001c440e045a490801c00e007840030207015104882c0e00d80d81d0700018002c1c07520307929800030240c2c0f4a5104491000c405a02032285c0000508403540382c503556000340d40c4010500700160304400100829144c041c60548950740c2c2d03c203200e0355106900c2d801a03000f0700b005040a034010340c00d6000400c610f015540880e00a0248184040140407028011126070405000c00350003d69241c03a445005000b0380c00c500d8001c5014180750b900f0071410b40c1034440940a03100300350f4040542803000c00501da040355869030041402c40b024001142000c1c81660b4541da02c07a00c0c24010b50001542041d5402e09040081c0030035807112182d805c5043c40d00740b0400364804006a01c105a06001c0d14007140134034004076064260303250f02e4040c1000c400d9141501c6c00000000b5250f994003d50501c800b00f141103100a05250303101e40c0700060000e0402d00403d10000e0f8817081240528544412251113840000300107114070518030f00071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 582326744 1250 582325494 582325559
    0x1170402030708030f0409061208041202040f0e01090b0703180308041505090d08010807050a0306330303201c051c0b2e1407050312090601060504 64
    0x40e00d4060958440f5a45000c04107254044030020802001101c0e02288140072141d1182c3c41490403684840000f000c040d0100302c20840003504c2940f0711485400207100041d8018401c0c01d0030151058602d43c840b03140d5640d0740e80010015003428a580000e07003458108050001100c40c441c0d109504000a41800001030014040081c15070641d0a0602ca440051080741003020440782e85420720361030440031950314000402d040c880003c1c09000c0398401442019044d04c4c5031212402010008044001ea505440003220942824810607000300007650060050b2440c5040042c503501d041010045a80344512841c400703001d001030595401c07a04c1562010701056484419601c51280031910b404030010320316001c0161804d540070103405401601da40004084030a0400138030a00b451007421070107800c2050040b002c0c440c50700079158989484605162a9054a40c1c91a64001800c0e01c41c005512208111020350309001040c0100203600340741341401d05044290048000486106004c0e40d0000b510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 582327994 1250 582326744 582326749
    0x30711010204090c08180f0604021c0c060e0a0b04050907050c1501060302120a050601021203130b010306090c120c030609240e010e030c0304090c0905100905010201140601170402 78
    0x40b0b600820205078104a1194241005411040e04071062014070140d24000c401294010070f4280c1c100f07030580003400ca140d840b40d081200618480810f03408841070810f0807400140807040c1500944580d440f07030078104074403200b000354042c0e49400c40702040c1014001048261100d070041c6421030aa802e0051b1038018400d0060310b000f5018049a9024220000000c0d03040e400d81d00414103c0009201200b85585081307100b02a40c100391960b0f40180d200300c406a9450802401a641192101030340e500c1c4000c50361150b200c0d200003038006840e040c4c0c3d140903031401c00408501c13020050841035a10f480c01c0c0b0090f15150300c0440188409011113440d40c05600410146042c0c0d00200750b210f04510410760407a00200005080b03450032000301d5884c0154070310081c078002060310b0900c1c200380015031a140c03e12a00002a040d6081d00c81c0610036403a50100300c0d03a8400c00030744500c405541e120b1000c1c41ca004002400e4840c403112030480c1d00c0c441c06c00d2108a0340c0c040024640d0030205884110309486901c003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 582329244 1250 582327994 582327997
    0x2090609060d0b0c0c06010e091e070f0906050f10120e030912060f0f0c04031b080706050a0f1701060c140f010b0f0301050c04061110140f18030307110102 68
    0x10010820010042041461003456000d04000311844040f100a6a2182c00207500308c01c0960b18010217a11021006881110088000c501c41c1400d0040d20f20040e503800040d11908001e401c240d030f11a03242c1c01e0074420b03400e10048405098004441025280101c40f1001e080c168428440d8415140c6401c000402c20b0780800807640d4011020300031814001001c107403951500d00c241c400b01d420341c0d221400300301c445034004845400ba0540540b1036181c2490f6640f4070103204500d00111011640d2804001040030080c4848030003000340792141941d0b0892031100030100d0442d40c00260078003858002104180501008440c152225418036035038030303152030074400212841d03d20800319500c1048842c003c0d24006404c160300c4510266514000c10303800d10101401e81c0c0044640e241005070902040000398865010b038081c201240301035441c01e10402e100f08007661680032282c04400704c204140007607550050707541d55000040241002a510130700d844c454403840040c010008020f95000c2503a01d0210a50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 582330494 1250 582329244 582329269
    0x80c070c0e042301050c0904020c010b0a1214060c0d020f070b09011505030c0d1e05011a011416080d0b030303090f0f06091c0504171c020a0209060906 66
    0x10740c520741460145000da200162400c000c10081d4101c011050b00404140982400780c0700c61180f080c1003d02500a01c8004c0d000302203007600540d250110705c1c04985501d42c440e0090440700516075680091402d0140a81d43c00200f030480951002c4d04210740503104105948140380001c20242c0e440300384031000241405000c1740078054441c00700c01d221004405500c0010700c3c0c0e040c4240b80c41e0456503407040545a07803030548026041141c1d6505003001501203555604450f504c2c1c00101903212070b54175840c2c21507121034005846c824000c0030810702980c100300c0100104402c061003510348010485c4290328800340d120001c240c0780001c84d008902c9695600030021051025017200d4480c030f49880159134421900c01d404047c1d00541c84c0a0450040c0441c03202d02c00c206010041007501c20615800c0d84d9070041030b03813080401505000114441c07003180f0b6900c1003031038000003d00103d03614540d8003200c50501300040301954060011b00d00140c90704803119510903030450301e81132a583c6910215810035001c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 582331744 1250 582330494 582330509
    0x1305040b04052815020f130501020f0d0c020f010c050303040b0603060f091507110d0503012916030314070f0f050a0e01081005060a0c0605011203080112060603350a080c070c 76
    0x807d440c1d096240b035181e4802111380913801c850740440031140c01034072403084020312000034100d4100c0c0805030600a0006004000624020561038113a40b40c5600350341094508075401c200791001e001c040d1904121b002d800c000300a04162090820303c11040d501c0505003c09100d1b1107581001134241400344090f8043c0f1501c410a5031042140f512000701f050303100340200c0a002507e010300c0e0b408849680f0540482d5544080d5041c034100101d210141d000c114480103d003050b85440100b080102e46140c0d440c00b583ca0303510365078a101d01c00340c00540040d4140101504200041c080200403640c05018042045000c0c2032410300354440c071559221495643d001650002c83c001120030032240e000303080701000c0b4040d0b0341c104156601d402c8203242a030101400903002861080051008141d0001d82c000300d284a01d000103585a5643d4a03071000d1400f0410b01e04103050a8407000320b400440c030034581da40d445800c000d64504585600040c200304005000c2c0c0408200101d9040308020030b02400c0320290011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 582332994 1250 582331744 582331747
    0x10608070609080120091c02061902011802010207090b1810080f190305220e07021b0a060503091f02070c060810141305040b04052815020f 61
    0x5031070010b801c20b500391190316003d40c64a43c82c40101d0600d40764040310601460101d070700e0164094104015440c0c42d9016090a4100002180050341c8110040004004044c041040101084030290844c5c03c1d52006c584081c010b007458400603a030202e140c5083e41e25400002800c1c600c40030115804924107009039070100304060a0240c408805620300b0100c511102c200d0760580d00c0344180c107403280448a681c8844447d80403401e4006070203035000d0403d003148031050502542000490742282c22340b607400210217101d000140b00c000d036414400480e00c150b6000c0c0090030380e0b0104010440ba40218850881044004004104020414060200d80342d00d00740b6030707000300300403080c10100075842040c040b96040e800090000300c480c0654038443c0300741821312040c02c60510380072500381d43c80b0340c00078034a6110740e05100c281603281042c4a864003950142100001d00d16007850b006140440701140000a0740310a0020200c4080d00484076180301d501c440c41010491142c04200c0180c02044081e2804440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 582334244 1250 582332994 582332999
    0x4060203150301150510170c160501020a121d0604110f060310060f0305010806191b0201020d0b030a0206190e090712061a070201030b0a090c050403050c0a06050a0c0501060807 77
    0x143c00e13414000707a400031500140001c005413030649410b0035000321854100f0451000401000d40003000d4160310104c0d003c0055074035440d6840340d089920800c405004525a101c1c800030b10101803113220100c207042c1151112503041b4060180c1d41e241c0c010001414070003101c6200f24542c032940300b4020151030141c0900d45074140340d0458500e0600c1405500000344880c07020005082c400d01503035048841401c082c0c0899140c143e004280740721541c114203102500c61015041d4083c02c2c242e412101d220640c001612800c80742c0501003562554820340f44258040d255000150352840200c0d41c11414045c00500310703c038a03c0c01528959400066650701008207020404d0030340d08407404920010303480d0804c1018984404146083c0b5142c8082080c20141c2031000f0790041d402030b0b00001d001240104505920703aa20200d030016100b40c1c60b07040380050000305042041002c10001c0402c02801156507000703c038180132000b409402603150001c20803022341ca03c001408000e500c400058201001a5166681c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 582335494 1250 582334244 582334271
    0x6040306052503020a0503040f05120a030e0c0d02031c0923330a0903062d061401080606090d050c1c0203030912100906090201030c0f0804060203150301 67
    0xc10962010707100b0302c00c51011101c014441e2007100c81c000b02e151140c90450315541c41b14848288001e400315041c0c40b500c1c1000b50a107401c1c201034680301404d9640441e0040e454080b640c10100b188540394080c640b40c000d180016500480d4509001c81d0603c40e041c0600c6481000321807000720340c2e01504140a21450007982d90182030005200d881040e24981c44505040040300c102103040314020051000401c2c0803011018680000c0441c008142f400d81c00d440d4070b0362960003c8402c4a001500414000384031100000268910034480b04d0960508004140c501b07082c800c01800f0070340c1190704000a04001415a035269801c0d12000103002c0c141d030001600d1407800a43c2d958003040b9003481281400207400d440c802d40d1480c0542d090b8003a000d94100317040c0a0611050a4150060511a0181d059518460b409030310405040030b0080c2030115a4401500014080f110448140010408629012485e0580103007500d6002a03014800598940c1d660328507030801008425101d81c1035003888811034149 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 582336744 1250 582335494 582335521
    0x70606030314090907030506030a08040e10050907090e060a0902120624070f020f0306090703020405010b12061002030f0f0706050a09021c0c051809060f190b0604030605 74
    0x4038460388910342140e102d060704818900500680560200003200080c48561080e08003982002001c2c0c01c036070002d03060341e842c0d807101d820a400a05010808000700030704800002c0c04580140310695407003649060102c0014070340c014501800b1a414080740100728503841c1ca03800440205094030b01151104105034003031070010001e40b21144140b01d170320000054801c10000045c2e1a14003088182d140080542e039845080040e004280c0c0e0040c0e40c80d001d81a9520180541885400307503070003401031241540704001c1241d00c10307003203501428400c3c011807641c2c420301c0c005203800140481d10210100040302c003ca207581f240c400c00d107441c0721010510218010701e003009040c105200e402c050041e03560b012a150212142144041d501c640c20140042d09900c501290605440c041c2039250000f944400c041020f84980500c4a07844411a074100190103109002040e000a00b80c040140d403070420401c2d001c005038412020614a03a641d643c040301503602e900456004643c40001402207140030507040050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 582337994 1250 582336744 582336749
    0x1914040501050609060706050c07050604081b06041e050a05030a0507020112050f06091914070f02011e0c030f062d030c14180f06120606060f0a14070606 67
    0x1681418000b00d55481c00c0c00a861030444060308940c105103040d101c51000c0c06c1c0180148000d02006c106480100d113050180a100d24041c1300c800350342d0b1140746103884520000714042c1120750048414000040d403070f26001a8110501e0100d000d0f00482c5017010b41c01c0c54146a8014403900c0001011000d054005d03000d055982d000f600c400c41115001c040300030907500d044550540b01190180028800d140034a5000d410150210302581808140c000280442d250314000240801e544010400304552200c203500c5132040310320003884103520116103090700c40d43c0110726154581d01e071450251018881c0c0d110813201e1042f0b02c0144481a81c40d102074402d0a00030398680d20384046620b68251840440c012441241e901c10605803100d894412580240020041076075804403400401108401c0419862070254020104c607080c4c40c01e0100411030250590354001c800c0390807003070400c402a038445042c1c4480e402c901d00220303074a4100c14000c40f40034052041c3d681841d00c010a0340710038800240e114006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 582339244 1250 582337994 582337999
    0x2706080f0c0405040b07050a1205070e12010c09180207061a1002030c030405010f120221060a03022b02090f040c060801030f0318090e0f15061c021914 66
    0x40c030000200b8002590300c00c48025004e07031828408102d09611800003040c0d240c520b480c02c0540c0500c3d44100318265002031b01d07804002140c098a900003894200c0e080034034952118001c024103803030210054190b030031501c43d050102c054140d911130013034041d80440704226400300c401c100c2032185040b6407500541d807402c0e840c09246004d00344840980000201c817030801000300210b0520346480c00440d1050300ba104e4201c03c2080c00c80d45207000c0005030002c0d105031201d030045060b459040603070004043c82c008107404d100718500c000410243c0c440c1540e41c9040c07290103059502808880391700040707140c150200250801c0410003000004180701e417406002d075219050720005503640340701c102d90100d000c0c0805001c071601c171450080013a00802d0fa4480c401074103003203c005039558140c0482141d540784c03040c08139a00501c0312031040103c2800965100212040d0202c0c60b17041c0100420601101504400d0f40010344050368015540d8a0080d6085d0340182d06000c800d0b0b90722005031314071400100400d00d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 582340494 1250 582339244 582339253
    0x30c1b020111120c0c1804080901090e070c03020c010e061b0114240108070f03090c1e030302010534020316061b0206013213050f0c040e012706080f 65
    0x219585400581b002e40d080c00800080c02070f480d1034640650b2a4044042c2c5030500410303040010304181041c103c0783c82651252034a0400c988581000b03800d00a4522120f41003168a1900e10200d58a14080e01c11050024501c2c03006205000b641c203004218095406043d101e078681004240c0d20080e0032480300f001c51050700040c18600d07000554102d101a5041030209140e039800c941410310940c44084820b00800c5100f2500c1e40c2c41003080c2c902258051118265602c1140c14818541c090140301e41182c1c80d1140c00020403009003004440030b004844c41d08400c2003500692403481e1081044d11b014103e94802d00c00c40040900d40480188402c00503002400c5042d82c0b03100b0081d0020642d07504aa180001b65120396656152004208040125098006071421170030522a2994100321541c2d00b40980e00052908102400c280307a298001c01821300c04808000500800c5a10740381d05044969003162403001c0213400007a10740e2000b818a400003005c0c40c056000842800014200c080000c1f030710241c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 582341744 1250 582340494 582340513
    0x60e01051014010504030b1e1501140f0d0207030908010f020d061d0f130c0b03091c0e0108070507150b040e01182901150f030c1b020111120c 62
    0x4028040e04035040b103000c11400d02082020800030520546d20209009424034040d00751034840c418840d05a07030640b80a07000840107002941c000622600040b1526082ca0800c135030800c0701741c068030480d0311041080e5004140c510400d030140b00d100002d46a0380e070007480010a81071011000b03421810281c0c0560741022030014080e4010014a603e1103158807131143e10b03944044e00070040e510040c3c00d0019540441d044040412003144c81c40000c0c1c0f081d804c01e1581d0b42000c030700312441d2103036200442c101c030b000b0180305510f03064001040a120210a00302045260340d40c1c10151042d01405c10003030000082255240e2848542e079000003d600d0040307400704101e00c0d5203184d15080b40c00c601000d04204d00d9864141020481d8005030740561202281888281c85401103009101c80017039000a505a138084985040c1c6504040c030292200f24602e030400004804d15801000405210071608141036000c0e00c24042d6441103040d0070310000100102d0701d809681440c8000c1d6a801322444d200b25000b9903070340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 582342994 1250 582341744 582341759
    0x20f04080609010b0f010e01030b1203180907020f0a0f080d06030f020102060702070b0f09040b040c0507030833010201060305160609050906101103090d0309050f0a0305030a1407060e010510 83
    0x400417070314040e5075042005c50394900660040111044950f030017601c8042c010380390300b010001041d01c1c110321200c007001c141d915024842c00000250029003036400c40508420030400000d000c0d80c4d0960000c06400c031411840c204a05a442022445a08035042010100501500302c1c1910b0805200780e08681965440c008100d854030790b140200b0f00740b40800c2205101c044014000340c00d202c03400400000f80d070200f42d000034040303550420110000c104086814814141c1000c1140c3c1d02c045031031891078a204421380c00c400c040d012014560000b04000000d10706d580d100f548002c01071940141190580b02c8000d1b40d10000b4991440b0322000280329920200d1241011b2100c14021030014050b918201c000110560300d03816114000d20031448280f04e00885030f55000c1d00e8005035406900c0d4120750505000910022038980d0100c0e50160421031800c00000e0030000c2102c688150618044980005080d030444613403048901c040e03d0542002000d03016098194003040c0030340364200184107a40d549058 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 582344244 1250 582342994 582343009
    0x10b2206020c12070b03130b0c090922121211090307030f1b090b13020702090f18030304230d0c0b2d04020f120c0f0301020f04080609010b 61
    0xd050050700003100d90012420301c00f205000307468503682510800c503100d13600f510142d041101e01c24a0240c1d1049030708203101034050f641c0e40140c04c5184081ca80703d01030003c81c4241301c0142241c407042c003c60a00482c0c06011241ca201e00d50361103035607107051000702240180103502d03894030a40c6035494000b9058031500e800c401c0f83e2111002402805401d0710f903841c1c0460491603c0400d580542c1e2998204e2142e441101100c806030149120014a0390354070410301403c800c4200311000580c0c41084100056502c00c210300740d00148070340c840e00c001e41e0fa83c41c0c1c510000500c00380300101c0d8070000c8144800c03c850007142d00c004428200701303101d026003420348480d86c83e88a10f030303030001103081c2100190106495024135644908042d20034849181083e00400c0c0303192403410041c20043d4501c046c0411850084d4030140f24003401c2710600901c0d04085819a00e450100c410386100300600c002c054a542c03800e40507604484481c0c072541d616260b50300c01e256191072086880d28415482d2080e4988181307061074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 582345494 1250 582344244 582344249
    0x1d0c1c0b0901061b0f11090117010f090308150103061a0306100504030b0c03100b0c0a0c0f050f010809010908040312020d08010b16110919060803090d020114070b010b22 74
    0x900b480c00113036460b10104000082c13801e5910241c0c0a403441c400752207106500d8020b198280c1c442160000c0107280c1401c403006800001b281c64246107000b00429070200205420150701110700c21144032420040c0c0007801e00f503105107904064a02070351112140c000c003451003000c0541d02d00c4007041801c0300c100c42500c51030000800300420800801e01d12900b03070700134680c400c200d41c086c00b10312a111000200384c1c1c1c000c00c82120b550350088511108100c41d05c14000002e15181180e04241c41c00c0c800081c100b0f409000303000d03042180c01000540c1c2c003802504840142504420f03d5680da6440f4102414204070b07006505015104404040c40e9082c0b0840e6214101d841403101c1c00c5c1000d480001c5458800c4040c0380a450002400380c905505954942903280100b13407400c140f0315000a111a000103131342903540030044035001030001100fa03440c0c440d44481200c5d424600740c21031007090414800e850140c5003020340103000810011415440b060001c00715074044001419000d550044549030444003030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 582346744 1250 582345494 582345527
    0x80309030a0803090115030602030103060e070609090c0e040e010b01140a050a03090320031b0f03090409080d0513060f0c09060e040e030c0309010f02071d0c1c0b090106 74
    0x800d81d80007041c1103101071070300300d001c03c000840e031100e140e2100854407000d6002034408a900100400c1000340501c2102009101040078040c0d0518062001c0d05903402d501c00c1540c000d8881c200c540307040d4820501410384040050040200f48000c1003803030300038110000c1803400b003586000000e400e250148152509410380e5070715540791510ba41c204034090301c001182101480320840c21800c400601e1a10501c142003448021500c4525405402d00c85206080310080300f038016010f00441110003004039200d59005550210302c1008034601074500f4881c404814114a00c0c00c001c0c00040c01c2c1002040e40041e014035002e000c0d503d0941d00c59800c0320a02030720a000300c0da008004108407405080d10061074031008100140c90f66240d050542540d01c00d20710b040c441d400c0010644510368002c80400e601c802d0a00c000c100b018184094851107503864100c104010035a240020384400d03d9400715040b00d5003281c3e1900e03402d1902c40301c04018012a086407842450300e20004280d0500c03031080141d480080303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 582347994 1250 582346744 582346753
    0xb0c0c01091e0b280809070f0518061c0c05030d031e0e030d06120203150717220308100509071209020a091b0801091109010509010306090513020a08030903 68
    0x7007191140c0c20307510107680d0000801c042c04040c0c804d01c0001510b9044600a61030b421118035109822500700790242d08802e50684042e482406681c81710780707003206110504521106d55884e41000155041100d582c0c504410956050403020480b084c15a1002c070340d03003501111381055491034158155000758940048094a8841c0280d400c100ca1b0001d00e50180d080082e00d1400c2c4102c2c1c0f0017010f80300300d5001601070140081805086003002c100e143d0182d00040168421403d000c40c0081008041074900f0010422800c0450505a002c8280c030b506800344d01e41c0000d44d84030354600600f5030f90302119520b0503444900703400a1345040001070306200745035558825492003808026800180520f04003a07800020b1071101154443e0203104148400c500b021540c00070000e00300009024002c140c1117401c22900340041524206030341e03025a11040824244142c8138a4250b004070000c007046d070302c0385403e035050805200141907442c01078040c89000780c80080301c10780c5404400342d030b0b40701c1c4a0029405178030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 582349244 1250 582347994 582347999
    0x1209070510030203070e131a040e0d0804030915170a060311011803151d0f060f18062d04111203040f081e01050f0601050307090b0c0c01091e 62
    0x1083c0c0c01075501181ca42000540700041d600402c0c041d07210181ca03007064a541d11070b2880781d8040500b04048001c021941800000f44550900d601c406441035004c0c00e0100b640085010507008001d0751020b0031414039005d801c81c80d208001082412500a0082c14000300d10209000d000e10780643c070140ca410034105074503107020301d00466406030040305c081c88000c483e100c08000030b80c01c4012458580400c0c0e1020840000070316405003030014211140319a41e001d9181c148801d0004150b00d580012070315140301d05071b1b440000000d402945c1038050404d078003031a402c11030035000b40d4102e40b680c040e5142d0203405100300004003428030001580c01a2611403441008034042c03034500c02c18229078120700181c900305503803400c1c00800c500090700b000c0441c1d00100c1c0c04610000c0e40044841d0682c0303100300203005605000500401c031034805031055040140000000b40001d0158030010000c0100c1d440c4c540e5030760034640415071114601c42b00c4e140020100140000c440404c1081000c03c050524000510b451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 582350494 1250 582349244 582349247
    0xc0901091e0b0d06090f09060c0810060e0409050a050607021207080d110403080f0a0e041b081f030c0e090601050a0b0c010612030503041b180b03070305121209070510 73
    0x40012030900700e0f0544a90010408507082d00600c002840c400002088042c461300c3c0c02415200d807004840108070004082000450b0000a12421a142410200703a40d00512000c10043d115400740607003280714102d400d00c108000011002d1095030b0340d50940705c52114009840b4413501c10000050180e15040c04440e1030040702d540484410194020170b00d00c1e017076590360f8135410b80d00150b00c0705803000d01c0815020b81058000300810185401110100200140c0e1002c40b140d405660351010100b124000c0042c3c0b02c40e00092a80050000c4081c94602d500d503240380c02211100c880c0104080c141a080100c1c0160400007041030680307100501e4200e0050406a00e00b003140c00140d45035250f907490f00d00000d000840d034100c0001d00d60103075482035030b2450581801210039500d10720703c0c0100098854100030040f21248452130842075181b010034210309c000c00181ca0700303a4541003e06640500c2b000d59000c40e1000006004200c1001c0d060f42c0301e543c038400c242d0b4460a4610a0542004805a6911509 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 582351744 1250 582350494 582350497
    0x50601050901171009090b0f0c0403021c0c260f010902030601060f05071209050301150312140c2509050c120c120a060f0b030c07020904020102150c0901091e0b 70
    0x1124039141001913907603076100c010589607921010346508a507030050040405081682c01e074003810000409285c2840e543c0880c812000c1c459140c07044003c1e00320075404125075107605000401c0b0500c902c0310317109281c001c40843c0102410040384180b0079030307058581d240c5040c0500c19015030000d02501690b803030038000362403882c0402e540d44104607040140070b0028048006194080b1070540e20000c126042100b030500311601180d442c940118854010000904000398002e00b1047c0d0f840c0c0350303603511501c0c03000c807c0500074400503120314029105d11051210140111021224a0101c280312803550b41d08078008640c015580204086001c00051201c4c0c40400d030f245400c0b105482c04240741c404003100415465000350f9100289075240c0008001d6130010f681c114020780200312030740e0300e581046101d03540c2d188030b0714100901482031040001c00750782c002c4c00340542e040c440c00c148070034620707103400c003542c2da41c0c080c8e0410303030110b06101c030003046240c154180032009009810030760020300d0402c2c0004085 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 582352994 1250 582351744 582351751
    0x706032a1209030314090604050c12010e01090f11100210151d0a0501140f0d0c0308030711071d2a0a030204031505090709180606170105060105090117 66
    0x1840403085281500c10118420540e155001e0b513000950000d6600400c0c00f100e002401040483d0b004105100c081070020840011101c801c5802580100f100c4443c2ea016264100110031a54a44000c0b9814015400340c3d54401c184a0b43d40410061096810000c0c0240b0900031500140d000c0503000f50f0f01d401c03542c4140c404400b46407098840d40d0751010540000e0f22000640c9182c40f5034423041c01410760307250203082d015040920486e40407003400c101007011880c814100c580705000c81e802c1d2200303000c00c1d85403010203140c1140e0140d5981c50324080241110005c09058840c40c4a141400201584240c1114441c0780029110410075102c050502c0526103040302408180d040c62038400141100100080405e50000c2c0c6000d0707201d600d18101054040c003540100801c06040c041040b003980c5020484400342d4004840006141c2070000c08501c2d54030b11031000503c41352410401080f0004500b40c00e10455001130000e10807951410300440d06402450721490100d0b00e43d400c03640e600324000009690 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 582354244 1250 582352994 582352997
    0x24030606070204061203021507020d0804150513110904232803080604111c0615030905010e010603150b0102031908040201080f0105010c06050621010203090706032a 72
    0xc0001c2600010200c41640d40400aa0700100195404258044c8481e004181171142c0e401198509160301948230f81501200c2d0f800c00518200060400000400d03040402a20301c100b08000c0c030f0800d440703c0c807909403020152041080c1140219207850102c3c10540304a07401380540303109101101400840b25040c1c8800c4281c0e016504d5080d4030f04540203000c030300f450340301c40500355941c2d41410041e02d05080a000e0303501981c20301c503202da0062201c5046410f0320809040c000090021000e500d80140400e400041c01c003c280341703445409583c903030000703a80c6e14000d00080281502aa4420303088803c60b200007008944002c2c1901d10245195020000310403040c01668502012035240112800c0141c00303401c0420302c000140703c00c0d564041076140c1d2140703003c4007081303440d41418006000824143e4006284a8607034001641588402da003011006440c21444500c0c1146404002e021b0340040354180d940d8414501c0001e01c1d10701c00d004010040920a1800000d95402c80c400c50071101b11200e11f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 582355494 1250 582354244 582354247
    0xf02150106140f0d11030a110405030a03050903070806100603050f060a063006090e0f151005061b0d0203040b0f030406020f03092b0813030e0d0501051524030606 71
    0xd0021000e00a0380902c0001c4004175513039150020b2804120341030030800c209490018482800b250312300042c100320f0550103080c82134592501ba40046c5c40c04201d9040880c4600070308046c04800746030702200905841968070280320315503528174130f6500d80390704580307850b1f0203d02050100010f80c02410303004020000c1600e50500c0281c03001410070b0f140030702c0c90310705241960381b50304002c520b484d485042d200110b601d001e808131724030241c03149a5828246a000005625480200b4913102201e9900300040c80040c01490315a004450501407881e0701988122090041c00084011640302004903001d40b070080d004c044c10002c01d80c0000b48190130051003141c1c146e50822003548400721110103144207401001c0244000130640707418000c40100200d80300240340e00d81141400e0150000b503040d0b40100d0a00c4e814a01c49014241114144005514103070001142c06140050000c19040300c0e201c0c15001003e150243c000c1e40601031355803001c0200001c1109421160000301d5182c200868110710020000c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 582356744 1250 582355494 582355507
    0x31e100b130503010b0103020408030a080a06030609230c0109120602090a0b0d0c051303060b010c020915010206130c0b0a02210705061b0313061107030f02150106140f 73
    0x30994071440c001d003407106003800d00b08114070f400d0080070010002031030154105490520031580d13a0140c887c8140500504c58000f40103d045540714200464205800380100ca000341488a03210340101c0358000c4031802c00000d0741881030009540319500c001a03480c0c4007454601141c1c40801070b61804100d03022a002c01c00002d05030b0b503d140740c1000d012008207095548050a03500c0003150001c030309030740501906100d800c0c0c09045c0043d5001c10ac80d001480440d87c00380e4500103c6940d803202400950002e461404d00ca400800c800c00d003190b00c0d4080e000c4075015120030b800f045207841c901100a101444c1540240450342d0a04003074600c030351450040790250501c04110760740505001041c804400303404503104d42840710030002c0980104045c0c3c505000311038812082c3c1a240b000414040c6a0002090480100031580c3e000004c0300300c2d1148100c0e2203540c0d82c500101140c40203c0c1c0c80c40140b00301100030070390750343c5142d01604840301c0303481d07907100c181500d800c3c032030a40c000107100c410210741800721 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 582357994 1250 582356744 582356759
    0x1529041401060f09140105070201031e050403120e010216032304090f050112020a030308090a0204060801020318120d05070e060a0807090602070303091a1903050405060a02031e10 78
    0x51030207040e40e503c07403003019200300d100107015100d40d6005180b01d040e000c9424034240d030403508440c45c1707540a10303000c100400300d010901c040c2519220f0b03a0082a143c5410001410b0b071180c1d540b0500c0401c01d00501c0b900040c211442c0c00e078000c40c40080e44060f0b20f10b00b2040024081c08002062540110400140000540c0c007404650081e5104d0103c0c562280320300041c034401c91045501500440e1100410303030940350045001c0d95a6400014180310601300400e14541e020080030f2625503004005114141d100e0540901070b40082d101c00ca504200d40b030000d9400d41002c255804114400ba0026003407501903641d9402900c40070f0300500500c003c203240410140c5844006042c01c800d15101d000c020b0510a00082c90780245034456130454000741003c1c030010380e00c10f150104540300d210011250030b03602c00c1002120700c94424202110314164240350b640d1500342c1c0103188903074042c80503203400356103c0058034140d10041f500711000f43c11141040d4040d0341c00c80f4400740c00c011301e04850082c07503854818 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 582359244 1250 582357994 582358031
    0x20f06120601030f050106021f060b0f0706060603090206071106070f0b0f15010f0e03010b0a12110609060405011101090b2a040b090d06020c010c0309152904 69
    0x9030300520300c003250100085541c2501442c15890196401044150b00d8210001e4030340c40005800e81048002c0c000b08400c00c50240c0040024211100b100b0b80d40701592008498940e005071004c0321403504003440061950b0092090f6895680c0280c0b0316850041c4c59503d1400a41184111650200c000c0c06a0008200a031403412507240c414a140c64840c28551048410208018040c20313031400300020983c0d059034403d00c0201c025503a4200005540803000020b4050421201d8064100f035151000103072074400ca00101c1c3c102c0d4010041d80c1c04441c0a50f0a01c01144a1039500c0ba400920030001000a075205016450007081942d0000800205695441c00305100658181c070400004030400d040707041d1203030100601801e0412500d80b0f090f2914000b1115030040c1c0c1c01e410310551210f0242d506215050f0100c400001061000700000912a200a001002d82c03000507030300c3d2000302c20314407072000452082c0035400c0640030030b42480717104403a10b68400103c0944c299030403a46414014017264945003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582360494 1250 582359244 582359257
    0x1903120c021c0c0c060908010b24130b0c1606090f17190615120b0105040b13020a0504450e071d0702030310120201090803030f071805011b020f06 64
    0x140d646d0303401454071908909403921681030034070480d17046130b11582101c2e0008820004903c400101d07a1589119550440910910f501984002c000010300c80088031011640c03031501d0700311a4108501d00c0e11090100c0380c2d55a280100f4401c0399401100740080c041001d50480118000022115101040009030101d2040008200e8500ea150000d03503824081c100090009481d0898001c0b004034020f44641c0c0120006128080c050382d62003c4ca03026544440d401401c18030302c0c4441c2903645004590707009155900c01e2054200786011405a4240c0c049a002c0709174226048404020307580c4942c44101000c52550155204c00980daa62170641c401c07030510a01006101594041c80031402800203116000401410310045400c20401c01c002c0a4000c3c01e071780140c90b2514510300840e200c03440161540256908041c030b0901c0044208604144121130251040310b5540d10001c54400a84c1c10030100f002a0080d1408100181c458400e0200c8032100d01207980c0c00100609541c1c000341000c80d01d40e50000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582361744 1250 582360494 582360497
    0x90c0d1713030308011428050306070c060c111b040e10090b07080105061602030c0a080109031404061b08070606060815090c0d0b0307081903120c021c0c0c06 69
    0xc40100280b42e00184c440e030041031005090040116840d0000340b1100c0740341e03100c100d890008201a002c681c501c041002c040c040c00b408442c3c0754184080301410199040004580c1710741403c0e1280004d81c425207207030b42103421640007810741401003c160403000c00d00c3c0d00d1483c0c01c96034903480441d681c9010002c900984c10222000250104d56080c410541e0800514100034017000340700422240d2030300c108a980f0400190420b485121440c8000b07414048402c0c02580e1010050704042016a4194400e2190900c240c44080410a101050440030f000e640304000c04620510355107942007204108050078544140c200d02d140003599074640c2e0469a880d00a4000034441030200510104000180c110f0341804440b002c601303103400d6101307032194400d0000c09200d003902c80c0e11800054030f0403c4030340c003c0c01061003964100f00503c141e013440f00b155064240e000901d1840c0300251710b4120302c0b4210401013070394090b028000b00d4002c101da03003c820000e600304000e000424000130444c400d00f8040034180c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582362994 1250 582361744 582361777
    0x60415080105090405150c0403020402030c0c0d1701060c0f0c031a0108030c1209122b05190c08040312230901021e0307170d050f090c0d17 61
    0x208600604000c0140c024900458040e418400460320029000f508034004104a1146598030040c03000c5c140581e5000075040f900110a011158580e40c000d4007070300080a049890403598004d0440300c004482041c02000712113840140005845039082e00e58180c014a03218018060b41d5a4004a0240f140d10940325440240010b11113001180d029600501c000340065040540e10180184c8820702c0c1c10100c0d036020400200400389450321011000707062100d100b0b49001d08003d06600c110482d007604600000107148441600c1c1078000c00039500c03202c402c02c00c401d001d04402c11003500c000ba40d40c00d05440300e040c00d0100000283e0007182c40c4030444000c0c1d50302c3d031900c00c40710b403118548802500e031000034440900c10000d103030f41e00281c001c29a07020b449142c822280080c0c01c85080d80304044c40500000712420f9210800e03e44100184202d00c1c000c5001c00c01c0341d07580d5017000d1348440141c0320014542c000348009265454007e6006203400c1c0600204c0d4240e182c801440040d41d8810030040b440b0102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582364244 1250 582362994 582363029
    0x103060608030f3414010522060e03070f030c02090c0c1506130606051201120b010303050703020c090711060106051306110304081e0f010c0c030e0f0604 67
    0x4180614401400e1140080d8140f146070315141c21140101d450400080c1d2203c8003049588249148904000a4800b9012503100c09400c000000350103080300e4100a40c200780101d80c040550356044401100b65a000d1525408180d580c58060144414610720741d102c24001031001c14012855281c01d5482502e50900703400f0b440c03040c824028001400303006c448805105584503c1300c00b240c001c504810001ca8017295a5400c4005482034428940c5c000e04107140a00224456800c4030007084910300c02406032500d42c2e40c0d01182510781442d07520080c0282011401040040c0c0980c000d041280e02c2801501c0103101e68002151040c402124030350001109074103d0707a0300410912070307035001d0101882d002d8034062503c4d58603207400055216040411403090b2070b45010640610980e800b4054900956010310b11b240e031000800501401c0118680c021081d2320081000e051040701c0290a00b5240c031f00a100c4283c03015200e0120060103d80c01121035041a2250f80d100402400030f4100311003000034844 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582365494 1250 582364244 582364253
    0x303020c040513030c0201180b090406091820060307031d0109050705010c05010f060b03060a0803030105031506130504050f160f0522090521070b0a0e010209180103 72
    0x1061000980682d203800140095003c2c089401e80d1a40d416041c504650101d91004851b2203142c0c0000e0200c240f0030380000309507098910001c0030900422181807198030344690741c2c2002c4418480030303250648501c41c00580021b01004030195401300241c0048503101e106030108041e54011146e40b00041d40c1c0c4d260541c90a1001006820840751030340080090070060b903a10b41d51140140074960601446902603003c1103825040801c8140c4605e0007070159070380d10002c00181d03070010b4a42034895940345801065020002060324101c820050003009150703884002040d1003200581060f4011004134400341c250302c804d01445014038881d000030542c40c81c0c071070206402d161903522280c100c00c1c000d000810103072207100d100d80c059400480e01075840c8041845000114203d0000e45001142424540f82c28058003140e40c038418031036040001031544410003041124803030090020401c0c000c800108614082651020f41003c090400045c075000b01c00c00000c01001c0942c0a840210100e03800610400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582366744 1250 582365494 582365503
    0xd0203190305060a210602070b070908030703080604091509111504030804051306080f06010e071e11070810021c020306100323010603020a080603070f090f1113030302 73
    0x200e00310301e0208402d050483c00220b400b00716220b151070340c4400c00c159120700481d604100b100d496100704c04540c2c0d90b110b8500440303008000c0700c02c0008a402c0c04400920710384044103c0b180f8560554542d40347e603039500104002005411401d455030402c90103c11400ca90381d2185002d29401030310129843c2c0d08940c00c0003200041c803c503020141a060104000040706601500c0544108030703501d0454010028003034004004c0d50f0b00075a01ea02c0741c0110213a8000011460034180c035014a4070140950360150141c401259000320f10009291032000402c2e651b00c10301a2603144401031042d5401a070b503909184d860400036200c5005010b6000613400c8120148000071000560005415829450084000740c40c845030b81244900b8140c0f00c0c1003502070491248000025031100d440c8403907895031a440f00030000e4024138071090204503c0c2001c40e989281c00142ca0044a10007090f580510303003441d184d140900040e000c5140a540c80716110302c0d080c1101d502810541080c0c00320006040d15504000380350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582367994 1250 582366744 582366787
    0x10c2d1505060a0f12021219060506031911030f120a030e07060c0f0812040b090c0a0315020a2d1205040804091109040c0201020903012a081003050d0203 67
    0x20040400c041000003001300b8104200c0310a5142c01e078a811040c00410b8189101312410b90340d41c0140b00c061a407a40880c00d034040424083c0070308000f156500e0741031503950070510f81b802045a01c1c0184c01030028640072145442d424015040c2d91903501001c03a09440c28160240c400269800802c40d00404c5605110300e00900071040000c000c243d03c1c1000280c50b80c00d000c0c002134940745a08030502d0034000e03040101d480e2040740211001c000c0c0f0702810441603001d411b5440a034140205030481c180c80c640340317140c10b05403030f007001c2d288a0803080862428000c0d4051201281444440208403c00c07090701420060220000e03006c10440c14102040241001450b140c0710117000d10b418144804622460152800e40d40a41400a81d0380a08444003403140214400b03280d100d0700f01054070b2011507040d0060160702c0c43c282d00900c244501080790094010700c0f00c01c3c11429944400000d18644d00c02c400b080e401c90421019446182e440740c452a007084521806900980d0001032458410101c0540b003484 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582369244 1250 582367994 582367999
    0xf050c040f05012909040b0d0f050105010603050c070b0601212c03041203031508031602030c040207030e0d02010309080a030c0f110a030c03030209180105030705030c010c2d150506 79
    0x41c1c01542c0c01c604d04040c00b0341c00c01180100e030380b40b2901185403503400100c61400c1c1c0210703243c0000041d515005000e04024003d550001c1d00b03103004554138030502c0d419a50b5465001710812107030fa884030b00440390080e00006034034a40da201030559440075000e02c40d440b000b070b17040c0102d49280101c40703880c0708481141400100702580104401c00100304914108040c2070b0b0b05180c085614140b810324441700d443c494012910500001804540e03504040d02c80c48105403080d81503420b50b50200c0c040008a0003101d60240104910a0000442c0d1800d98850b500c1144141000030b07680219885600b400d41082c038000001c03955541c040306203140c00079864680400b1510b45034011012075124a5140d545a16006040c015085900c9040500a0701a44c640c80d81c05005051540c880c07407200200800e0a10555004c2d004404d0003280c14240400c0c8950603844c1a160b50403c0e83c41d81c0e68250508507244c85809413083d41c00446004a903d103659030942c103005aa955107103030842d813004021603001030100da1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582370494 1250 582369244 582369299
    0x130e070c03090e1306050901020309250b07050a080301030807032a02130b1905040b040c080f0c07050a150e0d02101107080705010212070c0c030f050c040f0501 70
    0x35800040b10040e10b80c09915144903440c0d0b400340c8a050164803a00a202c20700340000c00902d410b055002d1413142800c6012103090600c00750341d121201e0240700032940007100340001805002e61000091982c02d104204035099954103848500198000380c0049900f05000510442455481040003000702012055070591a044080982420700340000080c040c41035a01c0c0064111540d0740615044900508000c0b60036101c083d04000258046c062284a07501e800c801c2202401e00340301c0c170050b146054842002ca078490525101e16500002c0240102d02c84c01c0003a1400180140070018415104100e40700b440c111620304130003601d1f05801007190175481251500011170740000c200010742c240c414009403200601c40400194030038008043c081c4100010200100281503009240001d0440c1500200b0740b50300404461940c0b450b8006801d50301441c05c00e0000c610400b020391030084c465022110388442240224043d80c0f040a2030048150b520001001960f0081c089011866a040c210b02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582371744 1250 582370494 582370517
    0x70c14070806010306050703020903010603030e120316031809150e0703051902210c0318070605040911090d05060105031209090406150b0c01020309070f03050a0f17130e07 75
    0x2182d40e01d90520024240d26105d0010910a030b00a074100e40e01c4101c081c0c004c0c440301e038882c103010740060103015071140183c0000e000750301032985c04810340e08142c0c0d00700203440c09441640c6084a060400104400c201e0b008810000b480403c181714a60340c080c00013507900845c07845c0014001160f40001c1405044c581040108814244071003400c03182d4034a400c00068582218038507514178410303180c00405481c00b00c1410b1100c8030540a021f18410026610070b041002058910039445424510903000890030605c801c0c09980041c0e0021801100d40a540d9800c01c89110001036895080a0050350283c000d030005001c241801d020603010150341060440c908041e0380e020800013440240301a05417550780a445212005481c2c001e0000c0c441d41005607210707200001014000d5205031350b4440b03240f044610014119031b402001d00100e982200103803070102d5072916500d440b20040b020807908180c00c500744c840384584040103090700301200082e00c000b26040c8a558a41d50700050300344001d01c400d40601c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582372994 1250 582371744 582371759
    0xf08250803030718050a0909050706030b0102100f1e0b01030e0705150f09030109032705010804081308071205100203090a03050c010b040f051504060b0901140408010203070c1407 78
    0x7101d420500c0384c44d2003803610624001d440b4802e080c070f4102550180a071003000482c1012500310710005802007059483c180d07943c0303a0541c21212042103403800b680100307403c1c046075a025400071400c10140070002ca038844c82c00110104039110000e007240ca40d40c1d20440b071a07695a261040d940281002c60041200d10b0034200001c4941c1c11400d204000680e00181c030049481105095400c0070002900902c10803041d032401400214000107100f207020030004802040e44007d038650740c01c586061316405141e49540d140c0348800d60195803031001c0c060000000040202d010024440180b54440c1d0b8590000d03102e1800a0422003a440d585007041d0040c4144881c40c0300104105009691508120799115000c1030a1409000401c2020b070380a4075000d050045a1650741120b8411644468102080f0750340f1317800c000840d6494010314105240c14009812194010021a00f11078400c03043c1505280d80c42038910309a0344100d510000042c40f0030201001c00031000c401411b903900351000b5060050410b10b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582374100 1106 582372994 582372997
    0x20406030b0907050708160614010605040f091a010e19080a060c0305151e0604090b190b0d0f02090306100611010b010e06130f08250803 60
    0x183e01c0c500c035208a1740312541c410001e5040a489407401d00e00414805000c9401a45d6a5414545828000c0155000345450342c1c2e075039030f5a802d10400c001203144640c01802218185902825001c03450b43c1d0368440440300780f820743e00009800c00061200f0703c0b0300c029882c942d144401d000c41c2c0c2d2600441d102140901070401031064201d4168210104c490841e0900b6000b45c200420140300e1030600c0e10100540c4803000085140042c2d54001041e03035000341c0c040b920080da00c00c0080100d062145003282c902da1844400d1510f0303450305070304044901c1460b0300c0a807400d50b0b481808400382c04070750548085000144c00c9071070605c1d0100d40b50040c04007600410012814544408589820500512416080682d20803840c1c000c41c5d024001c02d07030040034031001245031195011551599002c540001001264000e104c0f51420b103500c107414075092810040d0115158005101c40780b000030 = true := by decide +kernel

theorem cover : BRFrame.Cov 582194244 582374100 := by
  have h0 := BRFrame.cov_init 582194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582194244 ≤ n) (h2 : n < 582374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
