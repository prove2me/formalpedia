-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0973
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:35:24.417184+00:00
-- url     : https://prove2.me/submissions/6194c912-ddc2-4e64-b9dc-f45d5078b2f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 174820143 ≤ n < 175000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 174821393 1250 174820143 174820157
    0x604030206030a02092b0b061005030f0705070c0906170c0a0911070c1d0a050907090c110604030e030c030c0f040e1507030603061a010c12090b07060b030706 69
    0x40d00811442d0000030507103003040d80d0004524003180d55a86401d801c030403500c40c01020341c83d9a8001e54070354207141c00d0b00f21210503440000c9a520f103132280101017024a0759640c2d609542c0d0318400114007040280c0f440060001c10000080403403110201c101c060002c2c2500420040e00d4000c9286801050b13400300c401580200c62604019540c02d801d520880c0c80303600d400b180162042c615030180c0d1041480003054280241400142c4c01e030850412500c1441d60394107140d90b81d40741d0301114142d90040740c00f891603030001e103001e0010100c03d510400c40503155144c294155040e11201500d00300302550150302258040000c040a0f01d0100800c29000b00150b014202d40030300c2c2c0001c0380c041d400300c407825441142c64011250113240104030500990742c0485555050782401100903001344210302059901c0341c20f240711135030381070100071081d40d4103441030352510095111901c50707d0480009000080c00c10414840c0007a108018101804043c1d0251f440068107425035805c1515000f0142d020074144001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 174822643 1250 174821393 174821399
    0x20301052b08030709050a030b041b03030e0d150c030509070609081e0c180f0a0b011b14010e0102040e07020d1d130f0219140d0b130e030309010b0604 66
    0x6030728941c40100e500101ca10b850303494001041d64010345980203030343c00070700c503000000511041351403140c0a28050380400c0c903c0051040d1190360111140009004034000741150041810f0001d2a60810f0740180b08900c1c28851a51000f01640c0c10311740d501c0c00003a140d005000c980b41c014491000244101e08001109600d03005540e038958442041c04d503814100d14001c180a450306103d502c0d60080001d02c400200280a8154081801e00b07480c44c0740e28101400010309100783d5071042c1108004142c54269550303888400140700356407030f1401140c0e10000a9a6401c0f0014240500e0fa10458280000740e100c1d0b0405400e000d8010004001d0b90842d0b000d003d04c40c00242d0080820721120b00303810311001d6400f5828000c00c0c07a81c0551480035004d41d1a00a290b040178540d50b0103000d0041c088440c407001c482005400b180c000300e4102c1450030784030b4108031040003441d1540c08002214405440d120b44490328000d50b901321580b03602c410040e908000108280341900f07100ea000f80c00800c81d445070409003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 174823893 1250 174822643 174822709
    0x414070816230a030803070e09011a070218010f03031215030201051e0406052505100c0311040603150e0405120d0b150d11030603030711130204060302030105 69
    0x4082d100740c1001541000c0d0714404501160030901c0d4071907001c0e2000041c603540c0d150100300c0798421a60440056042c4c0c072800e0551500e40e941d54102c072014605403d040404100d21840303a404450100d900100d00c1d652059141e2682107032500038405422000442491802c0c05070a00304441007036805c09183c0a200312540002d00034a006882d02803030602e45844103400c400d507440b180c4803100810a03201090004906600100810080d40400c0f40b03400c07500d00421050b00f04401000c00140ba5400131445003084110310740c031408074210b840c540400d80818240381d4801d10390181c0c014100007900c0d240c2c20114908018060001404010040344035890240c58007174590021a0503001040d10020700170345042c0550300140c903282d00042c50b40ca118480503e148000b1344c0031801300000c080c14401007420344840034040d41d200e030901070061840c003009603071501920300092449980c8039440c0da4100740d10450b00d00c050400750640b81c0340180e89504101c10441a6160182c0d04504400b1180202030811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 174825143 1250 174823893 174823933
    0x40612060503150c0d02190e040b030d050d06030206030109020c012d110912010f2706020705071e0501030b0d0503071b0b0a020c040c11150601051204140708 69
    0x5040b6403102050381e204da0b440060070b8852485035075442d40c004500c5600c0c040c4c80c490b0000c1003034056111100405249004c0c04107842030800100c0d07140d008402013066682c019401410304103c03440b00054501e03125400100660001c0e002064801d60220344024052402d20443c1c441245200314907404400e0f0504498012010103078910070f8a445403407040c0005404030586100c181d000f4034407041051f45451140c021300d03021142220040c00d120000344d603192582d800caa000c07002c2501001d03a2003c1c0361103407006903010314400c032070390700c540200091407281d426040c1569410340040600700030702d4580018203035402c841c03000d4891402d80321401d001440000c1100c20440c0d008513402d452090000b200711841c000c9910800381c000c80091441c2e10103034086480315080f5800c48007000414801d03201107419680c05012402283c0c804613184501e00c1010700c070340b07a2007541403500602d0888414074118030907000b03580448050032104070410303140c6400c0c0910400340040d8002005004020941000360b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 174826393 1250 174825143 174825163
    0xf02041208301303120c0e03070603020c030702010509030a0c0303110c01021504290a0c090e0108070b070503130b0315030c011d0a1a0909010b0a020309011b0c0b040612060503 77
    0x407100c10310b400000c00d4000c140c1740c40034514000b01040702c5031514002414004100092038464040c0e40c001181c1e4034064420b442900e03018000541c2020310f541d0041d03509900c21100c0380c0d414440d40603400c001a0504400f1005540b080d0369030314584503e42000b0f0b1030070480c000f005044d500950b010040100752119607660040d00140c41130a00d00c503900814100405011f14a01160b07958010400401c1d040d821203e036000040d511680c0c9196242249071035031500307001e490143d070080042002070258500191070000e001c1c03010f50f840c1000005030f84050000c00c0d40310000d24040442000032005040c0c20141c0100d00030f4015000050408000a01012203039080d4842244160b402c0e6455440380404d10000c2c008102610036a51044141030003a504461035151184c20898004501c061001d0140c03822051203400560900341014010b48090035294500070255041141c1035010508419030100200a0012032507640c50400703000034000e80e00712048102007418041c0c00c21080e02c000440c180b074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 174827643 1250 174826393 174826411
    0xc03030902210c01120915020319020705010603020a1508042003060a06050909070b040603020d0b10030c020106170a062a09061206030b0601030f0204120830 69
    0x110201880060b000301c41d60241c804080800e460510128280020a41040d00090701d441c202160790b00907010649444000c010001c0f110085c1784245a462500a550440ca048409a2108051619040c101e80056000340c40b50303074603003208006504101c2c09480203828158001c035910800c40310080d01181001e040140f010700d844e8a00360604003100303204000002c0080c03c0d1440e0b41001030030300028200501605100303089500100f49500b1f4002144070458403003401090034645003200c00d50080d0080c44098241c03e494064200c40d40e40c0d0a03908030395440f600d8a0000790241d0a4800908643c00c1e03030010348c2c0d606640a0040041a400070356540500d900c400040b40d00b030406c003511249001055103c805800451b041022071035000012001034815550303512142e20140080d600a0ba04248400b4003c41311840211f01a54800e0b0007504640030803803005440c1c07640e901c40d05510345e104500e00351255040403c1600580b202c031903040000105441d421602200c506125450655000d030001c03039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 174828893 1250 174827643 174827651
    0x2010f020102042c0a05040b0a09020d0b0a0203040b01080303060a09020c0c0a1203020105060108070f031a060a030608010f1104180906020403110f0d030219051011091f0c0303 77
    0x15546100750100c401030070300000d036000071618100074004c07000a0350701a9019052a0000900c11100e10301c10507120f41d4102c0f49600094480d038810100512104009903000741c0b00c0b5841401046540061500030340d101000160f40c3d00d0301c1c0c100000a84810f0300300d542c8980040007440410746e6210100b00a039000c6020040c0d80d00000e4038024907004464454982095010b40005000354045080d4580c56001b0340083c0b0181d501c1c2001100c846c4400c48001c40450b0100101d241e000d88654498154480035040c1e0710a603002080000704a9001012075000180e116001400995800e02078203a501404500a002d501820951412140500d014080c0c24458000a9501d8454a50460f20030150082403c40d0360715100c1c241401d20f5a801c0f60700c1741c043e00c02c42070a810f850038030000d501341c5d02c1d0b0958050200381d000030022142000c20314074190383c24801c02c4005540458284511800200300417081ca03600c00d01c1100340070302842002200016070307140100390007103140c0003030801d83c0e8a0b40c1450006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 174830143 1250 174828893 174828917
    0x5011d090a03050d0c0302090307270504021c0303020d140a06080304150e010207090e060601030b0f03060604021c050a0504121d012015100b04030503160c051e130b010206040201 78
    0x400074080c0c8c1030304da039051154410000b90301d031607412160010341c80003ea610510340030b08003060649500752002074016150710b01c07134940c0d800308111400519100e403801514010343d03903001e4003c2c1c0c4c60006017050aa00c40300c091018042c03862094400800e40000650305103071a161a91041c1000002c1820a1112106c0d422015038800e0050748041c01e9440383c108101c16801210b03036665041251810f02007440d000c0740006618080109118118008006220540d036141c01c3c00007a4008000f8034040358003240c4031780c0144e01a405528032410f0310030400945490305041c0307ca00c41d490030281505201d1400910180c8258083d1003210960f0282030501d0303004100d1001d8072008a2400c49010310f0b0107800c62020a0286100310640512090910229402c1d00c5078150f04a80c0700310301c4010205c0e8010400041c0301c9100d040380040d0140145492200d50f40e031480891a064086a802208414008074401642c0303003400036240c6141c80b0700020081c6054000001c0d680d554040c1001c3d060080c04400341c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 174831393 1250 174830143 174830147
    0xd060b030f0303040317071b110102010f02070f020f041b0f0c02060703110c060c0a030804020604030512030a0c0206070f0804170a050a1e021e070905011d090a03050d0c 74
    0x641c00211445044950300c0c0780c1410014603903c4154080366590018030003090b00745210710301d03140ca20301c42c0c11200d031000003855031203c0d0796070f4602c070619040d035480d80011480803c80784090000c40340a040d28065044c9a88104441c1c04450000e0f284a030346400084140145400344140908103e410035060010005000751540024003600a40c4000300003010410194031000e101c80300070b082c0f812030310000f1140080050038050400345c0401588503006000100344202450340e0024006003803640b400391640c407454208015410803903803030b01002090140000c8070f07104503110041e051026044a080c070081c001e2820040220403c100300340c480200b0300780f00484204c000241601c40c50141e03140e104900151090b04070b8220500444e175000c3c201e03803517481c0c1d61011411547c499800744c020544a0007407000d90249046106c1c3d903902c5264004603c0300c15501c1514040c00000c80b501c5801d660300008084101740041c80c80401e5000401c01c0000a034110301640c3c403403000b2800209815060341c0f02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 174832643 1250 174831393 174831403
    0x140a09022a0c221802090c0f0904020a090e010605093105090618030705100c050705030301080703060501090209090f0903070c030b0f0132040e0105070e0f0f0d060b03 73
    0xb80d030341d115560442c85904180c1103c0244180c0c0420f143c1404188001c1144008031420540d0103500320b030386400041c5c0e1007ca03c0d07008107040301103441c0c4582000c040001140490700004100c00c04965443c1041c02842c1e445501207005007064503000c0e1070224204041040d94000312600341700f10030451380c00c401c803032006030300040c111003000c80420151400c05d6036240c0c2c03420f0503540500018856813040c1c220700c4012040307512080d00b0000a25041c3c4050050000501e031110104041003402d000140001e501800118000d240f600000c18030700d42541805400c40d84c0c10390081110a00c100701e40401c0780c0b1507400c16644100907620030f801702e6a60502c0c01c2c0c118400d6910040c80400213a13004030800510800650103403d02c1903140c02c5a07070302c1d1100498a01c800c125403040900588603400348121280e000182040d5000d0000700354402620022030135079906850703a60108401e20f6090710355044c8540d100700f03500c10071680014503450104c045003040c00c1c42c0001515107903d800486105d6101000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 174833893 1250 174832643 174832663
    0xb030a09060f05010e011a0313021503010806090c1c030c061d030c01050c040e1302191205010b040519090204020f0408060a14060117100906140a09022a 67
    0x2010b000e15071400000ba401018240280da0382c00c440b680001c500b12034084600b64100070340309502d41c13564a940c20480c070700c140340d400e0884e8081c5252054609484d0000b0180d4001d0440e4001081c80f80ae00c044158207243e81e80205500520249011484048400080703902154240c104113010410318104440500103880c181c0c46c0c803c55400d0242442c8900000401003e91076000030000c82c0c0f41c188441c80c1e144100c0c841d80c500c80b800c10010610440c0e42c0d07040c44000510040003014007500c0c00360340c5090304106a01c1059819032123901201401020300802d01108400c88040044d0b180210300c1d00c01b140e54107841d9030243d5a98885900454441ea811605003203c0800c1c15510769644600b40e0750340f08011110311030001c0c1001c80e0301054405401d01e0341d00485058680400000000d10350109040005103447c00a00e40354100052a0100784103a101034103101c465503989040714070500c1141303d116803003440100e104010506800c94000e003551030b42440811030a920070051003980385004404c1b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 174835143 1250 174833893 174833903
    0x5010206070c032321010b0301151d130b090f01180c0c08030903090a0e040f0602030405010b10020607021e030702010c081e04030b0603010b1315170a030e030d0203040b030a09 77
    0x31000b040105c0a1380d54242c00c006008104216a01c132580000c4901003071091034206540d004107445082d0294907403424080200c038280d404404d44400059011580040756810141e550502c2c16081c100441c0d1641c0c886c4407806000c0042d450500c040c00c0c8041d517440310050541d0390b40c1d81c200c1a107108900340302526810455081e22810002e80c11510781c2d002c1d081480c8207000d2000300240b41c4840302c404a108a40045464850910985540002c1c4d440204201c1e406d560302c07000c0c00b25035954408201e111000a47c010442c0d403030244d2021789000b40c1e6009081c1501704041924040c000004203c8841a5080c40c00c00031920862806ca03601d0b004413100e2404c1c555100380d141400c1500c5402810032a40109110540c54440030b007032600300d680c00bd10580d00035520b98204680d00650f500100b1a080840005c0c09407141c3c2c0d100807800140700784403420165041881c05406156004445544a40c01200a040860540c1c03102964078410f92250201e00c3c9808000124405141d40c45900060303000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 174836393 1250 174835143 174835147
    0x60106031a030a0803221208060a180605010f0216050616051203091902030d0c210c1a01050d030810090903020102071202070501051206040902030d0f020705010206070c0323 76
    0x1d00e086003075508216000404070046400529000c6e00400c2d49504181c0c01c81000850005159001c45411b42c00174011900018003030000070310001000007841c118003400000140260600c00014074001001030300f641158807558000300081e484a860304210303002140c20a03950f2541d0b030b403c144040c01e52030014000e17000e5107210801701c0c4403042c0103506c51344840b000d40ba40c00c20119829807042c15000c80203034055100711310b490859030040402080090040c03120900032281c040e00d44038003400501d668400100c21280010801a04070803000e500c1206190545103503041c00b02040d4903a4004002604004000c0041401c54020b10054405070140c80f20600c00c1e48060304000c0c0c00313948100f6040310115181c0146035803092021604d2003d450059440758075215840b40c82010300900a8415588140e5511160380141e508120480201c003c9440c0c0034407400003110b0281c101400799120f10b055400c03a00030004182ea11203940b40b0000e9050a01c102c443c000d024441041410400100a4100300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 174837643 1250 174836393 174836413
    0x7050909150708040c050102070e010902090a0806070c0b06090c07020d0821090d08060616030e030a23030301030f0b0405150a151205070b1608070f060b090405060106031a03 76
    0x20050f4070520880c0242681e0b8140c40d03413140120303a00e8509210f0481100308520040c49094056001007440316401454941c4054450103818103203841600c4190200b4081e600003000c1107480c2d035042e0340c8400100d51000301840c1c0880004118841c000d0300078854010012803900b0072002c0400d580051031078980c000110044130000746840c02041c2d0304034032039104042140601030710135080184105805070606050180842c400c0d4060510424110700f4006a40c0d200c02654070100407408180b4002c5800681981480405c00342c58818101000425007040006001240781020400501035124404007080d640350f003802c5040820b00c014030391020492806000c0021410f0304440841710f0200b4080554035501c0303441d988000016075008200c0d81001e201003044030700300c0c13010b0a00415909159200e00c251507440d041544d0103c00700315503c9130a49144002d2100b2071080032001c0100380c5054000d030034181ca0b900d990344014441c5500b099128a40b802c1d10410042104003e017030060201c07500f01309 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 174838893 1250 174837643 174837647
    0x1211030307170a0216020f04061d0a0b090106140304021c0f03090609060206060d0620070501060b0403020f0405070e061308010b03060103080a0815100c170903070509091507 76
    0x185039400000c1000075400703e6007038095442200e2148400040c0b4035510600d40d030a0103110182001a2607001d9a255000a41082003442900e04102a0482481a441c000720307003074101d903259503846000354083c400500115410503010080100341040c60390710307560b40d40b00040911403c040011800c0d09070172007a20030440314047c0e8070f40c0284282c0360110098ec0fa00b0044501035145e100d4400140e03c04c0020400e00c0c1401350519540c076008800101d44201c02d40a80910108002d40040d22a100010443c00340102072007898080c0c940b924071145801d1039a00051149100d07010301d648101e50750004114101e006843d254040140584016203070030100c103550280c140b49210f040030a50902c501802146030119025060700d82c0f10101500784528007000700d456050051800983d218080100419692124003090074103005507181d000c10a454544241c44000403050b254490800b405040d45659003c2096410354000341c81c070345015513900c0451464006c014080d9486801c0b400c051140c0c540d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 174840143 1250 174838893 174838907
    0x6040603021c03110c011b0c0806040b040501060b040e15010e031921080c0c0a020604091b03050702071e1a0a0f1403010e04240f06051801031211030307 67
    0x94002c1d1a807a06210b1983c2000d45c17103d82441d2494002184006240307246240e014030355124601075000e40000a84031002145001c0d0255401c2c2d4181e15030104000810509004417405001a881d40c2410103141c101303021505030300a4803d640c010200e05050301181d1150400038041040102220310003e400240d11034035203505802074400918005014071021b9052441d010300052550711000141c3c2d0b2035151441a4103c144641c01a00a1000b481e025075680409400900700d0b03040c002940c903080003ca040b0000c542a000002d250070101002800c54001c00e0403000c88000180610719071400140f50908200305400201000b80c200800c80115a8400050a402c44007919040e0100c003800d82c041c4ea9401c040c03081d9070341c3c5481c1000140031141080c0103182c3c00c01e11450903600201191040c0f81c10300708950304107481143d1f0f08d0024200e080e0203401050000c4c10242c4400d00d0586080c010700100220501003d09821011401c00b00c0603031051130034072a4494040c058946030304044000030495 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 174841393 1250 174840143 174840199
    0xa110d12080910110a0c05120a0f110a0308010512100608011a0a03170703050d050a0e120c0a060507020c0a08010507030f0b100c1106070302010506030d05030405150604060302 77
    0x14814900c00c899481124404c104400c011071482c98100355181c40c08483c01403068408440c140111020340034403041e403102070703c920801c54440c03c1c080c01001390000c0a02922522541460b88148001c801080c0c002c050704d81581c0081d40c42c1c00541d140c42054514008040701060042490001d0000ba80b62042d442040c106400c1c200040c0380700724080400c114209240401380164400c5c2d040c980c110596000100401d51107030410354105580540b1708001c441c401c981f41003200d0b842e40b051012800c01404030201400c0b141d070006040c82d88401d0850b030f54401015006081940d101d0209695074020000070001110040c804c1810a072128039880c0078000c00c2d24000d0201c0c0c1800c0301c00b8113010a90080e00c0b90450050f1041035a0620204119500298514162003070f441c641520180c035102e071001080202d0180d000810281401c20516140694150040f0104030050044c0000601c001c9200d80c50716461065114454441d82e001800804051b03200035401520019100047d01c0543c03200016 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 174842643 1250 174841393 174841411
    0x4052d0901060816090606030501080d05090d020a090905010b120309060309010b190801060605090609040c090f0906050111031303031d03011b230f0a0306030c08010501260a110d1208 80
    0x105590747c500c29416590b00313005803406900f0003080100900d01c540007828400000805002003140990040349080c0965000040c000d81ca42500b0703002d101090040003040e0720143c0d001c81c7c2f5041010400c0f0b8a0340603180202d841024008081148140e094000201020340284800c00c2d092808601000b161445c0c4200030441d4200203000a482c3d004000b510181030001d88291310f44203131102004014a410500201031080741c0c040413805000500018000d058141e100050f00d42c1040b00244c8060240d0005142c0c541c8100300c214252030b11201e020040380c0d818144072220000509010000b42516109503070550318000b502400e420100300c00a40000301a00c0c0c0010440c10000610001154821050848103082100c5100f40d028200142403101e04d62400190003520380d9560500c9590035400001160344850040c0000c0494920760451040d00044444110880c0c401ca40d0f1500100381001e0640d0940c090b90803119120780d4141c0000319070180004410240030640641503207c19100002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 174843893 1250 174842643 174842651
    0xc03140a12090302010806060a051c0b030c0a050616050307050d05090108010e040209042a0308040303030c051305010e1f0306140102010903021f11160204052d090106081609 76
    0x20042c050745800d000e580d01a5920056592003005000c66540011032000400204124088800d0840284072040c000c40302c2001c100a0f046208052030914111507241c0b08105030401040b0030384e030311000c84000007020132484682c007900c4d040003400e40c0a005000380140c0140c0329840e800d260300c44024182d08000341c841901d944d0b01d949030104508000c6900a4108058001140c00b0501c1842114000d842804002101d60006502074250308040e920854013640040317011720805805008042007001c85103041401c1c280f0b0341e0b101038110400752280c02d050041d411054055a21840c0380070b003002820081c540017940341860b004008082901c190328401c45102030025580d80306018181c55942c05500030310703503040311040d1900103014042c02541d0090303880c06000d180d0f145072000fa043d01e03400303901454840821170040c041642d4008050600c6602d54081080b002250004444203044184c41190020703500d0001c440d00400043d00803030040c0c840d07014020300c60015080c00740c0507100055402d00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 174845143 1250 174843893 174843923
    0x105040f050c0d0522050303010801110304121b0204050f070915050a030b0607051e0c0f01080c1804050c0d14091906020d060b25080a0c0c03140a 64
    0x4840080e1414180298104500040342800c2d07005150405c005004845c914420329019003101c0504040c12a00e94101100410002c5020320605428400d00242180395107040d0361510015090002d5807030603ca11000320109072440c6048011016074081c0c410002806c00700081c4941c107508550100019000003004640b04008207800704c0c503c1c1c040d8440c5d03030409010090580142001c85a004d4101d41c0030f05c21040428010051030050203444001d03405080c80c0c00c0c0149041c00700b090051401410700e85016607403640e200d401c0ea80d009480c03030115a2224002d00300e200e44000e40801e82544903041909101000030300100611940e000a4020418041c1c407101c0100c03141d4088a424140d0b4012186041d1081412080c0064040c0306074030043c40c0005c0c40064404980746500700185440c4003040005001e2002c2d85d0020f203040d180d0308501f60301e445591711492a03128003071100c0204050081ca540400c42d4201c12407001c0c55024040c4034522090b0700510f5510840301c0c100b5a03808151100c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 174846393 1250 174845143 174845171
    0x102010908181311130b0a0210050a0209120c0f04090506040b07020a050304060815091006031d010203010305032a060402100e0904030206060a0b16020f060c15010504 73
    0x920110390114400d07081c91103000380400b40c42d0000800c10303001140d8800158410140d81320741c0603840c0e81908419182d00070070205071000507040d00a902514010420051200c1e000100309040032078005d8080344956440360303c040030380a581401a00024600b203001080034020031690180401580d8052000c0e100804110035500380c0040a007090b001003004c607000c20764035030030b9550042003070044074400551681c0d02890356006034410000503500c4014418100003034811000e601c00d048409070501e052105d811401c00030b29114075802d040e621149100401d092220740c0312040c42d084001c644960f56410a5912607100c6e246030f4108120b80c4000c00084c025100702d2808608038980240003941d01c9a00740000034202540c40703000d01c00c20041e80d107080d82d1142d034072030b120398840c1c1d02600080c10050140101004181c015895988080c002001240c0719102e10b01c40c9a03404031081c102901c186404140d1511078400045010701070082000ca000c5060310b42c0d00e048038401d0744d007004071181d01040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 174847643 1250 174846393 174846401
    0x30c0e0d02060d060b040b090a1202030c210d031a030d0203030a0c0309080304050d0e03030a0c0206030c0f0c0a1b0e010512010f0612110904020607150b04020a120b010201 75
    0x120303405030003030280e54050b040540140c43c41c0b044003030000401075120300700f02120b60402d620000f41107800050600e0075060180303109008011000c0220355a004a03800039440395041c40c1d03520f0043c804518048c40b0715044040341552680b401c01030351085210100014068031200f8800000c03a4800d10428644e410000350a03900501180c2c0a1421600c1d880541c10103801521114400c0680700d000010216a25000031400f0702c1c410310003080e0000f6200405042c410700803245034480e0f0014003c3e0b403010f5800c4553800766016412030344543d81c1c3e5a000b000100c01d005a089155110102040317191060301c0000300e460a80c2e0146924003107005406a0700310040140d8098065481e0403940100f1244c2042d041e04078006041c01c0020483c07100e0b40e0300d044109c0d502c642c041c0710060030615448052040c400d001300c103840c10540c2c800219251036000303c3c900c0d01c80c49200412070301020030003040541d03042c0d025404142c0c0003482503544450344040101814140c00001146a1510b003904155600500c0307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 174848893 1250 174847643 174847667
    0x80a030c030e0a0f080d091712060904231509010506120102040f09090809131d030903030406051605060705070210020c0901060e010504030516030b0123040203040201090e07030c030c 80
    0x1c4140180c004d50ba00c01480d500080312854400303441d080c0740b4000420810840707603020042d28026880300c284896020308000c010388924050100c84091101090540e10072040d45141c804011004442c49400c0c03518246600c1880400782034028144808100c042d00014040c0d1812110380e00140e0481c0f40c040d00703c1c40f992281c07032846030030000208200e40c1c00d5040000d0b00341c061880c071820710030342c00c2c04030711826074244c824141d442e42d504c001256a61b41001140036500468011406c0014220100e540d034440c42c0501000e001010541e10400b8151110812242c2d62000545000e030801a4025110342c0103158124800d100d40000094202d01c005150048030800034620701d9a0303480c21b10295408000c1510070343c1044801c00000c0003107841040301c00040255501e0314481146142400070304103106030403401c411482c019501030342c401981c45106000c4401c40e00160b5035140c910040c0c0d46540507510410005503a407080005a44d090790004001d0a0107880510095001c00000c81366104851 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 174850143 1250 174848893 174848903
    0x203090c012d0e0907030f05100806010315060f12030206160c0b072601080d0215042904150c030605100809011104230d031b020d080a030c030e0a 64
    0x650345400b1202d00c080305440041c1801c1c282c40441d002030201e581c0341d0701101c92401180d115145c14080c640c481c4205039100c40305800450403035060140140d200d442c18840580301d0918180c40c050050101d87c400001400102c001c4140e040d80c41039628a035410490055001d400382c40f000074601d0103400b42c089140302060352451a0f042d5969030386620030310040d00c03041c10401e0f40a001d4000200422030861502044500c1841c191301d454461850003803155502c2003150024150b920f003d160440799290815802021002d00c44100103030240c882e407050141c0b0181c6440c48092001b805042d580c5121035104040d0140151a91007000341c095988910480740c02c03046024040000c1441890360b6a045105203001103a4040000d11041c200e030019000311084044290008201d20001e05000c0f1000206032648101d03002c1075280506a00c3c905c0c0a00c40c08020b0940340b401c01c41d569040c1c00300196600040e40b54407040c03188401001000110102d5021034a0214060b2020100044101c1b1a541c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 174851393 1250 174850143 174850187
    0x106030b011d060d23010f140a020a051603020a020301110d05090106050102060109020d0b18060a06080907090e0a12080105120c03190314030a0f0501091803050c03040b04090203090c01 81
    0x903a03404000030400505d6a0a412549118445900d000e000d02c504c481c100d10301c007241000304400c80d42d241000c0905400c0e21f841c4100400440303950442d06654040c42e07844000000c00a190605a042140d500c40080d071551030100c01500035034103440502004c034040a001c000541d1901c20756800c80744c03d4020140968010f0004001040c0c00d03400601c06038804100119566116901181e8040110041da201c8011030300200015400c08851031070040807245011411401c20b103103695150150f50241c160741c00d40703410010751005010803490b85019800040d11242d1700ca4030100500c5c410342800707464400e0003d4010420392503000521000d0010005024140c3c2040c218541820881c40c24812014440103180e802ca0300e01d1020095445500c2411000ca80350500c0b0041800b15001600080895450300420450000306010b090782ca1760750509245681c2c482e100b8070340d499805030ba8800e004420b0006008182d45841c0c2c6c02860080d41c0c1d507170481d030700403550700f0064804c5803040488203040342c03030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 174852643 1250 174851393 174851419
    0x10050117040b0c0c0106030b0601030506060403030804020112270c0b0a020709020310080a0302030d05070c08030a050910060803071b06120b01170406020702090105031f050c09030106030b011d06 85
    0x75010a03036040f0b00c94008081c40c0c10411062642900c00035032042e540c0314101e508000303c4c0e58050003919400030303045a52510385425641c0c05070039158090006410030a6203d480c14131b6008070743c00300d881101e00c0c119601500004502c0c40c5284010250111ba040d400524000340c824102c0d01521860300454004c1c001d1941440001002900000c2052880211f50440000c024a003401702081c160300030360103565188020050101550700142c414400c019440c2c0b443e10100b07015800b5071350000c0d0541c034081410349410b070241d8078000c617690310100b546140940005040310000000c040140c8a43c05e9400c00034041c2c0e40301c003007024040c4202000301340820302034403101d00c05510a034081c5405042002c1491550320400b08910000c95086800c40d90000741130040d4942001300c14010b01c0100c000300902408445481d4800101c40e0300002c00c140c1341c10110b10380500c4d55080e02c080f00e40c00341c02008555542d04200040d410300b80b18080982134100509041110003070100746c401c0102030031040c44581 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 174853893 1250 174852643 174852653
    0x1216120503011412150106022103010e180715050a02010e010e06040305130b030a2c10090201030603050d08011508071b02010c061a0a09090c0501030b01110a03081005011704 76
    0x101036684d494003070040d954202c1580f600b81c9a4903000e040300c0e900800700229441c10030860303180904640b030704002c1c1c20f10041058036607221220f503114040400c0e01041c544060402440c0408a804c20340c0d10050590742105119800740180c011500c5030307802840b4040c1203103441d034203d0b010b4640c404560f4002c100044c0c003181c081d9000300303518260032980140c0140d48000a0202c2e40050301c41c640d1098492103554029000c00c03094420302e134061440c01d6056401100f22940e900030f08000c0349442c94961a070740007968000e900c0b480055400c04141d94084492200041c0301040034004c040c1502012101031140030321610407144986155201ca00500c40781c940e0100c40c0c1c06400d40300300d04200c0d60020380b50008001e03000344284100070003040903c00801c0d00c1080302000468000c8140140f82000c07200c0400c0c000d80e04030040b0b80c42030800103440020500102c07400d040d40d094040152141c040303842c041581c02406180702c1d6825882c403c43c845d40b283d004581c1a1382828034000380700d1040c404540410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 174855143 1250 174853893 174853909
    0x5010b0a023703021e0c041a030c090903070507080c010807021c0c0c08030c0f010b01020c0612060d0b090a0204060b0741030301030c0906081506010212161205030114 73
    0x41d000380116000e006020b68000c2d03181d8154940d50780a600462504c208a09042c0240c08c0c2d407040c00c002c1d8010000003800403d9843c3c00c4a034600b8420b81d409000f041046205001721024580c00a00b0350303203403640f03400d06280c0e156440a2041c2c0003500d10800100c0d0f06101080780178860740d450f441480d0030395400400300c0d14040880000d44112518003000191481c00300300030800074500c0340141000720351160205003100c021008260564106401c480c030305030b980d00106d500c04c500498150003207442e00c002140442602c86001000b03d840103040c0140742c1c1000506204180c400c850078400785403203542401280c02000001009202601d01800c4140554108200c8000300104030880315030210040402c5060350803140c0c0c0e40390708004014014425542800c0c40034160214003400b051b0301e01a0402c2d900c0300e40840803103c11009002140340d41c0e1013844600b03204513170094801d89405101d02281155042041d0403140f01c018a110850001d004600740d0303049400440c1c0e520a01000c80c1d007030180700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 174856393 1250 174855143 174855253
    0x4080a060f02090d0b090607021605010302071a07120f0b0f09130503040f03050f0a0305040608040804030b0408030a0f0b0603060f03030409020406081006031104050f1305010b0a02 79
    0x910740910440362941c07200861349003040d01519401040c0d0904142c034a0400202900c14411900895460034201001d442440c0444500703180059480086050a510303080400008030081581c1100384444207910884000c002c40308005c0c100445a039600c03c030340440c0c2c210040d10f41c101c0c0b03a440d801d8405181c030702d03002070f40110340005400354502180c0e02e10741154802d41140340740c14071240c01841404420401d40064000041c01807a0300e01d01500c3c054042e0003548695010040304400182c00c0002501c183d400441d0300281c81440c0303041c07502d400035540d0800c480c042e40c22480d104000302d0404140c01400c14410000d1b110324515101c480620014400a405841d0580320812000600b00810301c0284000d00407603541c56200e00b41848100d01007240ba0380304000b010b00f4040340c2806c1c116040c045030b003200d8007204c8074200b142c0d5030400700710180e83c1c081d04c030340c552481c0500000d04a00458018908024181c1c03d0fa0040005070312190b085c035101c0c614880e09042d40c50000c2e0161030500800c03400f1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 174857643 1250 174856393 174856421
    0x409080702031c090509090715140d020403030318020904060c2016080307150f0b060d060602070504180f06090c03030314180303280204060302040e01080304080a06 72
    0xa0420036070042494000419a010074034000d0703010420100d60311410710409088111001081810008211a40e9809a0052444414032101141c001c50301030440c0320104185500c0707040c0c44003c102c0030354009412620094011a0511070007807003500d00b100d1080a45136000b4140103586c1c480741c40cac450040c041c111207003007400b44030031407001e40550b4082c802100c04000c90060900003071600300b070010030b0a079611510141e8018000400099141c40704007509808001c00000c06101400c5d014020b0f011112a185d0490000600010000f030716402a1023a1601902100d2000d6a00e4003800100e86810b4411005102c002c8001c400042402200140d03290003004041080310550f00d401460a0003503200728046a543e04017580100d88a01c6400d900290143e1401014100c40c840e058507448000d01c05180d0810001404100c513460b00070344409101ca401c004c41d16643c9451000c2d000754441d0060703907500002d410000410000000865095409100c040c0a10103a15512840a04090198000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 174858893 1250 174857643 174857647
    0x5090d030f020f071202130912030506030106180207060b100c1506050613170312010302090421030b09090f0a0818030313090b04060302010e1002030c011803020d0c03020a02040908 79
    0x102d03c801080500050724a4880e10030705103450b4030400c4084135141c10795482c0941000403d4010400c08580f080d0a1600741c140482c3c141d0359100002d005010385c0e00140e1324052444081c075038080b040d60180c41c005204500800c2882d4000c2d04002d214040040441c000400c0b02040c0c000065030800c0d0304c203c081c1ca0f803c0c0800c4168441c1e0008a040d04a0a2000b00d0a403403820108040700310408500341000458000d58a44590175082d80d45011050102074064100a00031070704200307031425522508141c0c3c00351751418041500c40100502101030301c1e030b885a40440c2c04a0642000410044002d00441c00101030b485002d580307102454200e00841c200b050201c01d19001c0c541c609000030040200341c1407a8620075800c002102084810080a01e80224600b100600050741c114603c401c14440442d030030740c6d0303424a0784000ca24510880034520101c3d424039001501a2003500c4880805612a400307542140e003802900300c52a06c15104060700503440300b034160015084c680c3c040c100160061048034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 174860143 1250 174858893 174858913
    0xf07060c03090b0f07050613020109030b06010e130c020708071d061f08040c0e04240b030109050616020f07050d08040e040c03020112150e0c070f1101090605090d030f02 74
    0x21582c0c0240e95030144c00e05002032001c040041c140700480c0d01c00e8425801002c0240c25800080100125000081401250202003503d680c05651022400d0070010001603103415803440141c0a0400c495004000d4880c40e900446c00c0780d03022901d00705850070526074020490344542d07100e584620107402c0c15005503a1182c0b01d5683c1003003070b00d4500760b45860f440e4291141014600f0a20800065002e29401c040200c00d10001a00110300c00c4500200b840803036a0340b81d12407082c1c00040416424181c2c0c0b41d841c085000c0200300d03011451600c0394107104403506c41c1d052409420307070f00e4010384400c0c50348640002c0f0341880540340c404041d0444601403541c1504091721070480001404080c2c03410758103203403401010821503911014200c40ca9038090f9040c03100c4030f1440303c0003440c007030300d13000d2401e84420003000900c4a00f00302c02a92045038015a0b210000540c03403d03e8904501111074041c0040c13900b80000c9006d03405071044034100070000d001d018209806440440b8640201c107104000c50041d00e0f401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 174861393 1250 174860143 174860159
    0x120406090b07110d0906021504020a2309060f0607060c0203040f0b120610091202060705011104030506060a051008060d060c120b030d021207080903071d090f07060c0309 74
    0x2244902e1994450611051109400c01e2500074080d5294003004036055042c0000c0ba40401c07080509098001d11042545a85c400190a003160f50000302c00024480d01050700f0140460052144600a4130f064109072175650900c0b59607050401000d800550401203080000d45130340c8414815005031056904103034541c486072048a055501c40a00e003130700407031000701c291201792000350000c40480e07070b0048280a020024150791341512409202000d15120030b030554691004035041c0a03440b1000304220229101c1b242801e030031a01041c1d5032032195000246a03820402c00319016a40e004240c070303103094120003003280c03200790043c0f03101d0f0000600040c83d00080c0c0039000e0b041d40b8508689800c0c2d66010a86039807c201d400e0801200d220b03502088007524900c4e00850b8142854008020a0b070784d9034505d040000036403084041c504d8140c4600100041c410707034080705501400c03030049040e0300350ba01c0e0034081c6560380c443c04009410030b4201460420000e40610003005400e403090070a600d24a07500d02803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 174862643 1250 174861393 174861413
    0x40605180c041505040e09070e0703021606021902240c0304050102091002061902180603060a0807090501090f0b090f070e0405011203090f0e0a0b040603060c0e0a0501050a020312040609 81
    0x200c030200d135011400344515a203280e00c0c5540300c0c2c202d10003031804900d060350310b904244003d08400709040e0300090071a1714800c3c420001c5c0000e0341105d006d44d035840303107540c2040211010400c1c50b00180101810b6803042007d030402c855408001c280300082c0c9840c1e00c00d0600c00e0340d00162045a41d0b41d420821340e1420780f10a90910001c0305150098012840c0031521241c1c0042c2c1d80c40d01d5014688100840000c400d14a0300458110000b501c0d543d4032503580a010941070002030f00103d0f0b8910410380b00051070b05a41d0480c90503100510010b0119050b80e43c0c5400c01c0c1c0d22001c4d0120740c0404a10300159241c06041c48070f0f680725219142a61440c1079400200d011903a007a0486401d043c0e0018643e024035800c40b0440004000702440c41e002c0c2c81c50401010701490010741100a41a182d030142141c6aa603508110040c6400c054100b00b00c1083e980050810291001070274000d05080c1c0c00010a5800b900c01d5403c21744498010754501000b1209401c0d4910000300129030380c030390720380302000030a000c410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 174863893 1250 174862643 174862679
    0x3090b0a060509010602010b0328170a0306060e1f030b100e090c1e0913020c0309040f0b0a1403030c010905061008070f0302060c0f16050f040605180c04 67
    0x10001540c41d0420b010300810701416001803066a041580302c40c81901c0005030200d65000120880c00c4c00140030214460881c140a0042c1500c43c14000c0e00b5a84450a0000c28043c2582d0b1000c20550b50f65034030944000220350001d81d40507109600c140d0030401008101c44031000f241c600080d441100e80b0004000208c411440400204890a0300800381048940c560f04151740549807410b09544d12060b81481d20070900751620040b000c9800704d00c80d25103442d0f280f924503001900b5500c5400191b985562034001c82010f500c500d04102c1c2004480500b44503003204440080c02c014415400d0130840304034800e1004007150148010030148804e00d20038803400310f08510400140145090800f800c0ca0150b40c0f5400c4101207070025801003003035004180007441100e44c1550841c2d00c03a02541130700c60400200c86490a114040c1201034040004010104c6094039000c8030301406501d030307080c20b01045504078041c0540116941107500c4600005000507a40900140c2c031491420751100c102d000450b81c070312 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 174865143 1250 174863893 174863911
    0x6021b070f05042f0a030e01141e090c040b0604080304030c050a0801050c07060926041a0f0a0c050f01020d05060909010515090703090b090304030507061b110103090b 73
    0x60710501291516001e020600e4102030b141d008042600040450a8880050303a0b42d4504030000704050224001d40202510403803580c020001d1a4150014440c15502292000c8108070403601526090500d114480e015010440044c5141c000740d106102c001c10361040581d0b03215000344800115007104000810142d07215196024500d46000180601300044d0703080740f0000e9041c0320030069002c0c400416101488e8000c030002c20380c15800d09208102003081d00000042002d00b01101c6460203120b0005c20449072005005050542200303c80c8803280100701c0310309a2160304115000c841445041c0e22064607005a00741c030200e418000c0c590b400c907403105018180f02519182040440d1034600d170440c0d0301c0749100c4001d2040e40350441d00088103072981860306100e00c0310b141c0400c880c5446a40010071003a4048007416890030271164903540e981140c07204807403e02c1001c1d80031070014824202c4c1c05100365031035419004c80b0071a0751503501d81c4481c500c01c1810103a94240c00c1c00401c901c40f514a01070721840b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 174866393 1250 174865143 174865169
    0x30804032f150c0a020d0e04270b060d030c1202120a0804030e040b032a03070602010213060c0b0a1e020703030b030d1b0f06060806040b100509010b0706021b07 70
    0x4400c0b15000307550300505110f03c104042c4112902c00d41c01242c2c800d094620340c134001c03984520305c500040084c000b40d42d8200703441214203282c07008000c1d40019802d101e402341010b8104c0d651030108011404045081c020300180611440340001180141054040c2c80302c0c4c0103540d10039038003c05494054100884030790000d0544414401419000203004006c040140d038103005414110010070b60350806400d01c60aa081c0040700c01e1074441040a0450742140e000b030070b40d80c01c0303651014001e0103500700200c444002e0910142c0011039034055520b40c400c0c2c1d5401172980d2400e69901502100912000900241c5035000c000007801c200201e20080c0035541c401e8600080703000c011014589010943c00a1805001c1245444000c59000452440c3d136251301080180e0550b03070526000001d00050751140b11031740b0924041c081004541c003071491255860000c2241026540c8041260110080c4606000424100010004078036150010b01d400280c3c01e01d49090a295005c001c1d1406e10ba581c05a0030100c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 174867643 1250 174866393 174866413
    0x10e010c020d0e04150b1305030303010807060e0303070c05010809280302010f0c0504090e0f03030f04021203070201140d09050709021309150b0309101407030f09030804032f 76
    0x107034818000820039241044414201d1050005c1c540617400b58524498000c24840e070281040d10400000e001c0150070f8a440c1e581d2100343d99981e800e14010800030030803070440e40b9182e04000054031a5180c00c821803001d82c03450300d401174600b5400600341c48031500801d04000410f20110581c0c40b000c0318800d26000e548105410000c0c00c4a903050781d10403903e404d00e02c0a0008070790140c141c4003500c09040001071006a41c000c4a450580504c20217852800040f0800503402c1030718448a02c82c034020b9950107840c06401c003010780c80340326023000207001c2800042a1200103e030b00d0007a1070341c0c0c60210380c00283c0300081d0711650307d461050746c000400590001481d05a2103000410180204000682489205c420078156450100c042c0541d0101c0b41c400301c0050300d04042004245011031140c4001c100c14000369040480018003220f213000400d08101c0081507481c030303d11034102070f903030140e96020503601c03155801c45000f03a03028407081400d00707070459035102e041440101c0308100c1c4640000f00700300c0b90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 174868893 1250 174867643 174867647
    0x60a140a08060f0f15030c13141503040803010909140303040f051006030b0a020a0e0a0b070c14010e1e030f01020706060e010506070b0919080702090a1a090405010e010c020d 76
    0xc3d40c3d10280a00840c0b84028074a461725040512101c40700000d11b13445e42c3d108006040b10340a03400700300d0440103094030002400d242080c1c14030312040f0155a55a00c0c0d89051000c55110b00c820341e8000c0c280e4000308010401d8102c03903400348a17194400e103403c0c0c00d07036440b0788081c03482c6400685064030307007031442c2c1042810403000700030340408904103107000d0100600d075032101c04110740c00510a1000640018403040b070035101d5145115904c0000f40540c00051302d48100303d11642124004940c413044105000c652109540380d02c0d00c01c3d000580d1070465602380760050020b4a20088800078185020400b0010702e44c1c3c060140d180914a10700006889005a042045c10b442c029440b140110300060010b012903100d01007114041d507005050b4001903100ea181c03a03071500c9205020744240420b050304100030045114002e00c40d0300d0003101d00a81303c1c0c494a8072101101c80c09004098598190414034040d1f0a04420072a1700a01035000050401c1c6201402403c2d200c05880c400016007124405400581e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 174870143 1250 174868893 174868909
    0x20301061707050417032206050d0b060d0606090e07030516110703060f0e011802181b0a0504140301110a0f020a2003061605160819020c01030c1d060a140a0806 70
    0x2559114081e200ca1074008d010700075110740d102120b80c1e541c860011003210b440340d000702c8400c148600010001690368800041040c03d150180d001c03d1810400802c0304184030f8018280a1010003d0040060254100c103880c0380200420546150060b008000040385c003511580700e0074030f880c080200305100014082030844107081100088500200d100e41d01685408080c4008015104460b42d02d94440e21090000d5108007180c441700d1500000380112125030110251049a04401c06240a041000b00300340c01c0e01c02078149483d412005200b04849a88119581d01c840101401695540f041545038403105a031101019141d5485100c0034489600b4100246540b10f00c4034001884e001a022000508a1084a00500b212002c0020980c14040f440c402c481c0d0200d1080f1050301d0906541201035243c003004095980032030b20740300603002ea40d8043c0c0000c4958000ca5110300740c4c042c4d240c01c200301075a01308402840c00c01090108159004480000410b410b180c561071b1a0103900c0c040f0208032003e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 174871393 1250 174870143 174870187
    0x21f0b030c150307030e0307080301080a020a0801050f0a0f021605240408040509041106070b10080a020a1511070f090b1f0815040204060801030b090102030106170705041703 76
    0x18580c08515602c0395482441626041072a80ca07010540031003c106052a5015080001c1c00703907900003000141c41d00c8009030141307a042c42640c0200d0790554503000d4908941084a60305007030309000300015480006075000c5c00008241c42e10050415004080c6056005044402240c0690042c2181200701308090000d100c104001c00d4403480d0361419588140c1d481c05284a501e019200c068046410003284c0e10a009041501074180c64a1350190300301040310110a8946030b1107800d680b280450745000106000b20690f4000d00a500344516050303410140104800c6041c00f00308603410900030000c000d110380c1e00141002c0514560403400c0412070022a99282c586038421114030340401c0f00d40210711040070406540381002c0b005a42e13407040724100b003c00000020b5110380b0000e404542e55411000d00b6050f680611042c1403143d50700c0031900c0c204d01c4207002d0a00403426621421030381c01040720b0f80035800300f0a464280e040c656900030710803c6018905c06406181c00c085150760480365004043d81d01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 174872643 1250 174871393 174871399
    0x4080106080115060e010e060307170a06080a021e090c0c151909060603060e0a03080a020703020303042003010f022d03070e0105040f06030c1d0a060c03021f0b030c 72
    0x41006050441100c03001c4c8940c40500022110340340540e80900500f1039024405070070309680b480e00d0540244244140303c0310304640c15244020912a840741c2c807465042d90a00c400504000c0720903020060302440c41203080b0002d50f00b1881014150f140c102005000708910104261681c0300034050905185041c100d20030400001010041c284040d960101d040151014000904200c9400d0006c05004146c001402d400d04080c1204110355002518060240c029a1040010344500c4c0d00c40c4140d204108015005900c00c1c00030802144207607548410349070341c80c00d001c5a1010220701103800d4540302e210708454682d010801507011021400c250301c0004090b1001c0f54030000c003030000e800500000e0218001c121440400c0f0700581d000b00203c0d000361210a11408900fa95100c00401030a803031040c01c4002400660305031486c201c400341410729164000d164000c440c2c1031410440d4081202c90050301140703e40003607000566400c0c080c4402e174100d400800b0801c0100d5000381440c010340d8418941c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 174873893 1250 174872643 174872651
    0x14070804090e0f010513240c090f08120304020f060403050d050304031106060112020d090f05070915180c0302071e032c040e03211005060702130b03010e070605040801060801 76
    0x100b02a146c03455442060707101c403003109404031041b589906a143e201e000b000d101d1404170320006850300300740964201c1c0e030034016480000d80c40b80307000364442e6042c2c4d02c50300d192041800410014500b00c7d402c1c00003500d0103002e80b403c281c0d07213860b40c601d0300c0d01000501001c07840000500c4249a8452400360f08003003154000e161500700030380004d281e044050103401c07990b030340810a881d61401c3c903040400c6803a0441c5001e030340700b1a241482c1e5140c0020b4421088454908254000310090854420f4211400580d11502c419070300a10b06010304000c140c1d2808059080208000044c1410500c01d40d039003810b490900c0306007892030080d083c012040c00040281031040350b43d440c500449850429030700003c1d07501189540380307444c2452443c0200341d24400020040c20124510304882c0006034882c140c40c0c0d84180d1495a0340301840071622071900044d4000d50300c040340740722100194022181080d00a40000782401030560128101002500240300040001a0421958109001d4003014200e1440204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 174875143 1250 174873893 174873901
    0xd031e0902100c0201020f0307060f050601030501080717010204030206030103060207030206060609030a030c1a160219031e090510030b090a06080c12010f060902091c0c0614070804090e0f0105 84
    0x302d030340c444188014204010300700c2c820210f9109102450040307201c0701c2200e46074440c034903040c80a03001c00007884080030b1504002500780c0d07103c2d000d060304a0b800c41780501151824041d141103c514044070341d4409640805c000401612504e00a40c000c501420300141c403000140b400a0801c20050040b510442c0180038040c495038000c01d51203482640360805a001c0303202e5140c00800d0100a800790401c6105450401c6101e608410072505000a940c1c2a03c000e20800ca00d844200141018003034001007071090610144480d030307000303d500c071659030034080c0000341d46100003250440c80020000003e91a101600c1e81d030301f0b02c003040540150b69800103104160410341c80503035070403010060354071980005c0c404c07113214075083d0b10526007811000b80030f103e81c40d224980c02029501260129018a405030940d0340d0022000e088030444540c405841140240b900380c0c00c0303a00c1525079450070ba1280d400c00140d40052b145400501c0100040c0c800840c3c9070a40074946401c02c20303545200700c0f459040500f00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 174876393 1250 174875143 174875149
    0x30c0615060504051306090e010b0916090b0901030902040e0f1203010506161406010e0114030d0f051b06011e05090f0a090305091e0a06051602041d0d031e0902 70
    0x1441c00da5000740c03074440d0082e46441000028006c07503400b104115240148013680030f00c0c103400c1a80e0034901078032004500d403101d07942404002600114940000d5024400303003c49400d2000034081d1050516000c114080541c00280031107542c0e280c80b154590000c00c903805040000e02c10012000d5203039003c02d0543d85020f02180e0305108204800d12000081d003a01410030a208102034421031316070040342e200d50b0b152010031000c40c40078020b40340c0e0001c1b00c0c0e609131021310300010700c568000807a503500c40141c1d442c0d5100340d034150802065040c510364980551401e02e4400c0017074500034164420f8074101400c140d41e603c404884141c003c180921500000c21075181180a00a0f4215082e50000101c2c0d14107800c0486180c0201a04158803002103c12050315404030a405000c0060031070b20402207039030340c6100391124803445800702c07000440c4ca20483e0142c68260300840044415903281c0080724446000d5070305141c0034901c820040303555010701001b1005803070740540007000f051908200445141d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 174877643 1250 174876393 174876397
    0x310091d0703151d06040203150c0d0b01020f0f03120115050a0f1701060804150c021e0703080f0a02010606030207030801030b19061401080907050105190e03060103030c06150605 78
    0x4090080900e1540240d2410070f950300903003940c291142c2c1c1401e00c40c0c41d001d020751541411742c0c050b803003480380b90000e0408610031909513001c0c2480d000174618040710300e00580058500c40c0070040c1540207013461030002050511411040701c241d0805503640720035034280c1001000040e00421000003001410210f42c1c0c0d0003400700d41c1041114140000c070000c002008072403074068a49650440c00f059070000a005401401890180348107110300c00e03642910001d02001c540a040302180103902100e9002004108a0348406080c2c40311010b0b40c1e440f54994a03002a00d510109510900000010f442604164203100d1070002c4c0069160641c41c054890314001e00854043c0070203480e500d56100459040f0001110013000f070b440b20001400019036505015445601d281c01070b5010071805000180e8850000c0313860401c1c0c60058680030b09095050703454000c002d80c07800d002c2c0103203d0600c101a01e036981c1040304a000713600c61b5551380b041c6c02d120326000003503030342d41d001013003240b04030a0301400450b0300401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 174878893 1250 174877643 174877649
    0x305031b010209031006140922020d0204020a090509100e1801020d0912030b0a0b03040b06030f060907030c140d02040b060906030f01080105060a03030c06200310091d07 74
    0x3104040d1940e0041458024881e543c070031a41807041c41030201e0301c40000d401c44001c596010b01c07d04507000d149001d000e44000101c0b4000b80311240d80a41d04a001281781400910500142c200382c08a1000d84c046812a40907201800106504a10800c26840c142c042150702c034602a00c0540082d1614800140007140500001c00140801104100b1030754254107540034054200418854080310781803000c2400c00080c0e010700040d0400e5001c1c00c0314203205105404540104402510715a41c9440360440200e000d00007507814010354945e4411100c041003010300640d40a00a0100c15246181c1200d00140d5940449950217001d02480959500c410b007120b0f800c0d0301602d011030070010601c00182240700c0c81d01591360005021080c007041d03100140c01e0f281030f2100f00d4002c00c840e07200c1d4010041d28030b41030710000740021000050800041c140f60481407840b0700c0c03404da4944203554462030403250307003081300d9000302340000440c2048000310070301411004880e4151803e030070008001c0201d403a440980 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 174880143 1250 174878893 174878917
    0x1504030308070c0b040c180b01020c100903081206190602060f04050709060602011d0a0f0f0c0e010306050405070e010f0b0309070b070c03110301020412020d02041d2401030503 77
    0x100092002c0e020303404448820790702c00c10380591841d25290904080321a030140c21400c0700d0310740100f6040d84080c882d803410032a050700242500c107043d8003041540020b6216000401c402e51400000140800015081072008500c03400b001d403400100b8002d0660280500c06803880c0c80d01d40c108071054000c101306401201d854012049541c0d5410702d140340c0345c01648212415031400d140064141e0703041d84960181c03555a40240054641d00b102a60b4440414034050800d0504031610400201c10385d00c0c10741014850941900c50035541d03803100e100020b00340d00a603085626501040b0401c5028003041010705a085541071040d4103040549001c44a540580000e0800000114008540800070300b00100500c01441d0b503614071602e4680191449484110360707501390010328454a18044c000d03182569040f01c24890551819000c11268081189099070071594aa01c0d141c071001c0d0300404912071560101c01401203020b407442c0d0916040e103c000c0500300880b00743c01880060008801c9410083e01c207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 174881393 1250 174880143 174880157
    0x5150108040611130303021207031b0303090605040b0105010e041a0f1c11010807111207031106010603050105030f071a21040b0a11090f010311040b03010b1815040303 73
    0x2031800074000c048110491901080219a030f452201504c41d90406030381c401da090b18032017590f00c0007004141c0191400140402c02c00c0c1707241801c102c511040000940d000f45008034090742c503529020210350050b42c042e80c078010584010700581d60459030029130030905690411941c511a00d44d181c0d07508014030702c20b110f00c01c0043e07040e0322540d13a11a06840c020f00d51450340b10725401460101c2500d2102414680401c0c540c000191049000d91030005040c0c0a2001400c07031400c00503818403580d44000c4040b002c5c030000140700c540d074803c10000f0381d01911107902c002403030b541800d040620f8a011841c01d801203600900090207580d4141460340c0141c484075001c143c50700140707808050601d88088401480d807080000700300600a4980c4100c2c050900484204004140c01d4603541542c80381056a41d000450381060a0040d4800d034401e0004824080610b400c240d207607117002217140d00a900606141c030022a43c801c203041d480c0032480c1d49001c1100c401542c480340c42c101c14985c0c0900d100c06014440c60f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 174882643 1250 174881393 174881401
    0xf080d0f0e03060f130803010e010905100e060114120a1a0d030203040302150702031f0501051c02012001060602010b03060907061407021503160207140a0b0c0c19140405150108 77
    0x26005d4040075240c1c4503450b15120b68513240c080c03201000034030850458504003c042119003000340c50200940702001c9944c500340c1d540384c1c015151180d4407501040ca0040800540c00308420f9220103d0092030b140074041001680104d61580c02400f000000b44100b0022600c80d0000f82c00000300c2e8101d80d410b03079a003c042c0c0c121501400141c000c2c2080a5014040d0341b01c00003c207116072440c801c1e5501c40302c0040200b6601c5500b4084424920070030ba4803600b03401d46000f40590700480703072003215021051011039902038209115081d20300701d034005e90160307440b0801c0c140246024080d20b507003d01054000c1002c02c0c230b0f0041c0103013210a0400058140d10000881506548601800a511a807840d11140c0c0d681080720034150000305500c542030040c010710b800800c400103002c4d102c101000c00105041d41d1a810300c0c40c901e070154000504c00ca040d100e560310071032203500e80c6540140c1c088404070116505614000a41200804d02d013401ca1003640ba04003080b91540d00d040320901c0c410703828030f40f0035941c0c3e817 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 174883893 1250 174882643 174882661
    0xc0c040519060e3408091c0509091620010603020a170d020a02210705030f01140a020c1b04020d06080d12090c050108100f080d0f0e03060f 61
    0x203844601d54610742c2c2000310100c0c404032842c10082c0a0100108885541d2094403449101d42200b994a0807040303004202103c0024800c4001c01c3d0003140075410703281e030f02403040716240701c00469500d100c0104102007041005c3d072a0044059600c1040031107010180b120740480100420a4103041c61030120588413103d445203000d511150145034081c018402e25500c40703110254100c000d907400c858500c903201140201c94404a102000285e01415103481d000d0031540c2d40c042009080d6018034144546c2e040041d60742d500b00004101043c211000040500c240c5108141090006000e0b20f882c5004200044d40e00b080000c0307070300c4160103040c140100741c0e083c980020301900c80c4114501e4118140600450010300200c1c07203958555154507456a620008030101c0140c03100322401030114111801d00300025400780894680c01042c0f10401d42e056900d440400300104078640252610307030322111440c0c1c98242c06c0391b1000078140c014100404615002d00000c0e82d901c500815215811041c079000c02c81c064 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 174885143 1250 174883893 174883921
    0x50f04021603140c071404060902070302150603010b03010212100509191e020703170610080109050403090308160203160e0403030c18030302030304060506180a0b06070f0b040210050c0c0405 83
    0x503201000359170f00c4594800d1014039284200000b948903616100b0700203240c80300351089441650745500038100802c1c00c000c0005041d2401001301d5015502e41164440b290f4081c40102008402200924081d062400b5148100b60140c0c000074024500b210a10000c4082c0d800800302e140d81201c404103001141030014041d862081041c010420300119a0004040c1c1014006941694148502c4125500d0104000140c1580c04081010807001c41c0107018984076500000d6000d40a400c041001665955510070705a100d0200c41c1034800003010483e0840c9014040c64500300c04046400a541d4140f208885112602034002404c1c180d4950b50030f03519078011610361040da1000ca031611720140e0350303040103501e0342e00c1200d0490b03144d0329100c00130300d00c1d1500c000380501101c03403154090304c2035031020f003c407005041d00c00181e41d01003001d000d04000904174500f110801071086000c0d88213802c2a205010250f02d04400c3c4906001060000070a0000300113032556894804a601181c5030700c0d04a1014030714 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 174886393 1250 174885143 174885157
    0xb0f070c030209040305030603010c03050c1b07030804030b0f010801050408090f031203010603090b09030307050a08040c09020f0a0e010c110d030e03010e030c10110a0804240501050f0402160314 85
    0xf00e610b400c00c0145900600514441d110075002800300e81e036150800c0702140d8040324684c1114400303115002024517019403a044141a140031295510f4403030325801e1594115038012240c07940100200220a0803803403800d801802080001d02060901d039484225a0180c1c0400034000c070348036103407482a650100150300f0400d00d0b00500e00d0b669615070400402030242260291540280400400c24004d400411280300383c210781d42d4981000e160800442c0c02c1c420181058803807c2c0203038804561404284000d00040c10b10b5440300da55221a4040035000b000351101890520100100807000310302d030600221901c1204881600c0064030740c0c581031b102980040f9145070903628102c0c0141c1800400030081c007040c40d1803412a11103447c0c0760707100e03002d48039500401c2c00061814130081140500805800d50014450f80c10340c140388102e40d445011296141d140c0c410007907111401003080c1d003000d2202194014007501e0035482d0402c85c0d0f600c00825203144d003006041103410b00d0341008188441c81a1850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 174887643 1250 174886393 174886399
    0x6040207020a0605091c0b0106050a02030c0118021315030206030a060801050a0b0411030c07150b040f05010f0f030f02060c0c120114010f08100902060d06091509060b0f070c0302 78
    0x4481d4450400a01d035801255031640204510054051b400b8200c00326000b6040d44416601403981c200081159030350460080c1c1d105500c0144a1280541e00030b008000900c035a60344403000d40e02c84d0340100403400100000b40b4928900d0f1008000c5150520142c80040c2c2ea0160341040d42c82d200c403000b640050000703902c444040d518180900012003400c0c0c20032a04e8500c00c0f074041c0b190a00148100310303544000d480040403101e04000110001c1c010036610300b0442031210307000a10100c0c00c80801c0a4800038001c000e211642d48005011107070135151010041c10440c914a0303442070941c1d5a581c09459000000f1348200c0c000300c0e007094034140400046c0402a00500504c40070500605c0d400d01170000c5145d040c881c83e021030004a136107040c940e280c0c01140c0302e410082180320340ca04030304c000504030b0f090241e0f00f22104100410001e0f25030b001340e100900080301c00103071101040c003c41111742600e0f004040c000e400c1410404c043d0b0b404a00b62845101c0c00c90005964580c60718101070703000129840250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 174888893 1250 174887643 174887659
    0xa060e07180e0c030d020604030c0f0f081b03190507170c10290f030c060c0d09150801050603070908070303091d041e0c0306050a02030601020f0c06030f0604020702 72
    0xc6104102c0c1c1000c80200500c104407004801030004064480810200590050b0310840009020900c181c0101003c60300511042d1810b1102c2d03103841c00142194501654020000100c0c040f038001940402c40c0030301102c3d8003450400c07254400c0c80300000a003010b0b04040000c041500400d018408014602d40584000916a1608840e603d291144e0400300c0048032186000a07150406060b0410000140350b0340401040043d8208104650450070a900b181c2510441080c03500c03075180c44004221042c2480014003200b401450b00074071503501608000310401814810420181e0484960b5055501c03c990b01616940c07032010841744802d060384511814031899000209064002c0c07603031010b40f00d042042d40d04585031806800c020384010b42e4018030302444403000300303030950305030f9142006284680350145000b503582d04d4080a45105840c0d85141d5580001448240d6030100301003890464104080c0a1450014000a4884c0002403014400384400c00010380a036071244d0445092650003000c8070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 174890143 1250 174888893 174888929
    0x913020d0509010603021509010e1003091a01080f0c1e030a050109060504030f05160201030e1615020d080702060109050403091d0426070f050f1b130209030a060e07 72
    0x43c00303405944001d03406403036005000f044101104007101d1460780c0686070700008c02c042c02c040c06001c034000340348007040507075030b41020000401d0700369a944031151801400000e541880000c41c240a5038800c428003139440141000700720303280c088511180d50381c205125008405010007082c20403d20351801403042d481c000030001080415400140250b000796201c90b00000740304e2095809201d524942003149814a800e02c00640c800e402000040c1c11f210103440c908518215410324621f5aa00400c41180d1007400140a00364104085100f6440c1450302420a0600000282d120081030046416203034598001034140340c082c0074510020400e0b5111804034030201885d0b43c100380703400d0720112580c480c0200306c40d00782c0c04203640d40d4141c002c40382180d6150400e183d6582d500341c2020202112580100e000000c043e0742c00307021014a000b6207078003c132036101c688801c0101444001d0f60440c40148148400f90b10f6807400a005a2056402030b0f00042000400425070f1404240d0744c0242c0d020802400c0b46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 174891393 1250 174890143 174890161
    0x40807140f010203072003070b060319080909060301020901080a050c0f040305010b010905031c051b030714010b180c16050115080712050c01120906020406030203040b0901090302030913020d05 84
    0x1540311381103540c1c40102d4034100c10000001b134500e1458940d0350741c0c002d101c2040030681c16040319400010040850310003035140790804030190348418080d14004000300c4c40d044c00d030801d903040942c4840214021884c01c1110000a00703200c10181030205043e60b50800580d0b0080e00d1000c440704450142e2540751599900d103419030190030b900181074002882e00000189900340011404510401482016826251070b2012a1242c00052100c010f0742d0000c0004c1c4036480e400d0004008440c0502041d01c070004107034611500391840904042d010308440e10000120114403c152900800202a8540c2e01e406a101e003100142003c1800382c1309504c2c00c04282c1c445d4841154040031034849a00b0342d02942d03501c80300c0b181c0f00210288080c10035003240c00c00100540c45044800d0b0035030084400003524015545603601241c010341c22072400b090340002484140000301503620b80c042e00c500002d0044220302e0394001d40f2801140d00d03281c0076443c03058a05a04000540580302c03403140101c41084030345000170007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 174892643 1250 174891393 174891397
    0x13180f050304091b030e0d02071403030708040602070f0e06060301091a03011d0d030e0709020a0504090c200606011202030703180b0604150b09130204260610030b040807140f0102 78
    0x500c10204e03142006e030641c2003c021900c030124600a802810081b80b61051a1080303540e6022104c1e41070100f00107020020300c0020190014180580c0140f41003420007500d0031241c81c513500882e011716020010412695078000c11241520703504800403a150381c51008c0504002c960400e82503041d4200031080042d00c1c007540c811a4040554021103010300d001090a808540c50000700c4034658110346820f00480b200c40d00100000003031880e2035442e095460154008888801c0300c5980014120790300e5051b8102031a00c80c2201105410140010b4241100080c0945200411091603590003000043e581030080e40082082c0d02040e0405c02404001e103040701110200b2a9403a116600d0411140c008035001c0440c0e8007960038544121f032900c200c0c1307403c000204449542040e81c0940070000869007100380303102c01842d064080f0014000740500410103090034001061400f02003039102040000c10082c11001d038100da0040220f69a422090914101030904c03224502502c2c4112802e213055581e0540c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 174893893 1250 174892643 174892691
    0x112091509110d02030303010905060f031203070201060605090315040c150905130b010c0308090a1509030e090601050a0c06020d02270306011212030e0f01060513180f05030409 77
    0x71403a006400b52000c0241ca0340304240041d416070700501c01800325104a91015401c103000070014110842c414000074540300000030700c958001c07404024841c04c15024080c0300054144ca007071444c2041000e0010036581ca08941c0c410701c07880400790100342070084446212006c2c0440a83c2c945a500001d440900304002c50300ca0035004410320300000041d10400d100f20008442c0c140c1d5a4840001036803412a1201c2020b004070000b40a0000070800241c0100b4600c580d4180c030500124040e1290300700580b94651140c840c0b40150b410700f040128503a8440103c4401003400e091100d0008031500307100000340690b403c1d5138460303440005c503190303450f120071a0309000080d401c012a20300301904081c1500d45000303200c2c00003510203d140600001d1000780e06414103d195240010715255100303841403420700e54202a40305039548a07400d00c06814104403a07451010720140030300800380402e2103020520030040004d0011100a00150104a000c0c0121001810503030406d100c1c403040102250800e0ba201c003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 174895143 1250 174893893 174893903
    0x703050712051e10090b0412090605031f0509010803040521030f0a02030d05070915080906040807050a0b0103150617063919020304080307020112091509 67
    0x702409125840607a03140d002c4060280c03400651558070000301100300d588104d0141002c203a50f03039111481409401da025101e800114105410428201c0c80c8421001c4100040d4400500c075107a040022a90484000243c076291500043e5241440d20144e411007035000400e003000064108000010b401544e41c1150b03c2030b00001c0340300051000c010780c400e102c800d50b00113103e8038030f442003503001500f001d10300d40c01a2464520f00304441c0c1d0848000b04c501c00003180c03160800b0710401c2c10074512031640c0c0816090601d0203082003106c150380c0320002000100002000140f00c0200301052202c840d0703895000c0385040003545c41c0e1030300d6910495a02403080410749015400686c00021055441d03075082a0303009064661a2004040100d519608100c15050068003102525007141c4d204074000b030012080e59610b036558958480c2e0b03800624100002150302c1800103006160011007115240307070b4242801101502610650b0010b4006080e0203040d0318a60f44288012109540000d4885446a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 174896393 1250 174895143 174895153
    0x1a01060201050903070c0b0a030e03030907060f020f1f060f060807030f0c0c1502090a09090506060a05060a050315040504140d02030315040f02220303140304020907050d0605030708070305 82
    0x280f09540d928054203001030b0400345495410420700300c00314000e240074002c03841d01066103050a000703545035078004c2da0442d10750b510514003003010513800310282002160750f1020303107401d80f040040f06981d912045480740c13041d113181d14040400380007544510010030460500c10141c580c0c500d80601014401c0707900c41c02080c1031100b200d100340d815106045c103042058440340001d006a0703c3d6800c40d01075107240070b141c01d68204075014241d0345150002c40240507146000c00c03403140914002e410148040c2c000d40c0101300200090145680300c100f51080b03900c10740303030058070381d5220700c07004498141c2c20f01c001c1c0e080391034070f0144028030142154122000102d07800b21989101841c804903074074401140c42240b8a208407440945c0d51500780c00c000340c180503501016044c0961681c082403094084141c0c103015808840c8104101038010b60300740019400e040e180760540c0b0342500810001d4000511803c01c00c800000d00e00449529584281c0c05010050f04850700390741c03500c040030343c0d03603045020545042c07041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 174897643 1250 174896393 174896401
    0x2042301150807050d06210309050303120f0a06090507120c0906140d020f0f040302030d02031204020d050a0c0806010f090b030a020103020a05210717061f0504031a0106020105 77
    0x22002518100c54400d685440c2d41c1d545440c001c80d03c9070040a03402481686529000407040340c544011541d00c401001604002a4186009008108240d010034081d4105020b08404e40c407040305000e0b4030103501040c000c02030340c922996500428250300041c04091400c801d0024180c0d00102c40c86803088420010040d4540728601501c1a4916100b6a00000c000c3c3c08250b2001200c50003920102a000001606060460145090300d810200008410a0011404006628041103081907100302030000e1883d02100ba0601c40074035a00600190055114007800020000700b00030510f030b0160000802001d2a49501f01652940400c2c81960301150400c8004a84041d1910400700c000d20010000d06140c0718a50054019400c80d60400d030034020240300d002c0005800d40741020110f044c2040c1074010741b60015025011400060038011002c03144800c0040031340b103500702d41440d05008405100188400c0c0341c200c401e8441c5800007032094001076100f0103504025200360307058520a80003440b00d956 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 174898893 1250 174897643 174897659
    0x303110102090a0302010f181e05150a0507150c020105180114040f05030405090a0903020106060306031109062202040f050108100b03070905060a020f0111090f040b0d02042301 77
    0x70707641c6003d900c0440784004100660003021040c203a111581407003004110713640c0c08141c601589034498940065151000d0245001000c40c40340a444116030b542200220046000c2060107103030348203030501c040000c2c0e0030148031500410709002406010300f403046054035070313000b4042c02c42a1058240c1d551184889581c22606026003142d841000d001d03c1170079a030703036201c0c40e0580e21008070603121400300b000042045d03280e090f01603208150324480450707020b10ba480c0003400c64545a000c070003090702e0008140700059502c0c5401114142c101c0720454941c039a200080ca1ba600e1002d0220b801c0303290103001101e01c0f81d90741c000d0403c07a24006102a0381681d2030006480f5031008947e2511080040f1205200451101d8090340d0041d804c0e140c101822600c40e0045200307540408a07010150340805074440c20800240038805c05105400c2500d030038000d824000c501034201c1100c15621841d29001100b1a640b036080280c5051500100144940c0c070700000d0003100844040203800f0008076000001c61016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174900143 1250 174898893 174898897
    0xb040501120c090506100e180403180905061c0c0503060a0b120d0f050a020f0a060911010c080a050d0f090f020109080c010518130504110102011802181306020a03060303110102 77
    0xb15001e030014005000c400c100300c7d0403420814003142d00801c40398030700e00b5029840386014415840303604c500854480040d034038640c0541c0365200704a241e08000030402e00c0d445003c200c42c41e15542440d1514070390700780e1a1004044d21030760001ca802d4469401003020b81a01904400c0c103014040d610094400b207a000c456860f4840340d03000002003011089141c5206110301c0007840416614070544001d100740029280c106149024142d075407907140c5a4070401c0c0104651600104131090800301c15011550741e4451a03030046582c45014844080ba41210f1f103007072600207410303203920390400300400201e9140540460300b59401c1640021070705400410200400a05800c60000584400e820903002a5007040c0c5645481c00b40e980001c14204100e81010700350190340e002c1c5100340d402c21050903001c40020301b1562102c2043e04a99480303c915070150310b45c0e0000c1e600086114400c8941d5546180400030070000d02c0c3e000904091002903009900c551551200b415640721350788000d02c1c2d0388200e00007401d074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174901393 1250 174900143 174900151
    0x3060506030f0907080109111e0f010f02120f13050a0b07060f060305030a0e191a160c0e070305100302030d080601021e160509071d01030b040501120c0905 68
    0xc0802040490144621141c0440e88466404103d550464680d03204030709448459108864242090355025458a4031038980798070030000000301c44000a034040081d440002020096060101e600182c1c100c4a20034800031202d2115003102550b00c2148246142060b4840d105605d2004058070000c601032502c8400c040440b043c0303000b5103042c0505a25050010300400e24a0410b1580e1171200000050081c00541034104281e1213401000c0b110f04248060010403051600c0700342c1610300c05000940c0c03141c03200a91038507001002a25034622041e10300c80054448409450070505890015000c071030b007a02184502401c1d03501344103d0326402850030354220103010095040c0c00520084207294480c3e02c245501490501c101c5424424001d800d690100e4403a0001c072290b0405104070707008080c480051401001c050b40d64000c24a442000240010f662850350380c000350390300ca000502d0340e102790015600890002c0003000345594461600c00c0b03040214004940c800e030b0400340061200200d01c525842 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174902643 1250 174901393 174901399
    0x4021009050a0324051305070905010b1215061612020613240f020408011107230a081306080a0b01120b0118030506090f16060e2202040510030605 64
    0x3d0450769090316070805010341c03000c2020220701038113204019003d901e0040030f000b0149103000d40c2500740340b81810416001551520300b404010040304481d50b049030300b04114a05e0344001910307280520401d0844500e5540c1d0300040205001851009006101d442030303103d018049070504501406a031914021288a0000b4084032560030101d000281704242c0d580030300d0b507419031071400031119204071030303e00409600b00c0e54045010702c8441c40922842c100da208000380d0790704007600d95803081c4191001000090441c280b5240c4100c2a000070810600a540d00c0f60203107072a0b0074280003608103180a031003550000399000b80483c000c1016403140050426040e55621400d901001e25040034218840569041140709070032600308201004000c4041c52080c030190500d03080c100c000d2450084090312003844c40d08461a20380760000000400b1041341c580c0e0604044590343e1500007040302c601d02903919684a8134414400943e8070b030b64010016504116000c2c06030108510003103084651303500031650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174903893 1250 174902643 174902659
    0xb10030606090b07050f060c220b031506040819030801060c0b01031106041a0405180c120c0c190212031206040b12031809010e041a040302030417060402100905 70
    0x101c3c41400c8010b04500c0d000d0022a454007181c207240d02d00d041404c86211101718004900c1c1d01c102c00e4600c0a4502002640d030050b2411030814800d81800d1201038200801c01d02c0c0e1010f030a00d01d071a20300586000f0003100e42620b8101705007007981500c008100703c0807000118008000300e0050b008801400d606900a43c064040340c2c255610b074540c1d840c00e240010740c070080922001445000200c80c007090341510f80c0a80307484030b241c08144840e03010000000c3c10024894420400c500140c10291102c1900c0341425a04540346d80703448040911402c1a43e90883c058110040c00240c0141003046003c0d100791405512003041089080d100e01440d1404800c48003440081040c03845d10360000c00001d00010003062070300d58444000741c0703581d101c18050b1b0380003c10520a030000d0b1500508a5004003030103221420a4640703903540c00400d6036285d40803400882c0c2c00e80401e060500c2001501d024029500e10028400d410019680d55840d086030203d1040c00c10381220305407240320340d14501c11544050b02d515 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174905143 1250 174903893 174903899
    0x305160809030307121d070e0115020a060207020402040b0705011b050c070620060103031101050601050403031e210204080c04140c1b01060f03020f03010b09061c02030f010b1003060609 81
    0x250161740b0070b0500d540d1942c0720105401070400d036021a08042a1407001484214545403103a407048105031310169204180b510212005500030403408001c1d076000c0401a5100c00320b01c0007900a015a80200240400100d0b4000030424154828020b1881894400d90304010894089030350f44201e41688004e504900300070003190740211034203015002d403507030b10280b0402c1400c00907240c40c0c404d82c000e400054590007540c2d0300d50000c0c412560004001c1c80c2803450305095880240402e09200c1d9040082201c0080b1070581c2031103030900040702e8960000e444030511101007460043c4d085030060182c0c0380146001c1603100d20300751003000c403170320034600c013081c0b0079600c4c611801110f411105d0701180b030ba0a160500c001011080c4107413400360406402c1045520304500622041c54002103600340640e242072550010360786c3c0c07500280d41c8030f80704990244013068500014404480100790003905481404610310192006402c0207900c520f054501780060306080c00f003103066505921800303010501c0b0350018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174906393 1250 174905143 174905147
    0xf060906070317040605040c1509060503070e040c030f0605061c0e0a08070605160302030906010509060307031b031a010609050402030604020403120206060a0b040501080114150304030305160809030307 88
    0x90203405009003010f5000300e0890198036000d01c0203c030225007840d0344208010400541d2440d0101401070300080815400341e11402610401440c082d01c0140100032001841c05880b80a00d0080c0c1280908103211060040d00c010b400f0b82040e98510400c1410700030082401d04010069030100d000b4108072048900920031741701e00802c0e4038230040704c590194200c4039010801c04402483c203284a51400036203460000c103440c995940941401d0109030040080c4007100800043c00c9055440803189610720340c49400c002403401010764802001e42140b098041b0b000d410003008001100c5c0100d0301024645540707800c081007104240140030200d0007030502807000d4189a4041c0d42d1104001d8801841e2075269200c000821061020681c0103030701c0801044660704011707041030001c0500383c6c03100741440c2c01c100010380601414010308805081202c8002e02981d01c2e401c00401121044454070307500d00340b50078000c0240008855500141c010103000c0381280b4850001680714a425401071811501ca0f0441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174907643 1250 174906393 174906397
    0xf100507030213030b040c05182e0f14010f050a030b13050c071101110a0b04060f052514030403050c0c09070c1103120304080304080f0301090204140f060906 69
    0xc00d0041503801e019400200300e00c2883d2502560290000f04814649841c2280e83c900454001c18094000d2400000300d0b86c10318490141c02c0b40100142010541c0e013612441e8174189035281560082c0e035004c1e0000340620b08880d0f804140c60015070603922400c481d50055441262044a40d13000030310800c000c00c5128829400b10810038402024243e0100e0840400e1040d104265480d140403440051000c08000120012a4414200782064420f8a24401c0040d4440003940805072403100c072800024200301280c0c0c0b140d080340303c0c1c01200f00040d050056038500311600603030b030150b100507032004104140e500072140300803803074030020780c941c550390b40c1d542d08441c1500050342041651040381070980780355541c0300515120301e4155407540c0c0410042d0621540c1004403104903800f940150700d0310b00c103072600581100c0c1c0c80341e0810b80896480c0c0303442c5000c01d43ca00c01c2180c00c00740441c6c00710000c500301c900c42e0020000c03503410401c0d070b0070220140401c2203039521084050a0b80710780200200daa160600f000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174908893 1250 174907643 174907651
    0xf070302150d110a0905090a0e0c0f01020102070b0a05010f09090b070516051c0306090203162006130b01060206090601210615080d020a030e010c0f02060c060907080f1005 75
    0x8804110300c500f2040381e40d01d42c1c2016a010340400c01e078070710034042424812a01c41c1d109580700300c18000e08410a69003500c1d40f1600240500400c02c408601c40e499000350111340142d1740c000440c04651410049840c0103007020b008065000d620040c00041c40c1c2654015004c81d150428581403c030344451a06a80a900041d54001030010400b4100c1c00300d4424803402e44000001c0141d1000d0346808440102100c085402040e0401e02c113105100300b4400340495062205100c3c1801c00f0340c1c3da560303643c80c424500c24000310001803140e102081703036a420f860700b440c105906c0340f494182e040c0d0300c42106980714141103c2c1132a40382d00140042100f805030f14420071001180e01c4600750907000a44440c1c00ba07070740101d0071124400f1244030801402000f081101501e580304e201914131000213540051a07611300c0f002c45810414600c03210414420501c00600c2e400340d006000c180c1c0c0341c804443c42510303040b04032400300303072400344080000c0c000001007021840700c00b0003005464048020300c400b10003480e001e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174910143 1250 174908893 174908917
    0x2030301121104140105040b030a1a06010905060301060e0117011409040201050c120318120d0203090c180717010803040504051005030a0302100f090c09021c0216050f07030215 77
    0xda012010f5250762080310340c20780e03004028a5556042c8818403081d00e6041c40c00c1806544488850702c08258007400d140c2200f52010004030040d2280300040320f01d0022500220b5000100000000c0e18a42203087c00b00d61901c2a00c1e14400b01d14024110303081d0138024031400c81e681c40041044e050a00d06410301a0f8050310504005041c240c04507411460003036144162200b01c04000180841c5642008403c802d00b2440f200400586d916882c43e21641e0082c2010b102d0004c2d0080042552403070f05000090a003400900f51111b07180c00810107031000182603405c2d4010a0400880c1c0746a01e1092544c0c45c16651410f00442c5010702e440d06020017014010302e901d92807180d0a0020901c1d5806211240310f0b2030195000b0048400810b031032030110394003002c804940c11710b40b4110720001104c01000c50300302c5000000040c2c4807880c488176007134400e081c5400101707030743d00c00200740b25441c8008a00c2103500707014500b11001079a84909455545180340000f941c450321103400120000f0076000144848103040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174911393 1250 174910143 174910163
    0x122703120c170c2103010b120c0405060d0902011d100e0f12030304030909140412030e160807080604020f0402030601170118050601031e050c1303060f0501050603070203030112 77
    0x881182c0300e01d4208549802c0d107904032504404641d210751010320080b00f00001c1c0c031851540f409591103e40d2144c401c40c445ca2084a0f000643c0b044110815a801480090412070340d40c604041002c2c01042c03201301c12404941c2c0b0000034502c898140001d621304d94405003a102c4171f0304102c0001d0714500b00710301c1d071f0b02c0e8012480c2d90000049d0f15035017041d900120f0003600442d2242007516001c0d005142d035401000e040d44c075204103242000d11142c6810380090308a41d070350040450b000c4040300540f60034841140240f103900c401070001c201400b034105c201d8011009a5a055031520b203003645074041920041e5110040000c0b000c150314080c3e00071500094141008050550048508168210242d2046a000003550004250fa51302c40c0602540440246410002c0d90606003680300c0034a1a4103515410583d070303000007407080201008903003190004101c84038103240d0301d01c8e0074005401888848000c0a0502d40001078a0070504281d82c050261900a181560708101c40e03406114240b82094910401d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174912643 1250 174911393 174911423
    0x3020d030f0b0a09020d0e0d0212091f08040507090c02060a11120c070c091103070c1106071b080d2c06070501050403090506090a090b0d122703120c 65
    0x40c903c4504001d04d000c2c40090f0310307042698500e408590b01e90703c805020303030499902a850030b036006c12911113640c1d10344e100c561280001c1d008903e060009a0001402c1c400d5001c01038582500308600c144034610a030704641140d5190800f01c02074409800000c00568000c001144080b07070300c0d8105445949826205900300f4514041140c2140c07020b0300c58207908000068484107000800035000003a01c0c00b0070b000c5c81501404e0600c90300910004104408112400408000308545d80e0840c4100000c0107000c030340c841419007009100b0380b85501100e4000c10f0121400200c0c0800817842c82002da070b0030b07100c0c460440101803000d5144c02c010300711030424000d1222000403c0e9104006400174a01a000010b102c4c5400d140c0503000d60a01c0c1c02180c481c2000b840034980d955200c90000060300c5104c800412850101408500c0040c08000000c2c40725951410f20b0135817507803202c0294080c80c000d1000028005a0030078844034042c01d03000242010607102d00d01ca500310f0241c0200e030000c0e403181407041d11500c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174913893 1250 174912643 174912649
    0xc030c0303131a2202040b03010501260c01021207150903031b170705070f12080403091e0303050702060d0e0606040b04180b0702031309050106120903020d030f0b 71
    0x1004071214a2039069004040b42030220281c04004422a9040c9009540c2840d812801070182e060b0b48403e8066440c00e010011034413a031304a6400e564028009110550f110500314654008800f24000d001d40c2d0516038203c0c1d0741c00010900c0368480306801501280c07890b9111000c0303da00188040d0781400031400400c803940400e05c10840014001d5074005250100c40890a54201014100c00304200c0032804001041341118440d54005030300703041055070f4540c60700e044521060550030203020004a4031901e403819030000300683c8a10b2003a560103000a480700004000c0d9200100d130034501c031543d00d070248002070050004084050004042a0400c094041060240c95421250760703080c1c1c0084092001030f05190140b0000c00741c04490500101c000f10b4846141d4110101c8040c1000c0d00702008501924024801c85200070042422030300c1c80342d140d021410240c2000e100e07150019030003055403803619a5910400300e04c181d140d80640a4412031031800c0700508442e13581440c00c160b440520b045566 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174915143 1250 174913893 174913897
    0x1e070f1502040501030b04020c060117010905070b0d14010608041506050310090b0919080d0e0d0801060f0c02100f050d02070c030215040803032a0301060c0b010501140d020c030c03 79
    0x4150100c0075a07218103110005003600d0f40162030500560050200341c0f0b441b9404140d01d03041d01e44183d501070203148842e040d580503020500d005011405031002c0414800c1610000b0440d41380f114506000300b10512080c05151030b400d11601c0001118a0040f03800502801c0c411001540c0140001ca0390a86590010f81802c031652190b2003481d0356285100c04115080d01c42c81e520180007800703840071499200803042070304403500000b0141c64001030200408840ba51010b112201148201d808500c01040050700c07900c400e0013a00c012440c07400103150103601c554a421005036010b001c00301000d001140035154102c6070814801405028000d2950200c2103201401c41a401802c0c2d4a125501d1401881402e280d001954064407404020a200661000080320340080ca0403121384455000f0001c20046074200010141c402280000001841ca911049d03510549000300c1d00015941d03030f640015520030b2200d40c00c004880e0b101b44000404400a80c2c054035880f240e0000f501d03d03151180f9411803c40e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174916393 1250 174915143 174915173
    0x14060a08190b09100c12111e0c01140c0309120f07031214090d0809060105060702090901060f0f031e030206060f06130303180603111801120e06060f0103021e070f 71
    0xc0c0b5011095403034294a004400940c4580e40d25507140240c0f061109023521854a40f03901080310000d07803d90510f20940c41a0982c110400008505003003100009050b80d000303403035800700c512030401c80000c0c3c0b50960044445080000ca41285481c2180d98180c4440c0c5d13407891407032200c43d40c887c0c2c920202085011500d1040304850f02812898803c0b010180550f0130103480303500554071080041c0800c0d100c003c121007044d50104c404015655422540301d000d442c50703400805100c000b00b01c00190741c0011001c00001d42c0c2c070803050b03a50084d0702e0740c402d000c490b040000082c006074030150110b0700904040910890380000070700441c0c94424800c500c3c03100c40816600c103c0004140c62161110881e40800c22030242c03865181c02d1017000b0051106500304e000b0440a0110344c022070705400e401c1c0c0e005200460b802030390804140140514401d0007901c1d008100d80031406200e0444101c03515612030310880e14807000e2000c40d0584040503049580343e1750403043c0221029041d2105000204511450700a04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174917643 1250 174916393 174916397
    0x60606030e0114010f120813030302011508030310090e0c061c2018010908010e0609121c020a020307080c070515190c021314060a08190b09100c 63
    0x25070001c100c0340c582141d100044640b10303200c0c410014080d040b84e44003100704440d0901c1114080e880941054034440c8178800c00d04038016800c440000426030190003051515070100c2e10445803d0380c0f1383c43c65450b8071040321b04040f04456031a0900034840d940d80205030b4078260b40111002c2040b5440400c4c0c4e1f036800302d220b00c602c3c0311070b1180f8950003510500914120014480100b1048600d034880008940501824030000454a0803004d50340d034400c8092400034109080280441c0304070940c0c4640b15103041c4e4071180e16008000c44c0301c2520f0368003000c8072911485240b200c1c070507019950b2540001d4000948000460200b00810404699080068500000500c014101c024a03103401c0101182e0b02102c10071101d0380a0180c6021b0b10f980f01282c82901e021814460703044103081c40050146c2002a0505003034134034101071024280403007040c9038410034041d00c061103440c0c1c40c0da540c0b5544820296280868100100701503001504201e09507800c5a1a5821207280c0300c034490668094801e5110070b400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174918893 1250 174917643 174917651
    0x220c0e09070e0d0f06110a03020703030b03010b061608071403030118180f030903020a0f1404060b030c0a030908031806160e120304170a02010f05030108062206060603 73
    0x286054818a0381007501418525400720101c0082540f4852810300070f0000100d560644003404407981100f80c40e1059444116038441035800301400940108500340d00181c40c0074218082030405200da1004000002c1c401c44c10078100848002200c6400c0300102c0d12410284040390018803101c1030030b0070080e01c4001030b503265130501e410b001004d4200e804401241d4106812504000007541001d09525048480404440130509003982c8030051580b0003904420034213800550100d0000e40c1c84140e41040c3c00c61405204480100002e561003402034682c415810804651410385110060050002905012450314441d4441070400d40040320484051400c0184840400c2c1c02030008641c4641281002e81c0441210a0020440c81c050250140a01841032060205000030002e039401007000070800c841c0e500115800c2c0e91180c04400c01203000c06c42c0b12200c1c41d0714a004e481900c0c103071020a4004d00c01079035000070800d00d00e1000c0e01c81c80442004001c9940100c3c020780500340180100382c4002c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174920143 1250 174918893 174918917
    0xd0c150c03080c030c0d0911030a06020306030f030c0304090e120f0301030201090b1905160510090c0e041a150d05060121020d080306030309030d020c1f080402220c 72
    0x6404032900410403101003204004202100e00c0c450305075a03002410f2840010380386481e00c3c1c8a4218104150180c3c9c0c1840b07140e803071504100b550340080d03101e20790a4060700c80c2076140400044c0d40c0d018030b25027801c09403c1030001b0701c010092680302c1041c1316400701c100e80b090030080c0c2c02181c40e42d12000c484140d9050010041c000c1d96006242080100b0140c55180d1510902c001d8104c02c80e05032030031701d00810070009020b010105504404d80380950700801075400300b1303040b51115801024426002c6403000c6003a20009042d4554425040c0700b00d40198102000800c05040d40e541c0010040100302074020401031b01280f0b44402c105524220f10980013000194104201d00c9500e07080114442d40201c0f030a80d032078005850364411802103a034010151500ea440d0400040c1c198080c0b260215018482c5488290340181d0010701ea191140b02514010701a450074030f040b003151510340142c0d5001c0b0f0784242c00f040c018100b01000c80110502c4210100c1c2041950000038141c5440c00018400502221441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174921393 1250 174920143 174920147
    0x90606030f0606290702120c1507060609020307020a060e070f17100b010c060504080c0307120806060316080a0608010606111207320607030212060d0804050d0c150c03 73
    0x207071301c540449003000c0c8998041d241e5580340d600c078108000f4083c1c20104040c0c031561038104030014160390001c00c1121000c55442d001d00045d00100780507950300f42031220008051103a40300300e9000c0c601c258064128212a51544800380c000440e11100c10302c101d240020b828241800100060908004884514140c00201c58035100e0b80c908480a00c501e030400b0246187c1c0c2101c61240300710b5026030301180d5941c890500c0d0b4101d001d8842a00300b207001c00a1032104006100d1485040080d0b5038032104041c0d02c40c0d03821b02002e4001250000da0b04540ca410020840780074100c0715503c004003110104040d078072041d034642555504c1d40100c0c08109446084a004c42d018012040342c403101d1000300b400c0c041d16486000705200b07a85002580105501201a4041004002d452400000c903089030b04506110794020000d44c44030180350302010100000c501c40c2e1802c2c0003894489500034403000e00349400c0100700a80c40100300003c44030075913480345c0001c840c0500080300089400325160700503c03099500740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174922643 1250 174921393 174921419
    0xa1401050f01081e0f030c060709140d020603041b030c0510020120030403050c0102030709031109090d05030703022b0e030c060a02070804090f0608010617030d090606030f0606 77
    0x900d00705440600140300340c000004004e012104a01580440a003032044ca40b810800c00d1a034840d0030303010010782003498000004210380035403000d554800305255605e100096010080c800a680004038800001c0503107450809560494064500180360100400c81182044501d505c01c03110400540410486440d0900080621500300d000074000800d140001014a1031904a05201c2c500040b003ca0249803040050751028298440210b40e00c5c00d01c00406002c04209200807581c4100790003641a8504104070340314003a1003510000c000004480b401a54650401024882015400e01031180100d00d50901d108044000350311a182d49004103001d0010f41e00c40ca46030b6030803984200a1520400400a5140d900002c0348800503152419450034154030b1059a000520b00d0b0305141200001e000903134007460840c1c0d0140000c010a9540318810001c0209510a08032143c02c24803024640001c00c2d01b010f030282e0310031540000c0c070741d4881e501c0082d00015040c054039115940c410500c90700d5101c0c12 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174923893 1250 174922643 174922651
    0xc0d02030f100914160216080705031908030601080403260402030f0105220c03060c030e1e03040e0a020f0406171003020f04090312020309010b0f040204030309030f0807050a140105 79
    0x1505200c0282d404e001842c040c00050442082602d104d0229140781d8800d102515544448401149080e039841d1401656003403d401058401c5c000c005c031861120860070150007009070712010075429076a405005581d4030314005e1091341805415504400c1c3c060840800ea00350341c13152100700c005400e0074014075280c1300c04144001510b80c5010144a2003040e00c4240b00c3c4882c028038508031804c1caa51811a285441d0b652006040e80e003440125003a1540540002d40d80d0022401147c40c440c00c13a41240044040c51300c640c2c41d054100700010300281c0e6461101503071000202c0e40140c9003c1c0c11280c20001e81e441607011b18006580b80c05030000ea504600c00c0340742c000f41c0c8400d25150160840c0c000460b540084044544610350b44d181c5402014090790b0f00c551604c424000441d180d14101d50340350301800d0f4100e2003030301c02d400c091740002e514a020f10948050b0380c1c240d5128801d1909643e5402000e00c20b0000c19107600c08144030003400608100103e9405520450007404011580c800d4642941d070054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174925143 1250 174923893 174923909
    0x20a080c030c01050117060402090a29031005040c1404091709011419030209030a02101e02060c040b070311030301090f0e0d0c0602090a2c0601050c0a08030c0d02030f10 74
    0x248121b010100c0041c0458000c2d80454946503991503881202c0001d00c1c41592100c0348030b00c9c0f045042c400c8501102481a150000d9040d1039118900031900d50403a9811140106821004801801000701c1080b05082d100005032000980302616114207202130509843c3e80245400010b0203000c0f03513030005503820023200c4800c00c6030030511448400341d10328048500b003504043d40801c41003450340d401c001101020350050854403c0c015403400040c260b4400d0070303404010107880d1015400310f80c40055118031608200c49250f06160608200d0085607105400940400c40e604034503c0c6d091200b03100443c000c0c008000009002c00700c0b8090607003030301c0284a103142140c00484503040c030711307400500040d165076100500695513413101e00001e845011607041b8440340c00d150707048420001c551803d11a40c54002152002040d0b913110b0045504d44214240d0410710303008850380030f0004071560702541d000141d10208a0030050014000d0040760002c4890041e40710010f0284050072580b005404044c01040d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174926393 1250 174925143 174925169
    0x1a0307050d150908040e0702010c111614030a05030c011e1107021909060801050612120f030a020d02191707051b01090501050c03070306060e01080c0a020a080c030c010501 75
    0x107032981200c50528440b504461a22140410100543c2d02c0071034010b808400151645c50904902c000d00901d04100b120002c11036044070b040203560001030740d8080440d6010780b034000d18141a4080001c00e114040e594052150103070200006805102400c1d507021a0b40000412068810b502c41079103400074002e840c01450144014144c0f03104c601211421a0141da5415000d50700b0504900b2084003644075100d070914005001c40d20080641029000707182c200c41c510b81d910340211680c1c0d2601c81d1040c030503100b0a401c004080c4125000405558407528410005081c4191201d0b00c40907030b4006d1130719450000e0580624803a19030009240e1002c440d4000d04d181c01460814009441032060020b231200e40c0f088143d4004420380c00350003d100701503119000b48541c0c00c0c610201d9045d40c01c162042e80201c0d0401601081040c4600c0c90a401c844051f500c1e0082c030340700c10042c5000c0e54000c0ea2000d0850080c140d20074040785540e0014000000280004c5507aa04041c103402e08650040e0483c10308150b0b2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174927643 1250 174926393 174926419
    0xf0c010209060316020613030f0e010216140109080d08040f0303020c0d080105031509071707030f03090e0a0b09040b040f171909030f080c0a0f050604030e0d0b15030c041a030705 78
    0x5c009c000c1c003507000e018107000e4088901500140d2411214041c1c0c2c80e82428042001b2589110305001505145030a0321540c0360030341c44003031a50700d03591041c480f000020700710000940820920720720351034000e029041c018a0040b100c03603038904000c2c01c88005004076420f5001002070f41010060480c0201070b05810214900b40340841d40d03228000d61280341c803040414068207556030018000040119440341c640d01c4015420b1078040c00d48081d80c800c0042c405420000620840901d019082d212180181090f0711f50f0349640d12501d20342000b50050740e07000701c008050303400036009406491800c6180c101894403042860381400f0001d1400d607612041104080c030400015810710459010b4580c890704582d2200c038018880c500d071182c141c501414401480100406010380441c03410302450103036481c403110724540c04c02e1001280c20004014480400000018541210241401c02e1b0b0076004040d52041e0700e040e800602070701c0e108081009115603e5000081524041100b200141802d584500c07250f02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174928893 1250 174927643 174927647
    0x40b03071b05070302060a180e07180305060604050408072003070504060806040b0411060414010305160c14010b10090504060e07020303010308030a0204032001080c040b0f0c01020906031602061303 86
    0x80f074800240070b01030128103a2030a50207244c2240b944074002c0d6580030b00541c1c400c54559000e000b0356045021035880107403501070440300c0e48040260f0b50400018001a1911411321004020041c82a070302030f1020f202210000343d22039240c01682d0306030800030340c0c604030506c100760800416500407840307145021307001c00021802090081d485031b0040c0180d6400d030388074148030103d1a410031503a54084800034011401407a081c68490382100c0a0f40d0401040d1f4480700821740241e4540030181c0400ca4154420000030648100017104c0758034a00046500000140482c480c82080c96020f004180c08601c2401981010b2240000030460b0361614001400c049001030344a10041c04080c00304807002001502c014a150104e40c0119408068010040c0d000c001040300d559014940e14001a80303000492b00585a1909460685009411036841d190880380003a51a501030109150b095400344072481595032804040c51003030b40c154038035501c034407110f80000b0b050501c0100750101241e451040c407804a0303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174930143 1250 174928893 174928903
    0xd02040f090c1e0e010c060204150801090614130b0d050102031e0921182101150305030d0c090b030f01060f03050c090405071704150b1507030e0a0308040b03071b05 72
    0x200e0700f800d20346c203804024100080a0320468026a00c0403014224003240aa4011440c030704031034034510708010791038071841e0010245561240f126400000f112104000310aa41d000c4105c2c504000c0540d40c0040d61030381c82600b0380c1c20444000b490001c2d00a00320940141c0c8201e62070340203a1800c06054010b407105041000605086d5107400303e03030404140f215041e07524070031410031520300410b0b040b01048082003040c800340c600203410840b03500301a019507441c00d02c3c0d601041035940c0800614203040c41005c00c04010034070f002c0184200401008002034001030000214000c403404042024550b0410002426100d48802e12800b010b02d42380400c0001500c1d8002d03646103270710458001c10b098072003100454412500c1c0c1d005005030310301c0340300b17100c04c0160b40000c40b80410341c001018482404601c0401036554524a0502d81d00f1508111b19400a0300c100155011108020014903102c1d8032501c2c0c1090f5074001da0014811030030000140009260419010280d500d41c042607030310110495540c0b151aa = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174931393 1250 174930143 174930167
    0xc150d02070c0825050108090c22020c030a020f242e0f05010f0804141f0915090f0b042102010501030b0105030708060c0d02040f090c1e 60
    0x1603011481e281000340101000700249540f81c1181c0641c0050300005a45401026400a500004a00015595004015042c40f846544c6c01500040a00d00240700c216407a149061a50400c40c480f03941c241007603440980b2102040307034001c2d230b101e589901000e45401810610143e5680c0a0f0480707004200e03051510314081d003075281d1440d070203032512054880c0e40140e030340200c1c0440c002034001000525052803201c0403646040d0076649000d5071440151000540c90a05d800090001c000040100c1c50a5000311500d0404008560400341030301c20300c401924040c00c20611450b01c8903560382c01e108002a981c0007401c1c0700c2030204101c42c1c1075910701081040305040140200c01420008052004031190001c5ca001d4200c4202c81c80300c840e0f40c0080c02844240400c86000090500101d102c2c00c5c0020540250307007440f4010402500c0304003039002c01c3c2d0410ce041583c1c842c0c08020200d51400600d1982e03004020845002c108940c0d4440094a080708e00108291b00814031401031040c0d903071001440141e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174932643 1250 174931393 174931417
    0x110d02210a030207020604090b040605221a09010608240f040c02150c07020411030c070b0415060312031a0102070605070303060503070305060103050f01021921060e06030c15 76
    0x80c0e01e0100710154040c1c0034891020f0360100c0c010400180020040e08450f03040c1d40d08803010440345072941e040110000302d815150344101a25915580c3c10110366000b024174129944003200d10000200008082c81c8098000200180d01c500911400c1402c0070151510715003210903040166014078086010341500d07040052280f078071001602318550082c404055010540c006200b80d52a19220741e1314503502400c2c08034061742c600392600550120b00c41c10b0324004c02242e0282460096141c84403030b00c500c4050410344004030b00803034109515031a842020021032181e500d030207004100c1c2d140034084808207083da020b003c1d2058000c03030242c0c4e800b113054021750700d0794102503884221900f0218020640703500b015400d0701c2103440100c140720380080e540381241c1c0304d0001ca6064508840582d400c2c1d01410114410070404846a600d00718000d203031210301005000d01b0310f11202c1d080d10208080d94001c0c7d0064020000c00020700a40e41414001008400030594040844c4514100d15441c180708003a04418 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174933893 1250 174932643 174932647
    0x100905030a03050d021902010c0f080c09040b011e02010f0614030d030c030e030d020310210305090409050a0f03140c1020191b02090a050907080706110d0221 69
    0x3803c020705605949110603070300c01ba50202d141100b0081d00801803201100c2c0170800e8000c01c0241144561000391041b9030103007449041040c01c0c000e00c809000c160990505110380f1022012451250030690308011042d58000b0505062220802c0304a400da50800602c2111a034804800390b20005840e50300a07490b8600020600c106110450040c0142e42030303043d041c0000a848041c40316150003441c00b600c407041c40103d50135a44d080d42c002101108003c81c1c030300b5515510a10110b03010740b0180820000251000c038031001c960b0ba401d81000100e800c1101c42d0811000000c0a040d4002601000e03815060100c0d0310b0301254001ca507035612004051144060f482d40c0d1020041041d0b15980300070012100455a01c0b040f08410403550114038201c60b0000130242043c0c1046450b801420004540d00503013043c405440c9c0c500200050080202511400e216800380040d17401c9082186400401e095552009826241600d142c01c1507103850441c011980030300d4144c00c0d06180700390305c00fa0404018130069 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174935143 1250 174933893 174933907
    0xf0d05160f201603030c0b010504090201090608040510090b070f0203180d1a010303050c0f01060f0603050a1d07090b03010501141009150306140406060914040b0901080309100905030a0305 82
    0x9850040444144000d43c203503074100008040e004112540154860984001c250b038865084c042111651a0b0107400120720f010308006490084d001d59401c1030041c02a669100c5071041c2a900341c40840c042250841e1000007040003165008241c601d5052561002c3c51400045140c0000f10a42040f9041c1c8900c424841c0c5e5004c01c00d4000c68181e1070b018900744401e1660f900e040240c02504845890744035405030703d403041d00207141807055605523084080b84000d40340c1800380840003400010300c1c0c643d41503070b10001c0700c035165010071006412005010007020b4850500c07034906c0a41d542044582e000340e0401c001808010155140849a0101541c0700c1c00e018090700412618242290702c080541000107144140580e410341090003070b50506000c50702080c11020078042121518480c0b20006000442c05020082541c20010b50f805001071020441880d6075001a501050030382c48080356601c0010305840505154007440c19022303031410441ca201d4034101c0400d4444501480c001c1c01c000001a943e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174936393 1250 174935143 174935207
    0x8030a1805010c050408061b031b0d0920090609070c021513030c0608041a07020124090506060c0601050103021303051905060a0605011409060f0d05160f 67
    0x120300c981c0240007488408071826019240368014010f2144070f0003000000b6013a204854040c1c0300409054a490345107a840710142034400340403500700001300ca801c010908104006000d0301750300c1d40c0074031001048401445800140100c844040c01c1c044c00a650030000030303580d01a2046e42c098200d04201012410034400956081d040d829421205040411f15005010014880f0b00580e88110251000745803074006c191030040c01242c0c010503060000e108028122840304e0600d41101c294000801e180c0381c1c0e1145001a002c04503140541c10800c00c90812103c100c3d4042c0030f410a10907180c0508d00503c002050f5202c4205000312410305800050b007006d0b40320081056030045405c1015114040f0412a511010400d100e506817450b01c51000807401d0700c031081c4208002c27203a050711a20441c841003441c2601a401580c42c0310b030305c610140300e601900c5030140014080e030070489100042d1880c106214050144900100004120b004c04106025642106980f0920320030b015103546c3c845908410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174937643 1250 174936393 174936431
    0x90409020607081215030c1908070902130906080601090207020a150302030402150307090e0a09050105011e0905040f14010603200a1e05060318030406111908030a 71
    0x8000d4014100103441020311020360301412031000300b44c80e030008580f9080f680e50611184138107446c0d0700d90084142c0d40301d68509407040e851446241c0c443c0ca1200342c3d9580352117040500c9640409a21500051003440714048082840d000d014401c0703080207170f030741000e201036981c000500450781442c0d80083c9940c00d40d512084402e008061401c0a5140703d10710390070080180d001550301300e008504c0950102003480e40d20040e203218004554811421900d00600c2042400e0050100c0c882c4541d03a0905802240b001e009007406060685045810a0020145004c404010368032204007240390405000018000b8002c00d440d150b00148110641e640c0034024030300515156100400440388149464a11040b051401c104042c0c21184500242d81d41c64103084c070345420741e2400b00154040c0c1c0080c0681d161040155400030003035000300020441c80c00800345503901c940c01c00004680f0206803903015040c10000c0090143c0c050f0403803d40104c0565801505000107022940d500351903440428150780d10f800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174938893 1250 174937643 174937661
    0x9170c0c1008163f05040203062d070c12020105040809010e01021005010807060e03071404090510090803010509090114041203020904060b090307050111120a0c021f030f0b010e060904 80
    0x185404d6482c0c60510450b09640102d42c2d4003030100000301301d240e1001c4c030038401c9920454001d40500000d540c0d88100030079049101c1c1008403d80040c03540800860b600324041c922420841c0c540c01e070111000d04060902110403882c582c1160705040401000a56031825201105c000b828280c04101c1c0301c80050341051480c03c0d40200300d0303203405d000041500c00004d0303c0c001c0341c18503140d503941020707040f0505441d40440c2c000c1c1180d02104400c0d01002e4249540705c01d0b0700a00450944504541040700b0724152610316106441c13200020006011300e241180c3c05135085050b4034002c00c0030b80c0600040ca0030f41d0b0401480a0326180544035030f071552a0282d012603113980b00003001044030586070f0418840b1034100b6003819019105820003c079465000e8004900390000f0407004049020740040411b040b03030720400d091410004c1c82a41000140c5940c080000e212040e00d0701c92642c4040c09030000d00b00c1d108100102882d50400b500003c642c5d801807110607002c41d0640740269541c10f0000420042c0403104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174940143 1250 174938893 174938927
    0x1111b100504150f2303010b07080c0601120b0f090c0d05012415050a120e0106030209010b0706050f060120010b030d09060906141c09170c0c100816 65
    0xc3e46000d81140d0211200d08000749070f440d00e0412203001800050300007481d02110001c04403c20051245401240c050001540314940162070044154119401c0000aa100b109020b01850a00f070801425010702680076150301c0c0d0301c1403245081510a0ba50340803540d0100d000e071110382d69810501c8030a400c40048424101c000e0b4100c00c0c4040d882e03201d0707084948a440c0715450f58603090b0007c248100c08503080005281d590081201040c0c0d02c020003081c4c440089a0203650791034002005844a052042c02818401582900c40800341080c9050f620000c1030b42804001010400c50181c1c0c1040300e00109010400ca10245601c240000b2401000e884010690500c40d00c10041040396210310f104046e5607560780d40c00b000075175450051342d00d0262460034040c1444c0900c0a180341c0c2c1140624540c006c01005000315030581d01d51520350300c0b858955804c040900000584000348002000000e00002c42921a0318200c551400f0042c52504041e021603180d24034180c1c095280b501c1003061943c0d888d01c02c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174941393 1250 174940143 174940169
    0x1050711040626010c0e1c021f08061f0f02101104051e0102031608070f0813060504140907021516110a030c14150a0b01111b100504 58
    0x2400d6244907042c0380103400c001000003010041e81d000010b00407604108001d446d040d50140d1040d08002d5880305041e00301804003040c2d50703031101596401c411079081802071011501243d0301c0700e100801c0303c0401040207016204002600b0040392031034200195643c483d14108802c00712540d012030400e21007180500c005400c00074004040a140b0000304201c0b00d04a61610000140d40f80c80445000c44030700b41405030308240032101c5100e4801e284111034500c0350101d43d01c0c0280c0741d50350806000e480c0400340c540b030001082c0c0c031041740320411145010303061a051160900d8600288202192150141d99000340440e07404034000364001c00040380b00d410741940311450f40ca0500d1480391040019500c01c13000800c1c500442d81c07480c002080b41e90fa140e4156031402401d60032a12039440110b2000202c500d507200d40d202c80d20880050340000e90060140120206505201000041490007030790445411504091024100040c110810016104003039035440291405040300352081e0160342d100203828045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174942643 1250 174941393 174941399
    0x11803050304080318120616031136030a060e0109020d0809040f061202151c0b03060c090a15051204030c021509100302032205060912030f06010507110406 68
    0x80b014020041298045c0c44d50082c2c2d41040010000291040403200d400400c04160901102c10b415a0207980a0802080c4000030701e12003081e0f6846520f080c07900c007080c661103048807040e42c03824244800700d00790b19503040300b044800691a00b000c1000104202d99460011610440072342040c0b00702c40d0001d00d1700c01507409a040a080301c0e0b100b01e031f807140b180e0310304505a0320100044c81490240c400710b0181d0030301030741581d092100c0c10710343c0902421480000d201d074400c8118012002070a03140b40e0f940101d00c3c4034008040c10301e0110702405900c02d0303120501a9000c039444029031f050413600c940401c14407042091b9000d071001e02c1142d00da050078203e584100010b154008000d00e06031482510300c7c1004c0a80040d5202950142807501607000181c2000401ca0901c2500030759002804900d401020007013580d0340d07080040d0003c404840582041003003082044041c081841c04c0d08240907070524500d00038800b0640004e008040b00d05001001c162481800450380d071031b003144d120203081000901c3d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174943893 1250 174942643 174942659
    0x30402040b030d0c0b011e0504050402040f06080d091d0c070f022106060d030e06091503090a0c06050702060405040e010f0e01020d1109030a02090c1c060e130b010302011803050304 79
    0xc240d209840600580000080034428039203a1004c4050b141c1c03c01074585e023440e04002c00750030094400c0c0d074042c4c0c0b0b4440c42010007645214010041c0084001000f10705003c01010340394010782d0780440c0c400031b00314100001607091044c0c42a8485451140a6628640d0f40351010442d45465006500303d4021400c030380721401100102c1e03c2050a0004a135100d079a01c00400030082c10f1040c00500042000da450100307030420001605480c1c2c5c004000404141c100c0c80c90034070640007200c0d80031080d401064070109201826004002400c40c614001745492036540108130584110702ca124059640e03001d1080c1404c0081d400500c1005034004240850240c041e030a038042e401c0040c01200451500b2601001d2400c1d440480c0d46000f4040d026020340311140d001c00c50404001494020b09140400424041a4090f21840c0c13003880b0f000c20002d02e940c03d24500354203c8070010244030841080c18480008100246100713811a03038240307414008075219100034454003429030700c000c20314440440d021032220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174945143 1250 174943893 174943907
    0xc0105010f090207030e0108060a091802010e0a1d0a240812160b060319030504030302060f061e030c030f0606040f0603120c02031504030305090d0201050c040b030402040b030d 77
    0x40c5514a04140d101e03100c0c10858100d109030311009021980c0c03960f06e100c0303650141c2c0d009035000d20000c0510100655032158242136400d12617810300e02c601035022840c02c56070801c85143c1c4810301030756214034240c1007000d0f034100b6805401a44c4e1082240b00700103901c0d182c050300400722107602d14062044152030402e0703580340402c0b070340643d46c194090381c281d100300d50b070343c00d420f4400480c0082803201c43d42d0702503103078800120400b40c00d41d50503000f03442100c3e01c03514400441841591107503485940d07492440c02c0007400c140010740200d0041600f0800d215043c1d40d02030610a071007070340040d00004403d80100182c9080031402c030440c0c05004035102010940401b0030001c0c800d000582e810b0080d00940488001110105c0c01b005208456842c14600352501c0341c0302ca0b00146201a0464a80102d40600454042d008880440010303855400b0000c0b843e1060241e4204040ea50000303014170f081586900310345001d0f42c015110040c0c0040001b50555a85801220b20410041c042d101e103451682030042c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174946393 1250 174945143 174945149
    0x306110d1d0d0206060f0609040912170106050f03041b210605010905040c180207060f06030201030e0a02061e0f0d020a020f1507030b010c2102010f150b0901140c010501 74
    0x6000b0402040c903440d0003c03030824440c0500800490718004c00c0c40030002560885480740360025030781c03405070001506a0b0702201d600d80c581e8641e1086a450140040340d4520141c0000080100900080818020f80d805076504282d10001501200c0301491060f8010601540410700a04102d052000d590003100d041641c0c4c0d90058105210580e00c495200003511400d8034014544411404100104401b201e4600c114080c210350151400c255a125102510030340150302c24000d60b02d040400441da0035200b589240c3d189200a011101940c0e00020054050350381d40740048800031080c1907601301010708984143e032032019199101c58560140c840250031102c1380d02d001d4800c40c4009040340c10000303000c000801c58450440c0141d5a80a0210050082082c4050601003000810f0000580d0f90141030601d02455090400c0c07425090720090a64101c0078044811a10342070442000b0f80c0f41c000f4840584201044840e591018040100c035222484142d110075804042980030144006401050407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174947643 1250 174946393 174946451
    0x30715110703111f0516090b2a0609010c0807020d080f0a0902150403020f0303030921070203010c120b04060e0a09031103160b070518040c050408191403070503040306110d 75
    0xe0303e44042d01039403e00d4090142c4001c1d24000d209080c9210b8009c144c11448a501105404002c141e500000303141000c291407c2080e40d44894a4a40c40c1e07510050f02680440380c0e10040100c82d80c500c0707001d02980e02c0a400c0640e140a000009107807410641c1111f14950317030262040d401104506001c3c031298010380801c038450443c0c503010f00c42918000040e20300503014071024100031000540c2700c41030040c81040b01042100148000b0025913070a225000140d041900c5400642500380810412102c4080b8120311441c600a414040344248001440d405019002c0003d02c1c10400c2c203055611480840d056400da10001036916003504100e000e4618441c41503484204503201c10000740c559009034600c50707201031446140c041c01c0b881c05810141b090400c2c5c0c101036142c2074a405001d0305040d12800507800640400340000100064007030b1103045901d0b10000b6500f89242035407516203074403540c44040d00e80c50311002000d40e40c00300c00c012100f440801c0e00c002c0129401800d003c05400e110410b403685 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174948893 1250 174947643 174947671
    0x24010314030301061409041d01020309070f18020c0c09011d0a050708040f0c090f0204050f0d03050901051e13140f0306070c03140408030715110703111f05 68
    0x190a1000007940d060384c1c030b152200a4140f4400301142c80e030350894101c0542c043c0c0c441c03801e180000c401c001c038400140c900070009070b580c0c0340c1a20000d08d0729a0700c1d402034140244c10342e01042440c141c0c02c0d4142407824a6000540d0700d044003404245411140e900700780d0b222218100009001c3c2c0d03506a03525882d40c90102081585c0c2e102d80381c643c101d450440328013003c170302404005400624100c080811503841084c00340c600c5501c07682da1004403002c0c80b0300540c2c0594001001d020354580184100d5150004070382e40c922201c080c0e03070014118019105041d051201c0403d1694a06040c03015605124030b403081466200c1020004c401c144180621940101c2426410f2031641401e000b03000c40d920a2010b4010031090300c0b591021250845010010307000c02c080039a11800e010743c41d5004000424030b180003907480f015141013000c030080400306071005540c0b030814420080c2c0540301c01d560800b84c060800f401884010312103070341006207017441d451400c09909505c071041c265a60195000d84a0421844 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174950143 1250 174948893 174948923
    0x1e0a1515030204081006060c0b040303020d0c2601050303040b0a0c050d0e0f2d01140d050912070b06040b061c154109070903050d092105240103 63
    0x11703049401a0082d40005034545112601050780c038502c00e90828480d1500615100440229030120341201ca54040094071041e88040554100341d481f0140c003c1e6141004800d515080c0007070b42d640724500c6500a540c42c0031401c18a01c5001d110307000c43e401d82190585401302c01c5460020110144044d08a10401d44010121582d08004402c040e41c0d01c910403040301c904810102688102506103640350402040c54412040c8230b00040c00b4180d03c04032240302003030905203014a076042501c204100c491021043c4841004250050510b6800800c140ca000071210100408a9414030580003444034601ea40801041d64414035441484101541c0304620314054607000d4044518060008c0c40c640021100e42d2424003022283c482075a52a00003000d10107008600041520340104032180000314403904020030910005100c10a0040300c1d5280c6108030310708111204800e147c508150b81c00080003450310a0400c4404c010425980e100d48503c17100c2400011604050007800340811910009254110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174951393 1250 174950143 174950173
    0x90c030907090b100e060f040b040e010812040e090a060207140d0f05090f040e2d0303070f0c03090b03100501090f0506070b1009050c030601081e0a151503020408 71
    0x500010300e401071001340c4a41c09920103e03403045841d0082e551102e030070040844011102002400200081c0d050301c4d40710b0f880e00d0b021b0044024140e001032503a4000000c202d981000e81c44c00c48003a109840341c050b615488444c6030f80d03d868030072140108101c0c030024510301400703a20107a10081c004454100c407901101c5410440d00400c0500c3c240e40481c5050214210310310700304100380e0070041c1c00f07000016400c0820800071728080540081403144024140c184844501c65080d00d141a00560000c52460810541c01400018606007503400c002031108560101440342000700001c0000900389a22400d298000650000721889264046419102c00150800410368003000321003000300340508140d070715252541840e100410758481c20614038008900030480d407003414080d06250112589038901040003400c9184040c01035010300103480000005000c0e07800c580c60384189a00004560400c0d146840c0300e00740700c3c41e0890551040b124031440c259681c190301400071110580211505620071942c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174952643 1250 174951393 174951401
    0x140109050a090b01020a08040905071701030b010b0f0903070e10050405040507060c05030408010501090506040e010b13023007081b0703030c11190507090b01080609040c05090c03090709 81
    0x4560700500c00758010001c00c001648004041903040c01a508100025944e6040c141c0c4103411540802c0e60359014081c010b035201c10000070550000195115a504603102c408051605100e51070614400141c1c10301c0c1c1c864500d003910721240c0c01800300c3d1246500c4003210548440c0454040b0204c00c0e0741240051070740b03000d002c3d0900070384e00007010b042018141a001c50300080040300a0303842d4401000b00041128003413113200d008040b00480000c8604144041009484e20320380c01148981c10548854015a01c0d04e281c5950710303a00b24401690f84d07220b03440f60a00c0c0162441c06141c42c07603036280124004406819080e06c41c10b10350755141402c1d030f5002610072105401500300151100140031040c0000e01070351110b07107200c80342d08001705002d114914861034a00a2040705600e031041c00501b1040200811803c030107001c03516001c2c00308500440000b046d17a2401001e0521600d56800441c06105030721a407500500070107007012819240c10585000168000d0742c010b5924030914a0005200f1080d2103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174953893 1250 174952643 174952649
    0xa060e10301202030714060901050709060e0108040212030a0302180307080d0c020105040b191202190e0f0621070305060616062403060509060c04031403041806140109 73
    0x5880210110700c0e464111030850940703040c03815884100a001e01280b81c2c81c40c00ca0100c90298010842454484d0140782034410141090050009100041c0601341d000f8444000b940e80a1170f001c003c07941c0d240005899002100ba0700e41c40c500001400c01256685500109000041c1c40d40001916038034109040e501c0040c3d204176040f6400c1000c1c210181881405003c0c0c1d902e0051402508240e11007520030020352100e4000b5078042404078400c2c002a030006500071442d108080b0844c01c0c548100b054245a0002c802c0110801001d01401c00345581d904c901d0300c441550103460b15807140c035961411320300c3c048050a05610300540e88002108507109001e1580715034000b402c072500702003511115002c40d642d8680c084980c0e40e264004061a80351040c0f0303600b0a010b206071003116062460401d5812104042c06151054220208105841707032210304441c11258004144008403060350100c900314020f0740c000100b005c120f4040034a8550440d00000f095035110080d0340c150f2140c500c01554491031a00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174955143 1250 174953893 174953969
    0xc02090f010e0f0a0b040c031b090b041503020f0301060801061d0a0e0a091a060111030f090f0a1d0402100e0121060e040506010e0105060a05120a060e10 67
    0xb8000030b502001c1c02551036005286444040b50030641403001034181c3e0700384a00320300025521903410048943c2c2c0c00c500311a401e01814103034141c6043c50f8805181744514000c002d0341d080358000c00c105092103981180c0301041c2581080d0b07180c1d44c6500c4010051102031003210009118201400c03425521b0f00c008200c01c000081c581131107140740c803000d0892464024050000180d49080ba58040740040704100402c00a8842c00002454003c00140c000c0490b1030044a0b01c3c0d0007482282c0c9030351a01401c586280b038086400c0c0008401c07081c002503821190b500203900902003c074150940b108440e20307140c01148202d501050403203043c4000c45000d80806d503000e001506c0a03100200f14100d02e079180100d03052240c070100380592503c1c00000003180c10342d0704a1f00d5a011000400c06406a01c80050140204844c810300d03003660b03000001c0490040d000d41107034000190380401e404041c280c1c481ca0003003c0d600b50341d804516101640c00d220b82d4462149240c4510400d0a92200c2003000b507600881680d50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174956393 1250 174955143 174955169
    0xb19020708070b070b150603072f0c0607022103030105010306050d030c03080a0609060608090106080a0c0608071b050a02030105070201060b0d05090309180a0e0307020a0314100c0c02090f01 83
    0x5a11414070171040945050604038403a941e40c0f01c10f8807168002c5118120589914001c00020400c011508100d90141c9403c0d0b0000d0f8400f180c059404102c0841c1103000710323055612261180009507010300c03414a140d00402011584071b0070070b20f000c800340d41292000d80b401c0200c15615800c1c0320b109084240c1c0240000c50032003001001a0240018507001124074000281141d01c03002c8200c200c4005422940200754500200a031000c1c00b4001c00001e850464060014a0480e660b444a19032043c05600140468440000c9146204a0740b030440c813004c070440400302e40814203000e6110110400705074001d5007040001024580140108012961100c0206142c06002040d480007000058402d00380c0f4081080103442d1b41e0350301a520301110b007807403410f05568280540b8550071034000c3c2c120616540c100f4040c49015a0703c5180c00310481c2c0d0480c149424040c000c002c5a402c0089842d5a140d01500d404000d05940e82e00a8150070542d1003035410402c9600c82c080c070400141c01c00d100c0d0103843e0a00e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174957643 1250 174956393 174956407
    0x80f060612070c0f021c11060a02030301060507060f1805010c02010e03090f030c13051905010e04320d020d030204120f051608210a0806190b19020708070b 68
    0x40381d042000f8007801540380b03019008056001818100300024002d5031448400d0010062080c1208a51a0a04200d030a40d10b0101d039001c020b9140d000510800d0300f40302d00452400d05120f0541c000303420074010704008000102d40340d45502490119a10b06645070743c6886405508140140b02c0d5543d01c0407064000c6040252100820a44000c01c203492170b09400f80301030711070017034071140e902c003080c8009103002103071501c0c00000d00b6011006940c5010b82c0c0c1c3d8107042c010071420240d5000e60b50003542054490300c2c04401d1a003200366003141c543c540003a059030b05110121083e07000c41e2019004003150b00351f44c81c191040030210140c1c040c6004d04030080380c0d4101c00400103a4008107400340b40344104c042d80d004443da90034641d500b5504c0c2d0311140850b08404000c0382481e0200280e02d03000f0602e4084141055543c0344001d1020600a00312400744c0094030f10400c280c09103e000f82d00600303452004540d42c9611100c000402111200c00001512502e500401d021001240c1082950900c840791420841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174958893 1250 174957643 174957647
    0x60f0f230a02070602030a0605190f120c03080d0504060501120c0509150a09020a08010906060e0d051e0f07080706080c0a03060b07050604020f090c310303080f06061207 74
    0x80107031811401c1c540c01c101c1c05001030054000746115101c8a000021042d1501043c0039445c03070000100380c0a0040c0c0c0c2011b000c00f00702d5400e1041035030031612010081c030b1000e16000c8082e1005810281c060280400d1b4403500c031145400503442103105103000d12030380c3d03079842d402c01c6004441c1c0070041440099a2041c00350741803000780c25902c89082008555044107403004107441c1c40c0b5640004c081c0c5900003032070a06254010103403d006240a0000b04845c901e003440042004081c2a5154031404400c2c079204180301e000c1140c0143d14520754451039130103560b103e11650b20510140d0018a81c001c0a000083e4694041812801c1352a40d4882c01091744c1c0e00310400340103070700104504040c0341c0d4809000c940d501c1504041c0c51210712135001040302d82468010403680c80c0808007081e108542d200100710342608803000303450388024019143d1800c21981821803080d0408440d100c00c5900801500006041d40054458020104510056802d4441c2014008107100e002e010080300042c2c500443c80c028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174960143 1250 174958893 174958961
    0xd0f05070501060504050408030406060b090d021017131e0308070516080723120a03090303060513020909010b28120c0e01020c0406030c0911070c03060f0f 68
    0xa0712540c000a2041c1d154000a01202d40c140c1e02907440c2000441040100902c07881020058000210b81600300342c1d1440c001b800b0041400c84c001d010341031181200c070707001c2e0113200d0b40c2d09801c0405413812414503208108943c585407280301540c0c5003150414406840340c00310740c00583c1c650565925542da40c0c819205940c40c1e800f00b00c1401135194013812040204806070050480356200d00e034150840d030048410072408401c200401441c0e900181500070039444120201d8144040c0c1c0d00b00490000301c1380c10141c000304000d80c0b015400c00c00c0d00d541c4101c82030080e4000d01d0404411140240982d0301c44910858a0040f48907468240f260107032203400c6144c0d05d1100c034020742410720b801c03d40c0b00b40303554000c0191020303600100c3c0803c2c011410302000c2c0d81c05010007080c054099404010442c99a140c034515856503100380708171503540d006400b140144590440c1c07602d80d00055540c001d2962454610024240c4086036410f00f807a00240d091203080d207010381f0b45a910759298000d4016110402c01c0713950 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174961393 1250 174960143 174960157
    0x503040b010b0f120103030203190e01020c0405090c03102a0e0d02040603140a03110a050a0b0a020c030c030307020706050426100f0b03070512060f0402030307020d12110d0f05 77
    0x6400900c413508405041a01c0b16010b18030039400345480e00443c5169000d0188084101c50134800c00d10702801c0903036400146208811030442d00860b02d501c0b420b41081c01c040c070608026405008610340c0e0055945940c0004400c283c0242040d0501c41e5094510110400301550b218001504182403c44502e0464040f206030b5000500011351640d59940d000c1e03c01c203c5c241c042c03006400c0a00c00b002495004100740d00c03045a0748018103000d24482d80e5964845c0500d0030014460f11424004c584c01d801d281d8140c40d803d807840c0d02165500c1d00203840c0c041e5a60022602400184166200070480d06e105c0c2c010303a4200c0314201c4405840c01d09240d0350f8102c5001d240300701c056904c2484140e4050004902460b420300007050800611034a940041c941072100d0303904410b011f00700000d0018014080010f55691003888240e00c1800c40c1c649100007403e51045050103503120344503142c030b031091040c0c2c01b1114600c034a075a15100320130464040c442c2e444621b000c502c100800e07403c500c50640f0a010300001c10f07603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174962643 1250 174961393 174961417
    0x10030905010204050603010e0402040507110d03320103050c1e040507030b21061608131a181e03040b0901030e0601060201090213090b011802070501050702010f0c0503040b010b 77
    0x2d05413901c0120300544c1099001c6212078419209020640c1030500c600e0750041d040745828801d400c04c107070b00b644d039901b4005000020150780d451b0300046c02038499401748008240c500324a8000038021000c0890400078002500c1d0303401414000728862a01d1007844051401074100d1010344a052020840101402003100c001d05840302842145959000c1808521401030742c0c602d8076507034402004524000b00282040b042c00c0da001c1006a4507a040590740381e00c540d0548800c000d4504600e008100b8061b0743c0d1044944608840c28800380840c03103121021040c02c4041201d4290008014209000c00c9095032507050303070002c000500c2003201c01c1c4003c114410042c14042517a2040c410101c2c03504400b640711000607551b4040c007804524050b4000003410450aa007440780300d0b00f130f450741c034010728061142403000c42a01c0c0c084985000183c054403145d80d000703002000313140307041c075406030203071902e401990016031903d44001402c5000c0cec030580e4040da820607500b083d16820301c11301014641c003040c14140c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174963893 1250 174962643 174962647
    0x141f030609140a120215040f02061b0114010509060f0a06110f0a14011103040c0e060d0f030314011a0906030615162102030d1d010c052106100309050102 67
    0x5403010004a03c10358810310200071041c1801c14000e061408458440e1101d03290741090201082c500f4030b0b20110390f50111501e5584140110880400170070081d20300c03503d542000c681e40010401010b030981290403c2e21406601d90700c010400520800c44e01d081544100780d500240300680c41070250f014070b000a00215a01490b0a01d5041e01d401590301c4111200c0c481d540c0c9090084d88207004402860684035003403404c5040550302c003c0d0f400342e01d00070000114055400038940d99625034440044c19000716101e2007100300b43c103000300941504520006213003041e4000040c201200820f0440b0502200b00c0c90341000c41003002c01c9070700d51020b80855070101c1242c0500c0142d0180301e005060700da000c4800b10b40380003464688203500d441a031116904113a80a480c140003140c0102c100e07040340741c2065002600c5c2c04205036607040840c00c0501c3c0c040940c81c1012602c0c850f07401200402d2008210301d10700e400b458a40901a0b0085412034903180c000e4136000a504540b8000c0d0050700031700b88501c0000d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174965143 1250 174963893 174963923
    0x3061309140a14070603021914040b030906070201050906090c04051305070f060e0103180609030908070f06030e030c2d030a030204061805060906070503091003141f030609 75
    0x51820045002c140c0f5003410700742400e20815000c200401c0182044e08041d8101600d1003003c01c40041c0070f009000510420036200d21342c00c2c0f1804120303030140c80e00c849650381304d0925650041d552582110000b025600c1c06011849204001403a24840c0b16000000c1c170200c080441413201824001d02211400c50300505180c000410a0000801505000b00200f0185240400080c0a0b0100c8003406041c5450040d048034090011010584481d401003008540054107180458401e0320a50142c04070740101701000c2004540c180c10b4100300c4038280e40034401c41c408071452949903c2004900082d6610452401850a54809903903015002000319451030002c0aa402030643c0c1c80311002d0400030381d0010b014000c0a401c40380c20740a0307040c0410038041550509010840d0784c03003011005c5200d503801007980300400c0030820803160b001d03402800c9030001c441a0000030f40a8120140f049103414000000111fa800210b40c9187c0000d1080ea0641c90841c65038862070001d00074590203841e40780b030944d140c0d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174966393 1250 174965143 174965183
    0xb0a0e0a092d02100f02210d060b030702010b12070608220326090d03150504141510050a05030a060e040506160e0d021c15050603010b040203061309 65
    0x1505070071620b40758510b480d00074030400a02d4010124400c080c000020080031400e90300003448402d107503152941c0507280e45241c0700b810706401020480b400071801d01c10f02085031a8520003560003a18242c00038410a40d41e50200040c0801c0c03c0703035078015944907030002c2202034480c1120540140c0811704a5501498034003400c01044500f6a045e4041190260162000c50b085606024100d040010350910742c01d1900c040740e01c0b0807201000c401010f440d0094601d80c20040381010006040080041207202103250b0290080c42c0112034880800044107025041030500c01d403c9a000511656402c0c82d042070203000303850070f80015100000282e40d13043c0110325200e101c40464009c0c1c2c06000140020324260f800c15845c0d00114484070b003001030454180007582c403205185400b0650440390344101e000c050030765078030b13407003000c20003402c03902d01d83d00d600942c040d035a030115000b101c0070380082c001404c1400a202c140c0c842900d2481d081300c1011a015112a910340c00310010741e1150345002069000d440c50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174967643 1250 174966393 174966443
    0x70605070e0a080f0c0609060a0c02030f0a0302010e060606072402040e0a0203061002070f030206030a0e0601171c08040f14030307020d030e0c01090509070302040b0d020c010b0a0e0a09 81
    0x1083c0541c1d444510006048141080382080729841101c07a01d00e010f20400204120f4020120507405012400c0703132070411554107012020740300e11442c044039681170507402d009000e444168500340c031b580105004540780e41040c604441d05207401400c0f103001244a06980a0100c01a14081c41926400d000110f010b1984d030700c03140e020340c50352100581c8078107001c8108075044022010150035540310103404c020710265850341c0b01c11203404540c2d89489561701410072000d0221070b00018480e0080034004104070301c2a6100c08c1140c01c0d0441100c1d000041e00c1c2c0a14004200c01c4a07000215804400080004046510030074030184501c8042842e607816001c400d2842d00160345e0003001d82c0102d200f1207180356140c030440054500410040480c51300f10320001e4404403460203060b004070310220026007014020340485008045007548103507101c0140490030000d40003243c880701d0715401c014904515141c0002040156494400090382a8840c40e440300c0040041720f2048030890f071030800e581581802d03c45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174968893 1250 174967643 174967649
    0xf09030c0b1804090b0c0a2d0f02031305090a02090405040309090e0102090d080c0f0a0804060329040b151b06090f0a110d02030a030207030c1208070605070e0a 70
    0x4034050702c900881d41c48840244011040e240114500382c80704020801c540e0303516420106242c4a2079580c4940c440032202004d480100b200040103100007a0106955546003110001540d40c65404c5070300310300c0e022a01c0f482038043c0140d850030302440a0145140416406800012389900146419401001315041c2c8408403410317004210307603290800c00640d0034003d003501310258a0007149022507410004070113441d00c803000761100c040480e60540310b0604118019202d03d181d82110140316003850308a00d244e006005103000a4101520400f0021b807281c8201d554488801300504400980c0b0300b03000c000e14903c1c1d01301e81e01c514031150194440c22a040244011488640c0704101c440c04040c0662400758040c054118550080c111121814400715181c030301e0551050070b600308800c000c00090740c0c0d492002d8029500d40540c402090416800150040c201c4c3d10a010b2202080d6403194624003201765560050185103081218500050507540902da003c0007a0900f5020b40307003040d001c9625914223030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174970143 1250 174968893 174968909
    0xa08032809110906030a0b0c0901180b07051203040f02010e060d0c020a1209080d0809010908030702030a0206070e0a0513020c010507120f051506070f0611090103110301030b01060f09030c 82
    0x41c020000b1420081c150982c0704400381d00070141c40441395074580300854000c0c140b84040d1004184002c082e8030130129080c4412000c5891800141c8071603902500b81e1050713004076040d102e1442160076020f4103a007543e101c1c903004181c20761028200d4005407181701c90200050744c414410880900008503c1c0310300c03c0036803c4c40c0e0040403126158a40880702c0c0d003030120008240709076100100031408001800e503022090b0341c0b42601c2c0703503240c07850407502404024800070117404000c0100003081d90300001803c4c801e1b80c1542219000d85500d0000d03a62400c01004039500401c98200c10b02850601c0100f1000c0040412001403410702c10712042409c440303080d1004400940905404801507005000c0c0e0300100c038a00d04c0411990030065110314000889132451030040740e0205400040c40100d000c1c0946030b640122041c05800ca540301d25504907030207840401d002c2840c2c413160001407070641007540d041c0d962100c0074851507402d080341600d611110034007020800c04a0040400011551000d0b00300a20300301c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174971393 1250 174970143 174970163
    0xf061b05010518070504050c03011e03050a03031e05190b030f0601080a05060f0c0a0f02010b0406030b0105040f0908070311070b04032306060a06080a15080304050a05030a08032809 79
    0x3d94601401e040e52684118895801e00f0240200c50541d00100d0b4111103019a5401000d01d0b4000c05e24602c0e146c039400074217140034000c1d1440034103402d0340109541c540d0140e075040941000500810454209031000941800070001e101820700c4103a1103814400c2e07004049802c03605c03000c141285440c009800203d029008400001d04000082203540d401042690503400a45010081d906060003101001c004000703074107801c211070034001e41c008a01c2010140041c0880da4590929100c490000e00c5400e001e40e10f410070400325030320b441c890300d1500c646c060707201480c0552580302110305903048140030460340580340340011110071910091009520a0030714a0038580040c5120021030205c3c402c01e0607581001042212036503038040413200b600c0090918501c507031181080f0900502c2d03080b2021040c02c03d00400841c0c444000000ba108940c41180c0b40b448181d1075809040e04c840c03180600a00c2c443c0c0600104800c0100813444e8130178110344260140c0d0540414180c641580d910b014245e52650358 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174972643 1250 174971393 174971431
    0x6070c061412040f0201030f0c0f0f05040b070b061c050a1a040519031103070809030c01050901080c03070c021309020a150f03020c0c041112010504060f061b050105 72
    0x40251101c21203801d0340d141420218a01d4100424008000030610800802d40c101160300907070202d040c4040707008042041101c1e03100050314054164203050f0100785101100ca4046100c1e07030480e810b6440504105041c881c0994420034035141c003518159000c0c0301082081d003111501c03140300c030701c2038003900082503128654140001e061540b020b9081018540030100808a200003403001c0c0344510070480915442c484c5c0c1000c035000d00708404581814000041e4404c2484a900058050310504030305a62100c50400015951442801030060114062500103540140c2040185a1042035800e002683c40c0c0c0513070020b4805042140d140501c0c0c3c2c3c1d107103841d00641c00c0c207200e50b04c040c1c40462890310450004240c040c20005525080318201a0005124006000f060060f00d01e6400d02a00a010040858401c4101d6400003541d00103901082400055280b400707000d0041101c41c5c800c801003c1d80c0c20300c0001c540c0c450f80b05000001014100041b00b0004200744511482900c182e40c1240d04c86035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174973893 1250 174972643 174972647
    0x20303120a0e0106031109060429030f010216080a0c0606170c030c132403030302070302100b010f050307200106051e061b120403050c0906060a0909020a030b06070c06 73
    0x4104541c00a1a80c0760210500c0091010401c204c036408040b40c1e080c7d015690381d80000c001c1d24200e2080d8810214902880703e00780302440340c05262681c201c0039142d00e500341003c900d00b01c1c05405040c0d070020b4001c0080740c2c00300d0b8104000306422005442c0580044981d0345880d0251b4411ba845a075910500350402c02100c007060140e843d0303844040340500300340030b100000600141c8556600048043d500d000301c03100304541d0040b0003004003416281c40743c010f9503810b0150094005e42030940140c001e10080b10140b0f450380c40ba880010034140c483d003181e01000235084402e40c200904440511450521440116001c0030210522044440000c41d00e9404d11081c8a11072072000031480d400b42c00e040c1848401d558207019660269a10415903021019040c11603140000c04a40360032055000a03011080c0803010a040c0304c1a08140e4100020740c0340d40050200d0707445090142d000182c0e0700882803004000300e4000305540c0b40306140c082020241000080c03100c1d4040601104d0100c031440e81080416 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174975143 1250 174973893 174973901
    0x301060503101203020c040b030c030109110a0608040c15030e030d06061115010b0d020405090403020f070e06090a05061314010e060108040213020d0f0f200406020c0105030a0207020303120a 83
    0x1c80103441883d1404981d65003c0d50310784e5185030162280e5103030b0400c05001e0320200a1070801c158010020700001c44141460f02c10148a080038078062081030174040f442d01d01424050380942c4d032080103000309901e42540054940250035200d410103032500b03c8550030300002c1002d0b20101c9000140081e540e490f105000e089001d8801021781b150b0003081d41d0780044502e00800c41d04440e121154180c2c0da41c02d0000f980c0c001d115940259a01c804240140000e166000800908040c0400f017281c0d0b0850300c4181c00c041014007280c0d002c1d031114007040040c01d114000c0c0c10864025502500c410b0069850f10f206100ba02c44403040305c0d0b40c84031000010401c800550030340c150404400c1c00c0c078601c241000d4011036a4560b28264040b1402d07000100e4a1030a039069200c09484200001c040054000951701da20241040601c0e131102d105125501060205140c3d04079400c40302207400400400d400c007001520103400091110b00b45603801c0c005480541c80a1004080600c29401c0c21403482c900705041904403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174976393 1250 174975143 174975149
    0x501140310110a0507050c030d121112040f0309080303010602010903020c190b072a0302010f0305060619050702120303071206050f01030b040207061118030a0b0c070c0b030106050310 80
    0x50038807100c0d4140b4030041c0111842c484851a1240c0e4901c81410114904022425296054401d000c0704c08401c2c1d40c040c061510b01c907603d980600c444030784400711210305d015040162030507050000204000580c04030b082d0840601c6805c22900641d0303940110743c01c64009910500140c0d4494601100b0554103100b0710980b40e40c22980440100b084200f00e900c1624940200381205000041c898144510b02c01002c3d803124003900c22118507071305075401644601042c07000324041201c0006040046010b40542c620903500034194504041c20045c5609a6190440091040c45020403160300582c45948003090340080c017100641c3e5905111200800c2c1070800303940e80300307004d2034060140500da4034245140351140091a010a0700d50030600044e000b403007102c078004c018500d025031510414000c58040d000d0314008170580000c0700c80c420103058039900360400007010031800c1c900140c2c0244600000d010b50500442c4e1030040315484075540012580203800040100d0008001c200c0d0742c620542100001e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174977643 1250 174976393 174976423
    0x105060f120d0c08120103060617030306010e060d020408010f050103020a1707030803060a0914150105070804050616080304030924231606060f0905060d0f020303040905011403 77
    0xc41c0d48404111a101c6441103000b8081044411034002401000310545405c0c0343d01801302101541c5d00e1500c980100694841c48036500101c2a8000c044100070060303a00c51481a107031084140c1d0200204140e5920624441c00115400d01001c03d00b10405d01c2900c041956112000030b0550460040100e41811036000c00c030364800b42000c80382a0032001c01d80a003160741c40b0003007580b261203080000d1200c4860303400401a003403a180d000303001140202401c40c0110080c009918004440cc00119034611174480d0160042c402003008000e1410114014610000012030101000902d5a25000d00354000c0d10154009204034400b030110809001385550b0208031040002100203c01c100030301030310a005440e01d491845000c0242c9010710042c02c56910106a5000c038008086034035001d4001c00950140c804807600800002c2214461446030b540200700042459002c0c4046559a04020180040898150005000000d13600320385004281c06025107064018450040c1c109041c5441d241404c4460 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174978893 1250 174977643 174977659
    0x30304031b03020a02090a020304060b0301060b040608040f0209160201110909070c020a0302060d290315070c150b030d080f0105010e011103040b03061e030d050d0b090403020105060f 80
    0x9400048030405030040405074039110401e400c003a8203242c0d0300c0001a40214000e03041244420156005510440c4503e804009403000c0c00141400c803140d500030302c0c0c0340d400100400d000c0356028040c0c01764002d00c2812850340d0401642c1c04988141c4d0103a803a211050130600c2c0c1100240c1d02801144c03043c1d010490080d0500c0184800030700e0940c0083c002d007040c4580711034028155181c1406080140d500505655564030808107880c00402950a010240340224094503030070310780030041d41c55450b50050040285409041010550380c0780502401d00340042ca441003000560710381c80c24001e42d001c0101c000703070b02d00c149000d2500700803840000104014001c8108000040c26000c0f440c1940d00a203002c803d040314513801626008064049581030384004100090501004401584116400c1d50404405e05000c00030f01d40460703000800542c16006085221010351144c0c019140c40581c83c0070120340e1604007408283d41e00011745081d001070f5120b604000444c1801003210020b1802561660 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174980143 1250 174978893 174978901
    0xa050c10090602121f0320030604200603090a03050a05190302031b03061e040f0204090903090f0308090603060d1a150307030809100c0507060c05071a0307140d24080303 74
    0x51031038080c1d800001c1a50b200c042c0c7d03004040b031280a25540c01180a0111103440c109030a10010055240008004406040480d50b4140c04c10300e094902070043c000041031103c4032a035060790943c11642410041040620031000c0e44200c03030320f0344c03658414141c4006030741e402d14964009500b0701e546d0820000040c10070501801e510703100c00101c40f00c035448852009460340d181c0054040d1180c2007148005500210b00407a140c0f10a80c45140858881e0b00d074030300704a54915128101c0d81c010310001c3c007100d4082c0315404503400d180e030085a00183c001c151111000550f643c03420105000210030040004501c01c0001039030010352004001d44c411401040403c1c90f40d6030348040d52090041c2240502440007500d09201e0182c6000018540d1000640e541e458a411004020803414441a0b60b244290280090325101c0e460450b1200c05400480c81c0c9117940311041540c083e261101c80e19009101041090b440320030034070803188100068001510300c039249005107002c3c0d207140e400443c0550404c01c244 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174981393 1250 174980143 174980191
    0x30c140d030c02010c150603210806030d0e0f0405040305090310020f040902130801140a1103010f030206030405070f1401030e0c0f01081b0a030b0301200a050c1009060212 75
    0xa0402c640c2440c20540140d26450101080032000c3c1040075802c0c1401004400c0220240d00241585032903960704c10300f008140c80468031040281c070803035019008004428445489900141182000030388102e10030540500031904482c2c0c1140e00383d0000c2d80c0424446000d1409008201c1c00c801c01090030f6040600208082049100700e02ca442c1e6000e0b0f001444e002201c42450140000b460090b0003001180400369002d500101e007102c1c07070301c90140703404100100141c443c3e0607241619000c0c2107401c9400e00f19401e0101c60b40c00500103444034851014009440d0383e1000c60303080a03000361030f03080b240525000005810385100c00d07018035450704030032030b908001e031070700c5200d8488401c0908e4013521503107070315005030f08070842e0540542c511100010308028580e0036030004650b00d00158002c0014411081006a4001c5030050482808408004665200d0310500282804070009030076603942d40da01e0b01404e41180c0001d5005c854846c0c000c200c00e19a41c1d1740c03212840e800116000106800d078100905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174982643 1250 174981393 174981407
    0x910080f1807080f01020301050109060309080301050607030c0219060207050d051c12140114030f0606190f030510050f01061e0509090720030901080610020c0a030c140d03 75
    0x18240032840480680001d05a04000c030703034010074602c0159180c01c05400700e0b45000c1d60003402054041440002c0c00940c0d94070074270500800e6070f00134812904590802007080200da1103070f10140c0400c1414174034400940e0750380d021a580010314068003040940b4108019040600f40e501c0710344034410b00500c440116001245250000401805146510034200c409491400f440d88070400c07000d00c2d1a0610506010002010b07041c2e40070200030003a492540301c00c041e520010003503e52403540004003c1021810250740b03088020301d440b204030020f182c403003100d41c400918070b600543c0d659000d410b1042d030407809480345640018004250003540d6040c424050034407030b403c00c80868015410080040c0451284041c0d40c02c450004001c60024208248002c000403040d01600200302ea50009008001c500002119402c11043c2c40f12a21580e60000700451851400070080a6001d0030220038001c2c0e480556581c007461240c8426140c02d170900990111040c0608074490080c4108480c0f400400d40040c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174983893 1250 174982643 174982651
    0x509010c02010f0c091a0417031312080d110d0207061a0109050a1e09060b03070201110301050a03020d0c0e0f240d020613050301050a060311030a0b1b090d03050910080f 74
    0x205180f240d05102c0c00001c6c80d481213910035501803004480c414800311002c4010241c0d8032000100d062601d4482c2c010300c01c1c051b8012401020107104002c403903a139055941007031220100c80d41480c1d05103c100d04091040c1d901000c0120781c113660304c000707041c58403d4240c8200f400e40c80070303e0099519401c040106040760010300400d041000c030519a080c1502c2c180e0038001c06045002c1d024410f5584c0e03803e1001c2590401e5840d6400b40d401c240921a542038144145d07412070707a005145202c035034a181c00340640c2c4c04228000342c07094030000300d0206440c0d52848000740593304c40b210104080c9040340c0f201003040308013442c2e0442c182e00b1603c84900c9903640a4803240258040b180c59a0b2038030080c80107800240a940203682550a00c2c0801088070000da10640880b802404000d15407150481010340b030b600054802040344030001c000c00c144110740e205030f80100740320f103044030b240c030005500003120207502e840d04500181c1e0004103810076092004110b80e410350305051071912400e05124443c91104018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174985143 1250 174983893 174983909
    0xf020f0406050c19060e0c0409031407021212130803040303080c030603011803020d020106080715050f04030c030803060406050d211701030609060e0f0c01050f09040509010c02010f0c09 81
    0x4103800301c0c0f0300804c0c01100100d0300d0316840000414a0351400b040600b0071049240040d0007000c0c1d244440e4149802810f0341d844e071607507400b205509121281d848603003107110700713a800480808200240100c20803da403140c00280400b942c42d120039442c03e071030300c0581750003406050700180800c000007500003084a80141c1d05107548da0b1640d5540c40843c1c01003503143d0ba0b03004280c50f100700712803e068000c914607071000e116500900c07519441d030400030b6884610344104044122890b240701c1d42d2512481c082c012030071402d18420300c3c00c1da5039203c07042110200e82064910a10000c140702c083d01d0107115400c018002901c01144204c815100d0b01186c298a240404040c0c07079031001342462a02c15282490b104500d1b180e001015612030820000a0880900460b0614540f40500c150020001402c1481c031400b08000c1142d0610500111800c1e00401c07104c8070100020700070840156a0342c02054403a241080c0000390705400c0e45002403c0d9981000c1300c402c1c00b032501e40c0c454407080c0e02410310800d94081d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174986393 1250 174985143 174985147
    0x507080418090b13020405071112030604110c060604060f0806070c140123010e092e020c0a03080f130b060a12120f0806010522032003010f020f040605 66
    0x40c00040c0280081c10b800510011080042180d0100c1444d42100c03031030b00a42d030030821940c0c1d10030b0555440840a002e12856803118001d0040102048015a40324101400c00b1444801300003045050b0341101c03808982c00e400c540104215800e0130702c600d0000380840000d140d0365515042c022915020083c1032a410011903450210500c00075510149440702000006c0184c8590030760103207000401d42078414209030b60600001420580103a0f514065001c650182c022002d660001c0b00c0d50402a003074201c0c1242445044051040051016100310064440902040180ea2400502c03104001300740301098100102884030101449420040c4140d000011102c41d031603610002c0ca504c2450303404081d0303540d0034404400c00c1240b10701038141d80b8000c0303444500440c05544c80944e10142c04464450006005205c203c150540041050003000caa0715840e158981d140d44902a0307086441d4803218010078046900c00081c1424841c0b003c4904100301c01714241400002d401d18075200d0741c81080c0c104000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174987643 1250 174986393 174986429
    0x3060405060a030c0b070201030f0b030606120a0f032601060e0f01090302030601031a220605131506080d05041d0712240902130e0c160503041505070804 67
    0x14040b03800d806150802068940c8940c0d8a00c1c0e50110743c44400124006414050441c07440d240c24044c2d101c030468000c01030899955070f40240310100e034102c0401507552145040c00c2000c070724440140303168a406507580c80801d5008041c803000c40c1070030906039401c480d00200100f000e960b100008032094001110410071003840b40700102c0710040240c0000e0742c50701a14000004011030320410620304a029140c1030700c9903903010085540907100d145683e203281c204840c1103000030760a6201650000481d514006419440e850f0380d06403545509000300c4441e80c1703400502c1005001c00c070f01200c000941c170b8494038082c141180c0308040044038081c0440b1800b11004954a20301408600387d880c81030107030420801072407003070780c1c024840c001c0c990441e0700c15143c002090b02c0c0b0890084031000c003441115502c80602c0c01501c4520014004c0c16641c00c1c44041c8a00c405002002c200c5a485601940c011503c03141017003449125000070040c00000d12104100d01400100e140007510200c030b1402100401402e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174988893 1250 174987643 174987649
    0x21170604061e03120f020604060207021c12020606030706090905040501020c0a0303060e132f04020a0206060312030601091401030204120308072712020f0a03050706080703020a050306040506 83
    0x286400c56806044a030402c080050071040504048a00580c000140d24220071810380e0546603031805a40181c100d2000540480c03903d400074251240b0140c0211401c0d40300080c0700030701d8075881a0441c1e00c00b803c01c1c0c10741c1038168104801508000124003a000c95032800c017000d403800500d03208900900342c40750001800d00c0030a40c1641c68103c000d90a4508140f228030300180109480e000344101c0c1a03d410101316a07a108503400c41040d580302c1c00007031140008207004003854440d82c0751a6205080503002c501301e92030394000742100003540c0d0020103c9040407020542800007041c91000d42460600c100300191384d100494508846601d05d40c0304148022030700480c040d1142e50000084a0703c40104401007540c0091101e11412036035440b1087c188440f01c511811009138120000d044080c5401408051115460f1640343c070310040250000808500106400d000300760f01c251000d03003104404020280d00440090751241c440d2a0440c40c180780a90f026001d400b01910032805103170f583c80055043e0b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174990143 1250 174988893 174988901
    0x9060402070c0305030703020f1203010512070317090906060c03070201111221061005040b0a0512090106030b010e091506030c030a0b06030d0e0a030807020a0b0703090321170604 78
    0x1d504642c14400d01030312400e00c590749a01461003100140310301c4c000d904000300042080c0c8403540a844065180d80d00e00010405103a105000400303850003031a00010005030400b10b52000080d05040a03600c8a0038141008440a0000c004034000c03081041003605240d404412290325a41c2400d0070b505031207101081c20b1910b1150580c03040c103000000b901c0c200e42440500e6403103280215000700122075503103005100d007031904030300309501086007804280100c822160180641805605d052030030705150541103d2144015501c46100e40d660f00307418810310441006407409000b0040c003280c0d02d130800d01e84041d170b10b401c114021041d041a0345c0200b085560309120002060350b004040390003981c000d08154841c82c406a41d040d1086c4243c404441220f80220607072005080010428440c2074515151100e440c0e11404049921078008407020030304100c0400a0110319022761b96070b41040b421443d000c031842d240c0c41d40040864540035180000c982c0d00c040891444400c0003100d9400d91152404200a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174991393 1250 174990143 174990157
    0x60c080c010f052203140d020d0501030614060604060e090c04030b09010b1c03080f0901110a0201050a0b0108010e160e0604060e100519050703180602160801060b070209060402 77
    0x15420075221108030b006a4201d1402604082440940d611400c18035504114a0103401008110070004001400e10050090440800e90010162400340041c0d81c1c0780858909070000c542195955501d22203016044100580c4a141500c8151a117400c018000c1e02c08004d00b14090320503200d40c400220085a15000e45005560140c0c0304041410000c200602a0503480c5006000d418030081040d640d410700305607103401a401d6103c454080d01c40140050007403000a0250050399203a070b8030f00c4841c1aa610042c4100315055000154074142903008000b6030f04104811130401800c007006200d01c035143c105180c1c000300b00c120060a0a00e05c2c850695a080101d10020fa0200000c1070019a064000d0320740c000a030030072103504410508032881901d4501880403480040303031054640c0038100780590000c00015000e41450421500e040c964000ca180f0290080310041c0c014000044c2400c4030000c4540251203134000030302003141460b090140c24090942d000c0c1c480c0c4441c0c0003040340c1d41c60b03c0e4115080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174992643 1250 174991393 174991417
    0x3080c0106090c030209030d0207150804111c0501050f060a09020307021002031806091b0d110a09020d0b03210a05070b0103080a110d08010308030c0d0e1c0513060c08 73
    0x1c441103c80004c3e001303401000740c0c01c0c02402500c000d080c689201180c10310584041c0c0f290700c20441c2102c0e4046407211001442118008080300d0340d2217035542e0b00c00c000b1441c410141149041e13002a4038019081d0b40025000614060b0620705024036540c8055003102a5401d8040058480d52211002c0b898036200300b030105200c034400000e000e440c00401904810350221a404c07245940c4500f03240c1c5544540c821000507090740d0184450516140107281c0d8841c19000c0d40101425202d1400011550280307075111102d150740c00112a0450f445900805901850440140c040307105c1d03010340106400c8100015103482a00050301a0030039010b40c0580e005190000040c0c080c0e50307180d1070032510b02d030301c400700f4030021510412071184410760010b115040c050b46c5a031080041c2c1d18654600c1c02ca50409840065910428080306003010701511a582d44062084006c102050160080d107405000101401c0700b000b0b000c0060198003c0c04103111811103455140a6568001d030b0b00307181c04540540040300c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174993893 1250 174992643 174992651
    0xc15040303150b040b0409050c070648030203070302071406010602060c03010b0d0507110303040b2d060d03140d0f14090607030c022113090e060103080c010609 70
    0x24164982e000d0200c40035100791003001d490b120f8054070314600903481000c10b8084100400d10921620f900400c2d0448024110141494840d6803140165034108031845201115030310b00a84a0000b5000203203c120290b01c400d54540c2500349500040344403202950078190004041007644e8801d5040b0b80000d6000081079000c803030725504241d1610000c0c03081c50010300c40c8070085070121084104980c1203520b500304c541d00c0c101752a01484042e02c8014016402e00c081d00310760003050b51051000314400d51160f2130601d60740c50b008141e4550b0800f040361210304000130541c055450140c1d000003030f400c820201e424040e0858a440e080301e1a51400500700c04140020039442d180301441c0c0c21070200c4d04020101400014011400f503030500304107d820501c0365000700003003910341e0700035808503641c8822403040d540020403160415440503d0311215003e400740000d49000d0400310410120080c0c900c40740d041c840c1410300c44019a9540e818000a091071100042d001c144403c00d5019500402c0f0700d0768140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174995143 1250 174993893 174993901
    0x1e0311030d0212010f0b04090b0a1a190206090a020f1504180b030309010e10200a03080f040210050a0203070506010b040504151514040b0f0316080702030f0c15 70
    0x6000e5048182d04450310f14120b80081605c42c1017101840035074072524201030400d40342c000d44601409100c0c00c440d8001d04800000b1030360003068404841c40c0f950300e1080c5aa1210681c4421003400b20b03080540301150042004e02082290115551400c3e54040744d5050030b2a00c084001448e8034003403920709164aa00080028018a40544036901c0303242205e0208107880c8160140750301c0303201e50081e040c00104125110406807034208607450380c031001e6161a160346c5e2011114440502000840000300360b100510200030154402d0b50313035034032100d103036464403003070030641d02040d14006241141424070201003414074005108200f0b68003000d402600321151543c0d2240d001d080369006d401203e000301e090920001d42c01c003083c01d00f0000c403040000c50307a66030100064115085207406030341c2000594104000220403005101403d040000308103080d6490400c0100e064001c40d20343d4405090080d00b1f020460003c0d00401510318200c000901581d4038031b0442a81c1e03060088246080c03501000c00d2042c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174996393 1250 174995143 174995167
    0x30c330d060501090e0907031e021203091306181d0607080103020909010507090e130203010203040b070314241c0b0604051e0a02090607050a150b0603041e031103 71
    0x4002119420b8840021361030720703851007004100049605d010242e20003013042000030b0112030425020390000c0c10651451b4119030016000040b01030303001e24240d10100302c41d00145080e6140d000d03e01c8074002d081148514004c04140543c008840d400c14195685002e046812229071170301c86440200010744d0b07114603204501910650f000c0c0010303400703134a4110000301d4034181440341d00e01031032050715040201c1e0300d816964109071000600d8124442001058034005031024000395024900c20070180c070711450010703001011a011050707240c410880c00e4051100c4213100c0c0d03020300200146025040d40e100c036980d010500c41496003243c0c0384103252041940d0180901400c0040c015a030441e414400b07030f100d583c0c60301c3c8020b0807903c038400c0c5142e00c030300464a50340e415402842d1040c0080c222600700342e03840c1c40b12402d15030f9117602501d0014881d002c20b0480300c824824030214503c110b035501e0850510340c841d4104150250085480c0b0b000a12082d003d1501a40c080b40f6444500e03011030b40d41d40c04a1040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174997643 1250 174996393 174996401
    0x21090c18010e07030207021e010e030304080609060603070b072901090b0f06030105012001240603110a0c0201030905010e0f0a0c090501060e10030f0615020606030c330d 74
    0x484107001500c401140c981c0348203008442d03005400402812903003000b0423080040120400c4400e043c004104540507141d101400a400140142000b900262511a51007800d024004190030b10030b8000007803d00c0011802e1080d00c120b19003200b40e840007400c00c400002d0f4861a0380340034000e4809034100018501900e03030094000b1000640c0c140712050400e000f8071150340000e00075140491100071030031000000349880407030601100780000c1003c2c8000b0717195651255910b0380c4c0c001500e000036810b102260f01400340042c030361040362180d89025040f0304020f294100014000b8101915801e110080c448250004002d001180e81030b1074003540dc4e203580c19520b0790b03000300854414a0381100091100300c48d115090483c0e5154582e000200f040004118048910114840500d942e40954a44428081c410f0501400d0380449441100010040c042d14043c0c1c001d01c42d620a40c013501040c400d07512190240c041c8264222651050849000d8900c450f4101010007182c030540c01140b4a01d103101d013900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174998893 1250 174997643 174997649
    0x120d0b0d0c14091033020d0f050c03040b310501031404050601050409051608030912010c0f0e010201270b010501080f0606070201210e010b010521090c1801 68
    0x111418190450803c0c0f0a04a404441113985040100000c101c0e2a010040810041c1c802d440c02c1300d00302e8811003185003080500c41030400142d01c840000e9801a401c01d8248004845078142603051024503c00150380b84124060280c42d0f000104041590880b541405400c16800001404980503546210714221405120b8a03000909003c200702e6030b0000c003103956000355003110160403070b60700b001c09100c0988900c400860300e503c11035070024480c1e0464074500026080702406035640741c0c84081044100d41489005024691501e0b40443c4010f0300f1480002e4018070324205030700740d41d10a1006078011700c02c0b20010705d440403516900b0039540850b4607800f01c040c0d101c0c04500d81c560b600d40004641400c0200c1d0800141c2c03030306101007413540c0781000241082610516007004110b40e401c2a1100e181f08440e40688200c1e200c1c408040080400e000b403103500c040c01c0c030740039051041c1040103020119195034000042d030350756004038841803005d004032501034001401d4285440f03170079440301c01d401070244 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175000000 1107 174998893 174998909
    0x810080712021507060c021e0606010e1201020c030c10020306090a090501060b070b07121506080a0e070320010503070e0f0f040f0204080f07030302120d0b0d0c 70
    0xf50000c2c002ca512448001c9000500510042d03d00b0480c01248800410400c0542d60b4410000801030b03488142481c0081c1c010300c82038041613013241103045440b41075000042d28282a0760001c010b0280000c40c0701110380908440c94500b04900042d2000d55000329030f607005c140d09080603080040c0042c00b51000190503951070580d4040740d07015000445610201c1c0080115880e0020900080c07615021001d0008440c4001c00c1180d00c0d0041c001c00d0b06102c40040413607800710169014016040401c8200c41821391a4217190810807409035031424400c0008000c5c17201c9500c2036081e6400394076951078421400584004000b1911540d440031038000310b015400715055030780c074001c020301044040001665241841515410030b071503501259401e0340030b4641000041d40c00680209040110707004280c44030560801c0d0400f800001002e242e001d50411118024030040c2d291300b404a50f049 = true := by decide +kernel

theorem cover : BRFrame.Cov 174820143 175000000 := by
  have h0 := BRFrame.cov_init 174820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 174820143 ≤ n) (h2 : n < 175000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
