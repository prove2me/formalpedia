-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1885
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:01:59.193037+00:00
-- url     : https://prove2.me/submissions/358fe922-cdb1-4b60-9312-8e077c60bb93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 338848920 ≤ n < 339028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 338850170 1250 338848920 338848927
    0x170f0f0411011e0c0203160515070f0501020a08010806070207031109180717010608010203220f02090c1b15160203090d05071503020a08070f03020903010f021b0f0601050d0f0602 78
    0x40c640c80702040d000c0f45c1c03090b425541c682c2ca11070b6110269006a024007540326080c280074100c020040c034040d0100f140a00f48100c000c1595031203450890344a541d1400010711001c0050040000400401d0740101561005000480c40e45e00d505030394a4515a6480c40345418401049400c14600f0441c0000086c03041a55046030b40c0e281c0d11800142207014a11040d4240b92000171000018402c0c0c0c6c0c030a01d144000c46802e2002c0a40ca041c1860302c005007103400506201c0780c030001d07880300d1401607c0f6020761000f42c0c1d03403121640301c01c0f42015010081c45480c0d61121110030440b407842c40000d500107105201e22075401c4090301003a41503010320031000741c00c181300c9070715482130010002d8410b04603408039512203281c4040300d104405078824059a04045094040446d00092180d00042c0100c11503140050411000100090a580e4002003a100803074021a1841a1b1002054000c1c0b10020103002460034440401401c0c0e01c0349030520030b080c401c0749813001e40710600043d080b1003240aa0b00c894115603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 338851420 1250 338850170 338850227
    0x8060616111002160e0423030d020d060f0b0702130c050f0d05070e09010e0403180305010903081f0f0b07060b0604080106030c090c05091002120703170f0f041101 71
    0x11364608041e8010711039640e810001035182c00d4854050b0007207030007540305040c1c8000380e803040c04654030008440b04984010003a804403016030388041d1500304110034011654078501121000400380e01c2c0c1001c210320307100704940c40040e0ba441c200d28466541402020079040b076103034820741d0b0301d00945121385550140010003480e000e44030341c8040e00c60401600e40309004800c01c014010806000d02602404015440c040f5020078007400c005e00035000071171080c1c490103131640d5031076096443da490210045101041803100011260817401c45408001e0304910700e0b6464104041d100011510600c211114002980e205000244e007242285a4010b8151070b0740319620a0110300130b2040d40320559161045001c0452840c08070300429642070b019540f100c5c03c0c02c42c68804c00c004d910701155244103500c10f03841d5111000d01c3e500080d1034410301a80350a489040040c0400e40c0400c002410a8544011641040134962a003000070385c200303800c0542c1864042c0c02400584080e498030583d00c030030100300d500491 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 338852670 1250 338851420 338851423
    0x10e0f1309060f060e040b04080903010b060c06100605090d02120109140a0506060618040b010e0a0803040611010b010f0f030b03060a0603120201050609150312220608060616111002 79
    0x41d028070740c0580c01c0041d40e07a100301c2d50205d404145c1d4018400300412001c500030a02c5100a002c15102c01000014241071010024400e60702620440c8250381001c4100112591101440c000030050380c107102d03141481090004d40101c4103054000e00c56088030380f00c030910729002d42c0030502c040e600444d00c00c112100304100315501d04d0300110449a901c603000004602c0d0a21405507910311181c4c503020840503da9604100c06094803000300b904101c88003041130203580d82d41d0302140041c25080f02441c3d90b10b04201000f04402200040762810b40c4c1441c609904590b0b20a400d4281c4000d54030381046503403556201180034111030b09005a041c440c030824403c3c8a1001d07407281d82124481c000d10044410081016800e0326012203c0344e42c00540c0100107900d820207082e01d24466500117003968035680404a001c00160010350700600c00414015260050541150300d19000d0841c1c0d0500706540c4c54480300084003882100c0e108501049034640031420028032415255424400400424010b858107030001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 338853920 1250 338852670 338852681
    0xf110408033406110c15061e130209060c03070c050117040f11150301090911220b011101050a05040303110a020601090207081209030702010f0e010e0f130906 69
    0x80d120300d0800c485410340b0355900620400d0180b0042244022803580310840240302500100540340e000300400d0383c01403001d00c000d03c5c0d10a8488401c603003074107040c4140440d0f800008500c040c45805041e03052140c1c0d54003400b4401a00c041080540e9485100010442a000d0100218a1840b0228400c010030040c0c400240c1a02d000b0b03a5440c449101640003000d0105066401820030000310084001043c501e0046e00c100c400050450502c2017404220300003280e100742d0200c0c146a5a98120700304102050b403000f1848242111603040540602c81e2a051003a8100414520b040d035501c0300c0c2175940d0003522a80c2c408184213008100d10700d0402c0e40f40029000031602200001e2070f04464003180c0c0300e65420f88100030710b00d03402819142c1c20204100001e5000c07520580c0c81c0001405071202c4401000901c07881400080b000d1a01c9000d00e20001d0300307601003c030841050110013401c010b141d0343c3c041c01d5000c92513401c0300c4512440b041c803404140420003a0050061031810a0b9082c801d000311034014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 338855170 1250 338853920 338853937
    0x90918061905060907170a06050a03050a02030f0c0102060a0c17010605031b13060302031005030316120512070e01120c020f150103020901052205070809010c0903050c040f11040803 79
    0x41c03107540e455008100c4130980c01c64019001c60150340c0300300c00c58082481855404111b00400240c07581c0c480c0c00060b03030052550b00c00c03122541700c0c0615204508040c0100c1100c0030b1945e00038544800b070345001079210b6400800740310351244d542c0c421a00b030b540305030104030310044402e018102c5540c64400c0100260f208407242d0018140b0b882070300464007441012210920701740e0001134491420018210041e40c805880c48214030110780d0f01103042d070b03010300061413140c4480394400b0705031a03035260003d00816500d4483c07003482000c2c40000400304440c034203103510461a1030f111810340c8903500180c0c0c00d00c0143c140d024202d80f920708401012031300043d40044100105084035801142403422585614090100940103000c640042003241441038071080c80700c00807c181c8908904110319101200c1c41102d100c0d0004036860305101c0420f40030700c03441203a24014500720030f0711800c3d52039031950750025040e1603000b25500c1080301280000b030ba00030030019075803c075131a5035680d64440e02c0d0b0ba40d401c0b0302d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 338856420 1250 338855170 338855221
    0x19090309080c0901050303030c0f09030304080706090e01050303073801140916030c1b060605040b0616021003060f1403240a09021c031805010c0809091806 68
    0x503200054a00403222504a64000b4007e6286d40d541d80040a420b41007024021582c85080c00b404e0b8450b48e00744040d0010f045aa00100350451030900000d241c201c240e0300c01140380c0b1a403001400700e1340f004802c030fa040c503800140c15260342184040c140100c24480c0690001100c00c901c03180030120031403c080c2c1c100d803c01e810b441800100b800402030410f20585504480d940b1801c40949101e009400a50641c0c94030b043c582e01070302c980008002d41045201080b80c1d055a039036024886480c040c462141e95200550f9241e040030b8046003501c01110780c43d0340c003038402c100050414511b503202c1e0300054090030445a0448401d0750340d03012100d14052030000d051280c000d512070b104102c202055407414a00a00400c402d003520b0f980d4100303005018400e0160b80001c8607044a00d000022000e40100701ca110355200846000c40220040c07242c03500d41c10450400201054580100d401001a9103420a0803074420542ea224003440c1c0810000403603036440303240030381010445240c15061401c10344404064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 338857670 1250 338856420 338856433
    0x303051b1b0606010f0c0633060801140919200c01050f0402011403040f08040e06010306090c1d0a0e040b04050f01090206030c07110a08010e100209181909030908 71
    0x401500c2c92242d86005c1c0d000a980c6a048030701060303150700715405c3c00030614901e064603109217941d00c0144002d44079a08189500f114200507096118140b9801404a50311302c140140350b14000500f038174000b4000f034080480a6044211604503980060381580d031002d8025260b03a041c42d103240c031640140f0f480b100e855107004001184280003280303c03449294140d60303d20051652418162940d0409881603440700821003420300060040001007000c1c03d448500c0b080a442e0520004040c1d800030380010340303071908049229489a4105484151015000c0e1203c0512415040402c1070002d44d40e004081c00401502404107101035290114000d50285054520b001c101500c8a400c2c0ea402c0a4000c0d0010000c0000848000d49540031300340c0d980c81100002c070b00009080010744c0c400e1071904001c013165075a00000340050010040320505d1051070b0402e40c141754125001400429403500d00003100318a01d000148000c41d2405040403014010b8010440f000c400d0400801030440c5000e40c488910410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 338858920 1250 338857670 338857681
    0x703110f1b150702031e0102070615150207060e2b06020a09081b040b0f030f030307021614061e0a0c12030e0a020f0d020d05101b020a0303051b1b06 65
    0x403411a581c3c180c015000f007045e42c0c4602000e103444084250000d82c655420300200d40050034a0094107184815580480f00301401c0c16488514010110400760035540411410802d0540002c044410740078226003450400e0f4883d44514074814140440d001c03400c0d2800300203810458a68003a07c440d6146903580c1800c241c80b07800315130750b0b602150001554190150820b580700c0c07800d60002206401d02500140003204034201107072030080205540ea00f25000841007224407541000030384801c42032410000d0000d1718110300f2101d080300c0e843d0114002c07040028050b00c000c107600006c000001c010708401d1780c1c40654160045c641c1035290f40c00c80d400c0d204d03200d42c0b0b4050b601c0f83c0100c059100c01d00001e08840304035a402c00091703140403001e4a4002c1f1a070a00b0b48050ba403001c001e8a0f295000c1c1016180010b04040724004a45000c44800900003600702404034081e030000d98400c91560500380081c498403481c1d405000c2d2004507041c845580000211030340c40441c540742001800c00300c0003c03204a6100c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 338860170 1250 338858920 338858959
    0x1b030b01081e1204120f060203040b0106030e010204060c020904030203040b03010b03060109120203061503071503020304051e030a0c03020c0907111002160809061e130f0b0703110f1b 80
    0x4803144298003150611040c06001840c88401c2c80c850310803040306c460410b4994910003a41c00403181600d00c220404c00411885c0d806004d01045407290300000c40c03519040c4100a400c5918000001e8010001c0100103410103000704109c8024003400c0304016140d40e075030841c007515640212031840c00100b81e002e000500501018004500360781c0100541001d176681420060000c1442e90003560500c2512400035403035000b0b003040340201000380ea0140e900e04c0d15007031091419005001d2607000030004107003900d404c1800b0050360b4000c07040e450010001d1885080032440c1c0310b600c0c50740c5071340080d8140c1403082d05500030004d91181038001e02035030040e10020120700f080740212800503000368a551130300c8001851031001462181c1004005504010081000208065417100c0c2601c0412000950102c045504e1604000420b50300001710b1030039003803141e0203c0c6401640e40060a1101024440341503c0e0180110303806094588212004007043c0d01012054441d0300541c3d5000e82c911001b0300200c0400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 338861420 1250 338860170 338860183
    0x24151103070809120c0406260a0b0c1324080a0c0f05070305120a05060306010902042301020a0506070302030a15050a12030212160c090203131b030b01081e 68
    0x400034041801c0c038580c0f0040c04451600310480c6540e50084601e440503542d6540b03d132202030244007101d480f040f50300784120204c8122044800c4c02641c000f4121a000031000220560b204605044140e2a0400d900103010300c0c25031038100300007070018140c86052040c20411601610452665445416202c81071410200c600f541400360000c7c0498100510240c0500000d00f40c592003071905507c0c3c544640305040304004140e480052860315a01400789038078007082101e000d0b2600200440c6003a103007480070301c3c4c04800c80c050b4142121141004a50a80c02408040710a40d040350039070f189403034065002402588202d64462581e407420b050f1464200e00c041d01001680c102070724802441c0c1c10711031015500c90014604a086100c1c04a00175907404194000d0000300ca40b0302d00c810f2440646143c4020366035850b40160905e00c1c414401c000710740c10740e2010a80303410781025201108844418001c41c003c0e0741c070303080a003059820100004103900000f8040100025428141a070094008069501c074103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 338862670 1250 338861420 338861423
    0x115030c23031806090a0c0617010509060a0909060506030d03090807080318120a030b06071505040201020102090d080d060e010f170705130b010216182415110307 71
    0x20308081e0007000040c80401590070200303081c51060110f031043c6103245444070440700c01c02d981d00045000d404200d00c00c01400060b294600f0100310f420304140b403100f5024030511840f480b81d803081010810645a90298001611000c2801c0c01100250b040400250000340c40d100d020b48255a000507405200344901c01c21598082081ea14100c01d9031035060311908007a160300902c4030101400e010b0508204408440714840006940d00c030781408501500315140c288a01d40510030410442c0000341c454114038014803000031000840c0c0c0c40e03900041f802405181a260307002503c2403c02c80c28400c0c52005007004410864013840f40d0341c2ca07241881d00601080c4640151554580c00900c400c881c24500300603503481d410100c81c2c0d09035556000070341442c0d03400030920300f03607a0343c030014681564144000004e02102010041d04640350000c4007500c480e403a05942107441e07032580d1031315601d00440180d082c060b010b1003055102d83c0d141d20455030358080b111442404180c100c10030b1841e1032008030a40313010303d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 338863920 1250 338862670 338862707
    0x30905040b0d080f0909070c0c0902040e06040c0c06050c04091503030c030518090a0c0e24070302070f08060115020f03091509030d0f0f02010612170c01050115030c 72
    0xb4403070b81d070302e8181c1e60304031000601c4543d00902c0350308907985919280c60301c50a10303070ba205500560035040540c000c4c0d4554220303008003801000107211a051500c500c50b08910180c400250f082040f500803912103840180042500e0b0030702d401d0098141d0303105d0250040e01c1004004000e040d580d10704141203461a8800103000c5845c02a03074402189c0079030040d00f0302c98420404241c03c40a248009501c9540844010230610f640c0d624090407241d100002c84140082076a04024000c4210108008550301c210000d004d041e00191040c2054400c0c460300c002415150382040306903450340e9400f910b4180900424501d000e1010542114502c000740007039030342600302d01561800c4070080c2440462500c0b100742141c41c0108104882994404010608951030107a881c1c00700b1449184000b04036008120420f4116814140c0511015280c5c28030f070f124062780b0400c526000758010000c2c140500031079081c41e200754608000001c40256403032418182046079a810440c60348262000e4402400c50300401030702 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 338865170 1250 338863920 338863939
    0xa0f1a0f0604080d0201020a080a150306020c010b0a080102040501030c0f0e060d0207050d0e0a06020a020108151906020705090705180906040f022803050702030a1d040606020109030905040b 83
    0x440c00c103081082480c45015000516054a824036146480b5a216030036005079400624115156809005130381c01400c0350400340a100d0b01c66900b800213441c02d00010307118540c0000c009034210350950002c0f610311400f920303420300a690794841c94001d42203440380d90b0200303040c8641d04c400300d4441c4004602003c0651614000750340104144480c036000042ca01020310360800c8800c2c0882c03420807000d103514141e81d460384040000d000c00d204d031101c140e034014001d41d40300340e401d000142e07041ba8803958807040b0580d28016503045d840008180402000681a85081070540031403000e5000c1400320698a00b995a901a604e502104948521031030342d21139902c08809590b10454980680069040600180007040040065201070b0480e80300c9884480c0c0c0c0e0300070000075200c1c04400e41c20f03e400000035040801c0140340c03082000e0741340e1080032000c904220642184059201142281c00314440c005002004802d44445001e402458141005d0b008105c2c900d80001e424601402010703018800984140072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 338866420 1250 338865170 338865221
    0x300e03042321070605070203010f02030a0e210a050c1501030507170307020a090f111b0c030c030a0f03021606031a12070b0702270103032615120f060a0f 67
    0x740342d000900100d9040d52100d4ad940c80c3c2a0060010303601800c00f002001800b1401e0703501031880c01e2440350381e0b008081c802c0c0765220144e445a40c1960f448441509000782e4035801d24560500745003a841081090b6003502002006220000440e501519400d4105106410340441100c3c1e8074090041d00a60048030b803d0b060040d44483e070001049134845100c0498103242403c01e01d80240c0241140b4601408440543e1503441010808517510340400d901800c5000f1511000c02e4031221800c0d4050301030300344c01750031404061023001403d48a90218a140d0708c96a1100c0c801800b4040400381400c114540e01a940340c0ca1400c2c07002052424a5640185011407816401c0207154100e100c041e070340881c080032a40805c040601c0d0303240d0385158050100f1440e604600d0003a04049140300d400d03030708444c0c1e00014110001c2d0810650341080808028a0200c0800c100007550b145442c00e040e4054002c810041421000014495000e03040c14107041c488400f06124a8040b619040c400c1c80301c5500b240240301d0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 338867670 1250 338866420 338866427
    0x601120f02131b03020919031e031704080306040b190e0711150103061d100b120f1b032805010921300e030423210706 52
    0x2990404048408100f0401800d004010841c2402c00310b8042500010520700c03514041e0354410f0507800506031303040d006086860b801525149007164800c0c10120b030720014107060191840708580c0d001e40304001c20700d02c0c06184c005070a400079200980550306059003103502e03151219803900f00e80300c40c0824a0107a46018041140030740007501200034442c01c1c0c82000c410803400e014150140e0012611800c00e545141b0b04041220007080b500100016031820300c0388107480210b001000300c40780490120f03c204085000429000304070a45600702d218900b030980d2030a4010070b000071448280d0506004018011042c5030300c444020410300d105e214944041c2401c0c020301c0c1c211400407409200001070b006103a036680d20800c0300e003880710f04e02219040b1184180c2c83d8003000c0d200125500b07588c00110244000008089401c00508509019803580f80101c2c101380c0810643c0c0091000189030324440403015208040b8520b0b02d820075003d1484111342d502c802088a60455a400c400401054840d207800d1089 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 338868920 1250 338867670 338867689
    0x6010804060605031009050d0302190c03021f050a0e0309010509010309050c062101120b070e1206161d01020703030804080706050c0405100306060203040603021812010e0601120f02 79
    0x484810b59600e101040c6603c0810081103044d408500003d0168580c0c14014500f18401e0300d500105030040002c3c001800e8a00106c184517186070034004180e80032490282e041440603100d0b15044c80c03180d0b0f4080300c01c515940220780100c030350074070410000400110b400c0d1648070f080c4005000c030f402088201c4495204c0d034480c88015025400381da0580c02004005813a990003400440c156848c0010b000c10000400303041c041c01013401c0121220303100714564035107000c480d00410080511950102c919004d03104c5190462011804030b0969081b85040083c503101030b08040040000640250621000550b0301142100c56000580041c5545480c40e03504581c010310040080741c90681c00d01c2094000b542d6805054015920401d030262103609000c24840000403003401c0030205820440e08021a580100403030b020384c1c40d140303005641d4040310740c0084034013414281d036150040e0310040341d0700c0080d60640c80b540d4003507517640c1547c0c2180da82303401042040d10700940140c408080785980c00c00520b03006500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 338870170 1250 338868920 338868923
    0x109170109120806090f0f041e2102120903060a020c190b0106270b0906040b071a0606040612090c0905150109230409030c02030601060c0c09050f06010804 68
    0x200c1c07105055619012110b2044801c0d0300412109001d0000394034000c440941d0110050348801e9162401070340202c80000054006440f0090098480c410320f08c2e0b4050016a46802c000803007010140e20b0405070139403420702401c000500074180054205007882c2c2c1104ca480e94000e004210343d44404181e08001e40c0f0480340c0082d184101041b40d00c440a100c440f0100d8140100011100c41d85400c0c0068070744141e86540c030808065941c5560380f809110380040c401d4444001c0c180e5100c0d0002c002140d860300c500d070032610441ca800304080b010407006a44511410051080c034150a854010a21590740200c0c01036101258044003410900501d503400008010b0040d4074014082c1d60714030a590448400f51030b00104000c0e9210341c0c1000317580109560004286012104120401000b642e200100c15442e85500c15034460310100c00b031600c0f071071840eaa099002070555046594600c0d024221110741c25003260700c20040b96000a210300ba501c15540705010140c41c2840965032600110b9035610001d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 338871420 1250 338870170 338870173
    0x16051e1b221805030405040c0305131b1a030a110901120f0906020703020a120801050f010c0503070c0e01032f04090510061202010909051015120c0c0308070e010917 72
    0x68042c6401c00000c0800c4a00a4004e556034034140010302058070405007400084c541050180710f8500d818503010010160000c43d01c55912650200c140d11405440e8002031501d9201c4d08840c03084844200194052510b90b43c081007a4146000203052901400720500d010403007800010801c00765640015041c60a620f2001500e00d140365194030803078002c06015001070307000c035140d501001201d15294a407048a400c0c8400c4640c50000011a24910212064100301d0340e80071040400100304143c2d2642039101f60b2640000382c90702121400c042c0d0912050f01c200b1081c6039400c1810712099038003000c1c400c043c142c81a01031891000c0c030015000305070045996201d141001c441840c1d0a100b0a009041c00442030004045c041c00010000c00d01504081082c5240c1024400b03403200b54480c102c00c030b41107030b60001c60a0a551038191100f0440181c00e100340340c200809640485e5000d001901854030a032610704068941070011158040d040310000d01050080800703001c1501840c04400c0c60003480300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 338872670 1250 338871420 338871431
    0x120705010f111f050406050f0606090d0201140a2307050309090411030709060501030e032a0a0614070801140907180803040905010302030d020a120516051e1b22 70
    0xd40f202d00b064107050307020046555182440200101c60080d01e810a039101d0030b20b185030801000041e0a44940000300e807241c5040340400d8210390040070011034581040108684540c0c0d08000601510f000300400d008540f402c03d4045e020618070b000303540c402c6403c032008509040b44902400002c1102800070f855140f18020045042d81c0c08000741030140c11880c0c004103134213207050005029200d500c0c1c4882001d400034030101030302c040d0030412501007030081c0100905100b1110f180c0f07400c1005802d00504114141800780c890f04505d02119400380c4115074a05041741c0e41c2d08a0b1700100400e95a00a070300181c0000030070b030024420440703800c0640e1200c98024a60703644820721072940d80590b004080d4583c0310401042989000d208106036552030b400901240038031660b070180c65985482100b002d00801142d072082c05140e560190a10961100490b60f0b103d1000c0300c08415840c0c280031502d50b610919260048a0800030800a0311000c040d214003003070040404c540a464141e101c10702c1d489035882 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 338873920 1250 338872670 338872693
    0x420060403021915050909040605040807080316020c0103090210140c071e050f0d06150b0406120506040c142503120509010b2101200405120705010f11 66
    0x503101d4056000038860319040c81c5150101300e00741a00c0071002c4409100d0240b040f020261508180c081e40300e5842031000031696568a07280316503000d07444001c4c01904011041011031b0354040c86041a1440d6602103d0306214403030011002c0d599440b800075040050080c5031000c03640280081c00340ca506581400d4100442c038044a0f1a0003d9036000081d00c1d150500d2030192540e60002c8400a0002078441c1504000c0c48400b1802c461074000009040c1660781019020400c248520a40681130846600e5a0360b40c0e5020020144071086900198492412010664500d800c0c8901d01d100102d81c0c655244045c101d58044c410b42e0405201c01110a500c4600e1420b18004201040d80d401d120307171240000c0c3c00200d200003049400c0144440310aa140038820525030350f40c00d0920f815602203401d000510401da454007400740482c911120080041900351781400e20311000030344240c59041c0c81c210001d6440d00c0c00d966550a06100c1d003404100040041c0100e240320f50800c2d00c0d2014142c088603800200d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 338875170 1250 338873920 338873929
    0x1508131212110d0902150307140d24061106060307060f09080d0807090803040605040308070201180b030a0b010905150304051903020d030b0108190c0215010e1e042006040302 76
    0x603c1c444510f503556a0340000451502c05120b21035405040740203410361500c02001f411190580900c6445550b012440d01d8000e1025000322031204000f040c2d404c111000b0410940c140310490150750082641c01810039a501c00c00502244281d400030000c05d000c616040c17003a83c1ca80c0c200c00075402009150f43c00814044030030081c0365a0300d0055540c606441ca0036500c02000e4564603040b000443d0801c1000300701041d841000d8405807034104040d41c3ea038180c07910050382c0d24509428010707032004003d400050b003681c203030010b0340c0308031b0058405002d910003c2004580290207401096800b020a10003504050240d00c05164418841d1044958400351000d0003c95036450010840050b440034484600c40365140c056800703080000c0c00c00c000f6078109004901030541218114070000795458586c07500d403610030407001c80100304007100c444040d43c440f0400340754500c0864203c00f070110b598101e11360222013080311511803500101d4200300750540b0017209005e440442d14085c0e001409000201c0035030784 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 338876420 1250 338875170 338875177
    0x20912060906040b0f0403020c151c06080c0409020a140303130305060a0f0905060612032a1207020d060506040b060a0302090a05103204150813121211 66
    0x81e260010441850107141840060000401c040c40901900081c8400a500022034441d03c41046a0102c0504144211304426001d08030580d0345000320420345d0300c111007030384e40140d06440c12101a0345001c1328000520050b10700820000b500102007004c10404203c2c80301070314003410350050646c1d243c0151180b9003410344000d50015a2260448028851140300d01d1085006409105406220101098407001e0301c2d404000c100a010350040340602c900c82a0500403034800d40040d18103840285818206010070b0b0011640e024041d11a81030240004406141a00d49044c0d0042031050120101d56030b1a002d0603000c1c0000750415140d00396420303250303a950081c00c40041555030040c1c0b00d554030001c100841a1503400540508511083c1c28950b55101c4a02c400d003008058603000b240c2c011100e02a070a9000c00301c4e1500d0a40041004103640d22000e000768031a440300d40e40c82240e40c55560702c2c070140b03800008005241040b072101c4404014080d040510701a407a04c00005140208403184c0c00040d030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 338877670 1250 338876420 338876431
    0x6180e0304090920030109080f0a0c1205040602121204021302160809040b011d010c1103030403061b0305131707020d150608010e0312060a0f0b030a0e0a0c0902091206 73
    0x28811001300c140001c407542440301d4a800301c000781310800c0035865221031032107014400102c030580040d80c81c1845018000380e101c5140d121380005460000864000c00a4200c2c1c06200014007451800c1c2c100b070311025003965014a621242900d042d00c4560070002e05200c407640c1d074200d00d502884107114110080c590807400c940106800f6503580c21510401046880b02c1001506001c01c10300c0e2458031040183c80e4040c1482c0a081144050400d418004500e9040b50805a41440000b801104000444c0c10511182480c0c0d02102460341801030f040d801d661080303c6d200304d41d924131054140408d80240043c4100a0441d580c1841c21a0b9a0003007000c413190500240c40c901c85d44041c0c0c4400c0314543c8103103c000c2c10323258001c01219904055568407480742000180e0780c0c00a017000700b0055600c410110000707201921000744901c4ea101803800c1c080e0000c60341030700120304d030004044c00703120003081039125254030086643c001c600b0404802c000750045200680c110040c200d20b80c4d481d1108001490080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 338878920 1250 338877670 338877683
    0x10f200a030f08090a080d02040b03040501091e0b0f0c0409050a06060909060e04080a09150e030601050f03030304060507031b05090a1e09110d02180f010306180e03040909 75
    0x21100d5090141c404a08a0054010801c50724100b00f0b000f1400702e1110744403540400204c1e40c810700c240c1c81c80c0c00303801260007001490b4800014081000015817000c00491700c2501c81ca8501400301e650428040303c218000703001e1120040000d80c171202d861614691155440c1403203401e083e1542e0768001158030454007548030598a00043c495a40c10000e50303402030114800c18007546080405155034a00050801402185c001c59940180d0340a40141d201800b16802e400e07c1028a106c0300820710070101941d00d00a00881001086900f04a044000c081d580a002540b560701c4940c2d6800007004010030800406a44c0c01c05400d07034041a41d144480d0460654891740c46140120805c01996030399401800381044140443c0050624414007504841c20f0210024281ca0304580d0700c0369620401800165851000a40d4904801080700d414030b540c03010703140c0115111041006508032401c9006d10008000076200c28100d5000540040e100741418009072810141d0b0303115183c0540d0218002102c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 338880170 1250 338878920 338878933
    0x804050a0611071406090a021201110a09030c0e1e04060e0607090612061d090709142203230d050109020a02060c0f03012312030301080f07050a05010f20 67
    0x1801250300e8030054000144003d00300501b055900142e0700c1308545002401200c058540c0300c106c0c0000c2d03218803100c4022500e126030303071691800300408110050004072810803800b64041013249542544610030910b41015010041451000380c00c0725100070812204103885000da90031001051204901850300390700c55136200743c203105020308000340d200071503800c4034030309801088080801d80303416105605580c9541a9a161030f5861824400550844141a42450446280840c00c00a00e034450488000e030407091642203070981e400c0100c804c001600040c090302c45406a85064a41c40d4a56402c52409604e0440382d102d43c141501c909070700c4000090342c00f064100380c59070180b08280e4800140d600300c6141035030000d076900d814001800360500816440115000c01840c007044811200c500074940804080c450346001d07565442405012218080d10948407682080064071070161b440040c41401002d00b00303401141da00c418018075500704002c6109070101c01c1c88003060340ca01d000080c40079102c07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 338881420 1250 338880170 338880173
    0x90b180c070c081e060c0304060c02070f0f05010908060f060411090301150905070203030106020601060815030a0506091209060904020a0309020a09090210080c030a0b011107060e09010b0a0503070804050a061107 92
    0x4101e902d040007404c45402840410a074801c80d401101d80c0305038099000921011041300403883c184454104442580a8040101e403012048482c202124026aa098291030321028441d03103ea400307440b0555090a0231010565030328054002d400c440303281003842401c004c0038200080c25a82c002d00d8002c4483c480403000d00840202d4012580d010029000031440c6500d0408025615401446030300c0c01c115103503001c240d448141003952a10468014200d442c681c0103402c240d9161002500c8001da90300ca2114401c2c1c2302800401542c1e180c0300014041411311002c2030501c001b80d44000480c0e020550303510300c40740050b51402000310150504d8800000c000100d407041c0100c0041128450050140c4442008251071449046aa00c807020303e40c007140c40305140700140c0d9524810a10f045c41400ac0d2040400c0301640900344600180d030440360310388582d80e14032892550344031300800070000900030000104080d01901a1580180c0710f0802c46459140301c0d22400b0443e07000c10921308041000089100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 338882670 1250 338881420 338881453
    0x2030405010b01050a02060f090a0b0c2106030a15090602030f0f06010314071803080a0f080a09050a022809021c0605010819060906090c0207090b180c070c08 69
    0x8040c80702c2070910758034107912410065501e0000a1540600322600750010b40195401d02104088130b03486507611001d41414452446da9030080903155410b0780303000140407142c40031442c209025101c06800f801c006d507620380301d0034180c5110305038542d034041d140c030303000320000726148011849071403049a85206800c0c1401107607005900078160318101818448503942104c2000217031504006941403d10250b008021501c072002130a9001500791240440c000710394039000071150824540b507682d040c145640b0b5450710012035203801c0000d000d0360f01118189006080c06034150301410190b0182d00a004503055220055924a82142042030f4011a00903680019039040302c2c203a00300c06000341b19030740c10240000c000c030078014040070b019402c441240071200c00592001c03020303251814060142c076443d0545030f009000c01c01003400051183ea42c00045107462481342c02c510050007420b02080d2142d16000103034400780a0044809201d00f0460900028240070042d001401408060501c110800180c2c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 338883920 1250 338882670 338882681
    0xb012a0311032802010207020603010e090c030a03030203090c010503190209010212040f060e18040b0c0f04080105061203070314030c191206080d120510050d05060a1506020a0f0204021c0203040501 86
    0x46044d0780c010300124005030b4031181a40e040d1541d0704400c1e01c15a50303056417a443c2100504086805020345070000e02810352540085100c2c41305501103c900506520044a29102c12508d070000c07840b86188400034a41140c00030041000144103e031041d0410006140459010380d2082101c0d03041480704000071500815400c0c84600c0c11242c1400d20b10544000b08840e440043c001802c2d5400c0100240c50100f0110548242072180c2c00582d0b111501c1d10340850091400b6942c65200d43c2c0814007203c0030800c000110b5441e554560f54020854030404e03440351030b641025014046940c02803282520401a481d41e004500380307199039034454030b881c007070814048070f0460300041030320b410074200d0400854200c0b4032100c12000d1850001a04e80d41e0310401c6c00c00a07865084150300c840803405280c148000040d0742401102082400c024840341fa12245100a02600c44c20740545c120000260120303a058281100d905e00282002d45000b02c080322041e060200c2d0f182854840703901205110a0000c01d00c0b61 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 338885170 1250 338883920 338883997
    0x1b03031b0810060302030c0d090804090e06250c0f020102031204150c110304063e0d0305060d02010807140a210905030301032307030f060b012a031103 66
    0x114614104040c00e01f4040c41441c01c0022543c0e1188500c0d81000040b504440003080c1d0b20f2001c101446c1c2c40150a40c03030758404c4e03804283c1d0b9a5008031146641c00c1d4a1180361501040762102600107190390748000920311340c000140d040d4007003448a06004808022540e21407441071080b502d60000300c80c80740c07085400700d080880802c9602d140c540c01c1d0000c004211000d5881d54180100001d0a44504039000d01f0079000e1504e0511130f42141c0d000144008100682410311102950710400715220100c0c02c64004440300755000c0c484000751405940900c400541000491920343c0000c040e80c0c40c3c002c2141e100a46001c0044d121411481d40d441c0c0c1c00ca504807442c60b41d108148144002074440070358901040c00003404403081c20101c1c21074548100d01c0309080d010140140c9400035a6400c10140c09501c000c0182d400c00d0510303516280c0c1b03600c81c45402d506000032108108040c22113071200125142c4451040b01070100320070380940503410030805405d084261950440b42529156401089855a40b14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 338886420 1250 338885170 338885177
    0x60207050f060609180a02100503040b18070306020c0f0f07080c19051c0609030203120f07170a0f060311040e0609070b1606020313060e0c011b03031b081006 69
    0x42c40103a9071240c130410b40104100c078054440300e40d0703081140e00700b010340384009500402c0d03143c104680a80040146200320f0081850700c801d562944c1e0305400340c26610b08007a103c2c2d00601c105100040703290f030140c02c0f55a020300481e042c0381c5008a483d8034003110060040c80e20380c06008208800b040c01c00120400e80c20545840f5114462132076082c014070650f01515103d5200070861001160405c0101c0d690707507802a03002d1001c00f840d800e010752030360310600f145622002203400141065600810003801200075076203202040803141c0000802020280080320700790b4032402c1a59440c8454080c041c05903020300300910b80e0a19440400c8100d40c1e03c041c07021002d400820401c10491030110f02e040889003096401c0340d8840d03081800d03482003024440000d0441d07101005000c0d03600060103807901d0403481500200308030510750300c078603540340c4000070701e2400285682c14852402e080c421844088500c2800c01190a0040245021178520b0304074050f00002c00403001c124a60031000017000040000c3e05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 338887670 1250 338886420 338886433
    0x30d0e03030316020a05070f050a0504090b0f0c040914090d03050115050703021f02491103040b150901030f02010c03120e01020a270e04050c0904060207050f 69
    0x200401d403203000042403100a000040c8125500c00d0003401000406030380074050341c0d450381d25100b07075000712071681c0515800b80b0f60b41000483c075070501e0301c01c485180750000150740305a41e4001d20b84008101c010101e04031078509000005114810b8098002400e090b07800620003468051078252400300035000b00030405041c040100000c8422040b0680310030f005190196481e03290781400d9141042d207940b6071074000030210340f03650541007940c06007031a95045581e94588540128520110340c80d010f034522200d4030704110300c914071010f0706406030503502074030000f16400c1820804041d00c1c1d081142d041e0390800d4039500700303c0102207031b0b92000420032003250060313030720b50540d10707000182c0031688402414070603881105001d04d170007590a80c0505054040a0020311003260300b25003c0d401401c0d040000c940c58a8000c0416030640c84121114400000c0034425103203840403903400b048001d8016a828003c46000c180161a2542001e1003240208800340c0d540800b444c12500e0803aa0034090b802d1500001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 338888920 1250 338887670 338887697
    0x12110f150a0603022409060d0603210207050607060b0d030f091d0412270f06030209030604060b06040312090f0e0402091801110309060106030b030601180c05090d060b030d 75
    0x900c2010b00c00021180340c049003001700d5911010134450440b07190340c00030b00441c034000180c9130354200780240d030720650716a00580308000c803800003801104008005600f0844081c8160f0400801400d4140c0c044c400101b0100182c3c0042032010400c10303410340010b40f001c4183d990050b08002100e000f4010501c0300c440300c1406131403e091401c0090801070022104650050380e4034840c80e00189111802122140444d98840e1038003480700051040100d590100d001c0000c5090080c801d403055014050702803c80b660791545c4501c02010000346e903e0340510180000710114119445043d9408825242c0f00c660504200030f219050f40c1550000030451348201c100401078807664005a001420300101d0f5501400510302a809001ca0341c1643c0060354000c401c1014405000509038129180e41d06e0400c124500c3ea4241616840700340603255014900581e40f43d1400806ea0240d04100c10364645a0304048402c000600d264555140a40301a515015040c80318a801e1280d1408a8614100f0b8441442c48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 338890170 1250 338888920 338888929
    0xc020111070818061b070302010311040305071a13090f060f0501020a060e07090c0e090609070206160504050a031406060405010614090a090c050307020f060403090312110f150a060302 80
    0xf0311114000c000505158000d450301c4050a48201c0c25101c510070042010100010f540c0b20700c0b620051b400071341007503106c5103c1c1105508590999070401c004d0400e56080c0325268880d015002c45150041e0405c100043d0412a10001c2c00d015100c0c078080071074280e4049142209598290300860315030700390220100002c0c0e03000504904840d50015020441500b6507421504040782a44018000f40c1003054000402d54031081d4491483c0c4112101c4499454030424460100c8086031403802592180000c1025000304800d0740004100364a0501c0c41c0a44440110381003040e5a401210400d00381003642154940030711000f07a00542c190750030011985402d80040034808441c0020b80c41f09ca00050b94401611101011400b408400000333005103214000c00504030f510480310500107018420144858410204859001302d40513661410943d0968840004503030030700e1a44814011580c604c001052400c4c05105940d01808004c0c0000c040540e07107540400708000d044d0b4503c28030f440001c0c00140c1e00e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 338891420 1250 338890170 338890177
    0x180f041b0b0313020109090c02030418110412060207051608011b0f0e01020c03032107030605010f11011e0501080d0507020a030b040305070b040b150609010f0e0319060c0201110708 79
    0x201c400780440700541400140e1b000e140b1034001e903070442d08006403c410203800100820840e4820000000d0801b0492182411208180403a402d405001c200402c0040d44810404848500600005240c46110b0303607120f180150f0500d540b126007860700c00400080a0a205030a441c0d0207071541c651054540d60001401540c13298100802c2c054030306500042e80c0d100b04407400c0001006401c695560220500010001c030060b04140c4190341c1d01d0300051800d80c0310340681c03811604d040c1c6445d091082090f00542d8a00410340d061040356589105400c0c020f03907a8806000000151306000940b07505145507a81087c01090188040c81400c01403c001601c1d5420240d0403a60080355110742d0b91514a4121101d10039a8409010b09445009000070b10080d403010034042c0a02818855600041c4001e001582c0610116180880d4503244d04080440c015641d105100500505480d001504004c803003014000780f246c10381c0c1c1c030742e41c4400c0381c82410740920504a2104c2c43c00403171810403d06070b550110078030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 338892670 1250 338891420 338891431
    0xd08010b13030b0a02070203070b0f1206180711070501020a080d05040501110c030c0105060f21011e020d0c0206091e0705100503150103020309030414180f041b0b03 72
    0x400145800c1071500c040070710000e15405500c90120b803c0601014001c0d4012040c103a01c82d0084080004401d400d034001c070398400200141079810311003201044c1803600340003402942c10018025100c0303069040b807a100c0d48980356545510141d410503024080c0381c4141b0b0b802441c10f5520140201002c0f61094041c1d5508000b143d83c0803072507a0700c2d89080b03030140404042145c6d8000b000705025010b880040083c190a40d1808001c112079910b0204100d1283c032283c00640d080020100d548580303e00500144c144080d4420001c150507078a5402c403a4011800c940d00111180d010a0b400005049806207140c00ca040d44000c0080c0d0070301280c5182c03680300020881c26140311078440390001c071078144086401800001d08800d08004504009030055008803509400c810034003840908030f601a209480c007842c5c001d8001c5007028101103120250700344a075001540405402d02d07184032503412068461007001c0291031036419041a00d00703440042072101c0040b4200c1ca41c00c00a02920301e8000503070350b010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 338893920 1250 338892670 338892689
    0xa0b0d02120a05012307050a0e100c02030607051209030301031e0516030303091e0c171e0a02011d0102030304060518010903030e07060c080703080612070e0115020d0801 74
    0x158080000c03034681282ca02c4020055420000c42c02c10b1002d00e1120340603510b503c060703119410b42d140102100c1510405080d400403540d1804550410304040844031041a068144040a0542d64002070300c1e000040320398500003a400a0f80302442e540c4001c2064220014000840c01d55055680300d5608290900400c5440ca140c0c0390000144a070800a5031400c000141c80207940d6916401c0c018040c0480c0c0c1c00558680c601070400c01c005c0c2c04400c0001e604542c01414084100e4108540400300803460201540a44940c0c01605c80c6010145154070030a00d080008005255081c4000342004090b0f03685c282d0451040e940c0b403092070760044216980168400d07030000b405c0d46c504040c0c50048140c1c04038115a0740c0317080c110100309901940310300d9554070801e08403000c0c030b603075400304a402440c1450001e041c0b507004c0c032901300041c1c020000f80742c000600800201008090408103031425540780c1c05080585418001007089041d42d10700000300c6211403000d1300d550294040054032428040c811240d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 338895170 1250 338893920 338893939
    0x509150c040314011a03190206130f180b1815010507050607080403090510051b030403080a08070e0108090a0f02043305010c0b01090537050a0b0d02 65
    0x12184840c0480740a10381c402204410249034400c080c0c024461000c48002082170342c440c62055260000e52100142e801c007484243c040017a50070300c1030381d1308504100d080700d891042c00440d00070550540e20001c3c100301c00000caa001c80d2810902c00303440302c0a01e00c60148100002c021001640410b066922140f03040c4110406104180103c03034031320801e40090858040d03103040c40a441d60124100e40a41e011f942e80c82c82041d2982e0422001e41d2101d000710b00400d404000e00d41c0c6280c40041f40c0074018060000b9242402e43d071341c4840280c1d034400b515842c001080c3e0303c20000e4407500402074040d0f07010b0a19182081c4c0c50712200c2d09540320210784000d000040310280702802c42d640da801100768009020310303000301c071a220400051040300070682d41003d0303000ca00f00030425501c608440405a508a11500016464492924010301000d45811460a01603079004184148075801c1781d005000c541907004414003000900e030450380c0103800f50324454101440c41d0065034501e9800d81a10b078046840613507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 338896420 1250 338895170 338895181
    0x40c020309100813110126060a0807050d0b04020301060305071203090e010b0412020f190501031808120709030f0c1403010605130b0604090501080c090f06031207260307030b0301050915 81
    0x10800d91f905030f808a60210070392203810f030711050f175029802010251100c1c400640c84002d80340c3ca0312402d0141a0700170415429002c0480c55101005411078009800060303001c0e140c0d11076900b44a503a8004002d01002c41d407106041541c0444080020101c10b0b1b407503140755061041000b5980701e2485803030351503001c400a10007503559032000c21607442002045503400a60882e041c501c203156a119060100f0f1404444000c91140c03150003450300c036400811507280103858141108400000340c03da2080014101020000034111158030108a002c2d0740746440395440c1c8010791960b031400c00030950080c1d040170350400803a25214a500042846614003203403048070310f408141d01d40620790003070101c40c1c104400041e41303850114248040c1481540c61403000d03651007414844000c2d056400a4069004444404081c0e10b00c401410342684281b07105580100f0010624200b09240c409910107000d00005100541e505071080d4030f0217030b400350020310261a04102d600d03203a101c02ea5106e9512074241c000901c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 338897670 1250 338896420 338896427
    0x16020c01120e0d031509020304020a15020a05010c0e0a1e090b270426030a090206190f022112070c1403120a110d0c020309040c0203091008131101 64
    0x1c607039402c1d40803640c104000c00c10080107804c16084030608030f085c100000c0340d9903409008907482141c0140014040d01c0c038210b00700040701c80074410501140145103042d000a40280180d1740f2400e42541c40401c40544501040078400b2180d0000c00a07214001520100c85406620901210040340000860110706000319194200e180b0510350102c110680326080c0300141a403550166021305203503000420395034054281007902c14100c4021030018030009260505a030030520500c1d1001d06041d08091030f49868085080200031420003107007203144041e510642c10410030740e021000340d4101c0603d800c40b01e40b82060307205141d003009494030340702d001600c4075005800c4000d0044d801001008040c0f500c0d0709003038994000d402c0c030b180c1959855000c92000038240c02000d012001c2074903201d2030b002c0303807800e80401440d0403428542580403c2c080303078210b50f69a10070b15141403010f4029664944556040201c0d0071049040a018000c4072002d01821000803200c20001981c08444191981030741380040e07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 338898920 1250 338897670 338897681
    0x406110a020d030b0f0a06030912020718150306090501020a02010b01081006030911090702030408010b040212011e05100f0e0405040b01050918030f04030201030b0109032a051203030f16020c0112 85
    0x10b6030480d81b040c40004080b54141d0022a841b80980d060700c52242c1501c20072070321904c0b503105900c076203102a1002c2c0310f202c0d4103501028000d0305688017441115a00c0d5602c10a9480a820503101c83e5400710301031282503028007403e0712003071017441c144000d4a84004808140640c1d40100410180d49800701c0c02000003070809507400500042004400c0d2408050003540c80e40725000d0101c56500346201901c080c04c0034000c0c0c0e80144000030249040d6030800c020381c4020401c1c0d5219003400c1c0c8107a100011262900c0410b80d0168445940d64600c0304086040681440c950301481400b46240c4401c020100d0b120100c4541592000c588031b000988a031524850001c040030203110b0b03240400600d80806805a50040088a00c00e803001c3c40b05911174401500c1c0c81c0110312010307100c01070584104d0103100240301113103900f6100040140c4696210404140610380303113000f00e04560300000901400582442c1c46c0f03988510300c5d244000001030002c1000b511031540650305414003d41180420400a4a4000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338900170 1250 338898920 338898949
    0x201081810020c160f1d0601030f090b100f031a090a08030108060601080108151911030a0c110715050a0516050604150c0206040f030e09010b030406110a020d030b 71
    0xa540781c050b112045a22400e038201c41044d465200c04000036080c2c181e28520044480445400c800c2c0e410111689006040003000c07203041507902d01e1144500182c900c41c0345120b90203445200382503c7c003010040c0c0c2c14210b60f00908544d542e9944204006641d0a0a042d00042d04048001a0b0340310f001e04e044c80c01d6a0703140c004110010120000c6818140001e40d907104007000d07a0b0706422070741d90365582520740e40129a0402e0301d4483c0070005071001d403841c180d0022481550000038121110408400998000b03640001c0c0143d150340791512000e80c0441c00b031414440e4180601880303407400c91461500449401c00c081030000119041da019070142054070404a0340341550865086a40b40c42900d64174100d401311540c1d00384000c48600d40041d0700c030740301c2c1c40718503070700205200c1e00d40d5201c1209100800d2001c400b00007560501500d0f07a11041d90441c000c0401030400ba40700d09080c0f400c1c0013500c0d080d500700f044445003030052581092707000131054600da80c2030400103140301c02d07880030400c1e000d4124407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338901420 1250 338900170 338900203
    0x80a110f06040e07031b0c020d140d020105190b06030106030b06040308040902030a1103011a03040c0306060b0a030c0f090605070c1a180d0b0f070504090908070b07030902010818 78
    0x42c0014208203101080d8840c41d240c1d0f808001d1100c541003000d40181d41c44003c000083d005000d40f100508000590840c0a400b031110402102d802d50708091609190340003000050351100284880078690b01d496911410502c8018024072000d070010a6160005105180405899240100c501e4458904139001342d03420110540c0e485442c0c1c203006010f0741c800d4400080c2ca40c41e02c0045480003000b00141da05907120310210ba8901100808110079907040a4801d88034500014000000290075201c0c8400410070740f081c0640364021010081c00b1a20442d903000d05210b903249060f100103605c10b10355410f48620382005500c0383d00c50300701040b880712181c2207080d65420750311000d2041034984c4041d01c41c011a40840140c513a454500b0300c90014a1104000c0215030001c010540800c3c0c400e82940e4049a02d24106040503502c000c02c00690b445003030705582c81040040c240c010b00c00c1c0c02c000c460384101c0c5070400b8002000a503000a01d0382c20000c20741400300e0481105000c03c10414084524040c03040306 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338902670 1250 338901420 338901427
    0xb1911160e070c170711030f0f16141c020301090309090f090b180a1b050405070503060108010312020f10050105030601060f020604030c020d020d0f050f07080a110f06 73
    0x5a04840100d502605101d58140380000324154419040380314041c1e40112145402c4040d5099450b03036422083c0220740500000b055000651820088142d4812000005041c085050b401090400245665864001008400034499003008006e80b2040c14429a0840c1c420354038815603041c0003c0d810720017035041d4200007031320003850340c00000a015100c603060200300350000e2800e11400c82c1d211880091007162090001485080c400c00711105109206040e00c2040a059503810a0005080c041c10602c0401c103100307000609017032080b250b0045560901c18510f013403e000290812105110060807038428514015080c0d05c24031000e00a850748108894654507445501e0016003001d0064170701078480e620001600a10620180c0003040c21500500019110340d01d01b16504004603001766006241c410722036006856178000040345600800030f443d00d150440c90a20b050a0f11071140c80f81c03603403180d2800e1002d40000f050040202e540001301c603139180051004600c02c1d042c0d0030f604960250021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338903920 1250 338902670 338902693
    0x905010506010801050a0e01030204051e07030218060403050a0f08040801020a02060603160308030f2d04060e0f0c270106121506050f0d090813050405100b1911 70
    0x1500030601616090b00d5288a070707a00c2d0024030000c501e0070701c5030720520f010744001000581401e9003d540c00c00c2c050340c0c3c00d80069112100c100c0d0209000d41d810b8000903400a4110a500c04000d405c00041600320307200e42c0b90518540f1220360b00c803030042c00904007951101e901ca04104240c0200c0740105000b01c004d545070780c00d20202a455140442d5920b000340207401002c20031072400600802941d03400074200303055848a01004500130300092410824900540c13005e902c040290300c40311804001e0f8840c1c182c07189060b150000035991059031001d8a9840702d1055000d001c0042042100321209450103070141380710b4101c0d403003405002e21003040ca4684120022541070341c40401c01c0490f1007881c005010182e01910003648080a0b0700c140c4002071803d00c05848071040880007081108021040130491031140c4c0c0b600710160b4045812806a0604c8803420000f40c14a4000c141d800b0283c1004038070000d140c04580030040c46a0340c500740c000341000340940f800600074082e41094140070011190030400c503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338905170 1250 338903920 338903923
    0xa06030f1b170a050405030412060b0301020d090311070503070501050c15040807021203040609090209060c070608060a09051b0a110706090e0a0b03072114010606090605130510050d0905 81
    0x1406007108284a840b0005000e065642c021240210b9000006624052a100c103110340301e02075400c111407890301d030b09200400ea5400d0010342000041805e0000b41078110f45000341c084500e100c4203401d29009000200304a68010a00c44129136080c01d01e1540c4000d02c5003114203005e441c40d84100d5940c0741f40c05000070304c1820009007140718030954410020b0364400c41351607501d004500c59100000c0750030200340301004440c0c014004a4002030803d5090444081c011424001d481c0c10107400284010104941071030072101d2103004102d04d040070440c609020400d08554194070710b04881d01c030000645a01e00740e116000182614041d1001d44054540b0764100414075405845204a180710600201c0c2c0038686030b2288000302c540080040241074684140f201560741841540c02480d00e10003000f0300031a2403514500f0b441c001800c0001040c5082c10070241c00324205400600c20440705100c041103500e14849a0400d4a40c200c0d60f03011200c01c00a0126203500c20801d4460026007840c08030401c1040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338906420 1250 338905170 338905187
    0x203010b0405102a021305131506050105030a022d030406061d040204112b0c02070e01141c1209080309130e0c0a2c060a06030f1b 57
    0x20103d4074031003c03141002040328102c0686030005102c2e00d81c00901001000c90446540344244058004080315a040043d08100d450484d90003198000704080201013212250260141800d030030b4080140500b840d000a0180c0002090440210343c001500c01c0c484490344624460811885030304100501a02c2c3c02454540055804035961070504802050142001d000d000c015158500351180503901c0f9020400a00341c6139140e104011010010748159503901c0c852a030f015819813075400e400d60784112402049542d955009400c54000d140c003401100700ca018418110348181d00c0c0d81ca901600741d00002c49008082101422443c0903004075401c2160f0300642e080c0f04150350301c445003803540d510850b6071244281d0681503408480c1d400c0112940701181e2202e20300b01d40200c12101a00c0d1224003144070f991282c1c00801c004007446c0d070170507007010103086c200c00c81015909046c416810010081804000035001d02d60902d0740b03640880d105050181c1c0304407e46690042034021072025410302401088 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338907670 1250 338906420 338906429
    0x20304090b0f0f1908061830130509040f0b0610020d0c0501060302031005010806010f0602070501081306090b060f030f100b1f080a0b180c0f0702040203010b04 70
    0x41c1816900d03021880c004001c44242d20000d00030024074140882085010301d008158409002000000030510030410010280709402d0b2262015036100d03080159850402e0100200801c8003a06000f004400c4404000844507904400b89613114034020422034450415a0406070304288200d0070401032004031181851136600520190409031a00418030511618103600400903071300107401e00da0a41d1082c4108070080f4018000020016140e0380000c0c1007000100c01c9440c8039172030f440148011a002c0c062280141005406118440d00d41400070b910340c0e01074454203041c02102c400040b00d07040d0b03842c1a10f90b855482081000f140c00c081c9407001c3c080c0c0c416a007440c010300081028800d1400c0014003998000d030440024030300d20400c000c106002c1e084408010b0340024109089802102c045102c2216211480d10f500080e803401d007070408100c421840320b0b54480c180d1170030381c0000315400c0161548c0204044ae00b4681e520030315111483d4a01c42c46a000b900302d84004000500012110042c20554 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338908920 1250 338907670 338907689
    0x60418061a1614030708041706090a050705060d020408100e1903080406020705010207140a05060f06010f0e0a05060406090f0603020c06010e090a0b152809150308030403020304 77
    0x8020301d103400720440c0114140701c2d868100191105010810071581256025092822070b49803000f190b803005200c2d0401d61003542c6141040020503036079501808281c0d8401d8249009180410041e10b44641d66030341445058000ca0340010a0080011544c040b60050302c044000c4400700240501d950004240c070305040d03003032070081c100d455420440e401280ca0b401a0181d460034095201c98507204000e500488040301c1540d802c2080e43e001411080030b00e440300480c1c0025240c01000d0742012800c14000420070161138420108029240c1c0c0c010180c44803240c41403810084428400c3c02040340f03840030741c00039544180301080001c1c0c26940414140140c5403044441800950768110a509034000d020760017145820403401072022201e507098141d4015019000ca0f05000c00a44605007150016114180c14000340703815801182800c407620040105040c04501c0203054042120071020007a0040c2007199468854524540c0005040d40c0e02440d00701154039601c0c00d091070040e50300d501502c2043c866 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338910170 1250 338908920 338908949
    0x90b040f06110307090501050d15030f0b06040b01170601091703180406031e1a0c120f040203030301260d0504062606060f0c0607030f0b19120206041806 67
    0x8040b0800a481c0504525118807280608150041d04e65400054504200c15510084600d0707201070060100015806086004020034941c00d01d082218401801075005a013000c09949041e603002200d040030007a216001551074440400480380c41541d903001d1a003034500e0200040322a080403000b441da0a03411490011109000380502040d100c0c240302c05040e051031901030b048400343d4103040a051034401e4102030400f0901c1810419000c5054500407030041000c58140481c009000c0c910740c01005840002140c0e280c40d50000b0340e039100c140071341d68040050519030382c01503076908034200f81c010081081c0c8803448940c1303500820303c0e0400e126800c00075002607002001400b90b03126000101098034000100750741d5003800c1c0a050f83c85481002c102c06030820050102d500140182e5010301116a00440d00c602043ca0070070548000e4581c161062610221805603021121050000c0300d40740d100c0071003140716600000f0010f0141da441201e00307052401c074128096030f6a501620a544500e40520301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338911420 1250 338910170 338910191
    0x60913020d0f0908030604230901090606091a130905010e010b190609030318050d0605010806180c090c07080301030302070e070f08151f02010504061413080d090b040f06 74
    0x544801d1000904850702c2000414007e0926801040d1512a400c0c0283ca0b01d4008a14400045404a910f81c1c40359649207040003c1021a014000c001c1001c010188020003110120b030480c0c503500c1c04141c1c4181a8084804c0e503544440c2c12415403580c01030001c0014596142403a40604104460a0b03c246100c80d14110382c1c150f120988000d40d807469440030060750459030f0a03281c88001a2008204070a5490300041c20750720300d205071601d144600c2e000b0805526120000c1d143c031a01034a8155009400c03c00d0000c0e01000040990419404503a010712646407070041e40904e1080c107038040c0c5200130000020003895000500740003120070100e403181c055654150200c0d9885102c04008000074aa03a0100b0a4071012010380300d00810001c0ca00703403101c2e1a8988910070b200b21501c058001d03035110010002808003d20460b050b5410040d0f070a015850f0150360031400b802c80d00300040c1243d13008075144841e5855540817801c003643c003007000950307402d10b800c1502c68454820000c55036070341408000c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338912670 1250 338911420 338911451
    0x40f0504060812160b04031e0f0c030302180a0e0106080a050601050403030e13060f060e18040b0c0d060e040219141003110a0302040f09110301030809060913020d 71
    0x10450305a00050120b43c604801d4201c0154400d004001440032490600008904105099401540702c0c2e1588400c0d1b0510441c0d03c03c0c4502c240304218103010300780748500314244e0414004031000f43d040c500140d85d00f80754120f03004600c1315600e1860704013075080300c00708180139142400da06a0350341d510340301003694800c0034840c149d420441d443e60005006001c1000024020b6007100c5102000401c548040c00440601f541100d08580c00b00c43d00711205101000040e070402e440804203d42a10410b00c5d482c00d5440810703c411010304000c22900d20140007804140540e001d13144c4d203022034038003400b004e070340c842c5e44419003401a0390a80c4160001026100d4509130840c800c82214503410740c68000419001c00c00c0403c0c64014842001d00d500d801141d0035044120700141005030098034016107460400f01d140317444100a410904c1e04500e011032a460611002c02520304407644041c03242d5403544072801054980c081c0440e1290040d0411120880b26076840c0c014020641480c582000a496030715139a6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338913920 1250 338912670 338912681
    0xc210105161701181119030204052e1107030512070317130303020a0215010905180a0b0a1505090f0703051e010905070c02030a0b07031103061c020a1208040f0504 71
    0x4640040001e4030b0201c88140c00e07045a00d1810b000d02c00c45040144065201240351b80403420040081d81c0003600307000c10720307212803021481c020f1100601c1c20342801f600165100c000e40081c010a1241d46003044160103010010309000d540c0c458140c90090142c421a1a05078202000071004501d0b20828103900d210600d01c1e00e072146c0070442d10600400e0307440d1000e0300290301c0b045403001180108000c8507070a40b24003058900801c5101710000307903458007990405844c130585800040a411081610000c02c9100d101d072908103a80d0b841c0019624000395103000c0d0b07122164403142c0c005001e0b904000d038058501d03844038441e25050302d007480156618400808507405040750101010b040d8801401040d15941c03185611501c241042a54480c01c5c1e00040e20b009072400b021602e20782c207081008090355140c082c0388083d148241d00300e825070612030001a0105940d00900d2003030091014040159910912a1030041242061800101c0c0d42800d000340e0300d90040c002c8161158000b040050030741814800c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338915170 1250 338913920 338913929
    0x10020703170c0d0e061314030c0d022b0609120e01030606050406031503140303150f0a2903100906151b050708101e0605030c210105161701 61
    0x54040303d880b824065035a002c1903107103650070100500201d1601d251800540b405400740b8012a8a4018500101407401801d4094140030300b46400e42d9400503200c1070349000b0f1001d03516080c4481d40d119034454601506070b506003e040b203800c1403a0402840407205c46000f0510700c80e902c00d00e15035031880054040d10741d1482400c0001d10100403c006580c4607501000381500c05184280466a6075101c2c407420650401c2c011029410000a200d1246280098610301500940c0c3d9890018005000100c413070a041c07040550f0340c84010060030845441d010480100c00340340c002030b5103d007846581c407095090b19010b200036142ca09180455186030000c004111100e45946240007c036141c00070031034810814404840b90300c00c02001107035054081c40304004030207100c100040c0c000240300d107803c0700b40d0301c6443c0191601d1070702ea001c0c0040c6e2000b19030f0401d4003906841880c00310084215684402d150008008825440d1405000f5090390312203040b50000702c190355408107007034014040c0f0b0004100b07108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338916420 1250 338915170 338915173
    0x60906011e1d1329030d030504050109021f0e010206043306060302120a0c0c1209050a03050c010305070503090705040f11033c060904050c10020703170c 67
    0x20804185205040c000b0100103040901c04040041001262010002000140c2d20b140c80f805603081c00403841d0008864186035a800d14011324403400072944030358000d0103841c101601d0320005810311009400c003a414960282070805000000041484850f600420480014001507010702c5103601c0040d80c5405143c2103002c400080f81283c01150000581a8103442078804e150a641e809a070580b059000901440e00c001da030b1482c0c542d01e42075500200605800341d103440c0c00301c840041a840b4030f190881950180e0007601c02c00001d80140c8050840303030700041d4400c0d12208084100300c00403035101d00000d82030300c09201c0e5032144001601c46000440364000c0c80e42c03105c0000c000c40e00d040c1d00b1010190004100000f5003043c90005000786910840340356a07031403007085090302140c00030b0704004c115003005280c41c0081c0e04080203003120580050305030307403107402644040f0f07003449001d10044010841c0107025049000312030001075100c00c030510003610803146118400031703200d0b03041048400e446400d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338917670 1250 338916420 338916467
    0xd1b05070b0f090c180601080a020403030c12110d0903060b1f05070303060b1b0d02030901210e07080a0b0906070504030f1401020c011406030307081213061406090601 73
    0x14000da0b5442002003070b0b88480d21411030056065141c0c1c03214103042d48021442e0010034a801380001d41807000c0544140680c901c10031040000c40e921001c1c00c81410b90110704010050743d41c02c0e0032603401c5009102c40d86c880c002d042038000203d8108182200b20b92294400340958070141c410411840405880082c1d10400c0e48410074140d440b800c000c1100d5813180c100010910b03201d808800094101c1e0b80988100f52181c410750820700300030006030132103450340d00c0114038090200000800440d103220500f0040100d214145013030000d0382d0000844440104200c0d20311998a40d02607685050040099400145c0c3d203001ca43c5071180890b1440c829034254481c00d142c00d2659a4210701d819195600761807452001508080e800800c0c0020000100300e1400810801d00750040d200c100000507208500c02d910400048000503044825140900d0b804200b200650340c50f106100c0880714140d5004000c54908000d4803003100001071418054007007a22100c0080d40d840c8019251080304070b01540c0842d403c1d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338918920 1250 338917670 338917681
    0xf01060b030c0f0f0f04090b0306091f0c0c050d090e130308010501110312070816030605030601060f11100501030b06010e15160803090a06142503110d1b05070b 70
    0xb07201070100390481c50f18082c9045c2c0d003403081d50001d0b08080500c9840f01c03070046540c6000c000c000c0c1c00a113075070050814a1030440070505034100002c0b44045c20fa442e810b40040e068041c00e17444426036008000c1d00d6001c201190024100c101500541d482ca10700680032035041d04045860000090b490b0311880266420040151076807080c1c29980219840204200b600045114150600a007026190140036007005a420411101d801240208042c0f0b0701c2820021a81c000036820704550b154100104202014041150110307409141586d05d80f103402c00c400c0c000782481e40b100c3d040342d005c0d450f1440151102c00046034450f600840d080c3d07108440507500f90300184d102c8001d040d5007001c41094250b01e192582d4000b599001103e0740da120303030000032401c1e0511405009840d056140301000011506e80043d840510b4100d00c0d80045a51200a04e800103042c0240d00418111400f1001a074989103e080c41002400074101951202d428000c50b1005250260081e620343c107078040d21500c1301d9900d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338920170 1250 338918920 338918947
    0x7022106070c080405210d090603050c0c1f1103070e010f03050105010f1404050a060201050a0b0108060d0602070503091c0c0f0b070609080909040c06030b03150c030603010e0f0f01060b030c 83
    0x302031130650340061a20206581b00c4c01040703a0340040c401501d44400e024034000e03029044a4005211000c0780304100400142030f84007048800789101e00003100003610801542e0307203000704030880303030710010100000900113800d42060b08124480f40990390108400980c50f01201920b2003807144901080340c5a4082442034001c49903d01600103491001d410259100c000500c46011580a000541d660710306100350030b00c86000700307c1e08000a080900386030604030301180551742e0300007021f00195808521901001018000c54140c000001c198210003801000c10440c11002c02804840840c422100001c0f040d079800480403c40d00e604a4540c20541d046d22130402414140340708442081c0b0402000e142540d0304038170702d07000b1801140405100340c140b0501400f29001003488038882e610030103038501ca6014110711607500042910320151213465010119014001002c0310b008203000340b01100402c92000982c200242495400030b100c040d60f1042d00c450207100c159050914420200030310b041000d02d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338921420 1250 338920170 338920189
    0x8210406050c0c03100606030f05010602071707050d12031d0705060a0302040906030b060307081513050c090108030c1002071106090d1505072601060e0607022106070c080405 76
    0x2c40d000e0718030208400d4002802c01d08100403080d8210740d51030051101c6a8144200701145154981c1042194141071002c0d680d40703045e00c10314003900c07460000c6603a400e4007400100002c25002d090703580740c0c22a600d840c05443d800c0f0325a14001074980264116502a2000003401c50711041019049442c02c207000e00646501c034101403000c0c582c08010001d81c40d145407080b02c0080d4024000400141010b1003014146903240e48544295408240b049139910151400d9680107800e28902120408891034000e040c8901c010106a000d8104000020314034000700062003451940340903100c001030760700d1400d000c901a41c8400ba01a500b91020b00e03070207081c548014036220000034985649140f040e0380305031084a054144191207500c43d003e0058058011030b920f148008032040b0303924550340d68882030381518014400c4004000ba242999240ea48840c0d0032204841d0700540b074000701941c03802c0000340c0d440700e00400da902441802d00040e041071003a010060080e500c5a20545410306e81070821203241c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338922670 1250 338921420 338921437
    0x100e06070e01080c0f030a0c0201180c0608131e0311070b03060405090705030d032a0507060b040f0e07080714090408030604060b0c0c0907110a020904050f160821040605 74
    0x500810044150350b05c91000f5520031120040003080e40310341c1c080000e0a559015115011a10b11a80c000002858a100503400e0b6809490500419980c803102d089210781150b101401090250032070642008403003900003280b034041c3e1642c05074105c036404050b5859082c0d20440013441c5040c03012170301d01c0c07429400c01a0030107c26801c0703800d040d80f5100043d042c040308002d148042035541035610488041c40422084944407161401c040c0e441820b00600b40e0301c03d909000301080d69901c0d4450f240d660700c1e0700c000300c07006503105d0420410900140d01d690381c0515018640c0d0f18400d003034001404210f1104e013141020405171072244151241e42c0c820010b904050101a4004e031908808030700402024050030114801100070312203121614140701c040710010703241100b0040d21740002c2c5a01d104c005520b40c090b40e0305135034030302080c3e9807400d00c60b05041944150400f49e01644401c980042c0c07803441500d080d03400c0201a1640448021200f5890445d5056072081d0100144402c06c0a140280064030304031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338923920 1250 338922670 338922691
    0x501170309130f0e0304030308010f060915090308030c0d18081902010e120a030c03060b191b0b040b07050c0a0b06240c01150305100507091205100e06070e0108 70
    0x40c5a1910f41d88250740002a0340c2c1d450b90310100c0c0420505611aa206004120060041c480c141c00d06800810041c4180511100008080a0844224030500d2603100441e04403203840d440e820012205074859102007441c020050510300c144074071952203500414425408908245055082c0f01d144158070246c1140909556940c0c901d440600800e015580d0420b2000d40c5660341c070300f09030401908a4007d2b00b4604109450844180300c01c00204084502034203580c41c480951040c91135080310700c110610006524858048444000c00c0300c1d140c8040d000c0e03441500b0005295482c0d0030126030f036016010741d4429643c000e10001e40865624034945030856405011f02d071021007540c107100c1c0d0034044c10501d01c01c0c8950004419040c803000788039941c441c000106943c0c1348a0b1031a00c490307983c0c01c00319035403130461599017011a00044c0154100e01c002c00b074001c213002aa9000d400c0140d21100c500401d01c803040d0505402c100b04810210380c00e40b007480182c44082d8203880c000011101d204009040fa42030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338925170 1250 338923920 338923931
    0x80f18011b090815071103040905070e042702150f0c0d08010b0703080424050f06011806120b210115050904150e100204260a080f0f12011206050117030913 68
    0x40181e52b002c0e49100e40c0da1a02d40118404215044c4402caa00d881003400c04155107115041c1c103010f90000c405425501129544036074800100b0405003842026100c129540d800142c01d00528404640c2048400240c1c442e9001d90b0b80c3da0a40f880c451084070700040004c2d020000140000c5c2691030008011070401060502018828110364204e8400343c8940c21400240303000c122640da0b00c90312a4001c101d41100703010415140c0b05000d4074100c251560358005907110384078003c2c0c035203480103e0a00640001a440d02e10b101c4041654000c0c0a00e10542c4508508030402140c181400c0d170035107008036401102c0038904500c8104000040c00c0d164644407050190842e0b1680041c1603001520145c0805145902e0002240c108408204088000c1c0015508078405003070200354090f090740c1e043d600f0a01540c0d51105428558031040c4520300461080e440104000300710941881c0000c20520301c80d410822460744c0780c101850b01d40b140c03041c0a400a61080183c140d6a040c001641c410103465910041507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338926420 1250 338925170 338925179
    0x8070306091a010909050706210b0411030f070216050d06020903070b040f06080a090807020907180b0301050f03011506050f07020a0b190302040303080f18011b09081507110304 77
    0x300b1000782d000c815195100c032041000e000c1c0c1440074400406003410008040103045090810700c5520920802c0c2c1c1070b568480151040c3c03980e40260003d1440120030b250b91b8508005002402c14096810710010310035001c020000510582241003a900001d00c1a00800c5050703640c4406540041d4200340c0601420600160110090010f08060f2600310010710f00181000b9004181d680700400c92a0060700b041c44d07980205011000b100d5616805548103552582d410b01c0950f003840f260304d4a800841e2a0071000540100040c010358180d813030485002c0340442503e401c2509a6001c0410a101214485e10030803126004400814071264091040ca08050701a0002440b02c0c075a40c0c807500418500140f5020051031058000d080040b85007000c40c103017420340d02c00411290006004149003100b04002ca039016507c450118600c901c100006d00c0360030820b00401000f015400450404074800c4400400c0510022559405c108000d0203c04242d580e003050446040c943c0c60145481408108170205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338927670 1250 338926420 338926463
    0x5061e071b06021605100b010206010e1302010c0b0a0f1a031c030b1503220b191b02070311060f180a0503070e04020f10080402150d090308010e09070807030609 70
    0x3130846000b10041c10401c02070300780200540722242c0f451411904240014011040030310400390b009000c4158840c0c00000798401030311100c03011100506210801c07420400c1c11425500078070300880c00c6107024400014020700b540d4201d1400042141c1c95001504516100100f0071602c103403400c201d10707003c68035942c10000b1860a00a02c0b2003e0110040002001140c0c4102c6c030b840d840070200d00c1c05050100440740c513026920328000d8605807064081c090406011551a0480e9019451100711084c2160135210b019640d96072610040700c0344c3d940e01c0039030b0b0503e2906605980482004d84c80c061b11f024407031016100641c1680b0801c940c1301c15a44408115a241003041002500254800018604003070040110b0b841d18149111f2090f480c0802a4644036808102c668000e07905503901000710b045048501c00901401d146800300d14a41803041c1c0a150b8000c5109040300c80d207407540c40d01901d454880d81d45607840d500503902c4076840014200700094455200e01c003490701030640700300301c4100001602d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338928920 1250 338927670 338927707
    0x70b1501180801050108070e0108030f0309010b0406091a0105091e0d050f0f300702010c0212010c0e0402030615030a090606141305040321020705010905061e071b0602 73
    0x1200c140e035680d130045c005032808100c3c02001d010b81e0440f402c00c5600d0504100ea49108075100c4020302c80c1e012011414030725003500718100a9100070000d0285c1622003003c4402848000300a40e0180d5241c03909003020f5024004903a404240a40955400860440b90766041252003203459000010001403d010980a021035600d42c201c40d0007402081c165a200b807032a000041d40c20b601095040e80c105c60042080070040d102400d80125007c0c0c8960703442c001a175034958482d07006034201c01030421003203c0c00310641c400b40c242d001545807494007001800500c0101e00040350b9840d0011a401c030212050400c3e20040c552000b050300c404564414030359900d00640f041c07030b031040d451001c041c1014180c5203000c0703040c60b9801c080200301700110f1901e5200140f414400303011000d10841170000741c007140c14050301114071058210f002441003000030b1410590750791046503543c000e0ba48010081549842100e01c0c0c501414207550b505110040a00300e44041c842030990448119070308104621644000c002c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338930170 1250 338928920 338928929
    0x90c09021908180a060e030c0a031e050315120a0507031b2c0606041a03040c0e010605071b17070303030e070503070b0705012717070b150118 62
    0x240814003501100c0070380205005000b0300075910b0f00c1c156483d4890070029540c400560481c00120f0307902c0242050f00c2c294442c0021090b014003d960880b0289034002410744000340464821113075080028001b115907001c180c5000b40f88030440100c0c00385524000034124142c10160003900c0342521941d03504c0d0716002d4541d00845981e42640c500782d0301a0026028080200321820525418840081d007400c184100c0140d0168100481000b00d050380c1c440405440103003820381604031804240201d2180240c01c1124200c1c0e508040324804542c502586400504030b80326503d42c10f003844100c1d87d446406401c030400016400010240024417078406e40150140b1500321030103041c4c41030a508004003554421110354080d5441018208082d07103000900a0840300030080007501c03000a45805805448105a906200c45045101e0003101daa80c814a81142d889070940444048180012040364010764038041c02101c400b100040c0d100c01024040400d16005141c4884500455544102280e201e40c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338931420 1250 338930170 338930197
    0x4050910060206010e0f0718052d06070b070c03030b060a12050c030106170c0c0303070819060f1403100507050703020105060a0803031b0906030a0902100e13090c0902 73
    0x2041001d20740602c0000d0140c07a000c0c60011491401414050402d9000f600310400c102003046041020240c64070700d1030140000420714401c0035540d0b0b08105d00160002e02180c003c540c801e0007d0603900c0c2c00011100c40a500c00582c800c26a03030100180c3d0408285e20b000d800b40b50315080b46400694980c4000c01548901d85c45603240c00e480962140b08441000b424a158554200018040d0907004505100c1d200714075050094543d0310340f4030042140c01104a4901d0030311020060202c00d07904030300d8842c4110800d801445500c40240f101400f510350030b203e284032060000300140302410f064500b0381101000642160100c0c40c040c254101100c1c0201c5044000590200342d85003015030a002c0d1603001242154009242810090416107900c800781610084803008032407014107140d44000e075020000f0003000c4c140c40303280030b580e10405844034400486c0300d8400c00b08070300e40c090700800220780c1400c0043e001740800b805041c804401010142010f40341c2e52419900014211028001452601d0b01001d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338932670 1250 338931420 338931451
    0x81305061f2402010f1415060705100b09091609050705130806060a05150301090e100c052a0d110c0409150e070806040f060e0a0c0f0807080c090c040509 67
    0x144000d08540031060504059070601c00303030b1801803045806d641d030020b0346c4641180f00803039031400184281c890040e00400d50700410629008103400c5610280800b4402e5524104507542c6401281d240c05184150700e001c410135450a02085c4c4060b4400da502802e98280b45207091181d6010f4144810b00d940310101035031141d000c0041600309038441c1c0005200a072007800147c0304880c15a41c0d5070005000781c030141c40c6d9400e000e181e548800c00100d049003148a20804c22082d060344001d209a004003c2d07603184414138403070f41100d61010030245042c2e840100c003400e0541ca1507481110340040341d0b202000c8a114112480307103590340718804d00b0300d141d00c582621000100c1010304070043e1000d00d8140c06068011450030801440301140d9298400e40c000000c290f019030900c2e21710003c24001c400403100d44550000101003100c21880302c000da49040c400c00071620303501c00c0c40d10f0b903a445501910186410000d00c4800c607051080320300d500f11000d2180c5500705601c840205024800c00c94003400c50103c001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338933920 1250 338932670 338932739
    0x90e090601080c100c060203060105040b1b1c1b080c030d06091401031e0203031c0506010206011a0d0e010204080d05120f0f040f1a16081305061f 64
    0x4010b408143c00c015102240002c010f564040c00581c503201018004940020004445a12950881c1c004d4503010f003041d41c49020191900c1320703035042c410f02d4001920540341c00d52410a40103080305003010300f0360f4030080a11a00304940300019032170718003200c4610003400301d031511080c244043e0641c01800480020700070f24214903603003550424200001c440480074014000b04020503c035a410003000c01d9814030307041c02e500c08680b41d481520a402004004401e412035030b4a07140e00040d01891099084491998881e400e06641044075082242a45001c1102d00d0070007106800c0803400340c4240000505095980704014200009004200d00084000400d03410120503203841c9604035800d00307242d560a2601c440000303803080020300050904504a80c03131504115500c046081c0c11810010458050f00704250f50001503c150f112190120b0300a40005004041529060300c41307a8001e401480640c6440b07032090101101e2140d103022084031013001082010f1138008800985a14444150031403400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338935170 1250 338933920 338933923
    0x20418170a090b1308010c0e0f10230706320903030714070c170c0d02030a060e070e090703060c021b100c1707020315070915090e09060108 61
    0x9100c128180c00341030042032440c55000200d20281c1d8400c00705541d0310840303000c180c103c2110f55400000e4560802c0c000b03800d00743d070103422402018019510115001c141030108185125502540b1001442841e80d000010050500408540d1060804141380031225202c0800395100c0c903010101130b01d090480382d007217100405a011401842c50005540c2c60804844031500e0f8840502800c0401604103100c1811b003c040e411600000ea00c941042c0c1269070300c44070450149602210f02003640a2400c56100d0350400801c185541036008000d04405120350b900d410050050801200962140c0200890701102c104106809502290010305c0030354658544203007070760f0400719544119046181c0c03080003100c0300c0d8907040060300c088031441107000d509c0008032170840034040b003d0140c810754503142d001040c0000040064030700903016036621a503d000801810041622404000345c5070480800c8803081c2c0141940007030517103242400000d41d03130345410420800255039a82c115017041c4010814442c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338936420 1250 338935170 338935193
    0x604051009050a050417190e0a0902030f0613060e0109150b0a0513060c12080c0d02070804030611090a090c1e02010507030e0c0303041404090507170607030b0f06090d020418 76
    0x1c18600f028907004d205140b1020b002c8410551f0414032880110012003507a5034401100588000c45046499241c0308400c07160100060300c0315405040341c21881c10810406010308000d0721070300e102001241e40307480f030491b005100300c00380080c501000040100e0310319a10001080020765030359480342c030341545c12403030760102e4801d510041c10701140749400d40000e141e090f1422100701850415100903640c86041c4d400d10320540040c003c030f1601c0001c03550304104882c006002a217000756001c1207034441d08516203d1034403a180e5010340c4005a08030400000c00d05800005a00c3d015103086020307550580241c00711715041c1148480582d4580c010040119410b100782c1306208101d600824178070a9510100791244264042e002101114100310f011540301c5800525a8030740c0202140e142c80d0303480d0418550311850802006d0b49010f0b00d000308916034400e0040480b00c040040081d0503101e40402040802d502003290550001d1802100002580c0d551040344140c0c0e40089004203007140600c0c00d0018dc51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338937670 1250 338936420 338936453
    0x30c0d030b0603130305070c03050607110f06070206160e0604060c06050a1b1805060c010c1b02011b020120161208040306090507170102041412060604051009050a0504 73
    0x4100380f00f0003807407038013a00d008401640c060415981e59900e90801c000e0004140e0030150031842000e00344900241e00c980c103640318852000949080012203121f140d00c2c0c040940d80784005a00c010003042d000345202480c2100c154035800c01d180803259110215100e5001513108e40003184c040c0840e841444100c2c0a0190700c0001d00b0302c100007030760300c40195000c400f540c0c000940c200f00000c0305804110400012640c041d18000703054544a540c12040603019002c596891400a442c00c0341c024a084a490082d40c00c603607050316540c0102041350b447c110042c1d402c0406a0401c4804168043c0120450204008032004c0002030201c5038448400e40d84600c00d81da1040e001d10341c0341c0c0300c0000403070086030560302580c0d0722090200e520303403544c10700d641b07042e070030740c000c0e03400302030304100d008200c40301503005000311000391280c82004008170042000280070340c0c031100340b281c01c014005441c620b015400a40c0c031005904044405a0310346404031300300d0758121035050413140d07210248414030249004410b01c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338938920 1250 338937670 338937679
    0x90f0b0102160e060a050901081e060405061303050d020715060609030308061507051c03110a080414010f0e0303011415072904030206060f04060803040506031503030c0d030b 76
    0x30000c40452000c402c0c892003010400f50b8900080382c0c2c16510b03815580c2c0203010040003050b8550711484116198401c040907107035500c1610f400303030040d84400310f18144207a80080281c0750640d642401c80200d910260411030400c4010046120000450305c058042d86008040800100c207100200d002210796503080710082c400091000c0000a500040442d80960300b0b90f0400050780c10310020700203d004085004040b40602a550300d0580034000c9540c07900b080700c0d6414001c1422091100005105400c19000081d80b00400100440c40c04010845007075840000040c10401111046007201d00c0044045005d410000041207204c2d8200d5100c04092811107406264034640000141e0314031440b00020f04c01c1844140c020516200c0e2540401c07541c0b2138406845481c03505280003500d03241c0807a2007030b2051110107654801810544901e0302620120f40095140074209010000320f44c00081c11910381d858201002282034030b0900c00381c486212040001d000c003034000d00018080d5030503000e485008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338940170 1250 338938920 338938933
    0xd1101110609070603020c03070f21030b061822020a090510051b0304032111010b09060f1f03050f01270911090705040924210c090f0b0102 61
    0x70300b02c0810007074100d81e1a410300603070340c449610040f41580948403000c0c01c003216a0564134103001070084a0034410403c00b0450305000110391054084503c940511a0451000e0103009800800740700c40e10f80b4540000c0c9454014804112a4004082c8000482d05400d0700441c08100b030760303040080074014040844c1c2090107800800c1004007030f40280312582c102105001e000c0002c410003402140c000d10f030804207045003140d207915681d103451058000007000a1110303a041d591181c0c180704070b80700400001c20403402600d4403401c021000c402c000d1140c2e1f0081e00b00c0b40d9151004c500d449284240100c5880c08038107843c00c408001d080460580c000700c01d4880b881000b1841501c0100c0459500421042c009030031030a43c01e108503a1031800c0072091300050080c0a21009503003000150040350426242486480310100030803401c02c2803454021502c644040d8180300d08084140088524602e404c07802035050340c0764a584c405c240d403031307031100030046d50315947c80031400d030240207400407102c00f0b000a012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338941420 1250 338940170 338940181
    0x11010e0c09040303020a12090c141009150e19080c01020319080703020c03120108010f02070503041214070f082406010e0609030d0203030f0a0b060d09060204050d11011106 75
    0x1c9141000307100034105540007699192880c0984040a0a002c00c0041013004141e0743c5408200c14595000e4440c000c1c400c10745540c0c491401c0e17080000310851700d0760340050543c5031070410a403914283d040801801902101c1c08100d41300c6040369001d448000300011685494051541d061401c42d182c145d0440d08104000c401c800101c01c0c2071681103500e8600030205e503481c008110001c1c06242d25242c2d180c040000c0406080403644a20b5058842540081205c03804480d0070004920841600070400d42061004202e0600340c0c00a444110b4080c5004104580c100c500160401034903400030810300d80003203400c2c0070034241044140064043c031426600d0725000450741003001240184001c0c10044494411202c07502c0d07400170759401c0c5d8000b0303003110181214844040d4490b0401c440c0c41c0f1244d000400040c003d04014040e419003154098903007460515500540005080c4190301652030940800c030000711038850083c403d802d14010344c1034034912080303a4001805252107101c0070449502c403005018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338942670 1250 338941420 338941429
    0x17030a020a0809040b060705030714030306220603020402030f0a0e03090109090507141b0613030e01081008060f07030507081015120204091e060e0a050408091011010e0c 74
    0xa90795042060036440d1098500081e000e0621501d0307580d04000041074444c00c1120020240c83c034103110b08900c5048901407642c0c207950b4001103400a40c450140b20381000d0100118050200d40035501001040494580e00494203a07402a81c0109141d44640c00704840748902d44240500d0344800c0c80654600100040000e04080190041e80c0440d6070340d80200c0c1800e80185110b0140c20203540c0029122800c694461030010b0300c969040e60340c4d0050710000360f050302e03c003c44040c003039605442d0711102d070300316030011140c80d80e0003002840c2c0c00c9d201107004a200c180c1002070900c07071952180d2103a01c130700c0e00d80d074001c0c107458000c1d000c802400100070501007901031010203541642e0450782d6100b45511741003421140425a4000e45841c10303c001404600c3d43c4113500454020052201c100140d100c6c27000f40d034021a5100d1144960025001002c20360b9503a0320303000300b6040390007500603c0c18207100e20b000804007214840d0541c049a20103408070074040c0e0038055035006c080300101900039484a5070114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338943920 1250 338942670 338942683
    0xa03020909010e1209010e0312040618030c0b03040611031b1c0f0911120c1314150a05040c0c0f020103021303050a1703090307060e010204090906050117030a02 70
    0x9114600420001e0310a4800350711202c40c1c400c00800700c440001d614101444554000d200841c0020080c0b251120320b0b04000401c0c201800c00b480025181900d004400c4450020a0301c582c0800821000c00002245c00044100c0160500c42c10050380c0f4202490008211032211168080b800c00074001c0000400060202e140001140010a03554030170285443c044010640f02d440c0f1002d20b0103860010b80b1040c1e0340900039691150880050300710400f0100582101200015607083c2e0107041c1c401c1040c20402c071560042d00c214034010801c0c81c0d40c0c0fa1032035401501101d80e110744802241081c3c040d0700c5d1181e040070060000365030400456000f020003c0c0300c83d0b80380d40c2c098840d1403070000d100c1c11a40309604031151540c1c4280300040039526803502d90b850306041c0e00305844d02c0c0502c0100300c40341406401220301078080311001b1480d00082d40d48210217000d540d0302e1195a035509010010785000d0724000c17000c0080c803c80c8009070542c14540841c203208000071060036035600900034450410f8001452 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338945170 1250 338943920 338943923
    0x50d0e0402090612090f01090b040f0305040e01080d02060a060602070e040c0b071410020a09050f030a200a080106060e01050d0b0a06050306100e0a06051804050405070e0f01050a03 79
    0x180022180840464040d12440c1e914a400810004000800b140000c01e03041c0251040070941e100c08102200450a80c0c201c2e0380b02402c1e0a140c2c1021400082c500301151011500c64102142490303991100d0107600d060076402034449800074051074142c2c640c14400c0d541c0c8400d4240d010020281000e00c02596404540602148198000301260501500024110040c500d461200382e848110346480784202d400054454128403c00f10034080700d8055000390303880b01780b0075503407905050710300000c03c524080c52882c080e0301401007848074000720f0ba041c03002c00c202a090410511b028914441804290325141d80842c0341c5074075007842407081c03036072002110b0042003003460455114841752a00303400030010b000c41e055011062100014540d5040409144200d2080342c0b130b003410245c0c48500f81c2e41004010502035110001500610205004001601c074100054903105003298040021030211802900c0c10759141d07028880030450110902201580304210042007100b13545064042008405035000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338946420 1250 338945170 338945177
    0x11404080307030b040b04060f08070b0915090d0203010c0305100e0906010b28020d03060b03280207050f060f100e0c090d0f0b100503031c1d060c0c19050d 68
    0x2c4c01401651150400e42141078010000c12056540703605078019003100f8450074142c1d0048030320020b1004040c40598110b120080c0045000c54400320f40c000300d81d0300050000d5400240c0c1c040c21009618240718020015180307072800034040c24a211000d884806540c007003009010004100001104049841d40c11141d550300c00c1d0f40c40d0314601c43c46e48601480d550401c40170f804658840005039034001000e206d50f0145490030400903407280b01850340da103c03c81e0015902003054514040d802c03220000c02ca001c0300b500900508015050b901c03641848182500b010700d60340320100344405500444c405075001242540d52441151400d01502d4103054000d0103181c0b18034020440310b105403102c52010300c01c03d91068030348404081502d4080f100340c07801d413045400c00e01c1403000480d0b28200001100d002c94071040081459076180e1010714060640c0f4121444100305005075001c0466040213000cbc02140c0342d00703442d40c65100391320300b25150908071030a0110b80b80d5a0f1030f0500100d80d0200302c4104d0385410b4034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338947670 1250 338946420 338946431
    0x603021e0d0f1707030225050904020904111c0605101a030c070b07050d0b09010f03020607020d020a0b030405061f030209070201110310030201180e0c0d09050d05040801140408030703 80
    0x2c0000c030b0300d1494840340040460029844c010540d01041122070041c040c107040040c0c4400f1500000043e074180941303034100c1898400f1401500d03201913000c0d80325125051060f0300c4192203001c01c121001584c000103c210b030780440c21081004070300030181d000704101c0240080c585089000014100c003451501c400740e4000020034404003e81d4110342c04990020444060b90a00c1c00009055912221541e001c1c145480410105071424200316030403605a00540d40e5401d045400f00700c0d03541e0000c0400c84c0c1c0549000310010060b140c1442c020010310390345c0380c02a100d260a003400c905145c40240030400ca43c034821500d07000c402090f445001582e405070b80720300803507079071340c005074010b10820030220341000011040202510004891000b940c1c402e0fa80d42d0082180c41d142c40c0c50106a500038104040d86100005400c00700500c0a07101e030f0030810ba00400e1a5040342c481c1800c20117444e414a000480000d800d0009032002d0050054003000b8821044161800b52111402404040c154008064491 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338948920 1250 338947670 338947673
    0x110418020c010221091204090c17090102070b131a06011701170d08012301140a2c0906010e0406030803160201051602030702090403031d010603021e0d0f 67
    0x1541603600c001041c000841d81c2e00000c02c683c1610000103019120041d6148000a8814002081c5040e08240c0701c00501d0820707051805250143c115040e00004000c20200344544810300f61084a0051a503500016954101d40c10250f0038010700804040d00c6071402c540316070000c1d444450b8040e16103003040210700107485100c0102e03402caa400e0410135048680000100d210f4801040c8a054421100700b22517402208500603076031000d00340300316610700000721441000000411454590386005141c070b80e5294401d90031060789904002503c20000c3c4c44c407104880100d41610628100a0030249110a03080c42840041d0b40f00500405041c10096002c4c180c00385504c0710342055000d10761200f0256107901d01840e515006003c40b0103050010342c00d21000c9100d040300b0150282d030503078090340511700d02485602401200140038201301d00700b580c0c0b0204403030700d00c0c0c900a50460007455000046822071035801000281c802c0c005174a04942c022006444d029501c450f0b009182a900502000391042c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338950170 1250 338948920 338948969
    0x207120818060310091514090405031207050301050109060c20030c1201020904061d0c0a0509060307050703030e01270c08060f0f0c0307121d19020f041104 68
    0xc4071000350001c101109008800404c01e01200581d43c003024100855030756520315011440e200e100d1000710b880e400032106070604202c20807136841030241c0102d03490055401070f03115406d1800c407610070008a01000522043d03901440d55802081a45046030380035005860308041c0340310061042c0b4844192400e50740040d2030900117001075003002440c0a6113904035900c1d90b8040d501205500d44150f1500501041140f0a02c60071b04d001c901110042c02c040d592820244081d5020020340828014240f0000c1c04985c2c070308000354861906907a42315107038000781c034024003511814415075520ba4140035201126201040d4100212164440040500d0506041c041c0e00701440c1e1b040340d00320b4010081000310102c04118014010240b0041e505a030b40e076800641000360105650020004030f4441e40d0515a0300d0036040600801f112040080344036410003001454483c00990050803a100d80520009615040d83d003078100c50019181440900050b0308459581c0c4581d000700015a10342c86c0ba140c1007003d0307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338951420 1250 338950170 338950207
    0x1501050711060d0f0b1c08030702030d09030f08370f0903030207020a06020d051801112b051608070510050a090b010602031201090b12030315010f02071208 68
    0x1d0142c0201e43e0ba00e403205a42e00584403070503860b18414107141c40c1008500b0040050743d210362003800814410b0070259194082540040c0c4542c00b148004c1c00b8202d400b0605204280c0710a120b038a40b6140c460304110041d1030310a004180c00c0c050700103510140e84058104c880f508070902040c4078108900b404061140003000c011410407070321881c0c01c400000700b5406500400c6290700807142c1e601010f5a600c4100e03651918041c3c900e001900500419040b10b05d040307088110b50005060508001c80903103800c600c1e000d098400c1071041000035840c4105004c040510004045030740c51310524000841143c04050017288600605000f0000780030405c0c40014004040500d0920105001c2070500000782800340c254030b1010b861303000d450300001424500003c201c80d101111280c10344000d030320341100180203010710f022183c0c1164108103070301c114040900045100b644c8a2403485c88800d5107d000404448a642000307045d503010500900c0408411242003000b00d03841030003180e403180c98002c452110705 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338952670 1250 338951420 338951453
    0x12132105041a090f0d050309012609060709080d1b03020705120312010504143106020403060608030a080115020c0a03050c1e0d020111120703090f060201020315010507 73
    0x8030320380c445844400c180b8005181c0a541103828a0304010707110200021050169801405c60b401008103401c10f5004a05041c3c4001100c0011024180c0c900035001c0e01200865aa40954024008202c040d0703030450300d044080c2200074000e24204443c450040e24a00b00401c0c8180c1c584400c80e414402c26208000160241078090042a0b1a1080640b03543d030301e80102c04841c10780e034209000800c0e1800c041c8200c0a081c204130102c1405030f01d40300510481c58110460800e110300494102d84200ca0049243c0e000d46072103050016612451400c1000480f00b543d04180074981041160b10003c81c0d00002c242e06540461501442d03034101c09106070310b04464080c0307194001c3c181540c00010300c50302140780d018004e019101c000386552642d24010001c11580c000307550114500390282c0240d4405c4200c48038120069044840c1890016034115050700100001c0300020301c0480248181041032135a14000c21710b9000030341c254140716aa56040c00004800340781080800b048010900406000c00718012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338953920 1250 338952670 338952689
    0x304080111030108060901270f080a120f020307080402060a0c05060106081609031713030f0f0c1203020304090b060d0e01020310050111070909031e051213210504 71
    0x81c0020700c10001d410034400d042c1c8501a040c0050312010041c02004c034003091960004002c2c0080b2581c10030000c48805050301d08178100360645000500d004010001d2001c3c0e40c1b102c8180c590101c00900c02c0d144010b06034144d40d801031041c4114282c000d02001c1e0043e5045407016200d06034544100ca501125107809003091107030200000f10260800c400e540182441d0800c10704200482d01d0544d0b0303102c1944001003030183e07088600d580700813143d8040d00416512803e20a60107a403602e4542140101c0102915203400300e0b01d000080003520126040102040302e00d40360800401d4401031341300c0c0100c0c4601e0344200d0311000c0d81603043d0f842c48225121144410720070004d2811482c900c5000707410485400c5001c50001c0d0001c03a040d0300444070f4401c101110002004141d08141c4254080c01242c0f0b0100c041c001840b11810041003202044990415542d46c0c42c0d41300c00c0000e00010031117001030310380400d28002241603408a21056031400001d04101015550005003100464003881258000c9445 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338955170 1250 338953920 338953931
    0x7080721030c0c050a02120f070305150f13081602030a110103050c16060b0103090f05010c03060b1903050c091011160f090902030106030b0408031b040b09090903040801 74
    0x6409103190308a90109680e020881d86014a600b511038103980c1c0d1014101e03502845580c0010700d0225030000139a07400340c041c0e5403600381e051103840ca09aa16001100c8640203070841070000c2c5000020305500518400c0c10480c1c0381014000304040044d0381c00041c09004001070703035000340040c00c0840c020307059015040350062055400c0c1510440601c1469a00190501f0040745160000c0c00586d03140300441c5203848403c3c00e0319070301c020007018404081030500d42c0f10a40b50002c41d0044030b0b02c0c03200c140188000b04040c50f190400504881040e040504a000c0500102c501b00b681c40400d0802400300341000169078880094014460007481d035404c1d40301541078420943d05070f020300215800400c000884595400c56410320a0003c2640100a00214801800c004c01c180387d40000ca01d150010300002034041e180c0e15200a80d190490313013911640d000006201d1480a181c0340c8855043d078005203241464101000340c0d61f00d1140040e454441c074040e41c046410078a0a10450f001030070070340001c014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338956420 1250 338955170 338955203
    0x150c0102040f1212030528060b2206020604030509040b030c0a12140c030309150c0607030209210c010f0509060414120328180801060906051c020402070807 68
    0x300e55040400b140c40e1201641404d030b880303010b800f0b071900414040c0d8000000e00a0300900840030b908104032404541d4070b8460000d18495503800800021001c080c808649006042410301400c015078401004c5602040401c00402d82c00815107480071001c83d4041404030034640040e160003c003d149580c000c180d03d0300022010007040104035400d2080f010001401c41c500c1d4029216007529002640517041084094000e00c0c12441003030f80e002804423141c0c01c00308040c502d107150090480305407001c80d80c0000d1000c1c44e403070401200c480810b44c80c02c0300004981c05414490702c80c1d00e22036129061151444076003560a00400c152510a038002d001c545e211991014400c2c0d190403801030389030103403404585201c0b030202c020040340c1069038040c83c5500040c6a8001c00d15000b41404000c00400c075056480c00041380c40544010000c04208002140d05401c0044103411142e0b103070710283c0704802c00034184958184032000090714940455005869000c5400c0c000298030070700d040100b100352140342000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338957670 1250 338956420 338956439
    0x60803041a160209091005040605010f12030207091a06070510110f0301030201050922050106020708031312140a06020a1205040503071113061205120405150c0102040f 73
    0x422100d0705501c111894400e040c14159510455420301080c426050001d00541400529540c0182411040b07500040f1040d164504568080d201140c102e03488000401422404030140009400c402586c10072114607598040d42da9800f500c41d800185031925a01009041d200392411204240070300760701e55841a92030240d4940346401d00e88a101407800b5001c00c1d06140a40a8985413081134041714179590868005560070f0300a0701c1e5141d0300c102c130342951004503d03100116041c40300404901160743e5043c610040e0411070150440781d519402805206201d4007612071440458029820100001b540c0e81051064508031906407040c40c450300b0188002c002e0540c1c010060132074150b5411a0002680342807070180c0d401901d000d48a03134000e2299a0104034691850350344030b500209552400c0004541120607608036038043c2d00840a0340c000041800000d03c0b880100d03d01c603000843c541800c00000441e4080c18028100c40c61101040c0c064051a00754121070181092001c1042c80b65503407454003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338958920 1250 338957670 338957677
    0x10e0d0c051902030a030305060303210402010f020d0c03030510080d020706020f030a120513051606020c04060e010b0a09180911040c050d093f02060c040b07050c04060803 75
    0x111064400c100002c4004411100b111801550090107403000e0802c0da2030407000b0380405072416074540400c10100c02854508500504030b0643c0e00b99050b0203242a0001401c00e151880030603040d5007201c0400b01440394044240c6014a9142c00c00080640700c152a03003050b0121900000800c3c0300d002c00c840a9550001410421031f6041d07802c071049a040702e5041e40e26805040490301c007140e000441e102c0c4400461b0081781c1e103c040b07071003d2880d03051151101482c14507102c0682680342500003052192903030600c42d8aa240c0c205580500400e8903009250417038160500c541c190206010031201e410710b02c1000701c0c0d001007143e4108142080e00e8109003000926400000700c07000c0800800114003401c00f4080c55a2460440d21500d00b0414105420340c090541c00d44219000c400203880d07421515000c1d114002580410615817000e100c0f40c8c030100c03002105c2c1440d56810b41d4042810420050108005c41d4180c0d51000000340c0c8668641c600a45050803596a0716845030405401046008001014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338960170 1250 338958920 338958923
    0x1d030d0902030f0706080a0e0c0d2d0209060103050414010f05010e010e07020607050d0e030f0a170c03040312020d05130b1008030d0b0a1505040503060c04150809010e0d0c 75
    0x81e211048400f02543d81d6a840c03501c9040003140c100ca000600f0100c0f82ea112286142402c0155070841000000040380d180c2d07044011181100441d8605040d5214021165100d0507005507456022100c7e800003201a140200f6032410991104005020003264220100c6082441c0c0000e01250030b14071540005003a09004060700038185800000d8030b007408846160060a40790040d07c10b035120b0341000c45d0603500510803504440d0315403404100c00c0d40d04000820940b42c8000c030003500d41d8001400101402e01c01a8bc401400c0e03c000705000703854006c0012280c00ca40d05003030000b401080b1401358000b90182c085039000c054a8402001010002112503c180e14840c1410302d041703035078202414511065901910700280c0c0144042004903110340d003c06803200f40140340414003585c85d551810150a6044644000748002c1401c00581c00d041001300d4000090762060b034100b90038502c14682d8102980b4640c010040083c02003100b81c0710a5200f10168914441030f1503a03040b82a80145c00c40402840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338961420 1250 338960170 338960173
    0xb030702060703091a0c1e0d0f020f1c0609050901050f060102160501231318060510051c020c030a1209020603010e0901060f090e0c0301060e06041d030d090203 70
    0x2480b00da110384101e485296000b03000e20704980052000d81400c0c2d000600e10400a00b007045242030040651741c101060790003c0e08895610f0207600c085c403065424410184001a0060141c0c41d5500e00c1d000c1a19101c00e940c182c4407440c4002080c1c60760103082582d004160301850038061040034141900001e2203200c03135201d000c85507220f0307400490341c40000941c48000102d2601301071080d90312810b04022510940c4030b502c0c18644088950340c005520140a88000c00c400007420881d07540858240e80a10090640070008545010b001c61171340c01069500104000c800182c0e0440b00040640000c403e614100e81152a001c046426079a40c5e4000d0300c2440104a00403d9150243c0050150000c1039a0107455207007135074602580c98445001c040e1403c00e165403107400c0031440100c1d24403001e00030980c3c201e02044080444031441d0900310320308401802641006028014442c0d01c020041d080764042d40c0010b15900400c00e1a8409840c4601c2608540000103608046940d80c1d0020080da030700803030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338962670 1250 338961420 338961433
    0x409020d06150e060d090501020f0a0306060215160507030c061e0e0601080304092c0d081503210c070b070611040612091e06050a05060d0f0210020312010b030702 71
    0x140582e141c442d06007000d071340441e0402010440b110160404403005100702c0000d420b141512494240607003190700018006a6100030400003158100464a650799403804810b4484c148811203c82c590200440c603030921100180c00310800d03104007501824150804400c000c856848501c45e04c07a01070350300e10603080d40d04105850b0403a40c00825505e0403039854100452401d481c00b12034601914004a00783c0040e01c1030a0640940108010100c00c881c0b07001000c1e000140303600001500c0c0c0c00000d8800c0d1a90890f0403102a82a1400100b000600061040c600740964084480011500ca1a000c40c00e060003a400005000101000a00400c5202d168280304025100804201da40114810500029641c400290141038103902030203405000e0744044140c5c07660301d02010402075001e0303012910140c0c1c074400c004850340c0920415030001401c841c0d4035000c0c0069210840e10724250180a8032440900e0004850701e40200100d6200f41819003218441d50303134803110041aa001200e00502502408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338963920 1250 338962670 338962709
    0x1003141606022a0d140304150815010c06061a07140c030312060301150b03061002070b0706151509030605060406031e0203070833040c0b030c0409020d06 67
    0x807550f400680710b80c2c00c82440840c8405501d5001d08003940025800c07001d010742003804140040d0080b07070091034000003980d45500e80540c10340c428501d420358104002d2820144200e00100c20b8440c901d40d1000d2815140c090f0003400d054009003402d0f440100350100c88040d410346005824003130102180280281d01e810320701500050b840e50304504034541e00d034008020b90800c0503202003150b40c1021002d0000242c49204c4030061101e503805402c101203842000c81001101d1034048102411403c580c07000cbc1502a142c82c007102d207030f8001c0d20342c01400a500c0740c403813540c2e00d01001500c00c000c1650500c0103015016110b005000c55519000079143c203801c00c4000340041c1418001c0008a03036011030b0080303a0301d429030704018501c0140001241d06000c0c0c50340003c1c4140c010002000b0b0003a408083d1649059406100c0d0412030700b420300503080d031100c40100f101290800d00d030301040f140901425640e07503a85d960362942520031034000d04000c0f880440c602d42820b46950080c4d0684d008400440a0f42c1180c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338965170 1250 338963920 338963923
    0xa02090a050906012d03030302070209090a020604050f0612040305070302060a0c0c1112070b18031c050304330f0b0d14030f0315150c0703020108100314160602 70
    0x200e451021a90103c0b004019800d100016020010504062101c1c141e400501010035000d59500980000c2d8020034170381d09510700701810b542c0010444c4001c140d4021283d010a07400c0c0142d03c2390512032850300a0710343c102d172078070b070121a15104000c0644829150924002e406504405030a40c014440d9400190480c405840349200071100c0b6200e5140c0c0b001640d85652314501e01c000d050360491400280c02c514080d0410070b9801030052590815107640303070141000c0c041e1030b054800c184241e003c0300b03201c024103841402d941c0c2e48520350315026669a84a06223010b150b0312440c000303081c002c005e031000d8050041180a0160900100c4401e10140c409503c6240c00d0312052082203500902840040c00041c440103c0401901801c07420389040c02941c40003651360340c00445900d00000c00821207c43ca5180580c5001403182c440302c3c030ba07400c040304094259a9050039001c024180030000c0d0100b541c40d141605080c00030b540c00324038240100780c95a055074a4814180c2c0e1110b44592080011404500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338966420 1250 338965170 338965181
    0x2070606080c061201051003110c0d030e0102040b0409093801062f07080d09050405010b04120b04020f040f020a0f08010501210905070b0309100908030412020c120a02090a 75
    0x725801c4c07800b43e039007001c041045a1400c51810000e1503660002445408110409031000c01d414a01030004851240c130080c0a0b50407000c1c103403006903c1084280405518142500c0036220100000542c4080a180441884500840c640c40009200c0d850101e08000303028090010102031001c1c03001640c2c1c0e10030540f00c02100e10000c0c00c0c0f0303024614a074685403500134901010f000200080f200d42a42d600303452810b010701050074500003043c500040c00282800d024141c0100f01380f11400d86030134581103512041710b1056900500c0c048109000c1002d5580341402803500c040010402c02071056081c01001c02540b0444444001c20000b0805007025402030303000d50304803101030f1121502401100d42081250f54804983c90810380c2d00c619041c00310740100140d001420120f08099964146482e8503464200b1070205241550700700200c0c00001801d0401b0750f0f81040d0b00c080045040f40c0d0034401a81820f40e00102c032500710105200d42c040c0c00a00080c0c00c89541d0007500d9440d115103030368110005552 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338967670 1250 338966420 338966437
    0x81e0306010801051e09070c020111060108061f051908100903020d03091707050618030304031e021005151201020c1b0a080709050106110c130513050102070606080c06 73
    0x200460010130403401c25916086400d014840740c011241600f500142c01e00400380c501c80b000910404000b021560401c003880b41c110300c544020710f01585040c200c0c41d42c90340300030001052552020b1400303c12803010180c107400b41100170074600c01580719224001c5161480e21501445208070500301c1e20007286481458401c5070984c3c090281c2e0750080c403042e0060104d542085a00c04001000a407420401c940640280d610540250841d0b09110b0502c00041c4014083c0e1a01c54104009110003c0d0b007040d00041c41d8004100c9245200c41c102101340e040c200008403000d400d905100800a0510301c903a644c08121208a903180036407040761890078203c0c0280c1d404d095907036000100c10360f5410040c1c0a51046034200030940f10f066a1540c49a43c24032a15500c42502c0d00d4560727006024094009903c0706449060b10000e01c0d440070580c0004054002901a0180240c0d0302c1010401d004003420708811311b541c2220007556034201c5450032600070314aa100b488400d016685d0452034510f03080c42250100e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338968920 1250 338967670 338967677
    0x1030f090213021b0307050307061407052205091003120207050109050405040606051003020901021903051209010e0a0c180501030c0308030a020702041a0307060f02031b010b03060103081e030601 85
    0x402018200c20025849500a0b40e1041320a0703000d112003480400040c69981e215034091604c589580c54080300b80c807105071886007140c407000100144294840281c0344c40100000700381322130701c4588041c40c0490038150400350f0004410410000b1822000000703104480c8104500c500080d500c5108030384400a50141a0000382030b800704003c585441d0b01b003d500b0502030800041d20f40e0391000014108a806203404011a4002c66020031568040c0100c10107102d11041940600314241e500808500c20317111b2940c10f800042c0045480150250b10000203011041e048602d240c50703030b042150302140b25114646003210b07040c0205410440c18090141240d40c817120002145003140d988043c1c90f0001458502410350900520001d69290b0180d403e50014403410840418110030616003000d4403034210b00c050281102c203040d41540d001044130144c50100b103181c4030365000190102d0142001c0040b0340c1d89485100004814024248010480e641d850748101c162841d2116009006000485241307010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338970170 1250 338968920 338968939
    0x6040303120f021c06060302070812100b131e0b0f0c1204090c0206150f010c0c050406151803050a031d0d050c043605030c1b01030f0902 60
    0xa004955181d0314544440340420705855840c016000c03a041030b540e11a403001c1c841c21411004045118200140030185010742c6412582d883c1c507000b6114040e400c0e0a804100e600084001d03181c4244000901044062075a0301e180781c0f095111b10704800d018000c8001c0c890800303900ca81b8030142e02c503012101000307901c0e4140445216000026000818504240d000310a86045c8008261000b000a09403000c800200750700b51580084c40d00300e0040c462000a5070410100060303030388110181042c9002480d10103409034280c41c007490b80030079aa02860300700b824098081114503030042c4c996030440b0740c0d60340d010111018100004040740c00e0b10028003980c100156a00109100d082c02d090300e800100d04120070101c864000c142504100a0f040d5030641080c14440d202c0e24040c01000092141c4000d4002003024510010b42010080c2c41c60320a0921880f444004202c824807c2d10754200c010000e480803103407240641c071810700862092030700081c50000b4013000f18900344178000000f60087e100409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338971420 1250 338970170 338970173
    0x103051009020703050f03012c1506030a0b0405040501091419171b010603050c0111030405040f270b0a0204030302060f070201060504060f0e011202090403031e1d0d020c060403 77
    0x2940221010703020800100518040c042c803040c000c50003003084011401c132401035480380109141c0e427890003034210714000051203e201340315224091031142c01c0322081c0e03481d00c0307400c1c1070001001803008071504182040100b00070300206500c110300c22070054154091040d803404250b81c494031b1100d804140c50110009110105000007617884d00d40c4014aa214504100d0808000740740b001c5070103040281e0344910301401001401d20070200a0102070030100b5030340d40509803507501c038082c5015041c0100d950366410781c0050900d4020700e560715540c14417541c2c090b15141041d50b00f500e40804c141e1304103039030304003042032100301c0c2c801c807400c07a60181d01504c01a16010030030609464098030311411992602c0000c0303000d0313403203201ea0390040ca40248040703121407031714030710b82d00b03812050344600b6403048820011400350310b0307003640f241d44260b052600040c80b40007240b5120b01411441051080c8030314241d4011420321181d03a201c0403c01c90f420403a04a2002d641040342ea035020651000c1e0040c0042c0410030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338972670 1250 338971420 338971439
    0x7080402010c1e170405100c0f060603080a0206070224040c05040609020c0c0a0630020708180a050a060f1106090601061706010203070b0a02160b0604060501030510 72
    0x190058030502d0a0009400c442e114451082a10044220707002c01c1804600100316003070300f0b904d95107814804010306051618001507480c0c0249030750441400a51120801000a00070729400b00e030703600c01d01c02c0015503181d042030400d54000144550151040e000030400141c00000c00c200c0b411442d28455290b000150303e04078600270007820860b204000c04601169656580c080d190142044100041c0c545070300d11441458000c0295006006613846030041c0b1100d9031043c402003e1406d1190201d2001c0c4552452441140000c04e800001c0b0744003140020400c4070b10002000720031068030800e52544080e00030401101000e1291540c02a24890100880e038050f4120704417249480c24960030015880f160350f820000b04a451800541202c40140082d68008a00d07046056010346130303030014501072001039622711440b503019140d05250310009040c001150100d503400a0245a000094001440c0106685006680d01c038031590a1200101d0b00d5480381c410705215402140c1009083c84c40c0c1855203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338973920 1250 338972670 338972687
    0x901050d02030307060c020d0f0e0a091107050a0507090b0108190e160311030d0f05040b0f16030309060608010c02070504150e0103030f0306090b01020318120118060e03090907 77
    0x1240c05010a001810204545d4416001d541515070041d03d03005448000091025041246180c00c1c0304403120341c2021500e80312450b9056603098140040c1060455400d91028010309000400511030b42105800b000004502502250b64030102403086000007001902c0c0210122100421500e50a010380b04541c529007003a45804071410544403940707078100001c02100320720342080d40d40c4590700046c3c003128141000f15140030203080c90504034112801d90700511500c540d12504400c001d01080305020f0030580300032200d0040e02d91070300e8a40020145405006014580b0341950318520340513001551480c10f004101d6507980641c007800d48182031a040000400c0039412000c6483c416090203d0401426070b000c50185002c1e0319000d1a1460b0000000c1c1501c800d50004148181003080c680c00c1a6000802d40714a80f5408629000c20803030700001c00c0c541000704600b00c10660800211400311044d04814840b090700800c8180b01006030205003940d24800e030f0303102c0c9802203481c8002907503e40c0310300c040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338975170 1250 338973920 338973923
    0x50d0318110a0915080705010302270118080c150408070329040f050c0a030c0e061f0504030309080a0302060f040804050d082107080a150902070f0209070801050901050d 74
    0x404a82c143c40750701c4101203981c0e04d0f19850755540000400c3c041c0315020040d000c02880c00340380941c6000c500c8810080c2100c41c2061740b4008d0b02d00400ca15005a01800c040324001030400701074100c0c0303581e50300c140d42c1d41c03910000103e002e2503124065514419000c000c85066030045030092034205e1a5541d841800b2100e0141c816a039100700401d0707041005616804e9000758001ca100040340310050401d2804c0c10701c01d120032807007580d0842d410000200e440003140121030804107004031503560780f408a03806401466103404208106450400625041009001a41e00940d50b071000c590b11010405e0340d80b01e2454020340581c0c00040010554281a00550380c014416694142840d0f40c900124105c442006402c98030b503100444d800035244008404000080c00d0809002600d04040030040c00300d80c4003800b81c0141d141c4803000f00319665403080861009240380c213000c554800803803e140e0303064298400c080344a02c0c15140810b144500c00c40103075050b62001031024001d6460301d0708024403410b48190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338976420 1250 338975170 338975179
    0xe030715120605030d0509030d1d042a0f0207090504110f03030417030d050c03040c030b090a021504090c050c0d030207330f020f0706181b03050d031811 67
    0x100803c1944040c00301204c003c03055128184c540600c078040600b000001e0000c201040503101c481d220080510401041808041d50b001a078807018281480c1c8105c0f0341310781c03406070382c0c051403c1000450380043d03040500c42c521303826501b0745920b54142c0d2701907480c1590701418000c4040003034041403409030640c03500030b0802401c17280340c07568541052208284848003c4c0440c0c2021510b1149140c141c019558481900074000d440e516040c1d481558044840c00007403c070003003100004600500030428a4101134000740f40f2654000d0070607001030181c0c003600600d5103260a1a040f200102e010f5801e42e041d01c55040c001d010030700c2d00b00700220001c0d0000d19040d503c0210708140040700c0d80440720070003000d0a0020f240a051790894888200b540c3c041840150858410012220760b283c1081c159841c141c3d00640210301c0030001d00844030900b030310705006040c50020b0104420444110354841d01120300c03078001c0d10704910390000298103e40e0152002c1c130345160105400d400041c2c21084400810134000c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338977670 1250 338976420 338976431
    0xa0b090705131b1b03120209041104150509010f08060d0b0a090204060503072d05150703080a05070903081b0d020a06050c070309031e0503030a0506010e03071512 71
    0xc00144071041803402009210b68070101c0100e062079080c4203415035449404d00182001d145010058500c0b4032220140070040841607101009000380c0449000c01c0d00288203004840d204080230f59a98030502c01e01c0ba00384c41c1c00c00310320f0060f40101c081c2e03005a0b5058460301030060380110240d81c4044020213207036004000750722110004016050090048820800010307487d0341904c148400c80d09217804c014800da0050900304008880e80c100071400301c64201900c0001c4403140c0503540f0b1030340d40ba0401580203080544004084c141c46019183c000d00946e10421551140074800c004c8030806e80d090800034543c4c00f001e002003200c0d08010100d0010043e1188040b07501c005c0c446040c1000d8a2100c00143c00902c17800c0e003481054000c941d0400e10443e001e41c9001c2003540d0143c021031180c80010464040b5169000c07a1907050400f2071f00751500107064035620310705281e10341c0007044c049232000d002c04d01c0d024004410303060004e100070669074016109100b401c1380040c1600c041038a805810000c80d1a030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338978920 1250 338977670 338977679
    0x5030a021201030317072d110601080105040b10050d030806011817160503030a0e2403040c14030604080d0608030d060602070510051603091716080f0a0b0907 69
    0xc030707a018002c6000b42d40d520445e40a101d142c00360b02d100904148100603619005440c2e6246480a41020780b2150103040c0c00307003842e0308040d2020351003041d040c0d400f40282c2d00001068603044d086140b14038480c014468050b5550101401060744c0c5000301604028142080700001c1e00844250360050814140000b0070084007402d103220071460f421444000c0d40900c46011302c01c0d0308002602216000c05d19264a45060101180d96801080461010414500140140c3d601d0b10103e004000c1da016031a41a1014000643e80e030507441071301e048481e640070000021b4003118006058178050002006000070380c9446e1074401c3c03075800602902810b40da0b90880081e05045c10030080c4402d8100350b2010500e60b251620203820200598000c0e130088602c10382c880c40c513a6100e0122481c0c00c04911018410601c141070031034052041e50041d01202850040303500c030500001400303040b9151b100f04281040303622404071070b4030f5200909400c881a449a200003000615652009502281280490b106035544 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338980170 1250 338978920 338978947
    0x50f0f09041110020c031504140313051008160c1e060906060909020a120305090a080a0b060616020913052a0d03082202060a03020c010501050406140105030a02 70
    0x181d804840540405540921505000c01846051090790000e480c071031101c0004240c40e1008400b6521262070a80d0010b820040910310907901c100c10f8408503a142c81c603000c803074990651540600352140c02e00705050740324144501d045074807a14090780100300c541480a02540c0c600c9503940e00f182e0006100c0100054000030341c0c840d00b4190302921022030402003d05205084502541150315101d040078101c00c00f60f12500c1d201170488840500c1c290042c070103424101e525003e0000e42c2a44030020043c00100b520300003c0080c021400340395055040d480317010411080788540c206194410000490341009440c2078048250b004040c0103085107400c1581d5195030410241512568500c0600c00a045403c5440400c200d0704080030369110a9a9485480c017034240e050003804e246072003c018007041340d40c00000340c0515140c1d9001e00241d4844001641c05006900f020340c00d40c8581d840c082c0000303018a898060700040751000b40c41c00100701503031001141c0950000341200b004075001c02082910110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338981420 1250 338980170 338980189
    0x309170c040513030e0a0501020a080c0c0a0b071505070806060903070f0b04030c0602060f0f0411090406270f170f0d090b01090c0f1107080f011b0f0801050f0f 70
    0x81c5500080c03041400d0701e805840105e03003078280b0380103003003901c005d122690f000620344407015040f01c880c2c0d40300d070740400340c00d480c10f00018840c98000010010004d011040007025088051144150500f9500d015002d4401c4a404031005000554800301203041402c1c4100200070085000c0c05a0312040d8880c1008101d00e002075000d20030201c030000f020014000400700d01c0c0c007d41110b1025011038108480e03460316006024100c44d002e288104003040402c9007201c00395900e0320313024100321600c1c501401c0007401000b0310a40d0004e8000e0903000203050141c0c44c81d003c0340c0107034804210314400309580c8a8080385c420101ea92452a0300403c541e6004440ea10040d0140910010001c200ca130500d1511200c0b42d0b206074032000c80641010001c9940030b07007007195225141d180d40350100b04440181885450184190300585e0740d4000d00e0b062401d4120103400410b9514403084d2180c01119082c0d40440d54440c03180425000552508010311040c40c00120805600c80d005014034500000d50b00010007081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338982670 1250 338981420 338981431
    0x60f0e06030c0105070309050f130504050d020c0f060d02032e1d060603061002010605040207030810060e06071407090c17010b04051e0613032006070309170c0405 71
    0x801410400c5514007049911889402843c006003051025500a0206881401340d2841080c181c4003c1000d500c070340350b841d60702101045d014807103070805080158a44020950700c10050180010601007410318010900032030310040c021500e02000c1c406282c00a41014000c0d500002074078045807842200517902001e0b41140c85201e0085925040b5443c000c03d0500840b90310011880040080d9070f5111000c2d00da1100c415107040305100c2411108030b00408023904299806480070400300141944280c07903512078001d81104000d0242c079070005580d00741804100c140e000078108011400201c200718060501c0004401b00e03041d00d07456094010517149440ac40f440050000c621800359004104406801041641c40152401d400c10b03000c240789068203020031020b00300180dd40d041ca070701c8800844469652201d003802a42d031300c0f0b2424401d0245d400e190540110882c03001d0308042c1c5451411101020b0f8107072600c901803854184100007464000100e0911070003510409116904ca03406242e1080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338983920 1250 338982670 338982689
    0x9041803120606170105010e22020d0501090203040837081e09070b09030c0618032a012d030e0d02030c03040501081008070602061503010c0f05030901060f 68
    0x3191603414011500c15510140c20442030813241021041c0319840241500d00030310700114840c1c0320b0345c00700d031a147d050703c10070545182c1143c5440031411150702408009029181c203106699a0700306480031381c04181e60241411204000c1800381c0d0300151441c1d140303060754510580c10108101481d0000f0135200812001082005042000040054140e0040003030103410181c0503080403882c03e07070384890601485c1c52004001512105940d0104411820884010a296a244c4110500321900880744803954041d2290010300d6401d10314003215200380301c6103e031490b82c2c081528001122061412034603203030035821200300040300c00359402c0b0303c030056802c0740c8001c9186a84540b0f03003480d00400c00070000842d0414400c000155001004a0f02190000d18158982e40c4903132855a0011002d5400044140300d4903100050312500821741c2846004602060141110100241802d03111802d240313000082c0f111201c0e01310240500c1c081e640100c0030300c2c00050b00725100c0f4a441d0b4908980d03008405c14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338985170 1250 338983920 338983937
    0x18060a081f0e0d080601030c02030405090c070c0e0403210e032212020108010312050906040e010306050703110a080c0c0a050610060c0c091806020706090c08010209031209041803 78
    0x8040c180d009a074486556100100010a040040249400d002a05c024105a00c981c410003802c0d108200381d40150000030300e0b1480b00e00b0000c8000b225548900811181070400e140001001000b08105038441c5415885117550b280820400c0e2440841189805280035628048803030354400401c00303007229184203107240c408400034105070614002280c1c0320040c038800c030413900001030342d204032014112035106000400107050f0358410398890143c2090283c00c842c010400050000c0d480d03c155040f00e0181c8000c1240c0c0d00c8198085007642c8a2182048103a6070410407000c80c03c2c401c645595024000b020710304c0c10141000700340c41c2004078004042e40c1c9540700c041400316a0310801c41850041007241040c8010106503681d440d03d01025210300d5414583d1000d0051a0501100b4076641c0194025400c540c2d03a4800d2901c04001e0421000c1514030bd174030340d44003080142c0148201e900c020307001002810b4445658204001c103a11588445400030780750410a428001e90340b00c008415482038645464 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338986420 1250 338985170 338985223
    0x90c05040e2d06030a0308040c030b160e010203130501261006020c1008070c0c030b010b03330f0406031209060f0305040b070c0f050601060f1106040218060a08 70
    0x1d60304044410a1007002c002c060009a60300018a003401d994142000701041da01c3c3d00b8411403103240755102520120020042240084414841d56035103036003512160340303032504240126500d000b003091119000c02d14071010300c425070080c07004c003a15528803141103d594800c282c501500100c1542c904030045862a810b2180c07030b4050000c030010300e400740d8020b0414204400300901d41500580440c043c4000840600700713002003580403502954028000124550355046103400c1030b070089601d9030301d542d42c007000c1600b001400c01c02c00a40110144841540c00b0010b010030140301c130002030065001d80d0b079450000016001c07034006a0b04000d03648458107041e1070818081c189102068034941010314000400c0009100241010341004040c50403801501e01c0b0f1412465001ea5140c02030401d00c500d10000403140c2c1c0c13020340e060b0075500943e106c103c07250081a840f540c9800644000b5400b2007094407203002c0c0c8003c44074007a0300841c0204020340003075950011509021504031048081d004a0708a00e8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338987670 1250 338986420 338986471
    0x30e040b040212011502030f070c030b1521030702040f060501390204181b2c061507030804110d12200f062d01090c05040e 54
    0x440340d550984041d45007421480c08079460800500940c1030626100010b1207445108105071081c1c50312480c031081c1e44440908120b15580320307030b1000b210070844000001d4251001002c0715070340c4201c05098144034010084007035220700c40c220310b00003a82c8818040700f40075031307203501841a0400f4400e000007078035400d010004011958403568600200c10a428008402c012900040061021480c0c040c92892040c0f0009001e40641c01c882d100d40004080d07c1d006000c50b08100680303004109070940903880d954a98081d948103001d51201072403080340101400010f01c7e40b255640030030001c012600600d5034076208042500841c0e4140c5c001140c41081100b00084040003900900e81186c1090007001a81e644507881c2c220341c00c0b90303400c0006028184084408110b202600c2100c03030400c1d241940240c4400c2a0350b03c4003203480150582e2034000070800c0011284040758000c13000e16040a00b603080102d400f020704401e403034410400c01c1c02c10000900c05007180005005503044004c96009003040d09078071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338988920 1250 338987670 338987681
    0x21003110f071e050709050c1c0f0f0c050405330d0b01030b15130807080c1e090402010f05071a010303020c0306010b16080d1a0102070e01030f021318030e04 69
    0x75041c401aa143c24000b003a400541c40b0300700d45220601141a176558011500700703000c0c1d45125448a030100382451132695250b001002040c000017010002c40d0080d98411056410030218140821801c00051204e404c0c1903451240c020b404508502c200004021100307c001d00341c8020822180e8082a611282803180c000c50080e40740074a4148000304880d000240c0c8894401416611000c0000d5903800320b4411030800c0340107045c0081605c146a135901640c948a61001825501c038410a08000114400740d103003c6800b03800140000c82e1039542c42d070065038800c903003c4c50035090090900012002440c00405d41000020301c004515081d4135514029207464612484c992290300f041c80184819011001075590700310303400c2c040003000500d5080c0300000d8881c40700c1e01d01d21142010000c6010724103030101040400400e90071141c0c816070358100d1100c011020701004006000381e110b07a80c0503140c0100e00848540c010400016690901d0420440d2800c0d07207141203012440a0920714400c0c5818441c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338990170 1250 338988920 338988953
    0x90612010503120a0206070305070219110f06030f010303260103031d031f02090103021c0b0f090f0406090317041103060703020408120c150705090913020d021003110f07 74
    0x8003130611010b141c0107521014002c1058040603a290000f50b14103208204102d089050304070b1f09012060142000c5100c0c1a9400d8018050a02060040420305204040702d00c201484002d07503007140d0031a5004c466919002e402900001441c5c030f41c0d90030b40c041d050910740c0210b00c2a194070800070b0f0910001c85004000d050390a109401001084131001540655034011480c42000169a5110280164001d0140c03911a000030300c0240460400028160f201c1c0040550803a014801000444100078141400301c801074003ca00e6034001c100000c070590000c0003141d01c282002180f0444060281141d00d2040320103407501c00300349040b81c54908040c08442c1d044030403840c0a5151a007000da5841e0b0780c02400802042165001400152032541448507507000c070a850210b2009040043c0020f02580200308114410483c142c00f01d0b91680c6c0960226086640c00f400760000e00b4015003c00105460700d070700d01c9041c917480e200c80003500441d020090101c121561101c2e80c03240100d080841420a0b214007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338991420 1250 338990170 338990203
    0x70e04050307080328110a03050702031b01020405030f0d120c0e130914190b0c0d05070c050d020a020a0e0a0605130c18060e0603040302030f0a110c1905060a05090612010503 76
    0x10003006c5100341400b19031000400e414045001d4075000b10483c030f144282c58020080101840d180703c0c8511041d0001d000310380f0200c00f111f026425201440380c851002e544c510000c10343c0c00b110380300d085200341c02035500d9010a00340b14403421031117008100c1c000c2d1102110100f541d07440c200700c01044104c040115100790311500801014850380a40c541d803602d880c40c00b800f0340b9030700c01c0082c0e02a400201120010306000e50180960304040c1d401400120400108840034080e00981800003880000d0003140d0b5a00203210040c0c0350b02d000010040307100701803c0d441d806c03611854003041a488010b041d00c42c0c0e100807100010080344008004194160078040400562000c41007000010761280070038289000c211100d950b40d8841e440c5c1a4594851100d20001400c0f0100f41806407030b0f000901800c2c0070641d10265102140c0010030800c980c00c1d07c15044004045944c002d101c28101080580815156400c20034a8041d000d00010f060b81c001c010f644c409850800c00600607030500340f10004c1c2c12b024860 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338992670 1250 338991420 338991431
    0x50105130614010507020f03070909020112020a050f160b04050c01030b030a020906060c160305030a20060406020c0106030606181104060e0409030e1008012402070e04050307080328 79
    0x5000b20201c54081c5415041141c08a071120035555040c1d0807008500b030003811207103140da4880c41c0101500c5004400e030702040c41c0380e0350644400214000c483c0450030300d44e925031600000d1521000150042c0c180082032072040326002c80081e00d091151406035000700002c00b26189910300040a40e8040c0301014042e8000c0304407400142c403600700c4d4682040080302d0301074075400c07c1e2180a18201c400100d0000307014080c08008248600440107140d48481e581d40c058031f1b80c011203c0841c107404600140c24241c0c3c08071002502040e00c0f80c0c058100c41424400104841d5640d4a41d00242e69007a0400c04c6d0310b5440b503a640201c404507125100b0800070740101d00381002e1030300c40040c0c0071108805025004648980001040601c2100c1c514403c1300000d002c1d0200407046900105044824010602c030000717070105803115503100059070020400240d00601219080c6010f0880f240c401500031102c501c0107010b282c000175444c0024600c5180580c40f18140c40c4071400746003240014403202c86900910b0074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338993920 1250 338992670 338992679
    0x130210020625080c071707030c0209060607050615060d14010914040309030311070306060b0d0e0705030a23010203071706091308070c09110903150c0a08071b060501051306 75
    0x8120b0f0740c2c800b00e22070b5090b458882070308000080074880300c0106070300f100008001301016044803610b51060b00036100500165070307041c20300c40e20340304030b10002c2c15a034003142c000307500c0c00096440c0307003c810b0000d407050303080035080c1507410b0036240300000b0b1844000074100184040c00c07c5100c0c106813482e0304120745403103081c00d40f0050a250384a00001e02044010f041a5194400c1003103250001d681c001410090150755441d0110181c02c2501c84090640c05d10b80040c050400c002403800075948010060300541c0c03160340d501c1c3d0b4919120f10000c00c03070700c9800800454446081c03001d18452003083d141c1c00000d908501311440c07603090060201d841902424180032414507a180c0100641d540042940e94a20300d50410f40c004912540c00140d0031403c107801d000410242e0405030481e09010340440c0d03840440c06c00b007441b0511080710590060501446160500d5108403022a006100c45c00c14040e00105100b8400e0a0544840259007241d02c4d0130041115040450a42c011a4622a010085c0500b030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338995170 1250 338993920 338993927
    0x80606090408090d03030902180a05130c060c0203010609060323010203540111030633071a01080c010903020f0415030b01030203070506120708130210020625 69
    0x9044900b8000e03905404c481c420180682e003c01c1c1c03000e030000c080e080d2030241450071456003881203441a21617400c10001c602c00c1c0720940d02d04d09000354840c1c15010460b040820407a020302d480c035816030303056403244c500041d041400d00c5090301035409284154952966221185441880c10307036030042a81c410010003042c0091803402c000c02c48191000044481110b0200c5e0300c000301e480500d40008548420385a40181c030f0507491980d6060354000a00694000018901d03040c0000c80702c283e0840c1440320610184013a001d0200741013000d1185030400b1070110344d1505a660810001107414450701c0034035403031001b000880a80100360b100010913a82c62094002030040440384402806110b140000060b82d9580d6000503990500361611015070a030750b8200240c0200e0700b0f1000380c0c064040c20390041942c1c14004111200c4038058001841c03140c0b81c1d02000c4501180081c20003001605804141005958501100e40c22060603401400141130440100100350100388070206103000407e4a0035241d500f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338996420 1250 338995170 338995177
    0x308030603121e07020a08011416030903051821010b010206010509010803220503100b0a0b0403080318030f1204021005030106020a1e02060f070b07090f0b0a0c06050a06080606090408 80
    0x201d03c1561540d00300d10118035441c1ca0307900415245e5007000130042072030512001da5480b91500303030280010440000c4090302221030911020380041da08000e0306403805089a9288203107100503007010a95400040013504040c0410240c05080c0d440d483e501e00250b031f0421429002d003270111180e01c140d5142001041d41d0307216a08828030802c800003c221481107650354401c1c000c1c038000e410f44074109030880d5144001c0c07419690740c0d031040f1103007000444c2c804205d9098600b41c03036010184505d551500381da2000c00d268207400003071851004100f010000b55005c0702600320b2002c0301d01ca16405007054410845071118642d29041044802c0c001002610342c009170b00003d003a04a45000030101005c00e120000c49609140650403000c00511030300c5070710522006096007405011422107503106c01200f148d8044051007480001c0516a10074000340ca82c2d200104001c0541d8105102542d0700e0360740e24025104121001079026a4494040040c5401400740da603001c442240c030034903907282c1551110111f00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338997670 1250 338996420 338996467
    0x605010b040e04150e0d090e0c0a200307021003140601110319020708070e180a03020a021302120f01140f060a0e06040902030c030601110d1d1504030803060312 70
    0x34041c031042e040e5036903564050803151345c1600603220084070461001c1c144000903c51407a820380b098000400741e000b001c0030b03200d40c696141d480d40e0500e08110600e40d100c9500240a003071500007000f80c4001a962030584281c0f6690340e4501040c5282c1c0302030f241c900e040005003000e050100b204e5101075000c6000c001c4481440036030941207070300340b00c004080b4a42016600442e00e2480744d80030204220060100b4030344140002205240d50025410144d0340740d802c03040005015a224192b00c40046c60400840c0f02011f0401030f00508000c41040300c140404415a8005c7c16103541c1801030181210f5503200414641c000c3d107c2800d030350f031424046411031007903081080402065000000c0213035200c074211002807151034020340d10390520140c4031890b948280c442174085001c405484032100b0022800c0031558149481d04003d680e4094030420550f542d030500c540c0d22243c08103050103002580c0b0040c00c0514010b241c4282c580c5031500c18545403040d0b0300c0c0c01c07482c3c1c024140030700c00380d0320701d0407141c2142e08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338998920 1250 338997670 338997683
    0xa020c0112060902030109050405160305072c1e0a021305040b040e0d0306090c082e1203080402030c011e050a030b06031305060705030106141c15030605010b040e04 72
    0xc2000c12140700041a4641090090304d00000c00050a0101c0b0f030002401580568152007000845021203400c0c800180300040039a0450b100c00c0007034110480c07003c113048002c1e00d0f0100c0c0010020304141c85101c0111101c40c0f0007000c503a01c0b8104901c3c4404102c0d88200042401c500d0214081c0703014852003130138410320f0b2165465000360002c54850303801014840c02e030002140c60007107180304047c000e04030740d0040f5810b140c0b8190f8054826845041124055900b151030b05890306001c6c1100c81444004000300c5000d900000350010740c00b41c00041084810b40269940455030919104041c1400700003491241040700d03800301900030b43c2889070611001c0445040050b90740320100410b070090460404400d90210001c802c0180c400d924040c400001d61049040e60160303510a5019505800280651000a58201e12210080b400d0310700420200a2200509400700300c1c43e0003d4007600c800d0302500e402801c1c0040c08000b001740d60300689014102ca00c5000d0b0a00c0c1c10503140c120412001807028060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339000170 1250 338998920 338998937
    0x30708070311070609050319110d050403020f0d02030a0c060201200a090608070311070b0a0b03010e0c04090c0b040b190302070819030e060906071d030c0607020109090e1c0201020a020c01 82
    0x2003203807c00480d000001140b141c4a03040f9458503014002c0440c05090600c01d01504000e110450b103e442140c0c00c1d240c4c010958018031403410305100c0b09c0d07000317440104e03010320804560201040c107205190006103100d40c004615081700c41d80c10f60a99581c500c8003e0b541c2401c2c0125019140c004840b0000d407941d13490250042d03614082c0807000703402d2000740d20244c0d5070005401d806001040d0403007841080b50a5050004040e1071050500b00c0d01c6c000e1405603142c03c80d0302c079440d0901c1e00da0040142107011f007004408090300c610b040c40403a0b105a108090b000400200c043d110000751b400c3c01d4803074207075060841c1040c81da6100d844031842042018021450044400d07036090f4040e501c03800107800d164007203c00d9480d01100c881e030340f040291508000705414403540c0006001c0b210a007130303d43d030000e0007800c4a0421801400002c2d040741e42c0890510405040128a40087d40b09061031501c03150000c2c00d400300340b40e0b40007504040d060001801c69004011110002d60005075440780ca000a04e8001034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339001420 1250 339000170 339000173
    0xb09010924030c05120a0f051f0b16141605090c0301090c030f0c02011418100506011119021309110f0307050d0c1a04030209010b2d030708070311070609 67
    0x1013520405050b182c2045610f4180014200719501442002100f0001002191100c0c007004c1d840b0b040d0b000f403040c51649515401d005900c480d001400d40310700e405121640340e0009540e441041d211b0440c0140059002c040341345955412030420f88010310302603900d01054180550190194841401007500d00381d10358400d014030b64840c0e07010036540f81180f80100304803122248000d0107030802c0d0082c4410007130180c0120f101c880c000c0c400e45103485480c900030300f1141c650501a4000e08002030066050100d01c000e00c80d000380c401d010ba50f4081001c3c606d1010544090710421950703404a10710b0300700642c80c054580000070201080701410023001c44802c00c81c1c2c80395030f00013031800030540c110503007103a40c0821000811130109009826030348189080104007100c07405000032070007203110195000b002c00c001001881d0f0840010030030010280c14511b2448804004140c0c42201c0001020680400100700428a41d100c0803c1e6040030702894240602c0c1104030585010b4060500054210b0341d0f601010300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339002670 1250 339001420 339001427
    0x619050102030f182d010905010909090606090e150108060f040212071509050301200a050d09082116080c0a03240f09020901021e03130b09010924030c 66
    0x1013221002001543c4840803012414005040032030b00900e10b02e10085400b030b603503000703105100a582d0103a540519007403802c442000642400d0005640345075030f521002c40c440307003580a51f04109000c180208040884203028100c9010160301081003500280148410600b24a0185030802c0c0c0403244c4101d0103041107160340c1803400e00d50001c8040005180703012030b07094008083e0b40c101d41044008110503150410f001d00d0300d0483c00c082d580c0e00f0f01c08202d540705841c09040901007210200b00006000c44207503460100940c490703c07044042e110006c4c0f88032104441e59010551001c04504019903580c52268042c1a100300900b0012031134501003500103400d4400d07440030305d0200f401c0503d804810004081c86c2c4040c4480d0027000b0383c0018004011540349618002c82d41183d9069006100b00154048804004045201070010740c1c0020407000c140c1806809050022b480360400c00c80d1764a080744005045502a540030665501400080c006400404803503c0e058400030304000c90801d603040c41c1107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339003920 1250 339002670 339002707
    0x1020613030e060c3406080f0a24030c14040b0f04050901020c070f06170c0f07020f03010e010c0e04090515040201090f030c060f03060b090d1511030619050102030f 72
    0x42c5c2d00b00c80131707122032038640141d80d650206241e20901c11070fa00c869003142c1c0c851003154030030140030100000c01c84044d040da21042c41d0500742c1c0c2c0074403829080c0d4441865400700542c401e50300c4206850b402d00010308076030000c1c00c9603001140c00b00407550300800450900d06400d8200e511850781c03003001848000c029012169071481d6481600d0b07410391106162003002041e0300078030f8000b4110991030720070303402849901c07802a400b4000450402c0d41490702803816a1001c4012604449007600301045618240101c01203d0354640022900000346030004082c0c6884000003403040c0e0408807260049000464120343c02021f50704030801c50382e9a800180c0326218a40d0181c14080311200000050110700048070050340c4075079030b03805000c109a807012003d80381c0e14001c00103c81010007046d81ca5190004408284601c0b40010b40742924141d40945d0882e8149e21080311208000010002c0e076241c0403040e2800150300d031580c40c80840c00e01c170000759280101ca05c42243d030000066092003040c0d010120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339005170 1250 339003920 339003943
    0x6052104080f0d090501050a0e1009080f0d0209041a01120209040b030d02150a0c170604060801020f1c020f03010e09030c06011215050f13061805030901020613030e060c 74
    0x39030f54807070a5240550041c01085820380706946042d000c43d9041d42d0600540781d42134010300040410869401c2c00000510b5140800c54851070b08004102200c50304401418144103540c90050f1100600401d110903200f10707034060700300405020b8000a050b81c0000040c0e1203002e02d0240161141c401a01080080018194003541407050003c6101c00d10b5000031411844c005003840485c03561207125802054540941c00680410290211540e514100c40302c0154004402880032401c156103000d06400c9a014504d40c0541e20000546d001603030321700156120b0030b5000c15104600d41000b41e0301803210384c08180100b0011680d5031001c41c0610a003003040c1d408109101040e00d2413560754410a840180590304111800141040c5400e00b41403c0e20555109004000031203840e940e410400e054800354200c821a5403a0341d41d101c2c11b005180701103003d00001d20581c000e41e55201010300180c6400c00090030151310350030000442000030340c812400310705440705881c001e842d12070440c112810100011903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339006420 1250 339005170 339005197
    0xc1e040305030a180302030a030507110406090515120c011809020f18041a010e030106031709040e0601081c1b03030f05010b0406170a060b030f0a060605210408 70
    0x4000c8103010011004200700341e00d0303842d82d4090702a0009050120b8100d440080d5242d00301c0002a0040f034018802016010f2003000f29010381400030001508032a4070341c1080d4a00c954850400426103580701070840da111040710781140007181603421503a20113585489604000d80a1800d401d24181450088090702014401b5911010444e00d050b94641150f00c1d10415200c81e003003481c02d141428030503070007112154054680b600d80d0150044d64540c2e80302e10115059940d503003000002c03c0840a909440d640c50f0b80c3d43c1544c0700080c004200c169001084006000d41002004019800c40080d0f505040d00521031445480705820606980b2030404c4019031000c0440d01c000c10b81019803550001001040d1041c081004e40d0301d590080303046008034018800494403075a0211100c003121580345d94010a4a05c010440715142c1458a4694005581d04840c1181403414004445224007466000d010280b402c4d0b41440d43c036000600c50140301040b00c1290000d428041010301c940d82040b911350055060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339007670 1250 339006420 339006427
    0x50604020f0607120f08060607050a3509030d0923060d05010602010b031006063603050f07082113090e0c0f03010203102c1003020102010c0f05030c1e 66
    0x1501609950711020140c5c005040480011454030b4040c05840415410000604c004420f80c1d4401c3c60200440020f4103a4610100c0c0c030500c1d901c80c044845610542650a80c0c0e129021601171520340b0000140b40300c02c0c80007d00b400c3c010481d1824280d00120462421101040e0010b00416818842d10212804d014104400403915903015000340003851030036800c4841018030702c42c184044a60703074003500d0700145181c10424a62203886ca0054051044030380d118190381c142602140715400c09034000c80d6260400580a0007808007804014000e0060f0305c00740401030071081400740e03d400d40b00b501004003036020901c40f000da10400c0b40b4a025040707e0300c003003100c400d120100301d0f0303500d401c031840c0c5100d285401d04ca4515420180250380c0501d2030040400c081500b4a00040200402001c604441d044946480000e000382d41e2403181c02602d142040b1a071141c1140002800c1d189500021014010110005210540d024003201d0f400b903048800d0940750190820b080c11640d44a5089000844012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339008920 1250 339007670 339007703
    0x215070b0a02360306040c0e1b030601030b0619090f09021905070303020c1501090c09080613030c05060103030507060509060f060108070e0d05060114091003021c0b190f0207050604020f0607 83
    0x820307c8500351480e03d020303401141d0310040320000007206c4142c3d07203013820402d00106d14154001c0e00200d80c01400100024100b1416800c0c17000842c01c1c040c0c6403070005000da181040398040714030f60304029014030708065141c4103501c000b114590078032003011001c1100c00641102894801e505a0b986089001c0c159130025a8181031840a0760081c0a0306914508c1e1403400c04076640900841400c1380c01c2d5002500d050341c0e494040c910200a00d403025000c3c0000400300e03400194080c04114080c5101e5158592a600b882c02e09800315034005000c11050f0340040c060100541c081d2050f00c0d80314100f40707814071f034607030701c1903001c9507640703620544031342c001d5080f04c409801c011000c5a031605031303071009a5003e6803000381c408110301d0034000d079040f40c0c414400c0c90302031000d401c003e008d03031840880112a4080100c143d03580d0000c2000c04a4080d0094111201610041202c0d03000d508100491010103500f40081612078645450010b03000034801c82d00301000c4030041d11240d055a40041d0084080104103090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339010170 1250 339008920 339008933
    0xf1b020a0302040c11160e16031409100c05040e0a050a060803070f110d0221011506020d1805130e070306140106020606090c0301031e0215070b0a0236030604 69
    0x101c5200140341e021b1246a01c1aa0310070a800c00100c42c0a40524100c3d07031215400d001d0104c41c440c5644042648400031403e418401000c241c3c003a2412000400b98409100007100860b400f0420308000c2241c200410400301d0401001d00b0740144a504002540352507040145008015030b5220b004507000c041052000d000750000340e01c01c40c40c020004181c440d03404400f04280c009145800a610101c0d8000d03882800f1020380c151021038004000004003122241c0100304011040e82c03004005902489407101002d500a0119070400c0c1d10542d1082e006041800242c0e0015410f0842c03103110f6a5080504030740c500400038a001150040000c10490310807400c480c5016500740103c0c2c015129100105529050a040c101c2c810400d003e82c00d03041d6421981c0b07020b8100401c80c3d01807036551148404002590f110092005580c0e080440d00359581c041c5e141990740d08000070300a40a5910601c00019001c1810f440300402004021421001111170206d074010707400c5031a8501c6e00b40c41803c00300b0003000b41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339011420 1250 339010170 339010187
    0x70c0b0709140303040f060c080d0614040c020d050d0f0603170705070e04030206160e090703020d0c0801080703060e0a0c0f0512031908070c060203040503030f070f1b020a0302040c 79
    0x6600860640b042c5100305241d60b80c030691040c8003112041641c2007104030300c1145580c1489201d595075a20b489100f8550400703a13030140d08100485500a001420f40746020320031426906801d0019002e0382c007606502604074015030800b64505500c924800023082e01039400b4002665200f010035005584d103074102c8005401843e812141c5105060001c6140841c41641910455044d4018840d0341e0301e110020317400d070342285101d009209000e0320540d2030380d40e03040025106201980d00181c0391044d03c0e601c03500f0344e040d221403001070012103030041c4450b600100b84481940e03004a00840c009500600180c41d001c0c01c00000b80200125501c08142520307060075020856400f20383c0700361071030584081561070780314840d040301001500f13034004141640a04800f591019490508000c186041d4662100380d030710884045030107400000805c00d1040c0004281030b0081b440d40790040305100c400001800d0400b0b00c15542c148980555800400c55503001d9685c805141e0280003400b401c0489400548000c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339012670 1250 339011420 339011429
    0x11e0f0f060f050f03041707020d12030506041a04020a0203160602070606050f0d0b0403090b070605100609080a0b0604020d06090b0f1f03051302061611010c0b0a05070c0b0709 77
    0xc91000402c804244100f00303a0f0b044035914401945562030f81d0303840c0d840468041d100d4071002038040c494000580d42d5a444c02c00250300501c151800c0700703915600141150300c0180241c0c86903140005c245420b44880601b4002c01030181d03401a40c030500418142e2542c002e0022981c0804410201002048001d8001d04040c5210311424003500792214100031000007505091600600001d643e44042903028001e030f03070018068205000074036110240c40125900620302901d1a40d16101444016401c9a00c042d00905d52417901c01d107400d09220300c544e210010a040a03101e5140c030000300d0389554032541200c2c180840c606d02004516680d000210180600c55411440380702c4489601a007414110b214034040e11740015105552810350307005400400016002c0c2c6104d03500b0442d181c005888240003404008100716400c1345016580c904002100076407a90503041120030101400090b01c038117111600000150f00208065030b42079000c41701e044044038054443c0041009000580d6000a054000d88 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339013920 1250 339012670 339012677
    0x8060f040e1011271318020a050f03030906030901180b0106110a11041806020f030621060103060b03030d06170f0307050c0d020a081b18060306011e0f0f06 68
    0x102281d140080c95070059400300c84c1d038201a40340303142800c540300101d00c507000d0f4000e11207000c5010b01c06000c012a0301c07510013244c0c00c101182c07a410552a21503c00c10003048111010785a00044c0740100341c0364018000800c0c0540c03004004103942090030b40040c007501451844601c04565507041001c0349203000c0c03081101181d48290000038211010911181003500100c00b801c00b603a100c4103000c0200b0300c0540010170b42031074410400020f0024001011400c501030b040070780b2801c4c0340c070401407042c010b4003a000c3d00025051106000010208581e0b0442c1e0300843d000440d0758801c0046821481600c1c4401110b40c58010041990b100c20003c4100014981301102c001c2090600d00d241da0303104070280501240c2c425440c040c450300d40711001c0100c00c1d1015140081183c1e031884a01d00d00358648000003a00c084150305132501d8148854440d1500c222110701c0300f0035003413003404a0b80b0707071006004185076048101342a031215640d002c000070003003403640c0080140640e00e02144410340c0447c019000003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339015170 1250 339013920 339013931
    0x120d0203030f06011e11030405041508011118060d060b0d0614010e0d15061203020607080f010b030a09020312040e27031207030b060c060a20040608060f040e10 70
    0x65100c1c5401601c018a001d126440e1344078907407810380703a00804c0d8220741310b1b0348820070021500c1d40f6540581e2001c0c4080d02c11096241c1e0800c0d440900b95802c0c01c440c80086076050080000c090802c03407483c0d00e1018280d038145e0b80c4281031002c40020307260540041c01003981c0003d1820000181e64810000c03140c0940002601640f080011110190305080d0346902c108405803040100740d4481c0e00411042807184006169903a0388a038400c1100844415800342c0c20000800408681180d98250300c030020319491001581465140441400054411004d0503980e0a40c041117403001c02c03a9070755500700501d004c4e403a81e80d00e51014007880700881c0c000743d288220080144568103064190151507c0001c0a542802000b26080565540080c4400105901e41840b00c01589444004003164100c008c0604600e2810306202c1040c0c850300600c4200300d05859452030001c4001009070740c00d4030300f14549039407a81c88010000d031001c1861140f8a500c586404219240d0010009514900c0062140140302 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339016420 1250 339015170 339015181
    0x6070f0b09010b0f041503020307061106010b04051804020f06130305070506030f060d11090c12060f01020d030b0429010f0c0f0236010602070e0c07020f120d0203030f 73
    0x281d41d0a03000c2c80e03422203100403404c140342c074003038001100307483c4184c1c00301c40c0c1c603079a0f500003c1c0303400380c0e680c0044081104483d26005510003030010f140508000d889140c5420b2900c1c02141179105d0403201e507019410180040303401c56072940800150110000e1019498014541d459000f148951001711680e108030900007a4a003000c3e81544c3c840c50b42c1d584030380a1a502e801c00c2c407070700710300e04034003115882ca2130044061999114040c16008500100c0c0b440c0e100c83e001c0c60407d212800c060241031258140003400419a0790000350621941018907000c581180c105000c140a09056803000c0700810001c904034081b1482c01e00448100e590907620a03a54a100d030905882014030311001070700c9500380180a00150514002e40243d003881c03000440b030020389041c808175107522101d02401c10700204400401005034100300c900058429542d01c900641031154402459100b8600c2c000d00480c4400070b4450240d0701c916036080344090500903a28660381e62100291a94030071100c41d4080280d010201e00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339017670 1250 339016420 339016423
    0xc010501061107081203010e090a12050d270615081c02010b010c0c060f0c0503070b010806090d0816020705030a1101080a05060d020d02040219120e030909180a0206070f0b09 76
    0x405c50048403807141d00d107900341241501f1101d070090101c0620301c100d10007900051800c20132500c44002c2590f80a0302c4400c1e142c1031800355185c45100030996030707400c2c00c402941100100410750a030f900c800002110008090320f03054480081c0d2140440d0300402c1c0d588a24504040017039001d500c03c80d8004c000c034241090054400004080b0041c100c600424400e01260303008080c880800025410102c40700500b44d510f440c5550b00006c1d00303c818010201c01082071000c2000030340c0c0c018501ca00a400109003805005205180081c107140900c0c03981034414045070300900c8040060b0002600307a500c0d00007a0f0410260151964101c40e0000302610000751411816114060042c1da005010410640c0280c0030000b03c2451800e007aa8050f6007046446000d9081710f4440740414400e03110280e400e002036040100300d80c6404400b00640d0000c0003424040da54203410b55500030801501c980320960b890050360301e0103d428000035040b0710000384841c00c3c0800d510001c5000d03071180289448540d91166050f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339018920 1250 339017670 339017683
    0x10306060f1203050702010903020d0f0203010b0102370c0e01140301060e06040515040507021e0f0d050a02011b0c05100615051b0a08031608010602031e0c01050106110708 75
    0x1464501c444030640011344518010200e040c01454a08962070b00ca0300040c51407042c1b41c40440350030018030050011030500b806001340c46002400504084040284210400044544c140d0007405080f10003010075003614020140c0c0c0f039001928069020380b42c00d500301101c6028061011040c503400001e10603444c0500403007090366440c034a4003170507865800512000d000d0181039000d4089a070410070010351564132039548583e00f95402001d18404075114000303004c1a2900c1d100c1c01d80c129a00c4c000407600d000400c00710965252a00c507540e0404000100d0050503a0f0803449400d51601c841c01c214242c0c44000314102c1809042a644030607840044901101c500d4880e041d0045405400300e90154007600150035000503c1207141c1d1105482c840c05130130005406021034100d4008030500003840b540f0180da401d491903d0801511550400c00040c2d0340c1d0081901e615078480008a1106007000743d40296810911411700a01240d41c450300c014040095403e071406452091040002e040c2c0c0002900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339020170 1250 339018920 339018929
    0x9030406170703020c010e07150824150a0c1712010e0606070b01080105010608060907050d05131b050915131d1006050a0509010620190506010306060f 66
    0x10640501d595294495a00000030318450905030300744440c0354542404e004406503c02c164000d0407469040041524203400407032004020800d0700400c05c0b407440810019481e420405441c07854020918000240c840300d650211610103400200701c2800b450341081c14542c03828402e07040d4a0600781020079492050180c4681030030300d42c40400040201348a03c606158101360040d100e0fa02c0c008840d10ba0315143c020a92185500342c0d5540010003c0541c002d4210350410012141141e840c105042c0080950040c4146086107503901c0e40841c40714510000b551200c968002056004500700c0c1d4201483e581040c850640a200c2e80c84c0042c103c1e0030441760f40049283c000304410030b102d4134100800d00628601e0100540d810036001184010f00c0100103d114040581001207180703800c150900003544102d0303016501460b003460050180d2900324074115402d03a44000c40c04241c0c0070003520a89006147c41040c0d010b02000c6106405000022401a040e280150790a000c000d0b6628403214074400140326 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339021420 1250 339020170 339020177
    0x40f0905060f040c020c0406141e09011e030c030b040201031103010f0311060d060806040c0b07080a0302030415020c1006081203060120010213090b10050d02070201020a0510050f09030406 82
    0x505140314580f0f544541e49180302481116955528400403c0403942c454000102240c4403850b045a1071a01901c15001c041070304001c0d4480010300f001154088506018406d0001d01050140705130ba114108800002c6030855104440160f41c1d04010b40381c2101540d0a0780028104000c3c0032081c0d4012003264101c89041405000c50303032a58480006256002e000c442e0300820810000040b4040e03402542c002c0c0c100300c0b0251880d030401d0f1406a0703108030964030056a540007844860b01043c03203401a14035540481c10003507034030f81d107c0c90002d00f41000e1503d50000c01303102040a00c140e00f00024125080c0780341b1722041150030785031640d59540360341540240ea8480340400c0058400e500c00c3c45440c0c00c10755000c02c6a800c0814a80728142a600300d0644055654180d4038200840d40310b0740900b140300c0c0342c20380341c1e0002d108040400404074410b42c00400c2c00f054002904200b103902c20041024004d800070252041048080c400b180a80310607943c0ca07010180304404942808004002c584c1194143e45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339022670 1250 339021420 339021439
    0x9010f05010e1f03050613050f0a09240617070317090604080a11011409010804021e090a0f06051c030e0a170f0610030201020c090408130b040f090506 66
    0x400440d03110109075203150300b02079050300078070103c3d030480c0c011050030903e0b03200454586811024000714680d4100d02200103030401050194081c0c1c01034007160000a401004100303106541410031419505440d05a03c106115003002070480700c0d9841f08040d1124101c6031720003096800b201c0e0790384003030f0f5010207400c40039003685a007a6203480c1c0c40180340750079000c0c10181c1010760761b5200354200820741c0e000f5641c40908500d1a002581d208008083c00096400c0540c00c142161000a0403000c0003003009014140e201c080040f4480039405c226604400182094000e01d007000030280941071018000c0700c0c3d0703414007502081c41c3c03170b2100545502103103c180c250406a0700352012111010300c05081504280103201c045003080d0410310440205075498002d11f860341943c41000d140c1540201102404040c1e2502800142c2e40404d914800110488111a00c0d807100d0030030a42d0361050109440795401c030310100264014000001e001102c0000e0900c6004d90342e207400e41700a850303048038200d13884400507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339023920 1250 339022670 339022679
    0x9050303070816110a060c03080f07020636102304030311090d050a030e011b061508030c0a060e0a03050702040e070b0a05090901170703080c03090310020301030501050609010f 77
    0x50b003c111442e00814a81c005241e07400c1c089040544590070030b00000d00803204010606030401d03e81500030302c4484494000d0700d0b00000081d00da02c0041d000300d110300c0c0c00115200c803154031003480342c02c1c2010110310403201c40341004489590381c1d101c14a030103100d410302c011002003047d428101016944074945d145040d64032950201c1c020440c0e143d9500750031006101500d015100c208074500d599224500500d0030031800c1c140541422020f540c103504106a5140c40e42082c5c1912003d940c240f9800074010514455196100111003103503002142280301c0400d081101000002c3c8514443d40149810031102034411b04650326003804860150105d08100700540043c180f0340d010058000344402641c000a46416524807550b000882a070001980465101018030300080ccc0b440c010040d01c240d0200f01402c1c101d4440d21200107100c080e01c1303900b01003100841803105008843e50700c4002410344070f0040400d030240b00203420070300040c0c90b15071801c2d0020b10b403800c10030030701c41c103079520003030841c800c2840c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339025170 1250 339023920 339023947
    0x3140304030908010c0c02040b0d050c040b060c010c090f0806090d0f030b0a091e090b0a02031f03080a030623090709050a080604030809030f0a0e060f0712090503030708 74
    0x1034812820000014800500640b082c481d002000c001079407598040262030042205a54042c8030b540e04c10082d200300701d8005400003408424000d4140d030081100c0070713804009003181c0a0105682019403c0c150091102070340180035406032140d004411500765101c0340015510794080380c2c51340140d0301c0740300c000c4c0d074030342c0102140858408240707404280032b1042400315102a441c2c0d8001c0f0b031401e8039500400c2101c1041e43e0150202006000200000107144c0ca915080700c03c050464140306074000041a0b00a84440445100d02c500e1400b510b001e0b070b541d2401261035840010744034006480c1136400320789003062191041c003510040c03040b4288000d081d010814011009001c0c40b091001e002d400040035116441007000412011004d8581c910f858100501384000081c59142503801c10440c0300021201702c0d003906d20640c61450701103540480080400c14600c2450f001307407023450012039080200130594890480c500e005a032802840c9644205243c0c0d82e00501c040107041003414400c60090014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339026420 1250 339025170 339025177
    0x3031407080f0d06090b19180e03030f040c090507053c07060b0d030c12120e0d0e03120403061a0a080303010812040e0106030507020f0d0306210314 65
    0x180e5200b441c0c25840700b4800501d500c01e2445900a54a80e081000032200e64440c042400301c0548850344100c24007005040d2480090081d1128080104003c040e1505564080c07641114900200d80c0d90703041c1555001c0604c907003201d08540c0c1104042d000f06281c91140500750003031146894803410104900035016a4042d1800d039003d00c047c0c3d48840b4480881c5640386508844001c1144654030002d50504000340c0e0354581c003e40c0903000d0034602d000087e61110b03104041c10380200f03904440402d141001c90f001504041d0455249050080380180b98034045074907104196a03498480e1030003885014141c45000700c03440000813100138402040426190b4025480f4841c4500b44c60b40040b0710000082c800250580000303400d68801300062191200030041004a43d00ca81c44d50350816140c00005200410140070720410151200041200903008204809600320304000b51602c004102e4070050042a5501c502c0348843da0709481d11013041111002903803216007641d1a964140d6644103c50318560 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339027670 1250 339026420 339026423
    0x50313050a021c02120102031003022403010b0319060b090f0a082401060306030206090f0f120d0f08130f0f0c0305060109050702010b18130602040306050610020703031407 75
    0x390751010760040e55012140e1242c400907070041c260031106030043c04a800c400c0424030102d03a00c100103009c07944031089502c1e01140e07412201842c084061700c1400300c408005140c1c400340210080000f06003903a40c0c00146100d103107501c1845c03510b00f68401c07000c8281e440c40d128160040710104130130100f43c20881c1120702d00b400007030440140d20b65201801450703e10100c140d1407080a1440101603201c0d40c03224628010a007500e000c3c841c00f4299000540300388191000b0134410070f0802e085e009a40c880c3d045440d4019001031591240e80c0d8121003c3d901c0307a45010108000070520840d00c61424041c0c40058059890081d031400880440e50b6040d0080f00400703003e072916521551110002180c40100c0303000345100300080c203601e51504900074151007024051606590401c0b581c40e44a460740158080703c621034807840301c040d85030080110001e498200300680a00c0c000617002c002d001c0300d900520702811080d00c010004840140741282c070360905020013800141030262501100071040301400005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339028776 1106 339027670 339027673
    0xc09040309051e121f020a05030103060b03011e140705040e151314090d0507080f0904180501150603050c0a11100c0504090f020a05031305 61
    0x902541c068079000d000610451540d44040703011503c03050341c016001c04003035003622022949551110030f40c80403021403400d0b070000d040013910071500c10440c9035440504690031561104080c22000c0c001a5240d9203400c00509402241c0c1b01e800c40742650300c8400a041000030700c200a00f0000100144103010042c002040790345a07240f5019444000324221541441182d000160a602c402044114161a00b401228140350507031a890151185408880c100c524801003250180b180110081c8100c006110070440044180098403541c03100400100d0007507039000314691140d2012070259940e80d114403d15004201c8603209501400302880c0501561900b2440c030400340c0300300381c010800c01145040c1c02e242c105081c0442c51044103030040910160240c840c0041c41c1d0342184c01600300c0ca52030b014240c04520118800c58558a1090f111581181e881d0000550400000441030750396 = true := by decide +kernel

theorem cover : BRFrame.Cov 338848920 339028776 := by
  have h0 := BRFrame.cov_init 338848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 338848920 ≤ n) (h2 : n < 339028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
