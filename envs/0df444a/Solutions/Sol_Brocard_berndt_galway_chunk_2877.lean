-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2877
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:00:40.390001+00:00
-- url     : https://prove2.me/submissions/b0e13cce-6c2e-4e2f-b762-acd48822870f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517266187 ≤ n < 517446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517267437 1250 517266187 517266223
    0x120b06041407020f010c08010b0d0507091a221202060706020d06030b01050f0a030803060d030302040306020c0102040e010f0509010306050711010903050a02120405030a030302090109030f03200f0a030e03 89
    0xb841003000c4d484940c200d44203406542400300282d880307030060406a0484a03c40042031401c180342074402e009041c00707440310f42001202d110002d2412821417101c0482030080e40e8582e80c13100031855460b81e08050210b0303840380c03400500301084500100c0481c8600e040d0142d500940c2d0300200e18100b802881040c1e069000c152034a0404024070803400c0d20a41611000e0b0f9101883c3c40000042040c0311203a84030084c141103042002803218101245181103461103410f002d030415403656130310821f1740c0284000e00b040b07a40c0414200307e141240c0540c40d00600350118a004640e04280c08100700d018140006440f2135210004201b4403803140300481414103440008029204917490000d06036400000d4441c010301c1180200011201c90f001180d04580c0020000c203c1e0b8501607806401a411010b81c00341408541d240010100c0d48031101c001116200743d4030102001e003142c592440b0801310050759040c40d400511703a018015000944012402e4040c2018a4403084000002e458048400000c0d00a05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517268687 1250 517267437 517267441
    0x3090603280209010f0804020a050f0a09051e01051c0201031104180b120f07030f020607050601090f0c0f021b03030405040c020c090f0912031005060408030a0305060a120b060414 78
    0x64807503030141030195001d982d0700e9184032248504499080082da030181d0300000d422401c00451412280400b1085009000140d0055880404c40101c0e60101c1c0c0f030440d40e5148991f841c02402000c0711446c0540000c071035407081050282d1343d13043d0a00041600a06156890b02442c3e80c5060580c00e07500140401d4504401e1100200c4180010f071031009220350061000f8141d0071240403004c02c114081118000040030002d1641c0c441c501d40b048400da0030398106804000f2500070510510800313010307201c114004071b028010f51040c0340454800b8442e00081190312038070030041c5a80400e410f844020708003501c0580c441d0500000341503214540c0007035802403400c820030b80aa500484c4030588030404813004500c6035521105a881900c04940c00382c0a90840c004000c2424041c1020b5a00f080424003099000ba40b80c1012590303903400f40c0c000040e60b07800452218a40c41d810300500350310201c280da015000d6407074605076202280b100b501c020003030030034400020036603292544074030b60082551400400034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517269937 1250 517268687 517268761
    0xc040b0c0a03030f0e03180f030a0b0403020c10170402180106200705010509060a090e040b0108061602070b07050f030f120903070201080412020109021003061404090503090603 77
    0x1144070340300440c0440d003855010300441c0400e104950301c0060f030354040c1d40380041c40c200515030040c00010096014084001003403080d03c00b00300040210784110841d1400e0305260602a150070480820148a5141e5540441a0740d9110010103a0401007000801d0180c940d44002110411030180458203a0307281c03000059803590146452a8800c0e071020050400249031072441d03154084e5008050200c1c0040014282c05d0130010007d01d8501120700d8255030050301ca102c44400040165402d071100d44600c0014080f00000f40195604030114058940c017000c02e11a003e529000c0c1c43c4220341b05417001183d000e09011081c012010364003100c1064a689200d070440d05000d80c1c2081004200d00c4807024001041c03c1c80c004221540c258050315160610b5485507180031036408901100000c55495103481c00042e115410042076280c03150b1800f1440d170782094219100244246052481503081c011f5040204802004440e4000c0042d9100c0e035a95a0b096924405c00c8100c841c810740b5150510515140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517271187 1250 517269937 517269943
    0x302010c140a06051006031103010308031b03090307060b09060906120a1a0106030608061b1b19020118030c0317040803040602030d06120308150307080109050102031501081009050c040b0c 82
    0x426003403103000c40740703881c1c031544100c00f01d4130708c00c03060314003040100014000701d499100a558000181c498090a2000301c61000609130000d07140c06620390300200d0100200a40c502400040440035203901000f0702e031500000e29003603809025240610303034091401e00740b0001440340d0801c07182c20101c0000c0c00407021b100311800762424800d450000745010004900312501043c1c050042403a07608005440d0304464101702968030818441d40310000104100b2221b43e0180b0041007908800b040200c0030b104a0700003d442c1c40500003643c07012260903d805c2c40002d166103011400d89420004207000424082c0c00407d2500c5550010324882c4404540010102e074000001c221900304150144440c60344c55002c5031403140c1010b0024081480304001030408005200c2c8a4103891000702107400c541c3d600d0141900b102c0c1c8880003074030700f41d40010070001e0400712000c0d041031f204001c2c6042140d1b45403c200305010080c590040d40400c540300c40104100d00c103940c1c15203002d00f48043c82c26030303184011000d07566 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517272437 1250 517271187 517271191
    0x40b040609060f0c200d0203120601051314041409070b0f09041e060f060507020609150d09200603040201180503030f07061b02120a02120408010b0109090b0105040302010c140a0605 79
    0x400170b0715001d9000540000401d405200c40b016800941c141270010584c030380c0b149070040400e41040028003002c40f40c0d076248945200104103680103400d10a0075030042c0810fa812150b007800c85e00034058148060600c001410a040352940c1d82d1940d12240f40f560704000c18400c3d880e11a41c86801d0554840100300030b00c85800b45603401071010095aa600c00048441c03803480d05c80d250119000344603c2015040c9980200f0241070b00074031501c0c8480110b108038605401040c0a04525555085084208650a4a0018404110188045214040ca000a0003484002d00090410100d1001c040701c01c240310601d40302920000b41600c0c1c0380c1c0c1521110403a1500229403c2d100f00341000090a5a44c1080060380701d0030b0b03041d0b03000c0d101c030801007100f448066102d114000214464a03000d040880301c4000500058050900082482c110300800180416031a070440b02003186031101d09c92440e07800800b02c508903942801c0c030403a0030003181014078101c4100310002d5002d0190041d10820080164170040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517273687 1250 517272437 517272467
    0x30e090a0522021c0501151e0501020118060b120330060901050618030a0c06020708030a1b1515060f020c1305180f070801050f040b040609060f0c 64
    0xc0d03480d000482c004040c01c0c6140103508040e8048010039081205a0342800103401100081141c0c011035502c1001c10b00150300a015082040c0d01c00010380700d4a1400310000c010910080c000d00245884d425442d4500b071f10010022644e58041900c103071a07071035540d290001034100380d9458503910302d02640d48040d900d000d102d0b545412101c0130a1140303502c1c0541c2c02588050301550b42c581c00d14080c02140d44c0300f4440c03003000200d0320075010000c1d90704008582c00070b4410701014250341d15051002e8500380c015080002e050300f0521110014550200341300aa1000d0020300003103c0f8900e0501c030103000da0f160360022000b418481c06081e8130000351500d00440790699511640c5040c42c0008030303195110055a258020341c840c040c556502d0181e080590071100d00030044041d4000010307070f14030708485c041a0340c115070410031781000100001e10031107911415018910321149415a5041031419000f003000340203e03510513100c0c0a010345136010014040f040281040350444040300989032458440c840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517274937 1250 517273687 517273711
    0x1c0801060810082d0a030e03010c050a0c0f02061201090b12340f080f060907050d3c0b010b123d06020d0c03080a09030e090a05 56
    0x2c5840070030310303030541c10484030b000025159040d01424401030300740d40c0b806520010030f0003400f0000c08040900080302802c0c42a00ca10702d006510b48103050a40d201c152000042c400705000380322900307811240642605500080c4403015406520020b80304d80504082055541e6583c7c00110b032821866015020b2100200c0c1c041e46a04103604900c0e5491100d103408508038028885403001160407491091140c042d400c0c08540f5880d00c4882008003000103038460075840d07024892010707818000340b103160740004020000c0e018150400c400f2130a0007406100040040002e010400ca4021092066218801042c51528400c2c02060800320031882da0660030345651140c1d100004090303442d54112100100d280000c0407460380c55009101d0703000c51400035100c50484c04910109080d00240c0c0200700d841d600e0300c0803a00c0d03e0512000074038040780e201601c0d0030b004e00300700c10b1404030b40c000b0030982d840040c0c0c030004507080e901c42c5002c031120b5000d0001c003a0400440b00034059101501e800c40c0d8031641000000f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517276187 1250 517274937 517274941
    0x50d1113031104110a050c03040305010911210d0f18080f0c030303060a1712130e28020306030304120605061017040308040215220902040b0f0306031c08010608 70
    0x4000403500003000c0d18903648130801c240c03c0d910b030090014041420031101030ba030401c2c0d0b5a4131500e09490107035400b00c1d185108001c0c100014940402031107c80105090b18243c200728a814590396400900d01000510158900b0719030310900c192700c4101c40030000903014010a503940210b40d0350302164684801d242c010850398800c41e00b030001c2901c0c42603038010f0105580c0c038545250a101400c0150f00c0a40d9400360613030000203000c02070020002c10030030207280c0030706500c0d050a10526000c040d08200b0500800100c00c0c060340c0071900b504420050340b0f8001684c80c0c4903039000a1a512980e03002d014070202005030102405210303400305202e54416641700170303003030035964045403080c1d0b0f800ca00e40711170b01c150000301d80030074860789120354418806046c08966122051103030403241c0002c034042035032a00203402c45008800a032003040080690442c00e60501c0c0c24801c124940780103400c0300c0c00310307520b012001880320341d42004001030b0300f4281944503503410745064000300144001d0044602003414480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517277437 1250 517276187 517276189
    0x3010c02060f070f0504030204090317131101030e0d081f080a05070b0f1905120a150b03220507030209011509060c0c0b03060a080601060903021f0807050d11130311 72
    0x2002c12010050351764240c901801c583c2048020300c881c60f019400c2004e041001461140c4c0088064040e0f514110851548801440d10800549250507028101410001c02955200002514a650b500c80342860803031135070b4a8407210b40e1101c0011107503010b00200000080c510710003090a00595014006403211291a0303146140f03281f03e90480c1c030005000070015190031f0041e50b199600040401e01d021407800e2186403e8503031000042c4c8007011030641e588010081c00c0c68a000f00c000400700c00c003507503056150204400700001e400c440c807100629030310301c4040200300050040310003440c0e0080403030160b542c55800e110000072902020b040803035407002c00824500d014014102c4040e5006d410703c40c410703041a401018039040a010142c02c580e150030301040860040c80510f0190045645000056145004220b641c07006030101d11103000f0b01d242000311340c940c0685d41d80d5110459003005a0b40d501c09105070310090030f50034020005028081041690b20202040041c01c40b03000300104145011200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517278687 1250 517277437 517277447
    0xf0f0f06120807050f0105072d08180c06030a05040b1b190e03070303050a02120304020603010e1902210a0c122d0f0e031306030f020903010c02060f07 66
    0x4056044049815114000060641c50003084010710920607902004000c45d030240c2910710507a0b001012500c204d81c28030041c940f20514542d0340c6a8100345c030640302c0c200c8001410401d0040c10500149040425034607100350f0411403402c11880140000d5907130b03e00101040010841a14102d82003100900031603020790580c2100c598046001d0701c40e03843c0c034076148103030204491300c000c044080c041401c05010303c6a509100d43c0c0029406070703c8290359030740184002070501189455100101209009010260f00c440c0c0643e17040d20011107150907281c4900e007154488401054162440900019001c2e188e40101500d4000085211003000c0b03141d03e0380b8941d1010303030320806400c0c0b0015800c4501d6500100860b04010f58002442d41d601140300710402d000d040e9141480c46c12000e181c0c072000313001e810341001c1c85844032100701d00c4091800c045403000d00120988481c8507034010036442d02201840c1203499070498041c604014000c20a40c4407241001e91100d4040382da45204807541c000092906002e8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517279937 1250 517278687 517278689
    0x5091908010b1e090a091506060201050c160807050c0a031a06060c030315130c0816140301090504110d0f02030d050a020a080f071202060103120207030809220f0f0f06 73
    0x207000c00c00400d64100701340304201c4001001145c00640702e608a01c04201da0010851ba83c022141d000f040702e1341410b10103804d40300064a58112580200141003055a5400020090662001c0b030b4658601c4581005440c104044c0300c4288d01031000030001040086e100c10751002440441104640c40d80c6007800c2100c0e6000300c20b9184029041000020207160200c00c403070200c460006c0c01c0420009a01c00036401711030a904528002c5141a4103104000c3e68a0601803c21a52803604404481d482d00d201d9141c0c3c00180f1a12008070b8840d0081002c0081c041d4106031001005416111040c40c0c40c14005141426210b0a900038007980c0585c0003058400c00441d03401c580180c0080495840d41d5980207a00d6010300c1c000700b50280140103450010300c0c2c030344104445052550040200b9410f6081020b0641107a5003058150b6229200410029000100307503140c00d08200c484000442440400102032141007aa4020083c6403604c0318000c0e44156004481c0d0300d81c064400c00098481c0c6403900d0407500710f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 517281187 1250 517279937 517279969
    0x10501050306060435030a0201051006050a2a030c0201080601110c010f03110a090315140a09030c1208010609080c090406050702150709050405070206151005091908010b 74
    0x1003109000d08a001c210781036150f011131007002c4011800d41719042055044800840c843d03000054800c0000e82d09008850f04130000c0d0f08035646242c607180010b400c61183d81950014001a003051201ca0540800304901c2d000708400101d48030a000c3ca002404000080d00c100d022850000120b485540304201c00786061070b8000051019540b90001503c4440d9081c550000301600d07044c20403000c0b244900a0464400355464620005046140840465221054000c0000c6c5880ac1d500d01e0030040c0141590080142c98000480035640e080444804001403006001d482d241d84100100359448400305040b00c0e030303030ba0320014000c0d1120701d07107520340c1d0801d0b101583c4964000040307000314100c3da001030f400141600407a040ca44038515014508042101c00d00081520500100500d040500030349501c15032600c09817410349001f410b4040c100910707000103406010040c0f20f176010030740104211090540b00500e0001606600440038110800d5402004c095500780106000103090140320700c0382c1001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 517282437 1250 517281187 517281199
    0x120708041508070c06180f0602070b011e03020415080a0302070504050c0702180a0b0a03050604170406020a0f03031d06040512040e2206110a11060c07030305040606080304120308010501050306 84
    0x45a1104c00191a00b442160f2008806d540488005030074420800c034020320039540580c507688142801e80d40780e08164010000c2c0c4074a8180c42c0c20515003400c10341c06903036040740e0000d0030342c001c8030342240c00d005a500008a81c0c071554fc0d080703091540000701c0508a8030115800d2007180c4c0c944062a00702e01820000941000031074010a0b01400d00f012199804280c52000243d11619000010030082850740265200d0b081042440b00703120b0806240300c00d26003104070942c9001d01e401002581e5641010b00900f0360101e041e034500c2058482c3c1c10030542c070302c114951b481c100d00030180c0894a50000340d030115032511030710450031159001001680c048580040f0001c0f2283d541e184a9002600d0700c1100c1c0110500b00f20714000000e0b000c1c495405c0c1796960040054844480c0d031005414203c010070540d005900c05020080b2584a1204541e405580740c80c010038603840d18540000a000c05400c131040501002c100464210302030612001c2060007503480c150702da43da50006450611094505c030390080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 517283687 1250 517282437 517282457
    0xb031216080306030c03120d060501080f0105100e030601060201061d01061403040f050d050a200d18150c02090c0a02070909080d0603060e0d020318040e12070804150807 74
    0x75021030245500c224090252a5011102c1d0006400c00b0728500011003c0b0601040042c0d407041e01d441803102501c800e081c500a10704100603a06500c80d0144650761082c0c05178404070800d5441200409112240a130031641c2a50315050064060141c9019100c150404c0000c5009210030214103a4100c540310744801027000c4c0b120a0079100c0750b0009200744c031001142201100094410408007808401e107907103144d02c8520206000340494085816411401c0d141105500140404201d14440c800b0038200340e0400300a01001541c000495400b00341c2440320070322440303409500800883c6d003640c42100c11744080e41d1008541e507940e0007280d9400005a022040074420b141072984050005401441a54101040301a00300141c85040d001150340301e40b5119508030300307201001760000420040c005141880c013207d0309071107209201000c0c0e6100d07507140e0751007011014092040d0200002c1c105a22a0b03515828101080e0701c0d4054410030582403a1050300e540940d108511060082da100c1d62074908003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 517284937 1250 517283687 517283693
    0xd0b0904120f0c080708030114041a10140f07030206070c0b040308040c03140705040605010c0f0605060604030c0b0909060a1212110d0c020a05030303100e070306180b031216 76
    0x18403002c0300d500083c06500c400981c0400e01c064098180c16104003207107a0313207604080d0080c1c007a0000e000c0050040781000500c3ca10304412800b04090072070705890640d580203000c901100d01c04c2d103105094812100010f040041c1c010244001c0078601c0c000d4080300c240e0340b1042001c81d0781c6071803544040c2c502c140e0403002c03c0000b880f500c480c1e50840c2c0501c0b0580740300c907202e444012002d2659440c9030966480207104008501b0b01d4000e2600a08090814001c001890348035003081043d11040108050390f10307400241c90f0350b152016540a19003044d80d0b01041c54680c001d0000540c8001030581c0f10b44418000624145070a44140702521458041d039076460840c1c2e5a052405a040001d18003403102c0441d5904a00100300051090350044c0c0d501c40320760424a00500406690640040d40241c004200300401c8d1000a0013280841e81304005607925a03035003031401ca0050100d5044003070040c41004040400c41307c039400500c0090700460995000400450007100c162049041040181003054aa1404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 517286187 1250 517284937 517284947
    0x506012103050a03021c0e061b0406120f0203010305031e030402010906030c0c0203011104050108090d081f0305060f04051603111e09040f1205030103050718200d0b090412 75
    0x340142d400c015007084c00e5030090701c01025956151106d00c0f5981c284610010b6010062980c0280c2011015020700511805210782e51080d400b8000901103251020101d041d2194000501c10310301c81c0007151296100d10344244c0341d41c4500c0400703c500c810565185440d8854201b103030b0065905844078107203a8a810019800360010300b109105002c081e05070071025880a000d107001d40200090b0702c03030b030b0b45040c1800034000c2c0c04d000d042a1000e902000040c050036070402412074100c8015156000008414480c846c4801c8950f08005c0960040d0000d2003e030807842075200e800386109005a803440c05552070800c043c111148805007409210103100300e0390703041c04600124220700c00d08002c0801c15041d00850000f54044d130b01140c081c01c1142542051041000306608810240e141c55491940343d521903540e13500b0300d4000c5416144085040d90100c0c4907980c00540340740700110003d814a1501c41e04022142c000382d0020142500700788040a1500e04038003580d00c03c6a1107001c02c0381c4107103243d80c00c680c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 517287437 1250 517286187 517286197
    0xf01060824190b09193813020c03040515070b0a0f0f0204030b040524010504111b0c0909070609170c031c02010b060415030b03031308010603050601210305 68
    0x141180e44502052282e150004240c3c803558480499600704812500414115241c821421480350844000e140303000d81c07000021000da90300520706c080c8031522103001403404074910380108255440040e0a9103d40c5006c00030300300301c800031201c4c9a00ba2074030140c04103641c820450000c14040303280300091810f8000e6840405425000c0c80000b0f811612065104100c0e40950020b41d8905000000c00c000c0040c02c100034a45e8861122043d02107403080003200e0000380c01802001e200da034842c030399070b099582c100307054404079039000309404c1c0b000000f900e14940b55048842c0f914010b1854900054200a0008043c001c9400f1617543e41103c0e032405215000707001c4c034140118994000c4801406280d9401c02900c6c030075401c4415a55000750400307070080d08440101242e203000701e001780030420112000d038815070b000c0f01c0b8600380881c2c4c0181c890006402c5104220b98413040004101000c10500015403100d030580e44a11704454259807079085414005000402134041201b04445900000b4400c8018003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 517288687 1250 517287437 517287481
    0x9051e10030209101d0f03060f06032e0e0c01050d0e01061d010905010e0c0a0e0d05031318050114011d1c021f1b03020c030f01060824 59
    0x500f010300c03141c0011880300c00040319600282d450360300c5085448804100c00c03c960003c4800780803100070000400c3e101c410062000e0142100400025842e031005d1101000c00500c0d6808070110701c5480d00d01d004200110b843c0000010b203491060205078000050210100741c0503101c0e60709010b10280300d000948a00401c40c400380d52286c40000d254400100120340340c0141c0071502850b0360401812404a17030f0140d20107403c9030040d100340140b003c182d000b1600b0036002841d0006000c0f84d05808610000294400280107220004121001d0f140c048003a5094400309441c0bd01184142c1041200740c0c0c40038020b4001203403183c0504021580901040c5021320241450001009107180000c8c0391601116a20b0a490350300030f2a0324118a482064000c00e00d05460200011f1a80140001e11044c407850406001001c0c0d00340c54410b0600810050810030001412100e00d65080070805010f8545841200d0591207020302080c001c14111050f049800003860f5042c01c0784d6200d0400d20b14182c1c05c00d03000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 517289937 1250 517288687 517288691
    0x90606080a0b09191e020c0f011514060c0f0303060f030a150914060a09110405070801090e01020705010207060e1239012a030e0703022103031609051e1003 68
    0x45548800c84414001c011010741d04010384a807921000075023402c02c004c0e04080c0691400d100c4604048401c803a1109503403126803c01803911621000c9a00c6228910b449160752084460420111800100540c440c0c0c2040da024021020f8407820706544e0a42464024150a14030300c0705030f201040c07030b44890f01003402038242180b0b490110805904011050710b084102c940c5030f02443d000d100a4150b003866040e001c0d101008145002c0500400d02581070095003a81c03034a403040384401c02d0707094058611468000008540d150103519200703009041600c0e203618503015100580864400c04420388000c20b1801402035031a0542d0440c40c401d00d07080d15443c030115026500640d550031001d104e210840003511744100c40d611000000600501840110a0105801c0c80082e54001e03902003000000c41381c0c162a0b820724042408445400c09281c4802d040803480040304000c1c60300a4007520f00410642034880c91034080d26002800404000059900c5d515000d01c01e880000d07003000d022206852001c0c1c980 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 517291187 1250 517289937 517289951
    0x60f0f030a0b1f080f0603030a0c030212040f0312030612110312070b240d080f160f1103010c090608060a0f140f06040f12140601090606080a0b0919 65
    0x70b40c2030b180c842d2440d802c00ea03a03028103c4411340c0049189400030b00015101655107808000aa81ea20894040310704012000c407400c01054020080c42c0300e0142965880e40e02c40d03844d0900350201400c40c0c41b0036140040001500a2614081d1003114180e540200c520084032019884400c841d2204140c101d800d40304254020103e99000f4002e00903e9225a5140340c06040074204c1e0038016404130344505420258203c00711003135441b03103400c0c0c030040d9101c01d1031b070f481e05a6906911028064507075040b080829609a1501304107605d0b259560031441552080000e90016013454200c8610140640100703800303000600940740581001c546c800402070410070403a0320b650043d551829241d10102c01003504003145d5045140154421904460540741d140c10b0900d8841400e01000040c4221101d111003000e1a1081c00345075400c100064200d04d040307562a595030442000141301318852040040c107880041840c10040f0700035428403502c02400d04680d902c3d44070b150146080a0343c4000101540e84007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 517292437 1250 517291187 517291189
    0x607150f09110a140d030210090c05010801080601030b1b1c050604060b0903030a050a091509090f02071101030e010f2f0403050303070e060708130f05060f0f030a0b 72
    0x2050044444004080760341074940c6000d280c080c0498000d1840384860010500c0029460320020b804800b00b160810651681c600f800c3c1d003005041005881900e0410641400b801344098075075041f10001c0e80c600019a03651440192a030341c0a01008107031844843c0442c1100d030106400d10a242003030007280d07140901c003005402c9002e514401000b44180ca450402c0410314180c42460000d140d101c44540ca4002d05100107030300e03840f402d0034a00a0100108285050710321441d030754009000700d0b8400458180d40e0150240105c2d40c148602c20006060429802c4014464000c0d21500d65021003141041d0501d00d00650181c4201d402c020210342d030b100982c01c81c0a116000d0300c217038402c1c405004001c4800400942c0802010b00c4401c000c130301c50400c0300301300003040001107941c004481e00c0d00080301c1011900003042486401c401906480b000300d0540d031740c50300014140044554402c000401c0581d10000d1044601418140c43e0344c1860500461076103845a80007143c0c0a6001180054401d0300c01c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 517293687 1250 517292437 517292441
    0x14070b0a0e0f090a0b1302090303220510020604060c090302130e031e040807050d081206030a06020a020c04060609050303070308130c180f0212060d0615090e01060b0c06010302060715 80
    0x13a10103d8940d01e400085090b401c0214042e46011140c01083d460000c103100480c0c2c3d80c0c450014444151124090380001240030180307860302500c8010240000d24244a200039a107802c182c0b400d0f02c0342d504d02820144d131103005004440450354090700320800701003100b40c0c0da00140f590300d5811510b0300040001e070707082c52007010b02e030b4450b08000c900d0292190704144406203400c080d0b400c11801005c2e003400c00000b1425000654030741c05e411246009040c5e030b8100c04641058900e81c40141020f0020800c004141d4000c215501640340644003017000b0740c3c0d2040c040301c50180c40d00c00c858041e04100300c0c01c00468031031080180e0142c11407505211384411595001ea0320a1242c2c41205200c120500c2d0f000e031419507004001620606680550401030144140600e1100181c080340c4208100d034504400c012290300715801050b0040d40140d40c040da00c000c042c001d498165412a8694030780000401e4486031001600c1d5120b440c0b90040003140c1c216401d1000951000c1020350b0404000c2c5101c1400d50598 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 517294937 1250 517293687 517293691
    0x1050f0f04020c101503060b19170304030219051e1f0c0503041203180810231812180d0302100908070606050301090b1504021605030714070b0a0e0f09 66
    0x5c404103080305155050030412200c0038002140305105210581c0044002100e1800584455420016096252606d100d2544c0300d145e00081d04811242a5080c0080c804e01c900c0741240c0301034894003c2e00fa4500c20041001d4060f1102c1603100d038510b02981548002080d040d070620b0014180480d0102641c0c90b01c5155400903404001902c00d252180c004042d481003591624000c2c01681009043c10300b654191644c0101d48210407079699034021034603007451350280c4c1c98501c0c90b5105d0030b40c050420600640701481aa403062101b0712403040304c500c000b04480c0403913007030a80b9001c0c482e03026070380c610800014405440d01901144281150340342509064842e03030010302e02c5451035a54844251030704c00247c074400d6000a220745d25040030304007c24504980c603584114006080b1503c10390b05ca00150007401650044429480700f403e6034020410000000d101e298068080ea1000303404007000c00b607492685005e2803003800e00a01c00c60000da8002d80819400c510b008008003070045c90300c80460010001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 517296187 1250 517294937 517294961
    0xa080a1812031403010602120904090f2607150e0f0f0601060f0906080a0b04060b1309140601021f11030f070e0102030307090e0a1103190501050f0f04020c10 69
    0x5404480825803c4140102001205209181150b14282d03000e501e5210f41c09842c092248001303414040c90792207500084403558048600905054281850b904840c5800c8102c41c50b5005001d444801e10383e40826a0721302035000f40041100d8800b1044203010307082c54041c0700d107140b05951900b1000c00c000d2001d520040080b81c020f02d069031602400512100c0070710304110901085550900011350701141c0154008440c12000c0381d403400d18000701d801011540d100104120300481e075440004400d0310303180102d43c50030000b80511f0310945500341c098601034403440e0141c1d104000c030145186000c900c0340a00d0321f40490026210f02241c0e5500b04980c0100c5550348024004401c204140e034005a010159090030301c000d40c11485c00d072102901c81442406480400920180081d400410941211400043c1108625102e042001c002c2070641d641d10101e5005c68140300011a16080c081c54204035444010841e0a0290591007448029404500010094020740f608001040c210740107115410203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 517297437 1250 517296187 517296209
    0x30515040501140106050304080a020a060e01060509060a12031d1f11010c0801180905030a020105180d050f0304061d21120105010315231206090a080a18 67
    0x140c1498a2821607100c80404810320319070b040144903140d400740070f0b40d40c015170107980250b40d403403c0b500907484c01c14030342d00082000c0d04050103824507141c1034201c1c404444c2c05030b40d100c0664640d0000c221a0590b0b84c003c1d01d6121007005020800b0a2150600882181c02d5441d800c0201401002140410511030208400c0c41c031041548628542d21150b041a14520072000b045202041040140742c0344040c8921607561800b40014880781c4c880c1c0e44086c5185a204081300d031755100228000c0c0c0030b4142103030000b005002e07000c43c04007070000c041181c1481c0f030520b9944600e8070945580c807a4098001400a44940760f454070f1444803214085000c190900108000b4000d0684000403c030000044011906c1080340030300654225150302820241507074800d08010500208903480318806d50080d0703000e00c10010000c0c2c101061400c0000c01c1c40c081440a84448074404401881f032a555407041d1a201019408062100040b400e698040c0c2820052440c00e43d101d540b820700030305c04101564100c501d48003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 517298687 1250 517297437 517297441
    0x31509030415140909270c0915032a031c020601150c0f0c050d03080103050f0f120706020c06010608010501090e0403051c0e010f02190e01080705030c0904090f061a0a120c030515 78
    0x100e02304003c1e90b880711000c06820100c2a42401103920b03405020140d11010f4070f0460700001e4030500485d10b5400d03201c0942141d070060442402c0c0554040000510005805800000b0640c01c2c0c02c2c2c1d100302e0041032507880304503175100503907100c44000d2100401510200400c4002003640e9543da4400d00b0094000d6592003043d50550030001d05141404042c19010780c070802d9080b0f000c80e00402c0840311a140191602e85441503401e00c20084d100e46c0143c04002d01a140002c170b8115004034059040c0d99003030741c6402400362182c0b4281c0e002641560060045201400030f0f545035642000c3d54510000701240c007259501800300b6550039104484241d00318182c0203d0001e541a400340808500070030b40e450a03803141400000040d04981000d00071804100b4000000b44402c0e03c40c004456201001134002c219035800c0c2e041a0700001c108a03000c42e05181844005800501c1101030030600d01001011000715616140b502d50103020041d0302141d00203882400000401d20901011010f2410008020154 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 517299937 1250 517298687 517298689
    0x90a03031106070e0f01081302041407020d080106091503060b19030b030d1403071107030c170111030601124a0a03050702031509030415140909270c 65
    0x2000700182450208038003480310004d2982e0b41d40341e42070040400e08040500f51a40e410104c1c101c5c1e100030380a50010b040c0300030220b140815204180c441c0c14640c1c00c5d01c0c2d0b00b03a00340904946481007071144d07000051850b0001c0c01401c0006801683c0251107090008401d50307035041034140c1d60826520503600b040261000f414854050040d60f0210704100c0c044e0050784080003000e0203215190308040055203010001401d07540c01803541d107805101c014100c40c4a2640d030310782684464150b00440d40c07105180c00d101c0c54800d005000d1104110b002000c0305041d9603540c00111099034841d40b60302c80c040d845440200411041c1580c07a51300324089141041c0201e034011965030340000c6000000e00d580030301616022225004625600c0d080c1c0e01d0f01c0c0103640c135040740c00041c1c43c20b11210800200540c1071014000019000001030044402800c480040d4500680054400b170000010307095007004100420280c034501101803a50000301c0c0543c10f03800b000c140580d0235845050002c03954859100070401242 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 517301187 1250 517299937 517299943
    0xd05060903090f1807030b1909020d0e01050405070510020a0b0c0a0e01050f0f030a0b13150801090206040302060a05191d04060b120405070914010515030115080a02090a030311 77
    0x1200001e66441240c4e6101c400a200c07140c20081c100c5040542d144a008807030390307804020800e140600100121300f141c96641160080d4400e0b968890070b20300c0c6c000c00c17801421040c0105842160000060102070b07140c603062150b403a11540d482001c6002c0d900c54003001800501d070703560103480010801034842d9998800030301652922140c0314140102441903040880805040750f5082c500c8040d0280c403a1140040c80d400f50402030400b562004070040400400e4129a0201111015000712041500c0c2e460366400c0c03c0301c50502d0041e4000c0400c000a101505002c402840350344241d141c801c1c0781203200c0c014605448405051800012000175100030050144041d00103000401c0790704111051600b00414810300c01c540445404802c45030000f07050042c24003083c1d006007841d15040c080450045e0290a94200034050144540101000111070b100780c041920f0684000e103180c40282c00c0491030070713600000c005200080c42a004c00c816400d6441c0d01400000461103510b9500198251030000d600b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 517302437 1250 517301187 517301209
    0x1510060206042d24050f0c180315090d03050901050c07030309030c08160b15090712180b0a0c0e0a060309050106050405090a1e1208060d0506090309 65
    0x10455001c68280000310302110503120f83e0704440d8070b200740b00982c4a058901c200000311409840355101602c00e000812807050b5418034940c0540d0b0405ca160f03501420b1110806094401d070052540a000f001c0854456143d0a000d08100400b03e40300b4000031080001d03400411500b00e01c0329040541079a00c43c07a0503008198003da035010085c4894a84140001842c0c041d410014007016210b0700084180760240a8800792190024080c035690202d14080014030356400b0301c1180c2c41142e200001e82144e41c03400c4851141c61009081045517100d01000300c851078140e0341001d501564034200540c10341e11501080c0201c902c41d8001c002c061030709119403000c0f107c1c220100000e20400c0240743c8070380c0e03950480c018103403940c60800040041e11803e095004004a801040d0050310b000144032401c080000c100c00c0c8070b48602101c8407504850160b0030a400300303902d0010208465038444159030703805642c035242d00000c02b5002607035030321442c0c4410b407420405139107404458100240743c86507400d0000c840a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 517303687 1250 517302437 517302449
    0xc050706020c07032312030c221d090303060d021504060e040b01030e0703080a11100b0a0605040e0a0f14070e04060f0501140d06030203070311010f110a12020f1510 72
    0x40804c0030202c00c160300c804102e655100c03401b200000198011800405650964801c084880c80500004039541c1c0036140030700890385a50030041d100b10b4581d01c0141c02d47e2046840341c01440c29511210280700000120701c4040764010b421400b21340761019404041c1000341941e40d10070b1854881c4109120403121400d00e0f060400d4100f520f190b00030200002c0400440354001c400300e94408070908100c0d00c100c0c070318000d441c403030150504103a10089990407036200c99104941104101d80d441c4400d482500c41c5104400300c00a541001907417500143d80041c01d030080212000c651820145181849494222003900c0402d008102480751030a05105402c007401f01001034580d401c2c24000041d01400344141088110300307000403441c00040807604400d000303541c0902104c041c02d40781e140c14142004004652030010f01c1c0304051820080c451600b428440c0507840c040d0000042c2d83d00c5c0e0303a01610708081003505510401030040781000f801c01800c91400524469800a03013412240c41508507d181e220b6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 517304937 1250 517303687 517303733
    0xd170609070e011d150d05010b0316030e0a020d0f05060709140d050703140607080906040f0605040c17070e0c0f0429030114032e0c050706020c0703 65
    0x321455030440b03511004031009007070000c15004645002e00803460b0302c4403880d81008892101d404c0300c102d00405401e0b00703034010310240b100d030ba20384115550a010885804003c1c929001c2c250035003d0180c0c0c0207a451540b103c0c10f5401c9c8d44415000310f947d0b120001800c507140302142090030203000051101c282c01801a150440c1e00c14a4103803401203807480c80b540300b40310360541180340c0b040040410807007000315401075002a000080b0000e140e00e8010803991300c1e021841280001d414100080f4400d48165030084886200d9840341e02c9100050030000c0040354112000400402c3c0802c03560030b00c2c403240c141d50008100007070814000284200024000b60380c002000e110f2144400d01400541e01501c080c1550410440401f0100040048106042c1c0180000010020803030003201c900008848105500f10f4118559031400890000741c0440340b5012076039008500a000c00d841d80090260341112302d042800c00420b0344440089070301c0300081c0200340c3e104600403c10002e0ba90146103043c18001d002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 517306187 1250 517304937 517304941
    0x9030c0b071e03021e03120c0a020d03110319020d0f020a090602160e0c16080406110f0601060e010306170a02010807051905071403070b011410050d1109030d170609 72
    0x4080d596190f601c1d041001c00d18194515030300108204180d4a0011300007a02c0710050410b0b035080031235507124045002c010702601c661000c1081c024040c55521034000c0900e1450344e0342c0d040c102c56101c6c8101002c1003c440d000c00c500042c800707250191010740d900000300140c2e1200b010001030420980f66000c1015074028201c000f810900324820941140c803000075203203aa44c3d0704401c020292096107501e401c420603152584c81806206405001510090b84a111441600c98a41ea96650f4500e5810269600c00d200601c001c0b445070440d412000303010704000c01d1842e00c42170808a05402340c0440074540d80045044015580e20a040a03003145c0c0a0034410b1a0605074403001c106240c048000d10184080040c0b01d404120b1300c0071010a111100805580d181e4800f4a0310002c401028424440c600d644030540904610300590030318050136494860358074015440200c0e00c0070701102c400004c041d240c240024001d42d1824852400d40d6840d690f5020035003024009608418a40900718a00600023402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 517307437 1250 517306187 517306193
    0x70f0614030109020a030603050d0513051c0f02030106080a03021c0903120f090b07050d02060106050f070f020604051f03110405010906050d150b0c10230709030c0b071e 74
    0x4101d03415a002210051380d18007005400b64082c2081d640000c00a1085e94108602264443c02030303c050441030a56064481e9035108002c1c0280300d41c9998160000505000c0d40012800c11107124102d101074004202c181d51002e02070f0406e2a80c000540242e00560b80501402e580c811005600c0906410b15541c02411500d030fa22200c005880007002703200030300e80c800c581c10380500401002000c05030031a698a400030700d0116240d102409890000d0311824001040c40307400740003a600d0a03180302000c141092440d8880c003601d000d5400b026a08000204000b2840340c0b500301304044001c000041c2822901c043c55802030840e1688802004400402c5c402408241e0b0700103a0301044818620304591a110312102103c0200310044080746036003401080000c00b00504405404009000400d031006c0c40008494001a1042e84682c0d00c1110607048039030b04040f135000e100c2d5820100c0c2d490891072050300d0b556142825000d6070071a0f811003401207440010400c0d508901d00038008003a0b80400d100b800d5075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 517308687 1250 517307437 517307477
    0x907020a0308040c0e04080d0b030a0215070303020f0d0b01082208030601031e05090d09080a02151605011406030a0309060302090609090a1a061201060503060406090e070f06 76
    0x44001e04000039040480e0611000300410400b801d94407481010505141c0f501030426805124030781c60392400c1080135420307468041101b5240c45e0f00a0940c40f04c042c003500605815501a050441c103059003840008090f04c0320708042c00701204004400920000312100260040500400401d4070503e40312941c840c203c0707081b82214010743c0c021500d40d22900c03242c0050b00a010180e86909520341c0100420020a646400060240c2d2039001543c056502e1000300310b90200c0c5d140a2001c140d809925a0350041c00c2c4180948590001c8444003800c12603a8903582c0c4000000748425603180c0e458540011181030300b00c0d02d160300304100310300034800b4001c1d81e9000f5100884c81d00c207400038140e004c20741c4920394407202c2c04c590410600a050800e039251840000f002400320b40403001410786042c91910b42ca0400f8400c50380d822049140811803a0f00c3c25038202c03003c4c0d000a10603504540c81e0000022010403a029a07120101c414000e80049030525030002c081134081d500c420704110402c4004a0040d07070b10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 517309937 1250 517308687 517308703
    0x41b05030a0f0b0709030203151008070503070b07051f0e061312080705160602120c0403021f1206060c02010e030705010c08030a110301061d0d1104090f02040c120b090702 75
    0xf4410600c00e543d080015034030b0300010740c4080c1d01340c094094150b00a1003000340043c800c01c0032003e903d24903601c078000e09548414038042c02c0c1d017580c450b00040c0005a50f40c0050101c0c3c0e40b05400702c40705002c0d103101c83c41c40c0c00300d88501c18044903281e44c3d02401c01030313082c040c05074450101c1440070091183c03900d82d1b40740c0743e40081444d001d0200040100340160711440c103c48074501c945084c05175010346450500003d601c4440b6040041da8510007081003014044102c504072030b0020048507035580b11601e25020022600210410700588440e02c881003103131409040003c10050329900f5801c1c01c0c5000151481031007512032031090308841c8003484240e80020b040c40c44a40c1014905803641c0d120407036100142649070380442440f00c0440005a29680008100501010150810300501c07960040c031402034034036030005203411104606841c0700e0410790310501d8240d000d5101138601464031f0b00424100c13400c42e04003100085400c0407003113800c0954080c0d0104071905644110307451505440c025110411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 517311187 1250 517309937 517309943
    0x510021b0d18091805030a020a1a090307120507060c0c1a2a0c03180a0b03090c0d02030a02040c030203060f030f100c0c050601060509040e010203090706030c03020c0303041b05030a0f 80
    0x156844650502e804d9103600356540b6400340071030340d80b1081ca8070007030341d1081c410100b1200540c8030a03444548180710420603014900650056081c035001d5580c0c920003641005246082050501044004c100366004200d0a60295154024115030301d0a0448070329201c100e01402e50740d030030340602400c00903100c4504501113307141c031000c170b802598128030014480c10386804464400864007100308020910440d80d90316003100d014102e031350780c1c540c0d00c051030000f2100c81c50700e40c01c0025005240c0c04c0c001701d0708080a200405507040410241d0028080b10040401140081d0303000c01048080e007482e04031016403102c200d005007100b08031141010703aa00010307401e840d145500d4610000784240218050040c00b68800144c407015078541e04010500e41044448a11450a09481542c00c640600c00c40b4040c0c1251000b03443c60790b0400d00264040c210440b151000c00d40d003081450f0520700140042c6000e1031144030510704c0d5054100203400044440d41140d4440d810444610340040d40343e00d070314201294 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 517312437 1250 517311187 517311191
    0x105070f061a090a0b010e01110a0f02010e10020f0f0a0b0115050912061f151107091a040b030d0206070c050304090e0d17010503030906070510021b0d1809 68
    0x6048800081c00c01d00802c6903030400e15480c01e00102c4021600720902c1d0f0082170707031007a841e030990000440c0c5c0941920a8a115070300220180c0d030114000c2024241c2d0240103060207860030880b100460320440024042d040180c020111003448500180074100c210300f01d98000f404000c0094688a40446040c80f1b024401503550060070801406039080e2140c0e010300428a03580011050071941d100c20040700d180c40c240802452001140c15409612001c0d10340e116803410118002d10020348010a8081540c02180f00345540003441074110f00070300c3c004270302038082c18000705107003824081540c0074201d140d44240c0009440c045890f50010302d00358407184d2480c21000700c054030709003582188a140c10504829042c1484a091003c0000d00c011030140d5a66030f144c0714039030718046011000390a01419070b150300108803249035898104041c00b480390046017691820305a030301c405000c0340d200180224911500101400c1c00380028440302210310385908010040440111008603096a180544c520481e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 517313687 1250 517312437 517312451
    0x60606140a080901090501060f0e060607081c0b0a09150b070b07050d1b0903110307060f0c05032223100c1103010c09090b030c0303030c0a2106090b0105070f06 70
    0xf0400350040440e00f07030004000c21030a0b840d485031000c1c003a490300400f001d030b510725130106116040c02c0007150105a00010b65a0610116181c034681803001d9510454400e1b49480c500d09032541c841031688010540641d00144803c6580f440c0c6036000f045504c1526080030911030880454074829226034019031515002d60350720f0041125a00801c2c190000d007080400702c41000c80100e1f0042c0c0030760141c90103200d4440c0440d045078209079807030b1258010640010a186a02e40341d89000d2400510014071804c25641040e10030800b031069071440901a020300306000da010807480098090700440140ca0b00c070103c1d03078250204081031030143d05007007038400c200f8402052403c0c072000500c01c081d1410014001d1218540000005090190398002d40003448e28200c007214183c600000e01040c0054040c001e581540c0d601440301443d07801c09810302c0144034500306c102031035441d080c07109a07c03143c2155002800b5801e0440c460111842d466916040c40b004016040201d4840104440e0081c0e024901240ea0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 517314937 1250 517313687 517313701
    0x36040e03130f05041a13020a0507080f041e080705090c040e0f04060b0103060e010b03040212030a020d1b030519090f0602100c030b09010e04030905060d09060606140a08 74
    0xd44100400380c41c00040980010800038501c4001100b282d20031102405004640d181e0740c07110001400006a10005c0c0c040a019507083e250003401034044141000c42c2080d0a0b500e035214282d00040b0400f01400300010103000f88201105a4103181c1d50301c00842c5200f03818002d2180d0350f1070003406214454803044c0c002134000d00500c0c044601600b0700080744049818a005540b10b00f04c010748048901b1030a2184c0701e410b0b54443e202e20000c0340d00c044414003242c2d290120b180003d6201400076a001012a1a80e03131581c0001c00040404d8503443d401040d0020840100130041c5084030b4203080e5040400211001007070f400429104000d205030001e6111904c441021390354581540d10401491052070f0000a05980116001c2c001a801800178881c0814500c000c40440300c0001d0690f42c44118200107100d030b14030032042a0341c40b0b4400d040032a1400e840c0c100064840d004002c085a21584420511042115038041c807801000c0d9414120410200c41075100c1c0c16000f400c2044081240c05400921a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 517316187 1250 517314937 517314943
    0x10060b1602041d06090c03010e030901050c1011130b030709180e01230f01050a06120f050f150d02100f0c1704080d05030c0922050c36040e 61
    0x102801169a0381400f40c12089801e49603c01202c608286000705800c00e03043d42410700a080f0075041100c0910b00d03104181e40103542035040899507800a205100300740c845822944240e2001040c0410720310b4448010401e0f801050751b113504034003c03019007031050204c2c0c144c01000100a942c0280b4030701c4d0408042c03000c00b4008200000515946609200b003580035503e10744000400503847c20952405a948d0f0400c0c025040b01c00e00c81d850704400c90308020800503100d46081015041d6042001c107210421b1540032056800549002c20101d00c2e0340c0600194186004401a80200031f0b40c5901c4c840f0159000526854020240242440b000751900703e103261094405441c0940c2c000004002caa440314640c66064000b400b411000d88111070814001601036401c1e01e00c07030030254a80c00c0c070306808003092041501217281c0701c03420f0004a0410740b90f6403181d07004d460f10920350102c446480c0c845c5030703403440b1f9403a030840c0d00414058091000051a80b017511480304c0c80d00c0381170398080368038110300c4100c0345 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 517317437 1250 517316187 517316201
    0x91c03080f04140703060e011401210305070c080c1008070e011407020319020a080f06010312210f050604060302060403020405042307080c061204060b060f041710060b160204 76
    0x1c0180621039010041010a0388000c47c4031204900030400e600840010780142642030040c100ca440b810711449004400c80d000301340c6403034820f26000381001c0d01560761241c00c0d0000c1c0c00000183c0c0003e81d6000bc1d9003000081c01c1001b98652401030341074145500090600060119030030b04116540f8090300c0e070710500408a440250b80641102c14040301c06154003141c4102c104120302c00d803034400c00080c100100241580e84015100b016241691940e9910003014070203e689200b40a1100010031080c0c2050014826041140e140816820383c1603003c4000c035000113101c14441d41c5001c40500c0961211410780b410340f41d041d10002265152400c00400c4401448402d074191401020300120842d4080b50300b80450300003000f183c80402d030310f00812060b801100c10b03020f200e0040200040120300950000d030301c03094000c0e201901d0809248000e202e5a0f01507045121484016211460601401c1003801d030003000400040111038200402d01d5151722441c80080d02103000010200195038403640b00c84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 517318687 1250 517317437 517317473
    0x603030c0703081e04030203060a020c010b0411030412050a200f0105010f361a031002070c0909030516080d1a032b181a091c03080f04 59
    0x107200d0380d9207140c030140740d52000c030241800011021500410320881015501900c0c1e000b0041c0c229a80c8007100c0308025044109002000d40d2124400706042c0c84a01c120706040c004001403d940c1d2600c3d042244180c422500c03103004000c42008455585a44862110040c0c400da142e80320821030203040c8a0b180443c1401ca2103865480d11000203050740008040c4030459819400381003003248007003045e407840c614103c840c038402280c01c0e0903800d91884507401604641c0c41c0d2280c410f240c4050101081c5012006440b00c8001e036400555002400440030251004110307c0b0b0f810301c80751a85070b42c001d2060203000340c144819900111560100310b6030005440d00c00030512820007184107144822082c0c41e0000c00014005c0c010000580112071203030038003141208407400c0304050410005021501008003481d1412090741c04207002c100c04001d21065001000381490a6071a500302c1c204003d0300c3c2c1c420080c5100c1421b446241000041d07085602e00d44d00c0b2000708008103407666613041c1541940e548542e88 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 517319937 1250 517318687 517318693
    0x607050c1614130203060d0303050901090b0f060123040e04030528030b010206040c0b0a050d021201061e0c060c030b030a0309061b15090609080721030614090603030c 73
    0x8511181401a410721a44007111a01c490103441d00043d0304078031050716425008110007404501007406904401d40040b1704200029680c0b4a580f80c0084528060f5070300c60009401c1824002c83d982c0c0303c119509107000040d181506090040701001c8140f0491142901c0016990002820715005030140d65840080391101d00349104071980c038018130b5a0340c00c0118082454900c2d0103140d5440010101c4c4503e500c00248a1a01e040c086009002d4000b4411102000400c0010240c00c009a002070b280300ca05905c00280d0950400c00060005201e4040c25042d415170388440011b0280d10540b54007109820450024200c0341040044001d0070481075a540c01d40b03c0c0d001b45004043e0710009003011a6115030352003072589101a00c40039403418440f0040c1844011582e104528860b0764821035216100d0728000580f004580e03501c203525000003d056500d03651040d52001c0700c0c080300140c08158110752a04006075421b0028a44000c1c0c900c0d10103134016222000001c40135101002101c0107030300c80200b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 517321187 1250 517319937 517319939
    0xc03050a0227010320030610090608060409020a050d0f06061d070c030c020a06080a050a0b2b0f08030709050f0603160e03031c15051f0c0605070903030e120607050c16 73
    0x6010306d80c4160798a5000d00442d9064600300c0340700e44028020307039039550755108540d1940803c00000d4450100141e81c0301030280c100103850364540c10140080d900c208480c180e000740da41003890850342668011885000c40d00c000d0808081d02c40c0405034480020300385510342d600a030400721005104024006d41010b4140c202042442d00869024880e0520f8002442103688850041080d1600002001e8111096117502e541d1400b00c25420040303840340301003c200340081d039200d92a42d001b18800680d0034540c00000e0080b255403125100c000362000343d4640d840100d40201046491000514440c61b02500c4828051281e2061280390b817020130081c00c4940741c6c400d15804038601c0b60050b80364081d69241c20800d004110b0440b0120049503070090295120f050360001c0c07240341001099010040102ca600402e000503403070b1041600802d08c03561f0360690b0030704528020f85040398000c51948118103c00010480d0340c8001061a805603052030010380350080070f2045803402c2d00d95240d40b0b13510001071034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 517322437 1250 517321187 517321241
    0x141504051020010c121a030d051b03090906040e031207030615170c1e040305010c08070c0f1106070602070501050603060c0f030a090c180c03050a02270103 68
    0x905002d25035528104601144994061500702d41040c00c035440072802e04411040480800e138002130507508101c50034440c4402800003c1e0500d0010070b420400700d840442c2d0400c090700409841030310740c0f01c1d000c01986050344100c0007070a010401072901d441903498000700b0348100800c4c41651a2107110510b140d045050254024015160b203004207045c6a801d0103111040c070f84900652002c80440171083c4140d5290780c0a400f82d254040004000b0070007200c03c0e007000506503040200000d602460000a011600c414000c20210b4090711000811206410711404182c2c10881408441ea1040170520031a82103c04030b03039540500b20380a0056071020501400b44003064102038030610f0110117881e41951040700224442c09003110360000d54805200041d040f0b070990b400010703208d014109175015035a54494030404000100700925000d03403a214034100446c1c00d802080c1e040b8144130b40c01d50a1a8118941d803007002110104000c0640584806510310390180d0b005c1000c5000414107000000a444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 517323687 1250 517322437 517322447
    0xf01030209210c030316020d0309030503040306020a0201110309030a0e012a110102060f010303031a101e09120b0402060d02031e07020a02150c010e010608010c02070803041415040510 80
    0x1c0e829030200c3c042c90024000703034075001c001c480c155019011405200400742d000d001c641c02802c03070201d060261090010000ca101040503100451003003402607a5600d020300c00a003034419620645220f10818024425a1240841070301e50301d00343c034504141900310110041b2420003210303082e00d449000c40c4c00401d01d46081c081070144158010802030180c900b440004903643c0c08101c4004407120001d4005000182c404c1c0c01c00d4651826082a080228802034000f43c10302d1a4000e52038081038800340080101c02c0c00c180c0800c0401550708241840e207103408842030800340e0010004140c80c5144000404664a10090304c0c40c628001d14115100d1604246c0d0002d4000603007201c0b071850700a0350006444c1c80c0300051302003c565014000301c4a6001450051034190040f0303030091015502c407000b9220603007003480750307000600b1004000b00c0c07005103801d4064280b00242d001400340c2d800c03c000038416038200406414103400305980440c1050700320320424666001d40d400032035000845001d4208040da000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 517324937 1250 517323687 517323739
    0x110307020708070b0f1218060c12060f091b0403330209130504141c11060c1219060308130e091b060c07080312070f0e0f01030209 57
    0x5000326070f6071a80b03c45003443c46000f013442c0e500ba000000c021201064000720503164200228175404100550300e400d650703003014011203007030003006c90102c0c104840707800c1c440280b5080708007510740198800b100800305211050080c200c03032500395401e05000440219004503001181c100d008ca038001c00b03070016212807008840d459569446810b1040381d075080c01c20b100704c030031104000300320384030003140f40d00c2d9040a0300000380281c803140d01c55614154101418008049000f440c0390a0030210340c1441005000707901041040402c0f544100c0410000c0f2102e1030840d004000728903141a003c3da00c0c24000d2039500000042030081c5810804004108110b41c400340c0b00081000f5501c0750650345502c109600e1442c201c80e00007059101c01301ca06600d1407201c1c4070104c0aa00603107401e140840c80355505203418025400340101c0c2d8800504121a6107071520705c0c503084146032400e106105880361000780580a0030301010300c6a1004000768407681e000e54129030035400d028102e44051598015068281e03048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 517326187 1250 517324937 517324949
    0x120e1201020a182702040b0c0601051014030103020d1119050420121915180e1b03030d051305071e06030203040f080403050624010503010b030a1103070207 68
    0x81e143d1004524502d907040c80580703c0c4800d425550801c188840208414405410328209500b004007003451008100101a001a194000c00e06035241c6070600185070260400d05d401c1141202000d111a00d40b101100c0c1102d8040b202c0c0304031030b6007034240601c0d0301061007a007540c8144841a40b03600a54400040002c644c0125401c111421106000c10b00c400908030220001e00801c200b000c0242000030200e581200020340c510b441d92000303c0020044a180b0031020518035100c46c0c0c1084005410b4260060600100c80141b000c1c6c0d902800450382c60704400100099281c0d04100040103840030020f94005482002040c40b06052401e0704000c2e2500541c016601c901034100b002c01c0c9010305102c0200043c0307400120546103441c2002c102d0003900003810803240090303ea11a00d0201e0001d40c040e00c017a5004501600c1203007010490240400c2000521043c550f80c1000c040703a16070f81040589044401400149540b0707903500b0030b500e004000034042055a410301005104071943d0025881055440b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 517327437 1250 517326187 517326197
    0x326130f1a07060525030209042405011b150c1206080607030e0307050a0b07110d090b0307030f091202010e031801050f0c030708070209061c120e1201020a 68
    0x61207840c000a034079044140c09198a10401c181000035220b0b911441d442001ca000ba042e100e103080354103080907040700d800000043e8012442040f545054455a1600e0315000d010803650051f844003540308030411b200701410f00020450140b07013014484c41205a156000b202c403410301030300c0c1703812400606a080c0c1c1c10700041c00d208102c0c0321560061203800143d8500b54000c0119070344242040300500f081c040001b5050200340090800075004100705400e0078410940c01c2590314068000400742c1d0442d04020005600540802c0b5202d50451580e0081d02d901c20324543d44ca9440e00300c10360140030b9002c02244104d00d070140e030341d0501850410343c00b002e000581c000d116103040e49603c503a030380c025180d00441c128034441043c4e46940c0100300500004003217840140c00c1505000e845815500f0840d8107039802d501c005040401c40c038002c840a50310040858992900c1c000d64042d000d410041d011008203e9145210010a05409003050b000b012500800201c42100750100d03a41c040d402c440c400402041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 517328687 1250 517327437 517327439
    0x36072c0a090b0a090c0918020d050c0325030b070e030d0e040c09030b0c07170310050307060804030509010c1718090703050103020607201e090603160326130f 69
    0xc603860003034044d0142c010085100107402c0c065400005c050800318003050140d00c01058006881d1040d0548440d0700880241180c0200d640a02d4100760201e50a4200d1010b02e0f011a1104020040900280c1e43c1000310780c1c4840d51190010399000f03040c0c2c400325501d0f21030080b04d0ba01c442d034407011200403200c1c107840600c0107601440017991000e0460000821a0090030009405000d4820117003180500510f1580d050462006054199600588402c01c0881c24401c0612160404001c1007006002c02d1804002c246829100102540078038642036041200c8039220105009441c030f141d10b0b0207154850341541e14081c0c260024011000400024003e409c3c076000149918000d1240303031704032072300584954640a456034a48a81a03403148031500902c0010815420b2505d801030b240c507407500e5494141b440c4403040130402602d06001808a84250b000d01d05540d10041150694022a5030101c003448903e041e0105443c042c4c9694145038480c5240411020030003400c2c616030030100d54003514980c1ca82 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 517329937 1250 517328687 517328701
    0x9100c0e0604031514100e040f080c0a0506010b040b2a03040b040509011203050a08090a0501060e2a0a050903010b0402030a14010609030515061836072c0a090b 70
    0x305ea000c03103040d01e80a08039a010019240010a86c0e40d000c0d1150381203080f4101e141d540c1c0555500700410206041cae1007101c0c1c1c1400c00c4070401002c0e02400c400b5065900b0240303401c10100d805c1c8a0751103180c4030b80000d03158440344800008031340c4103000d041074207036500c95403501440c28183d0031a125081c4a000804c000003041c2502c056a4481a60035540c0e01c1d00c1c1052603642541c0c44030010708070103c144280a010008540300f84520b1002d80038520340550181000424648000074454110001e2107021540268150007002101c9011100b41803454442522200007070041ca0103c1180d0341090001080041642d0240d01035407061456586100880e601e88608881e525581d000040640c0e000d84403031030107040c12000f0369a0043c0010048140c1c0c04290000358440413054841b130000d00320325000c001c406829a401d480d403002c0c1b42e401c0464000b1a034450540d40d0304032403050080c048444490389a0100210b4034214006400c1c003003400e000c3c10031540303010062a09140903180100e541d4082540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 517331187 1250 517329937 517329971
    0x190213330e01050105090d05011103070806040203060102060712020408010e0c0a0b0309060402061621081608011a0c06010f150314160504081603050609030309100c0e06040315 77
    0x180c403903004495507160700f401c0041d500c82d840860315035032141040491070300182c000d001e01c00310362000070300e0307142c43e03041000001e0706040001d809144294010b00400c010380e40e0000e0380c3e61344480c0601c1d0484400d0581e4500304001d00c2540c01c152219400c01d44480c4c2e540900155844895505031103025449941e9400110303075000075a060300c0181c000d400440c2c054a4064090840180f40160501f4450050f13501d0710100e250403a90340c255500d150355004c008a40158940d81c0c00940c0003442404142d40d128000e001010500402c3c060850305e0b40207012400c0207038203803414900c2c00c01c115455940c40302082420600540f2401d8184441c035809285414407a01416042040c00d044c103600c2500c0308802208020900d504150800c503051100089210080201003000f076600c5603558801d50070750030701c1410301000804008256100b042886511030340001c40b220040460390000605101c0001d04480080702012080d502040216002c03060280100b05224910101c103400c006007508201003d603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 517332437 1250 517331187 517331189
    0x510080118020a18270509030a0c05011d061008030414120a0606060c020405010b0406022a090403030c030f0b030d050a1407050303010f0e060319021333 67
    0x703060324a04040c1c086620307540c0c0241c0042400c50421504401c01000e074452200c642e5840540c03565200e0900b818040000411410035180940c001c1c445c0d45000181c1d50398a100d0301d0202410807180451403414000d080d408442c00d4800700e10304140d1000141e500d19603c41041e2242d5080d584244000580d03180008104e60031034020b0b03012100030005ca1020042002244054410345004107080240002d580d84100b202520681e140e600f2062140d005020440d00160004c1008290400052084540010380c0120000711803008440080188006c1c0c4400c100c1649003603005001c10080c0710800d0b0b0160016002c0d042e40307136010052102c15080d14010769052860003505a08600c0e01c041d42a4410002410b42030501d0401c0e15012806d04881c1c8903d610241c000c0c0c60700d400c08401400a41c03201206c5000510301030140391402d0601c60000b17610f40d14014007421503003503070706059011503c0b80d100c01010400390f90020001c180c4840301a030300256414130740c0e0f050030745401c00000c203442c0c45c5801c0b44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 517333687 1250 517332437 517332449
    0x910090531053606090622020f09040f1e0b090a11011404050a0803040e161202130302040911040b032e1104060f030501091e050a180c05100801 63
    0x1003590032806039000f18540da103010714038000d0b9002c411180402d004001503401001024024403175850450390002c2003c121300480440c1c079008000c9030000da5189070a610b01d1500407a401620b5403214a40248502c04240004050076256041054550011003451810a0155600c0d8046a0728100b806442c0c0e502c046005090075006d0311501e465500c00c100c044030742c512400906280c152550002228420039500042c07843d840000e0034005110340c0320485401c280351142c0e80041e005000000740036040c890900395880c5038007003070826085825540440003150017070005c0003e0606821306180480107a902c0034012428041c86801d107050003d5009141e02d60290f14005000b07040307403030102c8100744070361064404d0f442c1c1139484500d290900003440103124544521311543c0201c4006015607a05a12141185107400b00003440b1000140064080085030200041c03947d8078101036030000d18041d1404903240041c00e00b103604001c180c1222000b501c2c0c0841e0310b0390b1020580c2d2000c4940403000d000700c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 517334937 1250 517333687 517333711
    0x4050a0b0303120603030c011a190b07060f090602040b13080c030a23151605040b04030813230103060816030314040e1501030b030111091009053105 65
    0xf22600c04800c810041d0003001c0181520700e80910041d14a00b951001c0c1c01d81c81c190900f01440c062149405405036424200b040c3c4081c00a500d0305921840c07030300442502510300c030749640c44151032032500d0b0321407400164001000c5450b9078075900400c07915003182c410070000010130031001c100c101000400798030501d4010020480c6e00c0265691030080c0825071100a182081101902c501c0001401181000080345503440c1081c0b60180400000e41d80448510080c0441048248002c100c040211800e0faa00880d02c140da40303042e081441900c200715400141c4552441140060407442a550039a0030b0409903001d0000c540c650031120303200c90800d038400307502c032844c550104002401102d0912440030300350701d51070516a0394506030246031400c56240b01081181016071415603003610410084031001e50080090500d80710784030701ea0784282c101640c81050758452440c1d17030511071507440003e040040c00904d007051213190300d40340d82100302290300200c80c0019400080c0314010721695210750151103071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 517336187 1250 517334937 517334947
    0x70503030a2f0c0102070603150501211a031005060609040e0a12030b0108150a06050c010e071e06140306150702030105070e010915020c13180f0204050a0b0303 70
    0x105942c1c00c1e040e92941d0020701c0020400941e201c002982e03607030303000c04160301a141070000381000a00344440ea420210600d4500403003590074106c000c0c07444060390401c0c00c04264100441c60040c40c0740348405080e040c4e4604100c1c03102c0d13201003980d50091103070000740c04031f07172491440d841c0e42070030b40c0d00c00c41d0704540000c030a01112000c1d10b019040310211651800556441c40314649075031281000b00000c140100340c4500798020996031110f400d0341e00a100034521050780030043c00048258903a403040a00704100820301c810344d40c0c0203601003c1e2078480c0e44202c45146503078015034005000080e030050080310002d94005107407801004020303648002d180c0a2484c503aa841e0401807551220400c40c18142c0d024440c0780016202407148038002c282680700c410030640b00c80b000411b480e046401411400007113900da448003580000d4441c8540a04482c1c41c0c2441408024900040130801c10011949007100418030611158600c05140d0740d0007075900f8800390340e6403102e41054680701c030a03640d05070b842000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 517337437 1250 517336187 517336207
    0x608211803060106050306031504110d1112011b090807180917090909011a090c0d1b0f020a031e111038060705012c010e07050303 57
    0x1004000c1042038215090140c04001c02d1400000340c1100000c14000820b002162800300007001d2001c0c42142400e10919196072035401c200b00703d5010301e001d038a407015002c0030805c8800160720f0403e00540b08505000e03082d001c46010344007030002d003080345560380702840281c1d102e4242c42c07080d80c0c0c01c1c000401202e4901b2150305d07200220124070111966403a0148030000c1c0a124001040d03a4506141d03980359510780007002a01c0d24050000351060b85840c1d00003020b01d0059411201c5074104480f041c101d652455010a00f511500e440c0c994402e203080313075080c0c1003190002c06449103081ea80e1000040e440401040c2d80c1c82501e0b0700c016001c5070302420403400714a01200d000081400901c0c16020303010803c04031501c3d002c0140001034105456014204021400c0701d414050203000b502d0100e900c01c105102590884180e0212600a400c0000c140d824400250051400202c0302e03a4050b00c08109000d40150509250404851325400c1410041303200e000010f41d0340543d00d00401035403800325941 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 517338687 1250 517337437 517337503
    0xe040b0f01081f080102040609090b1027050612180d0801030828020106090f05040807030c020616030801030b010605070b06040c0903020301020d06062304060e0d0506130302010608 79
    0xb03601c000d40010f10085248002030014000400c1035480e2810014100440e0300309032500c18041c81c0c010304203503d2400e07419520031860940542078003900644640384401e80080d80e9210b400a9420180008040b045806082c1e8046d2240c400381d8440841992840b072219140c0b01c01c01c010100080203100140003240c0690001c10501b002c2200002218042440350b8075400441a0701402507551060100310110035405800f600100c0003104020b285040e40e58103565000c1d69a007c1c0401690340300850464903002d044a038503440c10022003109030498540106803010900003100c058440340b0000503014001d4007a9464950302c104500160b0307503030f40706210080c0410000c4000300a00d40e80000050b840070f10051014000002c00818050704050300500501088500c903042c1520480f181c03081c135240f80b8246c5007500c0031450140c004149020010316254000031015106024102c28001b61b6603c41180c3d00c1e00300e1190300248640350391040c110f43c0701c49251103092281c0b40210740440280e641a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 517339937 1250 517338687 517338721
    0x1b0b090f060f0402013e0c0105070c150327050d0f0e0409171c05010f0506030106141b010b1002340306021902010b0d08090d0f050105070e040b0f0108 66
    0x14080008040700b0100300c1b1030601c4070f51003000a040358100030740c0900ea0028001c080b1410802c0c240240b61000383d80e0340c080828042e100f0808210b9000181c0440c191082e00400034000c40b284100400c44414035000640c4840d0081c111490b120f14128450020702a80c0c11030352807106034940000941043c006e01014100312311007200c44800020b88881a0350841c0041c14000390030a495074181d1001e400300d2821500c068000b0800554590401c001c1a65900100ca041d5005441e00d00311450003c003082d02180240c0c005031103155004d4503c00429001507010014030b100445074685540c0c0039040c01c0c5d031642c121010b03900543d0610030402d004000c100d4050f55280c414014440c3e2084e50b00d46606040b81c114200e0082a080e01c100d000d0207481d824040d541030b20b00700311540344085c40e1555034800503101e00b03210390303008113000c040e0071050020380c012110f41c19800030001d10035443d002074000c0007401c2a0311002c4c0304519044c6101240c0c14040c01e20f10700c604068503100b5150311100100b045640c02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 517341187 1250 517339937 517339967
    0xc010e061e0a0e060a060e15060301180b030a082703070501030c0e09010609050108090706200a051c0306080106030f030305040f050d091503050f161b0b090f060f040201 74
    0x268241580c06003410803041e4480d5400c40c50000381b150500001400542c006800c400d190001030000108581e00c010840b0b04527441d100d00c41000c040c00e08541406001d41d0403d66600d4002c07003505c1c0051000010042c411040041000c040c5030061620740d4218400c1c402c10385400d41c0c4205004d0085501070342c0304510703004440c00c00b40c074902598000034205001c241c011100113109071000304515600040c400340c002c0842005054080e080980080800c03401004159030300c110340041d044141020300c180c852981d040401d4a00298000c042c1031a000e01d40361101002a00e02100000c43c0e02c1d041c4282030649900081c20550100c040e20100c02038580030740180c0d1061a400c1c007020005504000d042c41ca0103060b00c540c19224604141034a9950014181c1c40030b0606242c02c008400314000354407030344009a176241c0a006001c8020866148180c04801e0b114502c4d82c200721014041e000080f90302ca58a0101210500c600058400d40c403000251408103901542d800400c00540c0580103a13034000ca8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 517342437 1250 517341187 517341191
    0x228030605130c0908120d0519090506090c1206061e0a0e06011b03022509060603060f080304050303030a05040f060915062c100503120c010e061e0a 65
    0x245400005403615408802801c12507901d03e03062141903009450340000f4520310b0060070202d0501c1840e0603c9109043c0e90403038a9685d00001341c22042c00748030b801008240b40104100920092904599030b41e005c1e030720700f8010300c242e58144020340345c0080c00c84200740180d0058202a2142403c2c000d480002c00200d003048185160360030b100e41c84141d42c4070010031078110240a18240701001610107400000540700c9801a0f01d500b2021a4000a45401e80000601909130100070510959400c1196401002d001c2d03080c02800200903602d40c0140e000d440302007404c40c0038156521417080d6203214912501d9050b4106000103000307411658403242d4018010320f440c000c05043d95440404032694104102c5480c0b90403030303210880e5843c91003810b02402c0b031019800510060124202c121403040501c80045900000010384100800740c0c030f2000400740070302241c07162541445144155089591141e9007586031456030a00c5030400920280030741c41e18804000d196243c240c5058400400601305283c040e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 517343687 1250 517342437 517342439
    0x1503030319020c0c04090c030b0709030b0106110c060301171615051606060b1c05090304090b0102010b04230c03010b07020d06022a01180515060a0312051b0102280306 73
    0x9240c40c000c1b000c1d42440340200400c414150314000e0f0728860301803d004100312601c5400d200058070507500d503064401904010400070030300003c4904d018202c02e469608080d022000107961180310744051039614910041d101d142d4466101030205440611904800305130901ca107150190042006040f200ea214451a12445850b110001541c02c541d000c0d0001403000200e02c00501d040b0320a108141c40425400e005509080340107650340d0013540155402241c1e0b4841002050b8001d600404420340003800c00c0c4070680c56400e0b804074003c8450031f8440915a201c0c009030310007440700200c80c140d45c1e070403c00d181089a01e800f44408040f18040c1201c0c2d0310307400c104505408902c8004440d4070462028101d080102e0301480c01e003500c0441810b00d901d006000300400001c1c001140c1c601c0c4002c001c41011260b59151000200700140d10750015209210796840808003543c00b00003400c2c19828012083c04113000c0b40681402c0744a043e202c1b2404008a19a0052401750a19502c450b8513103031034045034036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 517344937 1250 517343687 517343689
    0x50402030604230a030509010e0f010815060c1606030e241e1f08010b03070e040c0e01090207031b030c060e01110c0304090e030a05180102100906051503030319020c0c 73
    0x80070f13a03810b501249010520542541e8003042a02904500340d46c40c2010f101e1210010744800806031448402c45034186182c2e4242c5c455800359005580f02600722009442d602c668601554518001c3d480000d00301003440002060000d40004c2014501500740e240700003a4030002502d24010b030042c0c10240782812044210781144800c82d0180f450a507c00340d480198002d0400e43c06056440503010340d0600c0c04c11011582c1c042103074012600324980c001905c0d13446141250395024550002c4c040b00c8a004000705601450f980500041c902ca07072101000b01004445c00403115540c1c0d0002000a8031b0006daa9002450503007045110b112250300100d009460000c08031711942081c80302440a5001003007c2041c4c0202d402900086402640550b02d0311800318001025480381c0b06081c03d155156044001e0564400c210660100600f2a410845050703039190070005000306441384003a00c09034191502540c50003208032030040400ca10044c002c0088803014078080d42110515036858060040c1111613 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 517346187 1250 517344937 517344943
    0x70806030a150b0109090c0923220e0102030c0405041a1c06060902030105060a050a050f072a0e15030f0f0a0309060206010302060702090603190b01150305040203060423 74
    0xc02c0746803040c00f04618846100041c8440f145501c1321680034141208000c0c4603421882070070640314a900c608280408590f48400100e90074644503400035400f0480840c8440c28420700021090f0b071460500c60744150441040c00d0b03000070786440801e25004c000421661030954041030610704030200004203a0310390b200161030300741c0070b0280e003501d09030803802c910420209103d08400b0b0003c0c440b045003154104400300e9600d028000e1040148440007440e82805402074040d106c0780c00c030300d1a8242e61420240b5201c240c01700c444200c45200705401e641c2d0050110340f0789001d400d8030400441a000e503a01e420000d40e09184592107150103004108160112039014044186120729460080c802800305140003844110160b21000454100c040184010781d2010225290103404440d030144544429002904281030a001d9692031054510700c0d6040200980030030381240c00031780e20328003c1c03032804200303a06440044078000d6040d00410b0015001801211407140701d60740b51130488800d5044101100c1c0307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 517347437 1250 517346187 517346213
    0x50402071b0f06180f03030c0f050601121709010f0509180a0213061d060f0d05070e0111160b03040524010f05010504180c030e03180301061d070806030a 67
    0x305030095403500348041a00642d100d000b00d05004000c40000e403401140400c68584c9010003000c000b9049035000500c0604500000012b421406890465968941c03811003450b005004903031008604d5005400048620280c994681c0180c560700300c2e04050200440e010f502c01030085901c800c6810600c1981203c3c0780e6400c0c0314041e4107400503601c90314030622045100c10b40d0321540c00c01200001d55032004801c400d038006440c0b01602c000d911209006d5103140280200c02c50141220314040c20031003440d5004000c1c00c1104801c0e00c0d01440110414000e40c1c8500124601390108050f111702002400300c003000441d0f20601032002d5540f81c003241071101c0ca0326456114441412844240140820742e01e400b5440d000300424241a40780502d0140c50104801e02c1e0f0040050855454000f415028069008400c1c200441001e4036910b0100380f01c40c0b82d05109044150703010b580b81280100c0c0384030007003200d00c482443d03a1481107810303900c03488100c80042c030040030280c145c0a6420750000040e85220804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 517348687 1250 517347437 517347449
    0x411070f020a091509020a200307152d0b101206150c063603020f01060303020a0f0611070c08010e2a0102030708030708010509090d050301050402071b 66
    0x140000500d00401c00c114050f03820034240c0b14078213440c4643c66141c01c41100d0803a45030382e0000d41c65000c20310065620701e840840110080f07684d4100020010303000300082c01628415139140664120303a40503a01115842581c0034101902e00d0403040410443c1c2c91004100402c0d2000880c5204810000c141000d12420110000c2500c406c43e118042c0c03854001d101c060104891074005008040000422110072800003400c8607541d070411000f079400380c000803500c4082c1144404c0917416034040309088150180410340045c0101c50f24400d0403181801003008507030b016801040e000700191541260181c0c181f2040301d0150b50b4402c010500308928003e07040c0c050040d001000c41c0f43c94128800d0a451250240440903040583d0980d181001c1c03180c645d84540e00810007a0701d00c209500140c4c0f035803150480142c035102d000300800c448282c0c05990035040c0d90041c0d81c5441c0700c3e140c02590b076982d810b96107044008150207200510660400b03a002d400321902804026495040d10358196a00c000e10760055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 517349937 1250 517348687 517348703
    0x20a0c23071a04090c08060a08030c0a0206090d0b090d020d02010504020f061c05010b09010906030c2a0b0405060901060501080c07080d022502010f0512040f02030309030d1107050a030818041107 85
    0x2c000c624040d80d0140007027010300051407522403440034291b00c410010354000e11400c1d021402c030390243c5501e1405040d036540204c0307402507420308000c40b40d81c80050b038501100500c104c1c015141c0e07040c4180260f85c0100d83c05809144405a4a420002c954100000380c0721b05900ea41e280c401c034201c541c01411700911032141c0b85540c8030400e000040410200d50009800c0c141008110742603d07a2103c40824814501507808101e11802c1900c10b8441c4101703003020380302c100f8913428070003449004610507001c0d0009070000c0104565a40065694000c12035100380483c03824423003600400e209000a00803501405001403410b01003504042c864500740c0461091a140811802d0844d6042814420404600d0074100d00345841c3c410200c0340507000600c0206004031400e01481152800c1040c0ca28892005050f200c1c003440d00d880c02031244c07614005a0f40c062007011b20000d60f82c03c1403002e120582e81c004a00c03510700921001c04004000f001c2030b000f6081551845400d916004100203410300c00d11803500c2c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 517351187 1250 517349937 517349941
    0x20d080715020306130e011b270602030307050304051501080a030e0405060f1309061b0806041803030b12120a110706020a0314040504020a0c23071a04090c08 69
    0x84400d03000010700180103040e00c10000c1c0300f60769442071000d80400814017404074203814650074560140c25080326121903110f0f03ca101c0580e164101b00c0d0081414400e110340f44020741d8000444240046d148102c00141e00f0030408076400034803400055a01c24010030885540f01500c060f03801841d00c003640f0a9605400c40d01e0400304040c0d016080e03011801c0105e800340302c81c0c204400010f525480e40c001c4a841034144104800442e03100c3d0304107110040d0090410841d60f984d011450729118110b002010001b00d204001605524241c403c002c811035224407560128480d45d9401d5006109c4005281c2e840103001c00e50407034070309080000b00900031150100b10b8403210032f00d130050110b11407618540c0641c4c002e6001030265681c001198079405805188c03c0054810716039035642140300d150003568105000203641220183c002046402c0c4074801c480d072902111242d50200401404850480c215800c520740030055070800c00e4000c2c07140c100340584c0a25291740c039130b5048200e0381c145240e140802d4400c82 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 517352437 1250 517351187 517351193
    0x110a14120a02180315070c03030b040c0309050d0201060e0c03070314100504060503072405070c0303022a0d0303050702100f05060f03071505070602120405070f080f061303020a020d0807 81
    0x340310f102c480e405800421a02c04e18800345020b10100500400c10031240005070b00925101e6040403040c80d0001d08100840d0f1b1000c0e4004015019425090384c031032140010405103940b05104c1c000446081c0d4406820351b1f103401031030034001d9001600070b000301030701c0e100015402c00d0b0100b8007034090780c481c04002c0605450901400b0555445611131440307500102020000c1c0c8609240c0c0801a2844202200c0d80f03240700c04003135600b8021114040c10a0070100e05c04410941c0000340b4820712011592090010340f040e611440206881903442038112a8a200c1200007a01940080717400031801e0050754041d69261364142c0460b010000e035442d41684500c1800760a050000082e01e20080035009002c0e01c03410b0800c0c0c039800710131301c000340c600b0064005015001e00c106581038408000c2200103d0b641810705d0304103a030755404039005018090880d4140000d0001307000450440041ea4030000d40f050350384000600014402c51007040d03040d03004d03c07041d040050f80c45c040f803c40a0b5100e001055120701b540c0c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 517353687 1250 517352437 517352467
    0xa03110a0e0a0f141002120c10050a0b061902011d01020904060603020f1e120c031005030c0a050613031e0b060a050d1211010e0c010e04110a14120a02 66
    0x1074040c50603c0030200042c403011035400f5140700b032a0003d45208907111100c0c4400c030b241c01d00d02c1d131603030500020104810410f114045104802c0785001d0703009202903102c1072101d500b03c64070f01e001103510500030040c01c1046120341d101c001c42240b46000002d502c00c403d2100b814220207200704e0a105941c006002580c6190500c2100041c1409181c21030501142c101e40c8281c610402e017500480c15502c1c2c0601282000c11811200c401300024094201c5003021a5840d010f81c000b070721507444a11413014049064200014605442c3c000181600ea40a1802050001302d5000c900c601c10b0040c001c100c080082004111502c44200a610308052181080d0404c2038402e003015081500c90155040b00304a19591520b43c179140680100e02030f0300c03103d116841500c010400a10136020b9500303091b140d1940180100d803c640e038000a8031145024000901008121a80c40705080a190340030f01c5108121441500240c106042417820741e4030b449810141c20b840341074200e84000f10030745c0000d2444c90801e200c4c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 517354937 1250 517353687 517353689
    0xe030a02101b080609090a0818090f040213111303110a090212010306110903010609061802040806010e0c0d020408010b01030b06090d0213150b0a02061e010b0a03110a0e0a 75
    0x1440b004000329001d80c1c401011418050b02840c41800010082100c3c00020f02000070707103540c040704003130f40d80c400240348042d910080c441c0184602d000310005510b1682265a003807003550b004110482c3c814440702584001c1610182d0998040030601c101410024600031601c00740d8096010085d07500c0440f030812810702c110b81c1000c11504c0c010312031002c024a0414456041d298003d5012403c110002052080ca000326040d26a147d82000c030000b034140040c0d40200c0907070740c42c031010210400c0c0c504120300681c4102e100726000341c1e00c0700004000895400c10165040110340340035074540300e03600038042c003030b40c100340c00002c0700b0f96481000d45101c5d03806210301240c1078026242c0c42d00701000540000c1c6002031503680039004042c5258804082c0909a205856000222000d002d80c1c0d40c035000d03c08102e802000c2000c3c00b500c1510301040005508403906d01400d10b0045030b0065580c02e001c45000303160000d0b81070400f49a110b40c2c01009412609000d04101e16059465582040041d41041107416007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 517356187 1250 517354937 517354961
    0x160206030c071e03121109040f33030f020105040308030f0105030714100e0402090613030b0c03060d120504180507030c050313060506030c18040309051509130e030a0210 74
    0xf081c0e403070010390041070500380c0b40d0303160a000951410395503a14140b4030a201546600504d40050303210400c540b0ba20019a884140c0c01800c2c4811942081d1f41094649810084d061039114000300006000c420300c40350180c0c8103142036400c3c141c0c0c80e80d0340b4101d5001900c00700c1c03000818000621150900f0409030b0001d100900c90345800c0d540040100c1c404410414131401081510000c3c0c040e10b0700c6980456100d0030016180c5980c550150320003002c0442070f0300044071500003107030100b84020301e9002560b016041c014130010400c03a103035407841c1c0ea40406c08000800d01034240710005500c1e0650300d94084582618030045070703616040c0b40c000c3c1110156508081440414014000d45420110040102a07808007000805448043c00a807408020590740c541c0640e207419543c41d000c102d0300c0b1a40c003491003038a441503046d48810821250540130301400095a00030b010420380c1e803030842601e1121a010041c0000c4111141074030340c1c00c65020030282000742e4000d10000308401500e21800c1541c8071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 517357437 1250 517356187 517356233
    0x905061311190906050a030e0c15130b0304020603062407030801062007170106120f03080a050103080702090a020903070b0306130626120a17070206130602160206030c07 74
    0x8100300c00070f00170780120743c140810995100c911840e07142040243d40c070300c0039005041c0d42c01110007441100c46a805000f03400d4049803100f40009440c101007042c2c1e4000e07a4020155421582c1d41024440c90b110701488403c0741800c485001c10780341a0b910010304e41d181c041d56620364250b050000103801c1d1003992582000ca2010030a5030f00d940311020030b1100984070b0400d0400080c5040d4500e450151030650052a1105c4059440804002400e44100d1031107100e901e864296980d424000021103d0034400a00790366070800540005180001616900c100e0402c401414880440080380c13a1005940180341c02080004c00c3c4181c5180058030110303000c0805800f480b401e4201102443e29034600f07401600c010398502600074054605026240c1c2c1c2120039035009031528103124004019500c02d6070545010696200810942c52000c607001d0312440760110300d403c040c2c43e9552100000c1d40305184000394984403840c000016641d80004500821007601055120350650071b01e4a0710600210282c01008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 517358687 1250 517357437 517357439
    0x60806063001020f090102121903020f070b07030905011a011706150a02030a030605060f07032a0501050f090c0108190219020a03020105011e09050613111909 69
    0x552421903002541001d5a540c01080000c00746500780301ca151820405554004104016010200c0025000c03040d801d9007183c105100717219003100709100702000d40841c5158140c00700500d034006d030010501d03d12203c5015240030401e86400c03401c1d400582d16540080c1e2560342d8a406d2007000d01920200610040c5143e40d03802c400f00010b400c20410640f61001250b0003030000d0040d540d07552407002c004180c24035540d44d5000d070340c40c020340300c0d8040100303400807910b031110104650030080c051311815002e0006261408005840549410b070300c940000040e24880341e04840101042c280700304000303108400115090400b410310540e0040c0c01020007003507510841046200341e03403041d0b12540007114001c0100e046600c03414800080d01c07503d08000c0d04072035001d15010095074006110441e0354000d40c0200066625018020100d0300700302e064127041c040710394003800010759a03071003580c0144005148031a4a94000080c4050f0361000805210301d40e0040b6541c00c07001c8409014a00500071850504001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517359937 1250 517358687 517358689
    0x60a020c0a170d0c05030d050108070f0602060114041a03031603230301122105040312021c03020c161212030605060304151d010e301c06150306080606 66
    0x601000f50390b850811031301c203444000b0300506008035001d00c6c0700c284080c01150f0f1664030448ea100180d10810f00707440305202d0002080e43c0301141c0b0324185c0740861980d0301184031380001c0001a1071504015110900814503000c045c0c0d80c20402000004054030040b071202d2200c1c14051b00c0c294400a464034030301003000004080010820440b81569024440748003004070074104203801c08102c6010411b8403020449082a50b50810054411a481a184480090b080600483c0c031031051051104c00c02c0003108408800c03034004e80181c0883c454110032180c440c154a1030703880380c1429a0740001d2900700c209460381c050140c00c018030b440003035113400d040c4443c0c0e1420000c1456840010170280940e40400311810003004503411000040c5c0880740216544903520044d42e0080c0070010200e01c40e40701c3d00b00324400c8100c807244014080d040c65130a030f01d007802802c500d110175a0302001106010344030140e00111420003510421000e84090000003445078443d1001a04031605ca4105034072582c400d50800000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517361187 1250 517359937 517359943
    0x60a0b13050f190615180b0403060914150621010f0207053d1e0b1003060303021509070819021509060304020d080c1203090106120302060c03070905060a020c0a17 71
    0x1700d2592400711022000c1c011030b002051125000601201030018002052200c1c0ea0440110103005030101050286400c28481da40c04415a9641c07080350118005410f81c60030f400300404880b0140c0415240075011302550b42181c01c1300800001c4544d0110f130000c00d12404000301884e54007011000d044000e510704100810981d913000100044a11040d8081d0110441e0480da826052418050b80c0c0d000d82131620101401054020502641103400c00c01d41c1d0a22900031201100c0d0190003508148900c104840c010f01c1c401006e803070441c810603000040000c007c0000040102101452440c1c1c0301c2c00d4410800b105040121500c9050344c03c0c0004001d5541e0303601100d800c503030f0403100a0550300c428545901d59004642d20a01c1d6805120f0b4140400e070302d070000031881031000741c008000c01c6807a0510403800994440026005900600028524060000045800c02d1725410141031440d6554001742c81039002d54031075030040e003014003a14601d042145059001c0c040c2040c070b0001440d52000d01136a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517362437 1250 517361187 517361219
    0x618060c0312020f0d020703121103100902030c040e090304092a030b0f04050705250f03050307030b03120c1509030d0b18010f15050c060a0b13050f1906 67
    0x1903000c0d03002954040143e410000c4403d4581d101d4800d54480307c040c00c000d494031803014403090816042c445100c4800c02c60300c0c101c80c803904120070403c554500f080322400094000030040740564404000c04120b100707400c0394447c8100b0a0500841c1c2d10303424590850244e41c40f0700042107211070549418089442036143c00116285146800275502410b40005181000c109940541052401c001d010010f544080104141c1c03c0303060b400c10754400d038420824401da40d2098064402c42d0300540440000e03101d0320083d60401050b01d00401d2a03680440000d080c002e040041010000001418100c0a1000c2c441c082c1c81c203002c03080c04501031401d1700b40d03c1d40742c1c482c905100e206280c1d2110603901b1030751440719403807801c03400c450082600e684807408501d4007c010f01541c0301d01b0013240c0c0341003400ca00c01d00c2111901210040540b01741d460304080324001e403085541e00f6074801002c10304e900880545e0310606104044110002c0c00d1400d00d00c0803462010200040f06917003906100d03060001c509201c88100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517363687 1250 517362437 517362467
    0x2e0b0a060f0507200114040509271c080609100317120a36110a050301140103020906060708180a031415011403340618060c03 55
    0x16035048500600720b40a225030100140842c107484145a050b0380b84026181e00d004082e207401203140442844118280518802c083c0c1c41280c140c0054942200c1c0a26500303070460700c3e6070003807200038013000043c02c101c03002052400c5a503001c00d80183e8143d0001c409504024241c611050509151b404925458411700026100302d00e00b40c0080510148003007294a44c0401e00381c0d008040c28200c04040290810b02a4100d60718025110410140c80d840348406000a0400e51138940300166036800a0503110300362030a502840030413000559440a014507600048201c0c580e440795030551041040b00d2801411503030281d4800e01003e00007130303180d1003114025100c490241c68501c490b0000511849020313000106800c04602d01c3c000300a00024178020038040d4100c00000c180e80300c14215110b0290405000d900d81d2011402c04028a5940e114001d01c60055058143c100d4901e14a41000317089644a0800900844a61f20340b0300d11400b580c2c00074015603e00206400519140108621a1510701c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517364937 1250 517363687 517363697
    0x3080a090b0a2f0c071409180307060207032d05070201030e0109020a06080406051f050105090a1a040e090f060f0907090c1e090308040b0a112e0b0a06 66
    0x3400c500c100e028001c6007000b405004514029850400f080816000b0030842c1089118900004c43d8444a110052404880241001c1d040395100070340004052009003043c17005000400c18035020449600007848824000c1c8c0b11401c08101020200d050f60756629021081c10700000098a0f40a07031000c202d035002902440d000c0340200d6040304680c010220f00320029400340c4002000240d4079008202ea510450146c00d04019070355544045282001c074010700e01000c046000414411980250b0180c40c0c0524040c1c0044030340d6498440424600e0060b40b98168040070100c1d081103071541a4100a502c0130040015241202c00200941d6841c0300c06040a10f10012240c0090307000e0804100300c0004184130002800300c00400c10300a00300302d1003000050390b040c55071f25000003501d004a8040040b80d0707000d00c1c1c81d403401d803030445100c4447d005036800c00104465090700a000240420940324048442884099001c14004024004030b06a14414075014101402d00041c2e980b442c44500c04c890450603e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517366187 1250 517364937 517364951
    0x1060f05130b07060c080906061003021b16080c0616020402070227010303091202012010060311030c0a0f090b1210090506060411040b160b07080403080a090b0a 70
    0x1c14019220150841c00c00c22001107050020700045800c00012840c0c1d944600d46d20341c4070414030075100c9404659450300420082c52111030580710742d004003921000c81003002500001402d04278104903c04e0300a021541c400c1310248881c0da0240520001e00004854180c5480542c0f20b4942210125400c060b204a901042c03030010740d01c4000089013483c0440004082d0001d86603031016902400307000030b60001c2d400e0713503010070501c0c54008120302c0300d40c05850b40381145040d04101d270324410181040e4600350164405220b0410228040e4001851090300c071104c060310500300b45490140240c50301441100071140800c103d000d031954000a5420020010500f8110000810074028020580c440d203885440c00d00e2107054042c0c0c0c850340e2400e119009444042d240c240c00c00c020f031150a0a0055025800c00041050f6061140144000d0349048048803501c4100d0700c0303c00030785204884040c08909424208400c03da8000c1c2c10303e41c00130840302c08000000c120f0300c482007608801800e1011541d07403125 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517367437 1250 517366187 517366207
    0x3121603020403080d0219050c0c040903030b060a020f100c0c0f060b09090604020a0504020a091e08070f0806010f06080f040204060503030f0405040b0a080616030e070b0702120601060f05 82
    0x4542c081c54018601e81d54580c2c0c0390b0805070007544040c002003401745a8050b40c82409206000300d42e00d815040d4000c1200f51030fa03500b000000e1011000480c281a9035080240140e100d03074010700360f4000b079600035010b5144001203080c1409682d600130450301d840d011014012a4001003500c544030b4200700ca400d1040303042d1400100801011a9030340d4403e04100821151a10000e10b140c8100c2c4243d80c5086402d42c0c130028001239015100846000c12a4810b06000500b0301d851803500c05a03040c0300c04214640d403484694109045900300a94144d030038481481321840030008ad42c010076001107420760355882c1010090000d500500201484880d11011905642d80e41d0040d5024140003015640c3d202c0e15550140e2080c3e0080c860301c3d006600f49540d0610a24209101e03070120b40c0800c0250029540318150010495000981c003828181c0d60003651309a6541041240040c00c0409105651a1014010031031207400c041e02400c0786610100043c42090ba200801c07028044c0746040160b22044545 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517368687 1250 517367437 517367441
    0x100b0a031a04110904080912070b0313050102120f090d0e03030a030e0307051606090504140a0b060d0c020105042f060d0207060e250305120d0b032b0203121603 70
    0x1003da80c0000724a0900041c0701558000b481071200498082004000801d40d01d5100c0d0301c00d00c100401c050050001480108501078030f4500d8622820006103044da05000c180c041d0001940d410100a014104010808a080200b0059440e19003800701c403208000e80026580c1c0303d88411182019103880c0e070120250030030019241c4482c1d1040554034400051030b10001108160f105007000151010720005180c2001d00c10003500e85018800030304603980d02c40019003d0328400c085541c00510070420008000b59611402101e5010744d40045054201810410090744a8052103444640108884000310035110017041c0401400d0700c0d45ca80f60209400035100034020600c014040030b0815511900c521000b0480c030002c4180c7c01c2a00c20300c80410003071506803007042e000040c4594030042d4a12501326a65000c7e2000c0740780e0180c007091b40207035036003c01c0c01c221290705000ca919004c94070744c6904401d0300c00a07500d404407901c011410035810b0300c420000f000c2d018040c417079410600c1c4c840340c2a0700c4c425 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517369937 1250 517368687 517368713
    0xf14040b1809010e07051215040804030b041406010e0c03180c031b040507051c05060a1a0d052a03271e0703020a0603050907080d02100b0a031a04 64
    0x107100300c0c001e58503015612078041c2010100741d06460041010128492a04400c0c014180c80508001e000c40810300c0042441c2840c040c00a844030042400700100150500c1d051720301c5240701d0307807110070280090072000f440c1a0040c2c101c03003801c820341410000c0568810081c1d0b503101a000c4040c408010b040c40e0686c4c1420000401d6a426005246c007800300075409081b2002c1c0e0302e400395010061645c0d6028215114000c00380300d4406180c1d1103c0805117240580c0000760000802002080d00741e64a040011030820034601420240d00d020403103920701049031081950141d0480169014601642800700311a042104c04100c0200d0100114050700341d0544074050701d00c0d010a100140311020740c00f0603036458582540641840020038070111810003c243c807004c403a0f0240c00e440d526820b020060340070300780c0145210311a100703003540000d840c8410131001c0c001412680140480b2600e010f0820190340e445840e10380121682441080000c215020040300c000900a102c103481d10380c3c0c070700b40045a0341 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517371187 1250 517369937 517369969
    0xd1b05090c0702181e10082e050603030f0c01110714070f06020616120f0507090803040807060c0c1518080606131d01090c0f0f14040b 59
    0x440c0030808110414002440514002c440b00241d949400e2103c0054910807242d5850040705014801802e80a1004454102d0709100100081c1901c440b0b1480c43c00b00c0c2c14543c070f15512520140c134003e110070140b400b181d9810303960082c0003900e040000319989204241c0f60191440780010425400d24081d40142d000d548c00400c1310b903071400b450400040b98001d040d5940180e0240c110002082444500654201ea011b9000380c526070751410000d10f46800229a01000e0210140c4000017002e29071145c01200148d004000507142000803004059113115003000803940d0003000280080600041e0310710071110145402503e4000d180703481c035000c10701030b40600c20b090103088180d02d04582181720801c030003104480718200c1d00c0d5101e860340d50303ca4013918450340180841c43c8850035a03007240c10440ca54400c403840804800580d0300800c1c2154000c1000b81d4968100841c24803110708002c00100041000030b200940c880d0600ca1880607404d0700080c0300b403140d0b980e1607103240151582080c155031420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517372437 1250 517371187 517371199
    0xf1203040f030c1502160501210c09090b01090302090f0619240504060c03111c0e1206010501050d1e0501090b24070314040504091406150d1b05 63
    0x165a10342000d0303c4000b07004128440601050407080c4038400102d0300c0107107440e80f9200e003a0340e00e42001561000552000b90f50f2140f410340b0711201807000f41c01000410442d5680344000d040c074001100040321a071045490403c41140801c0008da42e03002e8a03039800100780702d40c488194441400240e089000040320800743c604150001454500040095842c80c810315504e111132484000111100d126600a01780840d02c0e03420304101283c0f26005100300a10008100c3c1c48004054110495280140c0c00c81d000090b02c4000c00c29650812051303000710607421f40000d00055040c82c3c0082c1040c01032507480c0046580c1c136044641e02190035105403007a0020004d040225584603000f040c0642141c1c04017074000d00c0e9100406202e0200d155145401185104245003044861740c0c04a425411695100d42c40d40b1040c04046015034a5105261802d8400d0205e516030f42030a050603810a2401002e41040790140440140701d901c480760001c0e0044d17403003241034044101c0310146030394010143e00301d00d410078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517373687 1250 517372437 517372439
    0x302030f0706080c040b0406231603110304060f08090304030f03080406051f0510030207200108010906060c02130f11090a0803030105130e150c1c0b0f1203040f 70
    0x1003408a044019100e041d40d84000540c1c030501544500d100364469141900b4081004000c010721660440202240003248000b40b85d40c81c880c000d8142d0420708031010480c0781425034501f05038004154010a0742400043d6090920301030f0040e03d9041f5035410b00040c0515400040c0c07008900b4070464001e1a80040741241d02250303420b00502d04401143c003140e00d82d2428021030303085d16241700102141d07001e100d1814055400c4c8400c0c425802e1154000c541415000d102e0342001030700c20302d000e41001c102e4155403401000c41c40c000509140045c5d000220b120300e0030308188805540110718801c1e064041d80c0608040020803100401818890341424605190188013000c0001d40c0005003070f00b80045451902c183d4460f207080c0c0c1c90707110a01c911a40040b80d01e110207200c1e0801c0d080310b034014264070141d03906102c1034800003a00c00411907900d03079241c500054048058660300850000c2d0b0f5002134081044184030b030040382e482a29100d625118050350071800388005010002c0b100502800d020002c041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517374937 1250 517373687 517373713
    0x601020708030309070905073e03030f06011701030308270d020708010c170f0a0603080a1205010e0702100e030d0603050123070c0609050106051c060c050c25030203 72
    0x64074150280c6d400c03003030804001c240300364030030b6003198411030000046020701703000b00e091070f10030504e10542c041d00c46118071030b200302001c0188051441460400c1c00c80c01c69140c83d6000400445881a00c07882d207246c20030040c00071aa00c20551540001d003450901c8000b0000c0300310400060010f001c1c2c100510a8440030500b00790301103100801c90310080000e01c0410381e460416625005c90305030030346810b0401c40008922042411940d50010000741002461030f48075181e085255000200a60100e121407181140540c0359105031801040c6801d281c05840c103284400a480c2e00e203140302100d04a8540300401c04942082c8211841e10641050400c2810b0f0349160240c081c04030709114040c00f030702c0b1645911b07801002843d00c1d0700c200c0d195038130b000c0400c0407aa900002000002029a590340d0b8800c07002c5155210b09d5120100e8200009501000d10017600d0a01e05035860100d0150412805101803050003000050103041a010075041c481003161180481c0103501035a800654144220400303441c074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517376187 1250 517374937 517374943
    0x20d0203090a0c0e1e25020a0c0506160b272103070c080f090d060b1009030b0604020d0e0601171506010c0201080c12010b0306130b0f0103050601020708030309 70
    0x182d600c6100030303c0e601c2d940c698840000702801c541d00035000284035454220401500f0405500030745030340d40d03160115007000c80b81050800c0071100c42c0169022200d40c00078406c603c10103400800c4100c2c0c106190460006107450781c0200503030003c3c60b0480d0400030030182070b00c1f1208000c00038450120000030031104c0074256518040705810380b0304816000883c440040303d58080300e100b0400c41d180c0110990580d0b84022095110200070b0040c01c3c010300450001e03554015000700418010a00400c82c00c0c4400100700006444a072440c2c18000c1d02481080055040700596500c40f404460040c1c40701080180c1ca4054034084044130054000c90001141c40c11304242810107084070704c0112481c807202500380c46603048007500c00c02d011411031100d02006621808000c2e034041060400035061074411040c0c00740200003a081910811008403c0001a00300f011210070441000c403024000c169112000c20074482900480034109a10b450018282d070740200700c0d5600410828007100d5032840c010a806031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517377437 1250 517376187 517376203
    0x711010c140d0e0109050307150525060614090c03090c0a03062309030403260313050d0e0a090b010203190c030f0903022d18010302040b060403051f020d020309 70
    0x12600c20715940c210f9520a0548030242c4a024000306a203074204001c0144004012040c0130800400300301e0180240030841ca091600c40108840c02c0c403001d4a49040d41c00e4595681041a001c200404074407960b0f13030744540054200c910004135540d2501c900340070600386903425200a8111141c80b50020412102e40c0c002000565054865a101e40c404802044403880688a140c0e03150300c10f01051010411030340160000303024000c401041401c643d2492545030b01308075041c9070707001901800c00d0203101e070900490700e84441503d003610340c0c00c11980c00640c6102950141d2500c09603030700c600d5902c1d64000c0003240e4041911406207801003a09540090085424840881c00262104940161140103806910983c0e900421094035200550119055069a1013a1006480c42184980f01035260203040304803d0b801c4214845444d815401132105981c0001801c41c01a1010882040898030109481b40c44083c0c4c000324101d032a0b003d0803d02c019024880b0220000d51001082c04151140011501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517378687 1250 517377437 517377463
    0x405010e010c02150f0622021902060a06060504060207030809040f052502030702011209020d080301090911030706140a090b12010302040b030a020625050703050717030f0711010c14 79
    0x30303029905c12045800c2204103403001034100c4030b2118081104511501d440800428050006050810780142e175020800b548421801681050303040c400910014041c000c080c11560030018503043c07508000035552081c0c0d11003d01800783c0881c07280b402ea51950000031074509910014080c41c200f1414454829608501b002078840550744002401c2c0c1c0040140c601d040d40586504a00c1c6891500d0b6801805c81110100d03841990034046400045492020354060003014400185099951500c0451410202c03801c40c481c4d40101e00411500c1ea02030820760300c0c2c0c40c5407014a03454003681e64041c2e8100440350011a07410b03002080d80001000310001a5040701d000303c6091003156124800e06031690640da6001c1d4004034100310010307415444400306c0c02404c3c5440446c82100348103485480c00c20410350000c5841c1d0300194810400134071050700982006608001441c80c00060440a40881c480c40740c0040076450114014511a805460706c0c0a40d0381e000130032034464459946c10f01d901e0b852910408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517379937 1250 517378687 517378723
    0x1020f0c06061f020d080a0b030d03050910150504110c0f1f0212060f030a0501090b040614090d030b0f1305162c1507060506210c090405010e010c02 65
    0x1880003c0c2c841010703c0c9a540305401800c510380000c001210000310052661104030b4480c0030b000160b450030004030350025482c0d036001601d41001039000307007051990685804a0740c1085d44440303da030003040c800c1086171411034002884900c6d41041000c24080c44004090f24012508502a107400115014080c241801d040030914200c0c3e00da6101240103001244103003029400c0090782d5070408460b102c03218040281107490a202da03554130345c25a48860021924807800707005010070803003103009608501d108008040303564504040600d5807210001d401c201010b40340c54940b60b568441c052061001500945584112089810080090141510850154000d2401c2810400e116028a9050350104505004580e00b81d185440c3d240b03428660381940440d51402d01c4089540303010082c003a81e8030842c0007040d01e140c4181004500351030842e25106000c020603622490000218810322459000c0315001d00b03e031640e04285006000900440460358600710f05a01000e0300001c8060140220ba008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517381187 1250 517379937 517379959
    0x6050703051302040e0c040204060c140d05030433091106030c040501081906030f030306084b0f100b03032d0f04050909010603050c011101020f0c0606 66
    0x80301110000c6402820030071a080b0010018901600319030400c545800465031481c0c49900028200d901c03a5001002181411101c1000c000e60801981403203000c840c007038240003044800141440c813000704020b11000382d01005d01e403169499074820a900340511043c0072180d0b02d0180301c1004003980341c0192048501c5101d00d03002864801d08803849039401c0c402d05810a4a408015200000083c09514400c0d80700c3c401000b628805104e070000950061200c0300c4401c600341000340031145142c10180316508000d9803061054036145016050900c1d074099140414441c8106044810315403100002c0e80b004031504030b802190010707a20780b84a10b060180c540f0400c151903020106c40b07110001d03e0b003541040c4000e41c55100758041c01407000e1502d170041403008200340410462a0b0121521007500c0c0360220b414041c504046545c503600c02c00410080104500f0741c1ca400340d48a0310082c42c54108803150804104040307003034040d920340c000100c84060300c1d07004900c4010745840f011038030540184042e0744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517382437 1250 517381187 517381201
    0x906020318010e0c0d060b0d29040201080c0304030c020405040506180a33020c061504020705061605090d0b010302011103180d03111606120c050f090103150b03040605 73
    0x40fa04030300c0100d1400600b00e18205806001000c2c0302d0707010954290380d41c1c040705240c54032a0307520004490f1080d41c44009094555107144075880c052114605c001c583c00c410080181d130440c2d507154000078444d204540700e0f5503900c0c1c11150071095aa00940050401007880104030001406e540a8035941c001c003014040800e2040e80d1b02c45a551014202046054044064610311000240350910199800c00d10a00d11880b0310306076485004455910b910110070004030300304504031854404001c40d01540b9149d655107402d941c1d004050045c0c08061100442d580005000e6821500c5201001c0c0501038503400608280442c00400d10060380446d0700c101e0540510500402180c10a645580a0302d40c2c03180300c43d0070322002c0900c8030710403400d1100001c01c20b52030000c2042000a0001102450701d215420014001e280038025401c000b03a031418003409030101500131082d00d01d03101d03144042903226107003507004901031305d503100c1084178000010401060030722a000042d449640104c000780020b03140c003e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517383687 1250 517382437 517382441
    0x1b0c05010b03010c020307110a0512060f0f07021507030f0e070905010b03060d03030908090d1b050402180d020f09042009040b01050111070b1606060f0b0306060c10090602031801 78
    0xa400840140c001f0010000001e80ca01203207030314000003030100d103812034840000c01c41c10b17089042404001c1d0b00203c05c111028140c51440e60344040070328282010b03401e2000d000307542c03002c4140074003000c51814000213440e02d00c6030348100d0134481a20703020f20000f1304400300540c90350601e000741d2803503a0a007800840c0c3e074a4030404480c041d40c0050010400c02c48e017510214010b00c680b141c1140d0b604010001c4031306c4c2d5983d032190300c41603e01444038024221940b080c00c042060302c13039202900880c014884003e03911507280c8a00f000d5030007a216800c2861992000841c600d887d0005198001000310a000030310160020100d028000081c8406050000c401088842c000c11200200361140c18401441194403034101241d40c6024001291441d640364421248181c001d00e0740c0580e45c042101d002002d12504e401208010516052003248080c01c01100103801d00c00101124094100042c10306040d180c00c0004144400b055001084014030901d4000003070343c019a1140360034078240106801444040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517384937 1250 517383687 517383701
    0x9110a0b09011101180b1504050c1218030d0e0c060a090e0106031b2a03030c02070e0c0a0807020a060e07050a08010c08071b021207030204060b030f0c09041b0c05010b0301 75
    0x1005c1280e0048285d5031460f0390600c00410801d0046d185000c8049291103074090070f40559540b070100703a202c0d240d0002503003042400815400040e0740480d04080e845c1030110480300b13050120107000c01c8880d501c1224603d0054840a65a0004000100030241c0b96211600c0c4040d50748444641600d80d03a40d0f2411411b0780e410300d102115200c10760311601c0d103040c010040c0c4803406c140c1c90714114400d004042d40741d002c151504001e0340401c1e01d0701c07140c0003120703414002d0314060b102422a01903a42031401d102c50280c0140b1584005100200c00480d18042c020024080038a41c400424450080940c0409407130745000d1142501850401c140414029011700941241103925a1008410340e40c0c10750854036101c4510364030034141514017403030300943c403020740d01802200404000c2c030200e49144188070803a040ca6020240240c2c00384103000310b0181c00d40d412500310106000c0981c80d040e661000038028102c030800711010241448503407800303d0b005500890366600800c020003907001c3c10310605080c1d42207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517386187 1250 517384937 517384961
    0x121c0605030d3e0d09150827030d020c07090b010e0f04020f0a0917060f0403080a2306030706211104080105010305030309210301050409110a0b09011101 67
    0x4082001a24600310040b0080a82c4a40d01c6604900540100040010f4459074400b02c0d5070300020000640070350400718a070028405400115070140741c4c1800141229030117092007566130702240520600080d01c91000c481d078829070095a5440c504400110000e5110400d040d1440c040d280c40000c0507441407003140c81003001038450174280d00c40482000300215151122652040d4280003602d0760030400c0c3c02a082c004c1440e02c0b8400c2150a0600009421464407080c45180c1e210000300030105451a480c942c100707031300d4103040455881e505400c1003c2c020f090030202c04e45c9903113038805038005101420280503c3d415020740710b8250b2202022604074541c5100c02050f40c40a60350020079580b2588519259101101e55508054035204040e00f5100c00f03078429182c0d41c5c404000d01070b0041040c0240404d0701c005034650412201030a00740c90b030600051003094803841d80c640c10340061008554540900c20401410071301419110307801419140c0001c3ea4540c0010000110b03041000c40501c104400110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517387437 1250 517386187 517386197
    0xb2a0f030412020709150306110306060a0c150c2708070b09010c021003020421030c08030a0207050703140114010b030612030d0f0614010c23121c0605030d 68
    0xd030742d480d82c40030311402e0300c405001c51042807800200d20103644201c144a18031688850001c51a43c01d21805540c000148101d0a68040040c40071030f94628045441040c91400d050416495a040c007615a224156100c0e0302c0d5428160070b0082d0fa46e010090590300c21242d0048242c508180398999145405805025800d5101c410f003440041c90001c060320080302d0516000a03007070321a5000c189100c0c90139a46102182d0085418803041c02b07116404d000c0100341105d2108000229100101101001000603194600000100741e000c0344030340450b04165000000c954000e5660724101881c008541c4490401e03510b03126060103c5040711598504980c0c0102c4014155146c8100300105000680d00ca50028030042040e4410000c00d070140710540303520050300080c0a4540480d6000c4001784a24541c108a81c40a0000004031a104200d0651a1004501441e0f105205802e071800d036900000114030580499103100e0304102c0d8180791211840c4440611905945074240b5607a2401e9407000d1003c60 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517388687 1250 517387437 517387441
    0x606060f021506120c0406030804170318010810030b040c05150c0604021003090b0712060f0303081503102c011808070305130308090307050a0609090e07030b2a0f03 72
    0x200e0891800d5010f000c4c5181a2044815808000380c01c9902a80c000c603900100482c08124a00307640c40d00c800d8404100010b103240c0001001c4032441100f260390114180003091001c078201d03029a842e40d9005c1d50340901b0742802c500340740c00d040c86608030511410b417040920090b2401071000207402c0e964594507200040c0481c1c2c03030755420070071210304080c6040101a626a072920206e000300396180c1c0210700c01e80311584010780f40f002004c01c1d21802d800400744480c1c2c00b2410000203920110090303108c44c24a41415542401c0000a420810f4040150005a00705064000041130507034000c84405034120800d4502400c11405a0903100920203d22049031084002c07008240c01c44010301801d4802d1401d00c1c038003503200d01d0034038911002c1d0300252002075000c2020305039400d040100001401c4100c0320400ba06207040700050194210b0300a04103100e464410241c01c0b40c0c0d08101030400340d64850303d0070b01d0354906111400303900c0e5403040d20112070f1000300b001c290420040c402140d03208204600312615507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517389937 1250 517388687 517388689
    0x60609060f0705120a1e02030f0406050a090801050a140a0b090105060715060b0d051b0a030b040902030d0e09131205161a070f0e0d060b0d080301030606060f021506 72
    0x294010310400e03203880c0100e130a40556040c510006107040d2a4944030126003450035115080e400b160350003c802958800c100070b2800600407401e82d01240d031907140c0aa0360307000c0780d0f001315165525a80003c08560030941480342c51402a0411000380803040c00c6611103075100003602d410744a402034583e40005400005003c5070600000510702d4500030081c242c1802c0100040d04111100da9000c000e9440d808501101c04c09440e01901d50010409807146a082580c2481c1170740074443c6c0781040060603901c50b001b4140b515941c00140b4135030b4008050310320310b50603440c000d032a424900783d40c60703c41d079440710000304a822000000c11456810181040360a0300803102903415a1024501600c0c1c500044485070006020070102c44543d100c00c0c0b40840e8505052401a00401c110a501c0701444090842c2c0d081030749804906008280d003201022034044100800b21300484002500074080080000000c014000150010012160b580ea91605000d107255030490722003005c02007030f61241c5140d8001c01d0311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517391187 1250 517389937 517389967
    0xa0504020607021f1416080f07050307060516050918070924030606180302060d06080d0c020103060f030b04060c0e1207061e0804020f040f090c0e01080f0a030305090a060e06040b06060906 82
    0xd12123000d00140703000040d449103841d507000f00008803080e0351100100085071100d5050211a0849400e200341010300d841d00041f42003960802d254900402c0d600002d2009100d500c10b00020001d0440084064001440d0305049500c800f04420109090440000d03030981720b6000c1c41e18100c01610703130180c2d8605540c03c11045038801c0315807500e03007901e49a010614540070b11a144009130039848503203804145200140654034aa4440b40714180518400c201041c0001c14540e40103601140001c1d80400d5268180c421080403450203402c8000c002042d652284000f486a080d03420507229502e01c10030417082071204500c0c00000c14000750034880420300509058403083c00c0c0358401000803030762040d00b80d480022908100c03c156039009500004010480b03e58922a02424050000d070661f00c00f1880815a20000300700006c0405036180009200c03010180034020210782c0c0000d080c00300401000c401d0307035221810f55058400e14420004148246002400c442c140e00018040505141032030ba40e4a003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517392437 1250 517391187 517391197
    0x5150601020f0715051902030703031d15040501020d0e1006091a100201140c120112050a1e1a090105060d050d110717060403080c120a0504020607021f141608 69
    0x117008091160b41a8480c49852503024180389500540c0c40d8022400c000381500e440400800c503440d804912000801d0000c102021941702c2802003100945451034010300a00ca0540c1a5090a2034607003020b600c2c0c000450550345812910300240241034903850380d141254401180d01c41c01c0c00d41e42420700340600704807e0900c54110039000016070005010017044041d0412200d9003620400021120780c40700b10400002d000d01070020f060301941c803055450a41d40e04000c9009400551007922402c114140416880ca0540d070214510601c6030101c0d80707090181105850b08c141c0d950800001a1403810300710042d852840e008070042c650001e40350800c0c1c0700b503541011081080d008141000c21105c800e804450707000441c02d4010310861409041c001c00100d00505102000380c8200000c0050001564640741c102594610020380f584892001850510946130003e401240d5150342e4102e40701284201c0e813061200740c0f6500903038058200054501d105207510152104100805d03000450040c10241c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517393687 1250 517392437 517392479
    0x10509151f080618010209061b03070602211501021509210a090e01060905041a0d0b01030c060e03030d050a020c0a060e1902030c0108070e060705150601020f07 70
    0x2803000d00c2441e4060480403058010452035406401400140070000d0188510f025410b0000c5050003601d500041d82031080c0d48a0a580031841c1c0d400801d400e070b092080f56910b69004404558a0311080d225000094204184583d1045800c0004408051240c1400900d80050b8040c04010f440420040d81c81523000d8a8102c62748620050042214002011808059060100161201d5a44000030200482c0313804c14403a21030784000400415401c900000c0070344204982c046401c40c41034250000c188064489035030301c0300100f5040d809011440b803145044c1c074040c03148410038603283c1c0c40c10340c0d2411090b280941c00d54400c01c0400050031700c940c4000d4110b811203001515000321040002d01e040351345c10040d911643d0300d44200036813100810205010b10030700a070381c030303d22003141e0000f036116603140c07892505004540300042c0c0301602c1840380404440c6c00908080d120010390501795540c420781000040400c80c0031020540e03540c00001c060381d201e0340c85401090080d040c8590804507104800d400303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517394937 1250 517393687 517393711
    0x6040f0e010e071806050102030708160b400f060603020a030308090c03060103020a060e032109040501050303161e05030a0f030f09030e0607020f100302190201050915 73
    0x810404500b03019100045844500400690341406555a040d4401c603d02c140b1251821604106a076008015101c4a681000e481515071401240b06403021150030002400c90307107204d0812400200000300180000d80302c20024076201c140e000c1c8540a156844105125000c3e070700c0c60340d00002c0b0010170b110000b901c02c1c4000300e80c0c1552940030074035000e03403504110040b4200204000c074901c02040524800d52040f0004c0c0107551440d00800c0080ea80d074003581c1c0410019103a0119151410001042d52129403610040d003120616911055501f102182c3c500c25410300c000040c040c41c000056030142582c42080c1c00076104950f86030065410201080c50104044039181008036009201620000314070361074035241c02d00341c450000d04a5500d540d080200e1454030b920350000c20b0380104840318100059507403a648003400d0000034007172400f01c0840c030703403107500c001541002a9158000e0304214010f1642c009505062440681c2aa032048402521b15400b8200343c079045e6808800d0160003618003200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517396187 1250 517394937 517394951
    0x806060c120f19300b120312100e0a0c0302090d05010204050109060801030809061606090f0218040f0816050703060911090103150b0d05010e070602060615041a0c030309010f150e06040f 81
    0x4180034150b0040c0312001e1f0781000c1141c0c0b042e0210110f13400d0f40008000300400300141008845062070102401c0720070899030f24160096403c1c040e5040b2090035030024000c030358942880c5403940c041d6200703014150015001c0704002840c180121000d03070607254131500c01801c150050060100035000600032005802c895404031011810620131410300500a08460414030428014401c42c0760b1171110042110302c00c9000c00003c10100c041d000f80d007540c0580d440c0c2e07989900d170700d05545e803014201c00501030740120a400010010541c2c4402801c0c0d01c40c640c00201264600c0030050524801d10000d80315429090b210b08111040f03912020f8444801086028801c4140c0c56243c01c5604140c404650383c2d010100c28403220f07030104180c070b40c40715044954050346041580c00d00c020380994071034a42c04196080c8074509540303240098500c14105032048a403249080140e260282881c0140796100d0380c901200400d80000b251560070a0f6062424484550b45130103007848010100180c1c150b203a2580d5504c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517397437 1250 517396187 517396189
    0x1c020604090603110a1428240201050103030f1416050c03210406030b030a0503071a10050d02100c021009050915010806060c120f19300b 60
    0xa0009000350400c001081070440ca0b04d0741e105050b0740301c0588681500d050070000a60004112a1080e209485051040103460340e400c28410421000c4015142e60300c80204c0c2000086040981c1c0300303250341c14007c0350031010305c09a00b00d420a010240006008100b040c040d23070f001d11585090581c1c030380e04a500e440300059011402111505046406802030280d09010346000c11164000c80780c40100d0160202d410211403160780b08612030441415107601d80c0002540e4140410300210b50010180e9582d8103081c0b070303c051280b4510030b007401d002c07a030107000c0380c2d4000c101a400402c0e2040a402c004107005290200101411000c0c00300b010041c1c2d12a004005888104c6015100c4071140c5408a881d41800100300d01d0000040c802140b0800c920099091681d0144000d904000b06852580d50382c42100021400c3c8000c0d004800302c1c281c000502c8500d0f06850304020106250300c034600c810280144001240c1c1e2841c0c0303007031384506000740740001201d0704040b4413081c3d00341000413000103035816488 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517398687 1250 517397437 517397449
    0xc090405070b160302150c090409060603050a030314100e04060506121507030f0e0a0f021206160905060a0e040f1d0307020f030a050a0f11031507030f020909061c02 72
    0x1001d41191400f4030096410180c04110900728000300b81150191441c041d0b0a14003e80512a59148959145c000710810f204d2030f580041d020319003140039900409420b0070054041c2c00c045900980c503426400c0010b02110744034001c0f07400d4460646001c00340e601d4945030701029060240c0481d50202400001c00d80701300f0200444654240f26041003071080c41c2010f006070444003083d100c044541c0c201000b4500304a00800c008114a600002c0d100080691b8008555014542e8030000c50f10300c00c1c10b040c0500c80c404100340c3c81400c2c0182d99540a1183c0300c40c1804064052100038a000c03502c00c101680a502e41303900b00195005202074000f56102142040c288020030240402c5404e4000003840301c00e60400c5414080c0750141030f8020706040b9001e94503d5036520105401a02e401e410041321030800031651100e00d8090402000c0b91507030111020b0b0000c0c3c2c10025603400011a00d80803809002107154002d88500480c018000100c5544401c24011502d101c81518416591001c02d03040c01640d0320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517399937 1250 517398687 517398697
    0x6010e070e0f3d02071413060b0408010b1e030a021e0d0b06030d090b0d09031e0f031514010c0501020408070b0414010914010e21032205030c090405070b 67
    0x110f20848a0300070b00148903004000742242e0811900090020b02c038103800b00703807620300b07891003a81c405039a5080c14504000031f00e00c0e500141e410030fa00040c002100c1d0b0301500202c1000e2000c9600c0959154076408824424400036a5140c050b048214400d01600d00000c40281d41c90b034030218025106e24150002d8400040103008a40c40c900e54001d100003414200540b0120f00d41e80c3c200140b40509105002403d401406494001ca98450101104261145128401441c03a100100d2203000310014060110101d416054000038901040c030301581120f1039a404c121050304225900c5180c013070004490402d202201610159003c01002403a030b04c08201c040d00070000702c45000d440d1801c0001440f55241888070840c10045c04000500808a40e0070a03111010001d003403c0060f94136040214540c011001d20f190110311160500c111500c2c0084010403801210b10404d403812940380d402240c03c145070340181a0076900c64000c055507802c1c4400d007550446d009104807080c40b50b4602c6ca42109a00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517401187 1250 517399937 517399999
    0xa05131b11010b0303030106091e05040903030506030c0a140d1a09071a0c0d0305190908030a061d01030210090f0605090111011b050a0c0206030f0906010e070e0f 71
    0x50900740d001d1504080c0b04110444108070051444c552403d600101881002e000c1c201400c5403c3c1034440380d03c9082c549020052201174018006d100d494280a4018001118280d00034051156503000c5403034441140000e642d03840707415030903a4840e101407000500d41c5c207104460a030b08018a840c607681c3c1d40e1011520480e00c039802028941d0400c0c000c10800200500201c11164081c0000130880101182d142051207a07440c002925a40d072400c0d8005141c9a43c0092640318584203049003440440001140b0440d04103c040c0500c55440e0b0101d10513143c03000d81d4003005200b15005000515003840404150459071800b00a13142e100c01e5043c6c6801c010741e10000c0800ca0000380301c0b005581004011103040074607402048210900382e42d074040d64682038146403c102c0c0010728417098902903014020015005402503071603181100d1100211241612080414841c850001803008018410188141015547d01c4420340c05c5078140501070700e202c2d50f80c9910007451202807400d840000142004900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517402437 1250 517401187 517401197
    0x1101021006090f0c02061e0c09130509070f08060f040305090a080a050c040c0f0c0302030c0f1f09030212030c0904111c110a080915011d07020c0a05131b 67
    0x191009603081301c11200218042d50003080401c019003c2c0705020f05031101114420420310754415003084d03003509c03035504402d501c9600c000180750340711150350203503100741180d41c04c03501c04607102d854203000c1d00c00c5845240507036800680002e1160343d14130742064006100b810403c1c00c0416882c002500f03403000d904400e05030f43c404140401880700c10440d00b004080280c0b0f0800039001c01c81c10051688403202e0122043c84030030441c0d10200741c401c0040f2a5042044d500b40e46807071600d05505511141220101c485480e40861800701c90359941c49854441c50741900240b441d403941c5820a14540c20040c40780ca280c100a0110300d000f611103001ea12480314001e09081d9480d0342d108401403282c48803103288840180341c508001c60034500c5c8021202d1208850a0400b515a5070445040c5808203400c070802c8050301003000002c0c0e80c420b03034203543c01860341c0e8500c9020720755851000300d035076010307a148955112405a100308158240682c400c2c2039a81900f801123000f410381503c03030105001c070100400c0014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517403687 1250 517402437 517402451
    0x10906020a0c0c050406230f041a0315010f060c05070503010207060f051b2b0e07030210020c01050912240624090f01021e0d0f020307030c110102100609 67
    0x10102c40f010744090f180460b81040251704100e4810202038002000780000300e05001144003640da009694413003214020410310000540c03510291468625155450092050300d9020b50000500d941c218181e903455401c040c1da0307500d0890200c5068501100a0300c42e8022001c011034207071400e0005122260140a011030303000119807806048450082c030100c1c0882201800c00c014149210031220680700d4005101c401030720742080c4030000d0429840b905420351034204101032161001ca0307100102c80c001c84d524520203801c1d0205a071101c210102d950300003801003281a05600e046001400c00301d5600049900d10074114042110303030b881594401306920041000c010b03040c90581c42e41400041d20030400000c1124252001513a40111010b142c8108800ca444205507482040041d0441c1d131411007155121104215540d12501004020360014101c101701e40844c500010854404940c580d4a0001e007102607100c3c0e40f8410000b100d024110b01400710071442d451010702030ba40280c90b62800010340c80c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517404937 1250 517403687 517403693
    0x9031d01020a050c01030209040213080a0b1324020c010c0c210903020402220e0f060a1215021c020c19020904080309120304050114060a08030714010906020a0c 70
    0x40418850141150300011080307000410101e40000c0c02c040a00300581c039500401c2c0003602034040d06161403132101c01c1c1000000c1100c3c001511407002e5000d00305541c41c0352980280c10404500d00c2c10041c0c50b2411030155401c4403a05141d00c600c00708150640103042042e0040d806094504045038180001c6640c4d0883d428800c440610025000e4000e00002c00120610405050702c0e100d4400644107982c0401d05150f9143e46d1030301c00864080782e01e4074010881c0c0b1411151380030142611134210542d00600061420b04065003400262415804040003640c00b643e90180d00a00822030050615000d1009880000090340c442502e03034004000941c03251041c51300d9503d04184100d05002c0c1200910f00d01000d44c64201080b070304140c000024030b81c0c0c0e6071668a014a000c042c68603004807000c0000400c428020103500070159440e415000c2d4000c0c1e181d03c010000e900a250140f0900703034004109003c00600040c08221060015600104400005856201c226040708041e500460700700c2030741e0020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517406187 1250 517404937 517404977
    0x3070b04060c0905240c0309060310030c08010515040c2a0203010e1902010c03031b0c05060702070602100c0e0d0501060e01060f1403060d0b0408180d021806130903 72
    0x1508080c0c1342c1c0210148072a451740d50300080c1d4614226181e00000380030154180a0080304c01465001d40f0403a520304005030a07510001700f5200a44a082240001003043c00060040b117009100c0900c00c12280c0300780c0b00803c4020074103010740320140049000602d800c2c0b0760b115042180706000807942c00d5a14014014942901c64108188016801422100403051008140ba40c440b1f50280307820480c141007444c0035802040400314115494240d00883d0105c523034000a07070f050310f600c40c0003581c038a521210f1050360303240d526006d000056003280e50400b4180ca81540138201d400c03218941201d07400400404546000f0700360304190b0f031507511404240422108040650b0040ca4945402010a030052000400e01e819460103c60508400000306006039105e01c21f10845c207400c900d0185160610740341c101e0140d070052000004400e4440c80e46001468a0700b0b100c1c01d05074002d03200e640320301594030061400d010010038503a400100011010740842d2648a5684000e219448090300c40b000c04070140307a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517407437 1250 517406187 517406189
    0x2030409180507030308151f0804082203060c050304020306040206090402120901050907080f070b070c0506030a0c1407080d02030a09050f1605060903150703060812030a1505100507030203070b04060c09 88
    0x2024110004205504018230001c0080859092034151400c0d02d451410000310b114a0f520188185001c2c4a001c40301c00c0e18200344002c07a031060000f0801003c90079400ea43d1400120340195143d00031800107809030a000000b004000c400034001407030400d200d41d0084029909407249502e07030303554108110002c0d10420520010b800200014640d40e84110310440c1d903800035010301e6090a00c00f10701042040500f000010203028001d11158a0f4a0003418100041c201070060b10000754011184070f107242d50400440d01d100d0303040b00c3d02c540f804207045c00300d1000c0d5001502d220890750740c40d8003003404601e0912903c0002c00c803c80242a00e0001014801907850940d04298481c590401c201151982c000508076010840303d100c1d28050b54411100750010000e40c0d02c01040786c01040800b0060302544030055204101018080200139024000900811a58010345402000c2001c40d40c52050064000d014014444c1c4100c901d4903220781d55145a0b0007081d50110740d12600d458450b00c00980043e0703208 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517408687 1250 517407437 517407439
    0xc1315060c1a0105031e190305220f0501050f0702061c050903030609040210020a170406090906140d0f06060b040e07020d05090d02190303090e10060203040918050703030815 76
    0x442d5410a40041e40b10340c140020201e503940907a022003c140382c18010a9032411030001e400c200302c0ba150074041c14603449a40301106158a1401035510075a510307412074144c450100c2c8001c6c3c11418600103680c1c551055101c042203420501c8040b0050350350724002d083c0641680072a6008507100041c070800d541c000340c216103094106108009003134a4003001d041c0d0003a01210342d520304a00d40390707043e401c116200c0c0d0003615681d8610b00402c0220300031401001150b03000c2c0d50340c00281d80d440174400304a031403600400071704150500045505240503d0100c042c14050496200b0030718103991500122040c503805000d850001003020003c02584042c00340e030150310790000e0a50384100c440b008003648682c4140f10302c203000b5003c142055456500000411251449080ba00951030f0704000e40380c210684200d440001c0500b001981d00380f12810542e0403540c280c0c0095052034202a814405002a200107100c21500d0b10b52080110341e0410a500066020b0740303480310b1604060071600010a10a003050b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517409937 1250 517408687 517408733
    0x509010207142202090915120a08070210090902041d070c0c09051003021c02210601181b0e0a09060506030103060c020319020f100e0c1315060c 63
    0x8840d840e200005003014504a5000c0c0c51040200c03c8100240034000c40b0580000d404020013281c81d035250303400010000116144111054010440c0c0e0b65040a04801040f55800740450f00c014200014000403158540c02c00020722905c64440204903041030788504c400004070b141d5441ca44c2d003030f2a603d40d041600340c60410882e20a81e111117414007118403c41301c480d955140000c1e80c0c00c01d02c012030030186500401020016030900c1d48120742001459099100300800c96410384140510100da0314010091000382c11145e1074503c9120001156511000d400d944581b480380480203c1c6098507071468213130311500b05100c001c50a010744100300727400c007100403882c060090056580300380540741120340c410008590300015090032811401051410200822140c041d0402160003143d08190810300740c01300d40801030820740e602c060320b04400e511030b2580c101010303207102400d0951221043c8404d524000c030b05010075030010100341c0c0c045c0d40030b500054201c0d8245000c000d561380d00c400c031401d00090b030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517411187 1250 517409937 517409969
    0x10303090f0b092416050d0807020d1206030816060c0e150903030409050c0a0f0314040b06030a0c061d12150709050405040b0702190308270d0509010207 67
    0x40c0b8501e88140e0f040350340700f116244150544603000300c540d80c002e50340c0f0100440c0c84100e0507802840444241d00200c0d06800340c10520307401148100c0e280c0b4850103590380184243e110310a815154401c05580c4800003d03152070011000c285500d00071300c0c103241640c184460204442c00d0a6048500c483c00c1001001401502d0314400c1d07803456032075040b00684240e1207646100840001c0d10314451580000c03142410030040000018140015100d80e08041e02c5007a4600c025003402c030110703080c454004540005c02c80100d000300d030b070700e0200517442a409004c88001c243e0980b1218650940c0368851800156032140b5a00340311b061020941d51142c0586008405844d603d002540300e030307816440056081a10000144d01c540b1550b110780060034003a00c2040682030a04000c101a00f0484222015118108070340542e01400408600c0301a01503407404090b0319116521a4000200b0b0143c01e44440d004490003000901030020080d68410303070311030544c0d802c111800a82040341c05d07802090300b0b07118820 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517412437 1250 517411187 517411199
    0xe07030b0a0b031209060c030c100c0206071b0b1e0a06090c170c1c020c0a1a0f18010209120105011401140f090607060f0501031103070302010c06050a09020d0b010303090f 75
    0xb44c0380304010403a661ba0b120001358000314514092800b040c0014421800a86064400c65005448a4034140e09464680ea5040d105585240780300e00c40c4a5210170131101c52000c00c844420843c1c0014140c018180400c2c500c03d0041d05007002a6441084581c0d14841040200d40c1e80c421000c002d000e604000e600c05c0c1c0e4986500406407402480c891090500140507401c1001000a600c02c6149544c1e003151180180d162a5583d242650070468855290788a65003c2d15005d00d03070180706040043d800200b40d034594105014281014066000320340d028414405035581300c40071405800904c0000150643c9010341c00b00340c0c01c00e80c0034000d040c01100d02c00c062094009008035922240c40c02120340da43c0c2c015201142c101d2080010240800380b504282041c2d4a4842e001541280d0041c407040755441c003448101511800e16200c000e011802401d43e403000207003550082039010558090004c0c0a0940390082421049154070490740040d2800040c8200741d00a160b031030150810608030105642006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517413687 1250 517412437 517412473
    0x120c03030f131d07031404050c0d05030412060504020f060702100c03170f071103043f08070519020a05062d0901030f0e070e04060e07030b0a0b03 64
    0xc0320041445000600184140d03548050032006083d50500c0c5200c0c1403aa045030003c4060036141c2d40006410030304161614600d0142482c0103681040203080440510310070000c0100c0179400468050009000c002664044580500d106900514010800d40380620420a4210001410790b114803014880c030700250704c0304012806940041d003003040e800c1c0d590381820b40b0064848141341c20841241020041c08140c10200a1301942154483c000d2031191a15400c1d224000c90060f420f4080c032200d000c0d505039001480c11901c1ea40100344006101010311075505400400580036156518000381c3c0c6000c0140400c4000c12804a140300210001c0343c40c0e000a07505d5106100d090711940021414102c100340001e11380000040305107a1780348102039124252819041034030045d01003841d241d504880d10880f809021080320b40c0c10007401001e420403181204c0800c01378001e4406542c0c40c2c0011410a074100701c0f80002d1402800b014003e0300c0d00e0702507001501d0707415101c0d500941100445108030403c031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517414937 1250 517413687 517413697
    0xf210307091205010605100f02010b0d0305030a02090a1d1e0408030402040b040231050108090705010c14011e0e01020a02060708090a20040615020304090b0609030a0b06120c0303 78
    0xc40b041d200c070109802c249024158603048264131413010009410b0640c0c0150b07a03410701c40d82c40d40003400300850550810040301c8407104080e0200d0790410024a0b0f640e0198001c02407900c0003000c140c10b40d03850b231408000444d83c81c5e403400c01202464061000010795400290a010105142c2000d50b2416a40300002c0f40000340000340141c1e11120300070050741c0c4a0b01a00c4140072001c24081700340e4102c4e40900705040a144c903101c001021600086095440f415130a803282c07421100402d661132610004494202c00303403c06840002c0000d4101e011001d0a006901012014001e0001c016500100340011a0192040d80c6480c0e841040020515a000f0400342c2c0d2154050138088126540c00c00c8890a10034103400080030036a901058424601a40e010400c07503010545080250644489418900310034a0108501503801800200009805508500076650000d841141803080200200e8900742b203154044030200d401500700411401d00004400d24001205c00401c2c1c11071001300402e8981c031132 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517416187 1250 517414937 517414949
    0x406021e03041401270636020906010e0d0209100b0301090204050a0f080a12050408030a091a031e0613050f180d090b03041403040608040c050109031707050705030f21030709 76
    0x1203112a05a40004039038a40605442002c960300f5520800100c410780e01c6400d1f0220b01c9111440f0214080354401c404086030038030081d110442e13071300c056004c03c105080011b080c0030a4940044001c1400d0007480301940c001e2901e09800368032182420100f00f010300030b6400c0004801078400040001c8540001d14444440c0c1149942c140d00c101d9002c12540c0e44640d4108080c00c0c40001242341450b0783c8901d510040307403560304401c0702c0c0001c03058810788140f0041e01c0d0416444c1813446600144800c0140700c0b40c00c10380041c8410076002050240c141a82d03401c881d080301d03000184080110700001070b40c03964000480704000c0c00c503907448403001410a2240d8003c40382542404000581040903040c9074a04d0103001000b225120f039900c1400070329151080700c04130790004083c074001403076501814400c03042e6980082c15a480d0300c81988680ca10b0b400440083d134840c03103001e8002580e620700380100030a102021018201000c2c0420204103003600c0c4001026806a007003040103c41035004032300324165a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517417437 1250 517416187 517416191
    0x30709060f0c1e0c080a11040603080301260114060f0301090b070c02030703060204091e110702010c210f0f02030301080a021005070501180c09050f0406021e030414012706 75
    0x458005a942410300f00c00c0040840601e0003021940b18030000d07803524001c0c81200c8003048003045009000a5400e240b02c0148480c1c1c007400180411850400e10b40b44213511000d40410b0940070001c40e6003503d11802032102e0034000a410b2180605040c04844001c800a80003070021068550302c0c1c000c0da140c01802c64040007200b0400008565003804190021500304405540751034407100550003c0100102c220300010319002c0c4008204001d029032082c40f0401030038242418a580c00654038901d03021003c82d10800084d0031820b0340301c3c64841d444044141c0340d499a4440c0081d52020740b8142caa4150074056500600c0104204800000e840b0115541a0f0340800b245c1c0c903911040c0c0303060041090041481d4203040c11590b4950080710076415260041d400c01c0001a070381c002d040200c1d4001e4508900415a40c40082c0c04a03075150000c02c007408240c6090a05461682224100703500240e0f012a8545041090b00c41004403d00801000400b1002260007038040700070100c074400511240200499 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517418687 1250 517417437 517417463
    0x9091218030605040803090606011701090228020c010323011505070b0c190e1806150f030a06150203030a110d050a0219030209010504140a0b0c03030709060f0c 70
    0x2515a44903a0021507104600b800a401c1916003001c3c42d4008a42401c0c0f24030420300000d01c1503100d20441c140020310b040b001c0c012a424a030240f0301070340c454001e104200014605c28900c0500c410001c0c10480ba066000d8000581c4550006090700c0c4207030b12001903011950200d030144202003e000341150424244100120255034090b60302e8041c1040213803244c0d100c1010002e00081d002c0050149418844081d01d0443c60b048090300d2814540c00243d07001070359900a0700c078035003810021300c0c2c010000500383c60300c070346151000c066242d0004050440c51500842031081c900a0b50003504090718100750321619034400170000075680d000007003441010b561074220008001c00c0703c908647d0100215a0248000c2c98118001c101030f40c070031714120102103d030307205052445d48a4400d5a1340210142e41d0189418584200310020700ca04070f0102c0d5000368500c00008030b6405120041007821001c41c01786450340b07000b8101030401c400310b50006007484850142c00b00f0482d800b05950520701e0740304106000750 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517419937 1250 517418687 517418717
    0x601060305060f09041707200301050124140406020c0f03010506032806151d070e0d0203030910030501080d0504080a0f2402041e051302070f0f060203040b01090912 72
    0x80440c46d1000e805928001400070288520256070101403400545108a80740c404802d2600303c5609228104c60b103001e01ea00552039070021404500c0c600702601d0000b120641300700020a0b80d6116a20a001682c0311440785016403e0200300e00b200700d40101d0013049036142001c007203515417660a08103030b00f0364075040c013001c1da850b80d03140e2060119030031003010010300180071981617040d1000e0050f40450001084601700c0307100107000d40303071150000e56141802800d140d030900080da0307403c1c127007203a150006002e101003948401034201c2802580303a40c08121945003546150401c4c0c0801015403c00c0410041441044d10018078008001e52220004c4154040c0d424440345821041c14000b0b0360040c015094200c01c64a50080d00a6a00031680300c0048058000144c00350b200900c505074002140460080d0045001c1d03020b085000c1c010840000101aa940e41c00070041e15000102c50591780071090205000c05000d8a41c050000071100b04a5811181c035045600d5111004078420041e041440540d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517421187 1250 517419937 517419953
    0x3030415120f02070201030b09060114091503150a0f030c1211060c150105030a030206180309120106060315050f120c10030603110604030b01060e03070518090601060305060f0904 78
    0x880700800c50104460408050841c01a500600090740002d0070702070a0070943c42e02d003240324020310301619480710003040401d030000f181e000252800e1740039421400c00c88018003110b00030b600c600a14042c000b840b601940070030031030300c85d1504101e08601100c030090000a00c0c8244500036180c2e901140c1500c2c200d1880d10441d01c855030280550880f2000c02c038003a03c0207000580c440450307003000e00000241e0701e90042c15079400903558040c005a0010011888020340d01c1a82e48401c0064411b6070319010900c001f01d00c600842d901a40b403180c0d52800304008180c0c1c10302c076072114003042d4040c040e03542d45400001103240c081309040c1c038403a03130140304200d89580040041200c0340401800c0d200300c01e411044040c3c000c01461109a50007441c180e100c01680ca0030104031030550380d210000c200c95900b07040040382c0c200c00040e0615018441c2a030049502c1d40c81502031481d50b403042040400528120503110304020040c0e010f402414202400d002042d03440005440903002d0580382481e040d1348070b05200034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517422437 1250 517421187 517421207
    0x40f0e090705220b04051501211e050903030118230c0706051003080a12150e01060221180103020f1206030d0f020604030f050c01051009060b0903030415 67
    0x182c003403460300e50f111030160507003041c1d00e10b1880341d40208a1020070400340400d40b41d00b1181e04d045c590402016024560051950350804d6007804403e40d02600c0d03110b424402c0701c080e042004074031300c01c80c20104045886401016803041140000e9400e6500d0024242130300440c09180035215a218044042c05e00c502c18646009811300d01c05c1e01c1c006040c407041041c142d6020882c103991301c41c108800500342501c1c1d4403034241107030381c0300d01001c0c6400b0341100c04032040d065203d6031500740b07900d07000b822011554031103014001e010300c41d10040c8154544440a0300d4010070541a200e86141c0c003882107060018803013620f2050302c01c00740190030320407090012002842440502250400c0c04070b054035010a281002d58030911080d01225201e244a650030b440c441c01c0442010016848100010002442040091401000b0341003990424401058103400d4400840324143d50b03081c661002c216004481c01040000e20b85529061318200d19040825164403580c020a180c0d200d80e95201c480807841040303299 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517423687 1250 517422437 517422439
    0x2010302190509040b030601030f020103021312121e0807140906030405010e07060212090d060902031005040204110c1b01110313060e0a0806040323210a02040f0e090705 74
    0x40c81d14208800c0a401074111039100c5000e83e20b8403122041c14100000d085050301d4000710002c01030303117803079004401a45c41b800400c3e1704501644c00004a40304001040c1d9005842100e540000b0303250450010040221422036107040d00c20070a4012289422845142e04144030380380840c420314141410628900c07031804d24940000000013004280300b07041d4803d80e440030b800700c2640c26041c2d42d20b90032659884415482440d40c5404c01c112449440e03d00d1070b442c002d85c801c8101150107102030300002d05110011004c3c07401143c0704c008020852030300788607692015010150050030044041c515170b1b520400055209916042121aa001c5130b010f05098402d00a03c0740c00c503550b50000410000c42031000307218510101e480d81c099a201450100d0391001560040c2c002001d4654031034038111004500d907252100c48104d4109039560006464004001d1000342c0d00201e02c0301070380300c000d40c0001000145001c1d0814818402803021072032000b0024200d511108502c0616120145000c1c10002594000703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517424937 1250 517423687 517423717
    0x100f03050303061509010906110709020d090b010f180b040e030307120b06030402181302190305060604020f090d1b182904150905010617070c030f080402010302 70
    0x8108640080214400d14064400c0880c1c1d0108905455590140046040c0494460f00c001d020082c4510301c441582107415003200c0109a0b19105d24049034401881140d015449101405c20701c10b1910405005003000040045000d240c448001d000c1400380358421000b640300c62090300159140e070481c2440310740a00c180d03a41d904001901400d1003036100c1c81d802689003002e0794140249803c030241c80c4540d40180c0302000c5991031140c070b00d0300b0301401440080749599814410000d030319075403641d10120400c900f0340940750b81182891460300d4070050820740300314010410b8410f0325180b682a82d10301102075070842d21031429441c0805584580eaa81030149480000c00010404074a01c040031120040321010000c519540100e40e50302c0d040704401c00c0300b0010602c196117042c1401d034040c4809601e240020b924842d00d07520303403900b82c036000e0780204002014642c410240349c05644040b134011001e81000100c921090b41c2c09080c170511603c041e01448481400141964002d07011214546250303c45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517426187 1250 517424937 517424939
    0x2060a11070b011d091203010b0714010606120e070f120201020304080f010b0f0306040309030b100b131a04080c010e15031e0723030604140903071b0b12100f 69
    0x5295120f05089031192000704584c4081040050041841c94a1035607940510345035a007054460042680560f00446012000d250181035010080c070821015241681e46c2c1154050140360b254192000e000d1701d80030941080301c0422903842e800c2034400884a404c3c00034131940c0c2c032a000507411070003507500180181c003a50090942e082c00641c00401031a20403a4201d40190340c032810305580b0031040700c000f0301088030320f601800440c0301070a07542ea2001c02440c03a0f910042e1140600788079a00201c400214040c008502070048104441d0442e0074801485501030a15140507902541da150860113039040c8034030011094000d4454645d8002c0e8040c0c11000700c2e50b2403c01284c4900944175002540c405540c1d9180807620301ea10401400b036618140c0c00d613401442001d20307180c1800784d05c0603285070b6010b070f5a058040030740030a1020381440342c3c5500010b1a09e40c1c0140c20b05444000c210282681803240840c0180300c141c020506a40d18800d112189403000e84d10499150554100c41e00702d6802e6501c0404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517427437 1250 517426187 517426199
    0xb0a080d120c030e0303040b10120312050106050304050d030f1d1c05030c04260a1511070c21051f0f0903170a020f0a032a02060a11070b01 61
    0x480035045041c000e0100140c04000408800b01c6032100754540d03c50300204003080203e140c440456800c03408042510051542d10400b00322018880c030030450108500310020400300b402c03446141e00600c51030610910b103203030503622140c441c1e01c000a160245965056003580da80020b0b40b1108a00c0740540e048070035100e108910580c0e409100501d030160014920746280b245100b5800d03240151041000c9030309041c00c00803034203440c2c02c2002c0c04c000203010070000c0d20700841042200c0145036002d208205c402014520700c1200350382840c6500360f6a5030081113001e00045a000491003120200070915584c03840c11554030307005221034280070382240300d82d400c40c00403020061451091440e801c01f0401103080c2110b00e54042d54079291008c2c0200704c4826a01d00081c000c0014180d02c01d000b031200601e010308100404070950000d0384101c001984d900c40003600d1030b000c00001c03c081414140c00410444000c100259180707001051040c4240d01c40811200080001c0203560740036510071902240c2e580c4900c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517428687 1250 517427437 517427447
    0x403050405040b0a050913060e030a171b0a050c1e010c02010b040e03030c07080f2a010e0616030902040504050a02010905060f1206010507051504020909030406120b0a080d 75
    0x80a40782c881c5180852100749841c101c0c5400085600151075813906945a10601402c3d0101d4441078070050380b44c100c682402401400100503010b255200c2c500341d4502c00395583c04a040c000d101c901c030f901f01305e4500b0251540c0300040c4d9072280c8140c0b406030b60300c0d01054185820a075144601c0e041c903441c6070b11600300301801034201d6100043c5503402000a40203100402003030341e03d103c56090030b0740c00400206203a551000c0c0100a03040c06003103024903104140d80714070201da04c000103101d001c5045840d00105000c41c0c0d01c0c1c44a5410380314000b440220701024829449840c042d08440440000741411404103001c1d03048402c04680041c41008103150034100181c503000315446c124001041304030003190518000c1d0584100d14014940340341000440c0c082c6036981a03000e0101030600c941804200300041d0b041008900000319001d002003a41810303c14000b10000c05482250950010300c0b0921007154046a000c410340a92440803400c00c125001003a25040e180e04810341500030700711710003070294100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517429937 1250 517428687 517428689
    0xb07090b124503090603040b010f1a090409020f030d09050a0603020f030708060a120f020f040c0f0c0807170a0914211501080a030806040504030807230304030504 71
    0x3182a01c2c0b85004500c1114400c84030002d09074002c2e000010b80c200314110310708a6800d400500000c03246044403c40029205030001c8070101c411080300001031102c2140f001075503005111402405083c1d1116420b620054000c010a681c0a04e035110340f030000b5903650750018015000c0107801e844000f4a0098000c00403070060050038001c13904020001b43c40381c843e00c225083c40707803443d0300d4130f042d510b42c4182200d0f4044080d0480f54403694411000c224a800c1107030350703c50603226000c83d8007008024030610045180d05100f140c404c51510345806c141e2034010b000040c0700100b51805003007040e0070707140106a40c02141009080e40040c40050181c641d90740000b000c1c0c641a6031106c003003956403841284082e80f414040309420120045190003a141000140c004e802c01c29800d9480028000c000803080d107400364005a441d5201c0c02d50f000c24150050f91160300003000355004d000502e03194034090540c000c0034060800300981003070884403d001000c0005e0180c145411119940d04160800818076041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517431187 1250 517429937 517429951
    0x3090513090c0b0403020d240f020703020115080316030c050a06050f0109090c060e060706050903090411040f030f0c230a0b120a0209120102040e01080c0306010605070b07090b12 78
    0x602d00042100b581060645080340c1d40240b034000903c1c0199511264002c0645400c1700241100b6600404504c40d40244401c0d002031400050316001e060030000c0c2528a5540e03840941141400b060040e404003104503a40d826440c650001c030f2101c2d500d01140c150790450320141c07041c01105614401c03c0b111f900b040d40500212402c40714143d0300c81102074101d41414400a0128001000400410340585001c01c0d0240c1d0081c00c0d142071080644808060310021141c00c045900300107944d400700d251511448001034034100119007407a003003401031000b4a6440c00007401c14031404011000300b104651b40c00d00038041062720741c941000ca1007082c01108010301c0c1c0d43c52145d051542c003c0307604030b04442a1044410404e468084544031450610020b500c8540701640101c510070a81140b18002d0005000070b01e00200b46034169032509035994102400038406510030b230000401000751607800070945288603005404688541c40e03c16090300c6401c0d45500000364140b000c00c81d8902d0707000140b001ca100f100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517432437 1250 517431187 517431203
    0x1113060308070b0610050301060315030b04050105090d03090c0b0f0c070807211e03180e27330c07050d0e01050f030a02090904140d03050f0c070309051309 68
    0x13561010401100031282c1d990300010014001005080e11a4210312110040b071103100030866200c4c0c5503c0841d00089078240d41c26074446042c01b1441c0f00c104200340c07000d075081c070f4100300c58031b0a6030b1840c16240e501d2180000203000800c11900105407007049480703040e070110480305031555900c00c43d03482d46510700c601011400c03051202c855071010800740a0b4101c1d4000c05c03602c801d1404079104480500c009009504210807452150000c040240e2540043e101d08030030a0490b240a0307034a001c00841c100c81c9524a40002c81d03230710169907000100122140040c02001c00e80c1c0b010300b01446254030700c416005030004107040a201110003101c0c008c00201d03010b1001e5441c01503201005503115641102c070280000c3d0200b12046640d11100e0140d504910500c2c005841d24084c24006000740c50140c03170542d21119158400038428004202401e841206802c0500803031030300c0114001040d4000b042d410a401001a8090400d44a001044003400d0003d040c046d030040c4030045034004008207002261001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517433687 1250 517432437 517432441
    0x11041112091225030315090b120304030302190809030102040e06010305060a050604150903051b010206010819170904111e03010e061c0c12030305010605070c031113060308070b 77
    0x100c41941100c1c07003143c0c1c003100c0140d0302008081003010a007545905804055449505841d15120140003000a080300040030030108400010450307407110041c10340350b642d8001c00c006c100081c1c01194043c40c103e0307040d4004c1e5021a00d0700b040f08251203007281c0036501d5480000c001c1000354a00c15483d0151400381e07010000d0391398a505101007100d1074040e060f442401408200901c04032600c221003800328900d406880c141d0742ea0340f42ea00d00508098007540310a2950101c840c10b5904001850061a041004000c41000131107212502c628585010340b841c41e0b00000110164400801c4428408001d4420030016108040c11070554100243ca41c41e00d150800250000000050a40e8161600014451004e85403202080284030b00e0140841c0ca92030720340c0300c81c00440c0150403140300908402d2484a9a06e41030300e001404c03110141c008400b40320083c000b00300400e80400d01102030b282d0240070501d9240480c00050034204d0102180003006041600100800030342070003a1225912030034094201b6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517434937 1250 517433687 517433713
    0x30f0a0f0201020a0225080609030a14161104060b0a020f1006050102070e090c030f0c010822060e01110703030218060901120903090b03070c0506010e131104111209 72
    0xf078820311800f000144d10040f0b541b50400581444400000c05001c040044907503240b49450600e0b41c2142c0d038200f20381000c91400e038059000340f50640403140304c000091510501c441d020320707100302140000e8034492420346400510303246c075808040a0004821026122080c92034002d640d96610891041c2500441d10309044189890042d08281c5170140c01418000c0d042804585503c0c000134035104132841004143e00080c1c40500412100100b4100940194542280050700c04040544103401c0c1c0a40c0d0303400d0f80710f141100b4402055295000c40c1c003051124018641a0240001c90f0b42410158400149a801c154140d8002c0c0b103440403603040100c0400c5684100300c498003501010901180c03200090944034096030f4041a6124460708020701000e07140c480045094108842c10404a041d6148017024402c0c00c03c0200d0061a2080c0441d255143c01815070340c1a0900c480300130500e6065119000e81c6503141d410070440070210000d4252035030350507954103455020a8a081489020fa900100d040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517436187 1250 517434937 517434941
    0x415020c060c0309010302090d0c0e0f090c06091905041509061e15020304030c1413060b0a11010e060f0403080c0c0c0d0609141014160f050408030f0a0f0201 69
    0x2c20711461003e18180b404000c010340203548814a5107910114100c4104005507000c040b807000b03884a041d0b5405540390590a50a003500041c2c04039080b5808004607029075520402240c0244d60251341510954010111400780d1031103640050380d000341042e01c01c89815601450090454078552400c0c0320f240c1d40c038a40311000701c141800b0b1110f141e801e40000d00c01059040300d03207101c410280c8100c3c2d19082e540d85480c1c44000c5650011b562040c2e06864458a034500040d01120012801c50100440c03441d00000e0401886000144424003c5202c000342e4804820740c05483c20460000a641c0c091602c00d0520581d904111030440104921401182c070a90907141950f401c46001001010011004010440b09900314101100c0068803403070020001100000b205100048280042501c940b200c066072065411804001d02d0ba40f41e4a42007000c001140440d500f150015810b21001009420740205c401c2c2c400c1d074000c4652888006a180440392261001b03004450041c0e07110324171008014000c0782 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517437437 1250 517436187 517436197
    0x14040c0503090a020603130b01090614061c110412060b030f1609020f0912010902030c0f06030103080304060209031b0a061e0807111501050f120a0b0a0207080415020c06 74
    0x6981c3c000d0b0300000050410340011b603001450182c50303490850a540e181075008201760071020049071250001c020103a40b0260450346001d040321030038108000c4549124034007404554007641d454a031041100041c1407081140c1c0504884a0b0450015840707080403005058040e0300d00703010384070385802c03107000303000c0441c2c0d10a480b141001c00c01c080d1032400060f80060341101c100005910303130400000c0101c0e43c43c6c180000b00c178a414030012826041d10b0042505141c83c9845480c010b0386c800c45905110382e12001141e0640340e001d003d040e101d4442c1d040c604020f000c7e08081c5071705881160b00f80c84a0100b058142c0c1c518450407200c0000700764540305c013224903000f150360000d0074021000c05502071030b00400c1c0240d07202c041894202614915003411a260403565405544500801401401141020052600440c10a8594001c015918018641d55002c2d400c00980958020008203c0052580c1c040f100c5040e00440e159440d02c0d100d000c401d05000b4024684409403240400e17141044c2010804d0340c4d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517438687 1250 517437437 517437451
    0x15051e0c0607121401031401050a0b0303090d050c0d080d050a02071203020a1707090602070909050316051f020913050415091e0303060f060509090c0a050c0714040c0503 74
    0x75603032104101920b0310420701c4405840d0980b81e403051301211028861141c02103000d607600c810241c0c3c01104060031650040c0c103401807a800c0c4829500076803000001c0300e500c4a420340e42d00d5102001403c1c140e041c4001c042c1c0b13055002e620402440300f40000d40b070280c00b584485035810009074541c0e504540880c0b040b0711000b4100050003002c4070340240264043c00248101c2c0c00c00c0d8628030340246000c40084011540100844d03001e100c18408140d04000303141c09420032680802c00d01c5440d46956503030740210329610508040030040d50b0104141030005081c1d8940c10f0034075220390440e03c80068041c3d004881c4580c0101d0200c0325445801205004250095402c01007079940103242070036000141c10325030016110401a80d48126488886461072590f4600a41e00041d070f0345c0c24450201404449940143c0401c03205020106207952600011500006000050750f82c41c0d40707100303055806000e0a0110101409100000166002540401d41c840e4104440c00c108250505209a030b45010540b0301c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517439937 1250 517438687 517438693
    0x1603030c02040f020909010308360603100806040f02090702160e06030a050a0c1401080403020d051305030109030909050c040b0306090a110c0a050c090702101515051e0c 74
    0x1500503060580c00f8081a4001c0345000d441c002910303022504103030080c0c0c02151a0300300001d50740c285551401d04004010101c200580031130714101070903454000c0008410740700d10400004981c3c0e41101942d0040108040c2c1d050310b4540c03600d81040f040c0241c22140980c000e03002500000c40c001c1c40444c440010300b036000c0c0e0b9415818109038103c86454001488503416100340310441c000b107401000140e626030322900d85212090b040c400b18451054500b88140e0502424006101c0081d4003c241262821064030700b19448a69401e40ca4480340e178540c2c0000d80551801100505050388140300c030065071a40380c0103004680350390318481c0d1580300750f01c12001d1080c0140080342071072502c00e0800e9040800c0d00c0011840d41d81852403919264404440c1441d141c0c042e038203000801c041840076881402c4200d581080713520b040e01d0040e480f0341d4050030110000d5504d51540018000c812160805403038000c0418000c0807880b40c02030240e6010b5803e07a944004105800700040d6a03d0302143e40f110040d9002d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517441187 1250 517439937 517439957
    0x706030c1b02010504050307030b06040b0105070b16020c210d3225060b010509010905010e12060127090807020d0c1e1d090d140c010c0801030302160303 67
    0x1000d951410001c0100e04100f000c000c0021aa5000c02580b00614000d02c0800d4050800408100441e146c0c59810344c113010f0705118110225604183d01580600b111108424203003070401c00b21b092070640705c00c0b00d602c8001035204111040c0b00113a8580b54000140444080501c004016200201c802428804844124020045081401001020700f10380000340f54105140821441074888550140182c4610310f0301d02d07042400750a000f206e40015013801d00614103200d02000922050182c0209418802c02e40c400100e19180c11b032b203d0020b6500c141c01d80d0241c1d43c440a042d15101501e69030303a404017031900380505014940380f00d90301c00750b03500c14010b0745080810390030300a070b800381c003441624124001b01303002400c10305103078445084000360ba038103948190611400405450440091100008001c0704020740300390b0001c0c0e541d1050044c0c2c200581003c108140b10341c0c1d03e10a441240000d9402c1034030080086401104860580c0e11a8095a40304e460344183c0890007100752001030002680703081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517442437 1250 517441187 517441217
    0x10902070c08030a180f06140a05120412020f1219020f0106030803071d0906060c031b010c090503030a0504090f020d05090a1509150b03030705060c0c0706030c 70
    0x20003801800e11aa8284000603a42c000749420b54011207048404581112602446111188489400390082103881445a4141500244118450030610400f0f580c00516100304038043c4007030710b10b1420408107040c0d0a19083c0750620000d0390b1004020058442e1030342540c5007040c04a8440514040104101c5c103000340038100601c0c8441c030f400150158041c030424141503501c00c0c01082e0146010b50740d090354904119200803c14450015208441c1c5103291701c0940a648000010b40c2181d81250721645642c0c0c8498050305521941030515000c000c204601c506001045d000105111145e40301c4450280c0d0703500a154492140081da180040c1080200784071034000c40e44804600006180d00500b041c96a5060034201e031002d940080150344990321100400c080340618140f034240d07100c400c0c0b00355003a99680ba809040115090410580c640954090340e403001c0040e141290f0b008811aa02800d08041c80041a40008011201030050740000300300d40d0300134007072000e1112207540e9042d03035094202 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517443687 1250 517442437 517442441
    0x14030403090302030a20041109092d01140d05030a110a0807061406150d0203130206070b1609050d030e0a0905070203091905030303060d05210901030c0e06030109 71
    0x10421030900c40754001c0070000d07071400c006030a4068851904207945040200c0d49100f0f07049050b1102e88950300340503011000322112400d81d510040c3c203486148582c3c58600f80703600c98400c0000b04c5009601700c0c0a0713080038a15600080340c122080c0582c803080302c0c03c0e030505000300a90ba2080241165008100c24600e03180f049001862490461007550303a42c00d41d0340c0e9045450ba212000c190349142c3c4035020340f10714441040d5141c3e040300d03046444c62507000682c6011440d074011803e01d041101d902000107120602c0c900d80308002141d008100956076101c600c0c007862841010744054401102c0c0006002d606030082206030107840c002040c030b217140d28203994101d4040b0060040b40340c110302c0d00540041c40c2b0300c6a0051500441c919006940ca8000b0042800030b04c1e80308001d6071505003002d88041041e0b0f14084112504440281c80c414080c4495003055440c21728280c6110600b00045001041e105580c003002d0030308450240c0c0c046c06040e80e0108121b48013a44e40403090ba01910400040107080307410b03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517444937 1250 517443687 517443691
    0x1003080a0201060b0a03060501110c090a02090402070c0306090309060e060313060e0114070f080c0d2003010f06090b090a06030c170c04061e0507020f0f1e030d09061403 74
    0x948000f149198890000d5409500400311100100e61a80d009201270740e00a10b6440403060628018155009008002040c400000e8000380c00d05034001010f003203507142d540480325140d030444405c2103041c0d80d03842d10400400000e0700c290000b030b560301004129544121a40001d1354801092241187c49444c0e5540d0042ea0914040300c0e426600d2a81741035644081c001c0d07640d48498400b41410310710381040040e10780081840d200c0f0030841d54100700401007010b101900c01d5000301a40004007811100034a00240c8540e034080c0200e00808000018110660040e180c141d0780f1030364a60b480303541d41b1301a20316203009000c49903603c44030410007444001e00c40c3e407000522030b140345006010040d200070b40a07160141565000101c02002a003440280d41050b02c0c1d2020014805d140c2c42c030043da0400044c1140240341c2300904c44d9030701294034661607840c2441c2944c81b080c0140b10f4407100d41c000e80c0600146400b248414000d0240c0012006003c0c0100181000c50f200c40e22a0152500c01e5600100d00d0b45c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517446043 1106 517444937 517444957
    0xf0a020f0301030b280204051e0f040f02090d0521070b0403051e1c0e19060e15010b12130201050409052701091109100308 54
    0x2400e001ca0781100e80003041112a500c030720543d4850400d081c5203192040440420311031803283c0b1580200308440701203c1d4812070014009170750130b14541e95a04150303c00710f250144401c0e814a904090060b482c520320040c0f81221070400180d00800b4200156041d50000710480c4078075058403809100008031045ea207040806554030091a02002040101048000710310300b100c40e44820007138003d003022000310b84d0315910074695070100d02034501c50924134542070544643c0d1a00700801c40000483c3d01c0d00c600e0284150603104c24000e040c0ba80803201480c442d21401100c84c2d241b813501d6602034080300555503590858005071031034a040c0a0141c528041040303843c200140c0c0c01c0000c0700c0c12501c00481c007240b5aa41c956400c2d0f442441d501e6000b1000e21590020001146c0660140382518401c1d0010314440c10907038207010030048202c4102d24960517100c8144040b038141d5020b0044416 = true := by decide +kernel

theorem cover : BRFrame.Cov 517266187 517446043 := by
  have h0 := BRFrame.cov_init 517266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517266187 ≤ n) (h2 : n < 517446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
