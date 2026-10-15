-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:24.405516+00:00
-- url     : https://prove2.me/submissions/be4708f3-3522-4a1d-9cbf-6aa5cc2bf346

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791906474 ≤ n < 792086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791907724 1250 791906474 791906497
    0x61a0703050a0201320c0a0203040e07031107060f0f05010506090103090c03020301090309030512030f0601030e10330e06060c120a0306150503090a031407061e050c0c0a1b0b 76
    0x30b007a85c003c401c1d01e100180100281b01c041010844030520325000400d54089803141c200441d90795803500000c401401a0600d000144540420520100102a00103001402d5819070412002e0101c1c84076a003038900c2807140076008802081100850b520903000041c6190141c0448103001e0343e241c1c046400c492900c2c00a50000d1801c0c4418410800705000c44a001000c03080450308604202d101d02c46141c2003e400c040c1850783d0b50141d900312400c02d006081504030907440c2000380c3c81c100e03241d0380e07034601c0a8400107407110a200c0d02040941042040c42040d24404011103101d5643c00c405d20603d5404905045030611480c1c810b4040c3d003400c1d0b00104142e01c2c90b030b41e000c0b461514104403800c49420807400c44007844010302c10084600400600c03007001c2c6815103001881c1d54100408600903100700f03000900740c1d81c1004040c0030014100b400200598102190810072603441688111150150380803420035500321542107404540d108200300301001c1d0445041e1121a56030300b081c1c00702d5112040c05072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791908974 1250 791907724 791907791
    0x714090307090c0816140714010c020a0519050604060506180405101d0a0209070302130602030417011401091a090f0a05060a060c03080c0712080901061a0703050a0201 73
    0x16580343c0c8043e685170403e070440d8040300d58100c940d0300984003001410f0356809040d00400e159050100c40424503c800c00110004c0220358003070400291a0b01c4240020f5405103d542404040090184081d001c2c5540110281c2001e440d15660701c00901782c090140c6502c035108410398012501081e02031405284104008c100e5102c0407100341c0d00341c9190f100c01c0380710020500c152500032600400d00300001e546c1142c08102942d80c0c0401580240100702e103444000e03030385d000c01103503c80e0008000d0055802801c2501c10756104044180d09a46104a141c00f121260a004119051194220210342c200c95443c03100b450201101150a10380125044202c80c4c1e000001d01c0400c2103c1d200d06034103c0c0702602c80c414202c1c2402e5001e030900203064001420840110b0026540c440c600c3d05031240f259101c1c00c0c10481112442004140f002e0a6500707083c0c5528048000030746115003108010394283e040c05180c10034594ae101030301d054019111034410b41d500c0310704003031540d413081015400034000c041200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791910224 1250 791908974 791908991
    0x501020f130e0609040f03030b0d0605100305100501210501060b161a160c0204060807030c1d13060209040f140114060c070e13060e0102030a05090114071409030709 72
    0x103194880d001d00040e000340c180c0e10078000402c06c5a407084190b2078041c18040b61181a90000c0b446140500c840502240c1c0b620003403100d448403404041040300e020b1401c41d0941840d184900c0200c61082c070880017001081300d0f41c054021101128455014052000001d00c6503413402e04403140d074426420743d5102c6035083c2040e0100b100d1aa884c054052241c3c2070345841d0300d0400403a01341201c001c6c401d0824040c82d00c2c1e040f030456072544c00030ba02428100054811007a0f0328544041440311500810802980c0d000c07481301d509407000342c55442845c440705640240d40d61611900020f600103a00344c0c1c0c02a40b90406121401214020b586240101ea00500340a40c504040031800304040c9071880c1c89044100301d24248520300103494029105804800000e544916400100201e44010014005070a1201301213200f481075029500c2011668000c5c0701d5070707469800c81400c03610980d044c111503030b496202056400d482030040c15101190380040502e4000c14000091401d40aa444049030a8440220 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791911474 1250 791910224 791910239
    0x8104203050304260d0f1b021201050906130f020405041e03022a06030619030b090304031b0501080a050c0d0e0a0c06051611030102071211060610020d0c0501020f13 72
    0x184c10f010814880540030007225508010200c50480803040304114a500c0f03c0c1002e942004080300705141d005040840551074142c91340c1c00307043d0407150110207002d070000098441a11a4680f402150300c010401d070540e5a03542004010040500140e5002844c0c2d0880d07516426442c0803c49100d000e034000b402c0407180c20002c03031910703c2c0b042501555461907441d0b004082d01c034001904c0c0c02c8038040b2041358183d0680c1149600d4070003254805400c4030000414007014102c080010300a0303e0152460440c0c4400ca0001c00c600700100c2d20840e40052a040002f600d00490741d48203603046034a00500e9840c04c1c04407008541982c1c03244c0340c0445690480e4000b20100300c0d91080960050006040003070038852080340d04001c40e009000090600d88021403265400d035420350403550802c2d4081c0300c0103180c2d5143c0720000c085801103090310700e5038460400841c0c10342c03a290b810f0100807200d5034000e005280464008468202120701d0803513080d9003e1104206540215026007201c0c1c0f150b0602502c4940741c2100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791912724 1250 791911474 791911529
    0x324060303051e04050f120a0c0b07060501081f0e0a12030c12110a1805150901030c0c122d020c0913030512130501050108104203050304 60
    0x100d0030080d0f4002c000820103030300c0b00e00e4001c00c0b0440451706d1840c040c4540d0740c42810100e2034400100492178210700825081003910203404e00b0750103034000308017583c0c890b00440d664421500c1c45d4400c0c40b40e40c55025040d480700d500014580c3c00b141040e12201e10107070340d4120541c02020b08260101791900b00140d012507001000c80c50200d5030440a101200080203076444900c100031a40040100c2d691581694070713071107400d0700000c10010700580c0c4050402d0355903041c581c0041c1034a80c0028107082440311014841e02211501940101640c002034100c1c4000b501d84040c1401002c41048244901100c0440000325a0181401e950082c181060204040041005005001c20100f8100f10010710200e684101907030724145000b60f1a5440f91600d0300102104484070380d005100d9803c1034008503403074001113180c02c61000d00d408107008502d0000003900340c6d00e40a4032100a005029540c088007444400000e030480d940d95603042160f40e4507071300e90b941117078402d4000100841c0f0f085040c3c01c01016080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791913974 1250 791912724 791912767
    0x170702100e0f010c1d04060e0a0c0207080f1005010e061509010c140a0302010c090e0103080a0309140706030606140906070828080112030f14041806031109040507032406030305 77
    0xc804001d1a07040040d11030b005e48c400f074289424140c3c0c40f40a80b04c1c490082040c680074020010849410b002041c200554994243d26074140b03860404000040034240d0510060180c100105451054041d5205208903604042c18060421400c01d01400110b0340e920381c0f0714809031032030002e4202c04070a410080d0031b46071141c03651010046050780c10000c00550490032410b407030344a500307280e681029000c01c130081c4c03065210152560001d0610791a017a4000a1341a00300c0310346403428003940d980c5400030303140040d0340110072006440410074a18540b400ca0002c0016070705c80c0c025581082c540020001c65035081441d04a101313500800c100402a412042007401454201d4000c0000c5a8540d0024108510325603618140211030b02503000ca01c445501b0345010301480c401d0292400c0c3c021602002030012440300780c0700e4850036071740f149942c10302d0325000388610340280c01000a40d16640e1204480e800152a5060314620036090103280398260080c84c0003940240c0e5525160090030000481e0400210f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791915224 1250 791913974 791913979
    0x61d01031e050d030b04060e01061e03020a050406050706090f05030a0225030f0c090c20010c051c020705030703050c0c040603051f1104090c170702100e0f010c1d 71
    0x40795214000ba200080f10300c2202c88074500416a84803007030101c1d010b08115040044080841e00020803140c2e480340c091044080d003103540c059108008103080e8200c1c8508945c410004408010612021380194010070100d84501c000051001d419140c5099401c0401c0046440c1d400009114804582c1081102c195107441611118822381004100721414054840105009001400d00050014102403030f0000d01181d0300a004110a0302d80007041903031013041d410180b800400440c00710312014414001a424a40c54151915010f5222805280c440e450400f6044c0e4080118030006903080c0003520141384030b038552584031641d00c19101c1c280071840085c40d000f540703410784c100b020076400a060b100807200360300030041d003940f229030540c050030703100b210000e000400040003d0f181134254488010102c20744d8440c482d048141c03a0303886d103c21003a600240168002e420300b4450040c1588507c0300846020226808900311885190a4490551010307012580d401e071103d40d40c01c5100f141700c075101d404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791916474 1250 791915224 791915273
    0x3120f0609040f060e06151509090114060d021c14090a110f0405012d0f06051c14180307030210050a150f0321080415061d0103 56
    0x680100e04050700082010340f580400140c00818411254440410031000e40142e41e900d103020210803e88030002c0301c2e590300500c0c017291500200700c607400a40c1e900c500000c2501085074a41050000c03520f2100011940c0941e0030403401035040c1183c4020100140c1009600407080010700d84c8000301c420001d00000724980344000c01a4186d8045508601158046078618503c0c091901240c2c14801781c8211580091400d0004030303045906001d0302030a656800c011036149011090140c4210f0014420724080203045c50741485082d0042c000f03400f0203283c40700003030441c5480314000710031b1700c62545510180d0383c103000911540800031041c112082d18000000d514080d40380c0d4000350b440032104e40d6422042c2d91000400c18002d1140c00c10240c50403034a0f00603201c0e0381c03074000304a1035140c00d00c42100c4036641204801c080c15044100c008581c00c154440f42100e54031703370301e4004ca50f404c01000c10000b142d070740c4c001040704402030303100f641d130101d150b8503080141d030540c60140403008070501101c03000000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791917724 1250 791916474 791916481
    0x12010c0306060342180c020c033012070207050a051003020906040e07020d120b18090f48150904020711090601090308310803120f 57
    0x2c254586811403000140c0d140e000d4a00c1d5030801613202180b04805003d6450100000e610b00b5001c0d80402580c0e8800d001c0254801c182800c1e03985660369101d098164008503003401480390303170044001c094001312100302d0100f090b20841c019035901001281c0d2045a4000a0042584d41044501c0c09080e00b912180c40d080c4c1040005040030000d0b0850713004240d000140200d041d00d40d101030f503008100c881040c07480c1d070034a084040c0d160000001010001105c00701c010035a82164041c807038085001810707561000500008590b44881c00601c0030505100303000f815402500c00300000001c50603411810702d41d40482121240880c10f01100e42c40c0c24130429020760071406405030351542101c0742183d030901154030001001c440c0d40141788080c4c2e032289c8080344840600040070b2100716803c2c1c4c204c1e0071501a944200054495035a6070002030075440c801d00c80c092100d034070340040e410b8806203650070050400030407007600203140ea5900b140c911908045000440c01c00c4165403103410100e041a481001c0c038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791918974 1250 791917724 791917751
    0xf1b020d080c0901020a06090803010e0a020301050d02060a020f0d080603070e0f01050d05100903081806091b042705150106080703090804031b031b05010203180f12010c03060603 78
    0x220180030008150702c00034060039907a008201c1d0101c0c0c690f00c102c0a200032011402c0240407901b003446004c101090b00c800007651101580300b240c0c10381c1c3c4002c10310884d0509035024082a600241343c00f07401e51085c40b842100c40030f4100a00c82c541609590345082c985008000e02d0300304010b83d03012031040d0728844103001421040904981c1500c6040d24403020089113401c1c66441c0041c034140300d0203014034103450041803581c8040824407035414444660704400030a090547e0b900411034910000d900003920401c5007a07a0002d8201075000f0040000c1075092040001118020b20040c0942101030300709114010400180042401c01003040901c0100c1d40c54400c002c0c120210041039075040607610312410301008504825580910b410941d070b040c094681d000002c0b00101c80340400d5403444140388084400d0101902c441c01602c006074043c5081105144101c001850011000c1341e00c005c43e190a1545502d0b1a40c15042c00c1071000c00110307050148180240807100380f904200704040c1042c03a84007040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791920224 1250 791918974 791918987
    0x6200d0e0f031c0c05040b0c1c0906021f0f0e010509010e010c080c030c1b030d0b121002031321080f040c0501080405011b051e07020a0308030a0204090f1b020d 70
    0xf800030b05404520040300d40c004880612880d040b01c0c150070400328030044040000503500d120802c0401a00f035080742002000e030380c2d8910074462840181d01070100c000c1c100a0024800304038010840300451000211034000c0706846484010360000d070f66603010040100001d020b0000840d042d07200070058910111070081103008001c0c4401d1a404001010481c4c00300e403402160360500810000c840300398010b400d2140c40b0340c007000d0100c3e0740342e00b0b010030310540e454080d11100b000e0f44c4140081c04900c050382c00d480080e40008061500e0ba00c0071083e0302e401f15142da000078490168a2806d501c00d00741825014015100140c01d610040d032542c0100800110380c007020400307070340007401c12894581d00e40c0b0b44039001d44100c0c14504080c0c031462058010032900311000d040400300c00c950b0445452140f0340410246c1c080c0d51000795100c0c11a0000f080402c2c1403100464102860040161070642c8800c107035000d071603c10001d07020381e60b038508401540c41c000c440d8200e4051034901c00303483c0100150300010150f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791921474 1250 791920224 791920267
    0x70204140f070507140601030f1b0b030604090f0510150b09010509220c0504170f0a2d030c12051c05060f0901290f0706200d0e0f03 58
    0x1d101000602409009101920400301d580c6102126899078683c50954404015940100c400380c4600c40c0ac100f040d0b00d000040001d03100c0c90000c0c1811a0346100410020307000314003059800c00d0522014002154050101c100c48246c402d001080418000c44a80da8418007688200301654080c01b103c20719a910108503101c00b041141c40c8030400801c80580b0780e4029011451f200003d10744483c101401e40c010003e0012209450b41700311014080386066915200c5200722101c0740c5d080030034210b00040c50a2801c400030b01c00e0b583c0d002c5500400700740d54002035500800580208009421540070054041d4219825554a16149041155101004011296100702100c480e40c44400140242d00c2e00030030000300220051900310f065a4075408113280c081d140001002e03041e428240c1403440d11400c4111101380c03903000001840d050141d1030b440024240d80c80e0074096141d0b04141010101c07041009041311803120071000074480744101802380380c8024281000c90580007803101000a4000c010152107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791922724 1250 791921474 791921477
    0x503030610110a0c060f020a05060f0a092a151d1c08090a08010b10050304150c181a0405060f09190801060b03040b0a15030501060b070204140f07 64
    0x2510011001503401c2c20015801d001a0f118000b000300c1441564100380c4100c1c1c2007030b258048152055102280c0300c0c5a0b007100584654000310108035004025070189038080c1d05000000b07020091a99441c0c03c04813140c508141519907240142c3e81e0b0752403c0341e90f00040202064800b58041c1d580340c0a8a20b40b94840c007210040c2d420074020403240c650442d07062455a84965807545100f0354075006410340c000e0a20140109010344000c1002d00c0148100700407094024803054664078010390488280e03100800450b02d081141507807502d1030f0442d00641d000c1742c0e40703501c0d0103e801c00740b0000c012105000742d11181c2c0d8654505468529001d4023403c44d010345d00181c400710b40d00c0218950303440d032601c5440034054000448501d294240b00311402d42d1400e5504040c001d000c00c607500d003100ca225000c11344020340080c020201164010007268054103d106c0143c0312202202e940e52100c50848203d0703401040b22620000b010003c40c40c1611a20782c0203403118142c1a19130500305648184604018070460 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791923974 1250 791922724 791922739
    0xe01080604032a0b010f0f121e0c1a0405332209090203060c09010806010c02010318051b06030c0d09020d0f080706110a0c0615051e011b05030306 64
    0x1005042440303025100e0301d0308800e220348135507901c4407038070801101c500c25020658820103020941510f407145040100b50400308441d241c0c1140c0200d0f81c0d00b8810040112a01e00440d0400990304504442038140358042a0215403110300d42428050001d0140342e0f098a9841c1c10300c24a803640200340b00b080c2900b18442074050300c803035290311486003101c0310804079080b4103000d5070001032069080d00a070000d030348240c0c25501c2e56210614855058001c0f006080c1c08251958000340c80c5520903100341011600500d008680031101c074500c51900c000903403007524036070803815240316100f0224107050322429007550018a0b41c54201207541240c0140c907100d101c03240d112503000040d075440340340c18010f494101e010240941510b01d40303044141d201910407610340c0e0420f0341541c0754580a04c296401d840c1c1c40e45a040d002021551a039000f000740c24111a030007666594003088544a070444140450340380d117200b10190b415440090180a084400030180903c4c82000000203203010041c0c94000c5800e46111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791925224 1250 791923974 791924027
    0x1a03060106110a0605012408010b030601050906250201080115021905120a21050c030a05040221010f1d070603050903040302151c0b10080c070c08070e0108060403 71
    0x681400e02020020b001329007800c0010408aa00030036800d0352101090107020060f62505d800e4038249400d00c608030301041b0500002e0500d5015070014805080f00400340e6150411400d90212286040d40b202001009080a12411943c001030035078054494841050804044000001d640e040700020500c400d041c00f0141e501080410002034034407440c04440d0a4682418480080071580c11403552807000d815040070220700d02d183d00c100f038020302d20003490a26660314160100050500a00222b0f00541c203014000d19441d03058910202105040340003045541031805404152140b081c00b5083c0b240b40107001c1d5491450016090080350087d04020846035103420f415821801150b00180d04024030b4880342030300b01056001091070a245665a1803994000300c80c01045031a443c0c00c00d070700700c2110060016a280600041688100001c11a500d4941d165540c0081440150f201c449030343d0207040d090140e0304000340c106000d01603d0005221500c0d194400030104148080d601c0289503844264 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791926474 1250 791925224 791925257
    0x2030a031104260109120f030510060915140d062301050a0807020a020303040612050f0115050c030f07060204051005070f12180b0306101403060603071101090b0a1a03060106 76
    0x170300303501c0e4100040c640b101e004841d01400040c901131016000900d040001800206019124020b80d102c1d0703501d0110307450031720b407003500500340c0fa90308103003440880c0d005440950040c4008000c11105150007156661810a060072403480c42e00420b490008980054185c603680442600e0100342d0302d24240c091307034440480583c10720342800d00181d0180000580411031039000040380d8401403001c1c404210b02d41e18091081040a000c1c0100311000740302040d404001031088018000e01c003460301c10b41c0d240151455038460203a11030b420481b0301a402003010030086c42c04a5105595181a04100745030100b03569400d0f018200c2110028005020128003501c007a209804040c4540c1096a04058050300c0340c0a490650300200c801c14890210384da003480b000c51044030341200d01c840d103400300c0741161500000c10000d900024890401c04c003051001d140c10030001d02954a02c1c038015044801c10381040310031707202500c0a4440540e180c2101c0f16805844d40c80001c2c0030703411103501c0d1900b0544811590b82 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791927724 1250 791926474 791926481
    0x3010b220b070f0c050f01021e0c04060f1e0b0415031e060801112106150d090312050c03070806030c04090308061011060f0601090f030302030a0311042601 68
    0x42807000032844408000c0900f04010000d40141c0702d114919a6800c100074085001400f03090041c0c00c4a164101c0d03140d03007030300e20702c2107401514240c1d0100c0ca4100e01240840e03070783d03601004d001d6a03060010008610000d1808050f07420980c00030b5480d9041c003008182074485c1e031103503d00348800742c5401240c19100750b000c0821408660600d40310400e403068404041d100c5800748510951800100c80c002d144681c003120740c181024240d010718410300c4546540301190051046070492022080314460240c400d00604900c0c1c41180000b9050b811070034020f11005a01d43c41800c102d1410042c07100b00f03910300e01a00d81c0b01e030141c64400b0703041c2c0d44c110210b41003190702c05c0401e070010700303041e440000c0540182c03446215140580b0181c0e450390a03900300b11062804a04001c2c0755400940200e0040505403480d1359100c001030504018680d500e01c050941c1c040b42d907006038016000400d03075034100340d410b024440c00c0503058500142480e0404c040e103d00101949110301d1039542141140034a44003c1d007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791928974 1250 791927724 791927729
    0x4080d06030602030406051f140112090506040f060f1a04180803010803041a0703091a040506030c040602060a09150c1103030a050906090a1205090d061104051503010b22 74
    0x2c0e410b640341d041c00c2c5016400350000342c94081011420540340d5911580b142030a80c212038502080d8842c11581c00015180c008400c40d40c407000940741c0c60944040364040190a0007a1300c035620903035640300c060400400716020000070302c0c500c0c1c0c2043c4004056503c80e41c980707440c820045400040d0710440010400c018410000300030500320000c40000340c00c3c80c0c040003a0040f81c030322103804010b0704900f824543c1d082c03140300f60046c0031401e050818041d101011200c40204201003c076640303056100c000003215a00100d40966180320005001e2200540c14030505410012448060003117001e503584111428401440101040c3d0340c411000010900c140256141003002030142e980e6420071075440c0c4060305044401d00e615105a10100d06289030010780034003501e0300081c046804005810003115264040900345038445030340ea0841010481900c00d8148100450790103a54030f502d0842072103035154003004039844002d0103000420110059008642c0080501481450004d80c450440082044941c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791930224 1250 791928974 791928983
    0x30c021f0c030b01080c07110a120f02011d031f060b0705030a0e0d0b0a0b1305090105060a060504180f240f09020405010f08221514070804080d0603 65
    0x100103500c003892081c1d00a8084140d01c1d907040c42510300310030041d110a0000e662031102648104440c2000c07413061003840ca80d942000702403030b40e002d0782d0360120800d04c4924141520b004000780b081000719a0050383c00f41c210500c940140384078540700300000ba2a1918060002c404401420040c840800c203640003501410384e6078803868480c0c65500300190303a030f0045003445010809040a04001c0c0c94054070800c62154010205403050303032180c903110050000564103d400140f801d080e00c105800d03038000d0700d1042039014000600c03494080c0c2000240c0525512041c140f050410080c00080000e0f00802100c0100707542c08104000e101c99014020029804c0e4840b0000d2040c01125140d0a421440c0c8101c0b000d810301408500e45640c900c2d0101c2c440c500ca0540450712040c4100c1c40d0170b0081d42d40c40e40c456040724404503079100725942400c41d45442e00d0129451192002915004006403140345e0741c0300f01c250702041c418a440d02d00501803240141014140c0003020502c180010000d412010103941d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791931474 1250 791930224 791930263
    0x8100c09050a12050105060102010209101b0c090f0605010809070504050612160807140a1e0b0c0106030219060912140111070203010b101b140a11010215040f0201030c02 74
    0x480d600310001440c1070700c0481d44e41d403e0602280b203940c070500031f0f2081a440100044a1352680040540b0007003518007021031103001510395000440c29100c1c1c0ca2004244d490b0000c03440d0a4a405120b0480d4415082141170100075028071203030344000031b12801603480903100041c0035103480700080c928880d02c500c9001540300b011030f4043e140550182903000c9400c00000c031507042c3e4443e13201c4280603c82e42d403c1c82d04182c103800104071564000c540921500100400f6801c10740d203600106500750300c241301c803003026074442c0300810071400e0080e69250500c015081c4090900c5c04c16800030714240c800e09c14450030010012103041400210a0304540540010008001d1900000c08550082d00400e2042c1d120b5481e02e103251f481c40c14401204d07155280d1507070720f203080c0c4940e080e903400c020360394110180d40f281d43e22180c0001c12032042001441007030190701c02100420003013000a250550380001041e11103054024840011084031107800a5039090901181080403402c0891414178084d40110000780d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791932724 1250 791931474 791931479
    0x50909162c15090108150a111c0c120203040c050402210423210307050c01050f01140a03030221090918060108010e07030f0305040302060307091d0108100c09050a 71
    0xc0059600490300d1040c1d83c1080c2e10307a600d208040d21441040e13201c401c9020748500158110702c0035803101c00e4000601903198140b52445031030f103180103210035000b6041507440a86100c40c58112513010344014548005500d1440e2954612035112a00d204260056401160460000d0000c0e514402c581c100801181d40c80e142608003120748400e000302c0074084c82c111030040c3c07040321000304000300c40c28066141141a040d80400340481503000402d00070401205228601b010031003070040701d010b0140e20280642c10b5050414000300c42110080d028419078283d4000c1000a0b00410310414003c4010b0000001e66840129610340380702c2c400780d45a1061910040020451000920143d110310f10821941e441ea2200f42c3c840c00c0768500100d120940d0300180341000000d00c003004811101e84a49401c9090550700d82c04280c80343c00940e100c40200741c03a0030041c000710103441005100140543d03e0301c04d01e5498502441d4071400c40f08244102d0a8941c1c120415041c01390081c0c030b000b00b102400e42e025065 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791933974 1250 791932724 791932741
    0x1b06050406060b03150121090c05030d0c02090109020306040207021005031b1602060f12010f15031e020d0912020c0414060604050d06060519050909162c 67
    0x2008480807201d051804074080b41c4059a0b8056a104015040c124500364550070019a00c50601c1550841400d25080c0e000001d4011402400085489500c0481c5500c2c00e280800d400e02046007102030070003200c0f1142c1070150350b075800051304442c072885005a9a44458010501a00c0781440c0603420441140040c032210f540b10703004510400798540c19041040c4c00310704060191046900b10b064400c0e28094003005481c01c0300040400b403060410391407400070006410300208800740d10242048034036000800c810141c9459072190601c0c2882d003042000010445149e084a0341040404411303404a0801004000b99000b03180180d001400c80e052140e0a0400954402c1a140240d000d03604068180c2c0c0c510706401c8841c3e0080c1c1d001172449041508200c103000690b0b40140b000d40b2034a84501e40082c150302c6030a60b6000c90b90054014210b0b181c2041d0600408000103460f090369070703000902e00c10000300300070b42c0c0d242030706e080e42d070b0446e41c1034400c01c4000004041c0900070444400c0e110184481c09 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791935224 1250 791933974 791933981
    0x1519090b04110f030c10020c100905030709050f0c0306030118050d270e07091d0105090c090a0306020901030e160e09030301080604020904060e03030403030509190804151b06 76
    0x2140b05402e0488040c00241c24802c010205107440344e0164042c0907807105901c1d00c180c54001500403441111050015807001819400321590820046001200280080d04051200324094080c840d07040c40982451880340380040380042040942c600080085059030b0b500790480306101d0070640360100c091041c0c0c05c046c0d49a00c007511403d0302040349076403420000e900342c0c01701034040a04007103000611850282c02036880b041c0104044100401000c1c04100c00200c0707420140794480c1c225480d0199814141408000e6070060b02d140d0010f0824800c440e42540c03001880750135a54030100141c0c50312802c60044e0040c100500401c4514040e5840300084050100c14803001c0320714503090480c03641c8940547c1350300c80c40280280041034000030005400741c180800c3e80707500f29204030700025403038180d007010604580054408500182c2c82d041480040301e81040080007100c0340d040c9942c00e01415030789452143c404c91181c1c200b82e10049003640c1d015406010000078181c100030103000100192725041009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791936474 1250 791935224 791935231
    0x1050405010b210a0b0703110a0f180e060f0a09020f2205030303070525080a0201060905270f0a0f0614070c11120118031409031519090b 60
    0x1c0d00d032080d0301c020511022201d00000c2e484034000c0c008a81d180d0310b4594034402c5c0113200b00d061603294040c004031709116000030f00d9610380559aa112861030040002c001e41c403208a400240718880106001d0700d003080401c117030040f0341201c00c40b00344070455011031211611036100403c0180b0103c0c1901d090750000c0002d03d01c00022442c412542880820321103c240014024190542c0c0148001440c0a0080c0001c0c100106e420000c10381c0205080b0440c68000c030740c0c0c607003102d400101207000d0350040d8090107480f018241400f000c0c081407500c484052549001e440329018041448130348006c802c3c106202c2c241441c80413005450b10b00c83d8500b8445540383c0e41270802c0380c503035281c40490341040c4a00d002540c06080c0700da03200c0348140040c0d282c0e02d1400c91020140c55105c849600c00960b80002449489000601020300e10112100c500380070300241103a03007251010150030408407445540c0440c4104507001c00b85c1c1d200b42d46440b01810030140e80b0b54004d80391083e80c50280010284031170001c44620 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791937724 1250 791936474 791936479
    0x6070c0b010801090c0e070c060204060f120903050d090c08010e0a12020c06030c07080d140907050f0607080c070e0c0711010f0c060b060702040f0e01200405010c0f0501050405010b 79
    0x340e599a880700d25007221408400584142d41d00e2209100c082c1c01354444581002051801c00c4d0004000d8560004a038025031045000c25a2141cac120311054202109140004060000f00302200458030081c085210b515000c448031951446100c0811051201070000b4002280c020040e003400c95608a540311a001c806036000ca20500407001843e01c0010a09400d541c080c00aa04503181d00488c0540b41e081044225540c1c801441003142d0f24195224111240040d986281072605129840a00b8000a03802460040307807102007a0074140c44803811610300e568842407980da584c8000c503055003400780030b4002223185201b075800c0c0500201280081c0c000c4c02c0c0500c4241c20705802d09001500d100020f502d824010809116100c00800c0e100d0380b03c00a44000501075524000390790740020125610740705495180d0f82e903500c0d4850481824800c00c2440d50702a084194403401da44190203080c040d6104050400200c203080740d0401c180c992210700e1040c0d224000340035138105883c1150190400100f802e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791938974 1250 791937724 791937743
    0x111323030303010f030b07030f020a030501181401140a080703050f0717100903030b0d03020f0d05090a030b0a0902060315030f030a1d03070f0605030a111206060c0f06070c 75
    0xa0303190110440341211021034111072881e10b995039150300810001c1c02c032402d160b681c03d101541703608180024a6090440e03500060298181881e40c507450f400c1c0ca0402d1b20b484d21b01003121010308801030442d41940c0c0c1c80859980c4c8106001c002a007843c1d180e8100081034010268004100080041d02000d2148240c060360344a07911801004805840604003407281d500200c82010350001d99440850b0050192a01180d6021582c000c104a980c0e140340c100d0069220608044800c40140680380041310240f6040b8984500240003c22030b039031600024006240010120b003079100079a1054108607406000c0e182c0300c0c50240b8044042c0044210303600d00070301899400940c00354000c021141d00100584032940a01380c10b58007d02c421102c002c085805114160011500341540c034540d400901640d07aa82e40da910307080006a0903103041a0310041151f00038070902c0e0780d40782480702c0a54000c00c181d450507210484c420843e85007038120061103900740036200900208603484114014028081d81180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791940224 1250 791938974 791939039
    0x4061701090504020a05060a0e0a0f0512010e120a020106050409031d010809061f0305070b0403050f06071e0314240312092403100905060d151113 64
    0x2500b680c0080b0b5000f940004003004c140700c1c40c9006c0010b416507105a1500410100300c0801241d0444440d400c000001405900e0070070003407070300d2030300c021954003000001d00c081148149030035a58a0701c00b031054074082d00441d514074100e02c00d601140003010b0081041c00444683d09020705100360004045540d14207a8860903125401006083d00030f00b40307034005000e203607614904c290742000c03940c6001901074400c0000001184081003260302400300307131031a15503e926528009140c024030480c2c191890b003003941001001500458a51a01d40702e01c003a420000d1003120084000b8010b98ac5c29070788000d005000d101410a0141c020344101402c0940900e41800c0107003007555480340c01072640d030010000c10020301d0f80d003401d03075103021140101e4100010341d04411001c103080790012203842c0180080e81344104055042c900030280c01190070f861005064155881d21406001c11108090380c2644a08444084030040700071140444405038519281507218038030341c0d4089800c82c07905c008025000648 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791941474 1250 791940224 791940239
    0x170f0712050304050a0602030c0f03010306050703061208030f0a29040b0102031204020d030e031227010f180506210105040605130c05070b01080d08011a040902030c040b04061701 78
    0x2c590185401c00b0040ca01c00b1211394403040030b07600080c0010010341c4d050241500300342d01200918081c52007140049601e00e03205400030f00f15001c6502c0419400d16942000d40803685501c01c480d0812001c0040e4101d035900c002603040a045401030480c2d00c0e0144c00780d109030310740c00f840c400100800119418444403c5040049980f801001642c0d030708068080c02080051814070400340b072562103401c0c284480311007440000c0c00c012a547c1c0105808030005003e00c0d082c01d003160080e4820a8106d585c2e1110000030000900c060400c000c0e42c0e0074801076150281e00c4411002145008007001421541ea4110914024801d40001e0300b0041d1111410f000100d000d1501e8054102640c0c000340107503002001d03408144001d001200300010600c0f00c01c00440d004200380c01162406030040c40d004090001640c10018480340c41644044180c0d9101442000428008400c440440b5800c08015071241c4a83d1808001440303941e0107a81481c400280c0005e6082d0801d03290704e0310300480018401583e81e1800e6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791942724 1250 791941474 791941477
    0x90a030b0f0f2802090406030c0b12010501080f160c080a0906030509030711130b27090d23040803030103060506030613030806150c0105190b03031602010507170f071205 74
    0x10071440d03400520050702d03183e050f0380c0603049001000b440450b2899030307611000c0e1030101031b801c003542c51310b00003609600c0c0155001c581c0c1d004000c2868001c240b031130408400410110003921007045007004400074850144143c0074441c985800c01a5540d544600e264060406030040c810b1401090400f4002100d030100030040c2c6602c02e4103c164400c3c2e06007c01e040080d0f011641c105c18030003940e1403002240e10f8503103031281c00d00503e00c02c41c80200281c0ca00500746014030002c001a05c140d10401d0189807940c0d211000c850240c0c0265034180010091074128003142c01290080c0080f4400403000000303100c030342e030841801200d00f41c00b590706d15140c3e003500c4540a0009400540860701c408045582420700d400702c08401d510032004182001c80c0100524251070090340d55007000c20803d42070b0030103a21680325071601880d00b10004c603e020003250300918101001781c80681030240100e146410301040141110400200d80210f941d605a945030000298110701000d40e4070305010310140030464003600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791943974 1250 791942724 791942761
    0x13060f0203061819090309090513020f091e06030304030506040b180f07060503070c060f0f0b010504080c060a171006021e031b030d0213090e06010515090a030b0f0f 72
    0xc008809510b0000004001c0c5c0440b50b003c80400036420400211100140f00300c0d4055802012a0350f40b591260042208900e241e821062142501000b48000400c0c00c522040009005102d800c0f042e41c0e910000030700b94007ca41c0301410f20702514081104001404003a81c0c0b0039500c1c0003210821500c2d0b520fa00d9500c0c2100603c0c0700140d81b001400340820360041014590005003860700c11201030380c0e0b5640e00c040c0d4003042e601d00c681a44540c111080c55005005082da07504082c81c0071810326181640c03040d55418101c08050040d500000c1d140d919501c0781140904000740d4200d071072100d04002002c010090f51a204000040c01240882c882407000403070b4a082480d04032004605080303040e107400d5a1614542c041c0c074664841085a007203840c07614005442c981c044ca03480c0700b40041c607140540c070540b4110304002000e41c02890060050ba039030900010b4042e6000328101d5124030361140414569071080d0000f0303000781050000c01450001e085041c6200304680546e540890f2524074900b0480d01098 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791945224 1250 791943974 791943991
    0x706060b0a053a020307020601061d0103020904151d0f240a150306061404030816080702040906020403030e030106080d1202040e070c0309061704020913060f02030618 73
    0x10880410305880c1402c540c0344003040040c0222075500c12016040f40120f403000c400c05400d40210030080044e4050100718010f091b83d041044540c03103080c641c0c01040d0343c2d40344064103050340403588940d01d4440e0781c02103c00c7e243c0c2550700b00305540c40d810f000081e6002d620210011121600004030002c1c2103203403007130080b41060034840c2c4500a204006806107410b542643e005100c05000080c0700081e8074003415112820346001450030300f440c2004003003044a040e00312240c00200801c00001703018208842c02d03014a0f00146400144524024034244150000a0f500a040c00102c46c14812180d0003003003240c1c420740b558005114590b0600d42039411601c1050600e402000382c52202c0d902404045c41000c0d4215001480c5c80c0c0c44095600590106a4081000a141c0b401071020076411260820140c0041d042c5002a203080d2840b81040340c4008200a000c0e00c81c51b00402d203015903501c00c221000ba40008107002c0b0801600b0864025081100c0d00d46c45110101280990004a54940c0f40140c610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791946474 1250 791945224 791945227
    0x10e030c0a260f030a020d0906050a0c0206061509061c020d0b1207090b0f1e180f0a021305091e160503040602070206121005041118010c020f0a0b0706060b0a05 70
    0x3da19101240c00041c00105100d4080158088190123485070600c2e0314818800005c050a21392220802c40c0c011035000c3d0190340c003450520900d80d951407a10a40740d2082c80f4030350303503e5036101d02240c0b050080d6075050605030301103004e803540c0700c0307107038014001c00e8284645c00c200340c400000400101002c2c2c0801c090361904441402d0080103819000202c20103006401584000d01c9a00415901d50104039001d03c01105445902440c0c509050244c1d4046d072401000607660520404040d003017400603184031a266400079640b00e00c1d0148101c540024103006007200c1e840c0ca040602c040344031481000d103840c0c8102d40c400041c00c2035a9200b10648191079590740750f00310758481e5903280080d0b018284c26071303100c1020702a8103200190103004900c01c0c40b003215918105860034061000780c1d1020002c0528a910034001c079811000c41d1100744490003424a4004070380012800800c803040142020b2a400004150300458a41f41e030100800c0c0c400d2180108101c0c50395035041d00c003010701441401c000042d50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791947724 1250 791946474 791946487
    0x40c0c11060412050c09010501182304020703020609010f0e0c01031d010204060909050f16050a030e0304150e033d471002010e030c0a26 60
    0x41465240a840c44040c090354a880d44800440341d01d00c2c884a41280d0990000c44108060705114080300c0c018142030030b1000003aa200f410660320004d181c014280d114182d080c0c600084098944500c4a070300000d4003c541c2e500351414002d4881d4021103803100700b5800d045000e0103003506407058020754005080503043c14070f00780c40118040e0001c071800700220580c205070803058400c20720080000300031700c0c3c9801030602e2904448805a440003842c403000c1c00f41d528104000d0b14212a40226003034607030320742240d4403541408146e00800d000aa5481c040c40049400300b0540255000903141102584030600015025002c069484a00c248003182044030139002c40e03076000720480c00700b2030006d000200c0b0100d40d580301d1030002141c1500880b048142c00c51f01520100c100001da090030810920f00c5c9101d1002c80702100c1c00c15054002140d40d000e5042e061909410520039031084038419500300c1520794510b0901584e41e0b4030078000000f0358003050200d4451600d82c02c039092a41b0b61404070f0729014105036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791948974 1250 791947724 791947733
    0x10e0117070e03030d0c0504081207020d06020d0e01060f0501022e0e0307050a030503041509030c0213060320030609030c0d03090201092606090114060f1801030503070b06040c0c 78
    0x145220700183d0548005e000b40403000e903050007180001c140640d40c1c1b54580745002072403451300d8500c4074000d01c5040c04100300c401607140c0c01f410b81d86140e041403000da43e4940c0c003109440200184c1d00c0e50340044d440e1680104201109454843c04c60342c0980c00c448401c02c0850403103d82d040c4808040c800d44c9001c0d48598054502500700e00c6000181806613030034005c075511558104001c9007411400150000100010004602e007401195810141c08102c025040d07071f005010000101c0010307218408012405000c980c4580000b0090b5501c0031441d190215102301440d0011240f641c8a40300c1e00a100c001081c0c03100000c269038058a100b001001400742c0c0c058240c0081c0034400c0c0a0f810403846180100d6003d0200c5000142e000003102c50000301040c90b128103081403000303042126164141100c0c2000c90495600c00c0382c202808548480d298242c4200180000301d80c04600900750714a50000800d008000c800b03441c0d007074080c500090300b50381c800341080211480c403580440420600c91113800400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791950224 1250 791948974 791948987
    0x10e1903020a060918061503051906082817070c26010606020d09060305100509090609010e070e041b05060d02040807080106060504210f06050402010e011707 69
    0x1214111020119103440ea0081a04503803207801040214001361030800c420b444103411000b40405010040110700d04040309030409503c2541c001d0205034580002c0b9064413641c0a1030f4052400d00c940801c04942d5600109850307403a00e2905c480d06d480c0c041031005428034580601c030a0301d940110314034580f007000700002c030b0f89411000090f03580d001d441001082c1483c290f05406501525070800300006c44400b400e260945a5a400c10000c44d0042c030840b100039900101400c05451403400c000c2060fa80d0707486c01501d903000f250310042d8804520030500c4019580800c040e401040070000134410f00b11141c400c550380701d00511035103603001590800503010400620b10710804000c09100c030312505035101d00054043e046001c8216200e0f40c0014108000030003004104018000c1c100244007e92a0200140c41d5004900c10b1564401001203c0c40c05610985044100c6030b52000c03400e0034211913414007100a1008840c101c2c041600c5805200741036002d041c048240b03800750325080340190b85134141107401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791951474 1250 791950224 791950249
    0x1a0402040f05120a0c060c12031e0e0109050a03050a110f0604021e0301060305060109150f09020703021f050f0a0b0d030f0207030b19060b040f0b0a0e12011514010e 72
    0x1900940d40b03184e00207541140c20500814141d5560011a1510b040c840140031591101c1014580703410525420a05540784002140d48020030000f0341556850040d4054405090018118003801044004060b04880a030100080036682c0e8010b144030140361540e00d18062130191a2507101c1d1001400503d40680345a130018410103c41c0711104c641d002003400d40c0c00c00e800440700358119000602000c2d005104901c119000d034444c5440140c984501c12001e101180100000590002140d405241c02080001c03440f014011084409180c10050000100f8050700d41c10880c440100104207801028001c24030411001000c013916610303980c0e000e541c40d501040c210825801010700000215a1412a40d48952801030968540c10b1750500024100c0318035810159150509200c140071070031901c81c104007550040110180d480c070421905072401c0f060101400e51000310300d050001b9484064004900d21240e84088014203502c2e0280040d6842c1d24032030590001da09e03003441c10024500130800600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791952724 1250 791951474 791951509
    0x1090f140a03242913020c030a0801150809031b071d06120f0d122903060105030601120605060411070804030c05030304030c060e1906031a0402040f05 66
    0x403030554a540c0d80460444030082c10007403902c0b121096680800c5409a8030580c10a6664030b8113001c000f460704030244160900703160040f00036a600039424a5a45e04890411000c1c00889441e5604d080780102120400d0080c118400d02c0a50342040d82401181480e014030b40920156080110f503944802005244040c0b8440e1841105000507800904d50601d000e01c0940c0b050840d01490401c00384854020744031035158881c2c0c01499031541460002c21900903103449490003c200282040e0302e1340c0070f003107150b0710a5031200b042144e80880165080750180310030030503020340746243e0b1394508058481c903091207000f4950078241013160000b801e6600c0fa1340c0c0000c00400c005a1441a070b1940461504a1481225040c0b0f00080c24400d1005180141004000850081d0324003030455035100c110b252284141002c4c4103500e802c0050a44d100d000300300a250301c1d9028645d581340e407000010080d00c1d140d80080e641c900b012500103018149402128151000d80d00d1100d00189484248036480318030150020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791953974 1250 791952724 791952739
    0x21020d09090b1f0221030906130501060f140108181207140303040b100803030601140901020c0909100c0507081803030409050a0203040308070804020a090b18010306060f0501090f14 79
    0x400c2d40e60711031003503d480d80f94024032898240c140c07950301104500320030309518041401080410748000445135404100d81d4601414141c1a20784940274050b50781100001c1c521000e0040361607000780716554000c2c41309036289401922103600303200e001041c103a40c070003858000e14540200c6003c1d040081c40810b02c920200d8101c0f01c10507803030307a042d80c2090318111100307005141803101581c20014800007400425018500c1d50401c1000600030114088221600c0708001ca2403680903802484800304175000074140300030a1414407511030b1142d050140c0c4012140ca13080c040391000e44a041941c441c50350000480c1e14041c0c3e400703001840004407901c0c1680c14481084040b42500950017102c2c003902d0301480140e1281820328015009000007040401003190070401c01c80569149114441183d85841c000500c4080003804a104800300b1422000843c0100000001700080c55010343c089450340100c2c0307255103071500011920390304944210708540c40d60803014058211000c1c44c00390101401414030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791955224 1250 791953974 791953999
    0x41415061e0307020d02060f040204050613020307020c011206050a0b0d060b07080405180609060d062d0c0806030a08090303130305010509070b25050f0303010321020d09090b 76
    0x809000c400512162658107010050029050301040802030042060024140c41c1c58030a00c40030364024024000781c459602c80d408a481511007507000c040380c01118005640d41e140902000c1c0d50703010030303882183c000740070500074034803920441c40380806444008154042c0945850204040c54002c1d00c00110200d944004c0080c003103070540010000c840c40b868000c0c0d02c90b85800100000c0d031901e0a08144c1041601040000540d1010091b40d800301003126423a010a400b420b0007402800b0749086441d04030b461804031030003001c0c4401c1d40b50442c0d06a01061010061040c8100e92907841038420b00c0c4c244e44078074140c100185200010307204070388001e4210b0341080300140c81c05041c00c0c040d83c410790340c3d80d660f941406089007003401600080c064483c4113502c0c040408407900401c9580c112800e8480c4450110881044014411380250321f075040c00300c0e5180c0d612400e1000f00242c141c500e4900c01d141e1074203d810700c20700215140005038000c0d220001c00d2403511124a01900b0700216281d8044d9400407007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791956474 1250 791955224 791955247
    0x9130f060e011e14070c030c0c0b03071d03010b0d02131e0203190c021e0705090903090a1203080105090402011b05060a0b0d02060706111c0c0e04141506 67
    0x5a480ca0450b118000c4100b12000032400229581404d64280b1840000c04018503d504038080d041d149605240071540c80000781030001c1c01b4500b81e042180c0c02d0100106221080da8480100032002c1010303200d0031102c0c942c07803042500300c8101241c51070f0031084001e8100090310b40503040d404d00c546204004030303a000d044005042c200c041e008044c1c481d0f55011052014101c038110080807804500d05042282c041203200281d560400b81d68112006a40800a03600c8103400348125001402c020b01300e503c05013041d82a80d0b803a9005121748030b0207601c00c1c91002401c003990000c55036000350107445144250f420030052056815000f40203a050101080815a90400b820103000304039006002414082c01c10503100410b0718070246d505449142511605805a540d41084030401d0368003000014107400a43c0994080303001d04000003602c0403100c030486078605151b80141c009041a1354911003c000304004200071104003200000103a140f800008451a0606c0d0b00700140320710080429080034010b981 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791957724 1250 791956474 791956481
    0x50f0112020312121005030f0a060f0209090115030e030a090b0a0306050d0506060f01020f030d0c0e0310140a02190e063105040c05180d02042909130f060e01 69
    0x180c1941c851340c803002c10002d0407989040300042e02c800c4010f08101c40e401d0860325626041003101611040da0307800d5180103000180c2c1101c0a02501805034981036950b48a2034103120203548905c80400c2c20030140100400010003114000c105a4640320000c5003481910400d9401200018090566a082c085007a50720382c118101001d114a004050a2a03d002440444248c9101841c159440400802c114400110a031f0340002000840000d111007446003c640410a0350940b54050040703940d0600c2d800507a801c030340194060001d1582c1c1a450b10b088420403031003205a030b20040015425200d803c50f1241c2481c1c4807568000300418100310404000c1e60a504803141c5c0c140282d111500b0080c011111414110000c0c0400c541c05c0086500000e0043c1c4070f4404e1180780100504c8850786a0f03000c0c1c0e80e00b12003c0390a9005001000031081c901070313281d51444055041d980b560243d03500300341a8505200e00621491400d040c01c1d8501c2c2c070031b42e80c1d03003140020318108651154840101e0f24128100b4407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791958974 1250 791957724 791957737
    0x7080703090206090409080c161a07110904050a050d05040f030f05070e01080a060e0123091f061707150c11030607091a0c0d080402010210050907090f050f0112020312 73
    0x205000d039203032010039182e45000742c03849d4001d501003d028000c0013113010200e00c0351007168090200387d0b510396992420702d6048000740107243c0c0c8082c021041c4400d0140004600e6240c82c03142045460740d0505480681c5c1c54040e0784500480c2d40803005085c80068002c0340c2ea4031000d4803d03800c44217441e0f00c1d8008440c81d2030090f0081146540200d038114144070050040405c000c9150000304841c4c080c3c86c10540d56140210b089000c8607a46801040d04090108407031021003e6644450b000da100d86043c607405080c6c0751048100c1e07801e41505c45104076070040707080320448d034104461002001c0150401d5441c12030b03a10b81a500c90710002c01d4201079072410700c4142c0c0f1407519603032000030356814841e50740700180c07944d0311180b10380909115454400c1400200d8221104403400d10041998130f0340700403071030305540600309890310342000140002d6003000031b5070109a6501c900705010300c0c60b90fa0610002c0310421079007070700c4040c0b5080041010740d0020042c9008180090281c4620007070403e25041142d1020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791960224 1250 791958974 791958983
    0xc030509030d030c020d0315171203091e0f060403030b0a0b040e0a0606080420040b03030703031b0221030603070509010602150c0a0c060c03021303080403170307080703090206090409 80
    0x90543d581340d05e82c144202411034016050800c009040710807120517000c03a50240301d10503102c0c505802c503400001c1082d04081100302004d04c0e40e0346000081c0c40d0303c3e00900700c4400ca20400c040a0040550340c082101c190303c050a20003400c1507615074404801030004960990b4100704044c0700841c070805504000c0024040401841602d030406920441c112412a40880b0410138006c060000013111720b54210000142e8000e60190344030450001002000100b541d0395241c030002a1500c10142c16821009030300034030b00ca9076550034280100507622040b80341503504131403440c1d503c219210140c04001c0c54010f40090211000c003601d94010810a1000f070300010b0150340b20000c001020341141d00b019a10980c1d821000c0d0030b100403c40060070b4100d21100c020306d01601d40712000c3c4400d201e5416264100e40a508100b5170390fa072803d2070651a40207000603101c48205622130302c040700111003200e00803152030351214601c0c1c0c0c4410044008102602040f80d00c60010081c0343d1080e81c0701d0180450f001d004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791961474 1250 791960224 791960231
    0x507050c01270608100f0605040b0a12060e16030b06121906032004020702150313060227040b090402090a390c050c0f060c0312190515010c030509030d03 67
    0x17a8000180311305550303001051180d600c80090203903a07444020307601250480d01e2010303111000c0107815039900304054403010610340f604400180c50070050f41d900d0700030b04d0007040ca003078050260350302103050f03505507400e254200800704502540f504000c0c0a065200d101c100c103c0030302c0902410b038002941d14aa0090703a0620b01c56180041d1564001c8040c4004403045404501d8580b1a80c0881c034014402070050b0445a80440007400c0341c800081039040d80c40e4403480456030b40c2c03003001211a1001c0b003502c0030218444040030725240e50400b4420782c0c031072900c0140281c0e4a6503440d800c12990340e00c01000754903c0c6484041d520642c6605011204000c2031001541c50241c2d802003a88401398074801d1424100880b44082e81c0c082400410300c00c030594000d4803090002034410020448502c5400d641000780d21000034500c1c4254242400301c4c0c01140d400141884100b0304000420548030103403040c0030480e4503000881400d42c0668ac01c03285007403003810014103010314100000d060601c000c01030b00200c1c5d10b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791962724 1250 791961474 791961481
    0x6071b021f030501031b050a0e06010216030506270303060d030c0f03020606010e01031529030a0b1504060206010605250f0b0108280809031207120507050c01270608 72
    0x46d049032513040500035040702c55076940352000090203150144034a410b8007001d00041101d5174801d1244501101c4065100d0701c01a0f528a0020380d5103908551601a01c0d90405800403480d40b0320a1498840c5c0c83c04c0003c6055403160760070000b0a101a03d4100c081c048042c840000207007103641c40c049410b000360041c100500d000710014000c4407002d81510304142c41c0c1032986606040c98510b40d001e4440c80c26800380100d00d00f050386995004d001380d000640f01d20100030002d40200a4004032044c14045c0e641c4000c0d034408054209090156008000250300004010301034184140d026000c000741c1c502014820500d070944048041074000020345010003400803100611484030340312401030003003a0080144150211044c01e01545420980034090b20040c48181030103406815030b03145140042c251100c4110301d9450308166030003100112182000780007000391407030107141275814013500f00c0003134260800c41c507004544202450b0b0000c0c070384203416000605200c40f2890311501800d1152102c041c10304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791963974 1250 791962724 791962733
    0xe070f09021c050c031506040b0c010243020d02060a0201020702040c02061605030c07051903020c06030402060406030b13020d0f05010e0709030b07030f020a1d010206071b021f03050103 81
    0x40210b000710314107a0611041c4940e40d0303c00c5040b07a900c035a13a0508400441c0100001807000d110f603610140c4540303c0801c040015040650051808880000b8440d040c1100c029840c18a0a5008140701000082036059405c040d0028250050039200600d607a001c2123a03580000c0380c80d008000000c0050394040389800842c141807181c1c4801d1a01400203080c1032502110001e81c1d800302204600402c00080080342101d080d081c2078030b0340250702005031002d07180403400302c90100340303c401706900500c41d54040003c40c2c1041e10031640540e402070521460710b8289041940a000e0500088ac1c21a030702202800086401e44082c2034810045080402c4401d40d55000c1e005032041030704002400f1b034210301800b6444c1c1d0030040c95401c407a800791405103142e0310070400381c006218400c2c0b40c80c4424000500000c6066001000041c000402c0380304d141c240500390012030385c0b00b0044800341c0104018008450252600d11550a4020300c000c202018400c4070b00d0b0042c03c080840119a00400e403a00010310420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791965224 1250 791963974 791964007
    0x10816140f0316141b0109050d0e03060c0a08010e280b011412010504050c041e0302151c1a06040b0301090b01020f100203040f02061603090b0403050c040e070f0902 72
    0x166102e2415018204184400011034401d00011204c039031458103158201107005c7d0041c050b21500402a552908103402020f05100000760986200307020f180009650400d0707243c1562a10205a60340c2ca81580c2084140682000c5c040c0ca02b2880c0d080e40c0e0b4002c60342007001d0b04003415000202e00041500d0314024005088084109070850450106010503c1610480c0000c14112841282c2c0440c40d5110f00074050354074825600025862a111854512440d80280d0a03400704c0348262070906c820350f400710300181d0f68001d0401e8501128075030403200440c00f48681002c0024822091210a903101103400101103600c40d0b0b0000602520100041042039100d00c580c1001000030300142041249140d58591150390401031207540503400301c045424420340c40100300c2000d6000c6d207030b9a5165100018110091890403003180045c070302c40c1020501003592007c1e101266400401020003096007000c1201906003008800003910428200251450b08800e81000420584500503038403002d101c142d0014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791966474 1250 791965224 791965261
    0x2f070512070e0c0a0c050f061b07030813031103040608060a060302070b01030f15140f0a06320406030804080c0114040b09040e0d020304050a080705010816140f03 71
    0x390003070141001803200d040a0141e21100c540c201607a940c1110605031030310000c407030000d04507201c2d259002d02030003000211a409200940c3c44540c809210080441c1b503449074802c021700141c515004101e82c07111040c80e000a00740b01e8203040c140e480c15894124555085540064008bd2420007444602e081c01c01400020701110300c0c00790f10707102154a4030a016601848002c2100c12858501c1c0203000550f95403080c89a514102400000d000c00c01e074100c102019241c0c80715200068001c1611a03200b8441d2404403039038030414030101c0000741c4404842400504001c1c40140314640d0b000d0321987c641c40b07030a001d54403455009440794104408030b40750900302c0d000c0394144206180c03000d031300d0040841610215091100c000e41d0340c920400100b000b80c403001c14000071070f02c6500f00b00d884450300400035005a46c0d00741c40c02a03525649152141e07407085284112404150008007080c01034144007280480c0b0700b103504000340d070058008440340c910f61004189143c0c5501c0441844280c594410b2103244 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791967724 1250 791966474 791966509
    0x46030c140a0b090319050f0c070f090b030f1e0a1209031403090d080c01022b0b1507080306121903030608240702010612120f0c0c05012f0705 62
    0x1c0c054408045c03000f0f5803191801c401800408224050301c4210501183c000180300c02c281c509940da074580c0e080f0814601d001d0003840f141045948096070030002042d29200003036030018243d9012000e0110980c1000309100c0344980201c1c1180c0012070412180c5840a030382695941d8051407841c1802880702c03148040070700300c43c0c0013045142c10943c0c0d240120000700d900245969a104100c2d110f6900a2142040100407100f0604103000000f003040e2a620034252030803030500919200c03100f040300608141c14070354030142d0f0030b00440c0040b810380740c0550740c00000a0720810040c00d21050307080c50940c409007107502410901d0348200030561f00d802400300400040b00240101070350442d131404d10b0b40d40c0f8141e0b48800843c05000903070f080d2007500002c0c001e2050100441505400d070070300041c0700e50150040000f00e03480c4480b50300c03128415011402901c0d00800d424a001e0304100c011543c041c05084c00c21031800309126284030300b54216021012806900b801003020303518007000c2c490004913000c94690b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791968974 1250 791967724 791967727
    0x9030f0607080c03190e010e07050a1a0c1531050606010c15020d090b09030403080d050c0909070c03030e061b030c040b04060246030c140a0b0903 64
    0x1d40c5540042030b0b80c1d00010f808160a4807542c82482c8681c1e105030f8004011a1141041c20100c00120194024030b4021800010f413083c0329103070000d0040828440c4200b101800350840c809240d0100e140203005c0c04800c84082d20f4010000e5660500700440c15125090005180325050345441c1070542205000c2d801e24204801e070031100d0300e60b5a00c668006200a040c003160720144c00030000c1007040c80c200c4051142c411034550071100006001004407140c1225000820b0340807501e154000400e460440e42e0092591b450802c0aca070543c03019010207014a006141c090003000c0da5a900c0d20412885604960742d04400c40115040c0241900e080f10040e0a89030440b800f4044044995203103c80019009a01155030f03843da00c2004038288a164400140040040703000715490b81d001c074044809050360669860200300115096400f4209544003c4454540c2103828081c0020640b200c80c22038080c3c28407492504081d100c803c00e0607403c4000078420b40020600004002c451225660011010340045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791970224 1250 791968974 791968981
    0x70305120f01050a090209130c050d050c0310231302070501050609010308090f1f0203042d03061a120607020118020303070605060a091407080c0c070605091206040809030f06 76
    0xc9089006004845c1e615400140c3c046140e211060480381e0004030b9881000341003000c803c000c009801910100800605000200e02102d1402007540c1c092303401a0300f12202d9078580390442009801d01032340f903131000505440301d043e2030f901c6c491a1202e54491100140e43e41d02185041401c50301c0040c0b41602c195001001800441d400c070085d40c4a80c00700b5030308003801c0008140040d03581800842c041c0e140c0e85c281183c01d1100c65010015202311640140300c41a4032083d0094220355882c070740f139100060550a84e041000c110290001c0100848112840004c4086900400d10b040c51040c081c0480c0e6004a06020b6035a50900c5544044905d403c1007204120541d400a6100e01c107008001e80302c6a140c101046859448070740410050005074810403902c3c0c001c15484c101e45c10100c03801400706200900048403103002c0021940080b04400c00f42824070304000c000d480c290481d10115401801c09030b15207071041c3c8200a542e000340e00590380e040d1540f50300700405117003426500c5601c3e0703c0d420010a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791971474 1250 791970224 791970229
    0x30905101a130f0509120304061a03031b070f030c090e07050303120403020714030d110c030a0f05060c040e2220030c03010c02030f07050f0102070305120f0105 70
    0x510080408100c0454078404203031554602180510003a5840200d82d150b21444030110fa02403035a8025914007405240e883c5100c007511944a0310700b510701d8107010400180029500c0d40300c2c1d011039034400d0346000c04a440c80042450b5400104901ea03014a03282d0f40718500c110100091402809035005682e0414110754500740501c02920800d80429295400300b0800708080c40004050040079007100d80720351358480b0f0919421001d507800d82c0540500071000c542e819401d010381e050080094014541070032841c2049840008290030707000305c0e0241e607100b02d100303503000d000c4d1004850040741d0210306c01320315040203414054060000d455040c1e08000802c50075984102050b40003280703081c1c4100c2001d544460020440002c90020082005c91041ca004100300d81d46105404006804607000b01140720700781030880341d12054000150707005102e00d014402200004200f4107208a00382c0784985800f4400c2426600408400c90100d4008504505500c0e008440b10b85d02c0980310200041c1c65140001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791972724 1250 791971474 791971483
    0x5070204020f040b070c03121d01110c030d1701090b0d02060c0705130501060215061c0203070f0806061003180204090305070209010e010824010b031b0a05071101030905 74
    0x5009000d01d030040b65400c05240302106490082c083d500d015070b991101c618050100041c0340c003041310780391041d45822000500c00c107842c0e09681046890581c0c084285001901c107100c0307800b840d58a61007000c202c250f95450500450303600b08083d07181c2c0c80c03240305a45540103103800144c012204891515074a88030b140d03901486810481e4041e10a030384d072600c9030740c1c005051203c42c4d004503030002e03075100f18020764070450b40c013041c100d45c480d500b0b4800340320669011240001d01944c00319400010a20f44004010140c1c4244d1001c40c4010102c540c00f90340ca101d018201010f60f400000b44d40c100c50100001410042d05604815030980380070403016405510005242a020070082e0141da41c48101c00304041c010011600f2941d002820b1115541e03461403014540f40c1d0034014031001d4024100c40c080e600e18900c0d2240031450410000ca10103a003030180322003007038200920142e03c1404106001c0c03da0a600310003404035007156a94a6a941a035041444841030618a01c6c3d04151910304400d010400109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791973974 1250 791972724 791972737
    0x7050d020d0303051b0708040e130f060b061608040305060c161104180c1e0b091201021c0605010e0d03050a0c020f030111072001080118091e0c08010b0105 68
    0x140002d16440f1034803494410703400c141e5131201d108400151b02c8240305c43c44025104480341c2c00c510700c1d030f603a68800d05034003106000f0100074010145504000000350b85a044a8500000a0300e064103243c03500420385031300c16015030309a401020029050003405000d0000962180e8008800d40c94950000840ba0387c4918066002c2d100c02c2000003900b02c0307a80d0b035802c5140c0c1c001b010310800814280c1c03400c01850841d5548151851541a48008210030011040940440b0750300885a400c200ca03c0050120030740300315807079007019542001090341008030b40806100c1650503000014680c0d0814002400c0c105010440c1482000310b440000c0010364000e0032a0302501030381c908080004075a10114450905441e071081e419420102c2c103000c60001d45000e06071b400e0040320058800e2100d003030061a0380c600c6549084c00150203000500440040b4040c2012460741294000b0b0380c05038a03101d00041e94600908240003c00100440c1c0c14000300101a00141020f20002c2050380504030000e0001d00c18039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791975224 1250 791973974 791973977
    0x50103031b060902220506010206090a0609060b091315020f04090b150a03150902040609030f0f08030c12181c050c07140102070608060102100f092307050d020d03 71
    0x40c85071000c10a06820a08038507902810078202643c610400300341204041c0c0d801d080941c50100040c80541c400100c0500034038a410280405540d640c40312000791031501c0040e40e0f0152610104d26080e145c04100c184072b00d13003c66866100400320300e000841b20811441034546035006102e01c200340c54115044504680e41380b02c0c0014040d20302404101a880a040864088400842c54029943e0036820030f4420ba040d41000344a050f03103400e5a4001c034050750080e20001a415141400016980031b015007405016090b8402c3d108865614240700c0c5d40200e0314008950808600506c0c01c503200040701d6040032440034050400f0215001c4141c0d2140c60340422200c075000101d070308034801c5c0681d08569040000303030291030041e52070b814114a603081d40080a0700500c109540003841a115807882d40c0280713030580c003402c41503410780d50f090050802507241501241d607889030000001c500200782e550100400b01c901014580c4080c4540c24008198019809407013441c2409005036108e0500300e1030395905 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791976474 1250 791975224 791975267
    0x5031c0209031920031f051b04030c0608090708030f120f1603050c0f0315030c0108090d0f0e220510060903020d140d180b0a0c330501081005010303 65
    0x5480003078580700c03021b42c1503c0c07491840c3c901710005080c41c4c0c100b244200020001402c81d06031904860069110741d2002419203100c00c0c0c01404039500c21085940c01c4482107040303460803a264014582103a20071107076807181784030000b800e0340b0118003155403076407000c07252118003181e20300445101c0804080000c3c00003015500c000150565a43e58145c03808002069980c94807850314562108030b002003410360b103210b84501c0d00300e00400d600c144256449541014094025a07001403810ba40040c4411080800d00c002c00d500074034280c5440c280000740641845a100c440c490040043c021a03101401c2c03004244102642400901d0704805280100c0e94141c54030740010149080458109014001c080d0442c00344000f11700c00294030048000030307010f05d5904c280d1a5580d400790182548152150180452040108100401c54440d0161400a4000306020b0140210000c1148002511102c00d141681c3d8100500107148100311005580c1410321041000d541151170180c1822020000e101d0040c00d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791977724 1250 791976474 791976533
    0xc010624030e160f050405010801020a02030a08060a0b0316140405030a0b180a0c031202031801050c10061203020708060c0f0304081c0b01020c101b05031c02090319 72
    0x1003c0100c030000103441800809515100c8241406060b410712410b44158140000451552418800c4900010003034000394904000746005490b400300060106030f004008400000310b40d20080000c52140c03106000d001d00509803114082c02a0b00e280c103549c46038860622042c022900c00003075880702180c00c80030010550340d81651648015410702c20390961401600140010002025a03c00035644111451200d149241ea012a90b0740070f03440e03aa40d02441c0024401290703501400c01820003040c1d0f172094680202004c0b5505007502c0d45e6a000c0451910629211000c0c95030500204010703200e0390001d04283c0c1400c1c452080300c0e01a56a1120611100001189c10414141c04548180c0c1d5a115504850440d20161340000c240c2d0b000d215000d4001c2444c41c1030b551030020141c803802c074500d40781c900c40120355140304184005210401c40b4503101c1080340203004290078440c40101400348a001d85d0b180c480c00d0034113080c042075040d048028036000c407a44c0e00152081805c10341c0f08070f5000d000c2001300c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791978974 1250 791977724 791977751
    0x12070614161d1c0506061302030603070e040f0204090b091219050903030d0504081c02030402090109180203070b04060f09080a120302090603040308010906050d1e1b08030c01062403 79
    0x83c0c05010001101c1001e0740400100803002c101e541c4190300403a4600400e40e4050684810ba1204071200f5a05402200c41485007104201c0000e812a014543d0901e824915038040340465098007010b4a007807031500c04004e0419805c100040c024480019014146006041100e903802e551044443c148000862840d00c5900c04105954600001a2060169061034108144e80f035100640070b02c0246181c40001c03508401070b0085a00413075004d13000c003090317030b00e003800c400014400b640b1042c034103002e074100d040050b90381005140003400c010000ca27903a540c41c000c2e0240c07620210300b6010b0148480040c00f00b1000c000440c8110849070049030300c5024020f103030b178200d00a00ca03003506198003048c0071052100b8141d022078028140d8001c40010000151960304100800016a500a1940039140105a00c00c4508074250740e813903100e244000109000600003115491140d0801c1a095202082d0754030410002d0107210001d0195490440580514083c201502a038201a0000b455183e102080c1c415 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791980224 1250 791978974 791978989
    0x12040b040503070c140f0a030213240f15020703020108041b09021917271002120901060501030c120e0708100f050906012612070614161d 60
    0xf030b03030000720020656102d0aa44030345c090b945649078044c41c90a144c41c81e0ba400d190443c80e094a400520b510408501580c104020700f443c10050741441c41201f0300024690110100c103409000048003004900c2e003001c03001c5000c000d80720000d10466104690410140c4d03041509035030040d80000c10060741240d2000010f4000346039a00c070f43d038030a200003250100075041702d20000a0581641d1070b0560036a400300d11205841050302d0800406580c1c00d02c41c2000900b00c08101c00510031a425510b156004c40442006ca03040261003800e128010002c010410b4030a102d0309016103001d003400c22694640380002070249042c41c9500540507690680c02a0451040050ba0004c000403803c0347d020b900c202c0303800030141c090803081801807420b14000c180400d1003c43d509059880958002c0e04104200301c8004c0b00781186c040615a5010702d11400c600c0d81100c4005004032806081c3c041105c185007105901c90302c00007480d0038500050014021441039100f007001c110740e04100d0020190101000011700700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791981474 1250 791980224 791980237
    0x291005091e0310110d0e120309060105011b05030414060712180e060d0f150504030c110108062112040306060e06091504180f0506060a06030212040b040503 68
    0x6254803020076256075649808000c0746400d40c15240f40840d101a4081035034010b05007110070810174001041e494046602c540c4409885000300d658001c00444480c1040d0700a41d403d0086030028401400035580060410003440ea0030314110548000b0f64480c0742d00e900940c0070322001c0500041040c0103540d40c80007518061900301840c030104140c1703480d02508941d071024820800e02224080040c80041c0d03140f42d18070a03000940741501e075036403980e04c0c5148402400b81c03c680590359800c0e40880c0900034820207104901c42e40300e61254030914203001c0e2103042c20070802410000c41d00d00f0800951a5440c86049500407920b030780c141c0062614699041c1180d000c1007002002001c1400020300016800075070807910903841e405203580706c4a0900416000c00c50b0b041242d0307590107a51030307406d0403e40d00c10980b0403e02c044208051700580d81d0036a01a40500c0250781903801441803000038500b20010328000e1420f820f0440c5402002c05023040c81c100010b01c0034226011020024040c000240700700c1d40fa = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791982724 1250 791981474 791981479
    0x170609150402190201052a131d01030501110304030203161106071a0708070c120e06030a1d060613180803070c0506090303131b15090929100509 63
    0x40f107400502c000300c500c000c00300f001d20043d0f003000c01207034944c400405c3e14100e0651020072401210900501118103a005064001211301448000110203410076080304500c0d081c079004101c03e51450816909503140380c0032002d8014410428803001a4000040320004080d080400001c80400d06101d0340346100403500e070f0b800080005a5000304012001691915007410703143c4001621085c100b01c0710940304881c0708011607902e2b01c0c1e40c80410110444d862002c8000d01d01860100860404501150025501d03807280c1500c1e4184107007012200885404444401001041306180c07800015030501d5039003101c0640c40340c2d43c60300c1504883c0341c1300003011080d2b0006105035885c100204002d009035102c030003e890b02c0c0181c01c0414800c0c00040f08036801010075190b9140b4504082e02c407040100320070b4500551800c00c2c18800210390b115600300c0016512251280306003075140030045400c1e540040070840684206102c030440c40d0440ca02e018101420685020303c56800707541d0251140c0c42078110042c0e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791983974 1250 791982724 791982727
    0x604050c09041a04020a03022a0606330325080c0f13030309051c233c0a1203050408040902040806010918050a0303270804060f170609150402 62
    0x103030071ba030b095001401400b410b58003103c10501101403404451a0301c02d91f10601c0e03003115020a80900c0c101d401c102120038203524104103107035800003800c0030f00f6056031141401c040200c00c01c03002d40b25401704206c6142002d103041030030b005c0d5154010a5040010000e400c843c002007480556111010207491b240280603051400301303522810003030314140a170702c11544076601884420600b40e0292000600c450341c0046e40c0c00c0342e440002c140c8202c0d420009600440d03440f44614508600550045800d845290800301e803803c0c1d40d030000c07005502c0303880c289810020751180d250000054031a4030701d00c102c040107240004250703c4601e0002001e104035070003d24600e00100c1c3c0070030f0142d40880c0081c125540140c0800580050168140340e503820860003808507040b1030a1600483c1c025040040c4e620039103170504403016013481244000c0700d2059029210007101150510080e238004010703000102d410b0034002d10000c881c942711085007400a0115000d90450302c046000c0d148403550100102c2070003801507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791985224 1250 791983974 791983987
    0x5010f050d1505030f0f03040b07020d05060a150518040f0501021b150105181306021c060906060507120f0e0d11040510080d0809191a0604050c09041a0402 68
    0x1c8402079203c0c000c051190003500000140c83d00d00150310014041c0c140302450a16140100d070312066000180142c0e00009442080c06c0007460034803529100b41c103011000100740005c0f81519041d1a03164020034060320102034001d048480748401c0c0c0381d01c16480803040c2d26540302c52504070301a0003080d00074000c800071005282295000130400e5049201c5400c16100b10342e0343c07030007009074007010903000d01940c081c040d010810f074240116601c49482c2c06000d0261400b42c0c19410310030040807440c12541c645988241c00d10011846001c5c8000404641ca4840d08285058889c0400c0c102d00b00c0c000014020305681822945c1c0c092a4103e802c104000c142601644007418000c90201c2c4400b030491050786480e000074040a00207000310207441da40002072a542003050025034200350050b000f14194812a540d0503c49180085000c0220b4031030a110560030002e2281d80307002103006801e07544140c2c1008100041a20080c0503500700c01c1044801081200ea000810003d402541c102944c03c5030001480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791986474 1250 791985224 791985251
    0xc030606080607020f1204170a022107080c031f0b0306010b19030608030d020c07091a090a0203041e02180114131a061b010e1c0201051005010f050d 65
    0x20910034a0f283d026a000d41a0042c5036503103910803035036800d2401c1070910040c840a103800159803003802d0000c04407001c5840d0380d000100442c1b00614840b45940c400300f24040340090600040004110380300c0145480e2407450006500c5100000d444140300070000d414405100703d6400401050a002d81526420b50b1210110031841e8007100d103074050310303403a20510a0b032640710341314500440346020091400c0c00a208a03001c0030750f201c030346e040065101d4240301041c0816903200d4860503041c03070f4500302c01daa5900000d0058402000f008040c40a106000704001309a501e0144140c80e40036080084910242c0d00c001109031990690f01605411004004030328640782c064401e0a40d242124044140c001503c13480d0180d0b070b92032045001d40300c3c40000741c00841c28560040c010300f9400b01415482610120529401c40ea404134a1f0740c1552b10031403510148181c3da42050204000341d200038022454403a400c206480e10b0b9200743d41c104080d11040c14000c0388101c065a02400e02c440081c007500071507520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791987724 1250 791986474 791986483
    0x10c0e030a122712140a0b1b130906030b0c070804032d0b0106110a050307080c030f0f19050708180303221401020d091202041d15010e0c0708070c03060608 68
    0x142110403817506102d40066950000c1e122010700c2d4458011071403591004503a0040c0a00e410700121458014005a900520b100041101400e000700000982920b103041c5545450805000158007140070030254001c1a104012141900d070485e842c0b0244025040c50403010a1440080d08a0403840c244410204003e4900e624120342d0039644200f2414418030602e0786510740c0402c001c00c91390080040c00b001500780c001501c4034201c00300c01e40703040c80400804810140c3c04000c6141441e2800101d011844050350000000f1381d0742443c000b07040103000d0351a000140b182c11091b44922180140b0030010303541c03c10884015000c0401120304089400d03154101c2210540980c01e4402140c544c0000c09510026402d0802502e5665208081c1c1c6040d8158215071107052003a0380054980f00d48580031070a10b9442c50582a942c401890220020b0501d907080c01e0f41a0483c03404c081401c17003805624a1040155180240c200000303ea40700490b282800303041c080c07030f03100405407401d044000450750004134 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791988974 1250 791987724 791987759
    0xc090109020c010c080c0904050901091211060a050c0d090c032f030c0d0b04053a030c02030301050105210a0b090a02030105030a080904020c0609010c0e030a1227 71
    0x82c02030154000c0300070142c034010001c07031340d200800c501800b4691440c9855044103400401d01c03400003408903442c0e140d0040b11800c01c2d615201140b4076440520011304100002503000c3c4840700d00304040c1c2403180b0082581e110380c42c0f00340d04840c1c403500c250050104118014000b0341d400b2075400030700342e4004144980c2e000b2a40343c0a0480c400802000038504000c1380920070a10010844c0c0008091580d0f42880d01601800035a950320505003480c0681c401d8a0030610070070a000c0c007100c208030105031414040035440c4d06080425042924a080e065000000c0e40d040d64024244952074008413040b4540210003104041664400c3c0418803030b1aa0711030303000061800040e94800010341d502c0c4041810f0340700a100d0140c056014840007008109207d000c2d00c0c44417170040c0050b00e4452110030844c6010f600380c070100f00b9030b59188640b00c100364100c150006150000e80203132422802681703e010b1070340c44454150041c4501001e902da101d0b48202e070b440543c0c0501d071080501598441c1400c035009039004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791990224 1250 791988974 791988997
    0x15020f16140604050f060307050715050f01120c061d030a0f020103061a070609060209030f010608100e100504030309290a0912030b010509030a0807200a06110c09010902 74
    0x140c00c40c107402c080301198103540c0050240c40104103040305102c070580c4001d113500c0401105111940000d00c200c0301003c078604d07010401140d14244500b51000e40c0d001a440b07852849203c1808000249406812008540b00f5003003400000c80c41d46440101134400b490a19272600552441c101040001c070803d124180c002ea90801a950f05c0300b402c1c27208503007500d1000305102c2c4280100d400040507a00102c10080c4a00005410100d9810120345404a642001403a5035140c110600043c4400c0210000b940500003080c850805e0380c0c00a2912000715248510342a91181c0010b001d0600903082000ea090380402e071003a02501c401c418541560030280021403251041c004580c1c80c014600400f09107682100000c1d20302251040243c00900400e9030003410300c4402d0010901c1540c00340040115503000710501c0e0781d00e4031189050360071a51584400082c1d1054404801c02c16100d00c1e00c0481903420034108403a1500c2c80801191401c4242c1c0310701a405401400081044010340e00130f44025102c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791991474 1250 791990224 791990249
    0x23031f0f0506060406090e3103020606041a09060a050a08030a0f09061215031707060e010e07050607051002030c07031d0312091503010e090d020105040c15020f16 71
    0x80b50b0801c0035601c1a449020000340d5040c0c03050124160840c0b20f6500410340e100c414628260184c0000d081141480445501c400d030040350358180b40d01440103036400390b41180c007040140f440040c140b10f800c4030040b0150103001290002119034850700031002c083c0500400c3d0000c030380c5d654003955640350f01620032000000c2c2d800000e20496030103510300310305440d840d0b101c0d5a061200580050000c0000302c50030445402c1086000010071080034403840520799001c10243d4680644c10040b054540100090741d0716032420450a101030f40214000090304c0b811149141d07240201c3c102580351450000403480114800004c4c41801a0f0b6003004050040c800c1d228280d0340035084207a11074031890740720f500340c00d50460060b0303005002041005200b0490b004213003c800d190080750030211504260080503458010a09211140c0c00030042d240b81012948002c0c0b00e989842c0e501c40e40303034040a1080484038004003114040450090001c1500790300d00c1e00444101070002c036100c0011072007502c648a198000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791992724 1250 791991474 791991481
    0x60906150e06030d12020904060b04090605010503010506031828030f0c0c05060a020114010f0302210304090908090306070f0801080d05030c0a090b07030801140103050123031f0f05 79
    0x100041d80b8403440c030040c0941515040c905003a0740f8000d0700c0d1414140507908001d460320680c1e0741d1042101900003840015241ca080c003800c13004171940b9800507418840140010041d50381c4100c1182e90084541c00050071545080c07070505c1ca004111040b84001c0c004c040e08002081d062040040c200501a40e502c5149880d0100f00751800e044200025004058130b036010b0240d400c058000341465401880001010144a011240c6d0000203800c03004090081c428100158a0554034404011700350340ba140c03500c0c0081c0c80c026a85c238440c0388181030005440d042401e00384000310040c0c072043c16016041d182580b406580007000d000c900070400d0b002c0380350a4004100315000198a4514900b15102c0c2482d540710840040500d401114480041103800100895841c01c40c8004d0440b4034426119203195504003d10f07428804000b988190401d40b50000400816054540d5240b4a2200c04802d1401012402c0403a041034160103841d1840c1c240c100358040d00c0b6505600080c03901c506100304001c143c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791993974 1250 791992724 791992739
    0xf080702030c011b0b0402130c030b0901050a05011e09120305120f06010c0308040f0602042c040f0609060e01180606050409050309090c28180302060315030a06090615 73
    0x31303440e0403180500204c3c520307030100044503401143d0300a4002011400c400002d0050b0a0030703202441c004500198450303805c100c07075040c008410350140000b200c000c40102c3c01c140c0000c0c580c031a005c0c042528503004290311141c09005290070750290440300382b107400141700390078050700540c0004444401580d500000610001440d00d04a0152105030b6840034280b6664804982c00f1402500944030034910703288001c00291079100500042c00c2013108004004419030281c0411240020a9405e9a0841c810480015413881d1030750070f40396002072f00040711041c6050075001001380c1c0184002941ca0115058031080782042e101922074801e47c8248500b070340325828041070b40c80c1d6010040c942e91040c1300c0c900c19458880c18181d8082d0202c55418240968034142081381d580039007624134401881842c4200d07032a480498900040c0c04011034514803441c581c04a00282300c010310800c0301104842c4000c42c0b0399014000054526084031081c026824241484002404401801f0303a90340b400030400110702 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791995224 1250 791993974 791993987
    0x4090c0501300c14070b0907081f020c190305031803040b0f03045607031d0a150b030706050706051005061b0c06130306020c0a0f080702030c01 63
    0x10200c2550300410140c102418802074030312951040f00740038010341018001d0180034003402c1c0c42401920003503400c0c10481c47d400d0034030300c09070880c3c0300d2500300701c0d0100d01100c0162812209400c0d0483c00581d14007001052500341804400004803032100f1014030b909244d405400f960140c0311100a100020201c2c4a10564038401d52288260402080c001400049580009991b005000b1b104400a070f130007140c6480601c480d685e4010303074500980c1034880b0014811980034184030088440c82ca4050711504a40c603103080300100303082c0030503072580020f0b81e429089041000075181c40600311607081c907081c600008074000b0000802c1503986029915802443c2c0020030303104450303031170700c85902d4201a52260310242200401800c1043c410010000b1103407142001002200095088002c050350241c110a040c4a02d807805d4a100354000d00c0b0100d010751a2100d0401100d500900044e0388940165165080c10f42d440409070882c440c3c0300d4082c0078000140e0050840c103200b03c040e80c19092000d4010f4850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791996474 1250 791995224 791995277
    0x1f0b03010209010c0b04060207050604120f0c0f14120a031b02070b0a120b0603130b010906050f01050c0c060715050109052202030703021026062b0204090c0501 70
    0x12445a014000b00700345c1006190000e00444026151000507214285424829a003c4800001041003240c14550280100e880000180b0700390701300d1482600c42042c981d05641e8007030100500c80c000140100000c200f0070703140001c0c1c3d11200d40c549080070000b0f802080711410407042038800d80389501540d840030030303c5010349001c0c00759641001c603178a10444601c00c07c01c850101da25583d006120840c2c0d20039015600c02c400b40104000600c0181c6841404020103034040b04003d1305241007404240d5886d586040e0001c020310302a61204e54021381e1030307d495900300049400100004000c0180440c21540b00b5907070400304420311003640d031455003c1c115401298407041142c524040e1241c910000e2883d8100780d80004d003150700c910f88a0300003a41c45c100c08500d1030082011148002c03040105d902941c6082401c040400f00286009404a0030125100c08502d05d0004107a00701903910070444030341a401c0ea0003800c10009800c0b1031900c07906c2000345018180c0400c0b403490340e006076204d1a4450520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791997724 1250 791996474 791996477
    0x1e07080f0d02030a26100311041a060a0314040c0806070f020325051005060a090902030c0105070c030b041b0b071106090114030a050103230d1d031f0b0301020901 71
    0x20308141c94204450756a9800030b440da407001c0e02119a24000b128040c0c03180242d850781041b0070082d1840c68250101a884019035000c0c0b428018032403599010010051100a41a100c03903641d00e807502c00490080108800003038403519201305220a03c2103552880c8140d595004c1107450a03180c962050b200c0c00015006003006901c2040b8844c12080d5422340f0203969090403225145200096848600740442c0c2d14070500560350780c40c20003625241040e4400c1c01004111420401c00980e5000f1944451820b09502d0510200258100c200240b2070704080096800c0841c0501c2414a0324101c180c1540207014000d240f84100b4020541d00044801c64122552241040750700031144021301200e03800407400f082c140550748003070003101ca044000642c4581c01c9007c0008596065284c141844008101c4000107000c2c1100107012000c000a45c0300c031500302c1e5080100f03001003882904020110070024441c1c05000b0b9103000c0c0090140018800300e641d440ca002805008240d009041c205e01510b14a81d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791998974 1250 791997724 791997727
    0xe120705010e041b0806040c090b0d1d0a060203100e070f08091e0a0b0901021606050919030f0f050c1b030703020a15080c0909040803091e07080f0d0203 67
    0x8019801005080102c960240c030101c4c480c01c41e85401c803e18030701d00c07a080c0003003884401000200d150612505001d0070040c104281c0d0709041101340c40e0740e030091400c0c0403105565442c14044980c00c803400481100305010440351351aa480c580003002c1c1d00203036039140e404c1c101200040b402c405003501c52071007628540d803480c0380344031f50b03d50494560700c001d014448680107951a60444010782c000d40210505140020559581e40c0d18004034034600c0106401c074641d10502030446064280414401c16a03002600801d041c0c456010403824030900a00c03881110803000c031a1b50400d85c121060340c15038030158079030f17003401040301c10300ba501885074000d40c91003038002200d4108440304122055100d03040240448031103d40f249d012600408150300403800a0344c090b0140c10110340e0110103260f000340c8103010fa038148a4840086031050001410080c0315080100000f10000300402000c0c00826803414407641490200810a880341c440380140300e49805207056030305410100080c0f038ad409004560040d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 792000224 1250 791998974 791998979
    0x52406090114070f02100905030708120f1b010f0f1a03030901180e0705030103140a0515040f0f08041703070c0512070306020c0d1e0f0e011106010e070e1207 69
    0x19890f5002034421103100480f5542d4801588514080c6860618141c5a10581c64209400c161410701c10343c6c000c90a0703038000000301903480800340075100f800a040309859210141c3c0c811003078022400c4400841250300e05600d441060300560003241101501030010004034100301000500c040611581036010350007009410301035442011482c100b04d504a5031170041580350120b40303030382e41c50513640030300000c1c4040010300506c09119040c107880420b21000305052155a60b03035039201d41100382c1c0340d54080070000004090140000700e14401551003408110300351145d28003d070030f50300b10b4020610482000c09079409005800000c9403074a94119190322005c0349083c04010b41c9040101c44408203006100001002070f00c1800601052858040680400101164010040d0503800c403107800030000313000303060782c071540214400e1903c90300c510b82480c980308202e0040c1d4109800e100109114400c0c50000a94048408035584c0030f200035941c3c0e1440003810804205070403040d45000b003120340000604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 792001474 1250 792000224 792000257
    0xe0603040b06130f020c061008071202190801050a0e0d02070b09040e030702220b0a270e0d0201051f030b07110a0c090e070902180d14010524060901 65
    0x480e40340c0030f03401c004107015030f41c0c0950b0b00a98201c00346010490340440c0910503100507020340320025000c1038009200031807901d5540180280c0c00c41000c0d0045040388400c0c684803500403108006003062200038042800e010329000b0040c10410140305641c019810038500031b0f803000c5000300031550501519424883c04008201c020100f420b0100703100d200070006900162115140d041004a00301807404c3d50a04090094080e1000f400300d061090032042d805102c029502c035000d15400b0078041d00184080c02d66241e031401856240480b40c02c0744200300e0110181359054000901c03e084040f01c0ca0500102144403801c07102240c00000d04055071680010015407144600000c1c0d800d4040c21165100d00e151a00801c58907943c20606100b40c0700d144000c007164081011900812100000f1840c10501014008040e9249070700603200c0c0001c0c540180902901120b802841d0200c40d00821480c1004080d0400c003c0d0002003030312010b8044001d2040c1c9181500a5510108068407460001484e00c2c89 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 792002724 1250 792001474 792001489
    0x120c020d090303051828120f030302030403020a0c0b04060318020d0f080f1209010b0121110903011a01110a1e1e030f0e040e07050d081e0702010e0603040b06 69
    0x1e00000c191440b106145c81c0d512080081e00b21440c8085490079003041e0240d40d001d20390207070810b82c61300360f080404100283c0307501d904c660013a0b01450010b03140c0d1901e20b8102c1c204002000301a2940200c51004117811612074010011220103840c10440c082040340408100088000041d5115541c69000c0c00850a141c01e00a440ba1048030030300e290101030424060990048588140c80c03050003401c018210381c0c244140d2031054400d092a160741b0041c03820341c3c2d4807a840100000c4003152504146100c880b020810380e5070340c4400030f00a02a800c0c501034100030f007051a181c65800182e50b09a1590301880200e0710b17891749504881f0b24054005507200035609007260070412518154101449900707040c030b034004030403258481e58640d104500c881038002e102c2f400c02d880083c0b2a03407410032000054075000038000103c68003500c040c5041c0c03240b070070b102c2d0081c01501110300341c40c03e540030102035013005c100052100e68402d8a90819103200403060000034001103078018210303008400400c9691a2051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 792003974 1250 792002724 792002737
    0x9130b03070504020325030603020a05032d030403060e100b060a14031801151806080307060e01090b10031703222310050c09031906020910120c020d09030305 69
    0x44940450034a10b01b030203040307151b04450081c00244c2d41c0d031041c011850b090200d0740c000c110890051540c05c6000748644000c0b06c100ea800a0113071040340e54100402c0e001d10568006541219081050428014115444040b84040e651402d40b800342c64140a24003d410b40c2c41e26007290360741c00b00301030032005207100a038000341100020b00c5070040e03d00c010343c0f03090003010400b4180102c000200e9281c0384c4826180e002401c040c808060a100082c0003054002041e116841e41102c4080303205c05a4030501801000000700250051804d40304000c1c8041c4140d42c1709003164880d0307030224003503214038a04e9000ca01082d03420842c0078030b941c07010070990b51601829403041402500b900000700d402605840400c0348071040350031719400c03c00c40e80c1d001000c1031040561060900351091320b0304120304002a2513002500312416200100038040043c0300b22641075851654000e0074282041c1680440a404003c0f1818904595820511401c0900d44080348034205140c2d151502030f281ea0a542e0140e62642018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 792005224 1250 792003974 792003991
    0x41b06021c020721060f020a1b060b04052a310906080d0206061807080a0b090c090405060a030c050d0302010908040915090e0a0f1407030809130b030705040203 70
    0x102089848035603881c20b4460f240180100c4c0100114500034050302ca03401c5640030b10b988140300021076150011916035a84141189400703075203641d80380c00002032007a8a4003d810030310740340400403060040007046510141d041043c44c0c0d58401e44441d48506e210f5404d101c9100d80d2840d8402d074070051410943c10403002800e640303103611034803040070700c08584032136025041640c40a00082c0f134035501403002c150440350603140d4211a0f101c055074091500e030064100d0080161030070008071401305c00d40c80384030350640041011a81e410320010a10880d0450103500d842149805d0104c4c0311858400148811207900515000e022864101041140099800160155503c500c0904e00041c1c4540042c0042c0440040c002113004070810039a502514a401c1180c00b14a0301e1144078681400154942e03405900c160034142e85003481c0751203802020440785a032034520400d032011040050a0b8003411055000380c03402d00500c0d0b0303150501070a45030765840c05501600b20f40018081410140c0045a004492 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 792006474 1250 792005224 792005233
    0x810090b13081204081e0a1106010806010e06061611041d0703061d0114010806010e2e0e072007030f06020a02030c061006020105010905060906040b040f020f03041b06021c02 76
    0x4071020901c189001407a46c4c201154005810b103410384d0445440040300c01444002e100075814000c1180d690b80e418013503840c00c034240340002003041e0b031600100c4111300107910300d5180c1440c00349042c1400b501444a03c61045052009240840c0c071030700f50b04c0500c0d820308801001c005103546c030764400500c4d080300c081d0301c841c40501c0d000100000034022114910408506800c01d503140409140c10140180c1150340841c01c98018000d00c2d01c0740001c82204118204070041c0b582e403149200d012030b61101d41c8000d903500c9a071000c0081054002030301040400e02e092003058005032100d0301c95290241400001d1921024401d40070209266a01a0800b0512801185e280900066019160140459030106100c026403400c0c0b040c90b0382070090600400f00d260b0709020a0900d41c2c0007440e1840d00900340c0340500d56500c3c0a50066855805c10b1a0781220131401f10740d260214242d21000c0d90046034140c0c1c0003810007100c1c0b0020f04006450700220382ea02d03805411946181c407151190241900d250004600c01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 792007724 1250 792006474 792006487
    0x108070201060b070516050415210f080d0608030903070618080106030b04030e061e030604060f081b100807230f030a0c08010803090d03090810090b1308120408 70
    0x200b81d401080e6040c05017004000b030018144a006030348079960440c1d4000c0d4184140c0d4041401c50b0030200061b110100e5507009614844c500b20040503000d200c019000c1069546403005105038000105a08019060180040c0d9250b40c452960784c840e00001c0c0ba09644806010800b09125040040b03202c41c4084200d410b60b5519114982516072039041501c2c410510002d00c02003503000b284010207001c0503100b80d424040c1e124110680451645028181810000005250381da41d40e80b2800242051031400c203402d6032a510100d9035a504005241d060040303ca5049140d46802d4840b00340c80c102c583d036240401e5561076021030300489408140000041d80c200022080b00143d0040c00e0445a1141d00c5e0b9128584028240183c3e24028503040a008081c00103202581021003212400c45055504a8204e160b42c036045604854552241000340030355100f0031300702040c82c1c100b40b9507a80248040c0c3c0c044d07294000d01030560b00c40c1240081174080e0800c0043e006032a10b202e0142d100e4003520300c3d5402c00c138 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 792008974 1250 792007724 792007739
    0x90b060702040908030921030a2307091d010f050f15030106120609091a0c070c150807090605042c15040518060c07020f100f02150c0702010807020106 66
    0x218003c1e000c4070288400310811a856500b04003018446050b907001034903040005068404900c405418820b81a450700c900003909551584540060740056115002034503115600510803001c5024205001081c1c0000c070003040c1c40909118180ca1000090380641c0b0310b0310003080710011f151310f070140d00070020f1403260b0180e09a11003d18000c108644560441614600d0b4013012520560040c076115454803103003d002c60b40c82e600c0b0803e1a550318400d044c0b20345917002c004415010b052002801030102d40c0c6d0104014440400ca140d54107415142c00f410358603202415a800080d5026820018006120400290103028000a0040d51008605180c0843c84000003014141190070002e48008422000602d00302407041980c40b02c0320345101540c420808140c00d40303c000140040140c07260101d411001d40d41c03920b45075039502200510f44007d451886078003401c1c1520031001c900250068440c00c001040c80c2006562103070100303581c05031a180c0554010340346042c003e4030410440d0744e141c00114529 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 792010224 1250 792008974 792008981
    0x60702211f05060103050a061809380c03061c080f041401020c06090102030a030f020904090f11010327060b1302131401081305010b1903020111070f090b06070204 71
    0xe581d10700c002c21985071550014040d5000604501011841c1110402200340385a4001c604c240c800b09000c0350044040c2880710700040a410703007840300946894003062a214454001600d445001130321142c2c0e81e100c96215655000481703083d80c102018048031840c0360452203101446034800e102c0c01d03041101b121019901c0ba002034100001281e145200f1010568040148492084c0201d680f02e240c02e00c1326000030340f00c0c0100f0180b038040c180c9071b01c40394a44a0080d010340d105100d000c2d2041007103081b00c0c144210700010220301514440130f4990042c0142d4800d01400c0d0702400260321800f00c15406040c030800f210b01c60001a540b2542c0c0319042045580c0307101c03000305e4411100a000d41c03149800d02c0500c5030b10341e00750303c5084034024480c0846078990b000051694010b0702c0040e84c031040d80711410240e000d09260180e1075800103071a403180383e0f10441541d421099034000c1e40c0c0e5400482c410b00500c1d83e0380d6150301170305040180b0240e00700800c406d540c00c40c0c0b800c0c040c09014030f4140146680401d050303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 792011474 1250 792010224 792010273
    0x316080d0c030b2e0509010e040207050c1306030206072a0b133507030618060e03091509042003070e01321209070305010b06070221 58
    0xd03281c2e0105a418501104c3d1305440082da220782d2105220024540d8403030220000103035051041c0826120340c82d0b0702544a0b0202c8003000b0300103643c0d94030300d840c000b81c8480074a05035520034000b060042080307802900c15442640c0c2d02410481c40d00840e9110180c41e8001d1583c0b48082c0340c0d0883d0076400c0c000400a40030018442035068a481c0c104e07803040400803002540210804501c10b003004420302d0203403081e424090094040bd19018810100c030075040c0001900081c0c0f03000e0810300c80260004400c0d412804080c001c0600700510032040400507224480c48486503449030184c1c09100708010307200020030300c4d0000144001028804111484103e07104e0070700074880d1036004420040c907141c00484540400409103050145046c01d110301240e02c40840d0b142461200e101900001c0c2c0a40c803200b1518809081d400842161a0851031282e440d00b003400700711025400e0806c0081181020b40981e003146500421807807801720400d0a41c080d501d2030100c805490310601c1c0200c0c40056407611301803074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 792012724 1250 792011474 792011477
    0x16050f010506121902060306120f0703050d030501060c0b1f1d07020a0203100e1608010b01030b03011514041410030b0919060c0315060306140a080316080d0c 69
    0x41d07515090041291908003c01c0594a03030300710040c2107a100c1c51000420340383c0c81d41122000d031285c890a01246041c1054a00c24801d0b10500e10302d03c0e0301d614001050022640710b4070444151000001c01107055420078807039000410240c143e00400283c10100751342c0d001072410756901d0403002d9025044500e450381d07445400841d00540c0040854040103103400d9002c83c6a00042c40c0301c03100d40e0701003903807446191481d440d51991015903920342901070184441d2428038108038100c140d103911481e8000c150321084079001c079203851003070086400c0600810700b00c07070f48080c0b10460311071601806416030003246c802503074415a2451100d48907401b01420f24050000c020a140d4000d045241c4442850005003580c9010382c005d151001030111040c0480074925803100300407072a15900c48083d0050b01ca8244610141007103036502081c5c0551591081341201c20030020000c0314540d00c408e0080079941c40c05407166541041007810700e9180201c0c400f8030024400c5407000d01d45804841c4920490b21060f203042d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 792013974 1250 792012724 792012731
    0x11d130212060f0d0318120b0702151605310305120f27090a0c12090f0204181709122d150901020306030106240516050f01 54
    0x380302103680210301c1d40c4400107031400081e00103a0000100702d0840144000c081042c004903580c030b01c43c0701c190090014401c08111070724407002450044145001110040b00500c54030920f6070030600d1512209000d00010301140c4041c403070707031002111154440c0c1d110310812941c0819084500002c001c000011361340501c0d42d18480381c11841c00e10705200b000720305d042561a00b0300884020a1320030701115091424903548a205040312a10150501d030796002056101454400b0040e44032940d0300840d43d020a10343e1071480881c45c1c000070004a0b8020381c0040c01350000300300380c00014101035008804504151a090550386032541d114100414005041c00c194840890b4a0006003884c0c0340c010a800540000f4121a50498144210703404108014100b02d9180c8021450b084500703009080481e42002c0b1203001d145401711a05d4003070340c425030700300c2c0c041e40c600100007404059044000008541240b03005c03202c20041c80301110386410080400d15049012920a030000fa001c020003075081c0c20207000171 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 792015224 1250 792013974 792013987
    0x121e0f0d0804030e01030b12011b110d2f030403110f01050406082403031b0c0f03030409050910180b01050a05031518030c061603060e06011d1302 64
    0x290506040345404001e00800300240b10000340c00002c682101c620a20b40000c011400100040e8401c41015181c5030b154070707100c008040b0281d180b8242c0602d000c0e0384c1304d2115105142d1922680c61500c1c21252000503070b541c2d04400451001da000340304203424444c07101e080d040c500b6041404d681c03040e80121450540080440c8050030070746030101c880a400d09084c0d0506180202c080c111071002041011519042c04a42404030300c10f5001440c0c002024040b252112007541d2500f04030307e04c2155440091141e40781252040c6010998800e00700c00c054091030401d8035120044014010240c01e041d19400ba0100c0c2d030884c520700c0c0c404d6000031070754914040c90380c00050400030782c5050180c00441c09202c0c000800c0c4065100043c8111508010b802d007041c40359245854403070b4002c0c3e1206c4a4419020000e10100c1c01000040d00c2e034003171142441000304160009000f603007205d1007481100e00100750701c00003484660050000c2e0103120b41000e0380a0380701303502c0400600e1741046903948074022540031602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 792016474 1250 792015224 792015253
    0x2d040f0b0c010c090f06031805030f070212060717070c050a060203010e0a0509030a0e010e0a080102190e1c020d062c0109050303010b031e0901020405100c0c0302121e 73
    0x643d8000a21030605011250030f01140e010543e845010360410b254644d945c40c4013002a915503080c3d06504172003942d0f12011080c9065816611401d4140d108061161780c101030781e01c0c007080e403034010040c64580c10410b14407000034210450000304405d0511a04205040104000b8000b031700c010b07441810300503525810420300041e103800c003804005001380313460200906810000200c2c0d003101c4041c14030343c3d00c04000100403a2004941e5807860b0300040307901230000d00f00b0f00540203000c1d044400c0e84504100d006403030040f1000c40510315032035030004001940044950b204900189a1800a46107039182031240d25150161000e8510308824191480c6401100c00519400d2481a40c1e240009200c04074603a10344550324007040c0520078101d0302c008085001103411a4004206100d10780361504d052510714000c1f07000f500030344030700d80c000c1400c0c954034050301384101d595030130156214007038481c4541990203202d2003504882600d002c3d4402c2124000c0c034205071040842e00081c2c0c00c00204000c1004200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 792017724 1250 792016474 792016481
    0xc0f010b1219030537020c09040f151413021005040305070e0703061a07021e091602011d0606030d05070c0614070204020a05031b2d040f0b0c01 63
    0x1080101e41d0400501c0c00e401511085402c0310041d0185002900e504003050010580c1c03a6a1810200c0b0445494840b40440c0d03000d15185d640500e5a003d9841a0140350244104a002290010810420602c075400040d02e40004a401203010010014040c10458124580d07400262010050003244072031400031464041c40b10044a600c500e4803500b01851551007aa40f00c84501503140900710080004a95600ca9400400206140f25003d03400f030200c140548019844440c099004020000c000403001016000030103410341c02401c504030750782d98981e0504541c41c5210a400c115502c602c8030f00039445415407032201540c85a0b014000701d0402800300352520001c0745401060020610215002c40e80040301d210481d149410490002245404443e440c0d200d40400203502c548045503540c4c0c160f6110300694414690b00c0c211100c40d964101c80c4180324020a0784040010dc0c82e51a010458074242d041030343e050150325400750800e030310781c14811400b072660f07006401504800b0940d100301e59000d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 792018974 1250 792017724 792017749
    0x60905010b12280506030111040b030a06060824040b040510180c020a020108190203270c031b0f030a0803061e0922060507080711030f0714030c0f010b 66
    0x506100e0220010420f1100c02240701c0e0045003a980e403a07001a485803801c0d08590450700e120304440d903580b912000701407610341007940d2032012a0300d00040428030038060010030b4081c980b01d070305561407000c00c40b500b01c0c0e5160688903030a40140d195603c10000303807690701909004201c0784201250b52030400d0703e88844015016083c800c00b07404c000d4405e2030700b5008216560700c0e43d028600711981340e8403048603110f540c034200700190355644004200000c01c2c0300c203c0a0714458030003040c0208456200480581da5000c41340d0082d40c103412016004d51500c520803142c95010901420340008000c2d4000028105414110152000d040000400610b45800c2c0500e4481c0b01c041d040070440d20701d1001c0481d81d104002070446111071a032140311036580c0d0890580c21481c036071020041c060f51a186000400a050030354419020580100500100007004003d0781d801c4041c1d40c42203408d000d416205d064030340001c0040074030031b03000822403002010382c14041042140a080004a1b49800001c10f010710050b40f05d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 792020224 1250 792018974 792018991
    0xe0109031d0105033c10030201140304230c0301140402010810120803040609080d090212010207050309090c041d24060703080c041e0302090c0a0c1203060905010b12 72
    0x200300b00465049064440071080104c10880d02c4641700c01041552206402c41019a01e4064101003045641c10810500706591003030741d8410000c0d888850008240c0400d5400515000403403c41c4814488548291502c1e0201d500407281200036020100703007196120510840c8601c440d8041009558200c1c074a5074014240000b4001028030b44562010400101400203001c0f2800001040c203010b15600011115178004052759078504818010301300410741d04070100c1c019400e164103281c1070030040c82030358180f54100c80914540030711364040000d40341000701031140105050ac40400e000502d00d0a10600442540f02c81e24141049060703807111300c000c0f00c10007000c503100b5102561507490f81419505c9099050400300030b561100c0746405030501076504071211880f01036049403801440e0321001001c9078001c0c0c5075040c090f207604030310f940c1610469902001141c1840301e084005002240401401c9101e8600080da03652205051000c0c2c400030b070300403118040013190040c40e100b0b03550400342c3c0180d5107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 792021474 1250 792020224 792020227
    0x40c08060402010c060203060f060d0902101d151210090b040b1c020a05090c1b01090c030209090a050316030e0a06140c0c10030c08010806070905130e0109031d0105 72
    0x2c1e40001d04114842000506032600132011640a4545441444001e000141959200c85060400034014041547e069224140c56003100c00440e016041e070b0101e41a80d00c1031070704007402c524140844002c00325000800040d040101d01c040f500f800d8003040c00742030160b218481d100d00d405154400d94140f148914072462400342c005c0d065a59032240d002211808510040441c022400010414001a1710850b04060000700704114124610014600c055240c4d030b0902c0c0e12030200100c1400c840301c3c000000c06812070740e0811300243c5080c07074500358171881c60300403518081c07100d9581609540040d090703541c0200e40035a0941c20140c0000c05010104000d44120382e5152820310000c00c60000110220140400000d1550f01d01100f4420011460b8000d4500314000c1c1807000003d000700046400072300061103c50000c02e00440c00b01c0d10502a2000390303036043c100c50900082021050944030010000c075a10312020345e20700004c5c0158049035000ba1504400d145a1652680c880145400d465040150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 792022724 1250 792021474 792021481
    0x613020f04270b1f060f0305090a060906050105010207090501030b040314250b07050a0e0f03030408150f18070b180301050708040203122d07020a09020306030c180613180308040c0806 80
    0x20f0101b1203200540d82841c002c1619201c00031103034105160309002030403c905103c80c41c02888110b8101d81c3c1221000c0e0b08480c60166102c8441d01151801c1c000202014440400304012a04c980340004202c100c800096282800501e602500d851507082103c5042540b00900800d0280c1c0802084c1d00c47e4a50415a2800503c070800421501892602078803407051968218030580b03080082d80c014000000403200394030743c1035a00070034048040302c1420001c0070f45000070b812111590321108940c140030000b0041c5500346006581c41e07410145000b81c0040e80300c2030101d9540d80901980c1c1c0201c1d41c3d52641d034200d003440e00600d4100700511842444124040200b0200d100001c2030034080c0100418507542c150500c0d040d0140107100318000071b903100780c8841d030100e6050803640c000c500494049044600315800c0c8401c0c0600c03100300703807400c071b414001c030780005100d50604240d054028004140300244540d0340048906220070031000c140d0014482204100c104861038050401511100005017054036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 792023974 1250 792022724 792022727
    0x200f060c071a04030504180204080105010f031208070512040b0405010c0203030919050307052e11040e0a0f0e01091406010b160305040e01030807050613020f04270b1f06 74
    0x9203025030b0402c481010350005404d2522030800e4801500417004200145c0c103088250360003a4029000c4c0031a6546408000034403149400001400c0301c3e401100d022042d909600300f42c0302800000c00c14030921804000a52800342103020340f6101d54884c20b01e0b03046604040c00c1131402c54034078441c00810765004005001b120f9100094400084440c2200955011401d1403c50b085000c1e000d4002c0c401e101c1c205407814545001c001c07201000f10706494140e0b448201444240584103075070070105070076000300030501031300791120011075101031070550100c1d182c6c119052000c200e4042000035400369540c1d0390600308002d4070410829603040c000300184204e5040003d06207992007003070321458160750350781c03e0706040601510595004150005000c1100d6940c0c0c1814051603100100071100c0c2d0040c2c0700092240600004405030454010b00301e0a040340c0c500c8180070040664007254821340c012102c81000402c5901d081d28400ba115280d001914200080f203118040f4100c020300441c2c14250204b4418507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 792025224 1250 792023974 792023993
    0x60503011508250201243b07030b0a0e0a0e0622020d050106060f17090601360b030708150f25031a0102010b0607080a200f060c07 57
    0x403c0b908409500d60111141c1a401000b02103542c08220f1408400b01c3c00030104d510006088601c9030120b011028406100109180030782a84a40120b4040c006540c6056140030715951092944c00c000400007510000a9507c4c0c071540c0c0710f061509400c1d0100074a051950041c11140c03002000141014240082140152002d6100042c0301142c00140c902c10f559444a41d000d115420200070032074982c444a00a00c501c82030208200441c045143c200c1a0740726601070144582c9502d0068040c690030200300c0003520007004810000c0c03818141d1203920584a40c001c490f03c010300c1140014082000030245418841580d200317600b0b0781c204450124004020484040d48549004070603c11551a41c505040d950224040342c2d000780441401c024181d9007640c0f01030329143c03404980070350005841004901740c0b40c076020f040b0742001d014070428001800e0b41014141410803428220080c02000c940c41010310152411401c195120002047c1c07081c5090000b0b94000d080f265640d45440a02d84a41c8181c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 792026474 1250 792025224 792025261
    0xb15040b010914041b09060f0c0201021f020c07143f100911030601050a05060409051902300c0f0702040e06090d020111090109180204090204060503011508 68
    0x854050780945562992107500102c00c501782402d1211700352010f4400103100780503d014030b1000c1403400302000a0300313018103403003149683c0c1680100180041c2c0741c1040c0014504203ca00b0445801380310310f6405603002c4c4200000713001d95500080000d07128004104020400ca90180041c4468107468050341200300c000140540ca60300c0084200002c4a00d91450880c03407141c51380d103a0303280008090400c25048803000318204100e04a80050340c0390400c00100200310310078140e100d170703040104004d0401c0755000558009014004644408210f4902c041681d11843c80040302d490b002d480d8910940c0b030b08481040e042c01503105008180b80040306c001c164414090440e480c0500440c0d850215540d40d0401380c0e002d00d520040c0c62071030502c0c90301299224200d840c0240907500b820401000003900300305407101e41c0c00c1651079408083c58400f00f0b42d4100b43e14038600031840d400300004160034549000400007041a0396480d41d496140103c1c0b500d000c0c1c44c2c100303481c04004504043c4000d600100d4400943c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 792027724 1250 792026474 792026489
    0x90906070c0c0f0e0601031d031c02042105100203060307180e1537020921030304060b09070906050906090a030506010501031b0804060504021305040b15040b0109 71
    0x24140903508180c000103031154010600440c0d8590049000504060f00c10f002c5c00c0c2c20f803000d00c00e10361004450022070442c8001c5c038030341d6071042c440d04018098131036941d0000101103000602c1c042c1c464100346d441072044051500c2260010405c041009420041050440402d41c400c41c11403c0890009e40c45002c10720400d4403a190b14425001440005c0d8000c1010b010070a040f2881403044004070280f450007150414244281ea1a44100d00c0200c0701c5020000004001c0d5540b00841c03ca0300f80c2e0080d080f26841c141c0043c0318400c52440800001460b50070031303c80346c006640380d107010b01c3c28005803411510490301810584c1d003030104040e0007102c550103943c0f582c00c007207441d07840c09000300e02c15000d40c00d152a401380300c0010001c24001d0225200d816582e082c1c1e028005008089445418440b00c8140800080c01c02c0002501040942e44100c3d0464401840086030494100c8400300f0340300195400e0300c003240b03201d05110002504800007042c0900a413000c0c04046080343c000380000405103c1c600703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 792028974 1250 792027724 792027737
    0x605030f151608060906220504020f0301020a050f07080c031216090302010203070b15030a080403020901050901050603150112051f050a15030f1d1f0911040f0b060307020f060609090607 81
    0x616a47d14000342000050404130b1032032040303400c91001c0010300019103082c0d000b5030b1f0b40380354000c5904042c0211003d40010b601e400b40b9140f0f083d02c0224955006900554032404240164850403206000070b18404220056082140c00c2642c13002d41410b00b10840341c1c0078000342800801c0180d802006458506402c00c4d040c42d850341e50941e000000c00c030090503c42c2d01d400b440608400300206c0c10050000d1324001d4550b901c00d682c035902401300a07042800703000e0740508180000742040c068520b1580c840c25042c034003003448264048901c400e441c0c0a03110300340034031070036044842851042c8200c3d40003071404881400d501032514108103d85074a0149401c00c1503100c139400c1c01c203050b5582010341c120011208080d141d10108032525104c420610120820004909001041500c1d501541e01ba5039006001580081c3d00682000003c0c4001d0404003062526484007548907034030304c0c02941c8500070f00e03009042c1c0700e0b400e40e0070030b400c054000344814407415031001803003990240001d030075921071454207104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 792030224 1250 792028974 792028981
    0x10f0e04030e1f1707090b0f040e0421021c18080307081c050403091205010b121006050607110108190f0b0405180a02130605030f1516080609 62
    0x210ba4807240724101940001c810941ca0745a103c8400b50380400d580c15903100700b12442070b440705500404007990041c002402c3e0300b6082c480d4103038001c02000c00403100e1800c94a0507036181c0701c2000d0380000701c40c1611031094410302d80d2018034070907407602140d10880c1b010340021740c840d0000042c2040982c840c0020002d15242e594120b048003241140a0310f4078004890b2110018541169180d22890f00d2040b0800003202544024000d402442e00440e410340f102005181090140d510049001405540564840c8000a6941ca40900c401110100e40d00076140351801414003a050302c070b1641c0000e010745000c200b007e0100d807008658054620b400d03c0c00500c02c4c0c84098001ca82100d41740182c2e00404d10704a403c6850070038030391080c82003200507a014009599940070b000705209200d00a901c1d0344c0c0184202c28018039110f41ca21904601203000083ca01b910b400200740781942200785d419695000d030405d14108880d01e407810b540074049162011f4208511000101000c0c0050481c4e8002c038080c2011 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 792031474 1250 792030224 792030227
    0x1112071a0702030703050f1c121a0618091b070f0c1809060b0a180b01030f0c030608011104080a060207050c040203090c0a23090901090501060f0e0105040203010f0e0403 74
    0x1c403001290010120b480d42522418910344035016204800020f20400c292842e0014020290503401801911035858034401810214050010359045446c00c0e00c00300022984c968071040600350300b5040100300c045d102040d8090101403d00940001d4071150058001031008450104489080781d200e2400609600740d03160020b0040000e410210300d40d03a500380700500a0f003880c2d01c14071825005a800b0321040c144202803000b2070310180201c1c000e16075145c05102e105d070000e81190740d12003418980010107990340514501102c07200d8210000007501c2d030a041000200c240142d685012100d15100e10305450080300c281c1d40c2c04654002030419030041004024810188200d400c07a41002d001559079240c408415501c0d11601f43c4203e11071600e50801150403506c001c2c0c282101203c8407038550b90045100100000c0003c001c180d800c240d0f407246241d00000300c0078003c0c0030060403d44440000035040882d1361024a80582180740034901c14130040000c3c2400c030851200710fa078103c203914031075212800e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 792032724 1250 792031474 792031477
    0x10020f040501200d180b0708030402060306180115020106080601050f10120204030b0609070c05060a1505150429031303050714030d0e01053c0708041112071a 69
    0x5500040307000b40080f074141e9640005c0070880d1110720500d41040c032900c50140720280d004421000e040d0b41401d10014005090400096030003c10050104c0d03550794142c294007503140c8090700b182402c18105440004060340901600002e4019900030341520342c11714020416012001a04500c01c00c100c44401c00e1290060b00c58105035004030300c0039541da90f108d0400000d00401696207030301941921002036010380c494812100019401009410304d5141c0e00401d038003030700342e0650304100d11061040c005116501c0030b410068015407034030304903101c1d8600b0032010f41c0442c0d0051140b640c5003500a00c14040c60180007140e074050407800710324400c00d030f403410308071210700402d01c0c014541c0c0300112041c011150000f02a04848680c004107004000e8440102c50980d807080d1003402445610803004900107000d8140b2018a20b1010704030582042c0491040032801e07802d440140100701d5883c284418445424084100468252000740f40030030b1035110303190303114024422003c49400c03000c40520350401d640c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 792033974 1250 792032724 792032777
    0xf06050d1212110703080702011812091e03020f0316031b09020a0305010806011406090609011b060501050a0603050c09120309030f06250f05030406021e03060310020f040501 76
    0x19401c00844407180680c80844d400340c08258042210100018581c03072050181404605611382500405c800d00d6585004403001c1d0503031402030001d031060201d2060580c81203115020150007200403250300e50b0062001d15022282494001d4000c00245521020068101002c8903400344030110641e03503038420380e001703204036030000503010f4000543d0101c100d6064100b83d0580700c0300016a14075076650800c1884840d98038103090f40040d018411408030349080d00c003800349005e040c1408204010000b0425009043c0340004403039481c2c0e150014001d500346555000098807403800c003001281015400c2000c3c5000d98030010380b1408240300c40c41c1c0700e8030041c002d8454054000c0e00301c403803215250500350345924048882c2504140c00300d0491500c1360045a1a80143c1c07401e446030000d810001400303e803113074801001528015001c00c0b54001c8560a06801d0b0542c0c510510141c0c0c880c102002050300b0001d028030310301c81480c0180008000310205000b220100d840c00d09001c441d600f445006800c1c104c1011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 792035224 1250 792033974 792034007
    0x109020d260c0d0806031f09081204051e120712111006321c0506040303020405130603051b03070807170708030a1211130305030c010f06050d12 63
    0x410ba14078019000161204080302d542c0741c0c004180e403000c00303240d50386440d00d1001d80e1011844010144440940e8801004140565445440c0c004e80e58201e0f00c00150541d0304807059805603402c10301c42101006c0f110780084400c009003020b00303c6400e1404150040050240845100012922410b40240703110040c2c2e030b40300015900010b035446603000040010740720304034041000360001081d1090004000000014001d00c03074201440744401e00c4100180d400072801e00b02c1ca5496904007089042040c2c51046d0711070355000d6030300c81c1040706100da15094100e042c0b419504142051000450100e018480142c010b024402040d4061001900d415502d603c0b5480501803200b002c5a009140b2880240c1e40349401f08a86600d40e550207420303a00e1080302c048600180800d081d502020019800c45c84104d40781181c06404c10640c4802098005496402190141d000003290507401000b0300404944c6035801031b00700700c02e40c50080072030040c114480b0020714214408002c108018003485082c04040d004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 792036474 1250 792035224 792035227
    0x4150902040e010209040c0212040621020f03041109091005220c0f060203031b07060f020a0f091a03160203040f080a0213020f18010525060506030109020d26 69
    0x3007002c990007035010440c000c2c061802c00081000303050000a60022102c2a03d121620306031070000102c03054076400544043d100720120201d0f50b820305600141007820b0143c40d5281d0381c2c2c2045c3c03038007001d80320080403403034058004142001010440800c01880e030b460662404140c1d980c0f44e20888550303030b40002103001e5101119080354244a408200f00303040e80e00001c0c000307076865142d28091782d03280002c540d044080c24082181d00c10001c410400390441500c120808142c0b4500c0c061746105a8220380c600c20000740c104070301c1d0400070350f1011a000c01800302d031031160b030b140c0100300d20880507120083c03284032102c14036680030340090b02c04c200700c1d802050904507603c900d0f52201901e82d04c03504014801c1c2e100b0652101e410750406400d00c2114549041c1140c40f51038010349113402c01810304914481c81c1840428401540d500794801482c2050001d40410000341c0c0d0b4544c94030b00100d4070040c003001d00982c5015141c0005844d10b2401420094110328107224121700041d4242c000003e40e00401c0075102c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 792037724 1250 792036474 792036491
    0x18020d060c180902070618020d060b061b0d02060a15030633090510120b06031614190f0509460b0906040914060403020a02090106050a080415090204 65
    0x24998003401d1701c02d11072007091120342613002c0400c1e090314400320302a60045494005000080556024181700180070f08070a007064103801601102058030040c01c40540c12880e0459140c61b41845102d5001e90400c60410000601c55002c410074401400024100c80c1d481a03003004c11900c921030441542c404180c4800598040008407906c01c05a104044c000c1e824540480c4904141d507170110140c3e141000e10889000450300c603a1940b0801030400e540601445a2004090215071820400780c422203030011051203144041c01000c195406044a05d105607810030300000c201c9010002c126801102c0c024007d80b69500c2120b0041016500d02d6a00010360b1010030140c02d14009000e0020007107001c0d41000300611504e20700707440d20b038690a6030103c01070f0005052803a0560244200c6400303054036040e9031003101940d0b4900402580d05801690101e0f03110811450614119400340c0010b00d40a41840300c1540003521070345c0d0142c0020b00801d803400c00c6240b004051341c0f0901825400a106101984 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 792038974 1250 792037724 792037739
    0x120d1b050715020d0507051504020607050f16081204090507140703170c03070c122a020406081f1e15150903210306120c0918020d060c18 60
    0x2082c00c0800000d40621200b004140b8081da003602d0490f40c00c0340142c803220320110013000780030304024022a4041c200f8800d43c80442c404004850303120070114010440800000846104040190301a9065501c00c554030480780d000907090b102215400c4101285580781c0744029600105401c4c950354a00d200402d000c010325034400d1040c1d00c52000804085255200c0e03401503041c91004a43e10404100b9410501e00042c11442d070110b4044071502e004641e01e0340c07504420742c400d09000079005c00040301026001c03c1d40703003030700c07411001b0041480201641030842c0d4011136038901000300758100b10794401500720354000710300201c0f1403002d10400400c00e60b000e80b20f40080454142c02444c008000c400d000c3c0343c070280208183e900740c9070840d40021402c29503901460003010404140400c140e2910300001302c1000444400346890302c00c1c10b00104d4141000039240442c2e02600460441d407400b840c000c00980c80d80c2210702103c0d50000404500c04494550646480e059003903031520f6400c3e100310004590 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 792040224 1250 792038974 792038999
    0x1b0609123f060f0103060503030702011404082407020105090a0f05070f1e0609080c06090616050d1815120b0a060504090b04020f1c0b0301050a0911120d1b0507 70
    0x140d0080b120401c880704403c0044045030070ba4040c250305584200840f2000d58007606103030b22a28007032000580b80c0f984522185007403000429402000c020301c08034006071b0000f401400c0d0f51103c0c107440200b0642c034040500950300c0104a602170192000001044248281405068040c0080c546000c03180d03942c031003500c03c41d1070700d23a07203201e101e103109200118407584200a0502101c500000070848003802804000041e407281d800181e02001c2040305907039220503440d201d28000c2c00395001d4601004145005040351080440e008121600080103000c03100700ca00c0c8007203440c6107070725100204000c6034503007400900c084040b40ba40400c0300782d800a4416030280c000c1054a5101e0020701c003880c1d0a90038401a4010641340180300d9030300703103c1040e0b00c61264002800e0340d58010720205d450401d01c0040f0b0300310f69081d1603008203903271110890000d00444078409084e000f400e480000c2c40c07190888100c4d40f151100d06405040044150f07001c00e071001440b40303c0755483d400070103440c1316586e00d08144005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 792041474 1250 792040224 792040231
    0x20d150302030d1d060f0c0d18080601120f110301060308091203041526070e1008130605091f02030f06060a0905150409021b0609123f 59
    0x103841a06007010382d541c0b003000181041c0313540c200200c00c4140444208809500524100c0c540010284010f1110040410480790b03000006d4885600da800000070041684441c1d8202c0101c95000c200100182d11040ba00d030010075800c00c030100405603c40c600440581d0302e08014541c07543c2051030100c14084504001c103c2c010003100e100e0084083e0004594803809144520010740c15802e1401c0c00180c0900c10354010308800f1203011090340b0b1074004c0180b1040003a07400c280000c03850307043d803038660034114607030102c80c2c029051141451428254064a07660f615078010a80703500c1d800810581b00c1c0c00c03c0320b00b003422250b40340700c0c00d00e1604500d040025001103d035900f8294446020901e90708103a012102e03c511140d4034070121504220a01088035484228021139080400001aa080c0c040c400750517042d03601410000c403107283e00f560518049010344003145075001001079500c1c401c1131a0494054020b1848508040c1c0c03103070b00b6152074001101c0c3e006501c000c01c0c9c1c0200700e600b584183c585480b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 792042724 1250 792041474 792041479
    0x140a03090b0907143703050d02060403030c0c080a0e040f110d0b0a12060203040804090603080c0c010513030609020d050303130c060509090a15050307090b0102010501090e070b0c01020d150302 84
    0x107098200c1010002c17251a400c450f840640b03148514003011541c5407080e0001500d640e4040c03151140d481d650380c5e1030401401c00800c010b800500a1004040d458042c584001c1001c0c50a00c5440c00c8030340380c2d20440c0c4140390002c4144214903001691503217842d00240f100340304803030081000c694031400c0544036502940703d146015243c11a000c0192600306241d10903281d0324030405c00311240315501d04000b5440a4815201040140f000140140399809044041d42c0300f818000e0f00c03000d00342c2d8050702d4240d0f5400894117000d000e114000103081036a00020841c1d40014000c55590728a002103040401c161201074458000003082185060b5104140302d81a407080d1030002140d50b0b01c0b4411101030241d0510359030322043e000d0100d0720100d01d60300f0031100c500f07400345284401039685002901e000000d9115600b80c9480d94440101c41d0b80a20545004000750301c014441002c6000d105511464a8001c03001c003410b02007418012480e00754141c6a50000d154010406040420b200301079056161001b03d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 792043974 1250 792042724 792042749
    0xb0703020c01271a010806040b07030e07061e030e060a18170903060a09111e0a170f0705030309360406240501030c02030c0123090d140a03090b0907 65
    0x19151301303401c0654101ea24100107000652240d59800681f0072024100e031081645a2060b9a8006024803000c0010146c517190740300d191200346140c25504c1c441d03801036400d041c501295202c070b05901048080d40014480000104826689110083d92902c000041e0213504070703805154075085180000d04c42c0300c030101c0c112506659080c06100643e101c500d8000c1407011403d0080c2c0301030030b00c0e6100b00c0794181103825000c0310f1895400030503050352113035029401900300302444400480c402d0004400c5906628040d00a03a424a004203660388200b04200340528540c65211340b90b00020402102da4083d03c1403880300c000815904040c100c0d2080c1d5040d075a513441d007003020700c0059545046140302c6e044c030603081407058508001980101144c02161042d40400c010a0940e5842803040ca0340c1d0508510118001d8204201400c03491070300140581c1d140ea0210401d001840c1d00110608412120b1041d0316584102d44203085010b04080d4030300616454444007803084200d408226101074510000303642 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 792045224 1250 792043974 792044003
    0x204090e070e090c06030402130207110108060a08151e0a020c12030106120b0102030f0c010207140601060c0803061f0f0f08060607060b041103160e0102010204030b0703020c0127 78
    0x120b41c8081c1a0380d41d0f400c40d07112901600032418414043d40d8880e000821403400c0303c2141641d0800e0382d120325001c644070390409122400035a00003200542165003513941800060406003c0d44e925010248284111100c04002540800d0450303856211207403400700e201e1440c01c0400b107d501035001356030111014001c038001c0c03c01e202c0b10b00b81500e04072a10396070341c0c5080901003a640d40040c07002803191411030000b08901d50040e076164008003110a014400141c1c1c81c03042e418a50300e21281000f007210325070050300040021a07400440300b41c205030060380c8903949441e00c000154800c9540d00c0851801c5030300315800c0000c40d0304808002d0081602d52180301c2020342c0e602040314042000c0f500264030078014070562021070b000350300c1843c45c4007001e000001d60300211580383e0f41a030800c948000090001602c121100c07513000e103100c801c000c02170000b541040c0c01d680c0c4080d0a60f000511110401d03501080038807480340250010410801400c60503190600e0282c40311101640105c2d00365290325120120703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 792046474 1250 792045224 792045239
    0x2b0903090f0e0c0304080d060f2c04050a021c05100e150603071206180609020a0b13061407140102090f0f030d0513170c04050603010932010204090e07 66
    0x181c5214400303c01e1240c1c55035441d82c3d81e810031900144522150b2031b60310a008214000c0c00007008001d446c41310507100c0308000d4064410654070107040d801c4000b0840300203210004000003194141540d0458590541092040d105050f605040601800c03502ca0b2110000400002da8810707610280802d09846c1000c1c0f003280b5100400c0307020f98500e5010b50201800b0080c9074000184007007010300c00e01020850303030800074488a04440309035040d1031242d598440b50303045141c403002040040810112460038100c2d200310800301590b551040e0801e20803030075218182a0410030840702d003550f0010420940c4003000d501c0c28001e403c800c1000380200c0b910100302c0c003245001e22840200d110000c0041c816140c060f01c0c02c84164019203107244055140d902c0214a40e002007120384280f0f10400001c06040ca18003040000ba01e0014010034020b0b49002c1071800072805040d9208113095910000c142e00300d510703926030814140c07202900a160352010801042d0012950401c00012000508032440307240c581d0342 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 792047724 1250 792046474 792046499
    0x2502040c021902060c010f0207080c070824270c09220809060c07060f0311090603130201120216110102160909150504060f0e0c03032b0903090f 63
    0x4501c002c840703441034840014500500103010a400110021503095a841c078480241d070002c41e012244a00c0c04600140000030400c01d010007454080c00401c60a540644150442e0283c2030806a901c940c04000481c025880e03c0342d800044402030221420361240c0e00c0c42030310785840b0381c44144254030728004210b079110070320440d05030f0b050a082145840411592003001980c004144107070080414800b0b40512007003070022600070f11084e218080144025031000f0101e890300700c0d400000b0001480000e10a8842ca41039a621555100400804030420300044e40c0c0140c040e80b041010600001e03030100d04403010060108603510a044003108404800e006980b5000b05140d02400c0c0b0401c40010020920700d03801c24000940640c050b61005003200d02e4100030b40b4000c4805454031a02e0750380000c070352603a910a2682c4030702040c0240c007a945202001980f03922501002c044440240e180050301203a800110340b0112031002c0f07081180b00f240d46406441001144030790240000120300008101d0007981 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 792048974 1250 792047724 792047743
    0x510140a0b2b2003060d050607051308030301030c050621130c120f290103060c02190b150111010c08180d0801060c0f0b07050d1104030b0402040b062502040c02 70
    0x2c0b419406a48500f03480496402c010701455000d81c103c03884601040041c480c0d58080c8442ea544e555581c082e114400c0c036000f600e070344051084c1c6d01c00c00041021564241d022030541d0350803244156600d81c04100c403014413110503207804075454210f042c80410400281001c220600c01e03841c000449507a0008036613440041039010780340c60800d17440500000d41c0e50320080e131104800760303403115104052003403030b484803100340c104691443d0f40d041b1694629404100f040000c12041503510424201507940082195019162490004182d210441d6680c012410103101081c0c001c02009405061180100f48900968034606140a00c0448026954001c1501e83c08428241c0303e810300f49c1d10b030140880c0c000c3d0080c00203484100c1103a490800046541e02c0d5240281d805665150b12000408440c200b10f0f0409101d07511408010001000060b030380c0181c1070382c49074041300c0000f4940c4d4507001040f1107200740104406034001087c04d0070355041c04907603299042d034020385d81040b2604480b0340c141d0f91401c01c40b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 792050224 1250 792048974 792049001
    0x1b01021804020705100e031b06040f0303151a0a03061e0311010c120201090302121312030905090403020304090b15120c041a0417010510140a0b2b 64
    0x103022540c0ea801c00c1d8006240e61842001142e40140c0d9a811280848944c1110b6403002d0300002032002c042da10300944100604007103c00342031182841ea5807035102285e6800c00400740b41c0c490070388982e490860381060000305030007124008002100110407005034040f021030f101003031505401190800c00c12880848040481a035050040c1c1141c450540302e44188100604103d58100c030a000200005c0c52141001c00c0c9030004101070407140b0340a400c0402d4448402c000301014016010f41d1900c50080004907918034020161201c554242242c41484a42000760400d8000090104044c0c0c00030040040b03030708800040041c45211010007031080920700c2680c1c3e0501c800d000d482c84e1045580039854018100b00c0c45e8030720b050b42e59501030300c030240c503e0890714004601141c204031000500c000c101c80103113003100800451801640d0840e03d4809801001c0030302c022007c050885441e10407441010f803040408082e1500d40c405007050032010b5503000080000302e11a6940a0015a40502c2c010407001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 792051474 1250 792050224 792050257
    0x20f0607030207051b0a050d05060f0603012915072a0f0306020a0309060c09030524010308030703020f0f0406030f051519030f0f03022103060d0303020d060b1b0102 72
    0x1103080320304002182c42c0c8040d1b000c480b654000445550380d04036110031b644200f016004510345141840b599600013452036000341d0400442801e5032024410450986003d01d482004104020000c114149440407008826920006040d418003020b510320780c041001c03c03402d8082c031070090725180d0b68008480c0709160070803402c410180f00090b0706402414400409240014256205443d280c065400f00b44140c4003154036a11b0502c02d02c003050040c511400320005038400d082c21903144e0b028034450b0510021349510804400304121134800e0f0111481085070148241c0ca640c440c20b4518020f44c460f02c02c100c00700740341520110003c1d001d1b019452255560020552281902901340604514214000e0f01e5840340380c0d20101c00034400c0c2d01d03003919050050146101c15009490042c0ca407210080c198100c4240580c0090080b4050a0440742d00880c156009a0120b202d803034160003a0003001d100700002410301c107001c136216000c1e02c090306400c0d04a211151000c140d5058081c200c0c07003101001d4000118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 792052724 1250 792051474 792051493
    0x812071b0f0b0d0e15010f0902130302090619090b0108090604120e030c04020c0d09082b031d150a0b0d020d0f15050405060109050c0a032703020f060703020705 70
    0x12100c014141d0408100e1000c52806040c210543c200405251a641704124a10041c007208001800313030000303880891011440e07c1280308012408114130f200003841183d4400000321036854041550f203801500f000000d0485468061010103849038045850000d000040069030305400051070740e0245400000c290f9440308088421104101000115a01032080207a08542510340d07100900390f406104000c0c00107400200d10007040d40040d50310400e00342e402504814261041d031441001c6c603621407000e0099801c008242038018141c1d4130422081c008802c01000200200402c80d6852051520714891303541c2e45101090040360b0b815003036980c0203c02080c1520040c02c0140307042034100c0c0900c90240c400c00d05c990390350700009414404410310b07a8868040c4020813078100103080c00341c074001d4002e01c4603241888071884540220400001019165031312080d1078a04d40c1d00004060480c05520401d1500034180a0341d80e510b50704200c0320b0342c0704480024451a1080c82076915441c1e111024240540c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 792053974 1250 792052724 792052739
    0xb010f0c020d02060903160f05190e070e040c0f02010b0604360e03130504090305071104060306230907050a1208040504150e061504120305040812071b0f 67
    0x10503400498101e03000700005c64941d5810000b01d042c01c941c0b0301c000c2e00100d040c110f00c1a00c8a8440d031110f4017500d203045a4400368035000000c40d0648141d400b15064550300c140007101d00c42158070203141c010781342040b142c3d19136920a603d4025010160001d0004480070010301115115511440e144403c4900c0740052110340c02000001044107c40400b00c1103107440035540441d8411583c480d040d03480080c6224400100d45084001080e08503005c0001243d15100541036102d801ca0060101c60080000245039480c0d512403070203183c20500801840c5200c00c0c1461075150141482c5d1210000500007902e2280c0000d008000d4940140860400d546402c1d09000000201c0d681250075a0040c080842c15031118814064a03040b2184100700d0300d46040f092803c2010050034440c06001030442c2d07a0000070018080721308650034440505204010740c2070031030701d90240707400c420254003032203420300300003141c01010301902801540003c1c040039200c2c0c1c0c4241c00807141d100b10840400d80000402024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 792055224 1250 792053974 792053989
    0x120d05090607140a0201020f07030302030d050402061e0d1d0709111e0306012d0f030b090c0904060e040f03030902151b0d090f0b0c1e030d0b010f0c02 66
    0x40098100703070400c040c40c1c0d42c0480d5000900e4040c00242e221600000c2903681c1001002101760103800a00b50340e81c20340d1402512807051000003509140c8600100b0304645590044420490701010906c0d40c01407614050b16095202c0718804160303605051090449607104640d507108070385c0784001452100e20305180080603001855100036140302c00c0c0400c0b155200d0b0b06e008100410021000b0b103030750b403628800142040c581c0650a04001c80d00b10854601c100c288003d00d0020075450401c2d0101f80c400e10001c0b405410404422904010041b0030320401c041c1c15030203000800c1048406002d500e80720302c20210340e8481140d02606004603401c1c00b0001c00d000e944032586c0a800506103101022054458980d5171b48181e40c0703000c07100143d440d6131094a42c140f0070790440307001519080c03040d14504411403113041c2541c003501551184c0081e850610307900410803900046101c01d08154180ca40d9420305807641c00c02d40040e1070b22418030800100300e622410905506400e030352983c0e2081100e54007805103c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 792056474 1250 792055224 792055237
    0xe03060721091b03050a050d05040e040f080c0712062714120313030305061e040203250917061e130b091e0a0c03120c0c09020c0c120d05 60
    0x84001094030500803142d043e1440000d0360043c070042190321040d1400034505210000e07140204501031000b8006110007030301030380c2c102e0342200307840d008108c0070304007400c0d00d04c12060002054800c3c8500090038442d82c6414440c9035000c1c100412501c09040c40c20b00703038107070705c4e05001c0360301c0541d441224005850810b14480e40007103001100c0e10021001c2c80441c45520589464403403000510a04080540c1030044070790040068821b00b0342d454910070b01d4001400c2d11000d0030311403900440003440300c601045610030200d01c0d4884030b0903a80b400c902d000d03000c0c1c15036018145d105030401c03184983c21070b0005030b62405243d5454a60400e5000c0307005a140105000e4210341a6005140260010500030b0340c02902580042002e0086203500103542c0720040d4501d06001c074183c00410191010500c0c0c8103055085a810aa131448091065402110718200d0300744005c01403a0003203004500070030f480e409003900e104410101c4c0d0100400808024040c84d003001100340d5030344403150070007000c0e1089010340301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 792057724 1250 792056474 792056483
    0x8210a1103070f110d0206040527070c03020d02150c180a031515030203030a0e0d050319090501030b0a0b09010c140d030b010f080601032a0e0306072109 67
    0x80300c150140c555815980540000d64900c0c3c0003602e014180003400001090340d00c400c8802c11044200351b40819506c0c052403040c030703100d2810007142490740101c001707050441408404522406161480e03004d4550a0229019001481a20350f00ea0311140001564411941e9848460070640d580400c00c0c0c03000ea1007040e0001c082d583d41c019408145d15502c0c801c4000e14440d141050f004409291000120f03803060306244900080c00d130041000d43c0703001c012500310550301d25100d400c040000c008203103820b810740d000401c5444005150001c45480c0303002c80c402020540d80d21441c450f0f480b8011805e031444003201e154440c0c1c4c2c10ba0204051490080240181001810544100325041e12a45264a0205001c00c81c81e0040e40000c2181c6034188100b42c1c0032003090815850500160500402428005205a050565400840340b2140400010382c01800d4220720858600900c178000400c0e00b8401100b43d402407040304042005140507554114005146165404242d210440200c0281100c2502540d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 792058974 1250 792057724 792057737
    0x80112082104031806090b0309070f06020a060b0909030901030504170d06090c091a0306013e07230a0b0a0203040e0c070c092a03060f08210a 62
    0x10400791085000354010601d03003444401070302c0c0500700500882d880f043d28800c0003e40d404c1c00d12035641c0000625041c0d88404145035282d544011040b0300c1c00144d44c0000308201594840007510b80d5000401c007068600c16042070140d4030140e418400c2e51300055811400700e0300180200c81c2c07a13501c6980256485400b0751000007004560024640541e071140d910704901b80d807907050601c0764443d0b40c018030344840c1da6440c15104503480c207821004cd0412000c0e406100100001c086085a0300c51040780143d03080502d1010084122030181001e500402d0707001c205c85006c40c1040103000303c0003240d8801100d201000d804240c5205136490103000c10120001d980c0310b015500003068000742d8801518007199560010343c0d8130380c10207503101c020417401000d110012808201c60030000e00119808002c45140903404540698121403600c81900f0a5030100200000714a29200c1c1c1a8140c001000700d81c0d00421101806da101d0b10425120015054900303202100c4d203280c0c0d40740c06c55200007012003070402d00e01203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 792060224 1250 792058974 792058987
    0x10e010f020c150423031f09081318050105060f0c0a0c08240c07020105070f0b040606050103060e0c0403030806030708010903170c0c1b040f02030420090708011208 72
    0x14880d4101200f0b1058031540c0400e0600aa9000005682064a0741401034046203014000a56240d400d034410801c03030240742d0300c680220030070341c0c10540c00943c0c006001d586902c0e03626100032260b111031107501300c10b071010000101e150100703200d0f2506075040503003180e143c40c00a9403d000f0a0b440001400420f12403201208089060406400c2c040e003801c2010b04102034a603018189981c4a01d2442101d4445034028440711048210442d2422076083c00c0c41c54031954181041d68607522040d0f000b404030045201004200729944c2c0c04072040e40e009807801c200e074948a1814610400c0105e80217052190100424800b2a000b4100141e00510080403070341c009869080130740c25240030306000c4021409840c0d640c41403c81c60f41c9100d502603008202c0c00e042c240100c0c050b030703034500038079081407034a206a91041c4050786507a0003130552080407440039903490800b407400e0000c65011041803a48860301c1d0211514516050701150b0240001d56248034a0b40d00303207a207800344521158000c031106841041b00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 792061474 1250 792060224 792060229
    0x3030d0e06091509060f04140303090a0203100212010e0a09050a12021c080708090709061202040c0903080f0904090606090c09090527071e06110c010e010f020c 70
    0x45000c9a10400050728640c14241e00c41c6182031600c8440341c2c1d00c001c09104101c2800400122154000001d426800030b07502c690808000310030f0708410401240c00300004000035108005001c0c0109807080c1e084a00390000c56186000300d020b14400da02444840200400550302101080c541000325510001898501a95002c0c43c00070340c10400c035a400f0140201800c55501406201c2100404042d41c0402c003047ca80b0083c4055030040104c028081c4000216079441020003038503025244500e010031240b07840b081d101c461800a000c00300d20441c10140c400620300d1050600b0021a03922410050034060011180c20880c1c01c464155a04036130750f48141c0c0701083c0540074402c01801c04510008009038001c40c018507640042d04000119801c0c1740c00d202e40d050403002c1e108500c1070301e40b000d980c18569052400c1e04203812070744014620f404000c00401c1c1c01c03035000162003c5640507210710703c0c2c888000500c552540308801545001c0740c54516400c5440d4090a0402c800945500c180c41784900c00c00d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 792062724 1250 792061474 792061481
    0x53702190609321006142e030e12040308070b0403050d090b040b071d0d2301021308070e0c0a0302071b15231c060e061509010206010b0903030d 63
    0x510155010f03001180204040342803044010800810100740040c90400f8000d009180c03107065030601803402c445c14003c1c1070242c0050319105020700d0f030a00c4c0320950340c4400100a0540c01020840c18007901c030041d80b5111520049a0171170343d000f18040d007048190703110f4148141c4000c0c0103806004042042e25038594091080950350361040007000481d0a29090107004d10703000500000031f0001c20351510010300708152001280000480d084c0711404141c0c600780700703001240b4003441913000e0640a2202c8000064016100251340c0344407171900e4541d105107081e42c590340e034462420001402e101080c100360031540144000440e0341405460070030340303645418082549113446141c00301c55000601c10300110107014022040580381c030412000200221083d05113005c003030703800440d00c00500c103280d40307580e035026805051010a04000c40790365507415240080b4100d0354140f065480c1c480b01c0301e00d80400c1098607502c10040c0c1c0180460382c01c000b5001010341c8007408540d41403109010240ba411030501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 792063974 1250 792062724 792062783
    0x10140408101e0207021315080f030702090603060412050a05160309050a05061312022d09070302030403021e010209030a0c1d06010f030c053702190609 66
    0x1c0c030000d041c0c07816041100c5442c1031281240c540701d00411000d000b40c0d94a0070303400e1703682d48150350003e00d020740ca080480d130303280e0164041c00300741c0205101c50201c040c0100142413134600a4580130b00c02ea94070420503880c0c040c104c1c1c004140408604a01005e01c2c85800a040b104502d410720740d2400d010200d40c0da0095001c150100c0003d0000542032211342403401d80d21006090035030b4001c6c1880807205100c842000b4070301a0807041c4a0b41c1c000340c415991024000c4544000603403840c401c420140b00c0010046840d0341030342c0d0040c010701c1d0202d19843c1c8603200300e81c0b0450b09507010302195035161440f000c00a40c0145180c40541d024020030001c0d66061095a00180c85946c2c82441140b80039100124060741c00c18004d00102107408011071640c020b0505490303840310303260020340001080c60580d158011041c600c541c11684640454106c0020041a00c09614801c1c800400300c1070140120b99803002c2c200d481199080c001c0030034001503441d402091445203e141204180a5401c1049041e0708a86 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 792065224 1250 792063974 792064003
    0x2070f0c030503070c0b3127240e070210060914090c060405090c04150504050f09160c080d1104030210140715021204060c0908070510140408 62
    0x16141080001d03880c0303140006c010820446d8108400c0d1072582084400f41c103540d0003c030200d5448000b0040e69060403801034110044400109007084003051015658181003280f89440c04046d01d2541c1070070070f09006088000c0316241d42e017605101c580c500c07007000500040c0540c41002010070b268215800360b0b01c0645030804d00010042078400c005401c0300030250141c030880c0c00c421500e102c8c03900c0d04021a42940d0307080d5055001c545450400b00290320030f41c3d205000500d440d100400403140e2000081c0101c900849040c018210510204112030004ed41d410f140801d40080d010b600e140142084003000b0300445031103040a0a903103010080d030f80e41c280d00c030ac0240000074041c4114238096a100d1030441c02440d10150248000c0080311462040380406405024100f041c0d6001d058550110703940428007200c00c11890a0500e4201e010b8000f00094001060030301c200070502e800005040c3e402c6650044c0400e0380d041d002e045c01c2d03403010303990103118080a074104404955103000b0080281e00f41045c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 792066474 1250 792065224 792065227
    0xb040c0806010207211101110a0b0604062126131a030114010503101e0e0604021606090c05090c130b09010c03200a06020c07090e1002070f0c030503 65
    0x10000a05040198000381020002450200d4241c00c5019045901640c0400380000201c0e0406c0142ca01ca410949484128890200c0712410080307000c18840c060f600541d4280b200a0301c07400702c800b41c20750380000040c400d00490082d4011076000d5031964196681c0400420601c0036581c4811036561103c91142c82202612508011b042d01c005ca00c030001a03400454035045504001144001e0341079001141d04100d808804204402e100c1e49910f4000c025108041c04240d91050710004056118841d03000660407000004096060500845035041001c2c01d5940c0c0c1d030006550307840020f0001040658400e0a1250701090329101d5203405c1d400303165002e04035900c0d0f44180d20303804c0d403100e035030380020403111018041103550f66004401104016414107200001c107084170386480080000c0320800d1841d100d009200c01c02e0202590090014480440036150b040d51680452825103a0b80111000264003806140781460303555400740c000079200341c410140c0340b0b0454a404040c40c070700340c0007034809400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 792067724 1250 792066474 792066481
    0xc090f0203060f0d081b100204170c03010204140108101d010311010c0c0b03060102150a060602160e0c030901020702031005070806010f091a04090903200610090b040b040c08 76
    0xc0040403510400e00841c0c022040c61800d40e030b2050035008046c40d05609412102200c191903c06200c20100e81564501c21520f403503803044031540040c0c000365018007074010b03840f08000508060080701c050b14124044403281d841118011aa45200180074980204c00c040c004134a00000c03668078040d9240c280d1030880c0b154110b0500d200902c1c03e40b000a410700c0301e01d11a802c0044d01c0e41003410103c880c120315241c0c590b5200c00040c0c0c01c01000e100a040e45035040002c002c0c11160550240341074604560884900009201136005840040d0260017a95950f9200181c075540342c2100840c0d0040748880050b05012043e80407034980312940000c0050552641e04028036580d0014000340e000d6801d02c1d250000a8006101a000f40743d113000f4034040050094007400c01c00042e0045400904894004100e4080242801403521030f10702c0c1245c03190300a0300090303107070544001141802080301c03131001104135262413205c4c07005080019680707800c10780700c5920104580d528420341814811644850000c0e1a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 792068974 1250 792067724 792067729
    0x8100203010f12020f010509040e010c1d01051201120f060608070e0a140402060c0a1e0210080919020f0405040f2f0d0f02030a12090b0c0c09040c090f020306 69
    0x1400b07400000711200d00f40c244002590307031084001d049903003e0821996034242200400e0150144040360021340d824400c036034039202e0307104180c0000c0c541c409e2030402d101c0f202007004581902c200c1244000b150042c0c0010300040c1c1c508030320f6400d01840b5500904541c0015981d90043e10b03070070340c0f00c070303005810401c0204a08004a0400d6600c0000403808000300f201200c01c002e440d4002800c060700501000c01c258241c1c000400400d0503580d003000c103041401080b036200d005900c0034400100d020b80c001c0400d03c046a8016020a40510071a502400301e81c5080f00c21010180810300c0107a0b4001c01c8081a100a62210700c1928000e90040c0c07050317100c1c000c140c01c4c6892040b4480c0500150507180b908c1c0180700a0854040308039040701211035a00007800d27070030000c400030300c00040070b50305020f81e6130f03044c017000340d1303440e01904004594446842e40c942d110030500c03075402405c0460b2019008104040258a052150b0300c0c1e00a22803605110303140e458208107021980d01c80f0a006450b0b0380081800540e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 792070224 1250 792068974 792068999
    0x304030210020f06010f0f0b0702011706040204180e011a0a0e0604150909110303031306020705030c030c0d02150106081810060f0303021908040b03040606030b040b010e090c030d05130810020301 85
    0x184a0b40714160322700740c003a900080c03d42c80c0c40c03504072008042040100702d0701d42d00d41d012a0000d004059208042002000d19540140500e1820b00b039036606c0e010018203d9824281440c111480080102000c113183c4a05000003082c020512544980e407005945801c502102040c409132000040020386002a07182014508090b81c0e01d0601c03a510900400280440344080d04802543c00000541c43d0551403914515501030440700030418040440c03090808600041d07080380c2c0c003035542d08a8200d040412828450442c080c01407000107980f040015180c50001f0001481c0c0c00c4005040341ca484021090324403ca40c107a4002c401c056084040c04c000b407690400c80c820995001000c42440030b8103030364a40b09148214800d1303040718140400018180310240e48140000e41c0c1104400d1486d00d40340c0381c4660402424010181040c03110f40202e202d10030002445540b620020700106103d180700c55041c0c0ea01d8008420100c2001e1030002e0200d900700d000e00c00b40c1c0c0c0300d110030607016880b94104403058481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 792071474 1250 792070224 792070229
    0x70e0906030f0d140f030c03190209030705040c0e04051815010b070f020105070f1a070e182206020721090b09010c140a05010615020304030210020f06010f0f 69
    0x1c0c1d401280e02421030100883d0b245001e405070300f002d44104500c480c4481240c000c0c0f2140b152481004400c105070050000015031042d25409092114508904080d20480c002c800400d42c260384189000d2140382000da001007400400c90074441800c108150025080e583d0490302000480c0303400b00030f0100c00d842001138030050024070090003820b6040a4030903c550140c2d0300c02804c06800c0300550004c0d640030b941107400141d040404004040d0903410302daa6442208407030180071545800004401034447c40d4402c7c103051000b4440364040b81c42150f94240090040d00034001c0318440450b42940403030516490740000d10803480903880d0b0100d800c0c00300e680c065032684150014840c04000d100e95920000101c20344080c1181d01d61980846401280e0190000c0e10040101c9000414035818500c0012141ca405110307000912a05456030980005895203000074000360740103000074001460150048a817900c031620444002c204074030265464064203030f008045060442c00c05100152500a20710701 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 792072724 1250 792071474 792071479
    0xa120617010915090f080f0c1509070f0303020a020405152d04090b0f04050316151109060702060c0a08030c0307030e0c060d0518030409060801060509040210140d05070e0906 76
    0x102884c0380c0c8030000004d8142400400f11003002609100c40c031000d2050b603094482c08000c4030800d003203083e0000c40027074050750540320501c00d100b8000343d24440340300341205032075041e40586403819a550922000e440301030105040c00b00803111079440380e212450704041e01c6030400f0000342400041e1b06e6072842e0b01d02103014207005d2401d2030b42000106806007006504002c00c0c0940324407583d2141000ca0a5016454440320b8041d00c80c4034000c02d010010f01c4401040c090900e00708049404206601e200b4807035202c103150821001d01010000d40380041c00391128003004030030313540700000d1540c2c0d010703569004032040c2860300c2c004414000f8a592510588005c01a454000c1912210907c006a218013a40c08111122a02c40000400b051000000502c01c038085004407034445442d4401c0401601c0280102c1102e503280c1940002c0907d003007003519004030b401900790100e0040d182d1084078500000020481c1800041140054600b4240b19032407003104141d03600e90400ea4007004006502e0b5000c2c06152 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 792073974 1250 792072724 792072731
    0x1031d15060301200a0215010e040b07090f12020105090301060b0318071206090201020f0609030d0e0309060711011b081b0d120b031e0d180303050a120617010915 71
    0x7600442100105082400307040200342c0300c024190007203181628420451130113550b1f02c1c0000030b141d2a80c6a085000d603101c2c0b100e42c0690354030310804a510381c40c13a114500702d0740803002040065071041b40c0f0b1211818018134103140b80c00c03136a101280c00d52311582d1012b0789c500300000030096210a034030a06c4031a884440c01502d03810740342074000381c4060b140800c06002980d49910b05800c41e8001c101200c881a2100113880251800c01055904d0b600001311403000c17982045d1034842d0324540401100e580140c01001c0c07038105201e82d11040c1d0000c080d10791035814000b0a03901c00610320049001e41407158030580c803484d60b404604989800078a09a14110b00c82e50240582091031900204c0c024a84504041c00145048041300000c0c81d14082c581519540c0d110300c0444001e04101003100c40b023201c0503803141880b2007185c07080a5607410040c48054005a81070145190f00751003100090078008440001007002c3d03444005a0701600f0382c002004800369540d400707180c00c0141c4404c228980c0d401c00d40080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 792075224 1250 792073974 792073991
    0xe0a05160311011b0b0f0f0a140a0507030b0a180b01050901051c06090e160b03060a0303110703060e01140a05060d1103010e19030e06030c04090b01031d15060301 71
    0x1c10407440949040741800300030405661014134090700749138642d800203001c03002400c000000c0401710f2026180c141c1c01004100c0003c034140070342d000c0c40003240d1622038442480c4c0c0d0ba020b0035100030b01018102c84101522403c61843e40e43c0e40700c0d00807000d030001001440d02282c80614002c112b440803003040e81031080600c1031000d00d07038018050381c40980b02131000e542c13081d821a80580040005800079280300345032070030405d6405170004001410524220b2a0f480c031030748484800300d0701d0008854880d40112040402e0001038400d80e0540300c1c5002903c2201e405a480342d90704400d82c1d0901c003031021542e41d03600c0100d00300f02d0400c1c90643c00c0049030308d013046035040c440c0204501e5542200041d01650901c084a81a13031002d41c06003003900e01000075201c0b007081c1502d0300528800c6e0b01c0d10030350000c1c1514640c4080c078a09041124020720000740803501d07180c03801040001a11010810b5418960758051f0b41c001400070f000041c03818409400a0b102880903848002803980340948a540aa0b1400c0c808 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 792076474 1250 792075224 792075233
    0xb01080d031a01180312120b1e1c0510141003020102300429251a010902091002010603120c021309030f1413270e0a051603 54
    0x600b0041c40c42844e00c803580c414100b03180d40e0341c811580e200400345c80c1805030480800d644444038012202c036501040c841d198403401082000e410124405070411344c0d01703181309070a280a8120303000b1804040305026000c00c140d00d88034140b041c0880441c05a50f1105402d80d00c40c04482d000c40d90004602100740c24140c04c6800007542d580403c1500c2104000c05031822a001403250b4856200300301c8a4407e0b03030b8031620744001002c4440619404160101c010a05201c086000c00030b8440c0d074640d1443e0355403602c50000d0343da01501080360042c2c070580301110380004100a032410050103005501f0001d69540a28000e1100e08001c880707407841164503205041c400030320311041d402c81302c082924006012a565000160740740701094142040f2601d40360300d0346c08140d0400d4454015802ca500c86035440340e800e644490540c403070036030141c0c1c50341d103000024010b00c1040c500b48200784001d6117540c154000c0b2803000310308440d200042c071882a031100d02900e0401504224445211030202d80340c40300e0a02e50b41d90b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 792077724 1250 792076474 792076511
    0x41b09140a020a0504050a0815010506180f040b03010f0c0801050102031611010e060409060e1003021f02280512040f150c020a271a040203091501030b01080d03 70
    0x70800d800d60002450003a81e4810070603603000d4403006040c8403901d03599841d800d541d031080e1545031010b0030510300002142c1c0380c41e100391810a9400700c000c656405002041044581001d050154895519005000c40762024414940103440c1c81a0010b40d2051104e00a424844140c0c4402e0456004000c092040440400008611a8880c504018000720240140c90711480403a50980088000c42c2c0011848515000034085402d03402c020185038031071640482140004d408080e4011070710710381320040d003043c4101d0480310010602c1a00c005030602007420303110928940c508613030440900319440c10301c50300340403004850b6010341d00545881c0c507240c2e05d41460740c0e0504c40c46c4107190071043d0322220540100007060a580e4002c1484c0c00c41a01c03070180c0c0d070840c2c03c0c08416524030300581d0308190307241d2841c0c4540214182c0614403955000c0d641010000a0360004101d41c115002c1e10301c00c2c0660006520089000c2d43c030038143c0d4651981030405452034016003d0121042608008050900000040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 792078974 1250 792077724 792077731
    0x8060f040b030c0613120308250f120b041109130e06040308092506030b010f1d0103091b080d030212010e0a20040801110711010305041703041b0914 65
    0x103802c9921342591744003101040c80e09501c08200c0886680e2102e0070181c5c0414404d02c60141000719031f414003100d8060b40d81d665180c0c594034000c0f9500031400d03100d40d8041c00019060302c0141303030041803408034440403c6c1503580c3c81030184041c400100c0c011140e403138442454198122403c0e03081041f0b605a00707400e42e0b02c075400b0700040e05000c504808940002401d0150000840600064402ca8281510035540801440c451640042d19020020242d5031140142c0c03005030b00341e0f542e80100c00c200e01070701e4644a0049140703207040c5a07030b52002d18000b416500f1110500210715042c420a6440c00850071f050281104d0507204240c41041007004812000e240381e41952041e660010742942c030b81040d00000d110380c0011131201381c80c03078200502c403118200041040c3c6040000a00100b042e88440c00d18501842c400285401c0d4040c000292551080d4041680035008c0c805000c0c2c0346c407103030381ca005c15680107580030b80d0100f105280d140301c01500d000143d4010850848100440c014200644000c00701c040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 792080224 1250 792078974 792078979
    0xe04060806040816141516020a0f030522080105010905010b0c0d031112131b21050717032a03032e180507020303010506040303050d0f0c08060f040b030c 67
    0x21043c50040c001100070310032851580c1400c882489504000036040c03240200ca01141341f210b22144178800c648007082900c899640014440c12140310b1780da040d94560070071600c10442601c10b88800c1241d0b0040352500000b88807401c00010154108040f030380a48034140c01c007012001e0100140c0304800c40c0020001003854807071a000070400210801d03c0c1c0c003403041450203410452144207205010200306005081e540c852017100c0c29540c04520302e140b0f1102c0d24440c5901b0080d4480003003004c1a0366030401c49005109006449413241c5a640c484442c100b1030300d0201e0b1591010440210015031040c0a6652812030321062141703100c40380880742d580c8002400c1c000810300341c2c6180315010100c141d41c010820004069120310355142d1148000e55158055441e07016402c001c00308602500203c00c0381d041e10b4014251514050442c3c0f401d6a807684901201034000740d64070341da40c1100070f03030380f00743c50031001c40d5a6111b0b441d00381501000042a0004c250380e201e03514203013440340160780002e2416100f1009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 792081474 1250 792080224 792080257
    0x313030c0204110316020714100318020d0b160518060a09030503190e0d05150403050c1005040201020d080105130f140a021b010c051209100c0e040608060408 69
    0x140c0301041c003600111100c0305030240e0100a01c0449007100c0382103105c5004607422110b0341b5944143c0b00e24481600817005801042c3c40010101ca03a100b50080030300d0b440d41c100030401074003459001c942c1c603c3e4a80b00995081c1c2c000c2061101e00309224600c0100c4902d0703450300d10305000c01e40714441c0c0500380300080148205000242000f00350b000f0724103200110340200c1526101e40002c400c50701004080c840c02c40000d01d21000d180c0c0c06180c184500100641c2040042884010407280d100d04180041c01c15170a00c4800d0100c0308118200b0008811348400b008000b00e42400c0c54400a071500e502c1c0b81c0c081d814811200d0040c4855140d18240640105005d90040360303540004042d500209000d010f024001d81202e000c115030904107400400b010040d480030401000c2e011601503080361020a00c500c00a1020407aa440c11b40ac02552287c00c00111416517804442ba4032222007201d2a44180c14086104802154070900d41881808010a1050007900b030ba840c080d60b503000e140c42468009240c0040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 792082724 1250 792081474 792081497
    0xc07033e030a120501080705210313180203070f26042315060409020609040e07090540080307080108071202130b01020c100909060b031303 61
    0x1004404951060303005001148480305041400c0d1640d11001c0c02002140895100f100c00340800d02c580d60407213010f80003a00f409800d100030003010340c00000d140e100030411000d550384044810310040510030343d1018554000b034a00381c0340000da10107007440c81c0e100c184144200004290804500158110b00d464440200d01c1c102c16828800408142044107071030300c0314104005c0141c0c00d8850f002443c0103590100c5544e9001e10582e940c1c0e071105401c000e00f40100d0001c6203003400d00d50003c510080c4020503035810201020042800c642080f030003050254400e607002c020b001030510603150801c0386081601c501c0d4041d41000b11804402209011241c0218445a031900e080c03c0d0b611020b83d9888410982d4a04003014010080d8200380100c41441c042c8020015801c3d500c99402d6022641c090107401ca0b82220000ea00014040c2145d62415400341031590042c6582c2c40b003401c0c0340d00b021a222000300c00e05080004007118102c1e007050014101c100144604002042000710300d465161800e42c12105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 792083974 1250 792082724 792082787
    0xf01030303231b0c0a05060919050d300507120e0a080c160803030a15030b0c0313060203070c0c15020a1205040807030f3309060209100203120c0703 65
    0x80342000b0b00142d4092401040104100407d5084c0146030310303402c80e100f41111030202c80300c001e090b94004080f6484008038521613806120421041510f280c0c0305491003014244002e04845400d1080d48001d65440c10444104c3e0060640c403e08600d80008024402000c03681960360703a58554003810600000c540134555140400441d5410b041c0704500007503040c3d44102c000d9603030f08265641000310b4180104005050f68503070303100003106e41103034000c43c150319807015101c1030340d002070328061040c0401159040814040c2c00118085c0c0c40350340e50f002048065003040700c2410029000242480060002d802c0b0240d07001074181b0b1103641154844980e545402c406640a00c02c5500c901d41c2805400070003c180414200c84407079050050141c0c0c240003411282042445414005032a905d01c2d600b802526841c440341e101441180c81840010728160701b000005400c90340c80b4444800583c00041d8000d24404e284142603040104100d5072030500040380c1c3e019190201e01c1c3c6111203082800c2440081c409c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 792085224 1250 792083974 792083977
    0x501030b0d060c09081912050912071e0b040b03010b09010c052508060708180a0501020d0510270b0a12050a0b07020c0d0213140f01030303231b 63
    0xa60b88004204030000300c181c00074003103444034494440540100710886034070000802c08020850ba100c201c0c1244140b0308101035849402603024960031403412050000b04050401c212000307040082c10048030b070b04052180301c9820f1095000102e003a44240001c10a4083d0325096905680000d00800d4884469800403a1f0095407940080c0c1284120f08802101d500200c45aa8a42074030011401c4040e0322000c495603108000d441d01000184403000186035410703040c051041c80c0b0861410b03265902c45540b102800c2e6006072080c0d4103d955600e0510068601c0090184010074114182201c0760b44c04c0300307460000400c0391a18021315030f00c0d029181d80301d550320210f140243c000003402c1c2081e100c160404613a03899002004645850000004c0764505000260785082204c0c020b1a100741454158280702c2c101e80d091001141503615001d50380303281801080e1b094469100b100d9102e503d907155040c01820340d031ba0b2039103c0f6117410148004034041c0c0c90280f25070b40d1001884400304c042d100d401c049400c16 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 792086330 1106 792085224 792085249
    0xe0402010f02070f170114333606030d050705010f0501031514010b160f21030e030c030a110c030106060306031a100501030b 55
    0x1507100c0d4100030420140e9106880f00a0b07621140130207943c0310764100001c0700d281d1350041221000c007442403420601580c221b8052908203040d8503102c0c090681d02032031001c811014923081c40003045204003801c00c0090000c0003882d8501680140c84124a5107031250101c00d107500a07840020305122500134440103028084c00715048000362000da1019000300d0300c6540300e64402000811600c82d09000314040c80880c000d0b13040c840c0c14402103034100d644441e032106a01005004241080e015a501c500d028441e0b41e81070905410031310050050420020f00d4607290304880f00203002c00801040900c401c3e80c41c10310110b2084100d46840e40164100d25540368401e0003450303000e603c103854031128290002d0a840d041c00b03444011074251003994000c0f0000c80c0d2030b02020070800072000941448081c1b191108603803410407060440010481784079a03030400d91900103440d101d0b610810140903 = true := by decide +kernel

theorem cover : BRFrame.Cov 791906474 792086330 := by
  have h0 := BRFrame.cov_init 791906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791906474 ≤ n) (h2 : n < 792086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
