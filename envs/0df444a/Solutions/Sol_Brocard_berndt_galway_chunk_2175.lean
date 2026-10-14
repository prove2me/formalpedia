-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:35.723045+00:00
-- url     : https://prove2.me/submissions/a51a7362-1b2d-4dc2-9655-3a6949f3dd06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391007194 ≤ n < 391187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391008444 1250 391007194 391007249
    0x4020906010203040311090c0403060c0804050c0303070f020906060f1b0c0a1202040905010f1a03010f05010f09050402030c13020a140c0a110301061d04053304030e0604 74
    0xc040e0440d00100000d002281c5501c80c00c00740e00100f40c4601161f582c1e19224910140070320f07040140510304001f80b4014190380100d81c980168050401da0b51025000002c1654030301c80c0700d80082ca400d001181c400e001d45071440c611584102d004d00306034038000c1034003621801584003c40107909003800046c5103000d100100301d540c20340c900275128201d03403a08214002000c2013460800a100c0d5480b40c05040c10044290450442030b00b400700d0900101c3c980a45c450220607030513a50a000798039108402d10030f1100f900507181283c44c000c10710010681441d80e00d00c05000d0081099805116200400d00d06032607122040110080040780180c6441c10740e03500400110f0803c4080103c0d000c00c0c440b64082040200300c1e400340561041d4120702c1902600007181c05080c5942c080b840e0303030f1603d00e82c2031310445850240611480c0f1442c140d84814a154500c403a01840c40408040550000c41d40d544042d00751130f0103540c0040c041d05000b03012002c0000024510b900c1500240d10301040c40c140001724030140503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391009694 1250 391008444 391008451
    0x70e0a0b091306060e19050906060105030612120d0207140601061e0e06040807150207080a110102031c020a031a091b04090c031407030c090e0c0d05010806040209 71
    0x6100101000000810040700034003804103039908034400307000f0441c003688032000400c10030380714a003a45411601940b0380e130070001000782c2c1e041c144400a040c4101c007294103442408161101030031511001d0500a4103551313480741038818441c2202112240c0b55680c060100c2c6400440090782c0e50207940340005c440b1000b08100d417800e81c0b144005000b41500401c02a12100d191746d807500c641000032100f16207001d540c4c0c2c5656000301c000200803403100c03c0400d06106681d07024400c140004100740041740d541d11184038249154000e4650400003131006031404080c800d051040321b040104000c514081c00103800345c0d540c91990300044158005400d0b0281e81c50300c1c07241c40e042c40703c6198844041074840c00000c00310754000000140c244000094803098402600e524001040706201310305002c0c0040024100490300060f4641c009902603100b03008060307100d101650b405002610f00004144094000f9048040d10035052282d160144c0d414030926009006806c01415242000d00501c241c150000c7c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391010944 1250 391009694 391009711
    0x61107180207020f040903170613020309010507020c0307030c0909170a0c02100c0807020f01091706041a06010c110420040f0b21040201020109150c0e03010203010f0501080a060e0702070e 82
    0x1000440400d40100c10503d50041c22010080c0e01d0303032500000ac41060f098403100d11024404030074408000d17015408103204e1403da400b160540740400e020142e44151500c03009040034103080c400d200ca404203400c405110340c880d0510718443c541c00c101c041400d4201d04c1202e0001402c451040f0300358502000d60301e017006500d0810a03030301034042e03c402ca0544074804020340a0303210303455101c00c2c0c2e0740300b010200c004091b24040c1e07010084504044a490300401c0c3c406840140001c402c0070a090100742d003981c0030340d0341611404526011036452403e6458000d0b20359034007640d1030301c28038042041ca018000c0420b03407814107103a44506107494201e003021aa003006040070780601c800282030442da001d4490100311042002a1a903503840100d000d40070f000700c028600c001c81c41d0011340c408100e40000903900402c1d120f0039440061032042c5800c034002446a1401e9401c245420003440d40520b6206802401c02d5401144e01d684540701011070ba08281c800f0401a48100d00c1000101201d048264201803007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391012194 1250 391010944 391010951
    0xf030510060f03021b1f0c0203120f090c0a12030915050a0810120602070201081e060d0503040308032a0a0c06021803070f08010c020a0b01061107180207020f04 70
    0x102080102000001c0b0001c2c4207255000032101a40d100500c1d03a00b90700480c26044642000c02500038582e1405000035038401c05041005288145001100b926404503511031280840d6a0721106020810f50291082ca140d0041074505440307500c41c0911070001e4000e10780c0042d000e450604d07006121010b203500c4003030440b417680c4034108041c2c2d0020844000006a2400b1b4403552504501c0c1000b100d10350740101c0c40514034582440800542c0e80240000074003d1321514859500c10000d04d08440701e4003c140b054108050005100c0e2030480040c0130390031301500c11a0b040075101d0307585031380380e0348255840210b40d1011030440d01007401d4118141000094200020f09100001402a101c0d2505010003019543c01103041c0140d4034000214075140000181151051550368400172040c034041e0140649950034a030b034000c45c00d8000140022950761281480310180c1ca000340840318140d0900e074000541c05040000600c226601000300143c003041303034005a548005104000c0880c28000c00c143c0103a05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391013444 1250 391012194 391012199
    0x806030d2607031a090c0405240403030f0f0e090a02030c0705061302280918021e01020d030e0a291501020d0f0f120b0a060203071704180b0d0606060f030510 69
    0x100c0401c0e54101d4800769000f42154003540c03a030131440083d0342079278042200040303000014558006211302851036183c98000001c039001200320b03081010495a19041220200401e14054260780207660005c0d4989000b07041c9206507544c107007019010385040491582c08459901545001c00034001c009501312015042c54011002c6000207515070310070490310503030f0ba482c0c1a030000003a601010100c0d034014444100725803062841402c038803c121003e801032040071050308850b0702134030078560044185802029540c040340d031401010414007250880c05054407034038000c0702d10780f954020700601306250b03820341040b2507400091500b80600002410003d001c1070204540e40c0001041c1124156490046029442248008040c0c06080c030305540150301440c00040807903012018006407403081c0d070710005a1031055005403190260340102c50344945000380313050401d6915841007074214000b1304081c0c0d1003903a540301e100c21145681e100002058200c2040f842d1140d15104055001c0a0040c0c4e01c00000d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391014694 1250 391013444 391013461
    0xa020304050a200604030302160b211003060207050601090c02030a1218051b0103052a0d0906050a0902190e06010c0804080106240806030d2607031a09 66
    0x14400409000b680c3d60203001460030388000c0028801e4a005080340d507646036070b850001e5450410981d01c403030580c04c2070b401064288a4804440c0a4071a042c00d15815030b0181d5070682c0034043c041c000c2c1c0c1c080008800b0000c0000c0860002e0501c49004c1d401500c400d6160100540c00e44103251403000c1150020000d0700d460740d4115909401c6600c14100000b80c4c0390700105211858944950058242e11803e803e111800d84200c80c0c26030560000c2e82c0070b0040d40c54510400960041e1410021014001176148c01040140100070303111507244120003003100c03041c680745c070021a0f000f41d4810310070707640b00c201d8079007541000070740b00b013207818144901c030416847e007400d00c0c2501b0300207000c030b42c100b161030326a035028800d0070300c1510040c0940354002c01003903a03210340784081c0b000107000781e4004018401100705020f000f200b9461080030003038007a0001310b0040c841181c003e418030700840d82f868021026020340c10940d4a0152003402d2039200015050540440b01d01681c0c00d040b00c0d5403080728030b8410014940c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391015944 1250 391014694 391014703
    0x112020a05161a1f21060920120a0602250b1e1003030e0d08161202030c100c031b021b0409050a080a2c0414060303070f08090303040308120a02030405 66
    0x700c00e083e05110030100080e449900545c02c066000d8402400e01d500d070824444080034804540e00d80704a00c030344586a403414401d400c11a0100001035811059103200130071480d40003410a40300354503000610519400c020240030401440681d805050801088013184104140e03103a1343c0800131015040740b400019440040603203020050800007228142c08858990014504c4c5c290b138000d0440740c40765660508401c0400d000369060307035580450054504018004402c0b03c150f80d2510001d00442015540010081c3c50b001407101d0400d951490110303a42695105100010300c0c1541c0502100e500110240c00d542080c500e845200c1c03031800000c8000a40300240c800307031340d60307010003a2601c03441407000696a24403461200e40780e14841c44130751402c1c41d0442d409981e9846003100d040005038001d13510581d201c54102d0b8050713059441040f1902c0031031941464016643d2180082c6450441b0b003001007415070704540c0c42111030800225083e44845040c0c2151903216141c0301c811421842d26844480e0399 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391017194 1250 391015944 391015949
    0xf110604091b140d090519060f0b01050708071b05150a020d4103040f1a0714090a032a050904020a060809010e0318030d0804020112020a05161a1f 64
    0x12907a1301144401c21070701f4800120801a030318140441410107080c404054101040c2d003654591034480c014207190b006e04151104560400c10b41d82c240489641c0e5200514a03c540c41201410340d10350006066070340c2d080364548500400c201d60745421010381c029150a090345088402c0c0210f80720a0811160105122103a000c0300c8014503003804142d22650b42c1e00b00d010f041000103020300100b0003040c481c00030611200c00c1d200f00c1d034107034007400404540b0b0f12036a000c0d42c0030310014101c0003072141c10740c4089000d00740c0e0103002071400b200b40d40d0300d40e1005400603d005410104038042c01a0904501180c080b8200804040d80c1c0706180e80380940c0001c00b50889801501e0510142002060b2034040175400805a8803945084903942c6021400c0d4071240580401c0d190f00c02d1180072505030301c0a01c039903901c5020301d6068441040404401400d20060b402040d42101080300511540400e0300780019140000d50080b8400e070707480c0e104140a145070301070040241c060b096054030800c0c0c0401030f14808404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391018444 1250 391017194 391017217
    0x3031324051c020f0403060507090902040503030304030e010210050a0b010e0312090d0813030308060f040b10110a0606120215122206020d060e01090c0c0f110604091b14 74
    0x210b08005220001d005210b491306040c600070502000300001d0307911503030240050380c452107130280d658030780307c030581c4a140101d03074050b0014808600001d0154888042c8010140140d40308040880740c10400c8a2088484084040c1c40e004620025600104c07481c8500609030050800a031060841009502c58607941c180035810b1091113901b8000c005040c0e41128102d410b0070141c45560f810020640c24090318050b00c1a0944003c9035410301c4c1910441070300c04005410030f060311191880540b0112114440d25015004035002c0f000050118400d401c003a0154002e182e40c1108a80180141142c0421054480e20b43c01c10181b000c0d6254184240e6101e488c1040c003041020001103400e0000c455028010030703103800403514040300c83c1340d034200c0b006540d50b4040d81e070302e1a070f80d4070601d00a40d4500541000400c1c8014600c80c041407847c28010f40103405006040d1104030b0401c01b042203584280e01160300c0343d07552030555a81050106070040e00840d0341c0340c060100c18442440c0b83e034170711921050f02e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391019694 1250 391018444 391018477
    0x130509040311060f1012021e01050408070605031b1e03090717010222060912060209091e0106020a0b0c0a0212030c040609090c09230303132405 63
    0x404252040085a012107680b03029540d041c00c0030310029070b000d40c055403000d281c1451a040403404031603d50700d5508140d0001d003031908910702014a0400c4054946050b4100b2008200110300c1540c1080100300400c00c650365184e03640703040d044d65000032608c0b10700350980300e00400001c030340b601100d451103240d0b401501c051642d0740c03241c40c0600c1c60403903154086500b0015417151489160070646c00b074175030724501e0390720001884052180c0345001c03010781c09007034080b404041003404000c50b0300500400c018865078005150400440002e03c020b0411200c800c1d00c800e00014250403008058003607401041240001c12580e54266505422403c000b850256800004a0160783d6680b082101b40034106440c0c411a5503408c08100b000c000d603100f80507481c082050340d000050040e210744920030310508640c0e00d05500300d00303281c2942100300105421090340444950700d242e2503542800144182e101040580501c10302d4a6040035218020500408000107200f05804080b03400c0310880d8a600c04246182 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391020944 1250 391019694 391019701
    0x110702030705060a0201020c0618061b390a140f070302010509030a0b07020f30130b030721140604050604090f06020a11030c070504021e130303030c05130509 69
    0x41b40280203150301d42d44c84e48241c0040c049003a110a0385d00780744042c1d14041c2e41c1a607582290b00c41004007840d50442800d58100302c41d03c003403040003480844051078448003260f01d200540080c880300f00c0d220208400c40d006000c01100300403c40210310f090310005c0014010001000041e5501c074181840040d043c8000001c00c40c2d4903543c18000b000286900104070140e030f0611501c001c0d56000710141c1128580704105001c0e0351a24030300405210b820380d400c2440750000e2440d260307040d160015241c1c0010140b807518041007000e40034000d10320030051552900e003c1c0181d0401160640304180d03c00e6000c5150184d0505c0056840843c07591004003a1800304840d01c03204045402004000c02c044e2248110030a0813040161503001010522010382c0c3d110081100300387c0143c2c03a4415000c155003a60321400081043d820181c02905494501144914007168102d6111241c0d5122141c0403840320160507042c800c140d010321a2140782e40f00c6281c9a4182603400036030a5440086005103489900b0b0321000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391022194 1250 391020944 391020947
    0xf1b1a070c0f0206031305010e010b1504050f10030204080f030a021203010b16020f040c0e0f03120301180f0903030e0d030b06040905040f0204021303060e0309060a050d0b060c030a03110702030705060a 88
    0x10001d1030b1f0380f0400030803420f42c1d0030400170700814142070050b05c60381c0d5400102c25a110f0380020794059800092880b1403058a04003040307490301c13184540d5000d02d9001d0000042c055002e000c004030a903840c00c0030350342d90301244074001d061200c5080d6a000c0454280010700816071240c1c00d0790b001c20810a00d081c109070b41400020820145c9000740c82c1d00a003007144942c550f55120008980c920740913101c03945001058001c050701c9005140c100d081600f01400104401c1c2e102085050881c1c00c2c5242c0003403000312440c103440c240d40140c0c17015004a0f45500c5400d00706c0400300503024100c00145420060860103000080091007203100303100d2400d4a40002c101401444004a654260f0040046660b021000c0d807801c1c0781b860510041e5015803400701e46652a810100c104c440c01c3e40010a41840c014410206617526000340e02c1c03107502640c0d10702110f42e040d16035034024501102444000d5072242400b440040c251803400c00500c3c90f00c0e1050000c4e40068034001200d405075003085807210780340c100d034100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391023444 1250 391022194 391022221
    0x70c08041710051009050c03090a0b0703241805280f0609090203150108151e040308091e0705060702180c03040201030b010314070f1b1a070c0f020603 66
    0x55900b4524030388010701001c42d00e0111464112546050284510355035400c4540c044e01040f1141d07000f503000380040350000b40ba035102c1c460788803d10381000a08448245500306aa05010b0511460b460348424180218040c02a011009180702a003c1c0210719204109403d492180c000d0649000b52455103000c9010700e40d04400e4503017881030b500300030b482e81e514151070242c070f092501070707000b4001d090140e181504104129810313186040d009044942d00c0310b40c0c0c0c1c0c56a42c0c00800315040a02d55840e07248030145081c01c2c139801350340281e4600210b4142402010b00308002d45801b522031500c240c420020080300800c40904072981100d00030340f07486a5001081c0704840c28a012a1403030030480810807022030080141d4003882c001e80c0c0c208090049a8019011a01d2811041280f0800d000002d0440e501c0f032080c08281241d11f190095040d468031414500c0c0e0144580100c44980901c081001c0e82c01c00074490307076445045403070500150b03005510b408032151a902400b9005100010008018601c1101e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391024694 1250 391023444 391023463
    0xa020d020310050f101b080d050a14090a210e060c070e060405060f040b0a0b0a030204090506010e090a0507021c0c02030709020f04050f03010e03130e070c080417 71
    0x14400d6649181c8140c00140b150468000e0601c01c08418500d0082418000f443c1c80d2111059103420300039155502288043d4040700e03000b02ca404104004503a0610b14a0091502413454403e003c501170b2124460400f40f00380061200360b07075520505030b40000c034840d0401502034041d458a01608000c040c0700840b90111901e0721213800400000345198801000101c5104403813144800e41d11903200d00d410041510002c1d500a54001d8680c950003000340790075030000d80c000b0401000e0001003942c07034803000c000780c111a07007035030100c0c4c2c2c0850100607451042c0107480e4010000d01c0d00103141c244000000d8424a000b42c40725030b04642c6c442c0043d0701c1a000b0010000f81f00086c00450404c0d06c48042c00400043d05020201e004c0d005405000424844074001d49080740600120141894148028865540840e09000d030f415902c580c45e00c1e4000109100401140421725141c3c0e1000782005049400508090041400c10201d5010300010800041c00d807015600c070074440c41c00c1e9005502c1040d1410800c503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391025944 1250 391024694 391024717
    0x60303041a0c1506060403020f030115060314010f08060708090106030b010f1e05060a111204080607110f150c071401060f0b0c0d0c150507050901030e010e150a02 71
    0x1503009070401c580750003404400b4515011950084641802c0d880500e2040e2100c640041080c0820b10040c41d00c4405242c011501500000c0c00c0441c3c1f507240408030b159540301e034020036502c200c00d801030120740c6919405049480381c0c50f072100c4d04d0300450079a02c620050111040100980c082030301c9a40a4001c0b000450300503c41c03e0040d6119041480121000e101f440c0100d100501041d240380d04030a0701c0000c80e0030080590b810550385000641c3d089802d403000d042c150240c03880310301c1e0f0031106030013500c050701151000f42810f01e85141d0141840c0d1002c00c1d40b0103190702900010144074000070301401a825074081c4c1b10208c0c3c0700c02c04186101d018a000080141411b100d00d4030750680154895011503a1409000324100d50315039494549114050648a554101102e0000f4450245080350001442002107080000c0c40c078518404882058640400203980081c00804ca0f607810300507081d22202c400020007031280f035003105c5603803036484034821943e40f02c01c11300207028600240e041d1514100e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391027194 1250 391025944 391025969
    0x1a0708040605090a050d050d03200304080c0d170c16080d0c02071215021806120406060506030c09010c03121526150402130f09030908011a040506030304 67
    0x103031034024020f03400400405004904005000500b0b18000e940c10b403805400c840584510500d64504801401e02d58150803540300c16100c504000640d5040107510480c019501c2c0341c4c490a000b50b4503130410800c1d00d0b06004106203010306d01c00b404c0711181400c0d0400c407052010340d540c0410385043c4000f644244400362030810302165444400516402c0340002e15500da00b0f032590b05849543c2e00104001032000a00b00341504060101400480e42c0240300700d00725804611044a50000040c00c590310982d07400b5038042e001c200348020000c05000340b40141404803000380c2146425088581d290041c080d05504006e07182081c0d506050080d001c0c140d0f52072001c2070a00581c0b00c07491b540703550303038406101d00c0c0d40c608800020042c012100c40301c001e40e0842d10781d0241010721114000a0042503002c0c1c000d0782d00450103007401c45d100629124030304514403210f80c0441c1c80d080c241005000644141c3c400d00d602c0e410022000c1686440d4402c0f80b000c0c020840300002d180d00d80718082403440c00380340c000391030b1041d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391028444 1250 391027194 391027199
    0xd050a030f1802040608032a070f15030506040204050d020d02040f151a0c0a03080408040b0a0f030b012d170727050a06080c120f0a0e01050603071a070804 68
    0x1200841c09010f0080d58180006540c07694190b940341308002062119105658056845082d036503c4502144240b2046400301901d5203507118003041281e0100201412000468064136014010181d100710100c604500701407400c2e005c150007a08520009119444c0c04030401c04540e160380c4980c2d41705000584c10020b407080c0f04041d106a402a019000c42c4a60559248401860580485500c042c4600142c40082220f42e004d80300920003a0045510b100d040c000401d810348581e000d09120144c0e42d6541d000324402c800050219105000e20b54100050f034400d04000b510384d500640c034002c841c00328429260003102e20071500414503401b210324401000d41802105a4046003200000b04c0c0c1190b1b83c4014261011951406071070340c459580c121009200411200340a229400d80c003452034864188cc1c4100301040803000b8400315401648a9181014041100c1040c8107454082143e00020406420300000080e41c604144c403541c019240e000040c0b0340c0c18a414410b4804c1c03240c0c01030140b81c03100d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391029694 1250 391028444 391028471
    0x30515190c05040501050309250512010b0d11061603020a0209090c100e0102100906050109050705030f040209070c0b070207060801060c08041203020c121510061d040213080f01060b0c0d050a030f 85
    0x24ad209092040e03000b100000c086407810310851400c0d00c0d0017003441c011807a02eaa242d003c686441400154400c50602c900380e00500f8000303018205500c40c0d405022000c0f03203441003099050019103801142d610107403515200c2c2d00d500780c400300c4902d11400c0c500c1c5440c0e1004c00403480c00c5400c3c00b0224403c0d0601c40c40d8410070035a0f4124506980c4442030a0040f5664110212141e0004607a0980030f10440c5011030090300780a200d180d00f004042c9405505001c0540f1201c6c01c154040c0c81410059100020820441d503000f440140542094a05000c1007020b42c0c071010054000d42c0501c40b44004038448800406000b088010304402d07002e0020400c400c5800c0e902621600d1640c2c149614481e03690000301e0041d08005a00262421030301c885881860391141148295501a903441e0440e80c20010b2107809031018404000406240d0000c1c02c1c80300080b030040d42034034015400070440320742c103100c6240b040034007180350a0030654900d07100352565503450040b00039202c0314100d41807851402401c0030015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391030944 1250 391029694 391029763
    0x6070f050706020a020d030810091a0406050609132a022b140306040e03031503011506080606130b1b010c0903050303011e030515190c05040501050309 66
    0x1980100259529155a444141c2e140c1c120010b00a41c800383c80c280800009010b00355064106030451b41c24018140c654035014111074000d10300400d20083c06050120724a8280100f00141038140c414900706820040840c8040d1103683d22048140d480b04544e1a01200720b00c5000746251240c42c3ca030303403401d94401c0d007e07450300070740c50800c0810802d030116140d0070a02e81c0f030000009581036450030504619000108403941018200a500c241c0300d075001801d05200708051406945c40100a0000c044003804150031142d101500c036038540c0700c5031405c2041c0c0b0340101c41907a001c401034401da80d0710040b40c00710f807628240541210002041c081680d00340342c501c80c12162200725802c0002c10505d0303000d0100340c44142540c8402802e9910400044c1b10310b030f410400b03801010181c402080c10441e00c1e41d41c0c0b01c1c2060142040c3d441c02500f82c6040080e0315484c2c1c014600d46080b55036040208900c41d080080281c0b24500540d0b050250000105040381c1081060001c1c0c8407401074404a840d5041c40780c1042c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391032194 1250 391030944 391030973
    0x406051e060705061602120906030c0d09020409140c150a051b0a0506040221071403070302031f0b090f070c02060c0607020c040c030b0f0d060b03160504050f09100b040b0607 76
    0x140700359a150641047c0c00e104440c0850300080c0018259601e107021040b15502c00d030480840552150204001a100d0b80600f80001d88280307004003000094101c424608004034669502c1140c0c4200c0024641c0c00800441d00c0c800100c0c0b60880d0b440700008820000644034100095480c451009100d05109001c6540e030f003e540308542c141400801c00361071122600894000014907040036004002d2810008007400c614070018003500d540c25506e4000a04046d413402d20390702001c22800440f0780c422103074881c00d22032940468012409040400d0144032044004001c002030041d0308440c0e03000c0d50380307034410381701e0700181001254410301e40142c00a480f5501c200b1000c2c021800c110010503541d000307002e0400c4148024101d0141040101d042050301e440441099a6456a41149440f6500e040c0f12144203e00110342440d40140b9040a0108450004085203a03e070b03080d00510018200c00f00328008019030020b80425042c95410015008020b50095942d2140f00020100700f001414618880e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391033444 1250 391032194 391032197
    0x1e0813030c0801181a151810050a030b0705030c04030b0115020606121216050102040b07120f080402010806040605130c1e0203161505010306020903010b0406051e0607050616 76
    0x13030004181c1c0720060703400010070010100304010041240c155002c0e008258001c0c010201502404040c0c00864241d0341181131955107030405000704140081a1500030000b01000d488a049092460b100c02e00c2212019062008200b00000400c0d04005858140c401440d000031030010710f075a40d02c690300600100364102c040540501c0000803800d18001161000002604000d03142e080d4500d00c28400c1c0b03500905212928103107083c02c0d900466404d1010300054455409404d9845515003450f41b6542001903450080100d80000040000d03404101e0903049a82800c00c40c1c05619410005409007280d600b001e03812540d0000c0c9418074200503041440c81d14400d071550303614031204000020b038840c038007515000948e1007041041907000d4100e0061080c80d025411160920410100d4042502c0081c0e0042d1102600410400520726080c420140c410404807003c10003070f40f926002ca6910190f05d10001d01214034180c86407025200c00c0d04075511647c0c4402560f48600d82a96848005800f0b00310240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391034694 1250 391033444 391033451
    0xc030a03090320070611011404050f0708010c09050d0807060906020901110601081207150e060601080c0a0f0f0507020405010b030f010b0301060c0f0c150305011802071e0813030c0801 80
    0xc100d00304080c0c4000c1003600d60f03018243e036a08001055903000d0030b2240c0101191740c0e5100072005012090f8007a0f004c0d51061014120306070928400c2c81c40c2020300c2d04001a50b902d0300c11601040e940003c002c0084407c251031100d00d000103402c1036440c90103041c0000d030440e03085c002c03901c0421665600130080078000341c982d9450356911050381c0e40c0c0e40c9801d0084081d0341d030042c10060a000880c801410009104d001180c0c030600c07041c4415800d8403401c0014814a500070401d0080c3d56800c0114103501885d05240b9a060508414000386100700c0c8190060500c007422100c2020b042c40340080741d150640240040c0210750350b07500f4515142d8400c40710810101d045200205a1000181c00c40c1e0407929182d44206412800d5210303000030b506441c0045a524051003800507503405440c032290301080c9a43c800141079032410b0140e8001594000b2030102c00c5104110b20700024010940c105044070518800142c8200586041d040d01d108441c006605503404500003c01c002080005000380c90b0000001d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391035944 1250 391034694 391034717
    0x20d0b041b0f0b0409091415010503011b300c0206011d04031d0321030609010509060102100905160f0f05010203040f03150b28081203010e0c0c030a030903 68
    0x241c1214010f03c0700c400c1e020030041007100c425411660f5120300850b18640606c80c81802c2c00d10f01084081d150351401f014600401c210300d02841010502c8400c0d4086003400003240e08000c4c190025000600e43e071840049803001507e910309400e10300349540070702c00c100c44040b03814003950b5104248208030142c400759070081100032126004501417907141c3c039422401c2400c4040d42e04084400d501003905131040780c1c1020b00002404100080504888441d1036a0703050407400e1001225050b0401400707014204103001c450b0740c2c0095040d17241d001c04035000404c0c2503186411820603994070f040d600d12504400010034400e172410710b80800c8500109424480710398841c0103a0b2640560322542c460641151001c00c041a10440035580540e040c0500041e0300044500044c0301016103640700280313686002522510815110854005d403840b0001890216054a003102c11440140214034404c0204808690000740c401e0940c0e06409141c02980e032100e0780300c540240280705c04c5105400007030040071b40c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391037194 1250 391035944 391035959
    0x40318091a030a030906110a020d06050402180f15031005090d09061106150303070b0a020301151e2312041e02010e060c030405041d0f06070f0804020d0b041b 69
    0xe060f84076615031688005140381c6502900c1e940305039907084201e0302a4402c418016075641c3d0003581c04902c2801c000449062078018010213840001c50030010000c24001e11105041d0050326540c4048124590001150000042401c4c40c0c40a035200803407504100c1807204044000c42c012500101542d00c0840d040e0b610314040350b1021030f07283d1a140b1604110007040940d1500712643c454010040c048924091007076540c001041382c100c58010940390301000601000b41120320421000f209441c00803000100c2100d4103441d105800c44030710622518600c40403881e110102150f1000d42135041c90307912030345502c0076068040c40c100d8040304c544845005400f0300c10702452550b05196010303550050b038001c0000520900b940300c2118404503100a00c0001007070f6895000d81280754080400a510070810080e0044ca4240c840703080d140243c110704100442c02d90300280b140e2003d84c045c40e041074251114000316102001348440a00840903480412050203d44500800b055001e901509071140e47c0e0301c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391038444 1250 391037194 391037203
    0xc0a1709061c0b1c02060306010903050f0c040c090617151305070e01030911010315080706051306021908070606121b0b032403101d1212010e040318091a03 68
    0x104c403581c40c141c0b02481000d8100080038560141c010305020407125240d841ba68600940c175003496201e40d00c00911032003d17040070f010304002e41107181405240342d0305102c4080c11070800403a42003500100100000d0802240504502809070302401d450610020100d500c1c0c0603160403508840815030581c0a9032886d4401d200b80902e01d41c01c01c144204100e0034400440c0640070984220080028126000c03030100f8050003c1d20082c00d01d0b84440340d0b600c00000124410400070b9000383d0943d00001524138018400f1860040b0455002c8546030f40d030360480c508000141010b41055424400100303101040100f5464400044d6004118501c2d250b5a40c0c034401200f071000b01d4011512200e00c14401c103601d1000310100350521001019184080310718103a0000310b4400700300f256201e8564210741351101200740002c104130400201c41d90310b06406503101300d44400d018070410104c104030000007000e06116810f02c80d0704080342080302024035a00c40c031060140089031085401448440d402e031030b45d1300d000107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391039694 1250 391038444 391038469
    0xc010504060f0306170f1501050a1a040e01030804080c0a0506090418020d050d110a02011709030d09080d0605010c020d0609140d080a110c0a1709061c0b 67
    0x9640500e02410040c045904400140300302007815202c2c540071130f030000d0600c5084049411003001389400b116100c4030914004419042c3d040ca40076450040c40b160b140c0c4104001034411445030071007240b500c0302d00850b19100301d90213070b28080e074900004000c200225004204440c2000c00302d030b00b207640d004104581c04445215150b03100a0820103c070440c2025001403400001e080041e901c035401c40d07008117010b142480012180e607041504050303852500b042d903040f406401000148400040d5500180060f0321089200c081e180d07422000581d805000c0044590b42c0e820301e0010f000310388640ca01401581c00200030a030a031810300703801240d15481000251510758000300080115403464403001c009081000080c0d0740781c104620709400c0340b901040400038280700c680c0c94100340e1400000280032200b001141000c16031082000030480400041e5800035540c00407104000038040350103005161050042180d0080c1d0003240c50918042c00138000e04209151090900c9034008181c104006e0f020b512 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391040944 1250 391039694 391039697
    0xd0f0b07183c14150c010e011514061c0f0c030e0a0305070206030a0209190f05100f140c0a141902030709050910060e09071e050402030603010f050907090e0c01 70
    0x340080200c0303102108a885100c001400b400f035141c0c001318040b8110b80c000169142141e4550903ca44000c40034444c0445103070801d034030141305d182441100884c421b48201003a21070f1101196086d02c903000402d000000580c044c6042000034906c680c4c9102501c240c171421404285809445844040c0c081000c2d01c0d581d906940e881c0c41c0444035420004143c00140030003205550a00032000c5e16110141c281e07031000003001401401528121040c1405005a0011800f0f011089142c11099412070b840d00c09001c0103081600c9610130440f00d6201c0da002e21200840e10344a014581002c1c4070303032a90203410084035402580d445d403100e00b901d000c90031700022009405070312410f800c01c4011300c0c0e548040e42001d004070a560381507495030f008506984054014210401e01c0005004844004200400c0240250503544030403250913940548036803420f01c1201d004540000000714999400e40c1715114424114800704813500b400240540d0b1203c01e4019868058036003449a007100030002052075910005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391042194 1250 391040944 391041059
    0x2607060201180609140102030408040305070f1805040f0209010b13090204050a030f2405160c0209220204020a030c020613330e03180d0f0b0718 63
    0x5a9444200514500c1d00a48083c5d03640950303a189643c1c00e00003540198000d004041d121401e41c10702034140b002960089402071700d2514200a6541d41c90300da0408025034480c0010030b07a5441c00c0c20fa0558442520081d030180d4203900202c1c00350140d40c050b1591a4020058201c00c6486018590072842a401641c0d0b10a074800820800200e1031445031008071701c540c403140c0542c10401032000008849020414110351031b8070802801d0400c5801c0f03940e00500300c8c500803480c00020340101384182c20260640c007040d42140e000d2a440c4001441c0071720b02c194007610441d914802d88600500030001d044034000103014000c0800d561f280000d01c401c0c0450b4002e603200581c103400b540054010003820b810402c00030903001d64680e8141c0300c3e104d5504001d0040c0044d540c1e03200081840c07483c542103496000d100b400c141d04850041280407180d40c01c11640500000c480d9181d0840540d1038001d121048004142c150801050191110a00c06910a40181c600c80a24403103007519801e51840484c01120944 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391043444 1250 391042194 391042241
    0x10605010e150c1e07090c030c08180c12010203090106050603070215060a210309120503030c0a14161707120f0302090411040f0e0402030a0f0303062607060201 70
    0x402500a00070140e0400c1150450300113003c0145541c0c032801d03800ca0309900004020000300000b8003a144002480d46001c0010006410001d07010880142040703180240c0b006988a001c0c20030802850000c0c80142009007031010512001d002c0d42c400c40d84c1c3c003001d5003041400a109d0030601c00792030044e640c1d50064820740f4030026440c1e00d4140d000b050b550384600d46c0a40042c013411500101c00d43c90843c1000d403000001a814064403881160703004006c0400c5001c0504042440030042e41d8100c48910384007503a414000808036107040042c10009200f20002a01e0708200c0900d42d107240115100f140140310041503016014224051000081e100741011400c01c08114414640c4103140d4142e0b050042c14803441708041400c885d9103500785019060700240c1032200b80c002c02d40285c02040b1500c800580c602e4a513002c81c0c0c8581e01401c0090968000803111020103009070014009003810b800d9a11072a1540015140314a446c0d50004609010b240b901061852040c010440382801440b0390030600c60 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391044694 1250 391043444 391043479
    0xf0d0b1f0c0609030e10051b21030a150803071109070e100207080715030f0605100c0c090213030b090d020d18030b0a0207021008060904060b030a0b04060e010605010e 73
    0x40c1d9840813010400d64040140c1d990740d4003001c840801285a9419884643e01d0200041c0440b042c150300149a0248000d0800031807000e07036190307908601030035480d01c03a115000760401410000424034222341c29901c02041c0085d00102508186000e1010b01b200e20350b026040c01090340381511020000740b000c40b2a0503ca041c0701c41e0b02009105244101e441444e0750701c00c298100b0420350800c1c00b007000182400381b1184c2e8140104041801c10740c00400501e8a000002010301080d01220400d201104d5440c40900c41810410700040c80c0651045d0b5580009603040d252036885804100c0f60381c9042d501007807590400081daa45880d425800614000e0340996003966018410910031541882040000c4009001e40ca0900d000d07180ac9c400158036510306104100103010405034034410080c501082041c00c0e80c0b08036000d600642c02510000d00340700c0300c8000c2818032800c0e40d0301034003401c5003406103c2004016031184c0901c0900a000700304e11a00c039030044841014080840c0d0307124249400040004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391045944 1250 391044694 391044701
    0x160b1905040f120312050a0c020d08270f100501030b150a030212031620090c190c02100914100c080313020306041104200a11030f0d0b1f0c06 62
    0x413402420950401400c8015202c184c500440e41c103903406480300600300c2c1007901041105a500f03103604003181949000c0d0360002c01364080d0480c0100c4a40da20010140c0c0d040140720418984040701c048c0d944480c0d4205007000504403e12080f02e203020b920300010309183c90b1282c41e01c94000000e00080c15503140d9000c005505080c0e040004150004000c1403400b41c01003c80107910038030422074100c010b80c038800e02600c540b00d00ba41c418040e01e00d00c0700300121a0305040440e085912040f4054050081c100e1003150249269440290040d42c4c001104440c3ca41080808003111248400300c48001c0300344040c0040040301305500b0002c43c4c4104d281c10b00281e9102c000e0750780b01c550781c8039401d20401d20343c001074500f880c00d85090328550320321040a9601d00301802030b100c44003541c036000c0781d104a070000c09120903c101140e40d420070041032928a00c03580144102d03a241007090b18501c2e01e94130008201c2d4000c0141040c401e109071078103a424054003600401c004140e000c1a200c005007005543c8901c4040e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391047194 1250 391045944 391045979
    0x6070c0305070b06032a0a0b0a0f0f051e09090a06350a080d050c03040b1501180602011512020307050112060905010e041505011a0c160b1905040f 64
    0xd8043ea034050b402a00d102014200c0801c1c2010741e0406d00c89282081c02000c10f881d4100e000080b50800140034059040110255026410311344603003108000343c004c44241c06080b00c1c072005117009141144801c0c440310054038100d54100d0345418079464082904048941e50b125550458042e070780303825100004600200745151070402d404102250000d0414107100700e192080f120b0031408280480c1903001e074410146d01519014425240d8101f80e00c1c0ca0700d10407001004410b89401000c0c0c009400d0740300b29005c0940c02001c9011981454a8002c06030203014103032036140404103211000280c540004481c1000c1e01d802401030595582010011145140071818000c00e0940b224400111a152031180078000c141d010003500c0c407400c0c14904007149071026102c030450542480010b1150710000d8070945101c0c4000b0f29030315a030b2201103501034180540381012400c2098a00d070000ba00445020050440b0a14001341c00c0c8129200702003510a400b560040401d801c2040401b4007000341da901c0044039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391048444 1250 391047194 391047199
    0x160f02010b03030d1b0c02031011070f0303060501111b060c030f0d0501091409150601090e0c0702190b0702010e0f1903060501060f0e0603070c050d05030906070c0305070b06 76
    0x110a2007100202c3d2071a03010710504501c840d5070b00017180c0c01c2e5090311010f48191116103490340103d0295000660b81c1c3d07000d88500300040b60b407503500c40d022004420441d201c441d80110b00d16038503201420040d00a004c10710030540490814140302079151800320310480f07420710b04120b0644c42500e078000e1040a400c54401d0401c28071007040010b045042c103d001e010784000b50107001ca050f606003959030065450100401a1210300181440306c51075002c03488602c450701c2c0e24864100e644d15800121030440056003e038500325201000c0c0541748100760014012a8001ea0700003401480c0c00034004901403c5c3e2181d46c40c240d00510030b6000540c4034800072a60030400405c808408081070001845186000c3c1043c0d02c08620360310704104208060041a00401c103e080011003075441140240032224484005446400d0005c00540454010507090121607000405c8428a4505803400f420f607034410740d0740d540e00707110b280c0020301c05078455070700d24556907070594409052185a07034070140001e502070411075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391049694 1250 391048444 391048451
    0xa0501170f041a010803090109140102030a0e040f1515051201150210020a030902011106060d020409060204030c080d0e04050c04060503100e091e0a0206031909023006160f0201 77
    0xc0f008240540075800f03448083c002c1c503030b5030344000005011000564010500b0481c00090307041c4c3c0c0d80e0048150703800039000d0b00f81480fa4038200d20004001340600b801302c100c042d1600e55200d20030b00115001005652020395102c444003c802000e803a2806104214400d030305616005001030700b40004c21440346100d40c0119481c0d01118410b040030707a00000480342c00240e54400b1181990786c408181c1d441c4114980141c0842d0a1603c04510441010480a80102e45030380d02e0800304072003581241e00864201041001058a444d1056220303219880202e0026190202004c02d45c505072044502800072107840500c0c040c900b56080d5441c1d04010110030210412000004081c80d0507185244108440409000c403400c1b0b0b51803103450300d101c860003102d40b64454010000140c5507501220f0b0811070841030b00071507404501001010748202e40c8000c0d08004408010300400180d23300054440d445400440c2045042c01451a41c1e1038017201d400e40c00d282c6d801c110000490055822040c800501c2c400030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391050944 1250 391049694 391049723
    0x1c020111070609030806090106120b22050402190803070f0602120103050c0a0902090609210102300912090406030812070f090f15200c0a0501170f04 65
    0x4241540060700c040c0e403669110000d078002c05510043c4a40d0110084139032405d07550400e20010441041d4a030b042160f166038a2940720f8075030310390607034044c400320184813100801c21513940721002d0102034804a00a000003a0109a208519400081614007600045050003ca9144c40c0c0c4140400c1c0c0c070070b1303034216400c205461007080189a000d0103580a4001045151448c10510208500c140d10120030544140030305401961648210343c02d80d5030807a41d091010900000c401c1011018500c9120315620001d000391100d01d00c8085401818004880082805601e03440c400c21200102c545c0c0701c65401015140c50883c01c120041c0000120250000503002d031a95941800f5a011440c00300c0342c041407500b000038559000000065107076180c94287c1e1260718213450442900e4041c06200e220002c1d00c0404075100d881030000d01c030300000c103881584145030782850310358860011141144c00b42d048107201142c070f03501a0008020044850a030201c40e40c5d100804c01955000c0540200e841c4070082c1c952 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391052194 1250 391050944 391050971
    0x6010309021f0e010e01170405030f16060605121f0e030c0109060e070b030c07060b0d08090a0506160f0f121d030a02010503010b030907090c05130b04081c0201 70
    0xb054101c0d1401c4030200b04060b0214405401400c55000c940d040202c091801c1c4c0329641d01c015a02c14a03621001c00c81c684e038880b45081421801000040200080c020900c20f0342d41c18004480c0d10410b005000402085488900348054103010996200709035103c03081c511070008820100e032107120b08902c000280c1894914229065a20110301800c05039140c08854040c8140b920802c1c44040d40310000301405c924044600080e03000050207122029004100481800460f420852a50400910490301c4800c02d00e46400e66400851186005441440000c07070715092640442c2d20490960080703c804001d9965884810001070404540014100401400107150396011010109450300d07840c91500314541403030403101240400354406c0d8860b420000140c2d030040c3c11a81900e2241030003030b43d42d40c0c0380729000d0b00c0e080b15a0300440c0e40710701c3d0525613407810b0b1340980a01810204c2405020070342d81c2c0c803110b643c1d40b801607014040d500e400c094841c2541003130000e854003092030140000b01d0600c00f017018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391053444 1250 391052194 391052209
    0x1206110c0c12060103050d12020c061e0709300b01090e2a0d050a02090a020406031d100c17240303130608100b1b010b060f120601030902 60
    0x842081d801458815100c0c504244445603414800c0001c1440f985592511a0340d010400d11120502520780013165181c1104d804131251800ca120481d051800c01c002c5104251041054050820491030085404c60f03104052000031216079428612814061044250708035455034105c0314506110758801300000d0710140c2c010b00034820000001250b0740307c00d54050401500c0d860b490402010303105100c0c04c80c40ca030100300e40c0c111001d075003031f00301440c03140b41052411440a45c0039600010160400c00000390303a40040c02034848550f001d000c07050702c8458106040d01030780880c90054010352200414651603500468454400e842c02441d03034200c08c000d01c0300c0c80e1000d46608111034425845280040300c0c09040207200030046c3c0095140c5101c8104e606d0074620a80152010000d03071101048000c7e408010303185c040c042140000d961144414000002d00754140c80396032aa50a10031441214035004095404086c3c0000c5200d1800342c6a4840c21000c00008140905060b030714028040542c6032000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391054694 1250 391053444 391053457
    0x1202190e060d060e04110a06142a010c02190305070f030513030501021e030f13030905030f0601050405090c011428080702060c030c0d020f07020301020a08100e010e01120611 76
    0x142201303400d04046c00d02450b048100c00c5441d00441c40413004000e0b450307214a4a10841c5046020162103c0b0040340c0301d0f065229804011404292180d5260801c1106520400e05c0044640840d03110210441d107001c2200b1142e540500800d01c2400080007080314181044113141c46482c1c203030b207499041388164039041d0050300241d440d698042a07603c099002c080c07070b242d20900d003410458110f03d0b117010200e602c0321004143d001d20807680010403081501491019000d80310080644040600e40f512041e0350314030034881c240c422130a1002003181403d0100310082c040300d040e511159810024803860b01a540116441c100100f8840c030140b85011008190b071402003041c1e03075400d0840c02d2281000b03107002c401070160500081c04200303008996600034200d6000900c00340001d40c40d00602007524140b03004030400a50194000200f00000c281d11a0855229959144c81e45811585800c0100d21840090059244100380580180480d00741d031a2468440f600c160030120300711001c50000c031215007025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391055944 1250 391054694 391054709
    0x2120106091a16030c110306010611100b01022d060408030405060f07091418010e0f090d08010e06060c0a0b09190b0406052e061202190e060d06 63
    0xc000384480300c1d901c980502c1656620703030100e0501509081c41d4400041d40b201c01014807616410210401c459018110100b06000381591855a955800504811500380c603401039801510016201840c42e4813800c196000180d004102d500c6424a611070201c410014400b01042203001000c00007004206003440745106035201d98403401d1601d03081d0b2600801a00e13000c0b003c03081c3c50030440001d502502d600100d0305100c825905c1a500d10010500040c0412003140b00c4d03100310000030500e0018800c24500a980c074161005142d41c8541e9142c0d2114282108900000c5a40c1e00402c240c01210b0602904840022f040901e000c2c5001c441902d810324a0100f1030369100e040c0f04102c1c840e9024050b035012004902c4031003e41c00600c2da18a40d03e114000c1c4028117166541010408400a4140000d14180700d0000c40356819210201102e00d0f00380351050000081041c03103000c03000e0049000ba00e210714440c0c4408810304104da441a29420b000c01d0115802031b506005542810030180140c60060100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391057194 1250 391055944 391055957
    0x2041206051317070c090b030c01081f0f0303020d05212805060108130302030706020d0219020a05070609081b03190b27030409020c010603020904030f03150f0e040602120106 76
    0x158504100501090361207160b110741f0704552042c0d640c4003c2040c003110082441c110f6071980d2044030302005440858008001d07c000c044011403c08000200782058074000c0c0c0841b0401700440400721390344e10502d14240ca4024094141002c140e0b00e540c2001d41128502c141c00c1c05131070140c14402010901460442c0304151100103102e560750708040107075005070411941d00d24074121078030040d560f40b003810170003000e260b4001103465410309242c0c107503031503070074a0401c07500e00b24407d10f0000d66600d00050140e401d402040c07400255039020788200001c880102028103140249002c00c0e0001094848904d034044c015076149440203508210458560361245190152500b08100410401d407140e015044018080388414a00840000266011504480310250b0f0343c0850000341800740ca940d9200a4000006c40c003400105500044200010005654104008040d040301c920003110207210346100000384690601440850358080e0b54880d00032000907240c51104403242107001000d13401003002411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391058444 1250 391057194 391057207
    0x90c090c081503190f1b06090602010c0f090918060509031804091e0c0504060e150114030c07110604030309170a051f0e010606120e0102041206051317 66
    0xc100066072200c0c030550042050222610820b2400c429001c0003501a01141075000204046c045e003180c80105e40900b40700c003843e03880c5030140103112603028030740141d42400075180d034451184841ca50f001e2001d5448040c3c1e1450319002c20024180420070b41440d40017500030b08041281c3d805440e0180c0881c00082d60383d0030420000042e07480006002600c11801c002c5101c00aca00c2c040c5582a021103041c5840f00d0320401340c90301c41d801021661005400130304144001501001c0e404a1178494032441c2500c50340c24003c580111101e10303580760034000301041440407412a56140c8043e001052140d84010403084d02c000005e102c80e0000e62003240014501c01d418412490511881c01d0515400001400e82140a40c0c4084c0c60710021101c03000b2401160800d4854000e4070380010140c461050020040c0944460005012860b44110003494904202250705140c205208480031200100035142501d006a034030500503040151071040c91030010120140803e560300058003101c0d01411b0402c1d0740301c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391059694 1250 391058444 391058461
    0x901030b06041a03090f1006050405010b070506041502160803040c0506030c090f150c0f0c0315190902030303010f030b010b04060507030315080f060103060608011e090c090c08 77
    0x840903116180948800e1004001001c02403240850308582501c1c140d440c1d075151114240b8090001442403640d01c01c00d0b2401142211070703032058042c0c50094805212683e200c1211021900c181000100103900140000d804034041c0d00c2040c036550b41e191741c09031a080460102903508c080720401036561002c0081440100007210100b40300804007510418298640402550140d005441c6514054002d00c43c0e4000596154418464001c444405441d1a0002650200d90b5188030142c0d0400314411040041464070300001c1441c080b0b4106e40c21024a69954254460a9280c203d1502541519103600310700599081c00954003a040b185800800e2918504101c5170040040c2e1044a500300e00b00014407543d5400b02c21510340503090709012620300c2946241c4907120600d0342c001401805502c0705401030100100b000f5040740d0140600344407403625008400c0c01c83c0c207600b400c05070000028a410b4140f220b030341c000b40420f81c0601c520b81c500d60b683d003410f80c054801c0f034851030b00080c01c41c8082201d50b2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391060944 1250 391059694 391059701
    0x62103210a05100b030c130b03060a0503010b0f01140f0a020d02010506010c08030402012726010b01210906021b010c090b04090e0c04020c150117060402040207210203090103 76
    0x152004010321803410f2540050b01032000030f0140301e000c0310001000420410040003104c0c01031641d00c5020030350694810f9007000e140c05c00c0d5030700c91180d40d40c21070000f59841d05019520808400601352901040e29900540d11094030321020b1000050522104101c180d58402909001c0d8881c6c0140c044c03020205002030854000410a070f050003c120700031008a600d076000d03079a01580c2070a201e804490351540780815410603034450a00081500030100c0c0088601d18400c81c84c1c0751080c1e02d0301e0307000d4003086140d003a90070300f00c6280e000621543c5010002d22480f14100e282c5c150a080c0042c0c061401d85581c42030341c0c000e50a05401003d009001d40c0000024404c0301c4104141d4601070000300d04100158245101c1c07031140c00f07400e9807102c0711242840c1c0d0a10030b100174850014011555028000f40040d02c40f80440e0101c40c000c00e00e04000103800904c030b461410400c803801c0203441c04c0e54660342000000e40203c1c01c19154180d64250411807248141c45447c0110151b800841e100c0ca11080010305a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391062194 1250 391060944 391060951
    0x11040f0902041b201005090f10061401030605060a0e211e0d0f030c050c060405150108060708061903060e1c05040602190201050f0a210603030806210321 67
    0x800940590400041001040003880040c002c0004038150311041a258944005006080c230b541c018042500c07036155960744000d003100d0040301d83c4100c0e001207000540803200648600c64001a0420019150510580d00c5509040d0020984201803602d000c81c0c90047c4004041c103211607001030103900305028415551841c40da20034004205200c52200020042c08512080d4410301d619000d100c40c1450003030052320ba034078426000320360183c40c080c00e00c82d039100801300d04810445a0400049200e82001c9886403192030241ca41c2c4032141c0b00c10050210003240301c0041040c001751103101100150040c00f483c0e07001203a00c401050b0501080304401904200d5a031100d0500c07104010400c8000e07004107541c4003c006201000009005c0c900040c0c646119520268084090000d0008503036608446841110280344101318141d42814121000300c40f040c3c08094049801100091201d00d004000c29284005d807055400301c410714200a6860f5401240c4a41050010741d18820112c43c08000c946a2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391063444 1250 391062194 391062227
    0x6070207050609031b1f1806050901080c09010e1305060108070807020d050918160f02120f0705160605070308060a060c0201110c0a0b0405041811040f0902041b 70
    0x2808903650006070340d0717200342c2c04051198140801c02c800e0a030380f540843c004251050b102041e101e042c40c1002043c03024907060150b040c0e40d000901166141c07240341079503400c00c81a11001041e885690b41d41c201900500140c9042041300c01100203a03440303155a10b8a9071444500c085400c1c10500005801014002c1805e0100800c00c0100a0001d5000175021400201420400c0c1e0350b000840104075060b0601d49446c0c0845003400500040b0b0000d40340d8400403d446a85940c1c0404811900326221000c100c92194080000e1120120498601d801403507118813030b2040f41d602450680f40e6030134240c03140d4440070100b0700c0403a1400c1455008000994031410071121444513070b007446005012861030301d001a04200d400a018003042008110b802585200285100310a565890003a60b0360f40c0180542402281094002620324112201d03c3d0034035039001181c0703800c001c803000521004151100b880000e080d2a81004400f588482c80b0f02c45465014803910125165800ca000e02105012841e850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391064694 1250 391063444 391063447
    0x9050901050a140c070f08041401021009210e04050405030319050c0441120102030708040210030f1517030f0f16080d0603030306080705033309060702070506 69
    0x500d0708448940f01e61001607000c40ca40c0b83c0185040c075081c05c969101004040c59000140171400507090861000c0c0504268201c48030042c03544034400c01d07500c80300c9000304228a00c0350081890200500c04a031074000610300b083d8260020800a41540e90135a015940c58000000f48902225210300a0908200c103560602640c2880c0c81c04210502c903078480d90003450319440d101c41e5814084200c442410340b034410703c44070b0590200f051140c807880041c601807266050203500e020560040c02a284078000725121a60107a07101d809104c01c00952404480801d030351045080360306100c074440d007400940a50300d82121541414288448420b02e003560032032551081c820040003565002c00ca41c1c8081034851600d4031a07800d2424401d00451054009041000118006840240c140c1c0144112802584e050040d1a5100d1441c0e0312a001402803941540041003207024036900c4100400400314800789880c1c2c407190400c0d50001e140419200d405450b0880c800b44206140c3c10080345000c5c040486025 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391065944 1250 391064694 391064711
    0x1090e0d080114010c02100305090118120c022704050d1e050705030904090303020d06171005180610140a06050d050403020f030307020102090a17030301230a09050901050a 75
    0x500341c00310521411610f03900400420a150348111184111190302400100102100f200042d01512080315409606e43c03030144880a15203912000a05540e0001d01044003040c9080c0100d03600341141100740c0c0c1002d840701268440840001580b2521005820f50240c1800c3c54503006007807584185440041000c111000304403420b201000c40703600c4080341001540d0340054a41380741180690742d1425401441c2c40c100006240d095002000c6129031101e0402c0b040d0340b204086c0e51442c80740c1c01c0c04990340c0e1100706012454a0700758010f2360000d8500e90104a10101c82e038205203003c170211000c0c01124008202000040f82d80c80041b030142c101212800c4180781094030040c51809200c0100c0b1180b621807001c03805041c000d11481d005402110260b0fa501e21340305801038040e501c11940c4078010709038a0400140404801d269850201c12000130318a164078204e10300c120481060301070b101403222518440d82a41d10b12440d10700421060002162904d042241107013100d000405258a441c18031064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391067194 1250 391065944 391065947
    0x3090b0f0306090403120903080f06040603050c1009080a0c03030206070f0203070611090a1e0b030c090d0302070b070b010e070219060507051201030c0807061e0c080c06040b01090e0d 80
    0x103582c0e00c0041521201015641d60808841c030041000c01e030343e04149003d84c071105041c2d10a004500c500580064000c2946580e41400100d038003d01c00a0324a0700b001141d0079092400704200c005000062901070084e0351180c41c502d0130f02109100403200810203240410030160180b00882e8031030001d0804803a00d42c51603078044d499104500e00280101e030b03035203003200303421200f1425503041407070191074405d6168441c65001c0f8a6140e11320440b0140800031800252194038804a910074007441030003e040c04500c0d03050080c0300403888070072015402181008200d20f4040030182c0840343c00b0b2158400b180d4500260400491030151002045421419418943c85807200c400541c00360b0004000503681e0740c81904566500681005140c0c208216000005200d01c500d5054180c0fa00c000a4410140d903603801500e00351808480110002140403500d204103005051201d103e6000c0c04903249409002d03030007542803082c201d80031101d0081403401408070150314801c3c1d8001c0e40301c18004040030540101c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391068444 1250 391067194 391067197
    0xc070302070605070f0813090e0c010e060d0b06280c0503071b08030406030204030501060e01051804061409030a03060503030c100b1203190f0c231203070c03090b0f 72
    0x28010600ca40090b11504100720317500c82225894004014a1700c0d0020300011540944880c481c08081c40d041c0b14036144220b90100c1d60f048510030584405410011074011f02400ea005040d202180c540e072080134881e9038484000610002001c094010302900c1102d010004207410f00306407108000203081c07290000b81d00042145c070140d4010140f4025140c0d41c41c030721007141c1c610f42c106081c24080880c0000f10306400d50007400070b5034403a100030b000507625801a080710090910500303030301034aaa420b402110030000c000c5500140103403004500d140c0a01c01b1005c40000079104003240c0d900026030403001543c14030030000a000110301951800d0350034802542d0321842c1d144049003495588000c18065078950070015000303000c00003643d449041502e042c000061018006401003110850440c80c018030442d914107445501c4800184404800145c1c8c034010600c10190210910400c420f003072040300400090340c4a46100d43d241586030b0a00d03d030003055011903510101d5450804d00013542030007803010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391069694 1250 391068444 391068449
    0x30d060b04150c060902040c0c0b0c0a0905010c060b040603030e040b03010606020d26090105040b0a020906160809130219020102070218130818010f0f0f030f020405090903030108060c07030207 84
    0x5407290f8241950b04144c0300418407500003d60003490072101c40c180c0794000141e408034501654102c0616960110340c000c0707601c6100320440004540c000140115809841807012841c0116030000d0340701004004034003180c880d034000780c0c040340315005400f068ac40c0c40d0081041e888800d8000744907031850003030301039500d81c0300f17080550a0184070090360402c202c0e04107004075007400b031161070075503030420360100380c02400300380d4040d07541450044c00904825514021603078003060240607280b910400b80340d0340340d00d080a80f008880342d0b04100f102a600c1d44d1040d800720140ca0349240c2c0180d80f0544801e1408010307010312030b15400c0d0390050106502680e21800c030b0201d2140e0784ca03040106a40d99601e1401c1d0741c4217072034000703015840125540c1c1c10346045443c0145810420307214900c560340410810358204a0300309021000404c81081d00c62080e201781c20208180400303600c0981004d444030006003501404548065083d44007000400800c0410000035401c418003d010750300d0040103440003500c1d10101e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391070944 1250 391069694 391069697
    0x30c101d1c032d090c050307030b0417040b0a021e07050607121e0201021206010e0d03031a031b0a090216060203070203070804230a06270e040302030d060b0415 70
    0x50114081c905031a034140b4000701007000603003d1010350200e01c5002842540f0064415100e80c1001041d030f82000920441600d030050f042d41c0c3c41d80e1b2150303140c00c4000410b00511500007814000015404034880142c408800241c010f407810030741c022140300c40c4101c03140800601d0362000c40f04006640710f10f0103d841554000d1142e0140d4082e011040e1140d2550418882500740007201c00c4445039410b5014000c0c10b400059420025140c00c001103904d50703041400f06a01802004951000034000e6000c019100c806549040e452007000c0c4c002800c2c4030252030305600d0540c0d2a118080d007841c0910a03403000e00f2400a0031030034458804005580310780c003010010001c55000001c034034524000c0003511711540d889004079507a1a2154500d90f10740a074000480c44108082e03490800380e00c0d005c440c10b0151001030355003014013001c80441c800f2402022028001040883d44003051809600754500d114038000d80007555100e01c0814a0300890320654068088840d040c00b084c801d60301c0042280c046900d41d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391072194 1250 391070944 391070951
    0x606010f03020c010e070e04120305010320010e030d031d06130305030a090b15030c1e100908010f1506030615080a2307140405030a0b09030c101d1c03 66
    0x110480d003401001c5017003240515206000380018481c086080b0313580300e18410402c040c0e109c01195425410b0303400c00c0c0801000040d00c5803c40223600c20f8002d12142000e4140342c050b40d41c5aaa4010030300b4114850061400252a0411001a00d0030b4032402000303204030000501c058074104c83c07640c0b889104010002c040200000110b0150720403500a07180c800c1e08940b4049031410403407604200145551005c0d4000d010710f82c01d0312400d181442d054081c5440c0b64034881040034650040001e200e5165803583c05100b010200800c92603c01d1040c00c090b1101d40344005628090609203400090b072940c010010181412410b02c941c03415080004203824a504200c40a0b44414512340c000e000059400c1545a000030301c60354030b01810010741c500400b0f0984848002c50b00484004820f84164022240c140d4000590040050300c400c0510b40e0024040058034100ac000c1c50405040a10207180302e04a142c46081040d03a148100c0c0610890059a40080c07030500380802103840d542142d1200c26003859907 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391073444 1250 391072194 391072207
    0xd0204090206070f140d020f070515040f0b07020f1801051012021201140303040f26160905071103031b070218010509060909060609040507050607081b0a0305071b0906031a090606010f0302 82
    0x380032090b540a01554140dc4021351303207605201c20303160401103042e481540400554903142c100b0f510320417551140f401c080516a0700307020500c504464581c00c81410070821406699a0201900c094880c10307000301d48502003949804c4c403201202da003442125100790810441040008421010f5004072452900074142c0842204000b0000c070791008000f0545015410510010310365542d1400d05071101d0302c03c100080d440b54041210b00140d100007142803503004001055048a11880185c040c038803030100300b131420300d4980c0840d003a2201040142c400080200040c0b140d840e01c02c1c01c142e40510306940b018a14039006255964841001d00110b0041c0c0c001e0b03001c00c0c207001d410701483d4013070302e03026007501ea0360080ea20342103065600c007050a2255032488501ea040103040410410744c81a0941d4503030b410a5199240d82401070440c0300c00c0254084c19907070000b080c2c80c541c014500110301952005001600003203440740c044000601002203500b0610400c00e06a030002010800340032280380040c0c4035031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391074694 1250 391073444 391073479
    0x90615010e0603191a010c11030c06040b0403060e0d0f030506010e1504050109090b15031008070f0323190615270b0d0204090206070f140d020f0705 65
    0x401d54054507030404400800c00180c0d08840541980d0580070f130342c0410028400a1006400162140400f0b000903204804e0b58081011510449117812004060361281d9030405e00040f03c0b5481030340310020101d8007180400510001d8403d1084c1c00394458054007203008021001480851526032840c1415600c102250480e4442c0856032204100030301840c0401ca582c0140100300d41142c42010300088002401080307180943c000d056250101030314503000e040e00144012180c1d0001400c040d00720803041f00c000307880303001080a2402058040403007081d0a0950400950001c12030444030b0042c4000002c10741031210000300c4050000b2488a81d00150072a8503003480070305000403480409140810010996001e8104074006652012580900c840c1d840d00c000415500c84230b10141d0310001c030007401d1000d81440d8101c1200b15100a040621303000c00d82d41c840d12140c408103003d5460041e06000600c005404108900074810360380000c1c040980d02c504500c3d592101e07406410300030f02c0100c0c40d611004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391075944 1250 391074694 391074707
    0xf1b23070305030c0c1504080301080d021207030822150606050c0d0e030f100507180311010e0120150105040b130207020f031f0c3e010617010b0909061501 68
    0x1442c6d060201a010b09050804e113115400a00690455014411072405107a0000590065410343c10502a090048640f001d0b68900303c010401455000ca0103440f4403040880b600510390144111861070f1441c02034a01201116030300c0d00304c8002d100c0200421b000d209400100d850040312a031030320214800301d210100e420501d100c9071b40c03d440d110b146000c020030000c0360410741c03090010f955070705c521116441c1002c00c0a0700b00e1002900000300000242c5d25540b2841240b4042030040c1090703009443d650494440224448201205a400c83c420000c520840000c41a0040100700c500b0302645000200040c0c0b0f45034031413401d03000d180e80002d1100454660903208111418003c05481d03000a40c02200300410044031001d44640e46860b0314040914064000042000d1302017540c0840307081d004001880c0c0d6051600340c0350b040c04120301e011134825024024040074000e0a034101c210849502d004500b5101d400ca42907200b11028000c002184074002080e0354000030b00e42c855217121a0040060f6170a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391077194 1250 391075944 391075963
    0xd0212010b0a0f2417040c0e0114010905060415082d01030510050403140306010212181302030f06091504050c030402030c010305100501030f1b23070305030c0c 70
    0xc6501d1050006040070303c1040c0d2011504841a951000d071141410302892402410310840410b403e804012401c0c0c0e2003815080d4098850034003094000d48540c4003280c0054242d106d41005003041400001d01e5900c13210400091005403980c0d030403c0c4c14800081003909609520b1010040c0000004e00030b006012070701c0c9542c0700e61002d40e81d80145d55142100c5210802d010a503a11310139a100c03c2100e0b9941e209403881290180d03145000702649401041d900d80c001b4103140d045100303d1303490b40300c52154203008112100591981000030b0030500c092016001e020801c010b0b0340c03403051040202c061a54091550300950844894450356031f0b100b228940d443d100300303025400624100410481c2d0110b6002540687d000728110b4a030560214011000c0d14412540072a184200c5001007203a540240c015108000c01c0314004103011851940b1f220070300c1658101d40340041c0c0310b20045599050020131946130501c00342d54092901182d80c0740904144000313400c42030344d0400014080303001c81d000e0001404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391078444 1250 391077194 391077199
    0x71b031212020d09080705120c0a080702190e060109120b01122612060d031e12050903070c0f0e07050d0609020310030b0603030406120506030c060a030606031a0d0212010b 75
    0x10134842030801d00c3c01c5070480c1c2012641352203900309001014045070300740c5161061003070042c0851402030780c1d1040540c1080c001281c0010816004c90091884000018003a144511401009140800c001010b8200310750041814214040d0700b40041140303a40e0940c1581d1500c40d403009440c075145059141320114103080d00d044d41c3c000d03030441c007410516402010100c4a48001401a4654070b003000509005141c00501003180c0c03a10945200007080d410b842c1c4a6500e04151090a005060341000ea60040300c002e02e1030780001441d10200802c03690044080c08820040d54130241c103000c061240c140002c2c0c202c5041c4070780440c01d02103006840e00084041c2c500040159140d0410703050441202019000869241c8459800070310507040004c2994211651907403104180c1c651b1141a00003050040e0170740342c060090040000298546000030f2000348401d03a400030f1403604d094401030440b104280d09220000c5042c41609080d51584d11185840341c044841c0299400444225801002300340c0c4001d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391079694 1250 391078444 391078451
    0xb180705100f1e0e0405070909020c1f0605090c031314060a0606080615030604060b0c03031021020907020c1507051002091815060f071b031212020d 65
    0x5501d50b4031800d030760b01c1404281c60300d6002c1070f42d0b034850002c680c0325440083c0000c0c4c4204807050b02c500d850381003160801c030b91342010a0a2502c4006100981e030000780404810780c01000380c40e410b84d40ba030051a01e4406400c3c130402c0a00d04240000342025400b5140c08083e26000c404100900214a12005240d51000c01c0b4200c00000d070002640f550070440b0346a01e5a071410200040f00d50180100d648640c10050a907505002016041005504041c1250350415524070022501300c0302a030040c070354043c446004549910703004156195605240d0030030203d1850600a00c9814000e94146021f0a0360481c0c007101b842da40e24204031f140114480d81c207648141d4200c0c0c03004e8420034820040c1146030141054031041e04050a04070305922072082c1c00c030b4022406691501050b1031903144180c1040040707a0203401c0003101d00024243d50021080300349039510000d081e204101c607001101103641ca2450444601a00d9611707041075030315119900030b09002c5494480030441105034100d1703011400361007041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391080944 1250 391079694 391079719
    0x40302190f0b093906030f0f0a06030201020d05091c380105062809090b0d0f03120608030705010e0609030304080a18170109060b0d0b180705 62
    0x220000040345000c2d14940040d801081c080400400c480d4054a00100b03491078030145542100041c040703134400c002c080a0354509200040d52030000444c055080c05400003840d0500c9551140c1042d070140124040c140707808401c10050344c011501000752100b9044c80b03512011401d004c00c00d4802840ba1480c45008a044103c003007002c6480d842c0d0800803000d851040b051049044019100346d0101c0c0d02005100400040007145496801840000102e8245070408010701d40341d040345a0012480c0b1000c42c480140c00c0c89114102c0c4503884101c0021a8016401e00541c1c03100c2c004000c12032005010080380c0b03000b6601000c03081d082000104640401c0340e59480c15420540d0087c4680c04040e100345c010b4501098056a0010aa81c021a040442d20380303004440141034940e101c4400801d0601082203c00043c0409400c0b400100c0a650b600089a614001e2920340115200e5803112841400390140c0000441c04030080540d0280d02e9440002129844020301c070714049155009270350240c840743c1103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391082194 1250 391080944 391080953
    0x70e0a110309060a0c1106060d06020f0310050102010c0e1c05011503080904050f06130c0e0a060f020705040227240c01050f01030807120c020303180f0a0506040e04030219 75
    0xd1510400c1d201d0010040365586031300446d400741001c450101d2603407240f03021074070301d191400100c140c0361710031302c401071030448006004900340c2c1040b59035460702e1881721420807817560280075a9000410b146006c01ca8210000001401c41a48005031758210318000e09100c00c20900754045641107030640d400c10300702da41e286010101940b1110300385004606020100740c2020541c8491800f40c440104103610201c41c0c0c4c650070000b80300c20407282c020000780750200002030300d8136031216018004655030b42808404412010b8917184a5500240c012841081242c03808540c2c0d02982ca80d803118880e94803080c81610300010000c440000c0b41e1624004000101c1c103c03500100c00406039000318400900c61a601c80007010403400003480b001d400c3c2c400070481440081c8a8017040d81c1d200303200b41041d2207840955000f0a16640103150591509a505000d03021980f804410044400c2c60450361194100d0522012030036500440c46031250704c1c4500e00c089001c2600a00c605814044070801c02e40ca4903007142407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391083444 1250 391082194 391082203
    0x20a14030703030f050f01060503091507091e060504170709060605030f0f040b0601053a1505030304150203040b131a13060e030f060a0c0e1002070e0a110309 69
    0x2800c401003440c00c1313903100d5826441e004003031182e00704144c4030a03660301c0c00f101134845500040c11040c150188007020400790049006c01409082a9a40e480ca4681411100191034280d040702006110711a5410420294481c08440984103080c00e1403880c220b15a030380c2e619180c00b54100c0c42e81075080010114030254803902440c0315402034070130303202e06844501259883c2c0e0001d40f0301508041c00500040c41035402403000f42080c01d410200d800c0c40281199481000b441e8a40140742e5198250f04002000d0610740030b84c5400c480c1000c010300d256407078a8002a50307032003240306100e0b180180841c5e490708203000303000b0390380200b080ca0316403030381c4010308402c20815504c00d00429000712640b10601696924083c19181c9510140c40d4000300c075800c0a500ba54016030f04001140e01d0b114a0701e501b1039811050041c1c0e40034030385c0c2c00c102003132104098070090b04540710344c911035001d207170070f0009140410b50026081c401c1791303d4101001040c5c0c65652009010345141c1c00b69080c05c14000050000030900041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391084694 1250 391083444 391083457
    0x21f09080f0a3c0804030b130c1a040509070504081603060f05010326090d060608060c0a0801030303021c020c0312280b04090204061e1a0d020901020a1403 68
    0x640004100701c0055012220000070b401d900a143c103d142c40749a1540e283c0c1006030028040e20034036040a50b41c0d5204101d80004644020380c8104000040c02008141c030703d400050102e03403918a0180d408010502410300451145070f104003070380b0700468601400b400440780580290405c1d41d094000300c50707001080c0c40700d1740300480390103141912501003141c8078032449060b25401002d80f03004114680608902c13155500e864035040b003042256001e40d039111120b00480e03611950010600910b0280c4441c1050401403414008100c2044110001c59000141c103042d00c0e418200182c9034002001d200e4032982c4d03000c042c0e5410503c0010580540310002000c1c02c049143c40c1651a59540c400540340e205079a103c42e0144442c0004a81d0981003d5075007258055031800f4000113015421038001030203444090740260080820070fa01d01010402e401080300c09441e000511107110681800c01c00c02d0b510440382440855540402d800000c0d0b882449800103154002005140007102c24000d00d48030752201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391085944 1250 391084694 391084703
    0x3020405091606050a0905060d0b0307090f0b03011a0105030907030f140d0309030f030e0a020901030c0e0c03090c0f0f04050106081503070503061b2106040b010c021f09080f0a 77
    0xb80d001403458071550440d1460350b02551801103051424040c041c568010b64201e405554a0303500341c2020b03072010013074034000b05803901021802c8000e100304070088a1085141c07500076414030102c0d14441694418030008407000703181c810b5603075899188403801e066203500010310b141c10084c0c10300140460b800300c0b0644200d00c003041d6071032211010816011207140940080104003a8240c1c00704c10350296110000b040103480580e485031402da800101c0342c4034240c00c01c0b641e8101c1e195080c4040e11205074250b40c014640c0071010700e54201480020b9a864515889520500c0340c0c07403442589807141c010240100318003900610055848000103464003804803800c290000000340c019841e4900000c120003140ca01401514440e207070f0490080c0d490340d89289040003500104141c00100350b469a0150f840344400030710204504040d4100025208814012410440c0e540502005a940c0300e1200700b000b86046c01c029816161080140d6444030540e00042c0c46005407180c44c1c1001101144c07032000c99104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391087194 1250 391085944 391085983
    0x9060604211a071101050405070302091008100f0507170c090d0f0309031e08040306110c0d020109020319080a0e030c060a03140601140d020d09120201140a0614190302040509 76
    0x1004c1d40600b05c03841101c0182080e8090780040002d420700c018070540102501200700e40003515054403500d058204081021901d035244102c1844100d14414290812501d240000c0346540b041003010100d10007500680b001d01001817803540603079404800b50451540001515404941410090000c006502c0309441e00d0042c04440140401c04540004205600c40d400034107081c1541c88450007406801611076551104001c134000c11701d0100001e085081440d800410240080d1044c07608194015400c020740600011391040014030000646030305111901d09403100d0707410300e40042d1a110030128856008840000c60300800d943c55085543c412058152910702a110480112400d0201d0080c610720480103120340d1b4040c0307030f2a030000d00b01294651804141c034145610b030100d913181c41d8010340c030140c0c1d034036a10b16901d11203590310035500041c040c50030042540b9041c504000100102405885003440c01d51004821621170044009142c000c0c0c8208114648158016034608180f000502c080b0700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391088444 1250 391087194 391087217
    0xf020106031a061201021603120e0a1b0503010c0f0f0c1e060506060304050a020d050304031b1419090209130608030a110c0a05010c0f1a0105010e09060604211a07 71
    0x14001c1f241c050110b40303d00d01c84030a0075101142c0407902420404039054075050901071240e010030042c0d801900412101159218107007541143e400c00380e2202d4001c2c1d043c100e84080654000400300e03102c9081d41000850b010101c4001c41c2c041c40c011600500c2507549614440b130b072148196510003a644514010009070702d0344001c005039404129001089a13003d003140701d0041c20225141c0340d03035612134011a400d050300c1c0d90780c03040c0c120400b5407110b0002404210800150003480d48071440907600341d50154000c4d0703012804200300603250003441607060700015055440d8844000300088400741a03420060942c41c2e19615459900004000c400105420042d20144401084014146100a2541244618240040d00d011106040c03e0b90080e50450b0003002151100080c41107004880c4400343c1150704080000d0414400340241a001d006110100b000546405080702d0a907000210a002d0b04000c08246031009843c040d070042c195044003c61400ca5080c404076540a80d01503240c0c0c076070946 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391089694 1250 391088444 391088479
    0x10e06011814040c0b090307090212071409370f0602070501140d0c0521040201110106060e130213090204030204060e27160803030a0606140304030f020106031a06 71
    0x280030f0794054001c2024901c104400400c250041213040e41c00380075103e04680e21030071003080340c0000c1c2ca40c041522540341000440340e400100d01c490101e040507580c2c1860861000f00741650340620110304040d40f5901c0c140700030218160b055151030321000c800ca01c00d50f107400074081d28080511465003d403003440d2022403190700803903040080503500181c843c20050f40e81e038844040d08070b40b100c49060000800943c111152840084042030b03a12541501d2035040032300c00144000d03140101703a0b80ba80d00d044010f204981e03104107044070a04088a45020045444030014028803540e0100882e02c0220b45c400919a03006402510480e8000c86d404c11100e5510345811415900884000a80e00a10040004c422206001501e080003d40c3d0445203402d468203080c1610482c2038119402d198004020403c48420a0149402070110761810390030012090304d00440c3c03804050030003020302c1582102d25003c0b40c800d5102900654001d00e07803601003111000c0240d1081001e03200c25004240b060001032a24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391090944 1250 391089694 391089731
    0x1b0d021305090103021012023906101205101b0305090304050a032004020a0201020d0f0903023d0c02100b0f010c230f0d11100905010e060118 62
    0x80384c001d01035144040740c0e48007c8070300305686031030011000c4e42404404000b00c00088104003245810715108100d2400e042c140030707941506505070046a001404021500700700303070f43d2001242c403090034490740008145841802c150400d5482414145454909000040290345040713686606072803c00403604d03980340041d224441d03801000d4001048110400003e5044000308910140c1c100b0107421000c2c0c01e00006050707074003950f2003400503900443d0b03880201c80701e8440e103141540c0c484000c100d50000e555001c0e4491a0704c0d1030884581c03808806103055100010710f00494001890702012036540d4201c81d0364010540d42c02076000610480b00d14100806291180c404502c8000f07058101c0c18080c4c400464010f0514801142d03192900910785008607008400c55007060100400b0f0412403145042551a2048517841239040081e130400d0007820040c00305c1c1e207424052003540f000c1050703e0706003421400341000c04d00c56141d62250700000204a0140d15030380019120b0110f003440240400050400d58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391092194 1250 391090944 391090949
    0x11401060c2001050d0e0d02010b180106031d0609160503150c030604060806191415010804020d050a03080108010c050a0509280b0408070506030405060f1b0d0213050901 74
    0x94080d040b50309280700c0d00800c07400c8901d550501d403c41c9003402d0b80b82080d00341c40d806139040d11a540a07019885602c0e80a00800040e20010f5482a81400216240800c0000c040c4900d03824184d4615101d108600707003c41515145602c00126081c1d4200070b17000580e91800c440009407604070811001c251490042600200140c410816541c962552600302d0b045030b0000d050f541d4420394500c400106030380c013440301c0c6100f1040c0c4001110201100c419250588441c00806004014450200801c2b0829105010400310742840e006086daa10381c4080348c0040417084010f844d62284c1d04083e4101a44168003a050b82c52210081c003c2c1c410815003502c06000d0404a01d0203e0024041000c0d28100107140da01c03000c50040d80248a40340003203410700340705159003201c10564400101032048042c104801030040c02d040c0e4500b86980b415480756070f1101d0014005110480025010131a92400c40c9175082c0c008482580300359403400d560341e4680096100c100300e01e234518820400081c1524116945604 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391093444 1250 391092194 391092203
    0x1603110702040b03160603020909070203090303030411180114010f03060f180603121e020c0f01050706060e090c010905030106050102030901080a060b0f090405130c051201020408030c011401060c 85
    0x24180360381e00b00405418007030340098252180d41c6100700900e0003c071502000780440d131401030b506c030f5030341003804041c00340107107060190b500401086840d6240001203d600c650803100b1281c444c0100d0300002c059403a44484140c10301050b00003c01c400464102170a2030131800d03240e410b010140301d0025001d4441d280300c2e0844007601c582003041a00003c0b0600d107100d9450400004000740ca981c1c99650000310301c0e6900e80003600300791400e440600c1c9411280c0c10302e490b5000030b1002c242c03044001103005017001c82071810460045850300400c441030304004080c105d1054951840d20b410400d250707a5400b440c0301907001031f0955030001030301d007010b114060a07508103030b0145240100500c019100e00e41d029221091940e03542c40300180b142420000340c9041d40c1101b8901d84c1d00d2285c1d000b0001580d002811545650050102e42130020300074071289011504d00340e501000c05000065094028002c5501402003404000b410115000040d440009a142402e00202c52a43c8a200172154002c100b0b400a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391094694 1250 391093444 391093447
    0x3030905040b241b030c0a05070807030803010504020c031603080604060b0c06040b060109120302150f1302040f0b040f0f060b04060f031d150405071e15030908070803160311 76
    0x3800c1d4540c0c0b0020060000000c4c6540c400f00c691007241031540d071000034103500c9600080b00900400c002070061000400a0100902135079096803a440b900c1d11040c807135036104550014082560290500c16546000021410411000c015040c00b0b0048401190741c4c500c280c0c42c0c002c1c0452814024001c0d581c503098001c0041c05995980d945d00c1c1c54401e405084503040c0306042400080f8200c40000b00340e0030900ca41d01910030f03911140050342002034058404001c07800c500c010860740307001c081011852540c04071004281030368800c1903403008144140415400a0030502d01d40c10306013903508555003c100c00c03c0f0811015640d254860001e005d1400741d0400140b80302c0070f40041c54801d40080c001d034104464000341c3c0c1c51900d82c00324605144551700320400001ca004200c2813040078440307103009180354000980042c8900603515410000340c0a8000b600c070500301400c030000c0c441d038000801c469108007540d13034600341400d09801c00d4200b2680c1411015143d8001c1e01e0a500c0307401589a1a022401c10070b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391095944 1250 391094694 391094749
    0x3050709090218011706060603091b152b0509061302150304060f060614040303030203040515040c0e07050a090b0a0c02031b040e2409010b04020403030905040b 70
    0x1403000c1c001d02501681c3c02071540c10266203030240000264000c183d41c000c0100c16103000e0940500307005c0c004081e00d109280a004100c10400f02240c03001101c0d482c120303070401c1065a800018010071504103490341e054404038011107010390040c9074031000e071507401a42250314007426004098a804485000741a04118081402c0c224004814107240f0320040041149400b16540003131242c1007124141c42480c0c07a81e01280c02c44040e0306c80d0002920b11440c01d10340d8910b0b0013242c404203100f60712004040690002c00101480014040d114001b448140c4c40003d03420b060402c080404c00b81d001ea4490950f400300801c2c48280620102ca00b41c611688801820526000e0002c1c419008840f4403401d01002d11398200c0140d60038809003c0d4141024460701c620b2841900703010840306544070201c226440030400702091010604200f00e9a40c081c1d019001550b82c4030360407130241281030000c0c0d0300140045030100030150080300950036580107840c00c00820f50213030200309500903103102c4000912020100f8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391097194 1250 391095944 391095959
    0x120414131b0804080c10051519150504170c0306010f0e0402010c0f30110307060903090b0c100e0d0e0105030a060b0708120f15040c12020d06140307030507 68
    0xb0300340d105000e1008103013000b900911041c100740342e070001459180d65500400c010219080c0045220013410303106141d044c000240007209280246c080e86205603216070000c10010700c40d034200e0b4060102c0210383d440000e43c07082200e56420304450090303c80d0060030000310340d0f40195240d00b82152000031040c151500c8540042d034210b412000151146450380004401150180e082840d003900340c04240c500165030100305440310940b985540c020010345031000c86424a001090740d603169080040006c5101092806803001c03261588041c20000c400710b5012400c1d0b40104d18100180150302041c8154801801160b8807032464110070303000326034101c916aa55505c40c40165a2100030100005a1140c4503c3c1024090300a200708a0308600300150400040b402401220f03086010300c9800c05c3d036800e0104c44c00155442021300c00340696a207058000201e84901c102d00406566403204665801600048030f0141c03850340241c0110402da11013880c05800d0005900045030b801101914601e42460308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391098444 1250 391097194 391097207
    0x705120714010219020c1806061602030601080a0501061d04060c020304050301020403141c090e06030336091006050c070f0611060a090c030212120414131b 68
    0x10305449000d0319900070564030809100800342c1d6100d00092220318154644020725202c002c80304a40a8803c3e00103da01c0c1c810024480c03600080112100c6440c0d00007210710a4914109150203076251040000001e0401804603200c00b103903019900900c9480d40320369031002c001094150b00e81d924000940040d001c180c244e88003108d5905070784180c0b4501503a41c2c00190a90b009900140e81861500d01e0002041c503003048074003002d03445013001000400c00e8150180514105115118903a440d140c001401c3e90740170300442e100d62000c141482c204c0118002c2c800f850194141c0c0308060544414211200c9141c5020014480c0c00b01a00d141001401c04500f20f80640041850040310300c0b90030004210141c100299901610076035495207510144015114500320020b00308078201c40c9030050f510042400010394100b902c0e0140c65580c1400d06406140d85480c204a2503c0310030040810040b0b608000358010158840b0101c600c4824070410454420480e003148101e901c4902100700c020007031600408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391099694 1250 391098444 391098457
    0xa0c060e0c0609010e030c04060807060306090c080112052509051b090d42110d02030903090d06020a02101e050c070c090c030c02010b1305100302030a06050106080903070512 76
    0x242510240450703c00860103842481c0c011012b15000403905022441d0b0500c0340c00b000b042804800e000303800c008000540000750600880138408849411802808820004192012040e0040058014079604001c1703005615001d1341ca001806c05006c510744100c10200d05000c41340144e0311070300d040310180c208091a400c0c030744111403400f44500400300e030302101040081100c9665480c1940400030910540c46a0840d18001c01c245103825000c2c2d100b07417030850650311071100e444030040e82ca8445070203091a502a42403425070240d04403000104008858001e0701c3c01071860740031140c903510f550301c06500751102c00c050302d07240240703000ca40141204076402a5030041a45083c00d4901101504d40d00001a0300340c010041c11501c1d01030200d42a0792500c0342e0a4001c001d80300810810a90b200001c418601075807039150144d84980200c0c0803550544000c5000315802001c80f0741350806807800c031000e001c00f446075402083c00c03d030021b0b000d20700c04030440b441d80f584100505045a12400304000035040340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 391100944 1250 391099694 391099699
    0x209040f0c021005180a06050906070903050703030807120c020708011803050904050403031b0810060f020a111c0b1e1306020d0b0901030605040212031309020f0f0a0c060e0c0609010e 80
    0xb50b030010005e90a0084405030b81c0141d5020840d86400c946d034501d0020058800410814940010008030b01e0200341c04003542e07407500e0140e105480306d0703404035155036020f100400130502c2d0440400c03000e40c001402d01c04031503a040c000c0c4044c68031101c180040c0c0200c0580074010407410010108546096401a58000d1080c10700003051036400480501d030322130542c03003080420100000e10031080c0c0c0c0305c02268000c0c80d10b80340080000e040c050009459481025001301200c0c1d052480311816654401c0b010307200c5283c41d00106144040d4203294100d100107589108c880800c42c1c4504250800342c040d041c0c80342e804468000c00d441859620000290f0011f0101c806d50340e900c4007a200160394090b41d00d8003c41c01303944003051608060040002461011000b0205903004004141d10f22501948007012548180001601c2d0040c0b00030a580340c2c815000c2001a0110000b20500d5281c0c010000800d11401148100200c00c1c88511056591001008055019100380300c118025131040700d402c202c19002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 391102194 1250 391100944 391100971
    0x3020a020304031e1703040501050f0c0702040c2a0b060d050706080a1e0509100b0109230d030f08010603020708070204020f09090103050c030111070f0b060d12030209040f0c021005 79
    0x2545510003070301700001d030180d0b00725800002c0c0301c1480024003886420108409042e032407810658455040e5120318400280669120804015282d00880703003560300c5400c2c0203050290004034810049026a030510865104506030040780860034403059000c191a4814000d12000e401c02401343e812031402001c05401c103483c5d075007041e80c4001c0d0010b88960900014008200350806030b502c0360414a900304000c0c502403406036005981d0380d00080d00c03000c4074140d240d4201030300b4004420b1a84461034440140d04550202d201c032013010307880424006e81c110190344000880c0d8035444101c0591180301c1c00500354610501441c2c001d86881c5e40240240c00e051000c0c01d18050814005c03031813044090348250307810741200462a039281401c0c00707020b40500c4a144a9031401d41c0650301c0d01c054241c50b00006e801524018000342c55610381c031004180850708448205c0c00c2030b241e080003c0c041e62010320060300803420080e15000ca44e00354001c0020301a095000307001035100b07001500b00100b40c0140390507108041c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 391103444 1250 391102194 391102253
    0x40f0f0203190618050912070f060f090f0b13050a0b040201090503070b070618050d17010501050909040f0602070206070c031a2208040909060b0f060c060718051e03070603020a02030403 81
    0x80c8600123040e01c920074841000a00b15a00703000b001c41d16604a000c0013581400452000521001405080c490340311381d0000c06505c443c00140b1600311380c910000d001e803180000d03440510034144c803014890351003642c1e51648140c64500303068540896114003000f0b03010500c1080002101904003010018021201000080980c0c80380c0d0728014000b104800031403010405030844e0701581c0e82c407601410007828024681205140882c42c0380100a0000e030811000d00c0c0a80304000325501210210341e001410030b1b4586030075013000d0b00c120381c251100305c51226400016002c04c2c03408200641c8195444003040d11900c0001a42081d4000f0b1904222210b110030400401c003842c19104000400e03005030030005042a402c0107014088007801d0085200f2a400e1020b0340390701d540011229844040ba00d04034009d460a082050340b60107107030b000aa0300500d0046c0c51948070401100381c9810140440c100c4009564501d02075040740f0a47c2110380c016041040709002259821880c07080808440922900200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 391104694 1250 391103444 391103473
    0x304020f060d0f0501080f0c010315090207200315072708010b03071202030d051602030102040e16093c06050a02070b030601050301090506040f0f02031906180509 71
    0x2400800c1803038049541c3d108140041a4030711565000d0003514000302240749907a00c08a83e1800640241410541c890005c1d035100031601d11504c2c01800400010f40d111002e07403a1080032042e84403150754044000c04000074282c9400500544e510900300d13641011521110011030390300300d42070070700070750741340f02108103600401c100720103c00070700065000160580d881070405003420120385c004505115482406009070f500440c040c00d4280d41428420381e540c2d00c40c29800580d400c2400003960651011500181c50000c003500f0034846c07802c4540600d08881020003c0d1503d00c2d090189541410851011030003501007040416408003902d004a101010420f07030986179000540c0004000580100c4d500040d190100182009419400229420f6240c02c10008005001c140b203003100e159203400100d40591140d0784060b40e9030b40d0812007800740071800e800300ba019520035100301308001024926401216158414030040c1c403590781950440e0358031180d801010b080702030805040d500845280b2004030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 391105944 1250 391104694 391104697
    0x40207020d05010c320a0c060c0f09120c03170909010f0f12050c090c121f140d0b0c1611040507110a0236010905060103060312050304020f06 62
    0x510480001ca19001031040082c44c0030f00e010055030038a1400f030451031003075030000c14000c0311001c1d46031780701d03154014600300700c451060507600038000518280c501120554024280d00070700100d5251080f6035039807280403141214000d00007a0400056200070310000d1220307099440171a201410b40c5041ca03a2410006041100c00e0b40214012010a041001140d070240f01c2400100a1b615440030080380c01d4403000d4840004c00403040c4a0b190900001d105c500e441019140c0c0400c2c1c0052889440c50106450031082c50002c10120825408003000130300402c41844101c04203e01500c00351030300c0300365a941201e460020f400c1c2103c021043c0300040c554041c2c1c1d400e181001c1e01030320b08500c2007210001400b0860f517019004a00700040036021240f0342d0400180e2001c0d00341d069400780003814006034100950410000c06803440381752019920b65200244c0c514505807200c406c03041210340c45243c0103404a64051000070264010000d0081c0014051405035620600140034101c003580e08a0004806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 391107194 1250 391105944 391105969
    0x306030a02130f1104090b030307020109121b0611010f1a041d030712030c020115170a0501060626040b340305220b011e09091a090606060403080904020702 68
    0x849008170f030403c60b0003954080d05040e040c00b6000b941c50100c0e0f0b078000900050050095a45032403120b03501800304031010f002c80e4400301c180c40c0f07032000d06500e400c0b000b0004171407001c2c0000c8960a06800040c40780f150300c41d0354840c180002c0d00d120410124014030024083c809648034488000c01803814039003906000600b80380307100355035030740080180890140c21100f90b280184116854110701d4505000e00751412020398440807003a0311b884402025840c80c01040d403070010802e500301140000c000380c0102510200707008248411600704203102c905410100215000760100391050081126070314124004145810580050001146590750380181004c1509110340001e5482003000728580e10244420307042c90b50203100842c13034102615a420320600601601400c3c0c4c0c0aa841429844000c644140040540314018802c0940c90b080105520001d031208107140111500018012003000c51824440d80000b000d56003031506540b03450003103400c84e12035150890b50800c1840c016076032ba10180c10030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 391108444 1250 391107194 391107221
    0xb180a1e05030607050c060708091c180501180501050f040806040b19091208070e0405010b040e1e01030305090111060a0f0e010b010c020d03031404080309120306030a02130f 76
    0x5445240006051921900801140030170109102555404202042c181d0700100c8600c1c0414040e01c0e0000501d00704080c482440b0201c00315405407241c041c1e08288407054941c0000003003120a075881005461500e22030014401a401030b2200740025030182d00541b402c041103200e2503007495218070707000f460b281c810340e0240e442034400c038100b1007d0043d404402d904c00140c2c4809000c690041da640d00742200350840101c0905c0405000101010700c10110031141c8a0002c1c000e202c1542d6501c4901c90b150300600803404003602038000951b8a080c1664601071802c00303090581e5407070b032960b1000c84658002c0e1000d90b040083c4070545200d2003400308070140c01088004000a01d903100c402e0f500040310258100c1003c66410000c18142c50f82e0056040c1146680584018405152074642180202080051b582411a695080c030040c414040059441079a4941c206c0e208450a4054039910b40802c44104d44e143d84901541e000600f803141c8034107e0005020008500344100500d01415541202d00310351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 391109694 1250 391108444 391108499
    0x6180705150c0c150a0f11070609080c01030507020d05090612160908160311030c100503040b010501180b0a030b120f011a150a0210110c06100b180a 65
    0x141014203000038001e040c012030380325149100c03900e0804c656001c4c101021040c002e0501c418404c003401907100503440c2400d5016550785544518014284e60064016003085124000e0f416070380d54045d1080902501c400c0d0000c01d8420541030307003112540d12030100b0a40080090040000d43d01da2074803514011401a802c0b402e0880400304010141c944660081105a0040000c0b4400701c40d206100c0c810b4a030080c0050101c6101040400c0c07030318489880007a008224170b034003c101594050095030243d0b2096035202a240da03107a004407841d0800714803e1440c0c1084910421580b00d400000f0a0002e8081c1000b00b44511098001058082c926103442c0a40c2c0280702c03039002001080c4070326400c0e03207040d0b10311050400e54040840e21040c0004040c2080c035100040c0135200a008201c010186026950107020404e421b4100b0001504161441c416911a100c081ba07050143d031280a829660120100c600b000a8400180500001480300b280c00103c141305c0801c1484007901c4400d1020760344250752 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 391110944 1250 391109694 391109707
    0x110703110c010828090506130213020909010608090f01050f07120e0318060409020f07020907080712021608040e1f060e0d020105090d1110110618070515 67
    0xd800d100d034621a1a04200400d82000340001e0054000c010061024071050139103401d80d00400700400d800c07040501940b291908000c808200e4401c7c441c00c00d0303c00d0355580181400d80c0c0c8128181e004403010117911800d200014003050384030f000000d0f405082c002c100d501d1205070651030350860300d00391524070300160a1010041c0450300f201c01c40d40c021a114500700240d105600784542c0702e010b5036010400101044104014550394001510064203000c00700710b60b2401c2e003503050b08441c0d00c2004124028181400064200340c010500240b090360107481d00341c0c0e00e001c542c4105000313500c249880c00d030820201c000c0300085041d8030040e1010309062092140c10b0f00780f03940c000c80c80c0c1e0285150186210001d03d000d00015512510001c022002600c4078241c031003141c40103940900400000d560003201180c0c80c2420305c50710314142d100303020041ea4a003e14400d200007c448070232012072446007076880100810b0190200a1480014007070b40170036070b0300032601c030000100203c500348105961200c021404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 391112194 1250 391110944 391110977
    0x60605222403020603070215090f1c0c0303200c01051510020d2102030c09010906020705010507020603090709020703110c010915110a0501150816120206030406110703 73
    0x30390305051055040c1c0001c510640e031010390105190700000340142c07008004519418001c128500c40706041016148031480c00205a07a9120100c0940c001c4a11810842c881c08044a8680c003503921503d40c0c4d007103c070780100d45080e00a00b5017540000f540c01040c0c4000b0283c26078000182403103604090010902d07003081510b985405042c2c02d2014480c43d1103001c0c03040c005800158001400c3c0050074401c1d40910710038180e0b8007442c1201070154016000004010b40100000003d0140e040262503d0305040e480381400c90707507805503009450201d402040450302603c0c00ea00919846031441c0d08851916440380036007010703a04583c00c100c000c00d842145103121744106015400c01d1303c5081c42d260a0462801e042d03e07a003c07000c801c44d0002d1105200d00c034840882d05026100d01560007000034440c8022007194428480614462560036015842c01c80d01411000c601c814201c1d0500407003a00410499002c00c0610350014204a03103080e9107522501015076a540900203190180d283d111205803c1c500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 391113444 1250 391112194 391112201
    0x15030d1d04110a1b02040606090303120e0d0e040207080703031e0c020c0d0623160503130305090a180c09060e0922020d0b07021908040501050706060522 67
    0x40144100e00b840d0050305203202ca401500c076209024688210040400e0301200054800c90304060342060515102190043c3c10100039400c592095580e09203450001c1d4111040300c4980100c88002c0e0440b12810120700e01c1b84001c844503d43c020401032500c0c6031980c07135840075800604100d0201c1c0d2500016100300d141309034010380c404503814080c0320308802c0520003500c692502400e03a01c02e2141341c0b4071205100f11644190710368080503401074512202d403408180003000449400e11500d20030305410640300c0c800c00541e401800301e0f144441440b00b0540c0c0036280c40d0003018940d1381094400800150480c1e88140e1000304151903c1c000038401d5103500c0003484020782d5081581800710a03400c00070251915130055920201848859034a0f8500d4500803d11100c0300e20041e500018108880c414098614101c5000e60200d40031100e00b600c03044e00321b1003000b0b1485000362901c1801d00c1b082040b03502550081c50301ea0b01c41c5100003004d688a00c00201e01c082040480000c5000f0680c1582d6409150710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 391114694 1250 391113444 391113497
    0x10e16050304050703032a030e030c18131a01090e01060b030705032404090c0801050f0103080a030b0a0306061404060501030b030304050f060c061305060709030809040515030d 77
    0x15110745545001e0f12044c2c0d880c0158800102007201540c0a41516003109401b0004150040d2582500000d40c0c1070040c0080024030700785200c0e0080790070040f403d15124100502ca110790a540110070b54842a0520070640341030425200302c8035401381c1c80090120140514040c02803c0700008403078461448071400c5543d15045490341410030003c0c007090780e40110a4a50189106070b44c00808001d0000750388204c8501e000443d0024103111080c0e040010a0f0421000c0e1610710340208040c0c1d654084400d07441e10213200c00b40c200d4504020ba02c5095101c0c1d007011001210241c84020703042d50300e5880b4400c455281e0302000e580320081803007040b146014002e010042109107400c1c0a4040500000b9840e445213110352032240505411110749034a0744c009980d8428042400d0380c3d55881c0c40d0780b1a032940c1c0031140782201c6134028400024035440c000c88260301603a4104011a04002072101400002c0001520551450392000364010321603400b086603405000007a6a800161641950050410904003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 391115944 1250 391114694 391114697
    0x609060c03071b020f03101a031902190e01060503090c091b0c070b0f070510020f0703110a0b040c061818090309090e03090907081501050f0c06010e16 66
    0x40040c055030b02e5120f000c40070110740007070390ba1519003800d20010b414940521045609400740d1681480e203a603881d44500d01e03041da00f00750328000003079030002c260306c41140440c21860140c00300c80c5000503041c00302c41009003200102400c1400c54881000d129107e400742c0c0580f00060000007041860742e01400080181e950949114140f424601d03c45010040d031150750030840c44000c1410041d9001c20803c40c0b0062818900c202e0f900c42d800f1101111030f0b4400c2030195814859545480700000c2c040c0f0844509581c0042c03613604050307496030100c0e070403485680c02c9042d0744149004803010800b51074001c3e000710302c02e8035001610b51030814041c104c116802c0c0183c040c0420000d013007007144440c00c00000118601400050749549034681a00c1e07100e850380040401318034055403c2c0c050031000009050b80701045400d42c2c61a551107100300c034900f0f02101e07030940840281160b196103500035000b85c1070070b02912543d17032b0038084420781690bd042d030240c0c800e02030b810300c80342480ac861031516100f06141080e0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 391117194 1250 391115944 391115947
    0x3070e13060b040905101a04090503070c2903040f02060d0c03060501020f03182107050901090516230a030603020f0102121602010e06030903030a1a0d060f0902030109050609060c 78
    0xa170710b1300c1d034556116180e841905501e90842d5081055140d00000ca840401007040124030101d0400942d03e402c90101110715880242003c15103a809407181d0b031001000d200c00c0315150190415080558001034022901e00c01140745600040e946c2c01c0140208074080400054020072030300c80142558140e1744840c3c10354000102207444504040120b44800c41e018820707844041c140030100c1c05040b1005050051449100c10b812000040441d004c4110340c0700300c8a26126988a40005007200c40c280d40807002441d03800003070362641d4000d0505554001d600000582800800c1d0b107940ca460b40f14402800c0080d964520901c00c42c5440c080e13242031008280b009100a100e904654501e80c032580340d0100b1030505401c2402c046a10504c5621078a0070090140c9840e4249600c40c60317520b42041c0c80752400542000800e1100c00d00262415680000060000100d0300c85900c0b400002c2030f00b000342130300c6a030f1241c2d07a44025807400d0040000d07403407148000f004a49004107100742010320141064400000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 391118444 1250 391117194 391117211
    0x50901030b1509010506091207120804080105010602011506081902030903070618020625020411030106020d020a0503030c0a0c0b0f19020301030b0c030c07060501090209011106090604030e03070e13060b04 89
    0x220300003912607c0c0d800b40d481c00710480589404902e0440554000f04a070750598040c8810031019001a1084884400c000e10099894001c141c3c05daa82104503980d0154002808102d1179100e074001c641c0007406032100850038400384100380140c0c3e00494010020703502c002009000c201d8103129515802d01ea0001402004861b070b400550316125408803c200e2000035004140500080f100d05808241d00400030014296014a15811a04244908409802001010b100160000c15005121540300c4051803965032103480c140029040407421000f004540900c08000502840000340104040d0b1282041860b100d0440103030840d00101c4044600d005100401c0081c44002303072a504031302c00080c03c0303840c0c0c3e8401c00c0b5050b080c003907000090301072410b181c00058212801c0c0e0081c10014400ea032030020071400c01031450361303504041d2040e101d641d00480001e0080792103001a40f191002c000d00f41c40e545c56032035115590000c0290f41020b02410341d00e61120400105100b01a508602a5000d002201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 391119694 1250 391118444 391118449
    0x2206090806010f031217040c0501033c0b030312061c12080726010608070906020303011224240602060703050a0204080a4b0c050901030b15090105 64
    0x1100e01c802080c800d0078820b46402ca80c0207170030362114007002c01b140301818900741c00c124201e40c0d507510800f80407916018146900c043d10a0110344c90103c00d91000c1c400840e00b22151802140d1480c070b00d00c1075942c2d0041060190b40600041030710b400200c0f007500c420300f071030820840703c2d81070036840b044002100e8040000090341c54075003400000d600e06200f0003503611210241c0b91221403030302185908150582910b02440c00b0452941a84c0c081d554580f090b03951081c05541034107490042201507841032004022130744400302c040c40d020340310310070f018411510384100a00800e0740c036654407032040d00d4410306155800348544174140d2441c1c68500e80401c0380741a401944480004d0030305020192204001848060150110303402070100c0812244040300908100c500440c0e011303051085100000e030b004070700c031954440c2595841c004c0c03107a1001c84240d0404840749108070036421a1080300b07800000a1756074540100c180210b010b10300d000c0c614a4044034400a40209040992007240020014052034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 391120944 1250 391119694 391119719
    0x31704060207061103090918011a210c060a05030a050a1109010806010309080d060306111e0304030c051b030d08090c450a05010506070201030203070302220609080601 73
    0x290014200610b01c420319840113421740c031400d40ea864000703035000c040c08000c4010084031780300307280010000c00c5052050240345c0c941a000160b02ea07800300d40010b40e04043c2038140e141920020845003250002d102e0a4081091504040d1096000c168040100100800d140c014954880408101008a511003100054440c003800700f02c01c1c100719201c80000c41c81d074040d5014110040e00318405680b1044000e80c4023018200f280402c4414500700304001100880000c00d880b420102000c2c9034010031007185181107140c1005001360204040c01032a040850402d11a100840035441140719020300076070140b61518158841510400c108038017040611240401e66141c105003c50b018180650881c007004681d040c042813505040d46d0844100407109100d42c51004141450079003604503580d032020762011240d00344280b03904204108880e500661095005680c800c00a050060034020041c810303020311004c40d4100a400301d50740c2d00030700c081382e001540c0d44010142800104190341c1040800a0704 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 391122194 1250 391120944 391120949
    0x15040203100f02071704080706090503030703230301030b0124080612071d0601170f130303141f0f060e041805061e0a020a08040b04060e10020301031704060207 70
    0x6558445201194842d078040f6215960001c00c4001c00001040700d0b11196803292080340824802d5210024629000e00074040440b030006000e941040c0721a10280d80c400041e142501000fa16481c5040c200d440140203035004e503001d016800703129070402c10310481c20828100ba07441d102e0302c4002a10b9016038070130b4030702e9440380c0290350207401d01d408070607002d10702041d0360003910800089100000c0c00f002501c80c01d40c03107030314240d071a03a03000d4480c059070580901003036a0400c0d182c80d2003000101e00802071003000304030502c64940026040841010005007400946200c40c201648441c900307100480d0420b4003020700814000751218518148010b0300500c691884180980d03202c0c452030200c00c051000b44a80650020300ba22010300c1c01c80700d0000c103c000b420080c203900103c00d0100d145c0d03406500c00d49111042c2c5482d0074500740c50744e17122003280e0600188202d071000e485104811201d642444005240550700b500075840b5415480c1c072030954054004800011a402d0104010107a40060141c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 391123444 1250 391122194 391122223
    0xb0c0a020d020123030603061005030d0c0f06020f070201030f062d08070602071e12021207050301060b07020f0906091b040e161e050f130e0403020f15040203 69
    0x300700700940b0050300c10705100010396084034100d0030310428555210005520a0b90b0407004c0ea4059a5031881c8404803050ba40105030b0547e101c140b8907000580a804045419801140b180ea010000e503610b000a03640300c072290724064071020840c3c0c411541c06014204809105020612440342004441035480711448804444014140082c401c2c0b0b10740224100064040c030419282500e845080c0655a000b039880b55443e03a4481880100798188442c42d60390542b5414103503080000c5540c0c0801c80b102e40030b0249601c00c0e0040300c800140903a001d1245000804411385080d44403e50f1f030042200d4256280780701400780150780c040003040d940d031601813984012000a1007a0701e90301e4281d030741082d02980c1c015881d4201c0d00383c103002040c06201d250042001d01503903118488144041c03542c400c40c9200d076084020900900600c0c40090030f850103001e0400c208540300805680c0c904d2802c03604d480513601034000d40c100e000105c69181c418044031008100940803400c240c00c1913070110340d40b40b10100b45c070031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 391124694 1250 391123444 391123459
    0xe06010306210807020a0806010611010e100c1206090507090b070503040e07020f01050403080412030e100c020a0219031403040b07080a1e09080615033003160201060b0c0a02 76
    0x80c100303d892025103848a4010f010109400e850b81240c80d501c08081c09000040b40c0c83d210903568080050181c80c01c00d030074520103000980900802000603104c2d0312516428003541c1da04181045081d07200e4040140000349020030300d804d00c07490151103c80150072a008984080010706d001c82c20010444080300c02c40c000100303a80e6034500301281818080f841008065081106120034954000411406240900149112080c5001c03040d82150480203a182c002d8010030b03440c8000403401c0c0d0021050304c000d4015580c603041180e0014880f584401420f51002a201c00305105020f8410280e854000c2c0d40e100851a01d400d140407041c250007118001040c00340f001840000c901d118810514170b403140c4101000d4640082c0d00064411000d034000d401843c40ba51000542c842102080e0000c00c150150160a00d01e40c00c0c0744c40c1e01c240e2aa000c04a00500000c0c4500f135000c607a60000b544544009100b90503080240720f0000c1c25100c0642c00200146000d0102414803003020424144c1c169044a004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 391125944 1250 391124694 391124759
    0xa0614030103330212130b162a11010305040b010909020f04020a030e0610120b0414030a110706030b2b0542010b0c0a0c0f0e06010306 59
    0xd145030721100300200708216505044048000980c2c018100c4191070244000300f031ba4841c050a640c1302c07800f02000e0b00140c1d0700400326154802c0304800601020052802083c101c07500c014610340303405103c0c0301c000d58000c2515642d06200080300101c0f5850f40920341481141016114139031043c1060103168045d03030b6203041e061300319600c03e0b0344444641c1000d8025911011a0300300a40108078030042c03a050340c060700c00040da199403100b0421003030360092449400c0007400390b00d4400c1074140c000c208540c50b16000c51a501e018200300080c0212901076520070800c0d4001c000f8550904011f070b400315080c9800e09a20303c46a651304515245140c3c041e04059240e82074059a01c00da01c411003d0103400790042100a01c0030315204100006140051a100c00120044190105020a02900ca03100480aaa005010900703004006122842c8450708844003020940c450000f000525405000031001c0c0f04400c001c6145210040341d4060f6007400c082242901c0c100304450120820708002c214840c048180c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 391127194 1250 391125944 391125983
    0x70609051f08191407110d02100b060d0e1e0d09030201030f091a0615250302070b04081b03030c0a030f02100501080a111c03180915050a0614030103 65
    0x1080c01e40d070300b20400d0054003165441c404e03e1100c290f59082c0011909108180464000211103200c518141d008122001403d00040300412141c580c040d44500b0820508103210024009d40c08045094000b4180580207002250180217543d00e40c4900d581091201c4007600342c0083c4070004494080c28085800084550340e0b600a014010004181080a61413046038103451400c40348241015660514588011040000b0a00403000440325404c081014204d9010721441c110380c01500c280101e840d159214100035406402c25002000c03103078440d0340c6000740f046a80071181801d4100b0f4019501d00440881c40b651034003003603000070301403044100381007480505c02c0100c0c04010344690402c000c1c5586410803140c03104e503004402e4403010380760249880c1901c1e006180e912940c20b0b40c44d20500160b10ae42d0143d4185000000500c0c0c4402d8640c80080d0029190280700c00700c2901d100c00c100698105010492400041e07000181001540204018403044203011281900e0708006400705118101c1030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 391128444 1250 391127194 391127221
    0xa030f05300405010605030703170c01020417250503101a12010e10060605180609060c0607080711121308030703050409060501030203240409020909070609051f08 71
    0xc044001101c107448958040341d0903103460b0050303104100a00082d50740e4410140c0e03680050001504001165489400c0781320f402008284680390b4000150900d6912814450080d0030303210160040d070030500032a143d01c848584d0400d654607001d2a2030421608110110740d95118400301003150f280c0c2c0d4114a418401000300314840c0b0000182400c0d08172401d503691f64040c0c400086040d030b407403050079a50303002d01010340a00405c0e242c2c5a529981418503800c2d20101d2400390040326a082030342080f001040c0d4503102c1c010300381c3d400c261004240714103002c030005144d007070010b1485041160561491042c030001103000d94141c600001d480d17440f0420705030602968521075018107400c0c840002c4400400d50408003030022a681c00500704855039481c1c00650a0b44001c6074001e882110030355507201400e02980895550280c05440004c410540f6804155204410303a403801044c0e01900b01000107950060b0000d02418088d140780078140c080e65501c2c201d013200d07a460b050600c6440341c001040710340e0004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 391129694 1250 391128444 391128487
    0x403081204060f05090c01020f0c01052d0f0712090803090d0204141f06081e07020a020d2f03030307081e04030e01030f02070b0a02030c040314010c110a030f05 70
    0x408001300d0810302825a40c4032031180307107540035004141e0114501100450181e03409035068496500d001e81d03c000100000d054410040b01606407249801d01912220f400f0749090b030305c40e490701a65000681401c1d1340390b004440e2040100501440c0c2403040304c4001c010b0b02c1d00d1040686950200b030360284000b40103410140a101c503419046802c11a0a58018550b0b01c0e0701204204016820740d00c850045400340d004071001420762034000340c0d40b84522400000c8a43c403102c1d900c141c40301c500c01a40040e500d000c41e83c4090716a421011001030380c48850000b1995095050564000c0340c00c12036010a840f40401058002405011400500d4840315003445900810704c0180c22140fa1501b0300d80608085403000303a0b640081c0c030b090006c0d4000c102c240300b2107600681118000c0c103907035682c28070000070b0f500c01043c0d186807804c05e10001000408a000c02440382c051000041048001d1000060015080544000346d40d4444444000844d40244108640081910b051540c62080e000e80e40030786d60703809 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 391130944 1250 391129694 391129721
    0x6191a13150b0712032307050706060509040c0612060f03060c090b1605120a080412030b030706080609060d08030103111f0309020307080f07050409050c2d0402040308120406 76
    0xf0390b44100403c1083d05a02c00081d514200000d509000e801c200407a00f05040d0409040b400c0b012541141c001c40141880611480f03011070f0440d242d0002c640c050303030160740440312a001c60806028154000d0280d410790300c800c16040000070320b007002543c5a040244806045181d03146a61a1068410354000024110442405581d81c000c0c242c41070342c04001a81c151a140150a40400f0700281b4004803124070000d561110b0b025229030300c0701e80c9680b41b500078080525036129541038440c3ca0a110307040061480d40c0300d440c4140307082d038244100f40c00020183c600c650f41c0740c1c00c248009580a010349054070b8002e9240c0d408074031030348046210b40100486441441044100000303400b54960081240306100368159000959559082951900604017000c0c0c1c1d500404020b000c02e00f0141c3c4840c074494003c10860310110f40600c0030038219648103890401200b40f0002107400c2d008221996100d41c1c0c000d840840c03030507107141c6840b4a5402a840d0b40c1100761480000b04091203e10341001e5005802c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 391132194 1250 391130944 391130947
    0x9040e07120c0b03061503132f0a150c0501140c04090c14160c0509090f0f0f030a1b120201020a12050f0105060a090806191a13150b 58
    0x180d04078500c0036280c407401114100c1d000400801d00d901c48a096074003a44014240031520403410025203400e410040c0080c1c07000c51800070580201d1400800c1210700ba121841070780b09892041000c805080c2c2401a4030f0184c3c18001082000502d009091141440c0919003001014800d24019001d801100e0191003052115014042c403000304900134821549084410040c0a030304500580e400c10681440340701000091141d981c0c00a1480c40c503503440742c4102e0900d54543e0b01c0c0c03000030765400d0040e10f02090540c040101001e4400040101c440c103804601c00401840c2a292142d55581c1b040311000401c105480304e08070b540b682d0f040380403003c07258481034070014040700c114001d00039000003000400040d01c0e0b0303030300d0000c240c01881901c0c0500b40c00b42d800c41080e0700780014001c090b0301103501d0108111310400009000003080c483c050190901c605c1d4482490100c05c81201a100c1c401c481e11014a1001c07020261640c42c0301038481135110b072348804135020020020501801c42d00e0391140161680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 391133444 1250 391132194 391132199
    0x110a0f1107061e020c220623090106050c0a110103180302150601030b0d02100c0203030a02071d090c04200a051201120206120603010914030306040c031a0609040e07 72
    0x820180220ba901003004043c010fa15640404030303030303803400c05605c590401e40700440861880800441c4030300e485400360020580603074507000b4040c00910b0141000303000810303010703191a62801d044101e0041c101c500e070582c201001c144406803107808420b4000c20100c070300c40c1c1c14002a4000e0304140c0d584e40540004810048003814084c0d1609845003400081d083c40e5000501198040d10136442070190142c890008204258240710051000c0c1981d4002c0c062540031510051754100010801080154041d0120714540342540550f01c500c00c520f95151911a020400885e01c00100d4100f00542210080b4035961051f07a041051050b0b24000f4043c004000355022010307402200405001120400300580c07030b0fa075000700b200342d0b01d0b150724000e508c003008004481d04030101309405508042e004000240c200c07129624030025031402071410754180c101000300821482c00e840b928584000d141024403000111400d6118914855003c00e88a001e01249528203a1210341c03180c0c07a01c100301000c40d0103164 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 391134694 1250 391133444 391133447
    0x20c0a15090506090607020706030b03070f0f090f02070b070e150f040513022b0e060709080610050102071a120a0636021c0609050703060801110a0f110706 68
    0x285405082e0b0b9548145004108408000aa010712400ba02d40c06421010704060080b0701410501ea00c0700d074075115a001c007040700340304c48403040004c2c80d0030b010007c6c10600c0c2c00464010b5a4625010b540d16070710502a080c08a00c0c001c80ca640d0102c403515103040324601840c0054894041003c080034841400302e0701c0c0c802008070030020030a8504c111200740704100240040e030f0076031040b00c00781e094840030070841121250790220340105205180101044c0311408115903454040200c624a0004007118010084518244034540d04040d00c00021280c4a0410001071340c0d40800e4803030b1089039001c441e200192482c1d40010b8400c1200064600c11042c01c25040302030242c0524054030501e118040c1e4951400c250310000d1103c0343d006440407080324924402080000c5d000b001800344094070301c483e0421841c5092089602401d400700c0006018207000100400700ca50340c1c0c012411aa250900e07154106584509440b58218185052010b07688203200403140b0464480c130f2100644035468000c41c005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 391135944 1250 391134694 391134701
    0x100614060a0c0f061a09010b0d02030c04030f0807111f050a0527210c0616060e0a11040c090506070c030b0709150807120b0a18060e0a0504020310020c0a15 68
    0x8402c195040d81e0600b80b03003002c021246c9000c2c4212036400004214503054070885030080e42e403100c0001c1c0400c1c103050b900e8403641b903145200102203540c080001a0700c03007000038842c2e40000007001a1450102c01c1c0c680e404145498840e44448000c0c80400b09108030158442c200315070040c170400c034600703052219980d8012001044c240003070703100e040303440b2180740c94070709403c01c800380c003100000103080c2407076048181b01c0c60b82d00c5004800c01780c44400031721a0100c1d00320301450581c02001e40040130425540d081000d4803062035007081d40b19500703088944490750343c441040020b4941c11540155105d04928003151400441e0340001c14041540c002c02004c1d5402c02c4402085460112510b0485e009509040721341c0c00d000c440c0e8a0228069214800d0345207115404806510400342c00200100e4071440a1480380580b8429807858a840d00700620a01c0800e5120342d0700440c1101c0c00340100e042c1a80000d443e50303900003019100c0c51740403540c4c50000108000029406410040d0011248403000004018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 391137194 1250 391135944 391135961
    0x50d0804031416030b130f1104050610020304030201080a02041203020303011403031303080c01090507120c0906030f020111030f120906072a2102010b03100614060a0c0f06 75
    0x18200c1c2c0c0716000704001c50218070007045a100c01039003031146046551790286000d01401c0003050718518000310b40010042110540c07894002c660b54608a0b6040c81040306451340102200e005207680c0955003081c94000050f074090f01d50909150307015540d18181e03c002400349911031003d0814180010084c07640100c0110f0599540c5103c01c1d07503459104040c0f41e80d0b88202d6139405642c41815004101203215a00580710004840001007180190b60701c07418a0260190072401707840c1c000381c0054040281c85501c0710002c0c0313644036081c0055440e503103a5407408801c020019040c84000c401900d91140140b080320000100000a0b54031a24611200418140c0440c1e01103440e202d0303c0042141103005a259440c0e1102c20703040c2141c0b108160203483d030369400c50f542c220f0340340d02c040f140c84c0c60071460107491a92515044d4000075416080300105403800f407005502821072460100c0c24030020600d02d891100c0c407182510b00c50758580f4901400c0b0f0f0400d9400307a0160040e8030180c10306c401c211164000004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 391138444 1250 391137194 391137203
    0x2102130b090c04030b010317090a090b24030c0304082503030e0f0607030e0304120f02040507091401030c050405091321080412020a0f0302070608010e04020f0904050304050d080403 79
    0x42d40c40050142851007035000c007400c22541580100001205d500c4241465500603e1880c101001d40001c110240c407660010b0032000c0d00c0e21a00901400c041c00b02c2e201d600c210000040050001b20040300c207610002c1c05000d803000000000406201c19601141c1581144105104c1600210500c4107800355a10008a002a080c4488142101c500140e80c400c00022280501101c1c1c84022081e0010030451b81035420300c0c0400e010006040c07900314044c150081c000e91102101d80e005104100031190020a400c080c80310b02d410510070101140b40c42d8440c98400e0034001405981820240c5460049a010036401507200d420064480c4141c180c41d11414882c11140460054100c41c481c2085807500d010b10001da1040b0028000c0398090b0f152100c2c0d03502c11b006036019810107440b04482041161016230241e03208581c20015907500500181c010601c02074840514149503002230380d1400110100c40c412640100800d0501c0001e0084800400300104001031281c041c2c501940c02d41c0083c407050b0b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 391139694 1250 391138444 391138459
    0x60c142709010b030f15060316030f0c02011b0f32030c0c120901050901210c050a021501060c02091504060906090b030c010801170106031e061508072102130b 69
    0xc1406c0d50314681074a10301d60040056080d039444038100b0140a040300c40d004101034903034030400c08124843c0320312040d411443d8000f142200d12401128980800c00c0d245401708159000804203c5500a0342003500c414010202590820100b01d0283c81c0075611155120700307903000040c070449004100c02040755000c124140d0f0b40030b00d91404890100c1c064000114041030f000c1001d04140c0d0b02c0b0740c0e03886d02100c10420442d10805440030040d0100c8100040b2071020950000740740c45038036010050351140e442200f030320b07000315810a440245070b00340d000d00c02405200c4542c08560240103401014104a0780038004218a80da40c07881c00016015500c502040c4500e41018520f03142000324000c414608184c551fa00c0d00d910300f1700310070707032180d0151840f58040d5680c502c044001510340c0d03003d01c802802d84a4201d14820f45084c010201e40307014620943d0081000390810000d000803c0314002c5580d04100340845d50038014094040003400c160003980107074150800a040580da502c28400c0220585186 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 391140944 1250 391139694 391139701
    0xf2406061b080405040e030f070303021c18110112110d0e0705101107030803011e06050711060a0309080706090c060206010b12061503040c03060c142709010b030f 71
    0x181e803224100006440454100814001420242c21460a1485510451303203080b441050540060f0400d4108500103600003503941241e1a000040d40d50308440c1344800c101c1c144102030007020040842c0c4004003480540003110550703a000c1c21004544014071401489500d103100340703102607a405007180d40491454038105041c2c030340002950b2030983c2ca000c0c001c21441c024480050300c143e0342402d0303110020b2140c0440400040c0119000d14021300c42c0611411904400340200c0320840c84541042c4d040003024000c0300c1c04540000142d00321948187c96003a6914080e020403000b408241d803010700304c420006401c204006690f44010245400f64100350325942d1540c004a0b1250004c1c420140d040005100300c04401e81d0000550380c1048000b415a059103c065091000c00d400464040e1094480580c081081c000c0d01d000d200342c0180540b03040d1000188041c0799a00720b010761b1400030071345001c2c4901410b800181e031858007504003006025689544c1c0d905d02582c015031046640c0550b284215010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 391142194 1250 391140944 391140977
    0x316031b0b0411150a030504120815042412020a050f130e0c09160e040b0a0b0706060305030316110c13150b0a0203041a0301120f240606 60
    0x4150364040703503a0445031256102e10510a4441a0280c0c0c0624140320030700542908000800b49292076480105d41031610342007544250b40880c0e0780340280507461080050754001000f03095039038441102c0004d010070f503009440c0700444100c0e8038400c40b50004400818102d840b10405001c1c40e20807503440e82800d4030360051107a071040c40080950001004417111038150100e80284984140721403c55040840c5100002c05021003526030004043c00b6004a050b440c0e402802c0e001e0820f070640381888141d6014001c1403640b0b150b40300d00310400d103010541d00100b00c80e68100000171600002200e880f41000052518081d5402c0700b540081403001988030045000416000e4000d0310040c01500e061441c04540000780043c48070259140b48030b884081119118040070740703a401140d40c01103481c1d0342013104c1c1d101401142c2140d1001000103000412a0702e40850344000c1c03403944001e851010b00c51030f14041140315005050640e042c91030440d096850b005a030f0211049583c0b035075440c000180d80314203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 391143444 1250 391142194 391142237
    0x201110a050904150f1203030b03150a0f0b03060106050714012c0a030e10030902190f050105031603090f06020f031b161202070b0c101d06041203020c031603 69
    0x50102c0c07170600702d2403c02c6100211340d00e40080f14001d08000c102c1034801d0700000d040481624000c1d26158841c42440001e0405102c1c01110381106038080044c0019680080d07502c08051098204002000450200b0002c0c41c0e8801c03204040c01600904c500103403101d00c103c0d01a40e60002c5a140c00d11100d03030403209140020500300c110b4040d200c101e07009540c001803000482c00400071800b81511619402c0041e125052401c400c2010303423200c140301900b825000b005002907a44080e04024040c001c1c0f00700c440040c00c1c11220b805581c14001a00e401300e02d80f45210b542d0031031015081c244003154140721401c03401c0045204082c0f81800441e4a002905601028051402c58014845003408480c0010300d00c821801c2c5602c0c2540100c4001603a1015440e00c5980075105c42c100c20740004d81c8064082c56280103c02003004a0442c8201c1f410000d44802e583c0c42000340041c001c54151200e091507213000f42e04803031002600009407655000403810444182034047e03011400940b0340d1402918890300340a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 391144694 1250 391143444 391143449
    0x2070f08010e0c1c03081806090a02091003080f0c1c020309010305010509040f170d090501140705070201020a06050606040f060e030d030b060a050906120f0906010f180203070201110a05090415 84
    0x140800c0150361744086074008801070038014045211b40c42c203100c92204010b6030388038858950003094000c81502c18400d03a50303c040c1451020f00d040080070b0002034980c4056444911114005640302d4039010030307483c0750260052f5a100764034502c0a01c1000b2a078044002c2203030500c00c1c4c80030f000b07030f9a9800921550060849019151010702e40424001880c0c04461180b020840c801240c2410f00100800040b1400c80c2f50444003070b07545404048084100c0c040c0258468104c0c2400d1b4105109038002075110f1840f1200202010ba452001aa4550341d506c00c0c1e8015010361028502485d446100180542c1c0260129034820f02c18140c01ca85640d03c80e00404900d104c0191080e130800907456001e40d41c680014207541e9000a00340969445170080b840160b106541134034006125040c100140703801c000068115645550085c0028402e14082c040303030104503401d0310b80060381c07135540c003034200c0c01440c0b03c60110303501d03c2e40010545034850340030025180d000c008407070402c4090600c03404482e040c0c0303003031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 391145944 1250 391144694 391144729
    0x60601022e11070c0b0315240310080705030312181f0c2c060708090d0c1508240f19050f010c0209060418060606030204031707050a1202070f08010e0c 66
    0x42030180c550400d103811042230104c0140d10303082015995041103c03030b00f003110050746e58a03490f10100208003080181500420098026503d0b10422032040524180005c007a164052503500b081030414000304010018241c402c1041029070b110002e05030080d21100f24140001030000700d03001e90b110640c40d1850040c0030450b004c0c8555500f0071051146075000010161900c00040c400881d5988a003404068036500c03c1050540c081d0030000706101c1500740c20321003406c02001c142000307102c0d80c001c00e600401101d1a10f1040350841034000042114400240180c0c1017a40d2406031403032116003c50050683c5d41c00c40d0408481281007004407601c00070404081d40c051100c6000c640a8107140c3d1006c08403a001c0b40d0401e110000780d44880c81920800e50110b00080e13800103040081c4460318109080d2030204040c464508860ba480d0203a841d820400060501402e003113101c0e002e94002c00810000b0903080000204650b95030030010300070840404001054000c0307403508a074030701d0001c0048220302101c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 391147194 1250 391145944 391145971
    0x702010906030b10080c12010b0702090f0c0f030604021603020c0102010615360b0d1107021e12010603050606030705191509090603080d060503060601022e11070c0b03 73
    0x40484500c1740140c100c4104960400c0013802c1d038401d512409010f8405005140d46e9403801e031060001c2080000d05600108801005209c0c0c0000090200d48201c210960f072a91a52204000280203100d449074103004600d03000b0241c81016000320b070245000344240c0007040910740c2c51a04003000503910b0a0540022501088540341255048020b81101900007400c207183c4180f01040c00700700724940246158850100380c0e04002d00e0706000740c407040041c100c66141841300c10342c04203110b0b602150a00c0704c00301b40400400c1042c0c0700c413001c940c40040884000d00c4502e07601c0c2451900d48500350b42190080c01100808606428031200d2000b42203880342d0442d04183c90807000180c06807420003000104100c100e00065429400d0048802a50080824603980c140c03440d521800c607149a400070b8081d401c82c004000c607581c0c010482d000a001a01404900203070b01c1d4020906481c000660704e24103d10700a14640c08201003000350041501c580c200c050303070b15121041008076000488991481024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 391148444 1250 391147194 391147219
    0xf0a06060c06050a06050a0e0f010f0609030b090a060f060503060906041a190c0906080601021606031107060c0305090f0a05120d1e1a120706030e0708030309030702010906030b 77
    0x1030b0341d8041036002d0b426210002e1086d4030303040003a800100c0c540c0820200c000c1007081c80b240503980511640100340101000244620300000070300032702d085101c00fa040c00350a800080245400303000402e6400c1d800001080481000e2020000903d95409884d002c0d100700000180440e0b400185c02c1c2c000c0350008440341001110845403401400002c1a030690700303089140c900c511340118080c20f16550181d840300d0301c1150800900901914005003603030304541c800040d0310280003401c1c0301c100681e919454086004e40c090810380c42c2a200b0900010f01981c80e14208255280c5d041c1d1140d4003408400b81624003080410880a0740ca0803c1c00e005040c981044e0b880b101e12038400d0004080a81da00303903000c61010030700f210010b1041110f0140560b202d4450384c1c0c1826070000703d4100d0010b08001c40c0c1804885080c3e0708015919802e9000c2d060034503a41d0400601034400401c41c2c04020144402201da807840c0150320243c5a07000240100c0c01315030395040202c2d025000703008020420201801309101d600307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 391149694 1250 391148444 391148453
    0x2070b0702060f0703050d090b07030b0906090a200f030411010831020402190e0102030426160f030c051219080c0d0207031709100f021606080f0a06060c 67
    0x103004c030310110180401007010003805003490080c0c0e440ba60150542d00b10074500303007802405403241c008419100f079200038100109c50341d5083e0501d400c102203090000b00e42200e188400e00e504920080311f000c400000c105404c081b0100c4000b144518855001010410910b8005607402441910f50b4000e0344448980c2840c0d1103036113904d5000d00c56400d210700804032171980204040303078890b42070501c648211000c002421504084020803a02003803008515141c6003007140c21182501c501100c050b241c070010329007116003040082c13150390110302246a41d030960342c2192500c80c2c60383d0700c4110f66428010000191030311b00759000400030912100a44100b405140812030942c10900045840401c00d100fa860b20380010841400d1460b0710390000d207001401d60a20001c41d50801c0c8040c4140e090801c151441e907111b51024007101001c41c02c01d82895501880140d061098200d04a407104c070b00b480c000034000e54000c0b6828040c41d00e005c2c3c2150a0303183c551991085d00c07054000c44000c43c00d0b2400b1500080c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 391150944 1250 391149694 391149697
    0x20111070b0a110d051806070c0b04110303030f2203120b2101060614090a051212031303030c020c0901051908010606081e0f061e0d0c0602070b0702060f 67
    0xc8801940042d00c401102c0391040207400000550b0b00c020703528810440c400c0c213611030b08240c071610307034004007031908e08403c00400b0075001e000300400450244011a04100c0c9244d600000d5130b4009040e6034403407414000c4113018900450310150a50020080d6102c014000c2c0b0240d410b031505035a501140900030b0340c54502401141c241980c10036182c10000c203044440e148070b11b03040c82d02c840021440c145080d4004000301502c0c818070781c4110041003114610f07503544218008031a4151023480307c1c0b00040c01c0f000d0600d4540301d07588542078000001c02c160032901c0f290743c0c10981d210b0313141040740740c4440a040b039988502003041a0085903800044c4024945440003041d06103000c0c0198210648459945096441c40d030300402c0490030000901c03496000c00d00c100205103510145041e441d151240300424240d03006003540740070b80d0600e00c08442185401c500c034242d5040161003225079108529101500080c588900d60040c06a003c010561243c4402212000c58004042c5400c2511544070311a89 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 391152194 1250 391150944 391150951
    0xc030903030e0d1709031002161211070e06010807020a051e0f07091a09040b01050114040512070602100c0206010306150812030105090c09010210151d0412020111070b 73
    0x124000c9220800040c3c816544c0b11150541c000e0300c05d46514003c000d0614003245001201c24460052100303400ea20940703414908880e4000121500702e402c00502940e400442d2500b0b41c811303004034640402c2c500910000940200030070b90b07030741c2d803c1c1d50b81420481c0c5842d921000140706030000c0d0401c20b0410a05140061803642d18004e03541c000070b822600c0382c6020030703da202c07200c085d882c1c40d10303100031000b1828221003411040c1c551000324070b081c2c0d41c4e101408005004887c14010001580e2458407220003e980240c0340c098005024401c41c208590303910200f500c6a1401442610301114042940d4011001e8868403a0000e002c0c0c1c0e402c56440c80080c150b83c0800c4d08120b9900400025040010404030400c05e0120044950325410107050204072440288141040942041103c42990340091450310840c40350307000080e00c06141d01c00749101041d99100300c030b045110074100800340501c882d61a026910400060624080310170003a403c1c1c4030001072182c1d110301c007400040e0203c0c1807003000310391 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 391153444 1250 391152194 391152199
    0x7080a0c0203160317010503012f0d0203040501140a0b1e030307060507090f060e01090501030f0603080c0c0901120b070c060212101e1a090402070b0405060708070c030903030e 77
    0x188006a0f60680c04200903e5095001440c00c00342014584d8011000a02511040c1c0080c00380c8a5071000d418000410314040c03a0400d40d07c1002c83c1034281e00002501e9141c0000c45040d0364906003801d049020700000034541c80c2901079400880c0281c002c920441c0280a17000e0070100d041140c40403080080488403c1041d0540000c03c0410000b41c1c45110719032040d9000e441c2c2030069402c08105120321308140d0400b401b8032030380c50410b6036036a0300310300c0d140d040382c0003481c0110b02c00c1e05002e64400034000759400204605004902c8003030300c000203c0d1000d8810303800d40e1900c2c00b580c0d031041d642010024468001d0407503442040441e803990310620001c0300d201e0041c1070151034240e031000070300d2407a1012a41001c20701d1001d503041c001100c001c400701041c4042948901c50b000d0a0207180441031b1540c400e401081500003405036074588864040d0b0718903541014070103106180c20b040603502d4001c1141e003034000070502000206254014039034200c0b0a074065607080d40303c506580e003d48000c2c1600e2803c1c4d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 391154694 1250 391153444 391153447
    0x90c0420040e1008030703021c0216090203181b040b010203040e04030e09010605030f06040b0111061008010e061b0304020a0b03090a1b030503182202070c050907080a0c0203 76
    0x34902500c40040004000c218580c90851038254a4005124081d4210568075002004105d000c039500103030b00b003182e086049501000d01400f0f03105910306035012804090002d0400030008142c442d541c081d40c4070f05201c2c8500b412180d105200c00761158622002c07919041c1c0c54000707550b050b0074268021642c04106004680c6803a490b03140000142c0400c6408800160100444400d503081c1608504d0051143d414003a0a6051500b070843c40080010500ca0003981d544e207690603180c0c40350f0900c83c044032814064805904089452201c50803150050403c0b942c08c00690000807080002d01d00d12420103a40380440365400101041d0080e0310151040e0303032014101e8070100e001d10b000700086002c0d100f0742000341080611494405054030000506c8030540014810070404900d000c000c441040c80b0f000b049144211001001a28211100030000103a20764051015001050b40c7d0080c05241e008088540d00305a5401c00c10030284000c58091000a6000e00440d120703000a030440d14544140d4015139 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 391155944 1250 391154694 391154741
    0xa0908031207031a0d030e19060810060503060109030803092107060b030606010f0302071515090609180b13060c170f0f18160303050d14090c04 63
    0x462840d0855203444118407004414400c506030184950500c1010648011907a20b6031500060213410070b0b41340150070f000c03154141c0d078440e82d02d14450755107113010701c034041d01d1064a4007002808010110340c200c8900070945804a84070340504144c0f0701c0341005075510144a0304550324121250800360a00340315200b96010315004080c0c401080207400c1c510042d46468501900302002581e24101001e8001e030001e4080c44070a907404208020036880780d00b030140c0ea0302040c3c6404908210b03e0585081d40320302d06480b41214030f01050182c000c45038840c1041c400f054580d1004421240d03802c4003074000e09100301c01140043c458040ba0b80d401010520408002c05a81e140c18050302c0308500c2c0303d400959040d031104030108060b01110741180c0d0342c041d10701c081d01d011919070480520141814091200382116503c0e2000c0400110301e00c01a18081a1442c0c3c0c0d4916014120780c0000c542c0c0303d88103003082611102054131852251107040b8000061030340f80002014013000301001c42103928403d1084914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 391157194 1250 391155944 391155959
    0xe19020d0c050a18050102190f1208040314030606030703091a0f16020f061503120a0906080f06030a02040b060706050903090301050603061003021005040302040f1b03020c030403080a09 81
    0x341c01c055541d80c0c48181e510f1092050062040d00d030f00005032a0701603549810700482e46d002030044a8011011207100b10b103003123806c116911161460f0b004003110f07070110264460507880542c20b8026480ce440d00b4842e10081c01d20300c1107070b02040310714030b4006034180f0004d030f991882a00880d65490003000c002c00300c54001c0ca030227030110008a4aa00f4040309074002d00c40c2108107040c45000d040a180301808460490318620f5441d00b1010f4901d00d00030041c0704004407160303010b00014600300d000404480ea43c080d001400781c4019403501c44c0c0700110f003045000030030800c81004090302c00c400040c0904141401da50070000144800a042d541145003400780c140001d5061003914003600c0040c000355182c010940401d800d68074014005400ad4101d00140095001007240107419207a040301d10018213110701c5001c450030700451340b000c0e6009003400041a14002c1607841440100300480e0a8200360028410580a0b03214812880d1603c0e070040100700301044045e0b001c1c0c10010300300e1901e00030712039481d0754 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 391158444 1250 391157194 391157201
    0x51203040c0905070206150a0303020c1302130306090201121803080c0d1d0f0a0f1403070807061410050604061b0606080d03230402090603010e07080a03021203010e19020d 75
    0x4165015a000400340000d80068840d80e40d0780c487c048820700c20a50071a070b0000e403500c0d600b184082c01001040c2030039080306c0641d0180d8090044d401c12503102c1c256a828000b0240c04003141c240c1c003041c0107170340e81058180c4500490f014211003400c846140315640d901102d0366840105050903c01c024000d0f465042403500a1508110183d821072a0b44a9503001490502c440d180311103003540d21005038880001c10880c0402a0160400b072008a450ba80318411401d40c452050024240c5200249280030050940d001550400380e2075031042050759200854915003602d8001d1983c020403d00c42080a00e1145007030844004030192540c005c10010791f200c5040c2c4220b50440d04140e04800610060b907a41442000a081d03200004140c00542d03025014500c4400604064041d008038400034045813025041850560107100c2100c0d58503039203850311502c611040e0412070050286ea41129031040f0000c0c281da042e101003081c03081054454480c240c010003e103c8122072100d4081c0042c0011920611 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 391159694 1250 391158444 391158451
    0x203010e060c070b1510180e0406091505060f1c050604030f08071e080903120414010605090603070512160b030615070308060618031603021903051203040c0905 70
    0x803909030f122121442c0c5520510401098203080e070854404041090b9110a1103c12040a505105c6c00306210403a81301414142c81e00b154003011110403e020030070403a41e1014031329601030341912045202c1080384100ba6001038500030343c00404c8444c140e0461520300340604226400c260400f01010741551080c0c103022044a040d000300c4c40403502c1d0700c1d41d640c000421130707827200d505e1400240040411494a06a01c810080b44040041c3c80e0300050001c0300c10001c0740c030141210340e1543c9180c5040d1030441005485201140ea5035424a0350000c1c0310f00380301780780c0e0380101c90083c0582543c1c2e00f8482401a480c121905150071417084041d44000d41d401001d911010b4038800201503982e2070644203101036010b44040381904000d04100070804207a000c0c22803904440c044a005540310303111452110460b480d48001a814000c24569501f80c00140b4400c01c00c4034801d80e4202208840d6401c080344003207180c44041c1c081c5c0c200e00307618079604014030015a40184501c60820f6140c1d05d2fa038000e011200c2c00c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 391160944 1250 391159694 391159711
    0x90a090c0810051605030c0706110304060b0a09060e0a0c090b0a0207140d05030304111302040e040c1703041203121409073503070803091011070804050d0203010e06 72
    0x1000b10002020700d8000c096004c0c0075030b450350114111560008105100081880790081c03c01304030202000056004400341c860441c80494980c20b160600034018207041a50620412003014002010300203801080200c4850040c1280301c0d0b0740d039000d50300c041e00201e5a11410001c0d440c801240c04210140909500c1006038010004a424504c2d8140158000c0b100c581c89404046031030741c0025000022654840d03480202c515103d40d1000210702540c0e441c0703008130400b03400882d0124612000c254104d1141e805401c01c481d800e6543c1d0714a030520600e41c00c002189400821052080040400311225000d20911f0184002580c02010350111140403000c281c1c0c0c20703020f0b000d128009908000702c002809260b410840c040c00300001e055900003065680e01210003c40040050031701c4180306a601c4039410080150341c2c0c0c60800115500c0703c41200c0c1d880032940c508040319100a00084c10f07662a1544407103003a19141c204410414000d002c04e004030313419074845003044100700050003142d0151014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 391162194 1250 391160944 391160953
    0x50414030c030a0c1d0408180109150201020c061305030a05131d01060f1d2b060209030d090509010b090409020a09290307030201050304081e0406110c0a05090a090c08 73
    0x80178801203010b191404483d40304000f6000b44404160950116044001c00c8a03d211400714003a0043c2c1c3d0300324503075000c3c8092083c8039589881c0385406400400c007203030008d410390b0140c1d510801001d05a0076110360142c4030b54010b0040d1030b06107010318024034100003401041c80341c982c1c2c0e85007906006010102c1d41e800001c0b44c48010401c41d50040c00d80951142d031341c1806640803070130704044290f22000040c01841a4802110420113911920310707420a01c110241509030003220341000d101030750140300c0d941e0107840754140e82107145214400c9081510801001005241d1030f044d404101030700702190a540c019070b0390140800503903400c50444018040740a02080d4025078840c0340070f002c240b4548200d0502c80015980100d6a800700c0c602003540e03824284203840351101d0134041e032603000701da0103070001c61710051720b0501c2c3c1c500d00001341c01100c01c0c543e0354107030070111700d8219502c8200e0743c00100c5e0080300505041c04649046410141d000100510000b40c1054a4440489a014690007190241c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 391163444 1250 391162194 391162199
    0x1c02030d0c051c1e020d02070302060c03010b0d020a032a091202540c0c0c010806030c0312030a06080d08131a090f0f0706050414030c030a0c 62
    0x2034a00400c4840201810700e81d040411202106650000c4070f1046001c0c240d40b4501d40c2c91030900c450001c410100c50b031030119100d81207075100c000254800710056015200301c400240700340072000101c1c1c0c16a01185001c078105001d881505029400c01e00d1807805041c0c5076080107005c3d44000d0b0303248600e050b020385c0c800c98007851504003801e51265908210303481c00078008401b0150300d9240310044645581100c03401f60300c094076a0708124090710107404124400d91340d84c90034948980c26400c2d01040e006e0303811401c19120707588070b400c2c98400c6201d6a56540c000b68a0352070740d58080e0745010b9003c45e003c1c051300c001705c14481c002418000d05a000700d0702d00c00040705200c2e42c0f1240b0310418014066803401031034030200482020304094001800f64031001e4001110404002200b0400411254001898400703420103000e11601c42e011101d40d900d1034880d001282108000c001072041c01c1307607103a8031107519050800d603415600042004091b600b62088442c450700a032010018400c0d214081d0009284260 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 391164694 1250 391163444 391163467
    0x1061d07090f08030919031a180105131209090501090608010e01020c030327070b0415080105011e030212010e2e06050918010b13060c0804060804051c0203 68
    0x840c0b034102c841c080b00c60320002e0002c51000000c03100508800c071418440e40d075616001e49480b203e80e800080c180020511201503036099207100c0c42c0503004024525044410515885081380e00441d010591341e9a4051f55802007071028107801e4003d9490714010b40700039183c00784682a40d400b13074840c208051352a501044440f03001e202e079294080c441d400070351920140b0062241d83e80805880c8140390300099070001105e0022540300c3c0ca40c00c816100317941049036107140a2000750050700c0380c440505282013000500c07512603000c07113068920503140e01400ca8005001050410906481c000c149a0300304818072040e441c0c0b49100e4001e1898518010700b91404040020003850301b5006030719031904c11000c11200148811300c50f4162122450620b88a00024001400e8107414202c0c207801c114140c80082251a03812005090321110081060280d030360710b0904035400c1c0c1141201516591007804140200e0748984420342e0490300440c202c900c44104262800c199200d11510300b000750f800061342000f2075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 391165944 1250 391164694 391164707
    0x90302030408150c04150c0c0b0a0305070c12030b030a0c03050a110303030106050906030604020706090605181209040b030a0507080c10031a040b2d09150312070501061d07 75
    0x900b50580f240e9900701500001071500650058241c07800441c0a4030040c41e00c11240b030840244c00036211032146e0b43d1130211100c150300403800d41c13002074148400211030501940c108412a5480311201c80251f0748280220001c3c1020f101455050190100c14004502c0e4644820051800341010b4011001949042e61107a540c032400c4a0081e0814401001143d4200056520600060368a1980c9940e038500041c001d1140400040c890340c60600c12009000c2c80d83c2c0007a203e003c20070080504900c661900543d0343c41d40090860400b1f408110520361410300341c01c80f8004510142c101c61403040c0590b1610b04100594029182541c0300e41c00782d202501d01509800211006800d0801401400500b0031074000229031026008075240e04e5084541d865001910401e40c101d44281a003001c00c20759209105203511040a102d04900c80109031035015541406140c980d005000b01102e98180003142d8081d0030100098409568440001451080b61a580b542001124440c1001071405005c0603244 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 391167194 1250 391165944 391165963
    0x20c01050f0609011a1605060a0e011a0f060d0905030d0506040b100e01111009060f0c0c0b040c0308030406020a110f07090f1d1507021b0603060112090302030408 71
    0x80480711824007040d615000100c0b030564411a44e821022074040e0b201110034410030b00b8000c40d4110240e80701062040110350540074948601e403d111381c141c9071034132034241c1c3c6038039054142c5c203044541900094640b0541030001003d01034541ca0400d07280d2910b0300121044200c0580ba036400c0000d00c450740c05081c1c0709859210108480c2000301d40442c0006c01d404034030508080040c031030025080203040c4e01481d600c1100407001c000300c640e690401810300b00a000814411070300305040c6200100640c403280900d403404007269880014103541c0746c4415083c860050400c0e190422900c0001c00403840071401507100d64040d02026940d44030b8004000c2c401d100c120b60305981900054602c201d0110086021002c50707011090200305462024a05002410800810018000007440c440110b040110381d0b0000b1002000c0c01c4001951079107170503a2900d5800d00c1441040741c659948080d04d1500c0c8015540010061400c5040d13010100e10140886001c2c00081e00564000300303040001900810801b141c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 391168444 1250 391167194 391167211
    0x504031a09120313020a140109080f06150d05010c02160e070c060209060d0501030c06021c08060420030708011514030a090f0b0f1501050901200705040e01020c0105 72
    0x40354078101d5960340d100c00518900241095002001c52100e0380e58034688107400d41c0041c0201c1c0d4a95949110911a0700003d01c1d0601180c8a620000707606007002c2004141e03003030342d03802801c0f16076070384900b8154a03e0f0360000503501c200c1c0301d002d01c00071560910440d401000c0700d400802980004099080780c4005030740c0715040b071401d05010004450740c0241c0070070001e50b00070400368661191200041e030b18051105000512031501c00000240554140c2d81400c4580320b4003506c1c0b01c2d07030f0881205860545a010b03540c0116800318046151402c041e0310109406520042881c03180080c4c00280031076500a81ea010006913240c001803240304141c0a00c3c110a50403420001c400c0c0200f4111300006c0c0c080240320400391b56484410b4014424220f44216003241e00c201c0240c00703072404045812101b2400c1c0d0322900f03015981082ca0041e54081c608489074801c05843d4000c0d81d00303041000c14408a00e010101015001d5003d00003143c4c1c541e40607161401461800150301c500309032074007600311100100041d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 391169694 1250 391168444 391168493
    0x10b0405030c0108060f04090320030403030807050904020d0e1b0307060e06031005040504080a0816080609280b040f0908041a0c030a090303080601081033050403 71
    0x440d500080c2c2d03a040074400b82000034030ba55902c00042c40240074a002281c000d070410f20503c00b0141d02560010081c2c400300c0d01c0c110b0f1f9075110304500d80d49018078007000300412004c10106082901490180445420090016181c4200d802111040d00c0004020b8646c0d40d0158054010034918104400c00c404025001403541c649400f400820000f2080a118060040000451071400407000100e010300030140043c4a80d06262a006507140c1c0503c60500c000b41400c00840d18031707171450701c101544411943d11b41c4442e031a101e00f00101c0c1440070381024840409413403990f900c0d000050f0040c00a4400e1500021920045420710055644400546611034981001c0d079000600100a0301c0503212413180804c54014000080e000d9807040c0011415540710100c1d102c1c0e9400c0e84a104403040c0c2e4403030b40d03846040b51504001591a584151040741c0440e0030001c00703202c4c0410441c260084005c0c20f032804140b408039055240e5440c900c5500c2e600008400040600602c1204c00c100844000b21802c0c0c035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 391170944 1250 391169694 391169699
    0x13060f080417070f0c0b0a0801090605093c010f0801020c070b0a0504030516030c090b030604200d2001020a0507031704030813030c1202010519050f04030605070305010b04 75
    0x80b010940380c06000390079481d0106801081c03241c084244080a50300c44d2415102039141e20010010703800002c1048006650720001190031415409582c04480024060b6840c0b40c90340d00380c0e5020f012040c46101841103000c030502c01c00401501040d09210358400c80e00504cd410419440f4600086800100c1540c0c0100f000f00c0303c070b01c40010740c40100c4482041d85911a1345200c4121828422640054010b1040884100419041002e10812640b150000c41e01c07403983c449001c0d0a5a82c064141c550580182000030701047c00c041103c540c5107010f030381d02d40e42ca50800000400700e58503000c054414034002d0581000c2c010461002c21240d400900060010584980e102d582c1d808030303404020300c600042180064180340700c405850240d60301007800c5840e4107014825004000300d85c40141c59240c468900052420f214480c606c100031340603034803d032800038840010380c1200613240c0264204403007006002000b44e903440c0504041c500c11500401c60303042114005040c1c03901a000000700100402c404c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 391172194 1250 391170944 391170953
    0x30212040f050c0a0f14151308011812030f0219080906100302030703120e090702031e030c0f070807050102030403020a060605010816030c111f060905090d0c050f0313060f0804 77
    0x550040725086881c0c1b81142003402c0201f6400041c103001c0c016686008114124200400c01c0104240c507010402007000c01034100360720b10880307040140a0a001c5c0ea6102d0304203101d01c240c000501011040b40054a400040441503990340660501100002c0c80e039800e01c42c00d02c43c203020080d00420081c900d5031b485030070750300080e8131040c042c800102000880e0412010b0140601070050300c1e000000c02c40f01c01e616040034065280d03440080380016404072600c011a42c86490380c1a2402407011000d02818a00920000c181651001009031071804d014003120380058024002541700764441da01410084620703240c032034251001900518140070039401081311116142c41038403041c143d103150105859041031130035114101c82005032030b494021800c0c9011400300d04903900c40254084841040100d03a078010500848005a4100314980c200b404001c00e42d500c100402c04e4902e0003a0300317403000300050440c102e00e1a84521030307440702d814124204005c4a50051150500c001160402c3c07042407410340e07203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 391173444 1250 391172194 391172219
    0xc0403080f0d06120c031a090c01050d090516030c080d0f030f1b031d01020c100207081210150503061809031e03062409060901030212040f050c0a 64
    0x15020001c80c011440031249034041d0400c40007401100910800c041450034840001c1542d40000c0d110110101c40101d05049441405c0d4465144c6601034040d00c04003600440e401c0c0c1c010b01e5400d103465121000c40c40030803802e012101000051519501443c0c0c51407410300c154209647c4458595041414003c5245420200100081623903180024100d0005500e00d40181600305411181d14046115039000940581c840390701c00030b106c2c505960b40681050824240e11944074809000d070032440e040c212404c50fa030060032420b8811240a0300303001100a00450f00c2d102201c03144071080d0214030401400420401100f10250341d440c2c400d10754a006030208010900c201c4034100605210300010751000c0d001d00c1940c04048426400c0c1c1252203105603031040ca0307002900c0e114800c1d8013071403152640c104c00d0441300751b8400c040c41d4982e041c40300c08400c005d03a82d000300341a036061540070464540d03803002c081c5107944164815403103c681aa07103030400038034180c0b9540010340120b014403400d20852b88641c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 391174694 1250 391173444 391173457
    0xa2001020f0a0f081e1801230f070804080f01060603060e2802090d030c1106190e04060312111006080714060702060c070602120f0405090a1415090c040308 68
    0x2c2084c0d40d0782d1411604032140040c0e40d03403860b41115011a696689080b490141600354100740d1791000800340055038180d60480c2180c10810024082088180c04100c0401800300d60b03004a0804c0c2c1010f07624004a400c2a446040c08401c0b40d65840b41480403582501c2003c000c2c0c0032002d41e2240f9882e001c604001d001818881030030b20007280d0052500c0543e60b58044642280001e090309040e8041480d000d855650031400840e503000ca43c440b0400d40e410098162115040300c001c0816404d51180010385032070a800005a8019031201404008240c5002c6c4800e0342c9c0036982c0da000c24603031520b4801424908070100810725a818600c1c10401e0f00b500040100564004d418245a494141000500c0d14031806400a40114010030502c0203c0da0210f040001c81e4095002d969400d001e02e40d00949034420f4100700401881c1c14402807203181441e550040d0300a0640c000091514a400000400e12100321030b000f100c80e400350302c10442c41c1000c41411381c100c000070308030504183c11075586044501400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 391175944 1250 391174694 391174703
    0xc080928081617010603231c0503040201081e0c07110a050a0506090d020a08012c03070b0402010e0d1b050117010302040b01090b030702030403110108270a2001020f0a0f 74
    0x10008801c40000c05c2d0b024800565000c0d1924410520301c031103003004501c010204162500a00c1c0c1c012441d0100c42d082c1111009255403040d29582d1343d0740c0151286403002d012031407408152070a00c42c1c0d0000340803180b401140c03003801c451f03220f411619105254070b100150090050384064010415500d442500005076030046914548800f0400c0c0412214500000040d602864103c2c0c002803039841036010b03500ca10700188002e01000c2c0b0003d82d0070701e160342c202000400e9610411602010880d80c1c400c95410620515240764420a040c00150280c842c1e46030544082d01c0091013040c41c26212000000145000e0805441510011003001d8040e001440042d0045880d108010080da00c580700d40405415540c1d0201c0d100c0c108660025520b80040c0401ca801444c421041403080d8011410130b4410325001c0004202054001e8403103113500b800d59822107580c0f1174101d004000030024004003c0488019807501210342090f0002444e20400212404858010034098400700c2c1c0100188212503410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 391177194 1250 391175944 391175969
    0x30c0206010302060c0309040f0c0206070c0f0b06040b06030411040c0c0201020715020c06190806041109010f201c08090d03051003060603051005060901150c0809280816 74
    0x840c0005401d500c542c070f4140340e01c28a01080707906a27508640c04007000050990031030ba01c1c1d5503900001d59003148851000fa010a4980c0b4201000955159219a0252000d4808a44488072034003141040e00259802c40300307140503003d002c00f5400d1622909121604500c1e102500c1344141d00080d44a840d14012500d405c004207400326030700ca00800c00e072059041c1c080d180c0d6a80b002124004140416014500340000b02045d001c0740b840e2401d405960b00e415814201145412001e400640e03c0f0031040640c04c06004900c50143d1201840b480c0740356542c0c818002508001c0302d400d9140103003280c0340d1185030500c2079140901005080c00240e0051151843c1000261611440c002d0408a085c6510040c00f00d418114080100240401c038040c3c40020900c0c1885261030f240c0170008001024052200b84005c030694a1401c4c4c6d102d0090b0011050042a1132840c01da9580c001c20021591001e0780801300e5230749c22141000021200e40342d001451100050880d5540c3c1c101c2c1c074191500c50f4412401220b02d07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 391178444 1250 391177194 391177207
    0x2003010b160f0b0c0a1e0509120c0a0b0405090a1107170706020a2705060d180f0f0b090321040615080f010e01020405060301091d2407030c020601030206 67
    0x10040e0b0480c52203504100c401c800c1d0b28103429100c10680c00390003c10006400385e01803814095034a46030070111212030b154142841c60344814450507a803034982d19140c6106000c0d8800441e1a58624540034000e034155444e40c0d281000144110700001900010f800e0b80352403081a0003440240c02d440b90258490000c1a2140e5130040700f80c007034018440c01400b6140f00041d641080c94001c4801c4440120320280c5400a0044204152240440d48501a00000c2c00c0060104440140d400007801600f54941d103c03c00b000c52b1141a00d0b801c6e80d403401c81d601d08001311581c0a000720340e007880b98001c40c440015443c110082c1e00001e0002000c042c0b01100b229140d01050030021160454811003c009800342c490b9a80c030f4682c0c0b0b075a12580c520301a1254039280d007186088106000300c0d8141d40e0040d00e841c0c503591a020700d440007041814402030170314116003100110914140080c4001c1d8800044440050701108c9460b40c44650191900e000e05141090112031250040741e4503044136012140c0130345440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 391179694 1250 391178444 391178453
    0x408030402031213090501060e0d08030703021e210c0a08070e100804110a0e0c0a1418090c1810031805030c010f020405090103060c0903060f2003010b16 67
    0x1102e508100f4000900820314440070000440c0360303003c681d1089810300c07260340c3c1d03664241d854240a41d80749070400c25803210913001c03400003170017141c101c0d40e1450700500d010401d001048495000c0225085082c2000600005010b00111480700c80240022030424504120407215414071981d44500c01b0f00000b840018034a60103480d41d1117031214003a111002c0019081e500a2a41000300c0d4115500604500030100e6030074802d418005030751144210307403400d032562080700c130b025000f07402c0000407c00905808002020001c01510f16202c242090820121042e170800450785401403408038010000c2c0719030070b41002d20507140e2040c00801c4e43c0e0b000c080c400c159400c801404508130b04400e0604001d00c01001c0000c004020701504182c0b00c000c0101c0701800c40400103a110b241301341035003c1c0c001342c0188085201544000400e4026080485002e035503955954142e621140501c1c1103030369030744060260042d825400d1640d02200011440c07440d030414031240d000d800b07004007403145003000880b140d0400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391180944 1250 391179694 391179703
    0x1a0c06100807060809120d05190507020705040e16030311120f070f1b060c020301051014062d030103060e01110a140c011a0a080105010f0302090c3f010509040803040203 74
    0x1b040b40240c40c0d4949003092010302521050b0b604468030a1610441005800c0340d210b254003c0c007003540685290340c5814104000307407007a441500501d0003a040c0c9102d9040d002441c000045119441e01d03110030b1101074409041441c907801e107440709007041001040e01b581000c2190881ca038400d4081d401d801290130b1a0780140901800344c05103401d0f01c1e9000c10403580003c040030702c0038402c800a000e00d80d256401ca0603d006c0c140300b0002d00541c1b2208015051801c44060501c18200800302c1d030a801e10814850b1203000e800790782c0741a82500000500600c040c41c041c0d2129400054002d22411040c601b0040541c4034400503101000b114103549030714841d0020482d82c221014500074002c210156000b80200c408802525100707040300750000034110f0b018014035049032010750010000520f190207104c1040402055102081030801c0b10428131600300b101c84655403000860032a05101c180c08001448c0f0412442030505060400104032075034505000541c4154084c04841d180d0300d50344003003880c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391182194 1250 391180944 391180963
    0x30606190e0a1e0923070c050115030201080708070210020a17010308090a1a030106050901050c1c0809070f14040b060d05040215070210181a0c06100807060809 70
    0x41c0040c880001d40c4040140c54503140c524081c3c103204a40d545440b0503044841311440001c1c600100120526099101503000354096801e00b098084510907036240740c212003001c00103d0803c40100d50130b00175940d1124a00358820140d080030b200e141000301010755a0984580140060307500019444030262003085490030782c0540005603c0596140d16003035985800c80c14241d1f0003000c4144001984643c07800701000d0710300c0c1c00740b0603d1940e42401c01c1112164041610241400010410081284030030003200340d004441d40d07030b03e24aaa19044006103488400b51020700964410f4406005007000703080c00d42c04803000c0105401c1c0360540100070502034020728050a034006800302e462030950380980c11052085100722945e13108074025030704141003405403000294100c80bc06065151150003480c801e0100380f54108802c2405a0320300203211030400d01d0407888440c09001c80d1003001706104001241e04500640440040c80d41001c94442c1e8407841441446d081000300004581e000b0401d00040f0038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391183444 1250 391182194 391182199
    0x50601112a0a0f14030312041104140705070302010506040c0e091008150106020709050411040504050c040e0102250f0b1b030408121302011b03020705040e01150b030606190e 76
    0x1550340c3c0c1d55140300c50003005100310f088000321404800c070340f46400300807100c50744101140314905880d10344a10785944580417403a60402d039503001400d41907071342c0381c081032080c2c080750f032000d559003820320f802801e4440140c0894055403c040c00030074516085200c1c000210000d40381030140f40d8030415080b800d90310301e82c007030341c010700448420501848424912905864880d02203581943d0b445901004035182201d0240a801a05901c1070082c0f421b9000503401c940070300122080b4a60007400103007100d2442c24400581d0394000740703281d42069106211388403207074910481001e500042d102c01d0310803000740500801041180000507002c510380d0821405111540c542d207500ca15003440c100740c250380180c075070014501c0034400140ea003415929203420b51560681d10300242d40791301070028000544c110022810348c0a101000309031502c0714401c00c680c1c0c000107000880c614010550107012801e8607004508100410000c00915803550301c201c800d00c175030790029a200181207680c00c98805114000c45503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391184694 1250 391183444 391183459
    0x1170a020a020c060d1d160b070807140d0e04051e060a03060c0f112b05091801090b0909120a030e0f011d010207022202070f05030706050601112a 64
    0x5252540e15030041ca1046d80342c00f031881c80c503020643e0050b80c1e290b00c100417500d6881c0c41c4109004000d940005050411300ca44170300e500b0300103103641d803002c5458141591b41d125070050081c0f040c20366120308048401c3c003041d6020401400c000305102c00c6051040311140e841d1804401151103a154020340390011504907204000c00400c0d900000c1451041010134400101912029400c0e5003000c55040d01010600c4800b0070340701c0000b00c4d00313142d000480b0309030411700c00140f1070000c3c5a110a0b001101c900c1d43e0f1100200c0d150b04080c017000441c0e42c94002c4c98051248401000800c44000600c04250140325040070b4548100c500202d02600e9024400c440502541c8401c00c1c41803015004420080d12810f02075000c1e0403000455802c034014010060340c010010b00562622801801445e0549610030002624224403920785070079254200e541241e51740c5c8001414820701c1000c3c4600c2da0003100919004400b01c0c1010f443caa62908070380751454003030702c8410012910b42c1e9810602d5096800241212 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391185944 1250 391184694 391184707
    0x2060703020a02010f03020a020c0904150e0604050106060201060f0612060320090106320c010905030703080a060e041e0506070c05010e0a030512191506030b01170a020a020c06 77
    0x2e440ea508860102e0201c0c02450b082c2c8002402402070b030b00100415402020103d002c07004010041c036000d0010303604000107c241d118001c0c01c0f400f0300e0041c10b02c0d0400818482c10189481421501650f20140469140644c2804040034815511046582c80d14141d11340d110014800c0700206040ea0000f04154008070300002010490400740d070b440380003140c06111580c0d84060689803e0003c3d104600e902201c182490422403054035513050080540314401e0420100d0480982110b011580a4441703a101180071020117a0028800341c1c0176846940038490140b600445503904040540014007041c4000311607a11034001c03040501c42c1c607030000c044804034200302001410400032001c043da1b01c0e50038500d001d5104100080c1c5902c02d01d606680300c600d01a03000c43c04044d074050140c4a400542e125400310311f02c00f8101e01460352240303610300003508100c0c5405400707000c844c14441d205050014411382500c24500c0b90400f5a4054652a03026036140035a41d800c908020490b1095540120003081c1d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391187050 1106 391185944 391185947
    0x110f040e06180a05010c02030c12040e01120203100c0504050415030f03050a092c010501030509070e060d060e0f01060b03040f030c020a050301020a02010507080705120606070f02060703 81
    0x2a2140380c140b542c0e80b91709444080301c070340d8010b07840416400e00b07004041c03101c0180011003661961801c1e1074600c8005403418144180724113a21040059803d64400b809900310246400c2000c01064480c010040e0180c0c01900445000c0d5161075040e00c00d521030f0300c900600350307030308020f5034800c03800540d408072031a51116504400304942010f0004100c83c104c10200881e20410700c0c0c0c07601c0c5803082d00800310740c080c0c160b0041d410141010180503117942c000c01c10109841030003005281070340d50702d00420780d80400300000402e201d01d0980045410400402c00c14801c008820090001c20380e144041e50160006a80107400440c41c983c40e817000a00031210510098801760850440e07542d1040041c0c00c90b00000030b141d0150f5111420000f01c103030b0000c00141d001c403560820a04004403001d6040c40d980c1c005000da80190310028801044c440510480400564014134007a07850505190 = true := by decide +kernel

theorem cover : BRFrame.Cov 391007194 391187050 := by
  have h0 := BRFrame.cov_init 391007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391007194 ≤ n) (h2 : n < 391187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
