-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:24:15.228723+00:00
-- url     : https://prove2.me/submissions/a9e7dae2-452b-42a1-892c-d0d6bb72aded

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726798561 ≤ n < 726978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726799811 1250 726798561 726798577
    0xa031704052401140607050a020d1a100515130611030f0409020d050f010b07020d1a0403120b0d0507030b040c05090f04020906150d0c02070f08060f060a03030f05 71
    0x5544040040b00404800d07403511240b12003036225000c0c010004440c100f12103400c410010342d48a1320b0001c3e69150035a0f01c1c4e89454000703000300b41c4480404207000e010b0101d0320b62000c1425410380142000d44040740f0180340382c000c0510424120701444220001c45e0100c4010481c0300d0000814280b514200b030b0f4480d046030720040e415000030000144841403c00042028090410005807a000071914010440780020140420b90040c40d005108031038100c07040e100c2d100d604489442356100e0038600484200d2a14228a414180c3c03101407004064001c00140d0007400c130248200a0f2000c6041000071102c00c881d40a42580c000000a0010500720b000141d0311600885c1030440050f40c034404904001c208582e951400400b81c0706110461410940080e04000112401000e851684405014603c14810b505c060681d440402030382c02402480180d0003028003483c030288490340e4843e50b030384444007243c01521015071400000c2452529500c1c1c40203490301940c600c64a100352410139101c0303600ca080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726801061 1250 726799811 726799813
    0x4030209040f03120e01091104050403081f090203090a03080a0c0e01200313030b130804050d0f0501050901020918011215060803040f0819051b0402090904230a03170405 74
    0x80c042410b000540501680e014543c40002040c107e50700300701c00c1002d2403100a612813070804003804040b0750310039590b94005404005519503801080d04401090096520403541c2e18000300421107800c0c000718403110380d14001d46940308a641c0350714009080703903c0b0010f40d502103034200030403020710b512486402e580f00300d440c41d04240401c89100a185544c014003401140509003c0c030034010030420440c07907600100c82280c0c07a039801401e03035600010760145010340c2e401080a0030070a001d220900810506164008008111604100c00414040d42c417039920030380030f01d050915211103a0700c4c8008113812180d80b825405020350f03a55480000081c6140f090300009a254103010071001d0052009000400101100c0d0207541d01e025603003030070900706085480020742449598004a200404c0340049a9903060148030303410103074030018000303000f072442c219044000c0c003040200300105582c140a0002000d101d1705810810101525070350803070b0010040001d05d03500700201980e0001c00070103420601c17941c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726802311 1250 726801061 726801077
    0x30b10050f1c09050a02030714100f020a0f08040f0e16031508031c0609022109071a03070206010e0702071a0903030d0b270121050303040503030a050c04030209040f03 73
    0x400142c095031070b0503030300b80c5540d048021881c04500d001c200320401841c184851207800030840e40050001042e000c0708409020b035098203180450300c2070000741e425a9204c00c10514414180c103000300143c00c14080c0000c0248581d002090700450451020310503003650081681043c00c0c1841203002d03001100208082680448010400040501c01341611520030721002e480a80002c0c502c80a462480c0e0045041034070412000340c6080c0034418010030050049844170540e121107032218905110365002c160490301022070101c1c1c0201100082d8024800c0e50f08550069807a000540300c4d958040d561400584e01004040261014150150400c0000483c4e2142000f261801081c1160b2040c41103e8225584a4400c48686808040c15101d24641022030742030311850b1035a51985241030042d90104041c1c00494241d150041800c41c2e107180d44101520307200d084c145001c90b80c9401c142c03900c0744036605050028131105c2e40041a03d0441360000c09041483d01c440e02d41d00d0f2410811001a800c01141c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726803561 1250 726802311 726802357
    0xc0503070f0611031305060f0c0901181e03050f061317090909060717070f050c01110c03031e100608070c06060f1412030a21061203030b10050f 63
    0xf030300610310852241c2c80c43d94000c1582d1400ba400d040c002400c241d094841181404103580c075900607141241720030700b0300300c240008884050040d80110380c800751a141c1c5544050001c010103052100440e4400d0b030840d01d403001c004a44940f501d00440d0140c00c04205030307148c031010481070f15004d0083c02c1408215403410070300801190030720404032102d10a60340000300f808003261b442003c10303145600840d40021507050004008000001e2110b494042050204100540540c00c0d81320080b0b441500e039125a40e1381310301464640740c3c0c004545140880d140c0c520b0040452019101044c810311249540c0b02c0700c142001003d4405110242026003001000c0403c400001c100744142c1c8041d2038042c0204103030340d1404030368200640040b01110302880380303c900300788a00c100209880d0407112a080034401d059810081c8920201210044414941040780000b1020501030020001703900035502031000c0013100051001c201d22900b14000051800c01c279403100094044c001e08068848812091031000c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726804811 1250 726803561 726803591
    0x306020403030e1206071d01091212181a070813170c040b0d03030c051c050105010f03020c0c010302031504020c1b0907090e06150c0c010e010c0503070f06 68
    0x10340c00c128007094100702003c295241c14441c03000c0d40842c0d8001800300e8a029407009000505155048000d0111640c02910a0b8015440e8102400b5010812401d0819904000900b805c0306030702400803c80109640005610544546040c2c45440780c020000303c008400005172540f1428042e104c1001c103101d03030603544180d140d10500504074451444507041e010b6004c0c606050b000810144110716164030107150741c075000d03042c01c0803940500f40018407554050046e1403d109a034060400b6154095603211550781e5a4415816100281d0316a41c1d01d80007130740254201c0c8900d10000519500c800c40e18042036101e6001035038018400c56400301d006a640010405981000c100041d4640051720650220f00c000591070404800444a8031074a04005034094214a041c1c0107111002e0003020020b5015101d5018910b80c4080c2030211580c0c0305030450701325840300c518908880c0058402c544940440d0700c00d402485002780c000c4065440c03c1c2469842d131489440703508007160981d880d08242d040741c0030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726806061 1250 726804811 726804817
    0xa03030e151f050d0c0f091a060d020c0303040309060941040c080f1510050906070209041101141e0c07050301050408030a0e010203070c020402090118080a0213111909030602 76
    0xc41501c091141358141b41c1c0d084000300aa40100c0c072118584500d0100000c0c0032810140b80301030541d01c0c1641c48140d0a00c42c0c02030710668414000500c8004284003c0590215800b0308440c0d1940c1c2c0e94803d0754a45130900c404a50003540e0b00e00c500c940500c80d80305140000d503810340c01807000105404401e0b450020400b44c80c80303a0316440c04030b02c0310f100b0003441440c040a42584000e500e450180c2c50150711000446500e1800501d204101010450300110740341c2d14100c0f09202c0d0001d00640c03d030702c1d051510b0081c01c07150900c0503000401e0b101c21450360215000690300036604a915010101c0d4110703031020020b400c2400b440c4c1142c0f241076800103260701d080c850b55000354011440d60780c0e00d142100400064800c0115849400d81c03040040108a980c442808441c00d981118090794032030f0b43d040100c030301c1000c198840c01e9a070004000024a51b2000403c07400e054401e03100c3d50b0f42190340c0d040840440d07078220400807100e03100300f2001220040a0050841c4200241000808d041c1c0f40e07141c54040b60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726807311 1250 726806061 726806063
    0x7030b031612050613020d0b04170f0316021b010c030909050a0b0a060519031e05101a03040209010302010809071e0611190201030225050a03030e151f050d 68
    0x1000c44000006005080c003102e64880c10450741c1c072114400f41d9020a10300c001800000d08004080c1e0045030803c00940b2200300201d400740f60252f1641d07082c9000f0b0b48160f005031a0f800140c41c0820f000100c01e03001041903091101411000fa00001c0ca650042d1081c4102e504100e041040c00d00b80825808018810103005580e60b8000044c540da4842c1071148140c242e030132450500c0410300031800071a05561000080d00300340c0c540401c440160a8000c0d15106404a0802ca80e0f42403c04102e44541101c01c43d00c11035840104d01885000307540c120001502c029140a90004100c00052000d54090b1102e550417600f06402c407402256110b8080099030800c4c4080b0000340e03c003030005c1040130703070010007030b0080c001c0074000d400c042c0d5651141c01441c110306030000781030540100b6000500c40080c16090302c016405c90300d107003102c000b0b460401d85920b002841240424500b4000e0380d2022000540000d00351601d402c1a0919141e000d1000320088116002028221034102c0200d040d0710380600704d080c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726808561 1250 726807311 726807329
    0x2180703060306020c0f010b0d05030f0f0d1a01021908091002030c06040c471318111603120b150d06080c0d0f061b0c1101021507030b0316 61
    0x400c07811040070b0b0a44840e400b411744274544510384900841d03804001c48803e41e60310000b8550350031030360308406603038058079171148040c5262548804000b1081040342c0403d5409a0136500581c1000c80b2182c6a9140414080c5c00004c0c00c2c0b10300d514a0800c08000f4102e62041d004880c24428a03507000c03882c0c82130858044641803e200710130042c540034989d4143c10744803444414241e17050b2520300500d40301040c842100f2158124103107182981010350860708081c4100080700219521995200203a013615000022175614003c0320300044402da000341c501d10a07041c507289101c4d00c83c82d141250401101402d44800c00d44d50711400c3c031190703034510041588040c0101000d0b1111944502c5100702d50160707001f00b010340c0000582c00341c25607813003d04c8000036512410401d40d10080b824440010200f03450711041c820701d01400882000e030440c0740c0e035400c18400c1c04001a00b0140400481e20360704030707641d41408842c50001044c80b50f0300070741002ca00100090f0854080081e0720022440b804901d902c18982e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726809811 1250 726808561 726808573
    0x1e22030303050903030c12270c010806030703050d12060905040303060303020c0f030607140f030702160f08060c0706020d092d02060405061b2b0c02180703060306020c 73
    0x3010741600840703502030400c002550541c80c2c0f40705c0b0141107100300c40d03001040095040000e07401c1c005080c408044031220008424408401c040d29980c1c5014882c0c0c150701140d90080090950b1030000f03140f03400e40c0c0d8804003034080394800100690703250041e01d0304001d15a031100b4010840310f410b0703c03071548200d0180d5404542c2c40c0c0b5604010342844910a10603009020741c4400c00425107000440701e8018a080c5450348540d41c0c06c1640042c07502030310307424205420002080c03202031540055150445580031312400b00459403500d0710104c84001d8859005180c015000140c3d2a000c1c0760042c1143e903001c1c10000d85000d0341d0042440c00c076112410201c80d00ea41036415100b03030002e0819003510208207880b440301c0e5058190002401400f6078460f15120780d4000400c1d80e050300302c00c10180410031080048810000500c281d8a440c420030f1090134086d10b683d0110016010700c1801c41000041d0050f01c4d502695951030120042c01d140100140e041c13540f5840000001040d510040203001d40c0e807005440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726811061 1250 726809811 726809813
    0x3090a0609050318040e06011401030908040905040507060f0e0405060109050402030406060317090a120507080601171b01080a0b041e02220510180b0c2409031e2203 72
    0x61135003015895030b80a1868045494041c240015865041d29058608503a08848250040b070150400b248010110302d000704001403030607500d4100c64000d5210380c0c25a602192904021112024441d05000000b00d003150440840d041a40c012904200185000c00f0401d40710740100301030f60700a9404980380e96072000c0400030f0012810805a484404801007441c0011b031030001440c131092400b8951500301000d4043c01002410407210f030040c55000240d480541c0d640c10351202601d03010200f82ca181c043c007601d1a001000180c41210005c1050315038038910307103403817810800400b101001c86402566440220300d00a1003051140030030100d021025988214003103c00c004d06814000941c03240b08090410300082d17503090035a1444011500d80f07500340b1006c2c210760365084112076101c41c41d6400000388800b1510b20109098520b8203003808124400c048619000d65403140072a00d5a07800d40041c4610808200c034000035500400350f0038161030409241a400068441c2000c9110042c2d00540e00108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726812311 1250 726811061 726811087
    0x71d150c0c0406050d061a040c081e010f0626090309150703050a08040602070807060b010e0901030816050c0a0b0a0f090b03040609060207060c11070f12060203090a06090503 76
    0x760030680c140c40503c02640f61602240070383c41c111500800c0c460b21000b00c000c941a000c0c204110300c1d80001c2050003c1d80c8a00c1300a084207805407a0700f1b604042c0d03c1000e03004100c1a4404504031404000044081403400390221000c40303603920f0114102a00751410a8400420800340c0d00071400d200280d90f0301c500240801003d0050948440540301d000d2102d40d0200303400c0b41c2940e40741c000e80d09090300c003581c0e1450030300028401e000d0018124a004a80d20342800302c81da0041c1c0e110a0b081c0c0700c800c8070b08075a8003041900402448014203685041041a0301048110f10007400103202c0c100302e4120000500001e10f050211b5000440c80c000301050b030354441c80d80038840151080050800c1e000302400d10580480d20b11004001500b201c2d1109040d5013084502e60492710410f400210422440c090b0180c024118802800544414468050701251b00c03406c4da22104126030517182141c401142ca0780d111000794200501b05103150140e96034000115005000d5040141d00c100042c40d9038400d80c140c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726813561 1250 726812311 726812323
    0x10c020d02061603051911091c0507030611041a0304020a0b0a14091513150e011b0201031b0c060f02090d0605100906030c0e010914071d150c 62
    0x1030030440d0701030000d112442c080540441002001c0b4900401e00780d0780c0c43c6018010b0b40510300241d815528000c000070509102501802d9046001c07206040e40413640d06803440c4c000c3c0071003c050415044960208005600c5502c400241d09002c201c403402c0658400c3c840652140c1d40405050b140d03000000c0208602c0d155900f04081c10f0305c100c449040c01141d407001880303410b004807442e00014001510030384990710350303400800121103002030707680e21441c401d80301043c18600d00c900300002c10000c07034054050b0301680c11280b041c0e1040e51a29220003034a0340c070040000c28000281c1c1419601c14803843c45d0100b14410001c0480a41c60341824252b5a05d400400ca0b818041e0041c00c462040c0407284041e65100158540903411190100d89612901c84441780c078100703503000312032a40c54101e0010030031166031364520448000304480c140c940c0c1c2e5800c4441c160341c40002807800250650700081d039001d011b101590460000301c5004402c1d40984404a20305159001c11480014004590380c1100d500401230 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726814811 1250 726813561 726813583
    0x30c031e040f0e091608010b01020f06070c03030b1504150905030d0503010e0a0b04060909020123073c0b130201020607030b03011b0c05070b0f0d02030702010e010c02010c02 76
    0x28a107040d02d40340d030080c050b880e14000c1441003804200421611682040350014000640700907140749036841086500030903031032021601600030b0064202c107100c0042032552003882181c652100508a07030b50100e00030100341a41f5980903275240040c440d10303100d10015001909070701c0034a1135800203501c8040c104a0680c0d00c0a4842e0380300040c2560f401e03a0000580e411594000300110342500c03400280400f40c04a42c0c03420b5001894010002003142c01c6401c00b4210718002c1e03c03100f012981c2d006100c2c5100c040f010800030121400c0100c8030000d2142d54440806111103800000c0d01040390804001d510356038940d144c960a081a0800c00b8088e2614015401440d0002d450b01d20703c203140c1c0081d4407403100402180c149540d884021049840030b40101111883c010305600090fa00554064440c1c03104860544007841059000b0601d611014100c40d000726207055001d0600720b040481c10301940c0002c0c1100119521007490b260280000d00414105202c56000403034503164000300285070004e0002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726816061 1250 726814811 726814867
    0x2006010f17070f030f020315070224060a05212b11150a1104080318060f0702060703050706021801030b010c110d0812180d05040b121008030c03 63
    0x1504001400140c01d020f401c41c0ea000d01c00c43c241c00141d0000906010702091080f01c80b02c2c080c401c01c4413196002c191003030008119202c03074001a0303d10450a5031050b04403400350300801d00c2030003030040f41b034194403507201c0c0114042010200d2485a0400342000c489103403d483d0034059001100c50b0310314001455030b0321001442d0040710351106800156076000c41403c954181040341003c214505450742010690890a060b400da4903613071000c00503a20750040100b007001220f03914105400d4504003049480c1c003200300d400705041c031042e502044550342c001041101801410041440011000d0028000c990965659800342440c03840c00501650003000c0010704100041c8500c41c009104400c446514210a65001c1080e40f654540700c4041c0c070960b2000d80400c120310041042e01851070341b500203443c0010b000e403490390800314416503240c0154014148045014011100801c40b212a510b03030122500d4850034141b070761421040d086620003800c10240b41c00001d000503400e41d00015003554002d60030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726817311 1250 726816061 726816073
    0x102120316140405040903020f1c050703050f0405090a020918060109120f080304140d050a080c09010306030c0f0f0f0e01060f0c02101d0a152006010f17 67
    0xc003200340c00000114501082c00001003900e490000142c00766800b50070b015200b001100220300300a540c41600d19003041031817060f5690b181008080c040071000c85e1100d500e8003400c0a405540030340b500d820000920b00c20035400d1100240590318020709502801001c10016520340845091102c000103005848408020a50500c88143d17070000c001c80869001440003202e50000346460441807d000c03001074007224020041c00244060000f9403105441ca10088803000030b41e0303a005032282c2c0105244200811030b86000620010540d130000e2160300d505140c0001c22544030fa60702040600381d07822449003021800c43c14019150710141176406807c6d0780c45c1c0660440e103484807907604900c05021b5181040400140c140c1079038000c00315030144aa00800311041f0040704c03100140b515078194020554078007a0340c580b42d500d0a2102015055507100304180c3c020b00f0310100b05a03241c15209401c0c4658082c0da039140310b5800e0091241c140030300100550302001500d881180c031a144481000d60320181c0001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726818561 1250 726817311 726817321
    0xf091e0705010c0c0305062e080d0509011106190e01020f04030809010207240f18031b080303160801050a0b0730030501050328081b030409020901021203 67
    0xca20342220824a440e600c1510245007021044546610007051485084140508000c145a87c244003142c3c00700701c2c9009000402e18200d1203807640c0300302001900810004200d952140008283d841c2d0306041040b0307441441014249409821545d03a000c00d0008440d03880c140c4001d0240e2840c2509100013541484000c2121080a03c218030004100e01c100140b0856aa4000c2c0964002400c0c100100713154500e00140c40e0294506c4c105504c00000c0c000120700c0502409440d648040c0b1414091050a00c0e0440c0d0b00e1010a180c421004000c2e00b2000c1ca002442d00c2081004500c240024840c3c0505802007140280c180031040e00054070450f00ba00090202d6509582038030303040c1da02b19007000d0610743d03464070484003a1848040c0b41140721540380142001034054100c00c1c12120f0a80c12120302000c4104c103114055480d400148110300041542c2c40030500386400351400c441e14440030008626007940440c5554860740c07001d40000e801040c1c28207550307014020151900001c0d07c0051840c900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726819811 1250 726818561 726818563
    0x210050604140a0e0f0304031110030203040f0f030e060c0a0c081504061a0a0e1611030d05041505070801150801060807050304050c041e050901151a120f091e 69
    0x80100081080740d620703440c0213140041000140c83e07000007141665510b54503402c00000c06041002c4583c000c0b0421710f1861202840791088130310480e0800040100d802042c0d0700d0006245050409408000e00c1108001c135940c0c414008200042c8980700038415110300b0300d024140c0c0241517100c0423440d0401090581d903002041c0c031655219074007100c0007980f05140c2200b0b8041c5a5407084103500310440d10000b098035800c0b205070320b000c0e00d4841005405900203001c00c403104030f0102d0054072590401e1000f4001e1a6807a04140d4015100d141c070b201c1d080c0c9171b0009103012108112081000900c145c001000b040c011152041005050351030f1a2442e0b41c1031410107800440003800600400c4030002c0080c05100041c03004a200042c014018402d10b5180281021811440008002d40e036183c2b00100d1045141481028071844103d0440c82c0040d1600e0707240a8410000000b07220000000c011010396a80d18079920740c85807040174020011810078070f03140c500e820b542d001d080700400c0d200c44114141001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 726821061 1250 726819811 726819851
    0x81603060b013633020f0307030306090b0d0201050901031503020d050601031203020c0303060906011b0809040f02130905060613090914190209090703050139080718080d0210050604 79
    0x100304d200c600841c0300340c41000c80c074104c040701c60010107000c081810802c25505401000444400d0310051001c171149108008044e1b2019034000e002c07510400401da8154000d8000007001c0f0400c0241030a0542d880e0040b491407480041d080342c0d40d4100b000141b0401c1400e5504050250710780c5811402e228903481d0f0a95640300c00f500040c46050b504001610342d81c4207030000c45401004009c007117007640442c9800c501641002103404c0c4100e003418003211800c41d0910036103090440c0030113130001d054036100c0b1080003440302808280e0002c40400c00d10051065982e580c600030800510006070458460604006a0032180c2d24050f15403c01c615040800324404c0401903059011121300c2e031561103c5211a00c2d225059100404d50b50901496140881d1900f130f200035550842161903c40c1002e4194084010792110200030102c0c0b8500d02107064144554161754042904120900c45240c603208041d1411030203030480401a4030001800001c0350090143d40d80140060300e090000b10541c0c0d020580e030203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 726822311 1250 726821061 726821129
    0x803042120060706020c070609051c140c1203040612140a050c0c1b03060f09280f050c21280c060c030801081603060b0136 54
    0x12541c1e0307011000c903680d00045903996a40034408568039124000401c0d01d0701e03c2c61248902060342d26400142c10f0920080380841012491041c4180b18170541c0c0f48070407149090150a014820340c5600b00b41d81d00e5801c0040e00c95075101c3c0c011610b541c039100000f02903181c40301e09820400c0c1417100d0444220a0000700c00d8111000c07030000308180c0d4582d85250041c0c003460802124030b00c611180d5009c0084120080070301c101059003500d6080d91600d107104008001907500d0005e60b40b00e0a000412040041d1309203109818180c0884030540c2c0d65225240342014069043c0d030641c0007485030f038046242007407aa250320f1000400c45100018850b19054803030300000d2042a051480c13000014040a20015042010347d0015600b00042d8072403c006100d82c02012003207010425200001c17800d0301c400202548441d4460545a41302825680da0f18080c1403038441c218140b042d0002074500b8107843c60390421092121408000011809003068a0420480e5101d5144111804011075002c1c020b486060440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 726823561 1250 726822311 726822353
    0x1c140a0c290a0e0613050414090a0b0714040905180a0b070e0d060c02060906070327020123030907060801031106130918060c02190b10080708030421 65
    0xc2d03060700905690340400a501c41d540810001492141417001405d290305586046d1010003849031004140d1030f00190030b0b680501c03280d020000e40d600090f40c11014643c014218609249032049a8000e01040d4029402652042c0d0703c2d8410800e001480c44003440301da143c00b90040c10741420315110b03d20041c002811040c2005101c025440392a22070b0045003001540c000010810b850300c10788025180c850540700c52031507000e21404200110310078007131700d4034582801301c02d07448004a20f54100c01460601e0001c078188802030417011f0354603203a040c2000c00308620418060352803611558050902c02d071900190207200704a40103002203075060903d08118901030360030696a079101c1c00d080002c02201c3d8041b90740c040c1840c0d0b031200344820408927a02d600c0d101d00c030b0502455220039130aa0b11101e1904146000c10022001c02c0e0226064426460b0488114004a1051a01d482d442420030300f46800c100d1003a40001410000c0d400b01e0902c1c050715100314921003e02941c0360340d605044030401c6400c1c1441c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 726824811 1250 726823561 726823567
    0x1b0609140c0a14012105091218041e02031f080706080c0901020c0a140a050d0b062e0206160207050607150204091e0b0616021c140a0c29 60
    0x110b9005020100310350444101d50170816002800e80d2025042c2202d0f010300600584800020b5228954159005089500a02140906441e060000807c01c0c490160040914000380138180d840920040d0302900781d5040328800b0f204c241c0c030446a840c10769840815640c0c00a001040420b82c4006029000b42c0e0300036030181c1c2d407000d0800403403030b04011203101944149050310001b01010100b40340840d00b8025035148070350700e64032800c10080c0340e0080800b4020402036400134000d441c0001024a6031413440b0805c2d05040c0034440720401001c000310350750015a2000062290b103e4000f00401055002c900c014104242050003181c030340c0c0254040100105000306041d051994640c06440203041075580070420030402010135481c0b203087d00d03500314400385091040021410144110390072112040e00800031382d10990b0905c0070350140b1542071083c41206546000005030b240d06103141c0680080b005001144d0503040404003030890780d100d8100c04501c000ca072655030b40f100c441c160325441c41c522403d0b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 726826061 1250 726824811 726824849
    0x4051c0f03091a16090f0332012d181209081516080405121b51041a10080114100302060a1b0609140c0a 46
    0x702001c10f00400d12400c144141000555113200c0c2c0d00044034580c6994098034030340e845400810302441804081c00c03050291020301e81c46010b018200c40f51642c4560a07114075400901000e08550100d17144850790040c900007a100b1100319086a0415083c91034100221383e03400f00006070800741c01700b0040c25081d6646140103014002d031031000c010054002a40e09840c002c1d0385010000d80125401c400300f0002d004000d04881c85818100d1040c3e9001009000d60304caa111640c5e1280c0280351000751510001d0800c4610180a00c4114408031a02c000b13000c21070203811321030400c1201c1d81c20402032902c06141c8a03815880c05401c18084034042035010141e03441d5070500130b42003054204807410045011060040c100c41414101c8111140c4070000c109811081d0b481e954004000e80789460380e402503100600141c41c1080041414054a081a2038055440040c8003640032040e00c007510141da0b01d0b8040d200740156500f807401304005030005001040d10311000100640344900400149290800e4001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 726827311 1250 726826061 726826073
    0x2250b06010f1d040b010c06060f030c0608040b0c1602040e030304060501120b01180b12070905150f0f01020705030a03170c0304050613060b0631030201050d0e01090204090b04051c0f0309 82
    0xa87c845801810902403552140c5c1c83c04482c2c3c100303200403604a00d0380207000039010301c20724910380510351003000808291200144d0850036001005100d030410020215100140d8aa1090017400098280a951039181c141458011218141d02134402c6201b00420307480081c2801203501e041d6498800b0511058030582e0b000001400011201500305180f01e940000500d0002170000c11a0011142405141d5039904030780c084030030007440107030001d2040c0c0c0341c86254504104455030303088040c41124841503032a0000307450b0404440341500454181e201c2603155180071440194801c2d070f0455002c3c65410582c0d5002c1c4d44060003000b51034101150008541084520707045605501030040a4a484000f01041800b0800324107088084034481c0074610003000020000b0741007203d13016150b55050a80710488480a09a01c50003841c0a541e150035510043e40e40b0320605100ca4050b405628035131510340751040c07030f04a100041410041100740032000813030744505900a01c0d842850040381200d100d103486 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 726828561 1250 726827311 726827327
    0x120d170c040308030a0902120c01020c130e120d0e0d0806090a0905060108011d0c0604052e0c060f060b190507060c0c0314070c030602250b06010f1d040b01 68
    0x1d110f64000400d0005030200e541195036030600885090300c6a11040e1b01c01e50703442d02003104207070140c0c00c2803015401c0c91400b10300c0503015038410341020410b1242210301505002d0358070011081d808000c07403603801e00c0263b40704044581c03030800000c01c1c0c45498100e0280851f100203246034803031128000080c107010b0017a004425042c4d407000c00c5800c2542c4070740d1000d004c0c1c01c0103401d0407240010254098061880061613501100300548814a041d007410144141001c4100081d1005481e05040414044c11a0706817410400741d41d880f5482858103240000556144403d000e0650b4100031052211040709822511b00b54521010b240200724419426106406000c42c050902413070f1007940541c46820000086070640709654032503040c18120300c1c01d070361030042ea0009050180720030b005100284280e0f00070300e051805444411b410620220321442a46040c1400b1121101e02c8014844c41d540c00c003180304e24007501e505040500100e40317032603600c0c01c589080206200f56100c0000040d1750740035400f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 726829811 1250 726828561 726828563
    0xa15140105062805032406091903050a150f050601120f0902090a021902030f07110f060307090f0b1804230c120c09180c0408030a080105120d170c0403 66
    0x5100f503c1000100141c1103400417210244d000c00c207007840d51701d0b02c114518441140031009016906091111050100081c8030742c40c120701c004821340780400802c3c000c210b90b1502c0c1c0c0c0b244006250040c2107a4000c400d650310211003241040c00c1005210850382c120014a030a264002d40000380b8107039510066000d05140300d0041d4000070b20307100380400c070705842d0001c0005001803403c940720180c42d01c400301c0c0d41e48628240030782485000d0080e800000c101c0c0b40c2c04c20a10301d00400400c1c100f030880000540940c07082d640000821105001007040c4002042808000d0011400060800d191001e0041002a6040546100320b50750300c5015001c2c1e00c43c0c8049082e00003415a248650701c4c0c081464840355003d0602c00341d420010a000410400e81c07507007100c00c40c080180c402d880c50303584141d40e40c120b048060070000181e2418403012a6802c8100094100c0b0409950b801245500d4003003030202042814651003003d030032182400c0c0700b060300320b40310185200c110b1b0510011503890074554230480c02a500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 726831061 1250 726829811 726829867
    0xb01031b0806191403010b01050403051e0106181e1503081c0207200411041203030902030303070f110d0c0b0a0603050318030c01030501050906040c110607020a1514010506 75
    0x400440c00c0e5001c1c0303d03070301d0001c0e10540003009051000300049d02d050040744001070031075001d00e0595000507001220380320306c81c00c02000840c4240e200d00b90a4000300f05100b409030443d0741d9800c41c1c1c00f0340011411490904090160803c0580d9080c00c10245445c103a0101412000001035409103c220301c1c800701003245843c04086413640d925140070000b00b40300c40c403074210a501030100d102003481c00340f1900c85a000201802c0d45801d01e00641d0400b10310480341d042d810f040c2d458904401581f014001980304003819922064054400c0708003410b007000d98125049a50700400401e1039107078004034000e0f8003640240b800500c0d03586003603100002c4d20007070300b0007441d9000114480032805040d480f51a2003410444c1a10414240c250044007120400d00c00c032039000201c10f02154140c102540061800b0381586001d10041201601192070b108050b03072001c00590080c00c40340c00740220f48450074049168000c0a01444421510540ea404130600400e40301e030300b001070b0101e040d50b4142d0548480c401101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 726832311 1250 726831061 726831109
    0x1d030a0b0f0403020d021501030f030e0a06081e06030316171908010b070f02120a200a0503030a2c1002010b09070318061104081b040b01031b0806 64
    0x10300c10060500c080d00c04602500c03c20444451070360020451f004a22502006490940c0c65903c584c80303003003800481a800e000c110b801c6907071a0b4a13070036030b1680503200c662106c4078035040c0291034880001c12a0f0302c03140062040070900c01165004012901007160780d554113640100181020400c0c206250740c054089000000c4d042807041c9400c2444500c0795240c0c03030311207050782d13102c81d0300002e80303e42403000303102c1c90104010704018601420038040c42c4500c0b00c03c540410402c4d81e40c04111490909034200d1120049082e0303901c0789000c0b01d0038405070506901170b6041c506a600003404851b01103901c1c0940c0301c0c0b00d070724200c031800c10a030700d001c1440001001c0c2c88a0146401c0e01900030b000f0000c0321802501c4540004646a0281c020a4012075942103940180410340e110b604c0100480310304504098001c11002552400030018800700e0300c8800c050008683e9848104012176440c004c03080e041c5800c1246001c10240d68102e2411310b0710381400c0c03020040d81c40400280d402042d40000c10303c600540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 726833561 1250 726832311 726832321
    0xd0e0604090207141b040605220509070504060612060f12060b010e131d0303060102030418020904060f061713150e030c01060602120712120603080d090b060a05011d030a0b 75
    0x1c80c1760401c40500b0b60303080150544400500c4070303411000c0204d604440580c071810801102c29030005910020315415100a19125400141603c025510110000c0c10a21860350128640d202d807000424884a00f10308180c580000d02e200d010051f28040e0039923039904d00c1e10f80e1907401144040b5100074002e02d007098440c48074000600416944501e9941440c050324228401000001141c2c00780405800550038640741102481e142c1c031030304c1604c014131074003400406003980765400343d00007a10900f18494261401e201009105640101480b88010b46d400284400500b0064103201800e800c542d210000220000122010700038445659595200008005807450070650080056075034541c00e03070341c005142014030402c03030003a01d40280c261680c014030030841c540a6a0285240c03c90881c0104410b03036030703446894039a04440380d0000309130780b01e04405041161035110141c0c0301c50111140f50003a070400c0c0000345000385004142510030300006403039141d668200301501c0f0259002d1084e000e98604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 726834811 1250 726833561 726833593
    0x3307050f060c180a080c040e0715090e10050609040b280602071e0e041a0a0f060501030c09052b0c090c0c050c010806040906050f06030d0e060409020714 67
    0x450783e4040405400300b61001228508865440100c1d404c0038010300828a0000401008124088200f80648503442c0700080e1502e6919014150800741c4d01d95120961070815075081d05100289644501107c84005000b195a0902610744d03020080c2c1c2d001a40194180205c0c004540000c4c0390703090180750080c103c039000c414115440c00e4038075139030070784180d42da444182c0846014035032200b0f1056124000280407003c1136252080e032243c0034481013140104c1140b04450030800950303886801c0341d110120060380d00300a00440004100a180c1081380400100c0002c1424040e070045611925001c0700750440100020f840c0043c12414042000840c40301749000d203c900c0e000d2203103149040c01d0201222103280500c01c41c000f0282c015015150300d000317140045a00d140c00a2039554080c1da10344000005c6241c1c0c1c031816100e155101c004c1c902ca030520100f050324105008014404220038500d125000e912110160780440303419000143e2200401d24202402d8508441ea005144c8070310000c5800c5459 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 726836061 1250 726834811 726834817
    0x712170415180615060215010b070c05120a02010801050f0d14031c02030609010902071203020c1204090917181c24050108010501060516210903023307050f060c 70
    0x10008240c05444d55206426619141d0308502107146408030001004440d140714001c081d4203103d5a1400e2401340c440340020710060764400840c001c0e80c0014410340031540c100c90060b0150000720b508640c01c84038800020290146030400400c0000c0000400400314010400d40d40f141c2c0c42800300340b812903460b00e80710009410884006105001902c0002801c0c11580b086070400f5030072608500c6440e02010096001e5441003101e81d044d44580030f45c0c1400f107030403e0b000d400540301210b008600b2203424100111580d11042107104401020400070354116640000300750480002da60500da240840110f0391084102510301403d405019401906000609803500c0c0140c2000c007000c21440e600c5164503400c0700c40901412020440400050700381c02c2c0b8609852541e6480b500d0000c013480700c8110102c4007514205c1861001c5003166501b0b1045103004991001407903650320501042c0341d02d1200d0280204404c2e461944071050008801003407007014090814a1600d1030225a00d505226407900c03603541c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 726837311 1250 726836061 726836081
    0x120c090f130903140403020612040f08270909031603090510091503140c0d020d0f021b21070c030c08030d0605040c02060712021209010207121704151806 67
    0x1c84c641c80308110003194800f034a0960b9005484039040c03125503400a00c0c4000e001c1c00655000607a45084070000d0004402800c92003120800c035000341c1e0b0442c41400f0608020b482d0345100e0090101005540e6030b00105036494102e8040c01a022222141810386040280da0401600400703440400e80d0b0302c903007004c100c004803410742a00c0c80005500c1181181161750400c0d11b00c1c1e004200300701042406070040040c2003080001d0000500d0000b8061102e0700b1600f0040c001d034000b0760045001400c90301c0d2095617104107101400940910780c1180107981080c900440038411b05003021842c8018011640c000f0f1f80556441000c000722282c42d0180035590350040c600400340c2e10704103500800d250826002d107202ca0394079031700106200c6e1078903001651814086440010038940c01d220b00b0080c04001d072416070258031500001030b80e82c1924180410803002c03031411141403080b995840c00400010747c6000362b001e03070416840c0c0da00c2075045544501400303c20301c0d41403400b0107400201d800c0c03080700e9010038010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 726838561 1250 726837311 726837317
    0x721140c060f0702210901090503010e0601031e0203060624040905040c05100518041e060f15050a0e04150314070f05010504032006040b03011a120c090f130903 70
    0x1d503403190350484e5905c1898200302e10300303030079800c0f0307007004044450250400e0f4105040c440031164460021900b12406c1d800ca905450b48000010024081d5800850504600d40500c946508607950040381e45d640e03014004901a907808002c1c008120283c5d2071480402144290300d95899554100002c090300059805880030409003100040500e8483c01d0b0b10049030b296252039041003050030f132852160442034841c5400ca600e9424030486094820000d07202c64800603800030f10795080a0b0a07110000d259000120303c1868100030704102500001901c41c039004520b4520195406040881d01900d081620998424680304006c4100481b900a9091025800080b01c000e941d660082840d500d15620441d800b080c801c210500c00b103450303a1108104008580c8500c4003904602c00485d615500c00d500292b2940408401885190140342c01c5190090708840c07058100301d40c00c1542101c4000242a0008600f000190454036460710301601c1031501d0001c0501c0200808821540041c3c42014003c07000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 726839811 1250 726838561 726838591
    0x6080c041e06020d030207020d021e030f030414062b06150e040c2a06061a04150f020c01050c01140c0c010b03150f0c1603020a14030721140c06 63
    0x185c803d100340c484c0b103a002000c2d912100c006409010309050310710941510f40a4608005000b61403c02138549d160003030074000c1d0340d41d524000b2442000010351403c0b6100e50000c0040000d0355080007015503c030008980c816840d10214030b10503005010952007421103c800c2e00030300811540050800a0b1500241c409100301d4440d1003041381c000c41240c6100e840f0381d02c01202d03407034040c03d5a08960461481030300009102a01d4001150603803c4510b205c44481c00001014002c1e81c504255408400400d4140b05685148255020b920341800403180f03410070202050746110318209410602000360401c0065140707040102842c11151304c00220b03140151f0804501001c00c0c00c000030501c50b07211a04890300d4030368482101582003000e020b8880943c00354180049180b0203014803000105500c03e070028581080d0510f8a1350342802d00c2142801c03550810302c032060100b040d101c40000b5990040c0c080c00d80c0341051440a44890a081e445c91094a0010510a00d181030002e0202d010b07001140203819 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 726841061 1250 726839811 726839833
    0x70f03121109092701060e04020f0603101802190c02041104031509060e190b1803030a15180b0a090b1e1807020318010e010906080c041e0602 62
    0x19842200c2d05a6080310003207001036a402c078140040c980052914540000380d111581c0075500391600394100100404130503080c8011880c000d00c3c1c1c140440026622503085182150b41d01002d201d051044045614016135100e5002c040d0b0360480701c903021076810303802190400e080020310005ca41c1034200d02031841c1c103202c01c100304250020394046941c04011542e81c0c40c0408000e0025141d0b03030300d0440d01079455a1004960950901c50382640004020040c0600009424239415154010382070702058004100d41d0b5042100110442e0303030141c00c0b41400701d00f0321080300420b680380006502120320b4141e10304001ca01c404040d0400f0401c2c2d401110724042242c3c850b0105030858a03940d038900d520100f00c009660b01e0b00040c41e11041c15400c000c118044080703c00440000944d400c90350540181c10000c5c510948100b490081e101c960800c0ca03103d18503480b0000081c10800040c000c038400d0181150000310320b0761402c01150003500285042c4905c00515011448103503010b8003400003d4019a601c0c60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 726842311 1250 726841061 726841091
    0xc091906080714060f130e070f0f0806060325050c010b06040b0301030215040b0f0c0f0703050c061c020403051c020c09040210050d09030e04060608060d0b060105070f0312 75
    0xf0307283c068089891502610080000c561300024951456510501580300504c421010070001405060361003116413601c480002d0200500701c51a500b445040c098042280d41c1c4050840e502c004140d0302c059a81e1550410524207000c610b55003958101208101003204d80d0060240080c842a08020b006807121401000081d0240d4010508040024801007000d868003503071110224848280c228905074070351041c3c000360b03400141c241401d400c5c00034048200e0102007180082507040c14028240c00d50669403440c0d292000203510510a82000c142d58030a1821082c404550702039001003196100d0340ca1510744c1d1141c0010104504000080d0700001c9824000f040b000d00c0002d00400711422940e6035420807000d8209a02c00700d0402000b030101d820345003140c9c851003403a0341c041d44689000d002607104000540b801078001e441007003034543c1071048035240d5165a410241d40500349059980d40c2c10012140340c000c3c401d025007c0c408a0300610149904644032003583d4102400a201e00a0100414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 726843561 1250 726842311 726842323
    0x90709150201091203180503030f1005030c030d0e0111011b030e1c030c05071e0203010b0319021e0a030b041a090a06270c0e1e0a0b01020c09190608 65
    0x90000320b2041c6001e864641700e0ba00003105100e03191100d090002c1551902891a0001c6403189503450000060059208604100b00010032045008004c00304500740401e407031340d407010120400e0062441c07000c03c0c01e81c0604090000f03851408003c1000641c1e40c1d001c14034420300484c280021030301d0030b080003204041c049035012030b4880b40742d400003554802e80c9044006080c4130b4640c40400a0501010700040d100401c940c07c607144181481d10000303142e0041608480019107401e109512a000303101480c1c04d00c07504800100d40440e044000c4141c81c44401c3c00310004014010352044005001004100301c180c00507000c0c5014801400728070100b02c0013445001001da441500c50344c000c1820200090958102d60f01003114890108840450b1f15090035026000340021249900300d12810312600909815160f0300017003140d408078402c0100c402010003021302030300040440d84c48045541003640204103071503103500c0c0035107c02098502000b142c4c0360401c654003a01010b81c01d01400040c443c600080c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 726844811 1250 726843561 726843563
    0x1101030516080402040603200102120a1409030f150702010501060c08031611070602030a11011a06070302012306031b03031b0f010603060b090c16020d050c09070915020109 75
    0x60004401807000c810380350000010812a0304c0b40d2100300c040f00080c0401a11210f0910400c000e0201041e542c0000e030510311a0f20900360850018001400f609503c0b82c1c2610400c811249041d554012030408a81400d04034038500c070892103000c0c980d0070168002040396200b115658000c101703503600c03200103c2c0c80000100020b0701d80d500130b0011130703d9500c0c200980d090510b40303424000d90420800441d203041c40c540740d01600141c3c001140002005403c0f00800b08142d0811008014800105d10904c51086d5000b400e14000d940c0441c0c104201030003540113105a10481107418100d1540200f8000d000d03508885160003030150451210f1a0390f4158465003416000138040d504010480e00760b120032103c600c2540449228004400d000240d080c031034100a58000e0202085401042c0107000b43d008018104200040c41041100c010819400740030a401d40d048404403071410180c00d1662820b20500c20300c0340d0064054081c0b00000303030025107200494041c10380c3c0c04100c060303030b00c400d0703080f5503010300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 726846061 1250 726844811 726844831
    0x127140610060807030e0f030c100216140f0703080d060506030915060a031407260709020d090605100801050a0902010504030b0c0f040303090e011205100903050405041811010305 78
    0x206014090090100c3c640c85100d40c40c00054911106540928002c5018424050750b00001480d140728481417110707201a1410900551422107281422075003405800b401030500c3e4030100034554106030621800c1c440118440844059907200d0030440207030703130040203a03400c52880c028002070b443c00c04100340ca204032041d40142c40411240d01c0010090f020003404903501101007280840060900c80c8003048801d400001421090f080c0b500c001c40d0105090b0720b800c840071003072188401d1824000350030310075900300e1440581c40b852906503c00143c045640c1c010300c607509000411507102240d84400d01140c001d103000384110340710083c0c40f50440c0c520340ca010380042d04c00c000070300201e1850000690002d6503109900d10b0042c2103100010036070015081100003c010790420000307403444001c105e0151000203080b0205103501e640b06599080c0a41300b4003403a607103600029003454000c1c07050307800424002d801031081e003001d21907200c603c0c1840101220003c0e00b05881705100d51080c811144285c00181c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 726847311 1250 726846061 726846091
    0x6010e06210a020d05070503030d3c1e11090405070531170708010509030301180e121626030606030901020712090303170c04060302070501271406 64
    0xb400740913581a6848042d03a0502c100500029141c03410001804e4481c240000002d60845042620200d14135001d00d84e000b5514810800c100199003c0328100c0118900000280e1082e111040101d044984000c0225140c030b84400004007105802c02481d90a00c115020400c0e940d4416003650746000b80c40c000c1c25040300c615440904c0300b40741c1c4004604000442c8105841581d2080c004000c2707044041070b02010b400c949000c00203444c0034020183c03c000028003035815076060011020b0143c948008841c40107446403140780c10703410240300f182d8560892410b10ba542d0480a1500c41c4014040c0030120307001940d1001201280000c820390300b010426801d652403a588030081000051380003c1c180000c40e540c01c020101c0012000004000a034220b6250030018034a10b04000e0600d01c84d40ea10a00580c4084041040f212074038030803103007541c2039420010b88030041c03424454010002c0c4000402e41d4009001e051850340e103041082c1d50400e101d2035070300c0403455180c40200c2d15040207880252040303140b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 726848561 1250 726847311 726847313
    0x311100f050405060d0b03030d150603020c0d080703090b0a1d060402060a0806012a0201090816300602040f050a0b090d140613061107030c0803070c0506010e06210a 72
    0x4000170044400302c5007001c00c43d00d80000021741903603c40d00d0340107101070703441c03100501041c1c8070003050001309200d040c11410b000c208000c1e5501d4000010314001001a40c03400101c1281c001c0d4000000203070070042d9681d83e482c20b429048000c01d00e40568692890011401082d44900011200d01c5140c2c00742000b8102a00c00380c040c0c03407040001e88158140101c0a40e0040100346860400c0d1401c00d0f81e41d40d04545880c14000901120f20a4201c40c0c0150048446854a1030038050314200700c1d04000004404e20440c040c3c003003210104c60003001c429010384046407062010035000f50003620300c12800c0d0f4402d40e40d20403c00041c0342c1c0c1d0380b0481141c40300512003409545048241200b80c00d0058550800142c100110710f8201356003169400802c404100000007400078600c40d0700010001d03140414949900b1b03480c05010519840c0740100b80e07100000004421500c580d02072041140d000c0116142540c4805000c5003410040710341c24080c1403061030300c2079400d0184200d00d261b0120309014192407611 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 726849811 1250 726848561 726848569
    0x1a030312100b03071e0f1b0203030c0102180a05030610030605190606050a0e013b030106030b010315110406030b0f06030c0702092d071106010311100f050405 69
    0x306405a071403000c80c40060319002c5807008510550407942c0d01105001c1e50b51142500d80756440c60002000620500114020342150240e60144044032080c1110b28191000a01c1e501c43d51104000b10350022914115841c1c038480307a0181280c08584448441c2c1e11603090681d544000c468880046a04101c00c0001c00c1040e88202c0e0840a105422454055170f0124001030b03071480d52000002602c001001000c0b07603805103621418900920300382c800302c01007085a015040d0b030720f00c3c1d0503480c00000e89440c1d03030084001242c1e000040c000d0001d100c1c0d6070762800e00203072009003407005881814501c94900d120040d80e200d86011424284001c509050a105e0100c00512002000356040440c4400143c525603441000c1c0d03114440d50300070a542d6851a10500900040150640340100d50b0549105030715550543c003400c3c5064030b11600300e0340e036031980021180c000d022102c200a80c007a003400403040c46644218040d604d001a69201e1400b12907a4084414018006039840080c1051001f4815450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 726851061 1250 726849811 726849847
    0x15090601050a090515040e0702073213200313062c010c030f02040509010317040e070201021908070f1b0c0f0302101d190305030a080402041a0303 64
    0x800c0380303012003025841c0d0010030b4441d980d0f5000c441203145c2c00301d4100300d560941c12074030364030401030b1015088040c80e2038641480200b1160506002505d42c13400d012016080070618528000c00410480202840560f828014058848505000c03000700182050b060b10640480307000ea000d00b4602000b001c04c40c0c40350001050201448a082d1401200781018160b4900208010b603002c07100008281701c02e00c03030103000c55142c403400e1020103005100400450f590000003030304583d00069030311440c0066121360809813007190808950301d00c90034148160700354158081c00a49081035038609070f600403c0f0082d18284411103400d40080c0b20ba0040440740f9204002003c0c54905d0300b1841d060207000d135600c80441401f103030010340080c109484204294686220b0a0005000b64144000c040f68002c0c0b0303121102010140041c044c0411500c241402003c00c0000c400641e006000e40351207840b04800146400b40c290b405a2003582021060466440040c0101c0d0003010028000c0d460819079030b2402068013 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 726852311 1250 726851061 726851077
    0x304060617031e2a0115080a02060d020901020c03100203040209070305090a031427100306082a1002060403120501140d0606120503030712060e19060317070b1509060105 74
    0x141c0c00560381000030480140d50513140c10500010529000701002481c1c010702d02d0f03102c08959071042c2c0303c22004d80c403141d08550101c3d0264070003590311000a80140c2c40c000b20103000b190075100e030140ba00c0a490f099409980a58404c550005164503140012810780d002a126440250003002d1810b000070302548402c03640c1020000c000d0b08144400381c0c410b10909907540c040c000c000395140004200c1c6081d0b200030b101d054031400c0c10441141024112a40d80450a24140e00c0119000039248800d002d101a10307030381d210003807401113002c4003003400a40700c80003907800303c0105120f024100010307070a5020340c906845168855480e1030705100104514420003101c10365005035078000114100c400c0c00c154180c5140681e004540da400c0c0035400400062009070704a86441c6018418001d548030b04441542015a01a06954081c100c0c260800240308640c4010b00ba101904d0540c050004100064414140680e121750205c2d640e080c240980f420420346d925500c040f04400040307196015001600c0a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 726853561 1250 726852311 726852337
    0x31505040504060b040f060509060405090c012a0809190302010815010c0b01090209130203010e01060c030513060206010810020c19081306200a0b010611120304060617031e 75
    0x1d141d04d640440e044480c00100386648075142c1400f40640e0821204132a046002520208650720305200c00c2c070b44460b04183d100e41040b49401040d4150f04134221240302c1e079036034105d500484268619007250b4503401060704500602030b5650403011070b0741885243e011a074040e190304c080303680d44101d44820105030070b543c030341481503240616001c03a515205490207070035046d00040c1e54100d0001040042140d01c0d4070140301500400042c441518202d6500781111741a040a021040142c90255001d0140b02040070350f03081148000101e503507000134582d040710105403e030f61141c013000d218030b0305a02c24000000c025500c48408918500440d100c41a041c50050711810304001c420b0181105075080d80d44480005628000180d9441484000c1c14900a80c1e0200900301c000c566072384d90909201c144520700904c0040e00010343d070907005100842010059009283d50b030b02d052b1801c1c200401c07443c00740e01600d0040200e00c0c0c45ca52000000c6841d12220351081182002810200341901e034071103c221050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 726854811 1250 726853561 726853571
    0x50d060306020403081e16060b0111030304050a0201120212130602040305030409051e0106081602240901140c030a091e080c16061710030b070206040303050703150504050406 76
    0x100300301e0310240000e0341c0710304a21a40d40e100d80c60480c034500414003000c640500e04101c0c0040b103840081d40c0105090740040c1c003040410f01d040040e01d404461007400310541c08000100b0040140c04288051514400d0704c40c4c00c000d01882c90600700728003600265456504124011401e006600012080c078a84282d8016107055181e079244c0781940c00951040074456103610034007a4a0280190402d00d8146100b1501d1072985001c41c002c0c00b503040680a9009081000e50301303400780f4824804071122109040d070b10004900d5a25034910203210480d440c6d00035502c0c4c0601ca42c0c01045032039650380104c41103034003e41152100030410000b8a46100110380601080000c080e03820051025074107514020840c0540b070300c20510b000c40c100720182050140d407500020b0240190390b0891091458002c0e01c42c9001d680b503407011404010049182c0016081e40c2c4080c0802c0070b0a603000503214821842030f5000c0c011600c9010055050381c4600d00401680046141c00b44000d00702540443c0d8020b00550010071703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 726856061 1250 726854811 726854813
    0x20a060807020606060a09030201030203130618050c030d02060736090c080105010906050d020c030d1e050c090904062901111906020702061e070c0e0f07050d0603 71
    0x1400405640400042180c950410514540600c6000c2d8403140039102e5900d000c040c2080106001e000380402414558048046030400c4031080102e103100f40d020804105c9400300c014100c001015014045416100e031600280d500d0402040542030703001213400624881d19030900984028850142c0036511200c07202034011030303055a014036940e000c3d24510704081c0b9402c0c00c03000401d0303842407032611090040c024010042c6985c4460948100d803030350310304591030f61200203003003010740704010030b06000c0d21010850365a0301516a2156489404214480b030581c071307080d5030643c261441201d070400064414442904175060140c1000c1c1d010744103180014254201421100c8002c0d03613800c1e01594201030390b9050209503008013404884030344050042880c10007200b518400442c2c407001c0280700c0c03a000304542085407100400d442440c100c541c6000042c0003115049410303604100002d0718410a0200002020032074100580e005101c0f403648600150390b034500980780c0344e0001741200d440071723a5804004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 726857311 1250 726856061 726856069
    0xa02030c070905100501020319140d0f060501080124030b2d010206010605090a0b2b020c01050112020d020d030e031203340309020307050d1a1f05010e030a02 69
    0x30703018140c6040002a1804d14141410740c01c0140c0e006141554001c0000f440100700075814a502c171852890000080b40c1c888800c00c00c14021b4055083c0f0307660070308203c40ea4107001500181d080e100207982e00043d503a61114840188014800c07801c00d0071b00c1256111240c175210350404210a10042c4c025401c1003400300300217004c01500203c4960074180740304168120742e814003005004140b83d00c2e105041c00c16141c0020301ca00300c40d22038031409500000d8080510000c504002c0d10181e07620041c0e080e0154015548070180d40a040014059440c080000c0ba840204100c0c0301c1c00c182e0068101c1000358420b0b400e20880c085c0402c0154103006072650160400d0b030b0200180d440b4401c6040c0741c80e8580c20401d01c120070454944800c00c4482c401074140000c00b618020403000d08503182c0c90085684503040c004682003a05580120340c1103205c160034681844009031400184244d5107425009950700c0f2240c1318660310f103910345242e05c54000303841081302e5845031044860006000702580d140046940c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 726858561 1250 726857311 726857323
    0x80f0d090803090d030b0a080d050c01110c1c0f080a09060e030c0c0a05150a0f0e1f02190b0a0f060b0304111804020a260a05031c020909010603020a02030c 68
    0x6541e25807060b030300781132119458018865000e0094031070809036820300d80003d4a0380103444602d03040181c003090a207107042e002d402c012180100941500e60703410485c1080d0b6240d00144800103560400030620b40d200900c070790350b45d01d556411656050000d468407020100a800c01a00c2503420540b24100d1985208040c0000c003841d030180303002060324140d02401c0c0501062103a000a2042c4000e048145050700e25030308941d02d400c4685032a1054807c055020364100c2d5100c1ca00d141c02102d844c0750a040701b80b0000d41d40c07035003040300c2e021600307120171126050064500f5000c008003171480d00c0010070f40d6120f0b290008c0c031408070303c0d1001160391503d0315a4101580c1081324150380d100450962203400d03081c680155418442107500440061400d038000c030301d804010b8860b40c1303e203560725591144c0b480d44030360301c400702c400d42c040559183d084941062075898101008c50402c104005c4000c16181384144200e031141c05018007460f00c0f6030b20700101a802900a0110003080d40000c00500503da04240300b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 726859811 1250 726858561 726858571
    0x6010305060d17250503030f092107060f0e0a29040b0103021207031a0402010c1b0e1005030a02040b04020906030f01080d0f05070b090f0708030315030703080f0d090803 74
    0x50035444d400400c2c425002072100818003003d070002080690040b550202c01c90342d20a0000412a0440d114205070354076055924200700d80c00c00107020150344200144004004260040a060202030300001d40070302100c510b4141041c0650000c1121000100c08400c1103954880c0d50f0000f0300200009400c0d4460000100d800710b80c003002080c0144218a08222581e0111040e0001810b030103055a45480840000d400320842d4480e1400c001002c580c484c0001000c80d07a4065400d40c003920205080e5061203540e400b84104051040000035802c0740480c0d0b000301202c40003402856420515000c0c00000c0c201500d141e604580c08000b0124261a01c030025401099100100d001641c501101141825000b24075034081041c50f50041003a5a440b60a0343c1c2c0007a00400c80e40101c3d200d03042002c0c0341101c410f203456001d0103190b2001603088400310145200344c407002801110312070710b04109911000d880c0001403a840c000d000c01c5051080b00000303001901c4c003401c00080c03070340c19075110780360035801c04c0301c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 726861061 1250 726859811 726859853
    0xd0204060c15020c12181806090f1006180b070c091802060409020d0e061806060a050109150c1a1e010b191b060c1806050306010305060d 60
    0x98a00100003000408442c151014042103003441c602c02070302519212005d80344031040c00f022603074003004a40c0794102d80001d40020001020602542c411025000040312010b1040340c2d04400161002d50000c0c40c00d21031310705800e182d10b0709030170a0070076100342d10810448014440c4c050704c0890804e18520007801d01a002d21090401503140012203000c3d2034503010948803c02e80f1051640c0161902c0043d60150b50082c6005030300c0700420b50307060000700451242c03500c1a11811080c025940703619038511480074040025181c542d80c0c1c6038180f00900403a840356900003861359004101c405041c0c5410a810201440c000d22082c070386850340d118049040b4024507060031800d0a1003005d103290459000305811111036240250716244d00c0c60703001c1c007c5040f100543c010300c000341c6907840c0c4180001c04218000580b201c502c45800d0038490000c1400f403514001140d00155400c0c2500c001c0ca50304411641075940b02131440c0c0c1c030b0200441c0903240190841ea00802250841c2c00014942e00c074401d641c0d04460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 726862311 1250 726861061 726861077
    0x100606020604170f030103020f0420030901060e190917030718090527030d15050906011404121104020a110d0302070c2112080106170105091501050d020406 68
    0x30800f944021006840f01440100410031101d0080560095a044903012100480061600404035020f0000c070103044500107200445035107203540b59000340d40107d00c0d0300000c00c0f59a1310380380450401c03038080d50000d1110324150b5030040451040c0d00b04100f1944621841c0e021210303030040e000b104c1d0700280d6134540031a41c1c90fa08540c608001d9060203006000d2403806001e0b80c00d00741a2400e0b4010200b0000fa410001d5000000c0354000410880780000c003100340c100801540e40001040b01d40d02402035a100d21412808119550320550f0040d0040d80000c027140e02d898030b40010218101c03408001128a106440380000256a41c0e01c0545240401070319980101200d114103a030801409071042c0050500c1840300b0800f0036002c18001050b60301c194194a214580745454001035060b500000307200c00001c500c007500c29940409424100c4119846d06500c0584800110010b84001d0203140e80011110001032044450903010080e100010704141c0e2038503201d540908140c2e80a9001000824204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 726863561 1250 726862311 726862313
    0x115150f08040b07080709050d060e0607032016020907030902041d1b030111270a1505090d080309070f09020a1403090106080d030507080f0423100606020604 69
    0x41400841418010700e8010700502c2c280e51845a001005004101042641d400003040c00703009200341d4020f08001054242c0003142c03840d01001a183d002c9504825025081c04107080134003038024542c12030007204000c004040c3c000d40c1c580984c0c001848403408409403051030000368560701d030341d01c4c080c0c1071321b984c0402c01444a005000a4410a021800700924900701c8142805e034082a10071500849902c0000594040030001e400b40c201c400d0455803100c00090842d86000040b060080c4100f0311810b80c545140c40c0d4800c00115070030b244030300399441071002c5001c0c01d118030800c024135114074010074003c101d80d0701d5141c402c1d05400484240e2140e501080080c487c8282c10303001c40c401452854015898415a018005c055501204d81034558060200c04200d01a10a4200304c01070302c1d81d10200d42d4444103041004021704015030701107020501c41c601207010000c51107005481150009050320421401c0b441911075810062a02e040314000d00040c0305040006000d058018003142d03000303140600742 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 726864811 1250 726863561 726863567
    0x7081e07052422051c08031609030219170105101205240702012a03050601110a1505130c15050408070b2116050318030307021b04020403020a17011515 66
    0x41c4035900c00c5d1112448011303c000a841804aa03445641e50b040c2e02c0701003848810a40fa00e4001e5000294005046100b60200214110101040300c0c1d295490303032251584076800074206ca00a448650858040260a01085000d2404100c485100d80115162004000d00000c0351110f01c0c43e00034929035540c820301407500da0900a20090140944003086100141c0500141d503080c000d6062052503103580000350580c0c0143c2d41d40f6413000c9048203680740d0009074582200c910742140183e0742c0b102d1420300403e081048500a6800301980401c0031031482d42043c0314040918041c203281317000c0140803c004034250300240641c40042c0600e0310015100d1040041c000b070315580c00034108400b07a4503070040019910310211542c1515006061181d602d440303103010b41c800b80c00300f01003001081c07000200784084142c2c0051181d0b000701540c000c1200740c280c10000c001c141d12a40c132001c1c0d80024520030502c0f56903440c03858480c1040c103500002984003042c940001560300035501c00519000b0f120038038031368950 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 726866061 1250 726864811 726864829
    0x120e03030c071707050108040b060307080604120305010f030201170a20210c0d0e030d060608060a0503031806030a0e071206140c030a180507081e0705242205 69
    0x122100184c0310403424a00024001c1074000c0028150b00440001324010b9201440014050200340050f0794052515003031003083c40d81005418030020317103402e000180d42909200b130707403094039030594402a90410013000c42d80c401748090500115a1341d00c0b2000005220922501285525200d1100d6151584809060315015510413040c1480c031060007041140070703402c402c542480c070300c0c2c03500052006d020051f4940f0718080c050b50f09010514085001c90392940001803148910011582c05440e036449509250322400344034440b0080054103515500189000d501460b408103080700000b821500c5462414030f41300ca02d40c440300c0103402e258012820f014207800343c40c5c10820303825000071841c281000c0e104061300c001040303580e81941e00e000c040b0300114005401038460f81c1040455200303549400e4201c3d03c81282c402120404c0c07031500d016200011021440380110f900092030340404503c0086204011126000340b10780700386040280c4440c5c10b0524040c803090b48845000700c00103500740824018440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 726867311 1250 726866061 726866099
    0xc0c05060403021c08040902040e180a030f0f1e050c0d020a0b0f060f040c02010e10060503070501081801020d050105010f02060609010611100905061609030807120e03030c07 76
    0x840c08110900140c0c0b100c1400d08500415010b805244041d1414142424042c07030704009103107070000500051124445041c1c501580d0b8a5200760600130801130340a83d101214000280130a080043e80795070079001c1d40ca541500702490a152901205640058641c04660f11030007000c21404292400083d10400a445911007580014100d91002d40c0b2a00c070600e40052104a101d4160000a50a074032016107492169801420600411112030070107806420080c00803442c0d44a441e91041000106004000407035101070050401c45042038011510800700401a00c0849510225411682c00c05d1008040350251108006410350600c000100518103000c0400115800642400382c07941d00c01c0001c50441b01d080c00d00c010440d02240f00c541c2043e950f81c3d185000b8501d061540414000702003803880c82002c0cdd0118035884c409520300c058541080c14003010b00b40e00d80500c648000074000b610400100d0741d090804c0900c0034914030010386035900a0001c03500c1d5400015041201b10761192400c0560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 726868561 1250 726867311 726867319
    0xc060f0705040e01090c0507050f01051b12060d0203161d0c0a1d030f0316020906040212010b0c100c0c050601090b100c0212030a050403121b0206030a0b100c0c05 71
    0x2d807500841c0c2075240018080c4203006a07540045d140c0e84c900820403a031107640e004065a10400c170501e0724500802c5e04a90300c0a202d944100c1589200000c081150103105481001d41c0c01611031000b030140344401018126003502c00c408000c04012110b464203030040220661803103003071164900e0540c1e1078401034100c210f03a560510191642c1900054400002d1000600c7d40c80c4082e10240040d01d0080d844224540e81d00001070708888941038491a0305102d4002d8484104a403140c07403c0c8401c1b8442c00600c03e142c0700c44140141b00c1130801500610f006c2c1244021117281400301c1a0400440307108444490105001c13054820804c8800d20a0354014140700004000070f00d02107001c0b07150b02c0d070b0100c0030100300a032023a114800c660360004420307850360030042100d0300e860200c14081c0c00b540c00b600042c0c98021807514800560780c4154154a46411110188801c200e0035a0901003941c1000e441001001d4942c0340158103615181102c49407514a6075415446103903d081c1a00c0d0551560807490003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 726869811 1250 726868561 726868567
    0x30c180a0c050f0403110a0e090d021905060619050a0b03270606060703090b0307030203040201120c020304170a0609031d040605100c0314040305010c0909090201090b0d110c060f0705 80
    0x20076140c02013554116500112040f0417008042c0010f0f00600040d00f04a9403103032003105000303442000040031b90f4490500e800f282e046400803074010950921800b002442a8403000001d50141059045e030400c143e04056200c0c1240e48a40000c0c2c00210190002d400c000004800c01c0307100340708110400070400140c00d1500c246885c81100710303200c1e0001800700e406000002003d1007007601c1100c40600601011460075202c0c10807072070082c0a0b43c0291001c4e800107841d102490b00c0b0301e6140c0714800070042039400441c0303007030320744080010760001110b050001030007103403040b0700407500c640103800b5690b100b85c0d12502d0101c8885c110001190b5000b4030a8011403904005001300c3c1c8401020828014140c00e01041d81021450100c8200d09000c2c90490880340c0820300204000c415041030301c1380305043c1c484210b01502c5100c0c040c220b928811000c1e00080d0f044900f0012800300c00000c04000050083c04a510140201030303060036030001c0c5a01e01c03140d1044082040019000c180260424411b24146203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 726871061 1250 726869811 726869827
    0xa021615080f041101140702040e06010602060609010b1213020310150f0308070b25080601020d08090d030b0406150c060c020307051e0114010806150102160e0402030c180a0c05 77
    0x31030b09040341c0807418055040341440b00307000c40400342ca034150f034001d000b808ae4001200035580c540d0828840c0200ad403041d0350214043e86040700c1d01d1070507140b0400c2d80c030f414a400269000102c54001c0c1060810302008180c50001d038405001c2415000c0d000354022440c3e5070010150301044070340d58803070480e07040c1c3c01704144000f4a01ca8116160316401441446045d1a610201d10346e000c0340d46034045c000d6203984002000700e0303000003040e480741c3d000340c09507030081103600d4090b0751b006002c07154204075402098100324040e000390304c0440c4c0c41ca8060701c0050641d0f04c400041342184100891032000c56071441c05403003003081c1400340c68010480c9102550400c4202c2c0e0710304d59038501c841340c1c2200c0702c0020342014078600c1d400d601100801d180d2003039a60380c0e548e4440f441500c0c0c0300c05503180340054680d5a034080e05940000b501c1c1074101d0f00c80f00703505280e42c540390750410158006882242d0600a10029489980c0c0f094651200c42d4141039035001e9904007200344000315001d028045050000900c07000c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 726872311 1250 726871061 726871073
    0x20a2c0714040b07110a0608041403030708040201080709030602030a0e07141507240c03200423060a2606010905040c020f0a0b09010c090f0b0a021615080f04 69
    0xa002c552581008985035107051030318001007800c04100d030741c011106d101d0000d503059000042178003460040c20f04041c000b082c08401ca0701e900c000c6a42101180748540454015441501041d138401c4051906520341c1f0b480340e580c3e10999006581c00c4044940b150820440078001f4491500106106140b00c880114054081107910040d840d203051400e81c0824440c0900008688116000ea408004508542100c0c14640014070030301c104400020f01c1c0c0803d48503a00386d8201341740186446a0507042c2030916003100e144044034441640c48520f425051005403984a2a0103406101159103641038a9111401043e13074800520130b000d100310081c8805e000c00c07640c01030b81c1c03401941c4040d1404140b1031060171083e450600d49010240882c03081c410301906018900b6921405000807400038841e8002c0042c0480f42441f0500480c074040818201c00c011618240c8024140400d80b8010f4420b41e2406c080b203081c80300d285500089010550000d44c2c1d000302e42c03010960341e21000b011444845401c141d1285 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 726873561 1250 726872311 726872317
    0x1080606040504020111011104090b060c060105190e010314062203051b101d010b0609041d030d02040801060e19092a050a0605091c020a2c0714 63
    0x150203103507102e0102e030940e44109281303a40302050354024000c071030202d1000380040d4814800c11750024503020f44030300c00e840c284080b035241216200003000180d007014100032902d194030303110185021042c20001900103010144c6402140102daa0094160362600c82070704164005109800c0380742d5440300b50000c2c1c0101643c4064064152800b5070300c4155000c1030381c52011192925080c68440c034031101c0b1451100b84c01002d80306200e024020070041c0510400c5081e41c1c404007480e5484542070060302c8403810540c1c404007031000070844008403000d0340c0304004c0c00c6601804402c12100e8002034103010a001c06d00540b0010074840e0980a090724008088404c0c0c940d81d0000c1e1600540c80e40440424007958505501d0b114001e03036a080484c508403405403401030882c0c8106400780f21686400100c090143c3c042d16500390010304050022a0f001102c2c001860301604201d03400b510300000800c83c102c90360420b0405408009100503c901c0f0454409951b5100415180800404070180321601d00c0400507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 726874811 1250 726873561 726873571
    0x9060f0804020604170303041407060c031b06060303080906060916051c0c030e06011505030c0c0307051204080c10020304090e0c1c031808031e0d1d15010806 69
    0x3090100e501c89200003400303841280d1045010030040c0082c900008404001940580d00c02c251850800c8800c991071601d510941c81104042190b900b520400301b130040b050200d00700307640e018468100103180d4441003110305a030003c0e800120900204113648804000c460303000102281c440e80e040c1b60002d1000780102e4103101401c100b000203e0070324140355a490343e03446c0401441a044c00400f881b02c07070040080015494070341423842180c0000804480c0d031408107516124030794a40d0b2031543d800d9035840195200142d8444184010841407002c103006115240003a883c0e8030050b0750715482c00f08503516040c000b898442c400d025000d0030040103031300041150202c890b0080d0101d807008040c80c40c142488001414160000d4000160118602d0700e55100401c10344242c0713450032880010445500c0800c0203004c1c0410f668003c101000c800c003012603103158450900760a00303203000b450144071010ba5842d00401805550ba880010185800900000a048113603c680b14810361400011a9480d02e01802c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 726876061 1250 726874811 726874817
    0x26030f0901140a09050a0f0b061e030606270a230f04020103050603010b1f1416020103020f04030f050a030f030b091807050a06020d120b09150406180501090c09060f 72
    0x400c8004116051040b16600c42d001051fa070341e5000107040c0484104d2080b02c00501c5045c1c211620003012483e00c0038455a0003026000308000e0b40c6580a01c09001c0c000c07022914048620a051a143e004403400f043c49045030380d00c08560040910103115881503c60301e0ba54206440e0000c000000000d4000158056024600401c2940742c440100e401003641070580d507001307a0705005920b984c68029080035102941569104100541140d2440b07040c02030390191aa13070b03280b10354a2400740d88a6009460008010345043c1c0c42d203079484e61464000140100c040b5550741090f8070860034150403010311201c5000604050002c01c0c00ca0001806041c4014880c8000303807540300c0411040c040c20051740c00a0040640046407490b141e00d000703552a0030b0740750314200141d080b44c03181110111170b0040c0303440b1260181c00e07101c943d12402e0088000a4040d40d4090700f00350381d4400010103580ca45884203a1600d0000001003c0d41845410740581d00c80c48c1c2c240050202d000002c1002c03503408244e1a038010003520b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 726877311 1250 726876061 726876071
    0x405130b04020c01060909050c10170702070e18100606050912010608150f01060507020d031d040f0903021603020306010e0a09301701050d26030f0901140a 68
    0x4001400034003c680c030401c1d01d503280c82c00102d00100c1c0366100a5040b4096011030b03440a03003072003c01140d9903e850180300000c1ea6008403c80c0204a07a12060b0409000d0040e21326450712411144188417088a00c6c440340289a002c8039142c070400d00188200404d00c940070700102e804d202c0090302d1489443c8119005818101168107030788803c0d4890300c0035045620a88480d03205000d00d02d0240c0500b5210248000142e41c000a0258082c00407250599800352400d500c400f0b0740d0b01d085d03071280d50441d01c058070130494000b040d449940c1c61042500d1412003020000b0407021a06009203080c2c107000200d0411a0900700500160350001990750455060300307411522a9502203041001d4100004d0040c1010942c00503006a02c0c2036a811600714242001044c80c00c0e5921720048034030041d0380c48030502825a1400600080c244042a032000600416900c20b283d0200d050784400840142205020500d01105000d401c40202c0405500528a54002e210404c90351101180c040380141c421000e0594403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 726878561 1250 726877311 726877331
    0xb1e030703080a1110020711090a0b0d0803010f06020609120304050a0b01180b06090916090b0708090f0d120c0f0f0309063209040917180402040513 65
    0x400c4100302855004646607258204000b01404958904141d0303105401080b41d003a030301808a04c29181e56a4008542c4210b032042c0000b8010b4151010b0100400b0503140d84104140c0d4480704800e035085441030780e40c9a030300e46c5000c10603a03101000c2c0d04800d046402160500000110010b460b110381052880600da580d1614600305243c9a041007009101414000c00005c80f0001d80102004894000000b440881c1608003000031038800d40d80744a42c8240c100021070400d1414100c2c600790b611243c200341424503220220f080c0190803410040311100300008611440c0d040a050554000703800342c984c841050f075541d542c0380b01c041400600c202040843c400c114184580900082c240d10342081d01d03808060b00e1420010030351400c0d03009601c0800d4038020401008810f90f02030041c007c00c41c0300d028440c58061284c126655124a4820b40c3c00b0307846502480100d020112444038405a00040c07503581d1401d1030b032010f91800c01450240c810f91050100300419295005645250050960002440c00003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 726879811 1250 726878561 726878563
    0x6090803031b0c060103080703020106150c0f03210911030601030b040303110f04150311040b041202031509060f01060801031a040302070320010e0301020c031b013207030b1e03 77
    0x144000e88010f40304e0f15000200340800c000003000d03010302070317170003800001d031618145401d44e2521300621000442030000c400102c0c01800225440324030900e0150303001c030000d416450b0a8800d04207410520790303850005008009402c10700301015041500075001561550300d8409400e40700500203001c0c9900c0d510104003000a40701203421002d80341605d0741c2c680342c0b1740300b03111091506010484003080ca400c01c901420303680401031354211a20104c0c0e071407416080130340e00302c130040d2401012030b01441044c15a402c1c0603000c0000511070082d00c0b00814607440c050050018055045e405041845203000040c000314620900348a50f60613000010501c0d074840340340403032034000c06520207041907008160361000c02c1d12224405000c080d00760b075000b590400480c101400c0b8880c2e41d03480307040c9500803c030118608180442c41704c01e00c1c2010f40005201300c14000c0c40c2803650107824004901c14000100f841c91860640c180c0f03a00110285030810001d148100460052200402c080580031548400403045940c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 726881061 1250 726879811 726879817
    0x1c0c0c2603040b091006050f1003061706040312050702100902060c07030302010204092007060b01090b13050405070c0308060112091a0901060e100504020d0e0607020c010906090803031b 81
    0x80c0036503034580d24509070414042d900820784110b402d50141109511820901c0d01420007070f01d80080c6220710701d8a0a0301000300404603211080e05068407228005854401074062613a014000c00141850785403602d030090018207051a0b00400600e481d003132050050340025107440c1901c5814000610721298000219103015028000125101d00c0001004065040d0094000c03101012010302400030b0b01400021a44554500044109424003c80c400308001d504200303003215040c10418070702501c0d40d8601c13035568042c040c8c0e00700d5a40e010780c081000f404c09101c7c039540031000d4030303044101c030820b1740c0d00401094029207040d04020040b107082c6001c05480d4491b801003584400103078070500300c010b1403030442c61088401c03500c194078150700002e030400405182d07403041d09000c45052190b410a8100b000079082282c0ea103070003565466034101e04000810000340070303074005c0d0010114110b012000404191544e0000010441c4145040100000010503650028248c0c550000042141215068280 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 726882311 1250 726881061 726881123
    0x20127060b011e0f020f0c1503221103150c0702091b0a090317030103050d051c05010b031b0a0c060b0d05120c060702030415030b12070b1c0c0c 63
    0x181158444a4140382c00c140180c0c2a1360f81034003583d02c04003c5500c11522002008080c0b0340207028162000e440c05408402968000701d0718800030b45242c40e025a02c1c0c2a01c86121081360480c9902c03d44080c6860200481444130700a0004042240b03800700250405001d0303e00001d0040109402240d29161140c82001d001c094a240f981d403510450100140102c03814802074030110f40d4000454609424042240e051782e410100628441c4c600603401c403050b07400b4005000d803590410180286500d014003405000b000003034610f52700c0b401c100c014601c0307030803140c14a038040160400821210940095144944507001000040c1712419880400c03070003140044001c02c18024542e01c1e6502c0303221030b00a88103401d5103508032960f0f179071031741d4060703036203109034000d4070b4820540000384180c40e4400c0c2c1201d500d021010341501204003502d100c161416845400c90140002c010034000d101400c404c00c1103103201c08013f4288903d41c40c802010b0040a1544005000e0f480307902c0014480b0041c8541d001060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 726883561 1250 726882311 726882347
    0x213090b0a2306030705010f0e090f07080601020109051009020f0402040b03180a0f080d1509020301210b0f1008100b091305250506070f0201020127060b01 68
    0x15140500c06000101500000300c002c2d031140c549541548032244460300d00c0f600703020b0010301101c0d0809005580350310007180600304000c220b442d0f126080d103850f00014080c150240b606481400c04180c007501c0301400170003190445e13240404600c082140020024a0000b1545001402c90124000b0480d138103030f011582c07604103000240014240340b040c4011449840301c6550b507101e482d5805840c1c3c1c0c0b5503d080c0005071a8078107d0301c1c06000315074001d00420500c23003d000000740030800602c041024802d2035010750402a40800104545803c1c2851760104030040d00b1004030407603890b0358040e0020009880448000214800500c000d07102d40c04100c0070b000b440c0100c6001c180208000e0000d010780f01d1007240034009840200f1176120341c032403601e5405a4440040c0083c3c500a1864101030440c00904058800c0c04003000a003e44071305008044040c014400c400c1005154000a0300750390400c12040704614242011089000d9210282c2d0215a0b01220224500079140c1c0100c072a584108204066 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 726884811 1250 726883561 726883583
    0x140c040914060c0313030806181501140408070b0d02040e040641100504090b040b070e060a0513031203140a021905070c0e04030f09080712021309 64
    0x34000c80750241c44048003107204079100c998a001c49104503000580708010b00c6070100c100382c40040d0054904039030000003e080c522008910f40300840c00d456065801012815454800312150350384405500409291004102e10301443d1200003540c1e4005403080551003400400d07480007586964046400818003022110942d040c5810013000500c41d4842600e6401c40c03446140880c0214403006204160b03c0381c041807542d9000007460004404003c221034004996148041141e9a5901c17402040e0760103920048680d10385407034845080c20010708140f040c86100541480540d0b1440d00b200c0d089502444c00544611540d2410107808500303410007460314802201d007c0505505a10041c03090f1121704850103507403202c2103072208134400c50307139510100c02c00140a0341d00c4030f000d0401044510310901e003c4040c203983d50010711550506a0f01100041e01d00e0701181625680881140060040000504030307880c5880003440d008000448000d01a101c1c8074100c1072000c41c10340c040c0754556002030400007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 726886061 1250 726884811 726884813
    0xc1505010816051804060b041103100302031002090d020d030306154a150a11060f0907030f050c031608250311060403060e0c01111504140c0409 63
    0x3480b40e0b15580c001004180c905000120703403420072601500042c103040d65110988841d1074100242c0314508020350003e491b03661680c00394580f00300452250030a8003041d241d4904501c10142002044616020741e00d006103c103040a9681000380c4210590441c0d210341c84002500c1d041e806808958401001c04029400303e030304054102a00c4103030100076503600e40800d40703007224008220038110b850500c64200d08511078920f00b42005045410500204041444209180c40000f00c0c0c1c40791030030200203400041000d100c01010422140c0102800d00f0002040c03030848001da03540e004038440945501c2d034001944007800024403920f0090740001c2d080c1e44c0803001c8240005044402803042c0b4000d440b0303c04c422440c80b04101d000e0004034104561403890380b842c40d1a0902040e5511100d20350194003000b0000c0000c1807031082d055042501350242c0000d4031844001b62800c0c540c00c400940641180651840086e2886181a13100394014440b4880040c05c9204c24a400c0710410001e400c03500d0418518 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 726887311 1250 726886061 726886063
    0x3170702010b09060d15021813320c07080910090501020d050a1e05360108091c110312010905060d0507030f0203100f2f0405010c15050108 61
    0x1441c070400a8460f04056115081031001c24107030094013400c40a2110001c5040340c6454004141d040d07000740d040070303010171400c000030b000001c0c10b405681080d03510191041c0c1c8030341070006003100305075003a42c807088540034652420307424100411504d8101c50008002c0704205424042c0d4900403000b0340f0640880d81d6400300540130610707500890f8054818461700b140418402c03412200844070a1381d031072450075044141070044091101030001844400c3c8580d21080103460a1020b03982da03181c10301e0f00740d400820020b0000d40f1080800c4c07410810b91004000c0c00a400042d0080c07080c024a009846e0f14805002c01c90f01c880c002c448141d2503000010340064a8401d11400d00c1c1a00d0340c2220410030341d2280e0b402c05c5240c0400007402445900100360030408039003400c02000d000c50019055517410300c0102968011582c071802c0b1400134030398900b00351186811208122003030283c40b2010032048003200c00024190700a905c903290411404409040820a035031403070524003000b0840074400c55848451103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 726888561 1250 726887311 726887321
    0x4120609050f0d02070b1303171c061d100e070c150606091707080607110c0904020a180b09070302070203192303090d0b01050112020315010c0317070201 67
    0x280c94034407541e84001c840180118488509043d590000d08019160110a0103140c100b200b0101203404100310000110f060042206c103101c46500c040366480c030b2541114902c180111060b030740c219141000501101c0f4480e0515101251110035911090f0f03100204c2140c1d0941c2e6801c81c0c00e00c480b04000b40f280050b0131500c1c07841c2c900d10030307a50441c00003504510403040b15401c1c811840081d900903001c200c24a80d80d40940c0601c03c4070025104090380361281c15140440070b4403004001340100c116003045030000d01400700f05500c100d60a00a074141500002e0050f0501c1c000c507140100148204444100349a01030782c0c0c00c1c04054000d101d40e07c2c1c688070150003034226100982c024016101854400b071402c403803444841e503000002c0320008850f04035200c00005600e4103803965100400842d20a952030384a00342d40360744078408090966040c00300040400040e00d540d01d17000c600510510490041c5005150a4404203180c1040302907141e050482d500c9000f092691620b45558052117800c0b5819081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 726889811 1250 726888561 726888563
    0x50f1203060406120b060f060c07140103060816090c0504050a09050603010c1e0509010c150507030b03010606090e040201050919090b0906030a110312120a051f060305060604120609 79
    0x108000d10f80e5900264208205007802c010100444040016120b103010b03c11100303000b00107014181402d908040d00ca14049241c1c02c60b2107294454442c064035507034540a000c0c00340c103441c40940031941448118400c09035480c010484001c0d1101401000707d0b01c1401a240200401488218039030307946c00c40b050081805450140c021b50904c04007168450144502c2d0030182e00d0b80115058140400404440c46c3d0845001e4a04100a080701c10007c902d081d07091408009174004001901d0615034000f0701101c1c207005120b070180c0d040043c108080e60b0807504440440d0705e0043c0d03400641d0b4841c4012207aa10900c11800c0e4880b203c2484262801d0145810b001030303a20001080041c0c1d140c250400c903d8000480740705500d94010302c11003000500319448142c0c501c101504541c0d03078201d9010710b08007503000400700c032007002104420082d1040860081c00d41003040403a03041c2e1084030566512038151128040c0340306142d11100464210745482088074014500303e403031207800041a01d0050068010b400d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 726891061 1250 726889811 726889819
    0x80603030c1b0a0807081e070902071a10080a0209040602090a170c0303030103080f1b0303131a01030503121005061204060b120c12010e010f1d03120105010c050f120306 74
    0xf021034940380003d2054156405500103050011001c3c58141071400050001141ca01440d600015035030200d001910400744100c00002040e00860050250b040b8014003001c5861000e0908101207940411960107076501910101e91660f640e0803c800603110341e603601034001c00c64110001d00034540c0910001401f40b0301c800c1d0307030840180c5810559a4002800040c2042d00e00708900c648001c9141e00518102200d040c04843d6100703042c50310380c1160011210110503001450b2414100460a4281c4102c0400031040c200e0650454444560321301481d45030009140301840807480f81d95000340c0c1000203040081c9203903503800020740c10207100f040948017116807a080c614098500c1c0350070f0140010030340340400100100000700b020840d032150021201c1d10503559440e0000c000d01828021484001c49420020a264044483d80f0b2042e1244580400c0c080e00207205c0380e841004444000c074115042480c0003401c01c2002c0c00c00e0381c1080c4e41c50708043c01c00e11074030518080010000014600c1004111 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 726892311 1250 726891061 726891079
    0x7030b0f03121b0106061b03110709020315010201020f0a0f020a0f06060608070804050d1202090a0b25080a21020307020625080a1a121b01030605030a03080603030c1b 73
    0x105065090b00e0450066602180703811814040040007040840c7e0414020701d08801c840b030881c1440c60404400717402603d542e1307400100304888041d00c070320b008041000a04c000c6290000e0070b00c80981c20301078294200100581038080c400302c6442041030040094002000d002c00c1d060624000303008056504c50704000c61a0034000902c0340303004017150340c40340d030b000b9005c0e0000d03d10351281140c90366010318040c00100ea003400036070015181c007030f030300c20140c0303d100303142c6503544144072003403142104240f0411044e82c0c034a01c0c02c1c00040d11020a94881000c0c0382084c01d4014020b8118030401000c01b110000c2c80392000c410021000d900103403484c024440d010340880200241d01003044480b01c4541c3c0c61010982d5100812043c1e41154000303212003035800d0f0700c032881d080b04030006409401e25a43c1a949036008900390268022a40c903034200503182420100405450000420b4403020302c0c2001400788501c1900203110f6442c240115511000e0b910103458240010540e1100c03200001c02a034ad006200403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 726893561 1250 726892311 726892357
    0x3020106060e030c0d03030f020f0903121c020a03060b070f14160605280903031b02220f1d0f281506090b01180e07030b0f0312 56
    0x1903440e480c641c000607004d01440c1c020740042c00880d82e50100d04030101540c8011b4441007500d5031015016441c0f80e0000503907640385010406241010460700c110243c1d0040004c02d41105e150054440b000386841c8000d80c640d03a54400170380080107142d000500340d01d00040c11784200405620640d80383c41c45100e0700250582c211404558031801c2c151460070350f68001c90144452806200a402c88000d542800c0e5281c43c041540101180c40101c90200407541c40c81c1d013807081542043c020750029003a501464070b1b041241c0c000039a108c0c06801c0300c00c0c5000113804250030116960b080302d09001d41070081804111410000c1811010601404500720300032030103201080b21000c0f420110304002c025880c10b40010345c080c100300506070b50b2800c94120108011204940d800b60050100900c03200400040c0e09610400140c00c040c1080c2d0f0780741d85909240818054002c01c0551a500001c1500d400901181c5000210351003201100ca119490b00c99080c1c034110350804071008000d0544201a124145082 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 726894811 1250 726893561 726893567
    0x602030a0204181b1b080403080c0f03070c0b1c0504110f010302070f0b0c0415021b0607030f051b1204061412060933011404030f3005070302010606 65
    0x8031010410200d2440d038200320032a403207210070300461002c010418911461658500380c10361f1040e4002c6440700703804140740d01c100358140403003410501070300090340c50071240d641d8001c914107642c040c1e0343e0071590101d0554019452900400386400809200700542e0500b402e0200e8040004068640720b1202e0b042240d001d54464000d4600316a403111044440b84c0d030554540c40c1c0c01030300620f1011000014800003810b451400c0c0200000c25044d00644100c030008400074001c2411300801c2c60007480d040107003e002940c091a00c04850155280094549646000440c1d40c104080340c00581e41c0315051450070050035210080c011501d1944407900d04007000c10310211207010304402d04100543c11000581e043c00d00328461640082c05108510849075000b02018206054441c8010f460b956054044210b51f081400140d84a01c0f60940c54146441c5a98520100101d8400140b04402041e08071050010200e8022550341c240f1290f91a000d10228004143c0d070002c15080c1c0056007071540c00125540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 726896061 1250 726894811 726894821
    0xc030b10051e0a111c0e060f0d0e030412080405040606090e0f06030316050645012307120b060301060f0903050d0c02010801090b0f0d0606030602030a020418 69
    0x10052215124544501000e0040781c005601c07100502c12134520f02d02c01d4074401d00c01c803041d0340c07141d2111080d140a000d100401505641c003059004810802528034001480c80c1920315078000f511010401501c080c40e0a415405240d010340c11000c000d16101c0c0c208140741005e00252380d015201007103401c1da621400c171001050f80c441e260b420a524404164850703a0803882d01c1c1d0090014003124a0000c0d1a08104003581c2d40d00702c2915103400400501c0001081c0c8064110040c644100d000303241444443e606031000d50344441041440740b0540035641d507140072b401460030105a461055080c0049409104c4648411070381100040c040850300d980a600710700c290140c00300c002d804c150030340e0b0a10105940182d6201028802e1250900c0c0000c0003440070082d0607a036940c1da90750b840c5000d003a480050714070801a00000b103181d081041c610303100d461300c9000d2040360b4030498008003408024200711005120f250405012640000108a003610441d0001c00c21608241c0e071080d5101c200c040c0101c1115 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 726897311 1250 726896061 726896077
    0x7090e07050a03380109180201090909030c02030319021e060417090901090e010b031504030f170709050a060503090a08091203071101020c01180504020304060605040c030b1005 77
    0x100c2d9190034000300d140c4040003c01c0702001855111000c071110740140041000101425000c810340c1d00510100026015408521800c0ca02c501e0704401c01d40c0c0003030601c1d01e0b0345c0510354200703a80700c20140902d03114003050041c80d41c024080d281d40760070076280e02c0c03407049603189802c01500ca445004080d00c0b00c0d490408021801c03200103081030ba02d0b10b84d14200c54811078850034114141c00c4c407a1841980d40c0e030200a00031b01801d0000a000f28403d19081d003910440007102e403103078115028281c400540e01c01c07a60f5005515150100c0d000912a50036144085650314848804040d00100413080d90000c0c050010341e94101c404000c0c2a07901c81c0c04880c6407208440b100131580000b4640d00c006040034004d00800540101007403800d2000a01d410300e036070407006040c0d030b0091444034044072550b0180014144803e0078649241841c06c3e0980d001210b15480c4541801154004009002c0c0880c0340d0221020b00b00c01041400219042880100503000c0716206900c100a422000c0d513100307015a04981c814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 726898561 1250 726897311 726897319
    0x10f0608010315020a0504080d020f010b010c05060c1e0c07061803050c10021c020c0a090501060503041e0f050d0f030605011202070804080607050403110f01081503010e0f07090e0705 80
    0x807040f8034403018043e400c819038074000c1c06020b000101c0d21070001c2c001000c28103041d60050243c0d81d48130803e2401e6031501403003181030281c0d0f60840d2011031400b1460b198414040c8921070b40d0b072517140040c00c1050342003031000f114001c0d0128076019440b030f000c40d084049409594a00e032100c0b02010905041c1d40051200400a031310004a4124a09200c1d101803a4042c1c6030066420245040202900c21030010300d205005800c4014400c11620b0402c2049014004d0714004205660629001500d42d02c0040c201505118000f6005038028440040301c0198a5208541401c94012460300c00c2d03440600c090300c0c601180c1c5044e40174403076500c04d205500495005940b803101c40784c40303078aa1500961101c0c0060750b0440702008042a00358041108600507003003039072000e41ea54a10306001140401003c035103841101c4035141c0c0d43e516a440450b5a40080d43e840141050032031000009004180000e5005524060400c20183c2180c020801360200c0740000001d208201102000c1d0b501d5070104c1c01900d40c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 726899811 1250 726898561 726898583
    0x210f040b01050609211e0304320d060e0723040b0f01140f181002010905030a0e060d290102060609040308192a020a0c05190b030a05010f06080103 64
    0xb400c8401c0700780c404030844c042c3c8000146d00c80300e244081c40c44d011380e11110b50001a00300310f1600b1900517407103101d9611084040100b05113000203009000104411321580117490b00d00f0601c2003651050091050b158102d4892580c0c5001a0b180b014000c643c3c6507000d49080e08442e10b42c1442d025402000b50300a060400a040341c07001035070081e0b01e508042c000341400744100034613005c6240003400788030060309240e90300141c0301040140501c07060a03013101310b9050841000004100009451900201707003080c18000c072442c00401e0742030050040034019907003002c400051542c5807840000c4d03c03071841200e04451080400c01680c0d1410305952407a0000318000004020a104000294100b00b20f426400a003288a082d41403e0740e610780e10000760f140c03c0d03407069480064803c507940c40f8440c6034001352058840760b0300ca074041c5500d030b880340303501491958480c03121180440b002070b0081c010070b90f0855142d0420000c005d0040009010300c3e052000b001001103404c5020300351031812a45d01503a1540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 726901061 1250 726899811 726899839
    0x6120203100e030906070f0c08120d090206090303030a05010f12050303011208091504060f080906070c11031e010501050103060e0a0902010309020d030f0305010b030714210f040b01050609 82
    0x1000b001c03641d1802c0218042804071000955402d00106107060003640d0003c94508541003250901600c2d80c080382c019404a0803e071103150410060703507626190b03904006509540c0d400460f105114070042c65606010000c10048145c220350310281c1603803803101144009a4654241301203121b0074030000b504580c410310041044400e0384a080880c50b2086215a041000980201e50a201a0b81e0410f14554011606000c4294810050002c84944d846c0003481030405a00050700e40034054039540c20003160681d900c0600c00b18868031243c40324003130221a5074201000540501402954a80f107a41d400d1000000b1198403900410054416507052580d0b1601c0d04c0700000c0003006610822414940c55820300805651a0360341c1075180340c080d44a0841d001602d4030024119101600001d1081c10706006021070a68007903484c0c4030b444c4645c10b03a21b0f03980700c2c0c2c80da04540c0400441c0407030040e41e01200800c5a8002e804d800d942c082d6101d00c060303820998840c003c21001d405042c5846400035810300c4541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 726902311 1250 726901061 726901093
    0xc030f150b090a0308030906160914060a02151504061d06220903030b01180e01061119050a02090907030f060f09060e0706020c09010515030711030a08060406120203 72
    0x10390b905000f0008500266030340d035115401d0300103c03080691504103c00704042c408440712181480320003440c1020045051144081c203000742c100c1b0940c000c80010501920707003402041a14032549658a14540500d0140f002c20180701c20b0400300c0e070060b82004000200541a45a1392201350041c0d0104055955404280022044982074850021a64400000e1404480d1107050409400fa58001c00d14040c21030015100b90004180044a440c014104011901003440300605642031854040d04c802d0955090381e00d04201c442c440c00381d0690700d9403c0003c01000142101c0c2061080d03c071030b00709a8450380c400b515180c41344000f030300b0743c5598070b440000500d01e81e121541414070050001000e020580b50601222852030003052a680401c1c401d000407901000803503400c5104854a44046d070504000c180000740076003a0241261001c00030540320360207142010108402e0b481100e07103804000d11700030700303049040c0c840728090380c500a80810804140f000710b13018a900900100007a0400c80542 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 726903561 1250 726902311 726902317
    0x22205120a05030406210609021305120c0909010209360906010308070303140708090606030c0d08030a1b03090309050a120b040c1d18060709030b060d060509010c030f150b 75
    0x1500070106c0940c00048a000303244a1400035085807080140c8036511260038644e007250300d40011348110001d1303c0c84220440005a1040c94210940d1110500e4503080e0f1018068040c9401c0140d04c50007104450b0180a001380c9a04a011950400300944846803404940d40c0c000a0b81c80c4401a0001001030011544030350003482400c1c800e01e0300180018861524203240d08064a001c800122440c0034080c20440400c201904500204c0241201e500140002150118100c0300285095800310000d60703030401c507900c110307140c2d034800200403060203401e64010b0040c0f4807800210040340e141c81c4041141c6c00d103841c44000b9038100111540c1071580c2a1200b68a10a00174400c4981e1120b200c40480e62031b1220902902042c0c920310324072003070301744041455070310007080c6240c507030720790060041041159002002c00d04036504412507084a4484001044000d42c0064001c1c1c01e91b41400184003200341e0540c41010035100c9aa41044034500320b68815003512405640030000b003161200c1800034040d48401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 726904811 1250 726903561 726903587
    0xf1e0f1a0412050a120c05070210050c0a02190902030916210204021c02040810050604020a2a020d080703020c0f1e010c05010606181e030f06022205120a05030406 71
    0x4017040443e103101c00700f000d403070700301010b0713000541c02140c0c040840c10200746c424880e03045418a5424454046912035603010004006031044198000301c1d201c10b0f0f480c8924801500020700195641d14003040309541d5050103540c603200001280340300180381003240d091103071541d40f6203e103c14458101c0d02000041e40048052480500e0030341c002a18000b554402000246003450140107296034401e0341d0030458100410b40f600407030041189090700c0d5481041c031060411081002c0000c1e44644066030100002000c0c029000782c0041125400e015140001e01a124401c0d401c032241e00b5084418042941c0002080e241c00410304c10b483c440301012700f5044c0e00c0c031010614020500c290341761504c0d4251295684508086142c2c4030421090a0a01c0324070307000742141e00d54a101e007036007003812201d6050305484082d0558035a107251a08001d9160100d6100328880c6140e810203030a8040c45500043c910311803184500f0700c1c0700b40c1c0004c480002c101901d001c1c2d0070102560815142240030780d225185040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 726906061 1250 726904811 726904817
    0x204050604150f0f06020309090402101b060506100f0e13090b1806070516020f220509010e01090c03200306010e0a061406070f1e0f1a0412050a 63
    0x1e40c5402c808018184600910409420300c10700d92a151140601c2c401c150080411900200484202c5803260050710b0b4000f41c1c1940d031070030756a082e04400c8a400325010b100e250000c0003000341d081407116a0300118042c04044034001219592413500b0348203049496a420003040100c10003681038031b000b280b0803481850204002ca000d80040d581c00c0148002102c4000c004a00d401840c40804410080b0359445112400c0c03076854072504c0c00600308100040701c0020310031044100b08521740c2d1103803210b0050700d00389001d040e00700001d00c2226801400b02100c807403600d0f41ca807810011b0f400c0340500640b025503030420074440e9441d0543e214040039443c031000c1e17445490442d501c00020b0780c800b049014020240103451b403150381040d07140e003003e03900250700c626543c00103200c840c2220355a142c201c550f081d80c404603000210040d0319003140030401c040b80400107444101042d400388095141c114401500c60b11000b00c0c0c3c084031705140804242c05981c083c0003e440104c07107021980c0110002c00ca10041c0382 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 726907311 1250 726906061 726906071
    0x31d060708100b04030506040b01090e030d050a0f0216030e0a0b0f030a0605190f1d0720030a050405040f0213060f0e190e060108010644041703010302030304030204050604 75
    0x80c022051a030141d170044517240d210a0412041c440844000e5000d00428a81403200f90510a015079403030040f000f03240b020565030f0000c81c00c0c0c03100d02d5009a060b401500c4041d52a02041034000400c401024000c0c0c1c0455a01d290321032207442c0c900300000640b8030501c405400d01c144400d01c00c00d1074200510741c48207070707643c2c134004107880d510309072641400e480306c0e50001e031482d041c00130200072044030742d1003021911261180c0d02c10044004c000b040c0c1c02007c40c034024032a95070100c42003204004c0d4070551555030000281c14460b0316401401481501e500b60b8080c07104d5030744076030400c0485c4180020760508852a00c02409440e102d25429075a00f540780c500a00780b600000c00081007840d803400d01d02d28403035101c58200051102e00e00340c2c0380e04c00000d01f001c0c512585460000b03042441e40c40105008140800b00c03a800701d605000d900c046060540c410214005145409202d240703038291015240e810000407640401481c0310100c1c2e05076a8007030041c50520b40fa41e801d01016120181005174465101d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 726908561 1250 726907311 726907319
    0x1b090c0702010c0614160f120c031805161403030d11040e01120209010b07111002070902040b1206120d1d0402030405010605100201020423010c17040501031d06070810 73
    0x41d000e9906803080304222500b00e030031b084505011012003860390b581400f42502e880c10302c003508169030300c0e80100c800001045020302404201c005003003e40181103003804c480320960030b004c4000b6400070400c07610341c40c1414032500d0703003070055501103c007007115455407040150904038072540d0003c0310000ca03801020b905040e20394501801d540005d801c2034806403100234450003949051080c413401030400e41c0c429440c04107103803584c0d80070940d4000c02718020001d19040d81c842d244204000c03001005403a40071034883d41c03501070151b0b0552084036941400042000420303014604030091070214810503000740b24400640c40c081c1c0d11040e4001440e480348104a242222a840c6c600045104900c10400080c02d2802c101c02c11031110241004501168030510042c4942a0000c08095480d100c03e41c1c21402080d02000484816900b034034020011550390902904c00301071540504140c6909072414403c0600c1812882c0e41c5071030340c01d118180340d4803c0020905960080d8943c030b411481d15241c81048980b9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 726909811 1250 726908561 726908573
    0xd02070f14070f0f120c180e1203040305070609021c050304150207182705010507120501080a08030411100c0b0f07090b1c0c020d12050c0a050a180b0306031b090c0702010c 75
    0x55103c2002c7c1107521400d0310301034020207000900c1c0422502103414250301342614010801e004402d0000c203156694000c00b0309564800e11507160440c865038401800c9105441d000d6180d80003807040301201c003480d0b058043d1712400400c030541a200d60403441c510320115514090003074003000c6040401100d107800d845052808800250903018011000440c4034144044003c0005048580c0344100520301070052004075000300d00712441c42e07042140c840d102d49490501c1c400210480304010b61202d102c1c1004586030343c1006090f1642070058102c00b403d559010759074801803e0444420001400f4948c0900019602801400341641d200d00944c14071205a10110700300c1c0d400460701d0000d40d020010402540f540312040383e0f10307485102c17010f004906103d42c5017030850003514140c1c81031103c080340f0409070030300c6000d0800300c91002c1c01090890075030365040740030254401e0310483d0207801015506001c00782d803040602c10062010308041034135030f03130120210125000744008904104142e04402c000c950 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 726911061 1250 726909811 726909839
    0x3131407061706010f05450901060f0f0c0f020307030606080d09031101030b060d02120708071718010f020c0706020106080d05040b0d02070f14070f0f120c 68
    0x16250b10345000255910120110b1000010070550421404410120485600c003080c0e500c480284508510400700b07112a440041044000342c0c503140c020039141248207102d0704039a07500150140d800115503604c03401c044030100103500d2100080b80c05c494100c0ba8540c071449014081500422420f41f115180c1d0f80000c2c240941588141c920b26141ca0b8180500c0304203010349400c1c02c0d01030504c0c00c0c00900d15035075405122880c1c0d50980c14541c0c0da100a60507601c9030021142c41d29020802159542e44821019944210a81d0031100080b910780029502c80d015220b071201340b4000d01d07105101541c540d04003c000105018842d1031554a60b11040000034550014092203090300780581611810000000e00b100c04a9102d42e010ba0b0082070f892001540010032035003035907000503d82c0e07500e68034100000064030900d04000e0010403811050005c0c01556410450404003020955403000c0da2440301c2c15450025001c1e080c1601d081c1c0e1000c0201c0400368036080c070124031030000914416610445441100303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 726912311 1250 726911061 726911069
    0x140f040f1d0708070513021b0f101404080d0518010914060a02120f0a020f0f07020a0801110a0c060e06010807031505010e0403030e0106080d0903060506090c03131407 73
    0x1408081c540034901000e00111000d0000f0b00000c0801600c2c103000107030498908000124110380c000744010b041101030101e81070080422003100c50501c1d6051502d90b40d00c00c08152941c00e14030f05000f0f01044001c15200e64001d0740c11140180c20481ea15191100030b10001d401c1000f201071230746506030021400c0c054404128054401074070086031810b8800c0c20090000d000e003619601c1000041d4500814500040c1c0122107183c1d40f032029503411566200900c240c0d00c4150703a41c4004100280610f031400000c00c141442907400c0003125030788000322401d0f83c8504200d65201c0005000800a036071044100c2c2c0d41160080328082030303034132441200382d0820200382c201c05c8154100017400c1c014050661305e40550180c2d004400c1090307600d0890600514100034000a00301600d03150345030a140c400f50008000382801d501035450410314400060140c02903407004880b06820100082e01b1071500c0c8050728480c1e081400c0043c03955036088000a0b40d0031044404a400607008021444201c0080110310098 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 726913561 1250 726912311 726912341
    0x40b040906110c0105010905040b01360f0f0608070519050406060507201026010e06030c040e030915130902090a09090507030b1503010e160b04140f040f 67
    0xe100341c8504642540c074142c0249040d1810310301848004ac065644803130441e4085058004480b5203905400043c0b0007413001c00c654417007100e0101c40d034081194020030340543c014104211428061014800ba2007461060709071a80011008001904001404000c05009070034000700c03858072080010116105034003e00300045c0041500c004101d4086a03444900160501d800c0001b901c61000030241e80c000c2c540c1a00300b008640441c21601c48031100004116042c180642184d038440c50218070070345040f1178440c0300303116070305203100207080c07500c12910f8140c442d5019602d400800000d2150f0b005200001e026074000400c0042c40d0741c8202080d40c1c000d0040000302681d1100d200040102d0301303020380c00626006180c0b02d1003030300007040041e442d002c803548500028156076902007025007109601481981550804804221410000c1042517658418100600800e0b4503950300f60101e0080d8040d01101d00030840d00311005180210120715038401c000c0c004580441b05001075003e5580d40001030b156 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 726914811 1250 726913561 726913567
    0xf0e070302010206060105040e060d1104020328150915050a080705090c0a0e040914160914010b0f340c05010f020a0b1806070203030403140315040b04090611 69
    0x215070f4140049a001982460007030b044c07030b04104c88a0300f82d00020340150f1044021001c0c050401c02040400865860014021522440c000000c1094800104614100060384001c01200c82c070702403084208014070500e051100ca82000440390080c00304502d140b40d800525080050590b13500e50201d40504880000303403001c0c518000c00e02440403405041c3c40341d07082090001490265109032040c0302c07e07004a40111b0168451304090000c02c4030314440c10507074010700107614400038000c19100200d1f034801c5000c2044803010340d80e004080d00d0038003800d40c207250204843c0c48400351400280c40012468540f41091210214074090150020800e14603036100307200c014030612030546401d000400080c286203080c8205144c0094440040c03000c010000201d000100e0400707005002d1402c00c846a41d01114010708100300c0c0603549420449003100000c0b0700d50140a0f142c11050b050700e0040121201c0316040015440402001d045030309510b5030020340c0c500300c030000301d030aa0040c0c03021011003022281c0e07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 726916061 1250 726914811 726914813
    0xb0c1b0307091e0e03120c071104020301080f15091510091d010f051012050f0613120f0e121504060b040c090308030103110a0306110a031427010f0e0703 67
    0x8240e40c0804607220703294009010968148070b020746041c4d80440f007c000b059603420b19142038181c2c40d20f005285074020f4070100010807400000030b402c0445e0440402110040b0417940546011481d00b140c41d6500c5800c40d40140410350f0059407281d4010403446543c10790b0540310050301c1e088468602d20302040e03a00700c0c1c18038881c3c0c1700c1c28401d030710700c01e509064140410319080002140d03140280c45420f025200ba0480b40007800014401500c452909500b13030344050508050503607a402c10b550090301c261209c00054100c1d640144001076001070036403241d400c1c00002078200010007001034541556070007920000c214030762858503110b04c81c600c10040019003200d15014041110f120706219014404e400380140045503000741602e04503907100007152900140103001c1900258583d00080c140da0034191034418074035480010303080401496074200000414880b0f40704c000402030342c81d20003c6803520b0f80c400c09400341d0010424017400490000c40c120b10700200400444401d900c1d038240c160040709041c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 726917311 1250 726916061 726916121
    0x2031902190905180c0306030c031504030e030703030f050a091212110d0206041b0b0d0e06061807180807080303010e2503050603010902060d020706060b0c1b030709 72
    0x1c4003520090303e00340b102c20062000c3d01c5130204060f0030104802004000980d943d5401c106d00c07c40084080c00b980c00c0d17410102c909284107407003a28100d000c01c1a01d4400303000e500780058940105c0ea019603e244554114003c195490341c01a44000e04204040c0c902060202e100c02c03500c440c10744100d0742418074030304800c0b004051100b04501144103400c506211700d007441d400600140c10582040020304405000302d40941901c0240c0c2c050b42c05032201080c0c0800d002c075903078852050b8140c0d034015a13440c1c0d5075140401100050304440e020b1120345201c0402c07080c81c404c44540384440410ba030039890058139081e4442c905943c0d0782c855001ca40c000401801044800d4000700c1d0050f1200040f0303240e10701200107401d03070302d400e01d044607042644c0d840025200b076400750011070a25801403c000e90b60154981860060b41c028403060b602c040c10480300140c14404002250800b02d03005015092a22486140c0c0703a410718560300c6154540310705c801c0404ca107040c600c03038035042c100405604442032401d902c940c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 726918561 1250 726917311 726917327
    0x809060a02090307050f0604080d09031509150b031002030a2a0237060605010f08060a05310509120405240c010905060108070e10090203190219 63
    0x4250300c0da006102d4080c141d107000951405688049814454032030442c00403a03c28040d0340e000041c0c03031146180c0c500d480c80c0c110b05481c0950f8046e240040035070f910880c0708419240610801001a82c00c24080c101c10b80d00c941c842e003a03054004050720041025203070070006903081901c7e03188001d950741d1640c408445011070388013a8055000e000c170121407006440652100c0c0c1070922441c0319071000305000300103c040411064a00700e1450540ad1095081c1440002022140203003070100d0850303c0700c040554021308820b031081000601442d0280d092106104e9141a040c01c0f051244401188044018142c0035650401d0112800000b415103040c01d0150728110b1403107130310240100100400d20154582d150507060b0071410850400d440001c40092502da8414500b01b620154a4403882c0d208000000c16120304940fa1103003102e080584644050611b0b035825138203c841e010400c6000c1084083c0b070f8016560001845111300e00022140c1c203140c0907030740020101004d03030080207005101d51760400f0b40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 726919811 1250 726918561 726918571
    0x1509071101092a0302060403020f0d0b04050d1d030a0210030e03120a05010b040806221505040507080f15070c140607080f0c16111203030105040507110703030507030309060c080906 79
    0x340c90310f0743d145801184440c466030002070301610000c980d4259648510134090312199225150241c4c614060625540f01c4540154410014000b07100c01e000c0c0c0018603000004542c1d005024091907003550307080141d250982ea80c1441410b0310b80c3d42203010441c003400600040010b0414000141c41c0c40407012084179016081000e5020b0284028843c0702c1c000162250b02c8118808034a030f031040c1d441d08200b40180e80c100d00030301081140e07001c0d0400c0e80603a040b2901a42c42102110441900e030341019803540d54904200346503034000c1c080d040b072810300d80503100e4000141d400c251940c000d158441a14003450450114500e074001c606002c0c180e42e011150780e42c071010b400e20404442c1000408034071184200841107454405c1d010000c001e0103221035010040f040010100b0648008000746d40e91280c10910403113105130b24040001e00180e0140c0011030003000b4004c0580341542c110b40d001c0c4d419401000040d41050741e2568004d00140d0903115404c0000d51984402c1860300c0c00041a620382400104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 726921061 1250 726919811 726919883
    0x18020417060f0a18080d1514010e0409061b050c060108031312031709010903170103050a1b120804050301200d0b040e011d070608150907110109 63
    0x810004640005a000b94101607180d801080440c0401d000c602c07000784004003d0020b0800181c042030b050a01c1c0d000c884071038070a01106442d00d50320702d0703000085000070512a0209880c140842c03c0c9240c80d601030008103125507000608468598260712400c05450361840100c3e800203240045500100840313401000440c0085103084090304550007488210702c684046040056a00d50030540a00d004c07040301c11801c4400f00c141d1801c5543c50740600314161041e00850905105031408820307181ca03190503241c00200600080015607603016107510200c0200381200013142d0041454412200380314002409508400e07100c6040c00105402c44503852003a09004600c2888080110107550a8072601d08001d0000604400382c8808900074001420700351215501e045018401003100c032003085c0c2103800c4001141d101540f0703031805a079102030580341e14400c4500656500e074140740012981d64040b100385802003119600c110002e0a50b00a04c00440e5084840c1d41070b004100043d143c0c0105c1441509 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 726922311 1250 726921061 726921073
    0x1091e03120b010c060f02121906050603040b0411011b06150503010209150a0210050a060603140c0d05070c12080106020d0302120402060702040204050315060306240f03010618020417 80
    0x40013815400d14030100415060700c1d488180031501070350341500c036014540440d5903d030b803a040c040f0401c1c11007080f4941440518000e800300d8203060245c1a00c2c8200e50200032041c0303548070340e160715480402482409041240782040ca4011480e01c81410207034a01c15400418440d40c40700c3c80640000498000c0760082e8030500803071849030b640010643c0400141560690340d440104012828080d000010400c89401c2c4810b1001c0c0c4d06269010100f15101b0755003c1140c0c044540c0c101c03400c00c4058680e420860b03c184612a002d413500d511594210206050039199000c2c96500c0030000442002d901c0302041450004200d860340611480d03001d846149000c42c40c2032111550b01d0f020307800c044d2000e4010400400c445046456035030445015040c020102c8915404180b805c01b402641200c1c00742c0203000305004515000c007103224034607100e915000c2e0520b428002c4401d04c07056105817210310354550340b9107030001041c40d0541c0451040c883d0015015030f4480c2070041039880d9403070101c09850316520003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 726923561 1250 726922311 726922331
    0x180209010210140402042004180c03141602030412060e06011415030a0b041b020d0e06070b0403030b0a12020a0b130510090504050f0132040b0301091e0312 68
    0x140f1605507110340d04503400100d403100c6103503108285da0380c60061a001c07800090040344010f10b469145015101e11182409004103440c012819500b40422060f0001503000100701a00800c52003c13110800c1c1748101da08180e51445c2d94050005207140940b00305668105046ca482010301036903000d00909d02e024040c0910741d0000c51f0401e5a482440070b09540040007080214145d904000c001c078000500501031691b4001000d00a842403401400152055080c0035500c180120718800c4c0780c0c00000c1c1884c5c10006c4a44406104041c0240100d04056072421201481d80e21144004041d010101140c0701c401d9641c81807200b4042180c21112821400740060149080030b040c048050344c4c026034014000351845401039401da01c454001c258010300344400c015156842c422400d041312600300c494200401c01c00d0005003c00682800d070403030f504001e01c4010040c10300307030080012010050000594048140c4036842007101c00c1901e401c01e80020229001032590010030480840c1403250200000710f00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 726924811 1250 726923561 726923591
    0x105090105041509051603210e030706030207020414090106080106091416050c0a080a080703020c060c1c0908190216030312060b220b0711060310180209010210 70
    0x112403c00041c0c50316014500704220084c490b030000d0070b045010000d509522851b042600072a44142d0700940c80c504030106174039612400c2d01c40b581b80c030702070042c141382402c201e0118041e522444090380c1082d05c0f84120b0404200e421009403040020b00e000003120790624070002c2c203643c880d502c0b607402c050424004d03c0b914408840c40340c1d0450f02e2102c0c401700c05c40c20a0002c0da07040c00b4000310300c0d04600882081c00240302c041e00c02461200426075900340d05949441e0294128000c20110032045e601c0900000d8130340c40428010900c20440b840001108021000d19006644112001711000c03640030a402c410b0301c003000340c180b13514149800a003d0070011b400c20b0710554045403001078100401c080c40e070305845915501c0400940010224550396a07d10341e0039031103000200180301454048014000b400a03140020b90b42059442600011006d90721000c008103078202810101d00403000728800544022410f900e07000a4000d80c00142c0c40320205400a42030038241c603145076246040860b500c1c81e1480c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 726926061 1250 726924811 726924833
    0x305370f0e060f030f0703060302031f1508030d0b0a150207030c12150b0414040f0b011e1406040902071b0f05010f050a0e2824050f090405070c05010509010504 70
    0x170789100c0100704ea60300032045015108551005c3d41601420003a000c509250030058203c40055403414800107000d180c001e28400d0f618428040182c0050050401808482d0040341400c0c800a0290003003503107680140106511269441000da0300507602081000f036994002c10080211001810303a01c00184c43d03000311070b9010414002c47c03a40d92641d04002e41e0752a40b00118004908070015404e20703281c0780003524040500800c3c0c4010040781e00000b604c00a02c0740d0b070368003901c004155071811842c2c0641c0500611001c2d021650029050001003000c24462001c1d050160140000205900c3e00e4140700da90103601d0f4015482120341140d09000302d0b40c002000440040c0186132407983d03100c000000b1200401c64402e070640c0316041401001600c940c140c1740c03550645406400d0540d540d510b2517030644425201a16039030008103d401408030078090380140c607810005201c0140750580750b100003400c84604813144008500c40700d0100e018040b0904c40d03130b80e222481078020071450030076031221300f4808 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 726927311 1250 726926061 726926071
    0x120b06042601020f091c0f0f15050c1e0408010c0e09010f0803070818040501090b130212040b10080105190615090e150402041202011b0305370f0e060f03 67
    0x1d040c11003512403540d130401c6c0c1303821074100881d40c1c139070b254a03e409141c0280f060005e4440a051340d820311184819880340c2c42c05450301c000a0340c038201100c1601101d2000580c02850820824000002c0c02a028004c51186801a0b0384070044218480c081040390342c0180c01036042e07207171008410301c41a030000007240c0c0740700e800680803503c3e030004000680c0310208141c2c10507005420b000c00090030a180b500030600031042196215420901260008224000d1081114002c0103040c0030501080240a002c0d0b00800340c1e0015024940d01c0d0b4812030f0a46000b558080c14290100760712100002d481d2144001904110000d41514108994020208603460007411011003003907010894a039a51806005012409001035443e00e96030141707900070050100d4168046000c1c84128a41070040142001d11540d05464031400e03c454942c1c6180c9a1300c14000943c020508240d1918503845145407040402c80c9550300c01c1003203440c001000303140f0070503034520601030b45082c014040780e041000c05880e444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 726928561 1250 726927311 726927319
    0x609060103050f12040317090303160b0c1e03060303090901030f02031e060a1109030d02060a0f18030807090f1e09051501050711040903091706010e07120b06042601020f09 75
    0x1103050010410088c2c420320250035454400000c0c92401404440d5041310080d000e050b0a410b595a2083d1030a00c0e44142103010440d0b800746904a42582c40c150041e542001001e8110303814590f40c40c002c2180c1002c04c5e0010f85070100d42d45442070440c6810440c0f55030b009581c140741050b4030f10502d012543d4040103410f030120741e0384805460403622a0030066600401d8001c00300d580c600c0404102079114a0705954a407a01c60038200119880315950045e400644801d40300700c56564240c1c0c404503030781d000c040c0c80e11082041d4400c0c00514090000700100c0039200c4052140101031700140210300c1c000c2a030b030100c0700d40d03810700003041035005620140c00ea00390b4082c20f02603601d444501d400e10200144103502030344503140003107003400e040d8442031078002e88683e4644a551861509190381da100800d108045426822000181905100381582c55140c2c800200c003196042544c40002c43c40c6c1c0098018681600380110748180c0300740d07264032aa0780c03014500c0086140c02c071505100c6419209000c0c126000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 726929811 1250 726928561 726928583
    0x90c040b0a150c05011a04050c6303010506031b0a08030a0519022e0e1e01064a0103111206240102030c0609060103050f120403 56
    0x2400d806204990302a0f0b40c803400030400094480c1a10031806c40c41e440c1c00740183c0c81d0400086401c0c2860003158491481d602c8520301c1e01007035103101d0300d03100b04840b07031105416411851906020205462042c0c1e42d5610070510a03e40c05024100c44454002c00c510761280c0c2c10070041c0599600c2c0450f1003500e00c200189080303140807034040031503542074450703019046502c40001c5400005610202070030030f4905045010001c90807020080782d49408001c0c004a050400c09030079482c100602d110066100420180400d00100e004202070810f0808881c6081c0c01c480d221842c030602c0420711420000c0c1100a00c526a60b118200048803c0f42065443c400340c80c84101d1001c1110512041c1b4a00300078050400c00c2c25983c4a10f00b800001c41041c000b5806960903200b06120b800c0003050304e034030800086005403121107460100d001c90000c0e442007241036020070820070031000d00c00c1c40f11f14400c00c40c00b00105a65451752070890301d0701405a50305c12464104038001d1050481090469088a40101d0710f116 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 726931061 1250 726929811 726929849
    0xd0303020906120108060105010f230a031b0c030e0a03051207020a080a08210108101512060506090a0209031515060703030903080108030405010e09040c05060301030803090c040b0a 79
    0x14140724400e00503071503600320f100002d0501c40000e4914181c034001e070f075250b210200c18041559076110080b510403501d01038400e40d071030406400c400392005200c0b6280c04141c0d500c07006101001034103028109030000301c062034190141a0000000c0403804400c0d1480780c9214038586134107480750b81a45202c0843c0030001015001d550f00d04441102074008507040d509081360a1500a5441d800798202004106008654458180307081d82064122480300000c0c04465140402c00401400f254811403d90780032144089030703d0352141c805160440c800c440009081c200342c401c1144040c0000c20341c84100313004010580090710017162444080c201036001141c6619034100300e6405139000100c0e140c0020001ca52041071682c10342040340d90030300030b850f011401d07625840c0c0d650b1688078600960b0b020400302d070000102d40c02c250b96002e0707001e4000e5160391032240e00c900c002809540280d1003a0385141c404030030b2101c801c400f4402420b14410880f420080c025101c2c3c003103500c045a51044e00090464012041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 726932311 1250 726931061 726931069
    0x4150207061b172116020313050f011107180e0d05120a020405100f0e01020609120f090a08010c18030b0123040c02071e1d09070f030825020d03030209 66
    0x4014003044060311500d50101364180140d004111461005004200031161078940088121a6410411402c0002a50811090240c500c0640002a04215034110702d02c207200c0d418440c403000f0b0300d0355070300302c104801c544440e82d0f0aa5480304446406e130b400c4890100300c0260070401b11829822200c100707140941d164640b960003405182d21a68008210311400e00c00c156101e45101030002e85605d408040419107001280e0300d807400c4802e054a64003584804861014032130182004201d0b01c03c440d490405480c0106440903442d511411440c0e4584407450b20075078001881c0e041800d10305800084070351854030b8013030704200184644440100460013800812200043e501c401d440d0150080c0010140010025034402e52072141003078213214034000c4240714a01180000c210b6403c1c1e60101c0f5401000e032403040e40250082c2500183d88541361f00083c140e0030b05501c40300114050b11245880e20384001052524601c0700711202a072020b81d0003000d0041e074520606c0246140c0515005859a00c250080b17 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 726933561 1250 726932311 726932317
    0x20301050711070e0907090c090816091109090606030c0d0908090907080f0606160206120a0501060509031e1f0e070b04030210030b1c110a05090405061302011404150207061b17 77
    0x541d0050003162114bc00c2c1052003403000045815090040150180a2180c56800d02441c2c01080d880340d0008081260703490250b015503000b4030200849071500b4683c1080038201c4800040488c1c00860100d0340100b03030320340724051341d034803481509068909103070541c00742180200042042e40304007408220442c0061a10f2550000c0b66406040a6550011146452030311b44c403c44000300640e0500c0000305406110714251000914060b00910303040c0040c21841a100e6040d40e00c0c00820b02c01c500e0507071600514441200c21000c201040040c0c9078001408140c1010200d81186220160402c82080180c44241500c01c501003e89000500c0a031103400043c241e4804504517a00602d0501041050000340700c03c82c028618122195502c4e00e40e18400d0080440085501400c540c01090000d000aa01080c50102092051400303e46900441410694940240c0c104101d001c20701c50480e8031180e0104904009041107040c028103055034044240750250740248000c1042014643e0600c80f10049010307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 726934811 1250 726933561 726933569
    0x5180f161806020303090d0201060f1a07020d1506060c0201122c0d0806091003021003020f0d1a0f06031906030212030a320a0c020301050711070e0907090c09 69
    0x401074000360b031001d00a65a401c02e40d8005a140200300082c86114014070540c01103c5550411010040ca005070180c102c03041d65400c160030781c50030000319005a03a060039101016118007150301c2c4016100c036645080300c003140c101c038081c491981d03281c40160f038020000c4a010600c1a9012a14020b440c6000c60000b450140300002000d40d00007101c010b800c00b04413880304141641c0d809009954580c10402c80d0641500d510500540c6001c062026003440c0040000c03075580c50030050329044101d00010b0140c1c0c0126507410685a03505040030900e9482911344c14080d1044401107039040514000802d20b1201412002c0703580b92009180c001c8100e507412410080d41c0003030440000708103c4a14584980c0142c000a001610094a150301c403902c00100c40445d4942ca08044503003140c2c181400910340c0700d07400001c01e000c8691703400001a54240512403041180f5560150600da0350402071340340c214035411206103600f02c141001010403000441404503800e005000c60550700b014820b4070181c3d02600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 726936061 1250 726934811 726934847
    0x5060702030a020d21151805010e07080403020d1d2d10050702091506430f030c050f061b04050d0308070e0301020406080105180f16 58
    0x40068003600400a0101d02c50140c01355000c011516104550020018503030300b990a0100045110045090303001e140143d40115011442d65207078000e4003400c00d002001c40030b040e43c43c0c030014050301c1d10003c0e0294102150341000411803c1030303900a929607041e030411104100f804181c0001c94207081d5420303c0c903001301400711b104c40b82c2c08a000140200c41d88a00307400c10700d5195555030103428200b0748001c11400f595121800d00d41c8582c2046003050016007244154005e0b540c6046e000d658100050010350b0411a292807182c008041010303841a00c041c0d50b40c242880e01020a440200d43e82c1000502607025105001740700ca245020340700010a8030028000744a9040030480c507800c0003d4441c0030340414039051003c03110001801a007407007035000e03803904442c40c5041031000034050343c0c400347c00000f18103260300c2c0c0007204408030782203030070551121000505a000400c05800c285003d0b1030100700c1005240c0d103c0c9411541e2512104010300743c8445203031010301090400b8400c0203e0700b80140c1d0300c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 726937311 1250 726936061 726936073
    0x105031902040f0c0e120f07120809060d0c020d020106061b260406020c0904080f09040e1014060d020a03033024030b06010c02030a0b0f040b010b040305150a020705 72
    0x136401040c410544000502031840c100603480c40d1203000922443e1720300030100a003626810308203185e81c80741c41402c04568116060085c803806540700f002910200040c400e00050b04214210000c2c5040d007004038200940e4903149050248a901c0407010195200000311a048000ca6203009811500e898581290000c80409100a002402d900400840d2215400c480c0d040b03082400704404d4005c2514000d000301c2c0b0803c400010141d40402401c180400244005051b5807910090390411080f540050010f0f5965420715401410052500784c022105541928602c40390b070340400da0b006c510340000350911200f40c00304208901051500e45000b011528a549101010990354014081319043e041d50a81e84514021001007100b00200c00c407078101c48050119280c0100660b0366040842090ba05030180446500101d600145443e0082e580d050f0203040d2450031b41082c1000d0311040e0080c613000034040208001143c4006a034181a60720311000f01e1042d2500340e07081000303215130700380280180618 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 726938561 1250 726937311 726937331
    0xe0f0109091a030d02060106021e2b18051302090d17030106030e0a1a1806090607091a070b100e0a24060206010b07050a050304081f050105031902040f 66
    0x4042e00711407109804850000030022000d07a01d80c0001d021b1140180e00c10a0340c0f003a01079000c1c140c032038003080e00b00540b48038807001e042c070401000c031490340b02d164403412035090302c4000e81c070812200c100c0b465400751804460500000a070540003145600001c2900825841590b41c2c8040480396241ea0203441d0120012000b84034030070a80007481200c000c43c2c6002d01751540e0340004604d0101250340001500586402c004148200b10710251030b0000c2e911110040c0f00620301c0811840d0700400c81600181070b02c1c40c19910091141c049a005a09101941c0785001018000c0c2002e944440790f100910107195030302c490551036903103101c0d440200d103035030707803506200700441d80340d0000d001c3d1284000220784265070b01a114511781e481c0e10800005a0084004000c08510600903001355413080040e59805001c13512294a1034003d03401c00500344d000b00f130503540c000403000042441010101410b120540c940070000b0340303601c0311103840c19820614041100455446034458950701301a08010047e40d100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 726939811 1250 726938561 726938591
    0x408030310030507050402070803191d010b090115020307030e0d332f1909080c010c080a0507031403010b220302030a080a2a020316060e0f010909 64
    0x1e20b1000b40d401c0d015514010455080070b0080b40c5d4182c1e0010b02d0a8950380b00c0f544c01c410b10080c18645652419a101c4641458180080b14444a96500800410001034400420940b00f2069000020035121001c1e03050445030084156402c140d098103002600d00081e0020414008002100903c00c42c4a44400410408000d2020a4050204030303080c0ca100120507008044807240e07001c40c80076054481c004010a00c4c0e8a0040403285a0441103a00340380754880180c0c4100d1000351f401c804a02803e10078040030702c080084440d2003600f4a44038060900c1501c4180c0341c2d100b440013400400c9070001e41c1909240c0145c0ea103010802540c89116500d40e0b4501c0321001c183c02080c4030002c0f81c40c04481002181c400381240f8829240c0040182c424141165511400d5a001c5c0c0c941b04c05101135002002e010121450405541c2d604020040780031100c181304240c1041e0341c000316554135902d056010300c091030b0b1000d0061405a000d461140d0300015a00060362286459446114203600302240d0611183c0c2e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 726941061 1250 726939811 726939841
    0x1003020612180a051207050c0402030108010203040314030c37050d0e0a020603062206030c1508070c0209071101020c070501112a060d0507031d01060308090904030504080303 76
    0x340c80c6000315841000e49400d0b0f84a05038860050f02a45c4420800540404240010100300744180c0031035090003080c9002c50181d8009078030400c51070358040104414190410b0041d00316050300000e0f68614a04118006401e020716142000007101c40b00c846100400b00440c60411503262046032400321183d820300620940c01810100556814203950118034000081c01411b0164010442419507458100303001541c00488440102e100740c0546104980d001441540051030243c0088010141010390380103003c01c3c00001c141c1001104800c1190490340b101301d10340c48a9048a882c00740e6103d01c002203a01e41c0c4003181e40c000f207520000c9e13182c40602001405404598007a22640702d98201c0d000d0700c0e9210400032244068011620f20403031118010040081d0380110010007803401c207a9031290703c81c100c2d10700320f688601095540da420b202024407002c0300300342212400300901941d801c554401c4403078001c8181c0103005a465102060400d401001598040c040c80c05c2265100e261654410340070361 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 726942311 1250 726941061 726941071
    0x314040f02011b20010e0d12090b18150c070905061201020a02030f03190e030a03051f060e030f0a030f0807021621050d050d18050c0105031003020612 66
    0x8040e100303151a05030703400002c0c40392103410040c110740c010044e0440103030003000c40180a042008000c640c840987d154140e080480303000307000460501031405809007420a10303820001f60700d0014003895003000c03480481a817100d40e05842d00750541020341030004850081c040e0104031800381080110303c1002d07030342c0f00b03500c900c804980040145810a292600301e100e00620800160801c21602c3c200e0b1011038001d542090039401000c40c0f0380d024500f04402c885a221040d102504001076000080754035000d055048421a1840300e4410740c010711901a0206510400302400000380f1851007c2da810320208444800e80c1c0290750120100e850f00030020140141001d0108007070341e01044180c0e00c001100760b44003c0c03c888008201e07003820030100c03071a140901400800308600f100c1400040050000044250b507503207850f5190110103402c1d2003981c001d100e050345411414004030300802c030005202c11601c002800c16503540d403501c43c42421641c020340c002942280000811825810311a45031910407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 726943561 1250 726942311 726942317
    0xc0a0c0b0c0c040b03030406080405030706050c03011404110306010c03050c19051006080a031b0507060f1b080304260403030c060b01020a03170c130803070606060203041a03070314040f0201 83
    0x2440c52030100300854041c070320016010b038011f0000303118541c0144582c540150054003142d04000d007039515102602e004840c5002c90031008001000901040321115144010071101480b0064070000c900c84140001002541000b080d420800249405441110241e51708407054664110054440c2c1200d0b07100940c0c21a243e1060006500c003012280c41644c0984803801c001d00bc40800320703201160b46070044401d4031184501c010007480061400c07c00d8034000d00c125203454922401a5001401040c0b028292441000302140c0c1c4030300041c004001c40358007036403001944c4802c1850080312007000061242c00c900319980000e01206140e0050303072000001707204a0040c440d214202004a8442c000b0b6040240490141002c94103d00140101c232984a410700d5401410040300b18128420910b056000107502c5d04009224010703c421800740c030029040c1800103519117840c1013914004103a5960341d40b20b0140e0080041860a8440c3c2c0000e0281003c0f101000060b08050410ba90305144a100403804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 726944811 1250 726943561 726943573
    0x711011508070b070c03022202030a05101505120a11040308120c0c15061201061202040c0e24090a0e0901270b040203010b0a030b18071203050c0a0c0b0c 67
    0x140300f5108031010550300402c1c5070541c170300e5070b0300344102c50610b4880c02080e070f42901e00388500c3d6082480650700c94084008041124100ba09400c10718002c16080030700d818a076110886417480e0490704480a10900b0240c002055a842816500501146d081ca03c41903900190000c240403140c00500042140e0101d04039290311640d0801c203961149680c50204e44e0018165004a00e24252140d5030006001d03100d1084045003044440c00c551003500b0021084004180c0070040d03040c21310aa6000049900384203800300005000640f03445103004600d51001d1100504000c01100310098500110340606000c0580f07481d00040e10848404803103181d000e41c60b12042040b01190720b20307a541c0328000070100d400703a800f142e200e03840303a46001082030b60159264013030070303406880b051503000055000ea201c3c030280e418401e2003110144055914080141c1c041d0030180252b0800380741810143d90300d8109143c1e504001c010a0f820314404407000703040150b180c80d000a46440700801451160403440075191 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 726946061 1250 726944811 726944819
    0x12070905060414010804260c240402100207090c090302030c100e060f07120c030f0806090a050910060803040504230423010203042001110a0605071101150807 69
    0x9690240c1e03c28032803015401210004a540500d01954216004065041c8040d100c16001078684441e50349180117200f00090b404050300e014886203c05c0321131440d10400000c00010381d50188040503002900c01c0301c8600002030038a008009901c01072921705014041000d000350003801e418028841a030090003100130200c01440c01c81c0381c036580320442d034980900f00c141e036409000a68002124400c41407508000407408294100800801043d082c0d0700c0c010a111540707801840c4901c10b194034400d10810304240080e41e40c81d00c0000b540542c6003040040d40c1d80e5803c000624180d02d41c00c20000711407400e140441c0110000c4004d1050302e0040e2800e05ca004240044107020f100c09034055100080c82001043c00a219008000440858030740301e019400005a01d00f801c85e4002e40d412144c1060300c0c00c040c6a04200e8020307442e03044d007003401e0010782c0c0c0100e880d4454840c00500702c005e003119620000280f006000c1c0b200d02100351201002040401c40003040544040001e001c2c8140700d21640200003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 726947311 1250 726946061 726946069
    0x180e0a180b091c051912021201080610080604080a0c06021b0c010f140904020702012304080618030a0f031d0708060a0506010512062b020103050a0e030703080405070b12070905 77
    0x12610011001718000c01c00d18400100c1d007032824081e4222855408129807040c3d003010b2511a070181030705202909a0313061220003041ea41d0007076070000f1190307000f240401001ca8080f405a0b1100c9865081c145140070741454418028850800880206040ca8021600e0120f00042002c8500d00c283c031104119000100d0a850103900070007800f04003481004400c980e0305050300a885400e1040c144224041c1c1201c9150400c5403601c12600d0700c5000100f020007150004000a03900115090000b29001e0b13201c442580d101e21036102803000f800160081d09101c2403099000000c40c4005a6400ca4045040c8907156250340325482100b00c5841900702240a070581c82c494180201e00513190b5501d841e040e811552101c2100a001c0c030b500c80100040101a00c0205ca14000e016428160003000400c4510001d011203c0180090001c0c17442c1c0f40b240c1c001010300008a80c1d42542604010205548070700e4010710340744e40f40d041200c2210700411007054400142c104d10307000e401c0380e489503001c0c19240c030b0900c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 726948561 1250 726947311 726947317
    0x2120a05090a1e0501020a0804170901050405010305060f041a03061f120501060e0408070201021605092403011803020706020d080703182001180e0a180b091c05 70
    0x4400c198004048900c00aa11000c4445040f8001c841e91490454240c98050032600140c3c2e9002c08a100681000100603100010300d56a03410303030f401c0700c0c180203400c40001d041d17010702d004070f83c117050390380010445550b00d04140440c560402001407000e1020100c20070302c00b440001c940c0740240304000104100484100e03203e0000c0c840410141086880c24000000b04005d00e80705030b078255a210300214602c101241414840c5008078035203070356142544002440c200010340300c500350912f0014240581c1e07540f1411706170070090300701802088000300e00040c0103007500c0e41c0046a043d841c00d14511200512000300f600b1150181e003d0700c41542d030300c540036038480c80940d60610008030f4160000708141c1c0680d00050794070307047c02e840d03080041d441e40d204011010048582007014030f06900d032602560340804070856880b0440595104c1038600784a201e0b6a040241002554640f00d0300c18402c5404030800f60094039800a00f013003c2800e04852182e22200d03036140381c40946250700899000c0ca8010300807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 726949811 1250 726948561 726948571
    0x90c010c05161e05031f090c0806070c02101707110f0303040c050a0b0f0304020d0f02100207080f0d0e12160e070e060903190215130e1e1902120403020102120a05 71
    0x1b001b008251800c01800007801411801c07920f8074a01700d800310301443d080020300e01c00c050a032100d0b14509220300401c0001d0b80c0a20204040101c0c5000310318040001e00710b40c030b81107107036410f00c1c0d020403088140850508402d5400e03004988000302c00c00091200002240003129802e0700c1392812180c0715045038034180320b5a0b03000d20500b0000c002203030043c01e01180b40c007141c500504000900040c568005071800d0886409100140d0080e41c09200c2c0380000d00a0248100560004040c3c0140c1040041d0206020303901481c45441c04100009d0711080500c01c4c0e030b4041c5010401910682e89410031000300080903298100041d82c45503100c010340c24030b402201d6082000400811f00120462500d400e105200c810480e00030032010b020146615503000500301441260001400c90380c10001340c0650408000d0000303110410881c45065140d0888504580240d070b20016043c80a0100161201a103e03103014080745054170820807041c142c1c198007501100d900000c2e4428140c68902e5844165001620 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 726951061 1250 726949811 726949843
    0x304030b041103032514060106140f040e010617010b0414130905030a020a0203010b030606220608070321030501050a350106080d08090c010c05161e0503 67
    0x10208010851039900380b44011001011240b81c410341420580704600d64540c204040c920350400ca204121121480400703c3e9400c5008001035850804000c00300c01d00c10480680c81140052030003000024403040345e01500e01d80c0700050440d40c3d41c0500030310b04090340311502c2c540102040046a681c401c0741c12501103a1506200320090500c54041050007080b403400c4000d0b4640d42c9801c031000403400d1005e8150380420343c01a00a840c1940145420341d0442c0c1819403080d0064010050143e88040300e090b5640c2e01c40780624600d00f8038060481c010200d68011180602c10803500100300800c55089440b61021660f2600c4a00d074000801d0301038690a00550b41d0101300100240a0401100c060b001000c145400d05032048234080701ca0400ba507620008801540d444980500040e58208608500c2028a20f00030340503181c0702d03181585642100c29101e040111404421051020030010750800c0d00055a01d1807580e81c2d640955103103080b1800da1100081c030043e40001e40b03454082a9200c45210300c0d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 726952311 1250 726951061 726951083
    0x71a0f0429010b25140f12030c2508030406060519060f141210150203160f060c0f0e040207051005070309050708030702040b0402041d07020102210a0608030403 70
    0x905484903801c4010001c01140300300a0a00c00000c44180ba00300241c06052594030542c40f2150003420071042201d141426400030000840d014034a104480c0d00c920200001900d030300440142b940c1c1c40c0030000f00369100001100782c61084c01b20440045010b01d110303a000b049203035541c400b0b010000410315011b00386032000120403c0014011516500c02801c50301c0d0400d541040b01409101c103401c046594620340100c01c0c01c00c400030300e01c40150000b41a40c0b5055950a2a4240000750b0702e00c600318030744030311a2031103207440100046d11800d14225540140d00344022095101c0061800b04100c60f42c2c0000782044040e0102e038140752084442c0703031303070000f018242c6800400f09150240c40f02070281d004040d0b44886c00b2001c68018012007005d00140d401644e500e00c81401000151881244101d00c02c0e80b041200300b0541d40803030f10f19140000c1a407001c400380e944103c0d0a03070090051a101040d50080c0005666040307203000c502612604080b40104441c680384c55a541d40e03400f5a000081280701c2c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 726953561 1250 726952311 726952319
    0x1804060e0705780703030b0d03031a060a020a1113020f03040c0b0f030a1a04020a030c020f01060305191115030604140408090105071a0f042901 63
    0xd80c00c01c041d146160448101450300701c0c3d01603409081c1d11501c1d943e101c1c0600b80507043e079410300300d60800c010240035903071000c003e080841d072480c85103400b0007074601600150050416003c1d800629072404028003101c480f2031076041c042c014015205506280e124070000c115800d10340a401c0c2c800001316a801880c060056585804543d0700a40300564040d80c1e2500f01401d134012400148881d1070b890f1f0502d40c40341032034602001d160415401c50b0392001c200f4804a00c100c03585109480d481145001c0100341e19080ca1407950310004c0d0141400d401900015403008001d40540203494030001640c00c4941c3c41380510013072802c072003081c0001040c940080e443e02100303e40303a60058184500490300d07814808903030030001e200c03410b031902c400186040200410805182512802300c40c513102d14942a030501d00395032003030700902c12010664140500450035805100314002c0c25804140c5202003103510b81060240c2040d000c038101d42c100e806004280440500c4540007003072024a200c48414103180d40d0038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 726954811 1250 726953561 726953587
    0x50f0f1f0603021005040806090307050325060e0601150804021f02070806011d0a0b10030c05093a1e03210903030e12040b0304171804060e0705 63
    0x100e40c02150016107034074010001d81d82e10b2183c0103120b402c40d1505680c9514283c1a2418020b0003400f002c05a041403001d071001c40c8000c011501c3c650345148043d111561490100d1080c28207011010302110b15114001d210402c002907d1130580b0319449403074000480701d0b4400c0300d1350790b403c95009422010803c031194460f01e8070ac05900061320700d0b0069401c3d0a0b00c484015140403c240c0c480b1450348603082400b100d100c03070b80c0d83e0310382c1251703040005000b040000008a00c41448410b040700c1090fa45201428245205000ba6010150f00404181d4001c1e11351800e0180300c800320240141d4510001010682c10700d1406a0081155010030174540c1d6140283c007509a0624611083e0140408101c1030541031800d13030440402c07072503820400a254003650070000e0840e080502e00b44a02d03031140d200b501e40780f00300da01a45c04a8a10102c03090b81e1f03070380c2d0386050343c43c1d09011820307100d8504020440c0c2080003044004050311080546042100c669201e011004d41ca806949031000310301c04100062007084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 726956061 1250 726954811 726954853
    0x30f012306060702090a1a010c030831050a021c230c04061d06092202030a020910090e0703020f0603090120090301141b1c020d09050f0f 60
    0xc004081a0501c0b0082d00840e01751001182c801c0207040e03171101d4511030300c00d58024901b20102e0078a400d010080e540e950207010b950018148008441c2e503d03111884590b40710300d081080c00a07010004410500518100d503594503071400c02ca2056842c1c40b140105038211401158416402884542d452102101005801c104040407001e45000b00c02c0d8903406030b1241c0c06100c1c0181044040a13415241d150080f0a00a0014011070b12808000044c001140b4031011008581c091080505005000500c00070b80f8084825a00941048100040050560380b1010200c00c07035038401000d0102c0980d00d0100c588842c007a010095000468079015612820880c0140d40d128600c4c5000068082201c5126508107510a00c00305048038001414060303800c0c00c2c09042d44841107032001c0c0c01039041c0034291001c013940003011043c41c2c8201003088082d00514214040041208002c11036486004d901600e0140901e96800c1c0c41c14031494982c2c0d900d602c4000790f610042041200603218507091403407901c609038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 726957311 1250 726956061 726956071
    0x30a1502040b19110f06180a060504061b0e030d0518031e15060312070203120a0305061f080118020d110903010c0f0c2904050c030f0123 60
    0x5603090102040000c0414010201c0b99154100280709040c102e6009124100540306624650007074020b0705100c40c03000070031503002108a0305034204d04c00c800c002c0d603141001044010306218100740600062012680c0711209a0005c0303110590180b07466007054410a035041092078156014440101e4594440e070301034000d004034134a0702c0705d15080410001c0c0c90405806004181c0084010031040789500c100031100d440d80058100038180d2030120000b0303880c1c8205015200148100203030721000c65406019210000a210840d44e4864401c421300400a2004954003070003856100007046004c807114408140c1c00e0200d60310003209a0810004100d0422615400610183c00748042c0f03168101a00032101500041d14681b03869186c40c008050a50307848584403010f009040d81091842070340700d90102c42e9a42c0004000c40d014051961604501e0500c40341d0501880d0000305200412001250040345950f044040391001340415404a00300d0710f40c24143c8400c02c070055520f882c03503260340004030380c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 726958561 1250 726957311 726957353
    0x30c030c030c0f0a0e03010b040e0304090e030c031b0d0c081801050f0f1e03010302010801150938040501020a2006030403112a04050a0e1603060e0c030a 67
    0x710600f961800e0b03454109004a0300030421481c0d0410311810244107c4103c00011142444030900300f00c2440c1d2680300701d029103041c1e1902c4031440120b02c0c00c200100c44194407142e040726a42ea030f0340c1d294449142d08521880460380601c03141f8104041c410304084005942141e030f07081c903080000c5800305d82040641c1180f818480e041c0010405642d04d03902400b0500780854426a9a0001c0d550351100303004030a0240307040c000c0074401440540d0b800f0680b6419140c5260021201d01440401a2070211940e845980ca00142101541d03d4800d400078001801c600100e04048550070b9100c6800f103030255004041c0141c1c0413142c1040400e911405034606200682d00d03469250f450440412815407044070300b40c000c00ca8040210440c88001c000ea00305001450780d001f0129180004070316402c400c0f00b10818403640c0c40701c000c02c01c51141c42d4440d10000b0010411100300c1d48206400441c3c50140d440140e4a4a20b0b04103d0b81c01d042001c00e4003413125030010060200911b4964681c40185040c0c0310705080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 726959811 1250 726958561 726958567
    0x304110409030e130618091205160219031e1110050f0307080105130501060503010308030901020c0717010606080402030c0d0510020f09100201290123090411030c030c030c 75
    0x1c25100da1301c2c40c1c29520b50f1520041035881c20b21481150548a5803200101c1c1494840e03901c0100b10849820039070301320149801c503030354120300b001603101441d600400380d4800801d000d01c02000d8039001450084910544111030520070300603000401021000f004ac050300a256800609c0d0300d006c0090581100ba1810001d0405407250608884c03038108503240c002080c0b20308014002803400030501c1d459078004903070520040d17041000040280c001840010441000400880d00c60714003034046e02c00da004034904850394580c2c0c69644a1050541c3e800031040d41d4a0100041039080c41140090312076a0090002d0540800d900c0500c001d2140d0070100307030382034010104005c441e0941400181904081c10071150f03204d0b100501007180c81240000b100c030541e03240410101860354050000c031024445031300d810b06c100c003030140161083c05a110790160201a005003008076842104082d1007424000d542c1000b59800c841140c8045200c161502c40042d0420b100268003400074000a5601c41c80d20940181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 726961061 1250 726959811 726959837
    0x150318070f1e06140a14030405011d120313030314011202181306091103010603061b050a0c0f0201020c13020a02011a06040504020d0204050d0f03020d05030411040903 73
    0x4242409508650300403030300741e501045810002d010140c2c0c000090b0726206401c614203003010b004040c0b014007082c8214404140c282d4018000e03000d2070800c080c0d9042c0d80e030307491405d450698000c000507941450000d401603840002c8540009269490082800e8864070b5074607016201341c075208801d40124109500c680d100c40004050b40c403d00d009024442c200740e0421460710410804480325000b00c0c02c1c1c4035004040200d04c030301c5010604031040e04140c001942e0702d01428a074290700b000c1c0340c3d0613806608240d000001c011283e401720203030301d085010b60403044445c0a0700719200d1082c403104800192001100a02043c03110004294039032050045441d203559600200e4013950410651807078480c0e0200707881d88010f40a019512442c000b07011404402140540080e2a40c0280d015040c002c0d40d000c50784007c8141250b04580103090024a55504a80b1510b48001c00c100c0b0210114014051010300600d018000c00c262030069510907943d8100405040501000b450983c41c150100000389608213 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 726962311 1250 726961061 726961063
    0x109030b060a0909050f150f0c09010903120c0c1e05060c10140a0b0f030d030f240f090b09150102030d0e06150603010509010e0c04080d121406150318 66
    0x90301e194810380141001000145101e410460403030184000c1015103000c1000348d1040f49111948444180d4845880701e00050040714032440e1604000c200c02500412290340c141c1102c03c0100d00e600c40e0a5044d00f8070b441d103c1000c0199450b000e880106c01c40c1039070a1005d80361000c0680f0460f03a00340c00703c0d0450091021004145c4150050290120341c3d60310600c07554160078091156000301c10f403501082c52580f0004695690403603d14082010340e50000c1101070f56040e04403010340c0c01c0e00303900411041c0e0000e00e040705008052140a2880050140001e00307010280103480404000511071641391344e40f5103032035412030784490449045000804c900f01c8001043e06c11001302844440081409141c05245601c1c5a21442075030752096001340010403159803a2910241545c46c1010401455110418400054011604144c405002d00c2405d807415650010301416140d490340800d0001e80b10b41e5503400028101510406d4004402c8072242200600035401550040c0341c1a42e05002e080b45c0b21001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 726963561 1250 726962311 726962321
    0x1050c0a0c03030f0e06180907020c03010e03030609070908030a05250b0a050106030204050310020c150a0c08060103060305030d0b06130902040312050a08010e1b030f06090a0b0109030b060a09 84
    0x101c01180881c0381e600c0720154090b550944440741035400d18031f07050007032100318407001144100e24429400d541c00a00e02034400e010030842103030003400074813a50844141c2d10b9203a40048030101d01036003c2c100006d403000e203c0e22540040300c0001d005545051204002190300780e1182d140d00b051440e0901000e500700b4070501d082c6204500a4541c40014207042103104c09403107060340944109401070006112a80c0c0c040740c1ca000f480015107006a0320b11070313203075001d00f07202034030a1210f136881d8442c08210350041c40b41c00129604d00d4a66074a06175903901c400540444102c1c0c0070140c0603600502100c48401b1603580075030360b41c01b0700400e010306005038500540410350464000c20385198011034100304120081c1480034100005041081c10b0982c8040e0003040104144a80c604580ca1030012940c10080118449002ea442000d40ea41d0707494405200385078a8401d980040c02007131070400080500c4504e1090941e444016910b03e00c0d41440d6444002113120043e0007e5840582c100380094402c0180c820303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 726964811 1250 726963561 726963563
    0x40f1a09100605030304050630011503060e0c03010608100b131a0a0527041104030201320c1009060b4b04050f011701110901050c0a0c03 60
    0x10a000348200c8a240300b0740c0d02e030798851406a0300601c010300c03036070f03a815050300d415065910200300418071034000003c440100d20014080028004004101100e01200c8152620052741f001d020710340d91848003015180f01100d2004464405100511070790340301c0c2d20095002a843e00c440640d19850300c03a070306400d0303000341032400c040001c0d20f00c1001551500804144880a4024041d040819090024101d4400d1034000400364058000700001e03000d00790007848050700081d008011300002200781011540c4540800d1340441d02d45011180d405580c4410f00414440d0b000318010300740315141c50140660040032509410340100300c580e1650609910954400c980a0500480c2d03403880380d002d100a076060f4584038422111140701103410310740c600074011000c0b602c54010f9132034183c0710010114000762100900358001c1c10030051100c3d0340300d403c100c0e505135038410b0500340300d40750800006403c0300d140f444900111001400303442e801d58059005802401c0c907a02c2030303500401d03895440c04e45186207500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 726966061 1250 726964811 726964813
    0x15040e060c0c162312010c05071a07021216020310020304061b05220b07050a111c060504030e060409020a030b010e0102060a0b01031e020c0d08040b040f1a09 69
    0x15241400c07079007048240050051000d40e004000d0034252880540850700642004094031070016a00d117494520381440302c07200d11002009401060700c0020a254007180e001c2c1c1c1d09020b004000e108182d07000019a02408041d0020318100c0d22586080b200342c0c201420003a44075040c1d040750009070300c003400040102c0c030798244010395918041c0b60060480788000703000072041f14000d1105540e10380110840e40d06112034144851075030340c4e09c0140e140c29070542d002003a005030302090a03800c102002401c1c2607014829007503010311a04c075600b80944603111403450003504082c100c404012800a070302141e08540207181c400000314621011030081d5025a101d010b80da80c1c0040c44960160745841811320340102407901b0040c9090300340000b991f4050182a040c00d1554030311408680f62301950140c1c0c28408406c1c10510418044840000250460091454140108014048441d01c42d114440c41264400328081aa0310385c1d40b034003451240a07950495095040660350240d03500b060342c100d4030900600b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 726967311 1250 726966061 726966067
    0x3020a0b1303050a0c05070b1b010606020105130813030506090d1e080f0901060512030408060112080715020f0301030c03021914041a040504112715040e060c 69
    0xc60a031150309001041c2911200303030078407050002030380309003260340701d0a5034030b00f03071001103400e0402d07500b00400c41e40110001c01002034642c2001c1c4c00120000107203030f2100000c1200c2680c0d058140c0c00ea68040300c0302d102c00455004030700005040076002e03150519403001e64400c1e070303a03da589043c5080010389110b80d0aa101022181c0700300e620107420700050609540c5418208840b86001e0140e41c0050300b408001080f5400160503080250310141c0101001401e402c04180882c15064980c5e000c0e001c5c9030140d0160000124200008172a040040b540c0721080c14640f50441d103880040305200403510090a40801c0a000c640028a000d580a9400340071085015491441089a101f01f1136030b02d070b41289101d801c10040c08203c0c0200300c40c1800e0644012612001c00c0340c91180030304808201541c040d16000c140320a2000e000c50700c00c445034007642c4020000c490304002500c40d980700b24041080d044801c00040341031040d50910004032038040c00211740c1421740160b4500f03104c0100c4041e51755030004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 726968561 1250 726967311 726967313
    0xd030f0b130212090a0807290c03010603060f030f02040504020303070f05031b01140f2815120b06040b01050c100b0f01030c1b02031c09050a050a0501120902150703020a 74
    0x7100f010381c01c01006070050581c1c41c1c00307079200c1d42d090107030b4070010f40040520121050341d00c44c40a41e4480c0701c0c0604607108d801d450b00d0050b00c840c9810a01800c000070f40362600c049105102c04803070400740d0350007640011802d04250300300300c0500b4000700300b00d8040c04203000740c40014145010b103140151152015540342c042500050001d00b101d1900c4280700c0c1e0600c0c0006041113100c103010f54010140b00c1d5441d4007542e440010520303a00c116a291840d002e01c05120041c10b0700694402a82d400380e040c1c40e4000b0075076410300d81000528048001d081014402d011540310300c0c0c554010219210103041540c200003210610038101107040c1d04000d0501c2d201ca00801e0249402d082280400c0c50034282001142c04500006024000d54a005040b91401c2682da80655504204040d440419038039150741004030300a00422007070580c450540108001074002c141813900120403400c0c0c40060b95504010380b406841a0058004a4000d907000340400c0d45108060003113100404805001e5002414100d0301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 726969811 1250 726968561 726968587
    0x720010b190509131112070e070e01050f130b0f0903070504110d0209060708040611100911041524080109020a050f0703050408011401030b15030d030f0b1302 69
    0x2041c031150010018041003841140d80d02c001980e040210207461860141c00e0b80b401045941c0e032010441d9010402c40c0078070b014150001008002d88640c0d15181e515501c50910556606c40b6426040380480c41c2480321661040b043c0340504099124001030009403583c407142d606c0580d015840110b03404400203070940c068203007040124010141900e08208088800020100d980548200f4921442c0c0001c3c104600755200c030240c802c80c42e0410030035036846070f44480141003031681c420110458054285410403c42d164851011a80d4004410887c0f100d140001c101c0101448034400d6a50008034001050200c0d41c510b20b40c1600070605440c0f20383d0580d00c48054400d42050f40181644d6004200048040b94030006440d620603901184507250700d0701c0d01e010344040c011900074a03015841d00c580a4a00d0804048a40c100c0c0d000300b845500d9503c3e07071074000c85240e41d612045501940506013540102e071283d0310440c4980c454450015000c140480011b0100003500812410150082042d81b40068 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 726971061 1250 726969811 726969829
    0x6050703030e070f05040c021e07050901140d170d0f020c070b0408071e18140a0b0a181d0606010f0f0c2904060516110c090720010b 58
    0x1410b0303001441c226251541c1c0802c11412805201e000e9030319401c04a490038020003081510040da1002c176103401c0341c09403e0300d03030b02c1107507104441c0b064140000004a101c050340007903c0c4240042d2111000134610b44415400607100e00c01c0c582150300030001400510700510807041804019400940c3e206250780e0064941000b81e00040720032941084100242c40002800d0402c8070304002c16481d407118103400303041c45141154080009003449003503443d15420103510034444d01d4900300031003c89407500d90b1184212a0354800c00358119940038000c2c4030947c00840115201842483c3c0070600c4000c00c0540321808140f80c1c10f02115911050a010a079030300809102010300c8035140c81000200e41c200018085501c0300009408842082015194846290855464019041507070b19441c246890329400401003140d10141520409480d202c1d03c500c11b50748004c0004014008040ca030042d5810004c0101002d0503007403d00401d101441c00310a581c3e148401c20850640000030300294034000c0c030426103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 726972311 1250 726971061 726971081
    0x40207060c0809162319030302010f0b0f090a02090d030804020f0d081210030602030103050a020a0503030a020a0b06040905070315060806130609061103100906170a021017010605070303 81
    0x504140402407066050101c118101c800d9210903400078041c1c0c3c405a00f200340c0711308640d03801002286d0000343e5200b10300f110360100e80c03282e80200030300c80c001d1003402c04035040c026106500564031908101d8919000810306d4215075500700040c6481940400214008144102100458a000200030540c50034148040b904001035500d01c102c118995295100d07840713107030490340b580c2d502000820343e40c44c400b5901c1c07000380d540203d007190740e56104c0c2000396484610750742c02c92091041c42d1000c079142c100482610301d0303440a078004120314070441c0d03100622180006c04c43c6420582c0e40c2418404188100310300c50045008160f042841d034811b07000b40007620900d4000030500d601c184280f02003030071141d207504451078000400040c0c05809180c204040d1103442003074a807074072020082c07000d0084804131709421144a40e10070090550340e0340301140d80152800082c051600b000032803201509000c04050740840f900c1c500b0480b044201c1341000c0e1580404e800c80000150085070b2101010b4251003141545 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 726973561 1250 726972311 726972313
    0xd1719230a14161104050f061504090606120f06050603011a07050a0c0e0907050f010807170a0209010905040e06040b040f0506010306020d0e0c030c01180509240d03170411040207060c0809 82
    0x54500304090000d0007c014010300d019440d8245070450f2103000e803098502801c04aa42403140719078958004007022800340c00300f4001c501c0c04484082c041c206124500c21128050196425031303180c01c0341003c0340242040d141c0c18400080040d4000580c05101940742d0b10b100e48000604541014603012040c4030003005016554050b413000e0126a4800310010101c0c0000d1030702c205190b983d4541100c4000160018092001c6102d007071180c0030560360050600f282080ea548506195074000700015102d0092a00d000d6420000100780403a243c844190362090084810580030281584c0381071030234400368001e641066022030b2120704207400740507552501d030142008082c03001034200040d072201840981141804500c2c09038810340d4009040784001040018079101041c80c10582800801074000c091491180c0907840110480c545802a00710303040d0195200800f01c8000740203180c081c031f8080d200342c0b002d104451050b001f0340e0703480c00200300c60382c8a0580491925941c400140c003d56001e0a01e100c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 726974811 1250 726973561 726973571
    0x3041502011419020304021c0b0403021207030e12010b060c060402041b120e0c030d0804060c0908030a0507020a0e190b011d0904020d1719230a14161104 67
    0x3e49056080b0802c8405030401006035030340c950b0710024400c071203148944074003e040c009440045c82501503540b8400e40c0070b43c080c6c682854072500300044612071902d005020550165242005040c42c00860b481000c1c0b03c0c000140d014001d00001c1c900c0d0304080164141a84280701704821420305001e450b41841152003000304441d80c94101402c582d4580740841c1078240e941c8000c0c0302604c010404d4504000003c0d080d20300c00684000010000042110b094540c0f03400c294410085c1842038002108880607600a036017416410358085420f90f010300000d07071344040c2d44840414a00d904521080c019081e200794154a04080051f460903500c1050b0380c1414800d0004900c400390b000130b08200070740785080b550185e180e0360383c0c1300046806800850241041c1c3c200f00c040202112460014801410901c03035105107480c00035070445080b0aa00205030440e418100595040c540c0c8034080c041d4001c40f42440545a0601c3c101c0101e580c0004001142c00d00c85100d11100780a0070981281c030900c000e44050207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 726976061 1250 726974811 726974821
    0x80601080f03041d040309211a060a1205070f06050304150903091e0b0c030a180b2b05040501060603060608100b031e0a1b050310030b0a0905030415020114 68
    0xc101d0120801328025121120000702054440d90305000684200c41102059080001d103040304202c3d4040c04641c8070401c1074058101e20f220360000340c426440180390004031030a2150001c545a010403044850303200c0d514020400d641d54900c490082c104030359a1075101c0c0b501d070803d856403075004004180e400e468001d865001c81d03480015482651043d0117500413404a070341c440c440c40c0f4459401050851004210340014203000b1009112180156a9804504665841c003201c102100c2c424400c0124041103c0e44940c51301401e9518100ba100d038030105035182404841003900c8084074102d940e41d40d1007206000d00c5804bc42148064000b5250911652504a82d1242030041c140940c0200410100c0021400030350540540114078450750b01c46103600301500c0351800350a40c035440044140c00c45041c0c07140e652189042d81d2180c15014a1351f0000c6140d030700c0d9026021405894005600e44a01007003010a80400040005000042018480c2d85038180001d0860700c0c0e246500865024074001d104d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 726977311 1250 726976061 726976079
    0x807030207050c060309030c0102130e010509010f0905071205100509100b04300c1a0c030313030e03150a050606030402030304030b0601030603020411091206060102151b04080601080f0304 82
    0x3011440070399215689448007a107a43c1f4601442c072503180c0340d6000003501144071a21454500449600e8135040719140d80300c3c01005180d410074052601020b040710720410000605400090b080304507410f0585011100040307050580c0c0b0100d4280401d60038000c020445810207030012633210b00c41c1c00c2c400b1442343c1001d8503003d440c410741c8101e40c0d15495080011803072031411035120504840c2a0741000c8104001d00c2c0c004040f60152117042007420320300c000b40e154403108400320381c01c03040000d02840c51551103190744c2c0e28107003041000750104401400c403421649c80070000800354892041040620345040450b0b00c068500041140340114414818031006131400010380701903c3d8403000a9000342d03102d07401203009001d48e83c0040d40c800d00742603506150641020003000300c0384098a4081a50260115090f07445500780d808038010703401610022110340015080a8014144aa039a000c618010b1101c0c0300d6500543c100403d2a08a4001040309960410040e01c08506031005142001c1c03904402e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 726978417 1106 726977311 726977323
    0x1d01050c0f031201180204030210050c070e0a14060d050c131121090c01120e0f01090302010e0f06070215130f0c050f2b080d050f07080703020705 64
    0x204841c0d00803141a2074022b0b20880c28a40c01d40002c0790b00d907125084140307060007501c002243c0400c415031502c2c061042008c02050079400700c61544021240a00b62034400d044850304100001c00108200c1040101113620308801c416500d00703500070b0101d540c0f605903a00d400081c030915040d1304403898404100441c500c1d071283c2e07941c810f80540d42e03c0303818012400b090b5107195002001c00550080d03038082c9110b106072048021411911360030f480440b1011009032751109084c0c90001400c02c40400e1511501c8020090381c00c0082c400394031441c140d0500120072200c000020100850358502d040080d50002d034a900010440c1410001410140240c03442441c1c800502d00540ca00b48941a200d243c400d00b9001c842644155424100f00403c003084403014001c1c480340424a180d807041078410080581c04482925000100406c1a2030080c460000c0c144148400b5003c25000620 = true := by decide +kernel

theorem cover : BRFrame.Cov 726798561 726978417 := by
  have h0 := BRFrame.cov_init 726798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726798561 ≤ n) (h2 : n < 726978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
