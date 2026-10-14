-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:09:18.084296+00:00
-- url     : https://prove2.me/submissions/bcec3faa-a9ad-465b-8fa0-161a6f0d4743

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 194244604 ≤ n < 194424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 194245854 1250 194244604 194244613
    0x8040b0f040e0a0501031e0203030403020402130e010807061e1b030915031a091305010903030501030b0708100b091503040b341b120206040512131214 66
    0x300c0020030000400c1260749250303010026480e0025280c0440344284401490740d0030041c1060b01d01001586c0d050034107400182a2400c01e41d61343c0109082e40e0007040202e0130040300c1c035000e1110300a440100f0b40075200001c01031207000d0a0810141c2440c000c00060291100302e9020000c11794443d4042409401c03c10f150300c0e03900f81c0e0741c1c032b40a04410705900540e42d4484500345441c1c0780074800c0c07107180c640411608020800c490402d003400810f060140c4a81126030740360f40b003400031074800d008007400b06d44a550009890741c5941800c072150321001d402e68080018039800d020030301040e05500c005841014912035074502c00c160010700c5141691900078a007041c04010030041c0710b2041107842c440c1c0ca2a07075200d0031180c02da13200c54424144030702c2c1c011402441405c00c0000c43e1301c80e0b014011201d11280e00100f03101071980321b06409841100d844401a40201c1c100000c005050081090580b54800f26606241c80c0b6440c80022010600500d98198491000d8405012400c0c3ca42c1440d502220290b0b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 194247104 1250 194245854 194245867
    0x6150201050901051b040308071707051b0d2604050409031809020c060121060203010e060f011b021203041d04140a0b0a1d0d02030c07170c010c08040b 66
    0x80d000e010202c4180035254a8000068100ca041184040030320f50f054540c28a40307405c5540743c41d200d801812003502d031110b0120f4480a60700380c0c2401450411300906c001c2103c810040d1420035059062406540102400e6845c00c0024000300c403062140601400054601c00c560480324074180203650000b80d010342130020f0304040c55003044d04030030b802068003c0e02c40f04980350143e0b901640301c1d0600100c3c159101000400c2f80b02d884a4104408510524180c60205070030748402d42642c01c281c0040c00f4002c20503003446164601281c500c140e00800f800c1c40c86001000c0741058802600325080603005140228064002a0050044401401c15525408146100c0c90300c1048280700c1194119820f407031090922468250014445d15003603409036241c0c03142da1310000c1c100090f007014100c1030600c03032940c514101e81600601c2440402007180d40215280c40345000317002e1407d02182c0c0b01045400950140d031030345420100b154103d90705c080c2414400701c3e4861508410500c03403644200000003012800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 194248354 1250 194247104 194247107
    0x6030307020f090711100204080106050a120b0c041d1909050709020703051201120312060305030307140d0c030c090b12010e0c07120203040303120506011e03020c0a0605060411041a0306040615 84
    0x6081540d1409d0001c000071921001400240c0d1420301800c81440440c400c040005503a03400010350100c9181b0f4028206075440c0c5031042c48240c2c0540c00102e010503001040b050902100c1c1d8003e1075a0b41031030a01107001240c80d050b482d07810600038014606c0e0005075050038507010340e0031254084106e038004405507030f554060700045e0400c040c00700d0005030300312800781640c400342c010881607031742000c0a07515580b144070702550803c0790086e1845250700c091101c40c0846505205030300200e0b982d610003242030b0755001c01c000c09000c00c50b00148a60384c42401285103103030f10784840301d0540c0c404c01d001c0040d5840302003d03d82d0502031000002e08020600124044503039000c40a042181d00c00d80701c1503040d0310702c51444130944100700e503d2030000b13100d01e8a061041000d103410400141c010f01700145000082c00e49070f800c1488a980564005031a4018410141000e22502030080b050342282400c0c18100380d20154460705410301c00e1640d45000c00030a1081e511030b40000001c000c107850251030032800840 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 194249604 1250 194248354 194248357
    0x1080304092909070908100b030c01050c0709020f1603050c1204121211100506031b06030705090301110a0815010815040e160f08010506030307020f0907111002 70
    0x80e044802c0c1030001c1e03602c066540c61484803024410400b00c003042d44080040c480701c048020007041c204405002e00060402081c084015081071301107011035024209000c0c5482d011050481c01c1c10000d040001a012000108405084d02d000d14400b680d510941c6001168074001e020300f4410f038420340d030881c104054001008002c040701000599000000c1c070302c10004540554418903050017000e28225001400490403c0070f802c4990420b140307001c00061440c1d00e05a142c20f038101015940e003042c04444c2c07504010440e0501c684000803601d0602401c00715205020240004007400030101d00d004507542d0131b4104a005124801c00c8948564241800804042050b5050b103140c2c4440d0303c4080485d441502450712544565030303d95021a90718042c000240514241020301d8051849a564203090a011060045c0080142035401074204413065003140d1019018522940c0300f00420301c016180d0110741020391380101c61641042d40c3d0700f030040e1200480c00c1082080c6010300c42d101600c0007030550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 194250854 1250 194249604 194249609
    0x1d19060503040b07030506090402010302090301090813050102060a02070302150a27060b030a020105250507140102070e0f060d0501091a1501110307060c140409020a0e03030304030e0613050901080304 87
    0x24683c40c21500d07901026805c503403041e9040c0e50088110b4001402550080d00107100c86000038000141c51311007a1240b80c5290003501c81203100f8074401000700030700d42c0e04004468001c40b035180c0840c502490f82c0d030041e54450f00845d000d04050031160020b4055401944242d0000400e065060090b00008460a10075044c0740b10031900c16191111254035401d000400030f003150380c10703140d59143c00000305400403540011803528090402d42030400300064020710101c0300034a211522408658000c00c000390516070917801261804944408102562505142c03141d0050300a54080a084100341000b6000d40f0202001034141e55811607101c90603c0b6000400f8440c2a0090300604880c501c40011605080302c0801c2200a42c0306000d4640850140c0d8444e9800c0310841c20003100d0304901048460468104d5404144030960201c0c20f001c3c1c540d003141100c000010224040e40c554501660702400a80700290314a000e44800300f81e6981504111501c00046c0c50005c100124541e55122456504c0d8040e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 194252104 1250 194250854 194250863
    0x30301060e010f05120103061a0a08010903030b0d0c030221010e07060306080d05090411132706030308070c0602041703040510030204030812190e150609071d1906050304 74
    0x14100410303d58856010f8881c001c40341c40303c5044d04e03440d40d02c07044041c100e0040d0326088140d4095844000f40e8400501c000100390140010400744490f09010f000c036030765410020301500040c545100060113a1391903000b501d60440d480303100c20800d1185c01170300c051a602c22500075840c090185a14510008944e411212660340600200e0b4840b0951921203107072140c0310300824400d02c0100d84c5443e294100841101c0c50101c994182021524076071440602da0f4411101e1504c025008120035400e0a404162402400c0003403090a10755503008184600040c002c0040101406264080044540480380200b030344640900e00c0b4900f440009489601c20f100745440317183d00342d03d0080107602900903a022130f50054441818801003d8179940f07091401000000b04084400c4507031141480c1d44142c45281c0c0340040249410340d0040c00d0b10064100c05000c2d00d1203002440100101c0c154005100c00c0d0b01048201e904c6002100000410104614030016280480e08080c010611a0380000603500c47ea005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 194253354 1250 194252104 194252117
    0x4020906120309060706020d05070507110d110904030e04320f070c0c0b070809100905060a050705191419080405090402030a060f0b01020106090e150414030301060e01 73
    0x42904114100d12802607400d0680c005000402242c501440a410348500400000d4a0300509508100c03c880c0e04036800c1010407404110f6a0600052030101540d8003030036610000c01980c80d8940e03035200c03001160107a1041d44004005400c040c490183d010421074090001e000000920b03440c401010340c1544d0086c00c1210f41001c0d0910b014100c41c2c040d000f010700d03d94071070f032039103841d24100d07400c1058540c02d0740c00010740f54001481400940042035200c2c001c80384142c8820b1a44100007002000e9900c950800c100c1c000103222139900c0c10100c40c1490340c541000c0740c4d19803a80c60039504255040e08800c1c03401c101360203290207000c410700740c400b10900303902c0503640a285020140c0411144805026020306018042485141028034050342c1060000301128a050010740d1840140d03a50b414185070b00329101e200500c880d50702409544080c003096801030042122214403941d880c0302d0034100e1800310222101003020b0000d0344140286442c1c0c000103496072580c40307070405001201d02035401400035070b6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 194254604 1250 194253354 194253361
    0x12051905070302091801030f020d0221100b1215090f070e06040612080906030403120507110105011a0f0d06030b0703061a0c150a0e030a09080c010801081216020a0e040209 75
    0x119005251b045c1c0360f2080140600c2c00103602880f0300c00d030a5520498201940e600c5a03210a03e504400c4c02c1040010710042c18002074a103100803d4840311281240103060081743c81080003c0400c0018900218200b10001541c0d400c1450f4038150039801078210a0041c0e560120350100c108020500c0341d08165014041a07030b0b1004114000b81c8510006000c000341070004031210300d807800c01560000d010307151600d1511020b080389002c440c800e41d41a000300c1c484c48001d5134203c40130301600b40180400745007202000750702c4960310054840c01c07540f17a605480004401042ea65140d003c00b002e15040009034040345040d00018008008500a80e561489050150908605020126140e0900d0280078000e213a811034025080804081c4c100c080713168492260040c0c040d4100080e01c661401c50f5181c201c014030b095400c500381400c0007001810805d5000060000f500300091980041c450340744580e507104a2a40b0101d030003e000c01000b5404002c440307002800204042d00369014600807070f81d1000030385 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 194255854 1250 194254604 194254639
    0xd121d130510050a120807021305180d051305010309060f05011206050f160507020a1a0a030f11090603072c0405060d0b01090e0a0c0f150207061205190507030209 71
    0x4e80b40310b441840020f2000200010b11404040d010640c8080c209041e003da0680c03008050b18000c4441e04001d00605030f4004d1801d8042207000d013801d2481c20710a1a0520002c103c410303107000c03801907506041d190340414041003102da10105800780200010840c9584650720004401081c40c01580c0c55070038840804d9400764400f11842c01602d024580402440151100341e5240c3c100c0801a03038000503032200083c000340d2611811f10041218000b06135034404c8410050201d540c4c4609017071459182020110560807161701700c40680104541680d1a903844000449208040d007080141c08000c60f0312000842e10404c1200d10804000c8034140400c0e900c86080c4441051b040c4d01c060541018031004001c5102543d010401000b00f482c10b8940506807901c4540048195a024a2365110b2450f01002801520800420004d4043c4041c0c1852031406034004c1c200000c5910711b1564680e2800403400d240061044155011444003086c4202c4c42c1c0b242029000790004912140186201d100e03010010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 194257104 1250 194255854 194255869
    0x4080618120a020c27010e07030f05060306040807141609050609060109170106080f07081608030403080a110f0d02060a180605070201090209010e0105010207050d121d13051005 77
    0x1501da03030040100001c110104200e003030200c007140c517030081e01c0a101540c03450214200c90181240c07403090f01e101e041102c0f00500300d41d1144008401e05242a0500509580115003650400d40010050762110785170308080c0080e101019001c2c40310700c2480600c181340003440d014032003114001d8400700400d40e5044140510310340c0484034540041c00d140c009120b02c946004078084402d861400000c0da480e141d0a02c0c5103031202042812403954051141040348941c100580c400703446010301940703101480d02203610781c1ca0203280070040c860213010543e9460070f0320400d80c02e0194103401c0d048030300020007420070030f07281c1c2c1d0712000310030060040d030000981501d058028140400c8000d800c18400300d0701c1b0f80351f1000070030025040b00215500c1303180c1180540d442800d000c2c0680400c4400314640e500d00000646040741940c04680035080c1e40121001180b03c0d440b000c400860542040700858104111844004d207020090552201e02d40710300c0b02034101240d00c0700b0b100d00c013030801b8101840c1c2c4030010000744 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 194258354 1250 194257104 194257117
    0x70c0611090918070b070f0c080106081002032d09060708220f08030405060106090608070512150a0b09190506040b0d110703031a0406030210140408061812 68
    0x2a50038804216a0f02d0000c81e40d10078088040191001c007510740c4000c900b030382d10203141a90140d002000207001c0c401074030620001058420020002c80b460a29095101c401c1c0d603010a65856000c80022045856409201d9040350110134001c0685076018500d0314118054880b85e0341c0d48601030000380702a00441d8064081c04c5211080074040c0c980480c00c803e11078425600320b510b05d55140359003000410740c8000d0740c040d0744541f0245c00950305060004081c90401d40c48502040000d80600604642202c12103055140600c890200c59507500c150078000300e10300d80d0345030b04014070301400542d040b60f2401802100d00103c1e004110f00400e00800118803d190007a03641c00310f030400c0100510800c01008010411807141c001c921861564405183c5400c07904007680460f4032400402e204401c844026200164200c1d000c00c002801c54010030018034000c2c07a01824060104140030b031040340c0f00d00355402443c10204585c9140b808800311300c9240707009200d0f04140c0c4261a00031442d4807030300e0140c460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 194259604 1250 194258354 194258359
    0x110307030e15072c030a2102070f0308090315090f070501050903060a0c180b030703050c13050402030a09080414010e0d031407021f0c020f040b06070f0218070c061109 73
    0x20540380c16030040080c022800600c1034520044048a00c1c0c0701403003032440190103020565064040b01a90160701c507c5600250111340128030180310180d242820b147c1500c1e001050692a0442440880e00d40300c07a4554901c00d5040140400c602142e00040c50042c03c2d00f410199028207503650015034060244840301941608a00b00140300c00c0380d9a03000510f050a28a80120020141c0703c0f030540550194000c1d200c100c4001003040300454060040e0b9401c0b43c5041c607111301e0008440c520710b0105502c4d0080d41d21407034000001c40d505807816004507403101c1d0001e0300075958a5985103000703401c419250303540d400b00e104111081c1003032a000c6004c20b2030907010386a81e009441400c14810b503e50103010106d0b80403406030300c2a00d122840c0c001043c50520780c0e4442d41301d260064010040080862040140300f10b0030080381c10300c0c41d251f81007950070445c0c0c8151718a000148900c00127940415141d05c80076042d120714100001030703600c41103241002e80034003020880090041c0070051207215041d41e164 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 194260854 1250 194259604 194259617
    0x606050f03090a02190303020601050f1003050619080a0c060e01091a041a0a030b040c0c1502090303070f1103150c0306130509100f020a081306110307030e1507 70
    0x1440510316400550744111840190b4001840650000c0e4809030100c00307514a40148000900402da0100041409080102c07002007805448100080c107011410607142c08068135200803a200d038480301e00002c0c07140308007034090350099114420075036117a0540009940c008241400000c0341801740c1038002d426807040c0d64141c81d2303900700300d40410710604002000d5941a070410000603011303040d601001c03640d041408680e0361080300d450010b0540d00002c8034180f00f1460312003401c03482d58200b401140c840d0341c80692011843c0200ea1184028060302c001c50303805000000d40c0038100b02444103d9031007248182880d884045480342070607561100b8841c42102501d00714042160301c0c003840061603200e0001030402a003440e464400d04244c0e2000d40d00514103038441c0000d442140759a0203120f5420b2012081107044c2051240003c040c0c1d240600011098010141d9420503ca80c9402107a10307005410810766803030402d050010010701107010a0310190060702c0c42901e0310212a41c2d4135004240513a03070207 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 194262104 1250 194260854 194260867
    0x1e10120212030706020f0301030302160501120e01060f0b0703020d0c0c030f11040f060807060c0c06030b0d0614220f020111070515030f0106020f071406041e1503060605 74
    0x1d841124042140c000e4801482040005204c80c002840041e110b00d400c544c49514501e00039152141c848501c0504004c1c0380c3e018003207642d1018840344010001c0c0804a0b07028501c0b40341c2c80c0108820b4006400b100102800130900d10355000052099612a900f110141c0940728405c491341e11409800800c807010344982000410b103000c03c0100c0550051404022190982d8006401c4401600303030324000c5a00c5083c1001480700034007900c801040c0078103000310450380c1903640e410041041d0103050705155449090448c4e130348409010f00100b40d807100741085a9409000c070603c52120868000200450511400800c0101e02103040c80745640503490518900b40c036401074506a0a10f4201d120f10710a03050b0008142c0e5072090080021034042c100d455590425402c4103240b924160081f9041d54400e101c007200c5100000b17448002c81d1180c0c000b10318074442010005040b03100d180d1242c020b2041c00c0c0c40194142010714040005c645442e02078092206c070460782941503d003a4481c080c0403034414400c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 194263354 1250 194262104 194262109
    0x5030a080f2406040b0d060f080a05031e07051b1f0c060b0f0618150408070605030a02070602030a02180406050d020f03030c030403080d0e0106030f03031508061e101202 74
    0x200c40c020000f06180d06083d16120f501c02d0030b800c81d80d035580304582c8510080100d8442c6a140a020f4034000001c1c0c07403032034403949806039640705520b410742000e05100401051030301110240d420850b80001a1051101854280319404600160042c41420307148004465903000201201011030292212241d101554035548002c006000c07129420841c0d0000c7c10380b043d40c458004100d909061860301c01d241c1d04d010213003c40c0400c1141501c201d8402040700f031003010000108001140d0f058a0082d9032036403500c0d2202d0180c010b0080c0201458004018002200e4140e0003a00f0000041041c40c813000060000708010b8601034455179400401d6160f820b0050b04203c19a84601580901140d10741807070701c1106440d50388180c1c015070340040c01054041110700c1c14043e02c080314600700000e022050454540d107a0342d4a605030000d05040e45c030809016648600b0300d103030000300424000d4400c285441765a07400c410300341c2d0125940010901002a000c403c80c601690107480c0105120441d2130815401d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 194264604 1250 194263354 194263411
    0x303050115120c091a0711041a150c01020406080601020d0f0e040b0f0303130302010809060103020a14030a0203121308070b0405010f050f0a21020915160203030705030a080f 76
    0x3c2c0d203400c000203d000821740702c1c2e00d103044801020715200000d61350551820040000004441c10724400d80c100381c0e0741c1080700c044c840103038009001124079812145600607060780601c1a240d001000d0f5001150000314650055030641c400d1000b80c013560100000b0076002c850045900c1403400c045031400c48070201034101580140224000584000c809000010003c0d1071500810810103c802c0c4045041c8210b590101c803080c1c210100c100145210350456002401245850045141150a00710112103560302001103c48094001c1d0503500104040d40c0c04400340d0340005403410401d0b0106000003030800f000129041200c04207a55039003018200303001100c2c6101c50301e1000d01044020f20800700c08ad117545004000c81c0e0750585031b54070400f84030702c548451a01e10070181ea032101d00c140400c1c4a1034172240d000401c03100400f580c2540d15012035154001d190362200300030b5010301c00412184208000040145030000043d1511105607442c0203042205036030417610070003580300034804200003090111 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 194265854 1250 194264604 194264621
    0x212090118060b031005090705420909070305010305120a020703020603060d08030106030b03190503070f05070f0801050a0501051f082716060e06120a091a04030305011512 75
    0x741500c2c5900700c5d600e0600d068071400e9908000a41000d00200b1951801d44100b00250200c0c2514042654074000b07030880719008a035200c102101d1440d0110002c9200204440301600c0040000c01a800c140f03034001e00070a02408216164860078507010640e400703410658200c240923a004100341d0b400d60f828084180c00c0a05003c1d045070b040e981050000fa452409140a0f1071560740c000b50600842d0105890400c000c01040c1880790007102c0d03000401d102100301c8400d5038102481002030f440c1450054070b00342c160741c8490303001501c81402050000c019040a400742a1200c814010740c0d880f2000c000c4e82035540d50050407550b4090030940750040c000d41c1d4a80d40039104020400c00d10950821454043c10400d0184d04103400001c140003d00580103040d0024010794900207201210540210301c59100d6181091044160750380006c0045600c0c3d00b02c2d107103d5138048103168201c04400d64003d0744800c01c0c0d4040f8003180c1440c1c000314a1a01a55440e080000b441d995031884000e0722118100134400107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 194267104 1250 194265854 194265859
    0xc040f21230d080c0412030212030109150b03090624030d2d0207050d02042909010e0601020c01030f150e070221041419090212090118060b 61
    0x500402160009218032801c5151070341d040e8901c0d001021160078644441c0c00002403111400a025501280206580c140d9200408900c800f01181c14164a846048541010500000400400d1018143d004030040d003a03141c0c155201d071500c031003c44440d40000c03619243c00c0d41c0f16400081240105201c0428005042e40c82d003032886202402184c100a02202d000300406c02c84520381800b45403c040d0b044103541c51400e400c00510032080000d49942182c130409201d5545014802c040d951240e20111058114090202c64240b191440f50031500d03030001214031030107160000080c0c080f4502e88107486020141d0180c41c000341c2c40030040d80100920708081c0b042ca5640d141810580320481d104e08041d191070500d168007807500c0c28000b840c00003001c000a401c41803166504c030b96400c8a07019101519008000d294400180b0340204003081c940004500a0140801c40010340c005070741d00900004100c0790503606180d6824900e6400e0ba90301204031852160007108040105405901090030700100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 194268354 1250 194267104 194267159
    0x60603060a150201020a080a0902180618010e07020c06040b0a0503180a050c040e01090f060903030b0307030602070209070302090f0d03031d0328050403060e0a0212010f050c040f 78
    0x45030320ba405400c03846403140c030242c0c1d0300288100d40260084d80403030f44011402418000c021032603022507000c000d031a8404159211490208000d50382d40d1401d18964401d80400640310342c2d541901c541c210701c05580795400350003610202400c2c0d06001c0122015696008106464000c488c0c0c000c40355503000406c07001d1b02d00828450311110540070301142800900800c02802d404007401c007040202c0740b1000078080305a151803110000100102c8400c00007d422803000030703101c00c0c1c605003540541030f0320344400d9041c000c4c04c0010040140342c0d4041c0808074000e60304900c081c0c1d60400107a08900c1149100766000b01040907400351441c0c202030040c111440f078a00403030340c50361103003c0340140061100c0300030042e000810706082c4055955115100300d40000989400f0601d104e801a0051050340805091240c07038156221500100b00101c1010507800740c501c21894003800d0107607000b401001041e00c1081c0c14040400e1410b409c20741501c0a46402c00044107001e440c06100d0071034150000c44480ea410314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 194269604 1250 194268354 194268359
    0x12050c0406030312050603030c0d03050c041502150901020f07150f29060711010f0c0507030f050c0f010e0d0204090605042409030503071b05060c09010315050603060603060a 76
    0x100c500031a00194401c1d01c521540c021081406015100c0c001c05850113039006100d802490400020101070182c0d2a060015054886101c0c000c810b200ba034101a880d1381c0751503613407043d455002600d1002e80c80a00500c1d01941c80c0c400c401401d0744609103442e2a01441071140c0c2c0041851a41420072250034880002103201c140c2c0300117000d0721155070480c40e041101c0011072000100c9074584d00403040044500e60311340645542c0d240b0345001c034400014100101003c2442000d400381101710b1a090300301e03080301e80c5540d807480c28a5030b031103400b6002c5619024013041c031055801d05e800003810303c840507120000a10282c1c403d201a10003881c00681c0d005444512034004260b05105407800f45006200c03034484c04412420310170504442141921945191035004008240e000c0280c2c6c0d00426140751140711000500c018200071b08550304003621501a035800d0100c0a4011001851418000e1301e0a000302d80702601c2c00140e0310510b00c500f80d00031004200141091501e100199400305004161000c09034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 194270854 1250 194269604 194269609
    0x6081e070f050f010507170a020c01030509060103240f1a0301052a0f041202090619090c17071e11070b090a1e0603180210080c09060d0518060106080112050c 69
    0xc00803641f040c40d801c0040c40f43d0409505008160001c942800d080c000340c03c0040580d0760f240300c144005800080c5510350580520400702411000044050040c4015841c030804100141400c0c100b01407100c1e8405980625400d040c001c003440781c0080201920b48141001e0220090181c0c1c00440b4252481001055210b48000d000f400107403075031500e41400007503540706000140c1d4002e0034403445180c16003424550103401043c3e00c0242e4222000129401814070707030540c0c480ba146100005a041c2e19010411900e03440719088030b907182c10755000d000364030341c140c8151542e0350fa500c3d00401d29000b050b001e0000c205450003d100040c400341150a00d141d96543d001c60724090950103015101140c98100300740355140c024500d220208054140c0c06001581c0021030b48000758100b003060105000018440c6008101501c42e40c42c0302400c4140e03500b0000848900038007003207880e102029416421080b08880001302c0c0340c16242d00b611461616400e00f202c14401e8401030100f00c85504c283e402000720354 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 194272104 1250 194270854 194270873
    0xa1101110d080115022a0a03060c030207050c0a050f2b050d090902090105120709090203130506011d1b0408010207060507030c020d09090903090906081e070f050f010507 74
    0x15580750b030300c0d210a0b5040c040e0b0418515144003400f0110f60102c0b441407100f10110145950702e03190800c5403200c060314100810388504941d40007502862606100c032a004c0d030541c0040141034070a10580b00401440420440303404024041c040e0001c82e0b8040240030340c245040d01e210800c070705110300e42c203010203d07400b428015004070017140c10741c0040303100402c9030381c1001001c005000307050011340c00c11070010f00080550081d42a8800d0308000f08022032885401100d001c03010b400e4602c0305560f20b20f08060640280c0d1302030742d0104c40901c80c5d94000a44060611070344140200c807000c030004261903c01020441c42158103900302085000c010005440e4400d100500640340308e030001146500c0e0080d0f014040301c0f15103070603200395081100050300e1158481480c000366002e00c00d001515010504040f071300c401c0300c0e400031044c0034030300503000c100c2c03240c0001c405200081c4c4000c040429413070703214881d40f0fa00540c0724000c01500d071440c1c00c0c0242d02e40344059a001070010325008ac208109601c4481c0c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 194273354 1250 194272104 194272123
    0xc0c040f0903230327010c1d0303040e01031b0801050f01030201030b10021216020d05070503120c060105040f2306030706020f0303060f010903020d1a0a050402030a110111 75
    0x11a58401c070400c201a000b507039040c5014442e00c0441007406441d00404050b01c0300900c070900c07540f0a85c1002d40902c0c00010400c0b05c1d000014020000e040c00030b0030203004001520040d601202e0300d4008202103250001c220f805072605c0001c400801d07465070b83c0d070a00041d900041803809000103000800e80100910030944601401c0c40905040c0d4503500000d01100c0d1403010343c41c0210004040405400c0d0009180e4480034411034034159105d5800740034650308003008200070340c00162189180c00f4804000303400b5050b24411800e80f12003088641c4042d00038411008200c0c20760b040680100941d10300f960003460640c640c2d43c0003041080f60040c0409070680504d891600000c00681400114102080b080c0088e045a000404080d810886d11035540c4c0801045984140c442c1c181a4100380d2256450000071640500404040c2d8510315002e45050341d1030204035550107460700003661404003401600c3c02990040c000c8d260341101c503160220341e00c60045040303040c00111408d6103100e0808100701500d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 194274604 1250 194273354 194273381
    0x21c050d120c0801030b07080723030f0603010510030303202803051e0408070c0f080609011107260a0f11030a0f050a02073201020d02070501050c0c04 66
    0x7400c40c146015200319440c0d040e88004218041e001400025059100690840c0843c03c0042e45680d552104452000009040300f034095030901c100d1405150300302c042d502034040241000c07101d90340c00092508a8401f01c9403e600541900d40400100e40264407030b40074500d503144c544600e0601046203001540c403101d1983c55014030600364245500395409003000714009454107024609040008c003038803012070301c100310000c90f1040120381000f5488049035112680501880501c6a54039020303200d0700344611485240d80a0040000d160300d406114000284201131348840c00e002c1d407500c2d6200c0310000001c400168100700c0b034040e26038090035070140c0518049070307489030320030152400028401c1030b400c032170102c3c0e561090060610554001c02c40310920070251030a642c036501c2d25402280380211a038048059600c80c100c1d446041c3d641d0090b2680030b02d20205030b840d03000141a004903076882401c0745440060b001a030003070089612a400034a884555102110b04100c5650300003012900309500b0b0a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 194275854 1250 194274604 194274617
    0x414070812120a05010b0906180d0b01060906050903060f0703180b06010324090902010c0f0506040210020f07051302040911071e0308060f0103020c06040c0f080304050a03021c050d 79
    0x902c0e02c4038a10a2651000040070103020035450117500f134545c1d0261000c02442440081241c8035105d030001d940c0010000010400c005240d11030411a011900c02e001d0f0030000303620701d0004581e0318012011135000040181c0103045c0380d60341c0144480c203400e014080e0742c201902c036950214080d80d5141d1800038a80076841c0c1d40440d051120000d8202c0e080e0848a407210444200d012441042086590085a151a10105440246200403101c2c00d20062009014400d54a00c0381d042c042d0010f40e16100e030380f094484004491406006030303951321108040540c00d0b4007101c0103010600784180342d00024a5007103005800c140e2214400c0050b06e040c0e00260900410108025041c0f00c01c0c0c540303803500c501585801c85410352035a1001444444d0040a803401800141c500d5882641300b50b04940c00d40d41c404082d01c546003040d1a189443c55001d12903c00c03d805081004203d803c00803080f6812140024411032400e80346600b03014288450401200e100042d084214012903410302c030300c07503c00000c0d54941f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 194277104 1250 194275854 194275867
    0x603190b03070812030c0f040305031e09093702030f010f1805070c0f050c090f130b0c19120c090302010f030203060d050d050a0e030f03030414070812 66
    0x1042115100024940700794002141041400300225220261303181c4000925680c0e035440e064090305201d41c4202911010000500005001010010702401e601821107407000e08200d01540009005100406500018620100d50980e0346985401000b18032240c80c2060045030286030429410142c4d00421b90300d40010070401c0c014100c44802c1d004d000012030041045050070041415526010fa00d8080c040e40c9001289200380502294442660310005820050f010392a03c0c1d0340780c19042e0103090044810b000031400540c80c0f400807621852164070007056a50103034580381c402040161140406180801c184045042000034207804005680ca65090036040d40c221103041300d02421780c0c1003c0005042007840140c0c5e20070343d100d410400a01c2c0c0035850f07071114400510140c800c1d0000610b148100e03944e0082c0345802c000078110002c06500c44a4044801d00c051540715042e00c0c0701c101c00e98004100180000720a09034004003941b9010854035216100c0a040d403400d0341d60640d101601f00c0c0070408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 194278354 1250 194277104 194277151
    0xf07060b09010f0314121c0b040504081c1b111005090c090a021204030306050f03060c03071b0f0b0105120319030f0b0315150306070507030c02010e0603 67
    0x30291400c40503106092558584181c1c2008090705001c02410305a86000000d9094803c01044240c40c0f143c2c403440780e81e40c110507210f80440700000005c40040c1e0824040e219a440d2034840d0034440c4e41c10080151801c0005051490301201074481c0301d400c1a560303040140810032004079a071410744c3c04d40b0b950301000d2880c4c5032503185c0310070414000c540302e040c1410030011403c085800070142e1400d490248140c4c0b00c008050010740101c405140c3d140c10a24100000d050345504128129142541c10204c000841e005060701c600040300c24500c0000308001080c046881340b5201c12120038680503800d07440880d03603a05c06d01030b08100300603134413502a40700500140c07410305400784519a28500840c40c108600b1060148030b807003905400b09041c0e4071202c04180791015081503641443c000d0a0b21200a180380c0c460614190503a0a6040413150f420340b107106040c00213606007d0416070f1101410414251b504441c0c050003624200d04001140020141588075080518040d00c40e510b824490348903003459 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 194279604 1250 194278354 194278361
    0x20c1905071706070504030609110d0303060f0b0717090f090c09091008150a0e0708010e0c03031204110f120307020f100f0c050c09010605070302011401030b13060906020f0706 77
    0x101c0b282d03d0304100103100070b441c0c129048808480e400980031604850a050100090181501c007540101050044004040d416401070082e54151502e00449548421142d07050b805501001020031010510010740305201c40040c120020000b03017510314907004e01c070100720486c030b06441c0f144507541c0c00b09010b44145021145658030502d8a010100e545142036140380d0b036047c59101c100c18100c03a10010984411003a0803203e40d40e001c2400b02e40d00c05a0310b044681c0200301c180801720081c0100890f00d0220318011040701da0840281904042e0b60703c80d51124101c07004600c0c011948650108245000c0391511003034689041240c0002c2e5488036050b00501c0b03440e4015400d584d00c628015070920201503040a8001110300251401c00d00d408031900c0d109103401100e1100d01c0c1d0249560000280c40c07503000d00240100c6109900a01600d00c2800400249138003c0c0401000c00799030b0710000352002413000718100600c0c001c540202d0a031300780c1d841e260201d0303100030b1441001001c0061040c090210301d00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 194280854 1250 194279604 194279639
    0x120406140f07020f040b031902090f010e060111010905060c0304140105010b1e0417031b03040f03030c08120a050a0e06090a03180b04061d0f010c06020c190507 70
    0x445103440d0119a41800c4202e10480e40c0091280c00004440041510740703510400180d24050101e030b401e103018054003902c02e42002d004a21076110240003481503141045d5041c102c800020302403286445281c01514003104440b03096110350342e12616003021400c02c1003000d00070389a1001c40e5650b070a044c00c0c403841011880701d8440c2075a0408004002440c0400c040701d80b0070040120302d40c08580c001941014611a03548945901900355426020681002c03000b0540e0706001303004405201d4001e00c11580300c0c0520310403011520741d00d90040001c68001c0342d0351a0a14801c0c08110324282500c07841000320003003039a4110185640d042000409602c1d03210705040b00007510010074051810081c40c43d43c03562090401400c0140e40c0030b0700b444043e00d1400200240400080e0b041e1200d8503644008d201318484840c0002c52a002004011a81403c000c04000d001e03041c0d451702604142600c0e590003a500a540301d072a40d21a4405040308114410301c450240d034850300107854040c0c1f4101950910007200c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 194282104 1250 194280854 194280887
    0x30e07062007031a06031506040c050705030f030105010f08070f0c06061809030311070b060d050106050607060227300f07090f05010e01030f05030f030f0703061e06050c0f120406 78
    0x104641d07d00e130301c145902000c111008924094055001c480d24098450020b260340301c0030400d001a90012009103050b50800c2c0e07170744007801d206640d04880003001614207102041e003c5000420040c803e100030710031180240404541301e41d40340d8202050021801c05940c1b1640d0702c20100d4101580f5014a43c200f10b9403500c0c4905220060326040d503040d8001d8000740c451404038080a007040342c29000718008010042c890f5859200909281c0042d60010b40020421200d000340c03000c20203203445d0550050781c0b0151070307003100b43e0b502d0f6240c20013180050307122040b10f02c1408404c10280300410401da070701500000605022480d1640c4101a5003c001650303482034100740051000f4242052004c0c112500400708400302e07042c2e42013907400c500c00c04125903203c1d4400000c204044c0960000a4019240c59030104102a940c24080001c0c4521070300070400000080b204005c280e10600c060050303032820f1020780304001c5a140f00b8500e4521990030302041504041020031513150003480182015504c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 194283354 1250 194282104 194282113
    0x70f0308090d022e0609060e071e051602010306030506090a02040516050304120905030d1707080603060c0c1609090b090303091c05070b040b0610030e07062007031a0603 74
    0x48200e98940c1003600090303a4003442d841440c9500e200c0c002d1700000014020440100007680d00e8092040c007800c0100c401e40c01066441084800d9410900160707455220b456903003904201c4c105102491908900800303904141c1c48510100205000740051401350364201c004004280c8503206110544000401d07910f84405820a000324030f0350403804072984258040d001d010406100c0f10306403402030050300400d4052050920405426800c84d050400080f40302881c03c02c031365074420044a8400d000c0350417a03055003045000c500c0c1042d00e0400340044400713400640340144c0c560002011038220580c41000c107582c44030711391814040c00071030454220035924082c524501d824520107680c0e4400d0708201104404402c8441c1c8680d1050050f1804541c0c064011901030426040c15075111100313442c1c552003007042d404001c0101d8068410b2014008005001c2d2490381c2c680306003582e0b04e1000100314003c078060784d414810041000d014240c06544102c1031001c5210360510802e5820710000c01090180e1311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 194284604 1250 194283354 194283373
    0x60f031501080c011b020114221403060613051513050609090a050706081803031005040b0409031209210c0506060a0608150a12060519020708040603050c070f0308090d02 74
    0xf1041740340b404290302800d00000180c411090244144a00162020800750240c0d50805400101ca480801c031010700307047c003007041c3c0080201038480b1b4041d500160b1005c108407083c20080c805402259101c10701030b8515180c070090101148481c45c3c0c6110401451f55180d040221900d007940f03000e904078441c040245001c1001e5a60543c0d030745414003c00c000d110202000034205a9050031010482e04620240c030744030300f05029041428000f034091548078506000c0c4c1c900060810303102d09041c203130300340e900c02c3c4e28940c0c2000050024100300700c0540b0107425000d039185200c3c52080d8181403010059580302068403060408900307128003e001c503441580f0354a010810302c2d0f40310f20010b800408000303800030340c0340034100054001e0101351f0084a01c40c901d18168403e001043d40401e200741c265400440c20180c03140030500480c40741304002404403000344070602070700740709074456a40807031540b10280c501900c1e034840401014948004030f0005541d4420070540c00030501c0b011070862294001080800c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 194285854 1250 194284604 194284637
    0x604030f0305090703061107031103190c02120111031803070807030e010905030613060516170903091306150c0503090d020303070602041707060e1503060f031501080c01 74
    0x100009030400400d034039000803a03e114800d20040c0000c581c041800c202d401402e80e2541d42d141c001c60010b40204041e0341001031000d0021040315800d069002650014100d0844d003503443d0590301070107036005030305981c03000d030b034040240315110712183c3c903120158480c6450143c80c130400b040c02903524101c2d00244540e800003829602590f07122a0f040c1080160b2500d0100126404013003688011f916205031824882001e0a84035005e22460040c0428070541e40d440800075042c5405a0140000402500744000e104080c41c80301508a000711702900c0c50044c0c0000021502022141c111080c282c0d00c0e04100480034440c108071400152034100f44048141944804c0c1d200e00132140c806026a02d030030469421035500340708403044a036004504644403901c070450a01d20701800301c41000030344100140810418010b03079082c61006002010702c10700703e81c119012115074002403c02c94000d040c0c4040b00c4025981070040b90040383d14a40e42c40495894a0900c62511008201490500002078044002c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 194287104 1250 194285854 194285867
    0x21071b050307170109170a0e01090b0406080c040e07030212130b0402040e070302120106030203011503080304060f0b12160902070f0209071809090b0a020309100506060c010c030203010314060403 85
    0x1a5503004004074030303201c0700b03000502401c5051001003007904010045154520070002601e10018540e88d90101003038118015150b4501501400944c4070341800300b00304642c031501d0340a503c0b180700f00400e0b09181d5589000210061b00741d4015012175004600b009031603a840f03c40c164084c25041d00c14900c40107035180c04d4218507024001901582d102c6400c400e0610007080004021540a000690040b000b105030728001d00f1540422803180d420b1240c014030122404491a06070380d08041388500e91b445981d01d0380d004000b43c62681072440e07194aa84c0320302c0d039101d562000805d03500c1c101401440e6a01d070b0f075024403104079801601002c3c1c814041080170408003045652519070684402c000c54403400f205848080301c242c1180300c4004401008150082c190300404100c511039070344c8006540390300080d1000e81c00102d0718540141e005444e0980608219089680c011030043d005600c1c040180740d6882c01d4500085400020a4001004104100c08226144a2581808050306540c02d03d680e008140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 194288354 1250 194287104 194287109
    0x21b0a0f0b070e01120902030f070618080123040309030b0c031603020c1002030402060d0501080304060e221e0c05040602060112020105191206060e030f06010f05100221071b050307 79
    0x11540d8440346c004646040000c1080e1301400f01c21180001d42e650f00050005c1103134058000150b00041d03000071064414050781c115803d18803a694802c3ca25540e9003850108011720541c02c21030494030010100e0a40480c4500501a002c0c48507560b1074a8000300710680c0580031030104151041100c0740d007800b40419003034032190b0101d00141e07881e00c0b680006040e902401100c1c0103003a01d810000503006400100a0044401e135031a07210400b00c10f8010014809881c096503525844010350705084c0041c0d80d842022100b4104c908d14040515600d40e03d01150300859001d800b1030400a020b1000940400146006041d40d0112450081003a40000c080d030140d51000010a007003030302403461070390256001c0140c0101e800c80c100b000c8c503038500f001484c0384c0c88032410901a000382617814502140104465058071040b54130415898074003000d104c0245500000c0c0001c50007420342404807807007140740000d010b0100c403008503203905903810090704001034400303800b8004032034504c1000f00343c0700420f40408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 194289604 1250 194288354 194288387
    0x18031106130f0b0403170306130f0e010911011103040302031519020c0102030106081503060103030e0d080d051e011d1803121009020f030a021b0a0f0b070e01 69
    0x2164204203003031001c801040e801000c0b40020100c400b0441c41121409001144e014041246100c00510201c15030740c40281d508036000f05401c1404441000c0e541c00440d2924100c0c5000203c04454280d400d084070500042210441c0e10b004402655683c0100c0d0141749080806c00b45150501d0b6a000030340d40c04400042400780c1d890b0b0000164141d40300703040f45d103003406000300555480007040002c5000b580b09004283c085a140d4000c0369025004000c50b600300788010b00180310607421038601f500e10000345000140d011b980b603d9104005101e034030141005110400e004907403404c140011203d1030920841310781ea4a0f114070010441c000b60152100200c00e1614443c1005031a90444003118224580a0041034440010b480702c42403e204802841804a00c2c03664000586514501c0c0a80c814507080c0c0500520900214100702440d500403e02001304900900c0c20b2001c07002d02509100c95460161100c0404e46002d8050084c52415181c0c4a500e038070b4080071350220000080c04014903000d6112 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 194290854 1250 194289604 194289607
    0xa080402040e07180618091203111b10050105040209060703031806061e1e0e0c0c0a05100b040203060d080a141305031b06270d110118031106 62
    0x2042d041c814032214000d01180e01c4200300c01100000d030807000d03001031b1184200c00c006091003406801060f2140e9840c1603449002e014010a045a088019140c01100039480038420803020100d5210703c08284440003860000c2c05038a206152003074201c9005a100c00c0c021801000b404c00c455440200b00c40082d80c0c0b500300061081031180c0003095148400c08001c01140c5001404140300c141e5423a04202010020308890184da19200088252011490340341c100700d031040b1083c42386038030280d0401d41c0444a074828504283c02594154a032022407001511240c0142299a12404180c01559501e103c203480039491800c0600114648458490001d0100d4001040c1340c0e801500c9517490004405046100e02d841b48a941100f4402d6800e0380700c3e1070302c684112198815103d07468150101d542c030004011320304200c00541d420071000a541e500300000150071404100d2980c1e0003800e650154090b1088602c860034440c009098180d50020803950000c4030348042000944910352440c880c0d0040c0c407120b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 194292104 1250 194290854 194290871
    0x9151e0108010803280306180204030506070e0102030301061d1f090e040f0809030c0301060f080c011e20060403020102070c0b0c06190b09011502120a120b060903010f1e020a08040204 80
    0x403401401f60383c00558603103020b601e1504104440390003034002c0e240503200b40d6440c0d403900c420a880000e03803110b40300e001d41c20a0004100f218001c00e440701b80101e103040d4402074051510b000614400030f1040c1c40c1032080c00d0115040642d644090b190b0068561040c0955041c202600c42c00007000380390b0b100400f1103000150740c3c0a103480c24403001ca241030000d0f0003880345070f48850b14a20325403030f18010074500340320318041c0c07900300e40c410181120302108003a620310183c1000c030811640700391484603921102c046103003071039490301c03080041c184254003944c00107890b8441c2c1c2c54015643e01da554040d0100031810b0100c560416030204040e9040722204403442440d0b03009409040c00713011101101507000710684000114000e000c8066803d005c4a642500c071143c120303d41d5007521f4003e4030210800140240c0b2a0203810401d94820f48040c00010a654105144840000d0031340f258010100c1c0b01c070303469817501d20721401007450f81c0481c10100d000a42c06e20071502c07001000c503840100007a12441d158440d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 194293354 1250 194292104 194292107
    0x16020721020405090607020607170105040504030509090c04061805220f0c0c05010e0607020d080402010201060306051323101e060e040311010603020d0209151e010801080328 76
    0x5150010741c0500180240c1c5420400c0545440e42224490054000d0b03400103030000f403003101c104081d488018081c0301ca9134241002d000c001c100060040b0144903041084d6401c60343c403801031910428914103000d5031541042c1006040d13104049004000c110140d4041c060342d9540301c0908a1001443c024000c078041c0910a90007a0450242214169190815204c2d10300d41c010074000d1518010f030000c0c454442e102c40c00c2ca9481e00222103941c0103030032007005100e401d44500c01160b0098014400032a1007512520703040b0403100147d50702d0b41078003001032401041010300528120400c42c10940380413511281c0d00c0079a1200200624290400d580e80300003000401c5038142d1242c2840c00b4241003050945882c130580ca00503094a05601043d042d9408a410750300500070a0203480e409020311208000580c2800b54044000d4001c501d109107100304c0d00b00340d803540f854600040282807103980358a40400000b41c05402c06800c50481a001041400350718403005004100a40b280202c091300c031519a0310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 194294604 1250 194293354 194293409
    0x10050a0e03120a02010204031b0305074a060301060f1208070b011511070503030703050906070501050c03100815060f060706020406050d2a0509030f060109060806160207 74
    0x3001c0c0c146001040d0b0f03103000e40c0e0560240041d0380c400c4208244100040c40b80410f034070158070004120b075001100070701c1003c0d00c11b502c01010110020007031010103400c0c4051034035810000541c2c0e910a076100500c140b0700d150542800d80200c0c09070000c2000794141208804041c44c079001d0410000303542d0207050704000c00e00d81140c1e201c1760007000381141541c4800a10088000024200300012140400c403101644085001400c40d000140118071b0a903081c0e90030707103240d0825511194490b2041c0405000714400b0b0180d42d03c50030312a410580d40380340c0810818129202d542240c2c42076445444070440d50b240d10018950010011580840c00c40d0074800041c129100d5190020030881c00800c00082058102000c1c0444200104003840072110300301c50b40748160000003005913681d0b10122421240b030300500c0201001800901900c0c0020701d80d021051420f4420b81c004160181c0d1803200308490740c400e00c44984c100310110703d201c0740200801e000070740d43c03c81e6010303060844442e5650501c1c218001c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 194295854 1250 194294604 194294623
    0x6040b1b030907050312040803070201030903050408030703030b01020d0e010c0b0a060b0406081b0a02030a08091614030115060f080c250507050603060112090609060203131110050a0e03 81
    0x125000c0d620b141040700583ca80c80c0a10400b406489000d0641d1590460f03001554196a80b40d00110304011709500110060300e1030402c19000d03c48200008201482c052006003942c9020b500e01007400b00010307000a141440c1110750500b001400a101d0702a40c1e4000d148814803a00060400500c1c0c82c0c011489006014641c005c070402d410000740024038a4200c04258419034041602c07519030b54015040000b10310a040501c801600100804104980144141074000e04440300702d035a030316100c1c0340081442009410000402411029007803152600b4000c503c16070014500d842038462425802408001d0700151420900c4082000200c0f1a002902540c02c0d0b00b014801a610328002c0380c1c0302d1140e10f201108103079120b004520001c205801c04d032003241c0c0240301c10b9507500500858150360200606002108903286500c44d540b02c0e010070881d001942c024480f40c0c01c1e0011034803c0d0f02c2d2228804144284050103104491240a01150410203071559171b1403504001132500520720001c0e08003190352 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 194297104 1250 194295854 194295901
    0x30c09120319020f06090d0503010b0304150507050912010b03030301120f0b040309090f06060f0f020a05030a0e030f0106030f060507020f0f070609080304181e050a0504061103060306040b 82
    0xb030104500990004405110141240640300192150b88041e921003030089021004110200010880c0070f08541c02190303c90302405c7d141c08441800c0f0941c00c203680e803c0e1105000580d011030700600070701c0c000e0300b080303003840591000700032203081a000704e600c030701052088400b2044204600c00500c9080407142c0800d5501481d028028945031601074005030507405a001007600d03081441801c10300a1190703609aa1042e110360a082020384400c45052692001c01d0703045024040003074001580400203400e90b1030340c645812191f07080b203105061604040080d0444175a04000d01000483d070742c4065000000d40108020640d42c0d0f440c076040c0d01d400c00c00715002005114145031001d02d0200402e00c0c40a42d40c0540e100c1c0c0d0001d40d07071003e040d624080d9000e52001e0103d40f2011946e4065150301c0144204c020507458280203035942024401c4139000c8800b09582a00c0c1c0e020441000f030184509010511100b41c040d085040a001003070382c1d03000040008020361640c501180905406c680d0040c4a104074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 194298354 1250 194297104 194297137
    0x115050c100507080a0504020114131a0a030b0102060f0403050f09100f08060a050102030313051c0302090319080306090c0c01150806012903250e1302030c091203 71
    0x2000c801c03200800c811500c8100254031680170030315481040c040c9600464050b541c048076405851001840c69108a80c1800480041071000402481203007040c140c030568141e055131905088080036050311040384200341103400440c2000b81030710406c64010f030010781500d0110346590b15080901d50314400e544900b41d00981d081a540c1040340e01c40c03030120410f842d642d00c50380d4580344c45c0103002542c5094016280560420b10014121310240001e8041c11303170181046400c0100b00e09481e0f0314910b003041080002030f03000506170019003400c1001c8406606a440c401c0041c2006481d00d02c441e000140445204009840218526004000c00c0e201d10a02001c004c00141c500c69001c0c2c4c404480d50312841c0d01e075003d0880002011211310b0358a00900001450f548850307101c0c1c130200280c541c4002e210303556180302c50508403032000610002c034490f1710142d1181c2c04c4c6610100c042100c41c030785006400c812103004000308007000c1d484c5402e45040102c10340e00c128012001c0f0303021908601583c200c0402300d466 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 194299604 1250 194298354 194298373
    0x7020a050a080d0306150c02011407020909032d070609020307030b0a0204030510020f2203150c030b0f1e010203040e040b010501080106020105090a200d03110d05120115050c 76
    0x82c0418a02d0000030f11361410480c2640c0e071005480c080e880c4011400100e00b0300b9551300059400380e0b0106524140504185141c10034036400540c480704196500030103075001149000c0303842c0d110f0401202540250b500d4043c038496a480070715440c42181002000701e52521600d40454808020003030103190700181074086031074015500802908180f0054980f4071071801301c500c40c0d5480c0e00c02c68154001528196152000c1c100741c10403503042c5a641080c90380c0d80c0c58000000304112a0038a001c10044c0200800c100d003e5400003004d0301c4940c100b843c07003501c41c0803552815907a240c4090121308880d503001c040c103200b248010307820350266034002c5420700401070410041110110303031a4103891090305c9003030300c50340c803040202c3c201c3e10100d51007a4a6804294a5804a100c410300c145100c40c082a800074080e010b030002c648180b4881c60102c1c0030460100842c0c0c080803081c8403c1d10714205a103441401e140c4c05c0340c0c54070070388041880707000503e41c203803c0f07800010741c41801211409150001107592540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 194300854 1250 194299604 194299619
    0xf05060913050a05090d08060904020d020307080a03050d050f070f080a0e0106031104060f03110f0609060a2a02010909110903030a0504051825020309040608061008030304080f07020a050a 82
    0x1310488201819000e00c0d40521001c43c0140c40540c0959000303031000740b15a40740c4d42030040503090b00e44180c0c3e141c0700f807400008840d01c04200c4030329418440d59a45403500000d050801c00d071140074022001c1d1109400c100040980c1c02131056940d90030078a0710300c0040d151000400e001303102c0d59018194550900b4404001e0002c8052004ea1102c4291010000160b90300c500031802207240c00b0041002c1c00001c0c03240114500240c02c1c0e0540b0b03c0042c0b1a0f40b4040c0d07003070005151030780400c00e03490103d0349405c00e2501600795007481119020040e101106800d46550001300702a0070780c01034000e0255140001c81019403054150303602e021028045030755912f00c4441c0035081c1d40081c469070b48110b03aa4a80110646010002c041c06442801d00010f4125566030000402c40380e8114590110b1000b48030b40282c9589500a400007400d030741019002d1411f180a4003042e08080c0e030011500c6610420034000001c3c1801c080ba8105010502c80b151a00303550320004681003444d0b0301580c1c0c0b00c05182c1c804174004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 194302104 1250 194300854 194300861
    0x6022104021002060f04031101021207201903080a060b040b0c100219050901020a021509030606030f0d08091f0f05090c0901092708030115090f05060913050a 69
    0x110300864440c0781c0d2100d0208100ea5842c001c81707060600c024a0400719002a014441207940030440400250500751a1043c050301c10a00b112110001303010042000c0142c00205a25100e05102101030031034810070040e0341e1800c0c81032281c0241006160800100103a040e507008501500c000030106503965036440280d0117542101800070a1170142e290004000b24207803084170354000d6808001c40c00410103c0c003d07601c0d6001021924154040c3c290500b0059071000b205c2d14030140d0b101112078840000c20141803800c94010f050f94000d9000c2817810b64628400642060509802d1600010755a140b52185080001c000c100542541d000401c80241142c0b98004140d2501c00c00c0c8d0805c91a600c5440e01e41d910021032180d203410040142c0184004801c0d60480c614081c03008540e050003180745480e450754650f50140644298502100510100d80310400c01b205004141c039080b5410307402c00c0302c3c1060805e42c600c604e0348505400209840d858a0301d820301410780c9400c00040041e80780040c0310b240038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 194303354 1250 194302104 194302111
    0x2040e040b010f0e1602010e0601170f07051f110d08150303070b0c0306040e0a0c0303080c1c0f0e061f050d050303011a090d0c03030306050a05010507030c060221 71
    0x10107819000800e01c54100c0c281a0101e4160320f12998154036500e02580d03400c95800d107890110b540764090880110420031000c1e001308100d100d14034441e001d207000d440c1400881e10505100340c1010604114079603412000601c0c000c0300583c40c03c0c05071403101060b2a12510b142e00440d550003070514045032260083c05040c4102006c190020030171a0384410152030341b2821b032005103140d0480d80030400d05500b100c081c59100101410015451401c00d1000740f8000040c1c40c21520b00c82d035240d0034801c15900c07a20703c5800140c502d0105041682d14000c04410341c00e400c10101c2900d507620288094410a9000000d413404004145c034160b0511030303071040b40458404001d04034040b843c80009414180030000320940e5030032101543c05c59003807000307546045100069054440400b8406000d01c2c5c0e4803080b503c0c03041c07481022034100d820b10750314000d01a11001d920441c40754580d004100803a903088000c6501941d403510b450042140d0301c1c503201c1d00034000c0c0c26a8071002c01a83d42102c11000405030700b0ba00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 194304604 1250 194303354 194303363
    0x6120804052403070309020a080a0c0f06090f12050106050a1805010608310206040b1e09090406020a120c030e010b06030103031e02030409020a0e040c0305090606060702040605030102040e04 83
    0x1038824182e244030031010000e0300600d142c2c0d10100700207070419120f40e0000303a0300b0740b0042502c0c000e103071340342c03985840c2c00c04c02da2064440c41d013007140411048100d00300c00320080c02d00d420581045450901341d5101a50144035040c1c018521b1803007982000340a5102c440509402003a264140d89c031008000c0e041c900c404d900b0200a45070000200344103014102c41846105699581c426049080c0241648000c3d0300482c000382c04141030403a001130351200b01810242c40411300311902d4419442c0c4a22000c0f610f03540b22000810204034810740d98995074116a0b00c290840300140c0e44482c4a60201d81d074a00c1442980b0245161030316588103140c1c180c01ca50402480300d0300030f01c54600024100000380c4030a100c01030201d0306c07a80d02c51041c0fa07100641e00140c5d26040c01900e00f0a9620305400302668003c0d041c88001039118149081c030751a082c402d40c440c000c15454200000d06d4000602581e465010381900d201307a0003c00c19102b1592942c102c840548005002903407034030b80d100c00b0407480d10826602140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 194305854 1250 194304604 194304619
    0x10216021206041509060f021902071d0114010c0507031b05092401140d1b0507030206010b1c09050a170a0206040813091d01060b040806190612080405 66
    0x928414001446800fa0b1340029400354410513014081004150007003044039101d44400300601000d50302d2000e01107170805405040e220b0740c007040b00241170207041d4019141200607892003803c202c01c0024800e05492030802c10311f180002010060350681e00300500244240304e8030750040204800e820100384400580030300080314503100c000700070380e58400726200b1580b50103102200d03245600c400e041c1e640c594018100f420f5440c014003512a0943e0010402201d5541c0303c101c001d05800d0003006642c10f2070220b240981c10b001070350b68001d44482c0184503030900c01a0205498070f041c1611441c1c143d10622039074040010712981e1038801c1c1c403a0040384040c1d600c103000c1b25078644ca070f0384107000712036201103a54040c203120750b0380382c0d14000c150704031004116418404a802003200d80b01881100150800d042a441a0b903028023000c03400d40d08180c010900c0405c0521080000303440004900b6040500b24031304400c40c0d00d19683c550010200e40d40104401c094180703d10b41031045c40c1d401407056034403e40c0c800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 194307104 1250 194305854 194305879
    0x17040c1707031703040606030c081501061b021011011d0d0201020705100906020f2703010608210c19060f0501050603010e100312020c01090504090519031101021602 72
    0x548612903440050b0220f8143c40000c1c82000d151001150b00c940701c0c21000462039101d490b001c43ca0b1030140c002e00066482100034180401c0e03c1c01200d4018643c0c4d01e0f1000e210241c8a40d047c5040300900002400b803008540d4510080f8085c0411301e81c0c0500200013040640560403559030100740f00008172a4500501010080b182e1041c000c4821003a0004e00410548208280140040008240640e40298280310716202105403000604540c01d0060b08030b02e01c0f4040d50249242105140c2d240781c0b082e0300d422400c00c107080c00480d8058a208060b12804007a1b40c3e103040e50a00c9200f00d40f0f040c41180a02d801603480c20326003000d0900918042c003804c1003804194000102211420700405502500620040280414406041c0e43c000b051a0501140d19a242d0b03502d6001c10005030b40c02d015811541841d4080c0d42e1002d0320000628040b40c0c20301c1491041c1e2501d07520f501000b00082071654820702008240341c090f4410b600400702a2000710b594031049401c800c01c0d0111038000320300c00c551b00640c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 194308354 1250 194307104 194307149
    0xa0b09040216060c0e1f0c080a050c100b01020d1707270e041211120304050a140d03150308160c21030914030c060d0603020303040f0801060b0f0a030c17040c 69
    0x81c90840c211b90348851058244a4031000c1242c1c1185981201f00f000400110200c188148a402c41c1d280c0304400100b0300303015240c000390a00020202800407c0340b070388850901c0700e220498040d000004c80c20064400032400c104c0011409402c0451460909107540015801d0000c040d228842c40c00b801003481080c8584104541c881c0c0c00f209084080d0b80804903d202c884888c200075a086449003040b155445901d6446240c03000010b00142030f2a00040074002100741c2601070301c441400300402034400700741142d8814203d0300032812010124407420308024200881d80c5208005850300340300242c0c4c1d815500c50800b10080c50759204070009018042c0015000c26402e940008044008015203d20000c070000e00a098025842c00710130302e51500700010168a080c80148003601d07100e04a0030711182403200e503a0940300301e9444400d0b920000c1151442d05122102610955a01460301007640303c21900203c90f191114003002c480b81c21200305000820426560010803241c140c1012046080071041c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 194309604 1250 194308354 194308399
    0x1403060106050309070e1e15040506030102070305040e0606090a14041526160602030304060e0705060406030203040f140c0112060b0409090c08010e100b0a0b09040216060c0e 76
    0x55200c4617a000000500002c540c4000003540414010b40c0d42884030004000c40684070010390306020350b580310750707254070f41428039005455001c0c4041d0700961400020b03a0f0010000c1c03150380300c2d2400801d645c5003c96942d40e505022038158030402132140803401d442b03034040c1c040c001070003a03903901c15880c007030100c00c800721078101707101c04c88095014403420303040340049801d501040118210f12602500c0703043d5103c011503840480141505078019600c1c3c1c42e007840c11100f22194486000c1d03060b80021000c12050392600d00b10350aa81a84c500981c49469619001000511100c3d004051010302001c40490080001d0402c07813001099a49030f0840000700e601000f221403502070048045000c10090140400c660041e04036a07100d25840300e02256241c000c03908407031802080d400150000b80c0151804030711070142c00c0204e203040768043d1081d481d0a50b019868401c06400c64007aa8011811000440d200c8104038030b10de4203c0c009100c2403207080c4004190416816200f803040001c28407004581d09142c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 194310854 1250 194309604 194309611
    0xd03060603050c121b180111011b051e0f070221071511010606050301030b070207080604061107052b020102091c0c03080f0d0c08090d0305060609060414030601060503 73
    0x1402451324110310311200609000520b098803001914244405040035180206944080c43e100d4003004410706c000104890341c6503111162503814004203120102090120031400022800c1143e82c40c40c5114540340e49144d11284102d1100c008502010b01700d030910000c11902e40300700c444201401440d81101200e40401178504100c4d13200b19414440c1005552580313000c40c50700d0410b011182c0503c0036481c00d40740340784c0001c00028004001002005841c2d050181c0011183c0042d06c841c03402c080201707940e40c50040011303000d651155004d00b0403851040440d013540d6001029503404105100303c3e810104c140c10650110810906410000d091062080c0e8805c45001400d00d43c4150490b0101560b070b001408007610f107070710300c0000000001d03010002003500c5020268640d40b505000c80501c812a0501182c0d4030900400b801004080180820750301040d4400307007000210398803840c1c00309101b40071f80d1103400e0b04240006004112a064210030465460303046003111440d80e01e41408a50600098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 194312104 1250 194310854 194310871
    0x24010501031b080705030a0605060706091403070b160512070f1107050d3c0507050d08090d03050d0213081606080c030a14040b06011e050f0306040204050d03020d0306060305 76
    0xf4008141068407030300040d9048100034001082003500c3d0b90019100f030388100011614140d40302036001c20413064450940c86d541880001c1c505000395611100f002d40300c0103008031841400104045c90290060042c4d400300203000c0911025880d2a0070003800c0050702000c81004544100000030942d00000395140940c0c0019080e1000c0641da503030747c03c141c154540b143c0c1c0813840c0c5000c641c89802c96440c4400092000b06000303000d41e2041c13800d04c14104030403a0000390040214014110100740413408481513100103035105c108406031402c007102c80d40500c12841401600000388551080d01e680030441c140c0718000161540859030101c80d05000d62648220408078803000001005c400d00700d005160b00c44c03d022400301d0902c0302c1c10b07d0050080c1c0112811103c0c00025014800070756400709000400c0f5900015410841c003d03408003030224000ca0032010390201c00040003c43d1a143c2da01558010f10001e4039200e01007986107000f0b5118403031030190303d0009107409400a05240701c0e0143d00e0184401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 194313354 1250 194312104 194312117
    0x150a090b06030102040f06050c07120b0a0f020f0301030206070302100606090314031306050a12020304060504050c03064302010c120606050405090705162102010504050309040b0324010501031b 84
    0x80030002d541c80e8201c49d0380340c01c070b6010300e4000044114604a1324182e80c2d200d522840d0240c504440442e041700e111804076000c00b17205211004094078681c0c1200e0540b0340495580ba15000c0344d00c0d04a01d040308419519840380d00b448000140c1640100032002a41d200d155084030101150000c60354a008440407540c211071550b800700322030750040c2c00a01c42d1907040e2500c035804888050303043c01170340e1060b2000ca4049550704c04100c140035003880000312401080303000d050b40b0b00b032039411001c1c10205881900030307140490054170100640b600306045400300c1070b1207103010041c0e4041d0181c02042501f0405000c50002826559070708075510862051342e005844031801e2070b007407505004841c440286038a003031140402c460020b4100040881380451310070000116510034495881200302900c40c03207502075a0408080c400003440c0407040e40c1000e482070710001201c10100e000079280103095445411032002454100950b0030780a112035041e14400c1c2c8080c030586c0703665418101030203130400034803000800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 194314604 1250 194313354 194313359
    0x21f17040f020609061e0406030b03010507120e030c060112030806030d02060705070c0b1303030318111c080a050a0e01142d0d02070204050714030c0a02150a090b06030102040f 77
    0xc000700546036440000d050315082031484411081c0c1342a201b40c020020084c0403808004d0160f050094645000040c0d000744590305040101600b80ca070b06c104401d5815440d02c02c001c4405404005441c850407500080381c0d49943c0d500b10000302462007000035000980707100001605401d00003501d0107025255402080c0750b42e41d40d4411282500051000c40b0b041184600005509044002a1904070017940101c1c0605103103240142c101c8580515800f5464541c1529001003800125412050101501d941d1000f000c240c410310030b400c400801c010320000000c17900c1e4894a90103000740c101c0202e280c8650011880800041d81c07801c03000301c42c903440784604000c024501031207080302010000107a40030b0344020070586209c3e48203420852011162a602041c0c90781585054082c8a8105c205400c0c00c011490a141c2d1064942c8001095045802000201c0c400c1c40d91003000034072074500c00645048440d0030607820340c030040c0c89002025901031800c070b404210b8a241c18801c4804032003640b1541d000c5c8a2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 194315854 1250 194314604 194314609
    0x601030b18030d060b030901140c0d09050111040608190b0f01121e090b10060234090501090b0f03030301060c030509040c02031c0b0105070f0609021f17040f02 70
    0x1446090716800030300040c40f00e003002440c1c80c01040041c15401c0c0d49903440381780c244459400c4503207100034045070540c50020b014036001c007081110425481040c000c103042046092140c09008407038841c10301400c0000b4000750180e80305c114980100000000e00d0b08400000c0000d2043d1442540030f254000365540d01c0c3c2d086903000d16000950016642d40c0841d104509080d0034403440d64120700f0340e40080d2600300b164100320600e00da050307102c03c03458031a1400504210000307507940994101c10002c4140f25612201002e0642e80d02d03030160184150701c0d61000e0f165150300018010130310843c1030072820b05071030041d245004100c60070038080150085045a18100013180e40041200f810f806011040000c96542c0c0c42e58020500e100b1000e4000b1955103020f4944a038004100001c3d2000c01803615040082a0303902c4011244101c0d040303140c0c0440c43e1142c0c01c00100030036070f01c10000d5200d01564511001d52140e41c1403221341e02181d88900d60742a075182401c15828204850040803170045540c0c400051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 194317104 1250 194315854 194315881
    0xf0309031002030a09020918010b120303040f1a1003030e030303061e12060a1b05070503040b0307030204090c020a05070b090a1502010b0604030b06030601050607030f0309061b18080601030b 83
    0x80404d40701046240081e00800c29820090701c1a00d00300d002c080791481c407000c09010b6001091801e03248603252041112a4a480e404080d0009018101001a440c1800403e085211003445132017aa040c0a0504c00c03101201c0711b45511088001c140480c4042c0298030303000c020340c0c2c071034000506081c0b45080412104a401c0d0751101481d503106401580600350b214041001a06c503e031064400182c424451503241d403e11003011468040110410468000034008401d031401c5038a0140f03015101c0d00c0d4180d06801a004039004804000d00c0c200e4000c42c4642e001903c03c00381d5010318159071405803030b14008a10b51080440245e00080c00303400030000c3c42944142c2c003000082c18800000c2c2d02c1c1542c00080c0090f0320941c0161020b003030410900925280a008040c010001211100d15051707899502510f1022800c82d40d01c240340d036840000703080c450325800880d85510a0714600301c102085034000307001c0d51040c420141d02c65501101c0801c50400c001080ca060300d8208440607001c0e40d421140c4001c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 194318354 1250 194317104 194317111
    0x5160c020312040b09090109050601021207110603090607030b090c0a0c06090212030a080a18020d03170c1c090f020d080405060313061401140114040312030507020f030903100203 78
    0x107124001000c40da07040d4902c0a44040e204556200e030f920301851042000800c01038100600d41450300092044a03038000074524090310b000d01956407250524180105d0030b000c080a01500312000100700a00f8a5000c108144190720310345040140710348107130a111002c00125004030050408008650100e4020300d840303540d5a10448001c98031215550103c1c110298120002640d41e00110f01d41d1581c50300480815840800031741c2c01c100e10002d4a0495055400900e8081e0040030301010207014188100141e405994405d40c1c01011803c06150314400c6901c45c540c1180c4190003034801c021129450700619403039030b41082203142d045e10150200f1080e0fa80c4224200d540d403908100010f503607281c450240d0710440600c18501151081ca0074003d05640000f09805031040b119001840004000c05200c28400028070301448900010342580744c4911440c1c00260400000007405401d19078103800030341c0700d483d080c1d00713448120f040b60601581e030b4090801819855040180324aa0b0010a5400b4562 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 194319604 1250 194318354 194318359
    0x60301050907053010140c07030c08090105191112090a03080f042c0117100506220506030c01021c08070302040b03090601050f0f0307050d020d0c1e0905160c02 70
    0x180e4010300c85000c4c0c0b034401070b944040c000380d44401e001c6003103001d031b602c40e1a4071000c0f05058030f02d89269554022314184807881d00404c10000410081032592280e01a103004103402e502c489209030920602500e03c80b1030440d80c0c8a0303481002440490440520180c400d409400b820b1a801c4501307507660f0700700a0300404c800900c0c80005201c00901c0c403500700f0506c08071800505420451900366009090900016002515008590003400c200608002881d041040710101c00003600d0702c131400002c0ba0403884420800b0360f10220100009054451340c0300a01403c411011101070319501401a07844900904c40b18441c0801403078850180350058020581c01149441d00601e070545905418600f504143d440c4a40c40c0c0c4840f00601140c2480c01c0500781c0c08400321041103c1002c550002690b55045008080c0510310b00f00d920000c5480c2c10000c404e503140d0003040b001069480d44400e10300c0902901c0d10b07101c10440c500d000100c074a100c0c490a4013469000d180030107100310080d419505080b00e00400c1f40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 194320854 1250 194319604 194319679
    0x127050603010b180106020705060c03160c180b031b01050d090305070c0e07020705040b03070b07020d12050a030b19050105031e070f0e090906071b020904080306030105090705 77
    0x4002ea8512100414001090710344c101e065050890003842e0000c0c03508124010710040090344454070000054803644030782422402400c44152900c1101050540d02054203030142044145200300243c00018414400798200d90300a86641e0181500030003602075140071400400103003080c8007139a0001e408190003400c1c41da103030003140d5031904140413003580030b001d0541c06281445590340e414030004004010451707050101258640009848107032070b210300082200c00180c041d045441e09183c480d02c1d1034010fa080c11001c00d0407d4043c0041e0302440720780c5d0020b85816810759840c500b803041045030014629041d03400c1404c26006480c0b580c0050b00c0344040803014215504007601e455911441602c90765601080042500e070040c0841c265100268810740007881004210000000c8036030384403030b980ca480f031180300349107011130304c5c181c0741c450080d4010f01d44e28100020f02010400950251505070000c000c15030307070114201d4840221303016140e48103c40f01d5914042c040c40001c08840002c000c0d0815 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 194322104 1250 194320854 194320871
    0x21c09050414012607180506190302030d0509150a08090d0318110402091002010606020c0904120507080c060123030303070c02040c03140906040201180b03010603150302060d0e06012705060301 84
    0xe0003060444130030043c0c2640c450040068a082209884004146003031351303071032703824210341c00a0f4580421a04103000c121010820010980c0d4064162151a00030402c070356541d5520744000340380741c2049904542d107218880c0481040d0b4428071880c0f1001401c02480300480b0002c0d034450113181100c0b030800358029000c1c03185640682d56544e101040c90030350f40000800600d8180f001e8104250a0506485002e1840400001c82c8000f0301c0000b000e0070a10301156552014a02a0f066000721080c11546110302c0c8004a02241210a4242c094180a10307194200c1045403c150792484212403100000308613030342050060038250091b155444190078042030b140061400e04140040c04c58003002a90f101c030040c4829540c03c903120301d84007007142c03040500c800e0400d0305105144c481071087d1000c140d03440c0c0001500074031103105c00c17020315030040c840c95958071200060b00190403114201480b6003c0d90000085000001c00092a5010920068003070088509041c0c030080c00000c0c0031036090754032400300c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 194323354 1250 194322104 194322119
    0x1a040c03060b1503181023060102030f0d0501050a09090503090904140a030503041e020a12060f02030a020306030f0c03150603010f0204031a0105010804031707021c09050414012607 79
    0x313548903080950895040d110031110651030024210140e5031203d00d458206080303d000c40148290f0496a50080203050311607000407460762203007607080581c000c80864100c840140d60340226048a07400c50740c221040b40ca81a41408032110110024038070341c0708001240701c0b4140806030542c898000c2031540c6100101010850400c5082e20048000030b5000042200b04840080c07040000d039030b07800041502490560202c4c1c14085680540d601000314852070382c04004480d0040000010001c1040d5145d05104040801a400a951452113401650340c1909000000248404501001001020a1030b15000100c40500d8080d14068040d52101c00140c60b85540780028001184200c4c90703044000820107084031424010303001035040054610038800071030751140004c01020b081e66204c84071502c43d110241e240c091840849400151038004000d80d0a070081c2c4050100e84065406110302c03440c405410034804c800340030301e0781c607100b12808600122812894880d0907945010840b5161600e6007013 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 194324604 1250 194323354 194323357
    0x31e080c030a0801090905060601110109050d08070f11030306040207030e030d050a140c060c0d02070b2503050609070e0a090203010308040302040f050402150d1107050102071a040c03060b15 83
    0x48450300d81c0c0c80003690401c45540f1001c818010450440708001074003031603030b845843d680060041741c10880071800e40c10421500394454924643c0c4201110f203003465811000d030403141c044915001007a0313480c0708500c04c036008920f800d20100090024624565560003004001d401c0202c1c00d60401988450520341c0e52000c0003e1040300d0066241c103901d030014180006c0800700c85140c1c2c801e08940c24451743d21003410024070b1035086024260919114071049080344006c0c09203c0f0007501501007001401070502c4a51130840a04603045d200740d4090b01c1000090f8255001074403226002a0320f0300000e442644216050360710140300a1108001c0c3c0d40d0f580505084e070f0002e07001030b11074007000582081180f40034403541c072011504040c140800c0c0b51940006100035410f00d03560103484000a8110321805407540042ca500b140e0302c0d042d545545090508500030f4001c80c0040b5200c55266041104451414140714402c0c0c1d4841d60004225045a5445001e8207005507031642218124565504442030b030300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 194325854 1250 194324604 194324617
    0x10c0c090c0e13050a05061005030a0504031b06050a0e011503021009030503030a020310050405060d2a0e04140601080d03110f0c0d0201051b070204021608030c180901050a031e08 78
    0x1000c1207a06085e140d11040350380107011144681070401021040d103400000b0f4982c0290b15104c00109075403642001d884d506071819510140a015122020400c4004e03401f550050013829030410803540e02c1c4000074200d6007503010000c01462444001c10040c41c200c0400c4403070990034500301c140650380342c0d2000e2454200340d480c3c07201d403600481001110281440c0b601c006200456003805582814004911007507079000000d040b405140740c08800710344541400803840c0850f0301c0c031210071707030b0b44c130781810a0454050301c04a4440c0541d2200403040303200024028143da0038000a4000d07107840ea101500144088850740c1c111003800d014807d0030090010180c0449019a0060b103080300c07548000900311400100039401140010b151010426006015a860640c3c1034034016500c01e001500c000304450001e4004044203000400c0200b004200c002038080c0a903945003404d8002031800c200890a4801d00860b904200508000c101158101c1803202c42202d00da10f01003030050b0039850350f1a40d80d2025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 194327104 1250 194325854 194325889
    0x171e0d0b0604171c1b020f0a090213140a0b0319090b011e081b030c0a030c0e0a050106080609041a0405061609050604030b09150109050114010c0c090c0e 67
    0x259421002c01d0041c240700c040d000054000e92140c41340c3c00781c0040b02500c0040c0b04500032084410454441d80e040c4440c1c514010052884c0c00d03644c40c00311000e5809082c0c01b4920007094400054900318200124a080706c009045d031100500702004990f11382c000410096002c01030500808851303065101c0e10100c01d024180100c1d03558101010081080d8100d110100912b40310b5804010510340401c501100039898030741040c40440000000b4036240c4a80030300c2c0d600100741c1c2000801c001c9400d0948040303400312034540c0782e40e98400681c801210424491400840c1024000541c5403804d02946540144507046044001c4000d4041440144007218112042d5100c1d509001c080c196010f01c00321084880d02d4082206400c00c80401c0040c0100c0c400200120704003c080f403e1807500f40b01200202c010030060000039a55850350001810080c8074050941d030310412001405e503c124240c8a0f410b4204118068403403815030007000501e01901c540342041020f079000007181d592100c0b8502c02e8641c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 194328354 1250 194327104 194327129
    0x513022203050a0b07020604020307051c05011d010b0d150504020402072004050a091a042f090c040e130203030f07060e01050903030708010e0c2104171e0d0b0604 71
    0x340390540c000c2c00c0103840317081035601007020840103030380024800040d100280e42d111111849082c3d030340c01c0d000344240010507039400e0118101520101480341001e90001c03c00038005d8075103140034441c4103903210f900070b0146c6d40d045008030362482d00c0b03402064206202803c010300d00380e0251585400e6102c1c0c00c084a0b0520010710860307507189000d000c0d15030040e41c05a02000101d800d5074030744850781c0c00e482c41e104030703903c0c0d52002509200030101d90703014035010a4030030342c0c1c2c0f00300440c2001c1800101c1a6910711807580c03040030500948000c41a6016200d0b80c0500100d980c48000c2001c15601c50300f20202d07458401049112a1541080094569075105080c04191080500f00f42030035118000d2080c012903209200304000a903104003080d044072000c01c902e40003501c07030107030307094080c49490401d01306c000031003c14842403234615643d01c0c400c0b0300a00d020340f4150380d10750901c0c00901c94590b01410601105103071000c0c40c41080e0040440c1d44030204005044441e51000c00d14a4225074000703007407a510f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 194329604 1250 194328354 194328373
    0x20319021f0e070501081515040801110306010c03110c03030d0b0301110901020c130b0315070f08190c0e0a0f0501140a050426010504050304140109051302220305 71
    0x414541c9401e80d4528941c1c2448010705802c6200c0e500c080900c039103810054040d02145a04500c2c80130380c0c80700d00c0007410346c10000350000700003c065441413048000d076601c0c3c24000720f00c003511042542d0141405a446618040c00c80c0c0301150107450202914029003e905c040301c0f000d940800c020421060441700101391400040105800c40e4200001ca514405080042e82c1e01c0348c0c0c1c0826a804020f008961754001d40f01c0544480c0010700741c0c044155098466107804080d0316001c04452032084031035130b07071300e8440e005001030444029070f040d40c440c40304c0c0e8490810012a58226042070901031520310f0080c1a08081c1e0340020781c9000703144c3c040341028030015001e2069580c42008000d03100c049441007481e2841e0800028481d20852241c101000340203202da0107186414428001c0c441e03c0140240010308103070800c41e84a034440c1c07240410f1201c1905c400c41080d4050101d01d0110b94005180c01400880b444402c000307540060005d4003daa1154030442220301d9074a121800ba600403001000c6580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 194330854 1250 194329604 194329633
    0xa030926011a040b15070311030415020105060f010f080a1d012f040e0105090402040b040c02010b0906190b0a0216060c03030b040b09070e04110408150105010309050d0f02031902 78
    0x4020743d413070a014284c1000b01c83c6a28084400312600c955251905c00e0a000d0708042c29400c40c080c0750804000021005200b010260303054201c580107001c1100c0c0c64460424800040d9140c19441103e007021403545000103005a03803036401108810075600c0940140c00d42c4c0f071141801c44903020040340540c030316070020303529000342c071403a1b1595141602c48043c0f6190410004040d120014420580324103c6980002e04540b0b4980101c100210054018401c03040501800b0b406414040901400b82004c2d20019050b46004205241c464201c0c041180c000c5003004103019065100254200c12340c8500d41231641c224211601e903000501403a903d514100705607140050a8039007110b104c61007941441482d11132550351a4038160800c600d428200d1122b04040045005000030b50035940f1202d00205000030006004109140c01c1c1c014100500c46981c0ca800056003159412031015107154000501c0030200b0b8011000c009507908075004503420050401c460500c0550310004003401a04060050500d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 194332104 1250 194330854 194330861
    0xc0915081006030e0604083a0e030a050a03090c0503061006020c030309011b03020c04051003020102120c0c0907210c020d030608030a0509040e030d0b120a030926011a04 74
    0x145040c0c82c05004814013003115550b56000a000945400d90000744000300a00481c46248280801c2c06007003a06410340b0302e58246401c00c02d0500c000103040c1502c0b440d0b401c001000b190318070b0080e074680d50300700f020402d0214010b24000f1404c032010fa52400b17022070035680401c40039202c0d000f0803428103845820b10600904044035070846074007a81c814040a6a96a0001074100b5280c0c4080c1208455440d1410202d00c2c0c60407200304250481d1900080c0052000035594a10030750303000703800319885010181c1aa42491007504031480880d0010044003c0624004502ca81c209080d46400895102d00003507048440e0203c4081ca400c0e039030758480c5d606a954040c0840c0d800814142410000d40e4075000c032150710385c0b00d0081b00307008012002490700178982e29035109510000340c0304c0031640c560400300c41e800300510074100c000344a40600400e04144400001b0741d0540a580345e518150700a02d4003508020091200d00c1c02144802000d00c601c1c40c69000b44a4011404a84908084201003440500045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 194333354 1250 194332104 194332109
    0x4090503190c150f0f0f06080f160308091f09150e0904030f0504080a050303091204080307032105070e0a0605041a070f08030118230a0c09150810 64
    0x70721003640c081d00040740d501c40451583c8010554086403c12041c0d0341c3c00d00030590980c480034010314241c00078800da0410b40c07040e0182c4003040100c81800e1168444117a48003a51414040d4041d02103006200107414100036140c41c010251141020018101010401c02c0e4680704120020340381e00010402c1403034900440507400550b061001c98441c3c0382c404542c0002c40244041d041c4140424a8010f041c400c60481e0300828900f01543e900706500d10b0043d0b141d0f0f10540f0000000e02c90f400c55000701414150444044802850043d4688006a174060725400c80f5501a0320482c0340744204462150030714068a0305c5171032203550f00d03080340c01c030501004400301c0b03107822900c01c200052005110040e200007014011071a80151701d40c0b1008140b6015440b0b16401e203005100460220002456061003c50840880d04203070051100380e4a11200d0304d00380403010f4000c0c20030241c0102140410f0808e80c014080340607103186c1921810303200c0f14801b1000702090400d0000941100c20010310240c1610750001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 194334604 1250 194333354 194333357
    0x5030706032009130e0f0709060e01060306080307030f030b0a090506183303030f030a05130f0201031a030d0f0e03010c0c12021615030f0920040b0409050319 69
    0x140356141001c1000142d1320392644003030340d0b0340d406644107856040219250400c050012541110344900c20580600120321559049102090001c40c0e4240680150802e48007094021810902d00703441c102c0c0c4200c10351242d1014180c0ea1200c20403580c42d01f00300800070b048032100c04a014103040301801010301203102445152215001030040b0fa05441404400e61100b001d00117002803c0a9030003986154401c1c0c026925100000e0103c0c0d10394004800b0b180b0076148204100700b243d482c0c42d01c0108412018030b0040c146007108071381d5001917020b40e00c601700710303070080800015051070f03000031034904900c0251039004140c400030000e080c15400f4844048006081d0005d008094136240042e08400340c07079800800000b101c40013001c4461003045003c0190900c41c640f5214a5500c10301e0142c000600003481d4002800e2050001500c4190301680061075030213680461241c2a000700d60620900144c1c03155409070319400c60a41d290b85038000d070885640200d001e943e4500007000c00100c40d0095214100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 194335854 1250 194334604 194334607
    0x702010e040b0105030a0c09170a0506010e0108030a03020c0309030f0601050406060e0d02010e190e01060809060403020601180605060c070501110a1208040206070f150c03060e0a090507050307060320 87
    0x74810f076404001d49130401d401c1c61000c240e40707068007400d40700d21066400c000500090314000c2100342000080001e2070764020300030348146980b01d518070301c03a0715002d02450700306500c02c00260b6039851090f0b0040c41c1c003650620959060120060010b0704004071000d500c80140e210f0801807006240a102d000d00906083c1403e686000048002c0382c110350703008a01030f050154441d100c100c0d03a19984801503202001a40307041c0100c0c0c44d9000010b40801c28007440c0001440300c00002d400c2c0c14001486030280d41c0507001001d2070f80c41d102da146210100c0d0341051000a072101c03400240c54643c034029103840c101043c05071801c10300b03250004042c4920342c64805070503404100400003040c015000700400824614240300c07039039101c0c00810750358851309070014020720892040130240030121400e02625840e00500340b01002c0140001c0381550000d002d01d8611b1414000460200066135200604040c4a04250740300c2641c0c3d0b0000034140340240d800800401e845c0c021140303d018a21100e0f0070403041040c05103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 194337104 1250 194335854 194335871
    0x1020102160f0503130803030108010501060f022d0f010222050a062f01140705030702070b0c12040b0301180c050304080c010f020c1005060a0819080d020a050702010e04 74
    0x72014500703069405042406440d4550003400428000c9540c2028808605805a42e803042265030b41d5000744180e81c40c039442d02d0b002041842c030600709515040c14036402000140c01a0704000078a143ca1a85d01000380c000d1038081c2c06405051169200d14500a00016111100b40700300c1700040c4101610420702300c049110910499a51603940000c1e00d4007458080410f6074103c2600e000e42c054030004d0200e042d01d44618560801c815044001410fa03100c91000f26610350403420748443c0002e541590158002c00300900c890700d09400500320f018a054112a41001400443e02c00340e13001f42c1101e02d056000000501c10311220031911020492400402c01c035503800b645006007240405040180488400251b400301018250418905601345440c110b545060048000c0d40e2484041460400f003400d19000416070715140c40803508650b80e43c80030b4a1204420300345400b01800d003550888002d0420f0041101500c5c517031000d001c40e468a03030de03003c0c2c1ea2900d5000143c9801000802d0920035402c1c85441d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 194338354 1250 194337104 194337127
    0x10b0901080604170705070f14040b0901051216030f032709020306040b090f1f03150b031c081b1e0a2102280203120612150103060b01020102 62
    0x140f540035400040003c0c0648202c0108034240c0300307001000c3c10074401c8180109100caa03a965042c00c44456440702100b103d015028041a61210500c0030343c0729180b40010042400e10030342c0c543d032031003115058518026011758020307203400c41500140c3c0e640001200031010190800303c030003910040300031080342590080c004020380748030741c0c0200489a40c0210106240e900e45400c15042480028801c900030b182c00c98024452142c1112610340309079503440c1c03284101218440034815240c008000c120324143c24017a8034060491622910342511071011007110022003128403c01442550340c0d540e40c41d082c1040d0480d070700103e02130111107000040024000c1c1c1c80390240b000780036001c501825a00d405807210140c0300714210720f041c01c4a40d17000c821815141c4880354010a10740110039940688020182622489100c0080d12000560b00400050f054015203003003450307114400804400d5041103044203a41480e486002e1416102070900050003003184030700420300340101c288000c50800d283c0144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 194339604 1250 194338354 194338363
    0x60c0303011211030109030815040e0c15040f06020c031e0604030e190b0d0e030703080711100c020319021f1e05070f020606040b0609060c0109060509010c02010b090108 74
    0x5100c1003000b2403800074100321400c0c560140040c0010002c0100c00d03140c2c107014007038050071905e884111207000d003049454502071044440e40441d1900074060100940c1c1444181704041141c41c80d0000d041c0300001c1c40b403014080b8040580701a9010f044000003010915103081c4078900107480304000200881c10300a000194254040e0305890b00344000c004200104002c41e040307200b1410568840b50001c52500007030700c0105060300310448200940018a1070070782c0c4038010f0080040003d100032000c2540c442c03140c200020403010100550b441c2001d01120082150f03a50061100540c0010900384200c0300c80700c42d80300c8103030001d0025005030034070717044010321709001035020740301c450754440604001480300c0250356445400c00008000c681010342000e09090805c0c1c88030740c0180b107003800259090405001d501680c150241c101410400450108510784e00500512503181d035032808802e010403441c0c01580e000d503090310700000d207045c482a002400d40e101250664040d05811004012000e400103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 194340854 1250 194339604 194339609
    0x9060e0f0403030507200a0302160e01061211180915100513090e0a020a15050702060c19060605030d050304050c0609010c05070e070306080115211e060605060c030301 73
    0x43c1c000764595030144107036450305003911044060490b055440b4050031002604d400410f0080d000c551480c820005049081c3c2c5050088030450f460a400401c083c9000b11254003000c00b0b80400441d080c0081d003401416901700740d201e020b1441d0b00f03600d541020b0034070150154110300e85500003940c1443c40400301e0700400d03d0002c1b0704200800010250403640c16107004d000580ba0050303084c40075020546102d60349031482102a03100d20b42906000400f411402007401400180d91101800c081d40790b001c1042030741006498004500031102c5000380c84903543c5901d0000f500c90080014960300340000d061900d074402910005208080044c800800d1000480d1060004100c1c0c0165551300080012900001041c40003441441030210100d44000304400725885240f8590b01002055074600d001803e032100316000c901100c00d500018002c00c0b078041000c00d500243d15107404d20b00c000790340da180c070b0380c0d09205000b00f40561500c2a440c1004a035001e0740000301fa0440c1c80e1814070783e1b04410706849201c1031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 194342104 1250 194340854 194340857
    0x905011e080a0207021e01020c010503011d0c2503030e0c010509060d091a07030f05040f020d0804080706030e16032001021212060925080a09051609060e0f0403 70
    0x20301c00110100100c0c0c04035600d40d070b07000d00301c3c2c2901540030700070212080c00e81c41094058045c044101c2829403103402503038103c13556445144141340640720301043c0e0140250100080140404c05980c1519130381d5000c11007110001c0000c1c98100c40d9080c0141120b00300d07003035501035030001c0201c1e201c00c1c1c0c0c0c05002c1e290031200c126016540c402c042c246810081021481c010300c1d039001c4140081c40458441002c0c0e1103440c1d141c80900112804998540c1191000c4a00a0080d002c4103090005418404031140030b5501c2004403502e0b20782ca030b1000c0b501e030017010f83c0900d001944170ba064101c00541071215110b00c01c1002040b1692a04554904d000218a02c1d20504c01030544800000507a1081242c0032440554119290b42c4d002080d10341c1d41448000c44850b4090790141010464906a40d501804d1805583c0c42218001400120440d2114800341039000c00b01c2d119024203012480c1840b0301d6803008031019003901d03403a151118080c01d0781c0d255400121f290516904201d0000054000d0b02e6220364503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 194343354 1250 194342104 194342117
    0x204060e010f03230a090f030807030e03090a0306151a07061b020316030504030b010e0f070903150e0a0c08010219090b16081308030a1101020313020d03050c0105070305070905011e 79
    0x341711040000744131040029084c40784101d0800d091540080d0300c0c5005203110340e0180114880312031020b0b5240714000f80e1340c0c1c0240d0704540410119080c2c1c0d000d60303030012200714482011a900d80c0343d012800641800321504110015180d810030106103d2036242e03d60380007200380346008500c8003079120702681140b42803444000d1440000c25126004843c05198029103440319940c5076001c0a40204084901c1041103140c200070a000c28013402884044070303403141e2040c0c3c250101d0180f8202812201d41e0a0200b8843c15032841c000615104010024065040c0016120703900f444502420424140040003032180e83d08084c07003024560821200100c00d1420700c184249500e1a080c0c072140305042c1004008400c40b2404100a81c000c401000032996a5840910115012042c5401c074403003a9a80b80401c00c0c040c08800060030b080c142810700c60300030704100303051002d903441301400d5810490f841c40020b81c0d29020442031b290000a62006800286004405940d141d544c2c5403064660b41488014040e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 194344604 1250 194343354 194343361
    0x90605010612140c030709093605070501110a0c0308031e0106052209020c0f0609010c080615040b0703090501020d17040b0612031b100e060c0904020d0204060e010f0323 74
    0x10380c100c5008054910003000150f10b0350704000750300c0b0070047c07005a05201c012822000025122403000327800741c006000d007019524000040d00c4224011100c15002d01400d010340f00401c0052040c98010b5014090031039681c5841081d40700c4980b81003400000c2c251a6400500c407482e4008156040300c0340c80465500b41d511030300440c0c01c43d035807194080d0000b00d00020b40400d000b0401714000d1142c42c3c00350701300e0f020360f100e0034816400c4e0380c512032003640080e0300c1000040d06890020007454041201100703a40c500340d1110800041d43d4130031441500410000700d410409540d04004076030380c2d210903243c164200d40da00d65003182505e002070720103444503100700e010403101e0b55403000c41c0303031000d099a04695031900303800403c0d43c8150b5014106000c6006520208112306164059107000b25880030281600f035a800d48214419040705a11030b40242d800d01c00c416030b0701598401400503240584402a5440c51040018000b12401d40403030101418068505440b00e0207800301000da9850712841d808564 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 194345854 1250 194344604 194344607
    0x402040902090702030a020f01061a070f062301050604060c08090f06040801150902090105040303350f090109020609011d060712110304060f050a03020c01090605010612140c0307 78
    0x21400c100658400b041005210300c450300040203100c0c1044580a607140c040d41140044d00300c850710b00c40d42040300d007039004040c0d5112107080100001c40c03041604541030000b40c0c48890032074110040f42a520203e843c0c000c0d03450b484045500d4010001101d829186c1801d2160045c001342d01c02800803d03204d40031840c410243c0d034843d4005807103440540340c1034855a0301c100580c040d0142d0b4450442d80c102c3c01d1004030b4810b0040c000c480b002881038507024900b80c9180c0c0e0403100301c00382c40324080389050043d4001c0581703601d844120303810089515030641581404c1c0940f10340c03564040c11508041c2e240050700ca00503140c3c202520b8501c207003400c1c2004c2201ca0b00b08018108642010303001d600000010340042084010030101c060f42c491591015080c00c40746502594a00c52405404040398a668030740c0c4066214034000d0264440514015040802669003e820b4540d000c200301e400d26120001480166485203069110280d044418410340030708010665200c0d41c05001110b500c1d50000004031175a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 194347104 1250 194345854 194345861
    0x5070f02090a1b180b0a090f080d030f02071a0606090d060203010305070b0f2203020409051005070c0812060103090c030c03020a05060304030503241002010911030f1005040204 77
    0x9401900414061620380381101c014044005003074912100f00f1104801d103480b0f2811552402410341d851080d8600f0101c5504d160340003c20340000700030110402040c210706240505000303204000040044014518028090300d1044076040e861a1043c01004003040a204503602040c09006048015494070f4000c0382c80ea201e0701c1c0c01c158000c03075059a08410044154000d604070380c01801a80c4400341c40340318412951261001c50351a2480611022040180d904112040d02e0f02000d00d24103001e68980c0440c007583c00000d42694142c001e803408a58200982c000ca5520407038529218542d00c030700b540c4000e500d0040f03000c502c1d47c5490201c00204180d001c2d500c8418125005030000103071946c1d0b807902040074070040c00201d0007031003021400516420802d05881c011070b4540c440764156a01c4100e80035000481000c2c01d501260312003420102902c980038000d0f04105554001b0405205604001700341588000d4107a000381e0006034000e82007280411034546d114405400410030b80c689000240c00b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 194348354 1250 194347104 194347133
    0x3090a11190b210105090c090103150305060f0c1e0906360301090305040915030c060201021e0403050a08130801061d072d0c0b0c0301052404060507 65
    0x41c0c4054840c0402c00104200180c02e481640002610390034140c6005080707490403e01c6a2070300240c0c00804681404090000b0740440794042c900040c22040584514002030300175402514150000300038404400c581d0b001d180e9029044444090cd040c5000301c07540d219840880c80b00e8907003400481d41070f01c1a60b8101c2100c054040c0821001b802140c286c65801c442005420200f031001409444010365040600507144065059240c9500b06494244540050700c11040c0d04000c10031070000100c00a10020410b6024006d141e00060b02c0d0b2032004042d500140354203060440c5c408052000300000381c4000b4460130310590200e0b01e65220900c12031401c140c0c90450b040741049500b0408081600062400301c80031884d02c401080503140c031000d40c01d076079620701c60b8804ca51028468200020700f18000103e00d50801651508172941041511401440b54045d59071007a00c0c0c0b4000010082c86ca80700010111142400140900c0801111461007061080384074590620101103201414401c0c1c41c41d07820308 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 194349604 1250 194348354 194348389
    0x21c02031f09110403020d030302090306070504050f03070f060e06041502010b040b01030b0a0303080c39060c090405060a05090a05010603060801060501050405060705011d160b03090a11 81
    0x440c0e04000e540c1a0010040d00484654507a114800050008890107103541c400f01ea0a1550f00c0e20b4156024030000c5054820260305258080081c4441c40c0c0302088612710811055682d152a5401c110030030004c0c8052100140c4203602001c0240440e1070000f400c0b40c00c4414500700030f403000c42a0808500c030750189038403045074003a41e040c072031284c1c03034040d08200041c000450301002048151001541151081c04089410028100382031002900951520760080340041300c40d410001001c500c00644044010f542c8500d4241c14654010b210780000441009400c080c0505214540031110030954010710b00d03018030075915880483c140303845803c544406010040c02745503044c5881d40c2d8403006060284220000640f81010000d0800410700c610b0080d641d05940b2545050b240a0800520f40c12400c001d5429540e10321100c0d4100b0042c0340b45003c0f0250a40103040c0000340300041e82204202940108241c100030820880d0122000c0b80003402c9a9100c880b503911600d848010032803801c0312216008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 194350854 1250 194349604 194349607
    0x10306050a1d010f060e01080406110c1606020c1c11060703020d0f1803060f11030103211e081b0c0a06060906050609060c0a0503180f0103060302060904021c02 70
    0x3242c511450b060b4100d40210106140340f039998a28403190b00c1c440d449001e000813a00e915195071584180fa2294009008040c085410380f241000e140140d801040c6c41d00440e0b2121b502c58000100201558004061600150240d0090304c001314074440da450942595410365a0b40c00780810030208006160200050316094680c002894060f54a070724492540c0302141140b81041c581c2c40c401c48084100e461560f5000e0901c500d180c0da480d014100200000d09074075111001811403c460402550003103001d41340c400a208030b0707200201030807402c0c01946400c20401946e450050780800340101600c07074503487c102d980d580d1520204c01001d005e92050904020001600544408002580703100140c0220801c00225a40b400514116040b030b01c0340c1e54000409004800541c40c0030360107440d4403c080015207090190340d0380e82900310f40c020744040c00a00c1404d10010811b04210300700c3c4200704c400b82810400541507400080703850150342682d920aa4002400710302c0e10040040c56484056404000d6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 194352104 1250 194350854 194350859
    0x8030a0801050f0306060a21050a03030c080f0402100c0516090501051915030207020105040801060e0703110c2503060911040e0304060507030e060c1e0c0307080c090402010306050a 79
    0x8144400070b210701482020030790701d011414a000700701e0764041c910081001d8001c1c0c0c034044e040506407008910400e881120903145e1710209106010540d1100c1c0f00c0e60b40081e0408900c50068441d460181c101c9995028140401005845007807031210404458102110100913529225140542d400365440100c120620005801140c43d000b05040c1d82007141c01d03c0c9246100c2e030002c02c04004070310540b2241003424240d282468000e0303000308100c90061602030b15003501d40c01c21509640701540710001404024081040440c0d041c03141d9461422042880e1385000200e80c00d00d640d81c40e004110a00d90456145170910300074104050b1402035138000424060445181040d000903102c5960741401103003044169403410401000f101c0c16154107444103424440980c8088031401d00d01034007240c2001e02045541c0416800b049030292601410b403045d4225117650340720506190100400c1e034040d030702a020038400000e000c107401200751020340300e20b40d9a82c0c407400124054244e41e48a2904102c070740030b02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 194353354 1250 194352104 194352107
    0xc021c06090209060418290f2d06210a0b040b060a050901060507080f160203010b0307180f180b0a0501140105070206030703060f14120304031a1008030a 67
    0x14120700032030342d000541d03441c4c40500050750704900c4c0c20741d0034030079400003107000400045022041880d50000c000c401c00341407032070034031790002a240045100c410f10f040103940110340310780c43c80c240301d009108008102030250010365800060310f618803c01c90540e035100036540010b030701080003d800341110486211030402180018055805440c000034171800100c1504091988400f120700281c489200ba03840c000742210780390001ca1044400e141c04014121f252200c103005001e44080852408081d410360b441010b0131280c041401501942298034100203061085003c0d50200610800c00301e40c6031541e50a460007044010070a1000381d032032000d0300090104210b034417846121140b9040045036250404102d0807101038803040d0026000704002070050030104040c40d040403440c10081445a00d443c0f01c40b189604680058595009061088031585071a007800680d0340d0300c03440030358900750940d112403d11444a4030261140c04046c4003241d2580d5103010590028031580c01500c1c0c40d0800c2050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 194354604 1250 194353354 194353361
    0x1020a030c08061f141603090e13030f0309030c06090305040515090907050a0216080d141201091e02040b0d0e010e1f090c03051501060f0f0c021c06 65
    0x48900081d100c04000340650034400021380c841c00b0008100c0d4282c0c0a840c0c402c0310b510318210f800e134030070752424042220781c6031040314811841c2d44251508070000c2e042c0400380d240c3d1040182401a054100d881c2000800d801000c0446c1d080354034580454105c01170300702030b108650b8144c0f000740f42c2490442103c09043d80040a001554800c0741d1a42e905c2102340d003001024042c2808003a0320100e41400700b045070707005000404041421740103481d580c01e0904c1c110441502a80d1004030030f50042a1841249a07002c02403400810345140c2460419207850003240400505024001c0c5045c2d551150080648808008080e0044245c105660711602e6115450080d00032110081002d810305420401803c810301900c1c5400306c1100080881c0111901d001800041591140d030180b555941a840820003400711030000d1802580186070004040903641c9214505a00204c1005524000d4000b01c4d94001182030076107040e03181110414085000040803400540c2d400401c2ea600700c040300c420414070341c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 194355854 1250 194354604 194354621
    0x30e280b13060507080f090120010605030610080c06070201200703030201140402010c02010305040804081005040515010f03060c0e0a140108060324090114090a05071409160c0501020a03 81
    0xd6105026507a5210643d41406503e8000741280010700c162141c500c6c100c400380c001d4210500d07103108442d4841c50b40b45081e011038080c048103651210b40610590408110040e080b41406c8520100c1a10b0724121580b1107010041842c410b410010b00c0c403041d60721072a01c0081c80750800551401c0b40310b9100b00543c1d035010300c0c40200c000d5400c2090000440c20590188c034031654040e141c001c031100e05640110700610b0300601c21100500309200200b000c00082000c141000c10303c0f20009200d00301410001c0c0f40681301c00102820280e5030005210301061501d0000880f41e2024010414102c0c0180c01e582e00d01494422940196a60742c00040486480c05120700c1c0c080d0a0725003103070a03107442080c140c40300346078480e41c2c07141011804e03130711920361119500b194090f00700070002405000110102c040d242042d034900c42c056102403a0107080c480103006441c010f01014540b007401c0c400490105402d41e100801c4044d400440b400c0500140e4001c82d21240c209034008000c5648a03002c2502400510444 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 194357104 1250 194355854 194355877
    0x503011a281d010c21090b360a06050a2d030c02010608190507050414040b01090b0d080304031e050c0f010213150c150b01110604030e280b 61
    0x50846180e00c1d4000c1c1d000c4e40340325030440410b2601820710601c07603405000304210340040100005e4005100032107500a0024500c42c40f0031a000c950b1800c0820400c405e609a280700f4802d1082020300c00c80e0358903120075044030b0f06401c1154071114043c2d400d86d81d41d05d400442e00605c6ca07222090800f804046418000e12031400e8034100010500e0400803800c803a9180180d2201d640000020706110008262620f1070522580441c0d1119880b0070114040ea10b6018581035003041200030b12080000380400140034045c0c0d64001c0240c52119000201c8949030084050700942000020400f494070896081c492160040b1000320844520a401400f980c04100001028001c2a64100070004d040c0220f59000442e5446604c03001d00306210403d400340f20303900b010b060002c0001181e00081501600070300801c1a86000100d1000000014007010860f50117980355030402e02c2000006900b01d44d0303403056200141d520b040c0501a1680e0200c48107038540b910b980d46100684005602c04815008142c0224070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 194358354 1250 194357104 194357147
    0x405030409110a0c03080903070804090c0f2102160818040f1806050c0903250603050123040b04020d0209030c030604030203070816021002030315010503011a28 70
    0x2e032946020350701030b504001002900008801d000309201d01c0125130010311110030390380361030503e41c3c03071100507406a4000240780e41c9840300c1d041000d41006103101840200e0403d8240d2124011042240100401601051540c0403805101c010320074400c1e0b000e1355a2100643d035550b040d01c14803180700504441018030480c104046491511420b00917402140c80000b1112400380d89a960710000c9c01c00240f0452a64a060003d21186c0da070802020f0030208004181500d28105140340440c0c42c80d06812490600d4200b0f4010803240c004040f20085800e07080a00d10b11082c0d480e0001800380110070311107a403040c000305501e21081541c1c0d005001d0413004504076003c1500790801d154844000720707005400750704144105408200c2d80f171700500700300b01048107088004d0216030003d0302c0c810741c0000030401a400801084050000c1c0d0100c07840384402420014255031410a421702444001c1c22007011800000c10410828030301001100c50395855501c42e84843c40c940b0700003c0c40c5421003082c0da1000b128 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 194359604 1250 194358354 194358371
    0x705040e0403171b0a1d0901030323031003020d0201030b03010204140306010e01080a03080405011401230f0a091e1a010906080f04030806030a12032c07060e0d0b0405030409 76
    0x444c0c8102d0080c1d1920856a14140242d400007940e080c0700b40507500300003400303802e4016416030303032009200d000e981b0036218003401c4000a04082c8000d007002d13030510b0440c0710410511443c1d00700700c8880700849a04031003518480e54180700480240501c60314854040d030004c42c010a0307002807407003070b6100008207400f01c4d01c0503a6950f501c4202c2034000c1c410032840c1e030441c00401000c244100300c42030f40300f400384001152500c10088049507000c0240c0c00102034071208203504480c1702c010b03111000c0720030b0700301d0341d550688813035000080c5425194070510078039a030340d40d8007a4021a08000b1075101c5809400c02001201c8160309007042e1030700c40442c0030380022000200820094040c0c10254003444c611094689941c0d00e640c4e065920b035030090845a4144244110400082c0b40b07500c81c0f00c0140f50543d408601d0003840e1903801c00004040c14005a132040c0c2100c21100c280d00040c18a04951042c82d0924491640d5008a030f0041e0309041c011b41020001810031080c010000300500c10dc07008908100002c90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194360854 1250 194359604 194359621
    0x4140f0f1219050f04030f030c030314061011010e06150f06030f01050d0311010203160305010b0901050d0c140c031201050108011d070e030a0c1502150703050705040e040317 76
    0x306140070b511500020b8800010043d00c0b520182c00d106040d524043c1c60551a44c03251403c1d19a64101240010f80c5007d4000805505000f110024140d10704c40b4922400e100002480004035112510100000600d80403000f010075080103d503480541c082d02e00f142450601406a070200c04001400741285603080035a504014045034420398200c940150241d00b40020420802441c4d0015820029007001c42c0b203404d0001e20055025108001444045405070380002d400d0383c905030702c003458030681880301c80040d0341c010307040320740d000540301000031070b010004420380305200501d41080d503c040215001c03c160038000300903d05070380302165800d4603a0b40c44004503103450003400b03201d824400c611004a01107180c502c4030741d00016181000d1103806900b0001c689000c0507a203065035078171000d10f01001a030500c80902c00702148144050640d18130b0040341c6040783d610251801c0b04255841c000242d045201c1d10590b00a81281c04100c51142410b04000b014907040350b000500d401c200c4000310340c412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194362104 1250 194360854 194360857
    0xf04032304030b090f0303010b211f05010201060b0714010603120c03021005060f04020304060b120a11060a02031e04030206070308010e132a24120b0108010302060304140f0f12 77
    0x606215001b503246a00701500d40d520764116031030000484030945510381c0422209a00544203504809001026068199a2441c803003002e52195056900d800410321258a500049030b200b00d801840b84040040f441041a004005680c00134003000e1510115261859100e100c04000f24003a50895541c0c6580021500c1151403d5860980c4480c440166201d141002c0d0050350b0f016020b140001070003000c10000c00c04072040240703023590301d0300000c4031801000301064007011554020b440b420700b016071459002c1e55a11603d15203000c42d42080c0c01406a1528410450f009540c7c0500800d03100e850514010785200b40078012088101e081c00300041c00702c1c403602d00f04403c03070380c2150003441441406004070744180b44403207110041e20202c1c42c001c82c91400030f40b00c0200108405d034400900121080c00204121600842101e1050905401d1a8941e07840f481ca030b41500e4049814540d652280d190107444683d40141e40d941c9806001e60090845401107204c40100c0500400d40e00908150405081213 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194363354 1250 194362104 194362123
    0xc06010602010c0f121b0f02010f02070b0604090c2309131a06030c1e0405010605120615070203010f060315110f030606070822090e03030f04032304030b09 68
    0x1d1004040d071510500c2900c410502c41c001300400506d0001418884803000c140c0c2c201c0202082611944070041035091290044182d210441182403903000d40d602010304030040c00701ca1040e5202c00c05c0e0000c0c00690a00c040040c2211201c1c038180d0800724072141d888503010040c1c50304c078030075080018200da10f40007d2850103d5000c03101d0070641c0c0c44543c000b00b80c02d801030304d03444d014071440030109825121014250181001880c9041080440000700025140140c0000c0e0800100b408a04a5000c02030421608511704540d040142034000150701030341c0c014588040c4d0b241d0300340150a401d55400e94400025240111007941c2080500610b80080c0c41d038008040c07010010070412000f080c00481c4c051a00a240104100d160003076941301c098041e0050550301c0314400e121201044015800100c020007031400700c030180700301480950105d80f00d00004001c490002613280c006400c040c4600b4400b80080c0716507c02a04140000740315080d290400d000c11220b802e0f6182c0401d424070310015030f0424 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194364604 1250 194363354 194363357
    0x1e220605010806280b0f030a0b04021c092d060f0506180621150603010b0d03030207060605150703020c04050f070c0c0812070510050c0a0c020a080a0501020c06010602010c 75
    0x5026644c120120910034014840381c002074142803010035400400303801803400140b0440a10b8580c2846003000c000c44603241419442144100600c0c0204031846c00302391410501032030001840150390400f82190400075016150440c941c02c0490b82d0350310010800004980607140030040015220034941c203d0354195603080d0300c81c0c4925103000d80d9040000360194814006007907800344540b111801c200103481404000c240d034210703500040d0340703582c4808040d52000d4124004d00000603039001043c040c070b00440d00541003580000355942031201a8002d000142409080101011039040d540c1e5055004450300f14014040c1c00b01441d0b070341c9014003400740200d143d4400740129407200074055a10000c0400110b070242d6030400001141101840340320300e022550068950340310002d29100d4100b844440850000380c2c540400c2c4007251614000b941d042c0c00d0315040441e056070f01800000c1420400d075004c1036541c800c0f8003040c410420107401402202010801311401a603c1350310990a8582c000398810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194365854 1250 194364604 194364619
    0x1030614101110050609090c010c0b0603031c05090d030908250606030b190515010e030304050603011202091b030408070f0501150807060905010e1e220605010806 71
    0x685a00d0800841491080c1d01e0074a03462500e07410300c2181c10002c8000302c0000e20b55590003002901d041000032560303c8140c50000e01440002003001901c65110080003800c07002c4440700041d4180c600b04200c40e0140c4109090103003402000949002600e03040300c4440342402102540501c0b20b010f4000e01708881d1b0f114440b1418900300040c000f035054000c402c0d40c40b00c6614090302001051807489440042c1d4001e144c042540c0c0b81ca45090300ea0201c11060f07041e241498841007001030450301c1c00012404000f4a040c04051141100092a41c02148c06c215440b103400000002c1c0c1d0b9041815040501c0d1090380c09284543c0c07050500c1d422841d8202c041102b000c010400a00080c40c030b00c00601d02ca92007032004026400080d154242141c400680200e03500031006403d10401ca410803140d0300402c2c0c18a0f2052b030741400c0c000000c3c02c800750901103a0003000d1144e11648495071181858054160285c50325684481c14944403042c5100603200030510341c03800001144ca544503403c0c2d544a60b00240215 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194367104 1250 194365854 194365889
    0x30c0a0b0402041104080304080c0f06030f040c050a141e0109090903050f0a0e120705011b02030f0607121b0f0804050c12010207140606010806100311070c14010306 72
    0x210394010081089910a50302e40b180400c080180c0e000d0070117081114000e54482e030402c0149850712001e402c8651142640c01040d2030103554960440754000d9180d060300140781c455190882035200c1c1d6811460340003244030740c0852441e08900070054040c1c802c6955800b280c4139108204040481580410300041c0b010a05025803801c6070840010944030b031030700358540412602c102c2081d0304039003903000c005981c00841005a00c0d1100e15107550f0728040c006400801e20b4000064852403448201d91440c13010303a40710300250340d41404400c214615440c1034a03403901e05110010308198604500e04645403034a1a222080030244001d920044c540b5200c801c884008940256481c200080c0215580e1081300c0e89605640c9586101c9405001c0582c000350f00c510035490181c16400707400380c05010075070044040046503a1b00588244e0804d4041d2100d40ca41c0c140b951049026061844c0300340560b400012750032081000d00142c400c101d0342003403a408100c82e407482c011420b84165108505c207680d17400902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194368354 1250 194367104 194367113
    0x4060801170708011404060f0e0c0409140102070605011a03090705060d09061407141612110105010b03010501110f1b03030c010f051e09030307180302060d09060e030c0a 74
    0x44507501d081007000c6a032031a9075502d0507800d60700101244030b5803501000c180404c2003604d02610007616040c500a000d20320401d80e81e113035200c185400c5a4413030350b103c86c0c4132070034054003119071407070802580000d6603544242c0c00c000380641428458100701e0b048800e0b01b6111300c1802e03400c0c0c0340200115009413081c00d141c1002c01425420170102d007030040359610075040003d0f556106440d4000c05031104020a8a01001c002c1c20a00015903205000707070041203c440352000007829140b020b5440340d0700c540030070482101240c2c040c60703e0100c1002903181034000308071500003070081c50488030b013685d503841c072400c4041c2080c2d114129100d00007465404685000c802e00c120b60b956045030140a42207a003030a0424420501350b82c6c8c4846404400c5940d4814031040c807106094900c01e4600055084401c0d00780440aa070392488020010300030400d805208049240781c0303040312001107400401080d250140500c1c142c008104420301194001e1420030350400450000c010340d1201c0b1030340700c007520310204103844 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194369604 1250 194368354 194368379
    0x6030d05031b0415020c1311040b0f0408060403030911010302040302010f11010f1802040f0c0903141504050f070e09070308030a020f040f080d08010e0103020d0c17030d060b04060801 80
    0x28401c1c2d80b82c03e00c00407035201582c580c8001001c03c0c03503000742401075480b800e0281d400382092030a00702a081c00610080714280804407000c81d0780c540b0103603948a031001d03080074482c007443c1c0124003140a180144424103034140c1000c0440c9004580b0203082c00c003035000640491040e40320003030104181d42160034280d0302803038210390f20264050011070103901c13070041c4908a441292410900002c0811940290b0070103201c1c09910030b02c41d840030064240c0080b0050200485480018008041c52406292191042c0802080e42841044200d1603042604e8066103420703014140d80114440c2c2040001c005c0e1102032018043d0300010080c04000d421030b2500b12507507100401003400e80c2d40030451f01c4000d4403071100030002804004038070110b00d82814080c0b4200b441000c134400401804100501140b200c1c4d00e1400d0443c0d034101c554841852991070f0151020855510109080f09a02200c2d501200040020900107162510030070860b80c4403a42c00c603582c02280a55030014000c3ca006004280f038500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194370854 1250 194369604 194369641
    0x30510020702220b03010c170c130e071202030103030903021f050a12060f060c0201141201090f0b091f08070b160320031209240a0b0a08010207020906030d0503 70
    0xf000c40d4100c4d100c2d02080c00d40c2c0079880d90a000412960004030410601128950010422400a803078101451641a40c4e428540940c5031442d0208011410b80c901a4013580641000701d1402d54680d0fa482c00c000c0d00342c19680c80141d0080c0405214401c0040403010030810701500394464170300700528080103e414144490360300c20269a41d240108402d5402d24482d4002d00080c0d9955000340003901c001002d01c04480b0301c1d08102d100600a190114902c0907582d815204650000102c2460340f0b03c411000e80020005c142d017140c15802803180c880c542c0e00d080b0200c1280c0c0d20320303080e00320b546d5403a0039650481c5210b444000d0740141f0203d2003e07143c2c800070940060203490021150111807640300500c0072141000b0705250300010700c7c00d848030644450283c0c00740c02e0601501d4001c0f003025a81411449640c11f03003c249501100081c050407ea0744205148170010b88419032103a110442035000b5408104142e124188140015549140000d6040a010380c607035a0b460450b25090f41d103031807084400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194372104 1250 194370854 194370919
    0x5120f0a0b0a090b030f030301060206130201090e070e040605060f030a0b060c0f0109053f0c0109050304050307090207171e030a0b100806060406110c0a0b04030510020702 75
    0x401d1a040c4580e20b031222140078044500c00080e200c65aa070805103003031246040c1900e513030814801046010780120790240d00040038101000b2103502840100c1d0f00482d141c1220030701c4941c21003441142030f486000b0007002c55003980c3c1001031545030400c01515002d00031800004500802c0000e001e49095048070a42040c040d0241c2d00b8258050745a90800c3d412590101c19a95602005010b0103010003d032409595150000b0038400e41c1101034401c003041c08114401c0c0c0d40c0008000c2441c0705400002c940704051250020080d5074075900d840d40c0c90f41d1182c0b04940c0f1034490007030f0109004000b88200c1ea0b1090340007110703803181300b1440110130b5903030000c50300d848004506500980d4050b0003e0021407007030310003620002e164800902040800890205403004110010040040a803118002c0b1026036549040030100ba6405150951402c074080c41102e0300040c0c01080061407400c8140540700356403242e8240c442607140828038108034011030f003002e9400340501c02407000780401d0144488650908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194373354 1250 194372104 194372111
    0x16050d02090a030807061a010f11070819051005070f2703060204030605070f08151c0f14030a0e0609011b140d030b0603150102070e01030b010905010605120f0a 70
    0x14070000800c2840c40e580251002d103c0021000b0400c10300c1d00ca47e04180c4210098024000140c00c00205144032441c5c04009000c1007800c2060603440c1009110002c103141c0c0121098200354200c1e0811140c1e2160045456210b09100c40d1b0300c04c1550f0041c503100751603650764010480882e08c41200d1038200e078a04410f5462003440c0c1660f413013003141081e6000d14040c0c100035076207a207140390080868000800910030858810300613a1111b80c4400240d030080442c00030307499903204c542d000070103a0040e0788244011400340c2d00c00c501001409083d1804460181ea00341d4100c01030075100719160302c81c400fa00340c001160b1100c00c000d14034041c0d0140c020070304113141160052516100394140010011400c0d6028040078074520407541d0108039600f036005003858103000c03291350361020814038000135043c044c0350700c08401e81e4007960f4802c100610003803a42d442c010ba519690780c203201c1000031080c001c40b501641400000720f1070340d0040e01101c4001d940074510f40039607503401000c06107201c3d0140515107025207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194374604 1250 194373354 194373367
    0x304030f110d08041e09020c0d030509100f09020102151005040911090703150501050906030a05091f0b040c11101509020d0203060f010903080f0703020c0405041a0f16050d02 76
    0x14114043c001802c2d921101e80303503500021700741090701c07038a07640601d01060040081c80352006002c16040008031140c14040391907161030b00a541081d40c501c82108483e0f280607000704002c9100c0e007020404034001e030261100c0c0c1c140d04560521303a03541143c0d007855000d03a6032420000c500b06a07100c914042d0184c0d0440f00503c0240f00041c010711002d17a82c03600026142c0a00c1c2c1d07042c05101c2503040003001c007420b206103040080c2c03020900501000300900e040c90380d02c2001545100090140928610920000008a4080710150300040c0700640c00d19000d20720748466202d22500603900c01071880c040ca0000c041e088030f00320000e000350011601840101918040000e80264180060220707040d5102000d85c891411905006000044000c0340303042007038044040020441001c2280c1e01c8001d181446a96800c0d00e041c240c0c076018020107869040f0b8a00f104000c01c1c4541d0010b1003260903042e02d49040c280e104c001002032081010703640c03411145110004181654000c400400c01006140405810041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194375854 1250 194374604 194374613
    0x516060504150609020301050d030c0f0b040305120a05070c11030f0609031806090a030209040c12230a0b130314072406031212090507090c110304030f110d 68
    0x5005440850300c00401a2030303005154035a020b0f200c0642500c2c1d004505661422000901180071404060184100558414240201100d0684c0840d4100c507500d5891304091400500c2503200780d1200c822403180c80041443c14044c2d026440c000d079010350390340c4c90381e90103511460380c900c0e0f00e4009150305204410300d4140e00702083c005144111403039405181c40b41c410b542074041358811208543d03c1100d08100005290307540340038800a680c0c05445c40240b40d51146030600000d9043e801c2403406100b803110070020403590b180d208c40c0c859050480c86052003420b130001c41e41c40c8000d4000800406101c4001901000001c901d004400d00910b4a06081d01c81014100040c1c1c0c443c5400384e4642c0310f0800ba2040301e01307000084400703100c1145410411039107581c03196030700c11150032b4078401080080c8000d4042a40290007840c01140c21009503481d40781d440052100501c16090751102182000712100401d40021041c1c9045981103520502c2c081090b0395058410600c507d10142d1100b655045403011a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194377104 1250 194375854 194375861
    0x20406020304171915180210080910050c130b120402040e0705130203060f1206070518040c0206070e01030b0d060504170a090305070b07112e0201020405180f0106051606 74
    0x29809003c048101170640c030f10700d1040c0c0c0d203400c0364001c0080c40402d07680010380391102125450300162800c2c2d0015110030313407100d080c114910901c8025070308003000d0000303003101880100541490a445404800e60701c0411894a004102d0781c01c0988030040300040250130907811071148000118183c6400e15103810000310041078040c500410720b175011040003010f091039080c410102e07800303c800300000070a40303407441e83e07981c002000c0d40204000412907444002000b144a903000760020301c02e2040051200009607030700021a02c00001410b03101d02c0c01c8881d4001d1055541c046001340440711201e550f0f44402d80640740c00341048658481507110391985180c0ca8028180004003596403c50a070301e9030500a01e4142c0a4115484d800700810003000080c0e107001c0e5901da4180151074880716280194403101d01d4500000e020310250490034988110b040e4198014420785a08440074506000030404102c030100c021a001040c1040c44001440b4030341c00380002e440c3d5810a000080e18454413542e80800b074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194378354 1250 194377104 194377153
    0xb0d0f06050a24031e0c17010902120c160b040c050607080706060605030606160c03080c0718060b0a140405130b012c120106090513021302040602030417 67
    0x30b4070034800c108100700031242190443c0318070518090028140080b81c3c80350000c0c0360780c400d44845a03540c4c00700724414014440003007401400c2034011002e40e507e051031b50196121401202c80d070f90110000400c6000000140c4d20019405556118148015503d08000c1074000d00140c400100011000916036940390041c50b04501c244042a21040649008070654840c0e030003030301c28060305104128494403020162000303509030314003081c00c05c0210f08003a003d060340c0f60400303400030f01d00207a0076460000c0000c3d4001143c00150380e0200b09000045600210b40581c002c50010f00410000c964140d84103a2100070313161003d241c42032170a9903450005104400890755081e0640d1142d000c81c40350342e080f15010400c0c2c481c03919004500c061903040000c030150b605848501c148202aa06402103900358030031005403a44840070880da0404da02c00b2090204105000c038030805803014000701101041c000d407021246e080e0011418103007400044403883e900000c0283d401d200d4844c500e581507a494920880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194379604 1250 194378354 194378369
    0x120103050703031106070e1005160803150117070e190303020106150c0209060603070c050321060607050606040b040902030a03080601110a020108012d080303010501090e010b0d0f06050a 81
    0x1040d45940380140840e6918075a00d25550091020410a0354001f003224421803130032183d2458842d1200410f8940b8061803560380e0f141c4420000d01400c1001002c02135009941c0802c42d250307032034142c00046544040160400b4900e40304000030441650050040c2198801300600c0780540c41d00c3c1110303804a40071039a10980043c0e454900800240c44000b01c0c400c0f0480c003a28007a005415541c001c2202407030003070071060042d44000b00090000380700c0c090f500c00c956032201c02d6a0fa203c10480030980d041141030081142000d240d004900716152000c100d84c0510790100c09840c030303079582c40100401406204091a000f58954041c00300581d414401c004d2000d120743c4541c034042c20450001044007000384049013459120070705101c0581c1c0c0000c0254111803c1c2c0600c08a001015480d1100c22030101e01ca5010060b05400301142908002c000b540c161071302a40c070802c6590352078054005406080c0328002c0141c0042040e150402d8040d004240c42501c10343c7c0210340240d80d02c0100d00101070300e500205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194380854 1250 194379604 194379613
    0x3180a0602071707020303070b1b1210050118030f0f02090a0f0605060a05250c060c0b10060c0803040c0f0f060e0406080d110a0c17010f111e12010305 66
    0x2041280d10880c103da188020882c080c1014040c0c2d0100c0d03528800c01c00c0c040c0150001c14000344a1240003000d036601068444003031511454100402d014034130080d83d051500030541e0f1000b10315948110701144510807451010700c807080c595255018268011082554a00c03c50704008000d40c0381c0c4401130b030080c403020a002888114203c426411944035070000c0e84111000c11a018845510a0a403101c0814204603220180e100c910030820781c1040d00d100801e00110180000748841e04400c0b610611070050405003495540d009121002c20624040c1c02c000c00c0d00b02c13900c0008125808091540070380b00e484441440c58031580c4880c00c0e0111607008034110305501a003404800d42c854450038519030b0588092040720300381407500362500c0a14070500c00304a10aa103030015000104036588120b60442c0600b694541c5449078859001c041445443c0c0c158202035002c1d88100349841024000c1c01101d41c401d060800c5001c402c16903540814840754940300c00d10047c3e0f0f2841081c46d0f200e008600c50b10080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194382104 1250 194380854 194380867
    0x1a040506100f031a03070e0718050303040b0703020f0609011e050903030a09080f03040c0501030b06070f020f04020d05091e03030702070b0a14030a0603050c030c1503180a0602 77
    0x415a00010855406040210403050040e030b04034808008008482c100030680c400c0b02d1030481003410404101d42c1d4180715008000981903416800c5a00445903a0340c0c001400c5444140100812940e105640d01580204020015586068082c0140074400d1055801040c1e450900701c2c6841000d4070b4070007160755240c0100102c080c3e1508800d1000071152400d000518101c0d809540320b00009041250345610b990a00040120403800c5400f03401c9020421510703070619080c2a0041000c901486010074900040c1c0b070001e207424416281100d5005a072781c03c0542146e070900520204100c0c3c801e40141d005d11030f000081103d80a1540f01e100640010050300c040130440c4e080c407440c07140c1aa0b845030003c10074440c0981e07010482000361258074246540d5420486801c0b50742c1c3c03076084e220307065000002c014000480c1d003541026044900840c111214184480c00f00343c0c4560014050750380c030103000e0800411106494000e1071380081c00010720300c40d00d03941c8010a803c11030f8a2a00300c4100e0f83c0020030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194383354 1250 194382104 194382109
    0xd0b0106020c0d030c2604030303060807060c05030711121002120c090915011809051603020301060504050d02031c0503040507091503020904060e030f042306040e040311011a 76
    0x20440110b002c40d080700d90034581341c8000d000703100c00260107032451041d40c003445510040714410201412039008020307500c076601c3c10010020f2549005e0f402c180d0051030300024006202e0407014404507003041c00f4500c4c01c41255643d2aa00074543e075001d811000c4280031001d1990180300d81c031589600b003031000d070f0388480b11218901200c2d4001c2644e100c01c0700600001a098550080c8940d105802e9030681c82d038469034100584200a035440f121030801a021008a1459901c2c1c00c86801141c90402400304090700c410140c1c203a0100b400b42d4800035406100c10050741c94802c0544450a0028007030311050803c603030768034a03e8a440c0b5208404a04000180020070100b00003440051800040800aa088000d00803000c40b05522001c0e100301c40400c04a0113100031903101e194440f000d01c08895842818031980c1c04d190f0414400e682110000501e000c0054005842071056280000c100d01e01e001e06065007042044c0c0041c00c20f408000700300000b507900075800d1098550302460740c2c002c00c02c1030034010b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194384604 1250 194383354 194383363
    0xc270316060e01020c041103070f0e0907033e0913060803030423120d021927050f0103110708070605060901090c0f0e011107090509010e0a0c1a090d0b010602 69
    0x1418086c500e06000219a0540722054980120303441c507200050f046024001c540110340d120300140c0c09000c40007400030180d0994406608010640c2c00e4110018050300c03002c4030b20700c074105514210031a418913422403441c440c00a1610480c000e0501d0813500c008030401c07080f50055000303418980d20010500090001040170b584002c0221035003282005c0c1005c804039194403844107200c02c06036003c6400481900c4980603111181a10041d04544903400e036402000648551061882d5800680d607030510900d010a0003400e4810151036050b13136203120401180209458030360003204c420248566000a13143d0401058200d024481c00300b468208842009180d11060384190049407611070070340d00c041e8009004507040c0c070700390030004070189240300103803041c0c15000380d04d034030134090901c000c00d0840060b13002d50f010b020100001c01c1f00b04801084d941d59111b20641c05031250b035000300304000f03143c0b450388003842ca001da140b0154100040304c4041000001c0200c000c0b81d0040c00b0800611085d5070401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194385854 1250 194384604 194384623
    0xe04080a020120040e0a090204021207080702070302150307020a080d060311041a1504080d05130e270718140a151406040b0715050c270316060e0102 65
    0x3c1000704001140103e4610511461042c000c254502c4e5000650004855000e000c200340c0160007550383d11501c4444030080390702203503044c0c00f0542e40d5011444140c80002c0d00c2c0203030790380034040d0b4501d100c58500450842d00010540401c5110340d0700c1d01000110f0039805030501030460303c1c0c0440c1445c21841c1c11041d038110200100e01503481c040700c5040c0049030303100200d1450000d550800003000e10034000782080c8660341080102e031103116010390026610100410300d22801c55010704046032900c2600703407840d00c01c0c0c81180d4040300c5d00c03c0c000348000390011500910b03944442203503643c55984038278920881c00d95088072800c17a80c5d00010111a94400041544020144020407803810819860341c0d610071680985221114101042599601e801307084401410150b4151601c0d4071841c82e103400110160040801c000341000b012410401c42c080995000103000041080b00d90809402c180c282d54001540320342c50b2080c03d14802c00801c220516030007410743c0d0703a030350340050842c0800a4600785110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194387104 1250 194385854 194385881
    0x1b0a1401110417010609061d01120b16020721020102100c09060c0201030204080601031b060c11121f0c03140c300a0b0103050708070e090c040e04080a0201 68
    0x16004600034403600c0102d4050700e480d4840c0900344100103580ca801880306401c06071a0615010002c141840200c40c0e100c3c046100c443d42d40e106a80318858241503191076000240390a12070004100806010304805038090a14811110410b50b110540040002807e028261180002003203c00f03551b410b20401e00c803184001000c1c01071040d603440c000c18030a0503101e03940c100000c0361400b0007107a11a80485006082c51801c03112a542c60f424031600c1450034804910083c2581d84000500b0b60042c08a80040c0c0c2c0c200390021001502802440364145040142420a01910f003450340e01408404901050b0b241154000981d03800c1100c01504443e441d1101c4c0071041d2003142008802d825050886004103600505039101140825010300b8603c400d122099a89e1a4881041510305540e4000b0107151400d036030500c11030300c0d11582035615a078180c900703d0025400500d10210750500c0d426050300510825545841e207039035007801d0f18101005440c2240c0c02a800540328889035424024903c450300030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194388354 1250 194387104 194387111
    0xc030601080403080a091a01090b1504030204050a060302030307240e100c050906270f181b0c060a0e0303070c1101090b0a020d0201050123060f1b0a1401 67
    0x850010340001c0000304001c04000301c41001840681580e0810120319901a00031191550030001d41600078000b401183d52091403c06c907542030b46840ca084148403602008035519080c19070302804050100188640229610b4010020050b20100028000280162411501802c0400c204044c1000385c0060b401e550b810007109802c071010110350b5500040c0c44000000f8005c42d244402c2e40d0310f00444a18aa01030705c08100380f40c0404d1101c200f4410140402407010031071810404000480d0703034450120ba0061b00d099000c0040c0604014015081a81040344070207241d031000c18010315078414440c14400c4e03004002030000c4503405000350085000903070301543c00d502d042c000060000d500b04002a0130900404130f0a4916405000110041d007101040d81c0e90b5501c10080103503030b400c4581c88860066203044000038080703035080007841d040742400d060441044105010030a46402c0013000200c2c030030080041500c80078a2102c0143c0441d20310018100c9209a414852003070004c440c1e440360140d04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194389604 1250 194388354 194388361
    0x12050613150504050c0406030c031407050705010e01180c0b040627030b0f01060f090803090d0201090906120b0f0412031112090c0406060e030303070807120213030b0c03 74
    0x5035080c0c2030150980c0c1010000306003110302080424105942c0c006a082807601c000d010400580000400a0318100c0c0c40500c04031055203011402c276044a9060400c448807180441c45c1584141c008000060040002040c5800c464a1150854410f9020f05581c1c0085412090400541e103924030024921003009505040c40c2c030601030000c0c1c034518181075656508059240e02542c4183c2c54001440c0c1004c1c00031001e10b82154542ca14150038041c841c00701d1001421041450f00c58041807084c0d500d484095810142038405020220303040e00c07012818400c54401c041240001d84c400c250041c60108602d03141c2c2075803800d20040c1000090b01070b00300150040c0402004c2510b00c079184240094078580011718a1402141410600405140d040c4041d00c14081c030941e4080040c0034504104c3c01c4070b007000500e035580000d8402d403011813000c0750540c0040c00003036030f028042e01c1c140d58064000e0611000c003019189009041b680032004030360381a01d0302003050051241000382654019240480d091442c00d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194390854 1250 194389604 194389609
    0x1110d0e03041d060d0501090515061e0103020309070e100312020307030e130603060c0314282403050102120f01030206091003020906040f050310061a0304020102070b04120201120506 80
    0x400e00d40390003400036070f098046405a141c4806010806400030004c12068405181c52516a0f100714403201d03a41120201040381d03440d000d00300c10803c24104110f10b400e0220000107401030b400040419446008a0000160040c500000e4a10650290002d43d45d400c0c1149802805030082c0595002190300500c076483c0001d42140149800e40781c110791035029238500f242c1e4240685502e400c01090141801c0003151070503055000302c400700d8058841181c1560b5000c20002c0742500c000031608681c071809441f61020002548244a141d049c8002c012400d00341c12403260500e982680103c450307079400920b081d500d2910408058001307920f403100c14599413443d0001045800b41000c07540c031483c8410f00c0c1034030b820700030f0341262080c19025001c0354841c0c1d522030615512020500c2550b000b400344504100c190805c0f8814441a07900c0c401e1018200c40e240141d030005608003d200b00d05602c45c01d0400b0a621020318060710041c2203d82c40c80c0e04940c0a840010b00c100f121042c4a4019800c11052080a5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194392104 1250 194390854 194390879
    0x20103021b0c100e210304050607060f0e1c112407020606010c020d110315130204050a0b0105070f11090411040c020c03070501050d090605070917030307080705090d0501110d0e0304 79
    0x1707440b80d10b450000b20b102c0c1d41d10f0383d00714403441d44182d80c0604c0000e1000c0400c5265004401e840c0c0e01140100f100d042501102c2e81c50b2110040c050072925040c00d075000d101030080b0380102c4241461411103c82e000090030762540c2c80d000050070103039000520104402d0030b034100965580050280b800b01105000e5501003908a60349501c010b0041c5445580011140c40c00c10440d0340c110b05d03043d408940b0b81881d180c00881e02583c80010f82c019420240011610807041c001ca502400c1c0c1a900ca615149c41600d941d4000420441c0c103c50328101c007104804c25540c1c0c1704090f400740b80140c0d800195400c4120400080701c22031000c000554100000001c601d036008140403048680c02c4c200340c3d0350b400ca070809100c001e02c15141c0090413103241c03d06000d0003550188807074064580d0400802e502d21800b032201075480c0000c540f4500000d09400c0062900c51203800900201d071409400c000803003003a555220309460482520741d00c1103c01080b07445665405028221018446101940c503141c00d15100c2100e2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194393354 1250 194392104 194392129
    0x1080703050606011d130f0b091005091803190f020a03020706080c0906040b18180c0a030207050f010902010f050a08060607020d02060307210c1704020103021b0c100e 73
    0x103020a5100c203021004813100035000c0e101d0006c1000042ca00030341014401441c918454000892030309901c0010390421030b401c2402408068030b210f180501d001c0070020442030003003803848410016980c5100e0118208050182d10010320603604c10030101c080001c0c1846000a50b0b10115404030b210180840c0c0c0201302c030800d540709880c2c41221542c2c1c0e400003c1881c0b280c808090707002400050000740c1214054054007121502c0c00b0302c120b07803c12040c1040680c1000300c10320f600c46882d49001c10040c030781020007800c0003c001e06000d424141591500b504080904500f4403150751160407450442d80e000389100c01e4008107082c12810050050340003070500100400701402034500243d0784065503602811118643e5004141981c6d030300d4010001000c00000003041d04004042d0034030207079881c00c6401803010009150b0340e9480e8001c0805012060390398041c1c0180c1c18142d0030041495400422081e91020085d5a00181036003c20401845003c0750032064070300401610b803041a401c2d81d5481d820908 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194394604 1250 194393354 194393357
    0x3091506060d240b070506010501080108280609050307110105180d020d0602070312050603031e0d1514090a0902150706020f030a1a04090b220204050108010509060108070305060601 79
    0x156881c0411007402c040c00100c803d040c010104100004020194400510205129000f80c17001640d0380d00041d2a410000c0c003401d2000c1e0040460b01001d48401d550402816076420000710151125480300c0c1c0c2150365140056900390400907048050240c002001511a0020b03c1c05070700c0d0600600c40354074100340d0440004e2041d0002c15100c819561750510307041900360407410442d42c40541d80b07005410141740480704101d031818400011003600e00070082c0d6621042c540b1000f01f1011046404540d40d41c012401041001e50f140100e2002e81510f00e4440091b000b144100343c0b500003041308010720110700400c215101070a140280b401a2292200014100b0b1420000707525410b031480d004000e0300408000c00080d9401004100c40c80100750080301c0c4d010f6900d07801c80e07035401400c405d00041c2c80c3d080300b001d01545a81004030b000026003484d807107040326200301c9040b500d2445078001030640350203038049020380e0344174400d0001c1e004041c0704030b60042480b038000b0041946150703651511200010031460 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194395854 1250 194394604 194394611
    0x30a020f040f061e06080c0c030a0e1201061401030609060503032a0d0206040b0a0212150406030206220b0a09060302070303020405030a23070e060f01030e06010b03091506060d 77
    0x3100c50001c0e8000030041d20801d6800c45051342c54084511124201c0d2040d0000035510001088843c1034480844882c03001c40405140f4021207580107880100c006042c2a410010002064081003000c0c49400003030000220152032818042d8001410b49600340c00144c0ca05e03180400c1040b00b903400001711000404240b00e2410301c02d0740e80b220907581c4901022684030701d02030a555108282d6003c80c40034800d0b846143c1c0545903403138846180c1c1c02c034041c04210962505500c2c020400c2e0b0303004400b2944c107481004001152050301d99001c1043c81d0014035542c8200901200b03180707240d80040303801c2d00c09400c14191160030000344290040a8103114072a2805140c2c1c005025820305d4442e4044401600016040382c10303a100914004401e407008007920303200c4040c020f401003180d0340b01041a008a60081c04038446d242c0b46c0310100401903801e0b50341d82d818940d542c20305c08070300241401114020078810240d2a2a407410000c1c0c13038281030b014034289005006a00c1000315950310340b0b090300d4030448180e0002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194397104 1250 194395854 194395871
    0x30b01050d15050916030c0305040b040f110307060216061119080405060301060206041a0106170a090b0c0304050706030504080703110a0602040b2106010801031410021b0c030a020f04 80
    0x1070082c0e429401583c1c10401c00001c00c8030070b402400f142240c1c190150390401c8000744c0180220101d4805840040c030b0b04503035801180102c0c0f26241e11030701c0780d4001d1440203010301c041000030b071404c1050744c03002026800002c00344464120961001000380340a0400c45040d2070700c584d4690312594402c24006804450000681c1841284002d81d00a00700c0a40166070340c0d40c441c50080d5071001c08480842d08030f442c100400031800e0701900100d04032881500c03581c003c07450a0f00160300000c0010424035189640f20708100104d11f11900300b81c000c0040c44101e07030356820503041480c10041e071904038000340741c1047d05100010b1004001c65001c0360b054913142010b0403102d2206800c00c0003400000e04094000309010a4101101e401084960607411411700074103005090070440c80011500240030900f11801080812185a1170000d850303a148180c0d04d90002083c0603a0890b0444030840b252041c804004551095041102c0c182d855401c50040900080a500040c141014040c0c045c0c066611410300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194398354 1250 194397104 194397131
    0x50c06030f0c2b0902040b0a050609040e010207051009031e020304090207030203070f080901110105090703290f06100314280204090203040b24010c0c12050a060c030b01050d 76
    0x208035508003042101031401101034180090032284900b40e11840c81c01f031404655207841519a412074030007803c0c09040c2882803041100805c80d001c0312210039502000740c44000b5000340003504e0f42c0030020b540051515428100101b5034103101c1e2003e40080c00301c1c10318081594001007501c1c1150107403a0b000da41d82079603141c224118040c0300070083c00c80c503000b9014020460700d10040d0803040b0007030762000d12a5032035010f49400d032001500d4886050f0006001800070544640c2c1c1813001030010b03062a100c2c10101864450b5070b82003260440c12031003c2500b0f0201900c2d00110082c1846998a0180320f5065444070925a070040502000c0c840200c04860b00e94864600500b0b660380101414119200c1743c0d0381c40c40001950007203c0488407007000303100149000b0b10051703000058000c100c40001042a0280064490a4030b142042c0c07515100c05400241c06401c1043308109248581e002c1c002c6901a45058000e40d94901407000a0500745101900240d1f0f00c07109590706844520b5000c151800710001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194399604 1250 194398354 194398387
    0x5070e220c0509031c030e010b01090510090e090601211130010209030f0f1216020604090c02011a060d2406110601060801060e040b0a051309050c06030f0c 68
    0x308240c250191001c00c000445260140c917030314040300d44050003100000d001c545d0032202522900e9012614002e000d103d603051801009003030151505100303000c00d07140ca40c1c44815050031152424a58004001800403245045241c6502050f0b0346008165071410b40d1000c0c40f10380d20607400c41c000c1d103003140301c000c045108501070789038125000c0d080740e20301e6030724003045010750300c203c0d4481c1c00707485000030040e142400041c00006030f5401001810300203800308a40131682d8021342002d90a0307481c10b8061070241e507600d002413004200b003c0000410090304c00e8040e0944500c03104401c040070b5120342c0e13503510340c07a4a000c03112174210b0101d000030b200f05416084c101c894021341c0c2580e42600100c00229071340d5040810014080080c0341103c24aa1741d0b4001103075036030710034002c5500080e605001c1102c581420340200207204001042c010010741c4810125101e022844004000c140e121070000301803080c10307c003c03c440202954100d2940c40c20103014500a5000b4040040d000340001da5041c00c0c220102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194400854 1250 194399604 194399617
    0x30818010309080c01140112050c0d030203090301020301060509010314090304050609041407020c150c03070f02060705060408091203031b16120906030e0604051c0203090d0605070e220c05 82
    0x60003e82c80340d08481004e03000300351112000040b01118400030a102580000c1044020340c003200030007440c0c03103000a020082200703280c1141035210078411515296820b0000d140070300840d40d12070344ca33880000300040c180c8036016580c43c6c0f558941d4003400074100010003190107032102516019926207506021900038415400da08080703001c0041404111580856484000d107401c80f60f04806080da000502205e11860b04400001c3d4400c002c1040006d400c086040f41c010300081005d81420015180c0703a080402c1214215010b260001d0004540e1409000e91640240707910000d60852a01c41d044a1510784180c07005248400e0109816048004094138003400c0c6a0041b03060b1007000200710007611851160050001081c200512001402000078107284516006801400f400c448c04d03082c20814120b5191080840c001005140702988580345020074940c402d044c00502d40c601468014000340e0707010a400c1c072410034a10182c03149480c6e02c1701000c603151072440004400c114140c003555503200e000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194402104 1250 194400854 194400863
    0x90c0e01031112040b1501090609060c1425080304050603130503040f0909050106090c020a020111070f060905030f03040b120a0f0509010518030405030a030305100308121f030818010309 81
    0x3c5040004004603212040d0095180c000000040c0b001140159141d0309203010340c030300249030b00f681007050900c0348540c19900ca00459a000b0050f601c080f06900b444400030601700010908045c2042a040d000c0d841c0000f003c16101031070a003414440064201d04c4040c100401621141c0c0380e1744c2c1442000e0080381d00905116002e13035102d5542d02440b0004e080c803068156047c0d480d1810020311700085006141401c0c4180d070150400400b00d50041d43d500800e5a2010558410711038045000c0402515038405031041d5198040c00c0d504e85410540340c101d1038108000c0b070303410910041003440b0441040d203c0180c40001d0b10082940c55007403002c0100700c1c041c03607801c65034100340600602da4010744c0911300440816801603501030312522000d0340c0e88901d02c00c65170103500491403c401309111780c1c0704540058600340b10080490307494460f2401604130782e05c0001202280c1d800d0201c004034000d00c0d80000358601c04000c1500c1c2c650744428140b03000d10303010f9045c111350741150408140e110b98040034115502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194403354 1250 194402104 194402137
    0x30d0b060904060e011a09090a0f0b03060907170102040e1803120f3702070f0b01060f120507050d0c03020918060a06170402040b03030d050c13090c0e010311 69
    0x61340000b0040d01803c1c420744418003000408440c10391050002c5400140d0302070040c0c201626000c80e840014103900c0c040035031841e6500c5da08041c9640c103110150045000d40001e10401c2d040180c1a44056601c60007c0514ae2041204000c80c0340901e034100c0d485425400d030301d40f04800c2011400c0c03d600c42c0044030350034000d001c030070001c2d280601000355010311802401c008444010f022084d00700c6020303084a6801d402c0c5c15645a01d034101c0c42c0c0040203564416000d50060200c1b41da2130342c80c03904003a001600825105210380240c00d0780705120700c1e01703880952010700640c10f10750806840c51058580707241c2619220810141034070b000781c0484215001c0a0b200c20044222981c4140703240c44141c1d022882040361601c006195842400303229614122188810040c3c1c071075600b000000c01c0340c105403640501041c440580640c0842c401c4d24411000207410a5842c030380d0b81c10040c82035810b17800007034201e031a04140d8070040b039011300101c084940c2030078001440c60405400c2ca00c0c0d0701842203200050001e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194404604 1250 194403354 194403359
    0x1030b1906061e0806090f060a030512032a030601080a02041521020405010516020a080a1401050f01061d12070308090a05010309120507110409050604150e030d0b06090406 75
    0x43c0b08500001d081e040000030840c002e50980211500582900d5040e80000c200000c80c1001e00c08a10f1345420110081044000a981759030302e505201401c83d00030524000071080243c0b100c0d00b0000e294030440c40e421107a400828503a8041d18034040540590b0400000d400000d02e4140e1560489019240104020006158a000040c0880700b603090b48081003040c0405045240c1050084d60141c5070305864181c241488400800200c0d044020260390100200301300051404091204041240c01080b568011881900e005403e541c0042d0440d4100035180c00104801903002d001c3d90301a4508103081c01e50310b03910100140c200c1014014109090003120344c00070800c801600103040b0250165620040c0766030318801034041703640310032010f08410b8402c180142c031035124070b00928150b4451004c144260301a5000300b0200e03020010100e825601800034402849100d134140d202c41d010b000b00500c030100da42e2002175180d016130a91120203e4403400601506e9955500f9282e100c4005032007004102c0d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194405854 1250 194404604 194404607
    0x1090f080c010608010203100303050c0c0a120b0907030209040b04020424030c0503120f030406021e0705060f09030d110403050a0b18070e07050706150608090c011701030b190606 78
    0x2408810711040c550320f0040000b030418010f0080c1c83c403034401401199103561458900380d9055004454842e045c0c020310104405a50307803c00c04034050111910240403030a43c1d0b10f000180d05d44046c01000d03980c0d01550041005a80c1c1424035070340a54811310b17500c03107910386102044c0a400c052010030b21810203408102d901d0221460320000302da000b40403585a5546d55002c0c9910381d10201d48447d01e450301001072001d807440c1c4100a6400920078074005117020540554204c00075012048007411890008240b000d00000300842c0da080f00f00c980c07446035507007000400260380317124503030144000c69210507014022083c80002e0390000d5820a081d943c0c1c07408945042214104102d4002141c804400d00b0074002000000d48007094400e21007195816032a102c40940d07540d0030802040360f6454550042c0d01e9480042012000101030b1900e0352095410404a50303400d1424082c01e050400c080c3d18891440100103211040c11250800d0110600e5200c00341c801425400140d680041d1070b00f800000602903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194407104 1250 194405854 194405857
    0x4112703070e0408090613080102030a0c09081b040c02010902130f050c130905060406050d03020d0f0c0c0902030406020702030706020a02031006080d120b0a0602100e0d0203030a050901090f08 84
    0xc905030703800d5645502010710b04640c107480c050100c40c0b0500000754203040041c01002c101e650001c058100d1640c40900d00c0c00e82c0c5c002c8500c40344454880c012041000c1d0420892005407071170030040d14044201030a006080b042c2480b0413849140c503181c7d002e000c54001c0d40103035452500a04444075465070300c02000c016000284454040a1600e00094540090941900d051541642024007454139118a00c03010705400f90119511036510600000c1d6955050400300d0420f20036009008018403810010700000065484081403001b00040080010001c0d5010740c00c0c0d541103030006807281c0715800c21340c00030f00407081c00070b401d84242c8a0200f5196000034a0142280c82202241c40103000c0a040000f5520148a461860b41c80070040c0c1c00f000e030044c04132072104c1403101000190500c01c1000608030004650121000d42c00030303035a1442100a0703000d40000c180800c40148003440c04090000c1d52440000d01074850f50780d40c4e4010600c602e6013034001d4030509400c980050107048550400c200203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194408354 1250 194407104 194407177
    0xd03080603120a050a030b1801080d020609010c0c061802060c031225270603020c011503030903030804110a03030e18060a12020103060e09071d0c090411 67
    0x40c1c8142d00c0100c1c049111441101c480000c15591107040903600a0103501a01c401d0381e2030ba91101403941c6c51600d0315911204a030003084818001d0440c0c4003265006030034118080c4c90700841e0313410a80c0303c840444c0c00107503442c070040d84190001422001c01868401d501710b21503000758082c00001d2101d90103100000a401c4042d01016442004c3d02c545030a01860740454261403495401041107141090041081407100b100302001c9030952807142e041c014071034007641c0105001c039030b001c1040d14502e0000d01c0394940a520222500c00c1103811501e0140404c4a00d10008040103000b03c005420030040e19120f1903024002342000401607100d29026004510b11099980a001c1120401069010260320203014060146c10454200d00304000842c84600155080e810b143c0c40704e000140030301c91170384023034899040c0034042c01d2903600701512042c010050f103110b9513003002d0350400d000382c2200c1c5100b00c410300741c4216400036008001a0b4181414000c0c87e41e1203808940307005800328011100444a00c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194409604 1250 194408354 194408359
    0x60906030d052b0c110a02010e13020d05101508251b080d050609061f020325050616050f09120307030c0b010b0c06011707051507021306060206060f040b0d030806 71
    0x11700420342440d2039a201c10f00000640002c982103a030814034204a8881200b00d80c10440c00340c0f40c510100c900d51f007590400ea80b241d003140c100f244100400220075003640780390481c5181a2229041c00082044000c0c90900b448403d0000a1110f228190203050040500d01c88071100e00104005410074420740d40000007402c00040c182400a0001d140808801c0c0c8035240042550b81d802e140722204044030a60102e800341548400c0000e244000d4900c00c03501900c0000540e0900c480741c0030324105c0d04200c0c000d42a00c3d85444240300c1ea011581d000410b441403190313108401ea4641000714001255010362402c4000c180c000012003d0605910a00c0ca034a030070f00410610742d030741c0d984014682d403920070f08511408030b400c0b440040c07245a5003590741c0f0360003040c45401c0f1140103480d5800103c101c8601c40c0c2d90b00c0040c400144100031400c00000a41541d004a6010450303d0b240c100041d40b5848004c0c0081d04c00c510340c42820006a94a0b400410500d00c040c01d284031505c07c0b03240103007041405480f05803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194410854 1250 194409604 194409617
    0xf070905090906040303181a0403052502040e03090d060b0d0f1a07021c03020f07020301020a090305010c0c0f020f031e010204060314060d150b150a08060906030d052b0c 74
    0x1012920071f102e900c60f040f0b901c9614503140269071555003207030450280003101089020010700d4050742c40304001a9a0702015031041112055520405c4100c46020701c11b802c264105210345111540c504050050b40b6401a501140e020300c042c00041002c1b10005005010b0032900c00c2090034040d204000c481413000c160b420720a00d0300d9148003a40e9401c800301e00d680d00058008031130100300d031103030b00034101850b48406420708205c2e05a00203400da03007140c66180700050743c03460100f09003e4240110680d54034a07080888900751142c568030784042e80150043e000705501142e034462500c01b0400d01a5015004000200700362002410074082e40c090301c1003200107030904d15804002c4100040709801044010521031481030207550f50307050110040400c50401e580e0301980314240d102c21000300401ca00c6000e505559488040020301402d801400d0580207040311010480c00b61030000e03948400042e1428299180d40d10000000c95a590354100d09810300512140c00c0d00415642d00042c44000039070302d694 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194412104 1250 194410854 194410871
    0x108010e070323070315020c1002090307030206030606120103030e010225120812040506040b01140a030311070914090105010b310806040b0a05070306030206030f070905090906040303 80
    0x5035201600d000c06002020541c02101400e180003c0000c040f210342c00c15a1061079403512407008404e1640101a40290001240807001009128042080f16070000031800e1070035100c00310b6650415808024041d40000020071901c0d034440068842154100e03014124030b6840345002480002c101c0000d034054880d9095410303207014500280d020310905445920219454855405100c910080041e21103c00030080d00c9032540c02c0824240c4124000d50003441c490030b240c5004140c0d0b035016403001b8041000041380302800e036a80340c3c0e9601166050724250a0305d40c1c0c594555400c1102c0c41e4404002c49107003894400a2010307a1090310300c10a1150006c00050780d0320f1907490590b2040e40040540c00e4001e2803803500000f840401c1604030010525041e071003680310403100b480d094064405441c84a0041c0401841d001070f40102d96108041d444d00380b00041c90740d40410024040945501d240c0011500010541d620075605c8070000c0200402d041618101070003025200d80f0f00b51029800030b410030144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194413354 1250 194412104 194412131
    0x203070b0a0206041b080601080705090601050a050a0806060408011404050c010503060a290f0711010e010c020d060b0d030807120c08060618030f0f01180305070f080c0d0503010801 79
    0x150303520200079030041c0c002507035280e854070800f180b1805049102c072010600461b403c0301c1003002601901038480202440c40c14042080f0314180001c04082c1000400c01c00f0001d8180c1c071070250385600b502820715840ea03498240009140340100d405c030400540ca0240780459040c0a0410540a94007410135205088501001102c10380700484415412a0321000708006607442900340021342010301d10341d03100b0001344119403210340d40140c608011101d00800d001050001144c00d011040d407003401d10b816150040c10010748014000d0802a204910001d0000b040c45900e070400810060001c1821031032203030501c1c01038400a807d8900b5000500030a90b03402c8018001c0c842c02c2a030801c1b03501d4001407a0741d4002002003550107800000d01861a908400003243c504114007070b04641ca21002c0c11194600e945c0844c2114985a91a03004c0d003500d50161000c682c00101300e41c03000303801ca08443c10320582410308920502c91014061a544074080c0c60032040e90740040614182c44d1a04c000780484400d1030384 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194414604 1250 194413354 194413357
    0xe0102120a0b090606030a02090a03030806010f0309030f120e01060f170105010302010509041d01060803041703040b0904090305040b0a050409050a09050d08151504060207050a030809010e0d0602070f0203070b 91
    0x3600c030f03044194a400300d0081d01e049001303958040210200946403410800124500c0590b552040300030660100a0100c03542c0c00041c00b2124140618080102500c161401818042c4c482c84190078418004d03000031a03203c154000c51016010300000b48810b80d900c01c17134890b204190303100c1c090200d512900034640101041c00381070b0489405035035641c103204401c030400c8010824a00d48c660076841d0107a0040040200380240700040c04282c01460700e9919101e01480c004100c6400c01c8440d4104000a201c2c1d145000107513171005505440c005240c26551806448034480c0e50004844120b01213510404240c0c03140c001c0c825503960200600550700e40d0700605c000d0b1003203404010001e810001ca80030480f4458104107621205c3e51070345600b9138414001040343c01450001401072500c0004060160540410189004080588034940340903e1519800c070680900a402410440c9507100c0305081d0742d44111244145401c007104641c0c8410301d14082240701401d610881c024011240002000d448060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194415854 1250 194414604 194414621
    0x30115050c060403050313050a030801060809032706120a05010305100b090402010e060f040306091e0308010605030a0b0603070e030601060509060f0d06030602070c06020610060f0e0406090e0102120a 87
    0x146083e88969030240d51a40005060220001d086862400440c02c01c118444400780a61280081541403207402001900c00821811181d0310411200e800c08244084038015140c400c14a06005d4400c040020218890800b090f0801c0201c4414840110340c540e20140c100c0f0301c660111080190404480e4080d96040140340d03512888060014026500410400c990780000510249ca4a609040c0741401e94000c3e4100361120f598544524003048035140c01c240f11990004404280142c03990360007004004140107c104000010000c9030190300140c2110300003c40c01007446486e482e103114000c100c60011034490303103c0e1145d4400066580e0148040ba8150080601503516184441c41d511149601039803103410140d030749050020205030319201520300d00380306401800d5814900300000349000809810140003503002c1070704203c0b10390401040790158034107040c08807101c0c015900150007000140c4c842c030012030502c4040104c12302e040d8000c24a008404003000401d0b01c45007451400c440c50381 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194417104 1250 194415854 194415877
    0x91a09060a0917030601020a0506010603060311030105010b070f03020a0b0708160f0203090f13060306061d010b12091f0c14090f06031906030b04110d0201090e0709030c0b03011505 79
    0x10200c20f01082d000c000860348aa0103004644110701240d948a1400310309900c800c000940d0b443c0c0038010482c5000364030751031400440007401705506040c6054010300c02d60000a01d1010041da090082600034424281e0f4103801800d62049450a010040e00b00c40b000c80392840d1040e080010400d4541c09a0090045943c0c01d5000318203220690017072040428592981d107034440d141c5000c20104549900543d030195104075008681e442c40c040468040480060641412103a6040180300034004401a14600a80c030310364120641c9402500d14103280070400c0d821a46003007401e21403000c00e80e64000d2613018059607201514001250b41c2006a80141206a5800041084100d02c94503050b070185811059030354940c0c00c480ca044000790b003210713a103038401c5a0440309003007004240700c100c0c050b0b544040c3d4181d845844503103050340000d269030300c18000c2601030180d4502103102d29100f1242c83c805558460881d02c516500e41c42c071000143c00c00d115890050500283d04d10429100c0d400391440821032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194418354 1250 194417104 194417123
    0x1e0804170313031e080309031306082404090b091b030109050c0d06060b0703091a0f031305070914060405151f03090c0605070303060605250204091a09060a09 69
    0x1190b40c1d065020000303c131004503800140100602207060100254003a1034007000442d91000900c20a41c0020080c0d4884818401c11100308000c1d01c2c0030000d5406880e040700c5004c947e0700a0040010002e00e80400080c03e22400c4008201440000103200000f000300c00c880001105074a000305401d1725141d20006089400c103503000c60507410482c510400040c4140300102d60360741c07103004a04c200d4010100039800505003142c10030500e824180d440310b005480035441450f101c1d519101a50a20001d84901584100c0d121841d090010078425a4050460240140302e07000c140008050000b40039a04184a40e20303007004504150601c84a41c4075002c2c01038a000d01c0f0301101d440025070481000415400e05071100090300014500d807043c0c0c40580440c5d10b40546400c2c0303a007001800c42e0615007111051010400203111101c00103420304c400c00000164400075031a2510208000d0508004001d002040f10340c0400c0d403004000e40c006201315081c6046500550340d0500400c1541c002c20301c00f6180e9401e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194419604 1250 194418354 194418359
    0x41509090b0a0e040c0909030804030809060f040206071b09061409070e060d090b1905070309021f030f0203010b0a1d0f010807051e0c01110403021c1e0804170313 71
    0x1120740c4010391060050005c8050740e41d407422000b0940700c0c0e42c01d080700091007000c100000c058010500503000b01060f8004c106c1ba01d40fa9519038111031000d040a4402d0001080380ac2c2007004d241d2411405e43c102d00560b103900c981d224070541c060320a5000328040003162181c20b80a41c20b104084038031450702603541c90204840d9074144802984901c4210345a207485440000101e4014056180030f5045a41c0c424005d0110300b0f00442101c0300500300d0070415050944c0c940142e03427482d01c8262440d100d529004234500d42035030150000e145041540d1711880c00440002034411102001d040e595405403030703640a06904031710ba090004501550107500650b01a20392120303500c942c2c0340960003160350401618058680042100c02c074980c1c4c41c25400c90800242505090f54280190340c00c02590800c0c00c1c2c10b107802c5a001a005c1c540c10305003070f05840b1141d10080d0030302881c109c0c8603494010080c219821443e50f800e00c3c6c1280c0c3d00c1400b40500400f1500c5d0781c2034483d400003003100c8400440350064041e260 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194420854 1250 194419604 194419619
    0x1204020405060d053304050a06050a1503110a0509010b030a09020d0b090106060207050f0a150212130302100516020405150a0603150e0108100b0312041509090b0a 71
    0x2805000c540d0003d200b07032040c00014908010b007021903600070542c02501c81010000b0130340c030f00a62800a00d2007a4000911000545c002040390513a40e100101080300d0b518203c8400080c91001800d504034540d5003000000d125624100c003007e000c0c1500c180c03200b99240c8007800b10048080c4500d0101e500100001843c200c5140d001020340d92004101d039040d4680c580f0340c0400f140040d500002c40e079540d00b00420140f42c04201050007010f0035600b003070b8202507160014a404800d841800b680d510144180802c0300c1c424050b0740c0314a403032078000540720340d00c00702d20600d080a1400704070b0044500780c2c955080c0303d0045068604082c0144461243c0080310760070b00000d0030019080140c4141c014000e13960560300e4120310000f6144543d00001c0e000315652040e510200c40754042c50b184504100180310201c0081141d100c1c41c0e141603404200010b103580460716102814061342d20f100f101007800300d80e0034080e0001c0207502ea5182d90301e0701d100e92616400011180d0507022039600c803000344410041da0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194422104 1250 194420854 194420861
    0x160f080d030b030703060b03240a05070e03030a230f0a0801060c080930100f05060603060d050a06020403080301060e0406080c10090e1003020907031a120a1202010e0c030312040204 79
    0x1c800c090155540e02c80428600038270b40030035681568030005080c0400c0343d50318091189541c80240385c60060500230844c004030b9142c1c840d40c06c90500b00244c000b1405017502d41201c0b010500195107a0b059a51002c144c181d42c00d030780007084088000303943c071000081c0c528821400610455045000703036107080081c00410000310b48030b07040302c080f091041c1c915a00c020011890340c0f4019402c1c002420410f84000917080840b100c15540ea04124a810140007150b15184103995100c80306030381a0000d540181442032400d10242d90080c2058000540801040700410155041301d03410f0700c4030084441c01c0c0080005072403080c028000240d0046510040910b048100e43d01501c0490400032070281d00d0318018011040c0032207200011208030b001c10421403c02e407408580c00b80c4149400c10801c400500d42c9121322003403510480c03140b500c0c0340482020308400e10100c517195903c0300480210110030b44019001c3c00010040152a0107007081c0000e19007400301c12241050403550244500d55919401c00004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194423354 1250 194422104 194422121
    0x91e030302031e01060801151101050a0b030721020f0123041706071205131b05102c1f020109020f100801090c020304030c030b01140a030807020d05160f080d030b03070306 75
    0x1004158270070a82807070400c0c400d2a0043c0203080c00462900d0b400c400703040c07900c040c0342e0211450103611404055800d00511390344a01d940d04840d40d1212a10040040f42e4940c04603a80b803240c070040500407850428a00001c1080702d1400004004940034076a0340c9480d1035007121408042134520303884068401030ba500241c0d10400d1200c90300540ca05076210b00410341596615841140703034450050041e0710345282d0b02c1e50400d41626086904440c41000714246001c51620700d40d500510b2100c0c01100d6076410070341d8641d0021881002500280784800902030b141200d0140c0c02150700d0307005d4007513604201c20004260f1045860b41d601c2c0c0d0b4607006000c80107180c4000c00c0d1086010034080030001500d030070a903000540c06010400425410130302c00b42d02884043c000188134103041d240400001d003040d8191031160390109e40038a50f2007800e040c91070070308204d05002c42800c0c66042c0c000c9150f28421030100309075840032085581061480b03509a044a001c010310590503071200708100006059900848003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194424460 1106 194423354 194423357
    0x30604200f0d15080d0804061811010311031509040c080a050f07050604050108040f0c08030c100b04020c0c0d03030f05010603020405131e091e030302031e0106080115 73
    0x941c5c40020495a0900800303d0016080c4000b5078000310341101c40b400c08004c0500705203451140180711620582c0481d00e04590305500c041400140ca100f070343c081c1d03810601e003040f101c00c000d0800c800410880f111101c1850100b0500820f0001e440705170700c030300001c22070103060081d4241441659040540107280a000c20829030f82e012280ca030b017080d0043c0720070550200038244418110040c0d041110184400100d4100c844000101401d294488190400c120300040c030411040e4451404103070100c0c2d0141c03500f503c0350b00d4010110307100704c5c0c42820300246850000307420718140d8400341d100078003181c2d010804100b141084c1c0c2c50390302e0002d0109030811070041000c000071000f0301001e500410184c0d43d60041020400d40e6085407030208a00ac06003140d1101c503140c002d01a6004075081d503000f490101e000906000412a01810384440e500c48120316800e04116140d42d07030f4418840f80 = true := by decide +kernel

theorem cover : BRFrame.Cov 194244604 194424460 := by
  have h0 := BRFrame.cov_init 194244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 194244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 194244604 ≤ n) (h2 : n < 194424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
