-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:03.068281+00:00
-- url     : https://prove2.me/submissions/9b10fff0-d46f-4a6e-a856-919dec7e8a0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364748201 ≤ n < 364928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364749451 1250 364748201 364748213
    0x3152d081f050a0603051e0106080607052203030207120501020f0d0606080a1a0d0302031204060218010e0d060903050c0601031104050609060102120c120f0d0c0c1a0a060e04 76
    0x489410710461450107000c0307018007402d442168140c90340003008040703600b20b5401c4000b20310040e80001b0920b40d2900350100c0d05010901c086c80c05a00030303032600381e01d070343c440c5815803000c082c2c03595141140e08038020100701080d030004041007210641c06569268580170304103a40a1700c241011007050340b200103020307074440307000d80d0200080f00c01c0796880304025210300380e0707140c150340020410302100341102e144602540342001d00140b00c207100c0d0040341d15103c1f4071000000e9400f000c4400341c410540c04102000003440d50b10051201d580300740b0740249002c03d84800035001255090b4050000365a0b000c0000415005408880b400701e4014201c500b15a50b038a00440800800c600050069007040b01188407030510341500f0340560700c160040e00410104040d40b1a007500314034220b160500c0303144803001d103402800703005003c44d0b0301038070b01c0c0e9039242e00c4000710000755145078a56070200300000710f1140c08506003880308035040112000c5030050352030312882c5002908c081c1d00060f0000754510144010040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364750701 1250 364749451 364749493
    0xb1c0510030317010e161205070314010611060c09030703020a0e0a0f0b06180103110a0c02091b030109050604060509070804140c03030a050d0f150603152d08 69
    0x7110383e54401003c1c9142070442440d603000e2040c1d02e089101c060208001c504400390381e41400d240740c684050310200c0c0028460a950080e500e140c0425500d01041e1084981840040c1c05411141440520203e50340a00d07541c5040040928568850110f1075200c0c41e50140710f004020b43d0028003030200300d83c032089070304018072080e6042480c26192201c0120280f03981e015401d075148008000a0400460b066004409045480881d042650301c1c28442403c143d0030015001d521481e43e10301100080a1052000101c0058000c565800c04121110b41300c440d10000c03241901c0d5036480220301511031402040151100b500a0359000e030510301007285032584803151a00c1240550403401e00f00c0c417894205070301c4100c0101d0054144d0010080b60aa0b035002e900200302c03a840403400010140000c0009800b200c5100160b00c14440c0c168504005e500d50601030031300d052000030301810031039140510f4984094200031000e0030b40d0105501d0a11074030304d142c0540001380308070350980300f6640019280032204a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364751951 1250 364750701 364750703
    0x51305150f0112020f060a02010f060b07020406080a020a05010c0503090d0303240b0901030911060f040305120c0a03110f011e0e06130b04051e100507030905070b1c051003 75
    0x1c512000000c1c80031051500c2070f141c54001d0039403082c8420780003c2c403c065011000f80340c15503480c1d94400c030207003903907200d0f0720f008104a45800d5280c0c4000e02c100015110300d5070012220354000841440569994107140c5d0031503100742044401c5070303800d10780107045024412809030f02c885940c2e104c10600d0f405030000c2e11314540c40002a007150032400d040e440303501c5280c000c1001699082c0b0a055055001c0da02070140503010304500055131090800051407035000c00300d2105003d50215040041000800181c81d4080c100d0300030b07504140da03100005940e500000e06c060108280d80b86903504014050090145000d0350304028031400081d6a101001d101d09502c0401c212458680440075062005c90000d00031000508812000070541e00e8170031664074082c5c025281d5000c0c02c94012004888400103032741d6400504054103900455441d40012110300a042400b410b041140820014034042221000e0714285072000383c4403464440034011f081c40400103608440c3c608414045408403003200b103005c807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364753201 1250 364751951 364751971
    0x3020a08071a0c030721060302190504060506040e1605190f080112031b05030408031303151803120f060b04091b0918020708031806070305090c0405130515 68
    0x90346503c2c0c0c010005200865400001030380f19605440442041d801c00f42c0610302c000c00210380652240c000070541120111005180071b00380900f0020340c00c00d4000c170070041500303d4a55040c2441c10784155000c0710014101450b5106502e00d0f003000e903010320b0664000b2031040240202d4039a524001410b00040c1d4042180132524403000020305565111101d103070035a16564500e18030782400c1c03130548080c015100403140c60006100105680b0b204102516201070f41c526513030300e8603255042105ca080c81c0c0341e0303410140a00300a24903200d4040c00e102c00004540c0340c039100a003a84074140c81d000500307031140c51044550138000c00085020500f00507000380c81095404105440b80c03080083c0d451001c0c80165004a0001041000810a8528051802200d55401500c0c0842ea9030381c203d6980c0c0700302e40da41d0700100c4a800103040180204030791640f10040d420200914104440202e585144005003c0d1155480d00002034016030002d1405e642e60f54404100c44118114021100c1201801c903840030306 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364754451 1250 364753201 364753253
    0x3070204060812070b1803121023100c0c06090503101a060f040905161805030c0f1c060e0d021b0409110d0302070518060f0d03020a0807 60
    0x1440100f400d1142c542560300c61480c0034000c0d5510794510100a10b641c41465141c4800c00c1401020301c001d02e0484140e80c580c2103a403504070700182d40c8403819009101c12021081e0240304101e8001100c05003050201d50360341400c0100c100888410410700c000030300d00d900340400000e460340c1000916041e69812001d803100d0b40d1061807840c0440c4e09035407900301300121030a900392607402c0c010000c0401201284203545000c0e01ca5980710250380302942c0030040c44a0418070556255409007111788200b00e070304007180c0341510344000030381d54020320040c072403041e40781ca41600f05a1b600c800070808070010b034289070350f516072050a06400400405040404901039240ca0410040c80800e4170020003e440401c155641041c0c02440000c107852141201c1402c1c0070400782d0b80759612452070541c61403003913009040d0ba47c00d05040c480150f146005890301c460b2640c05100c195500c120185201074000d843c00d007281203503824220300d400442a0090084440003404809212004201c0500203145d045d500c0c00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364755701 1250 364754451 364754459
    0xb011403040206070f021923010201051509060402091c020f06030708070e1c0c0303090906060819110a080604060f080c09072307050f010c0f03050604021204050307020406 75
    0x24140c401200d000703500c84401c102113000200301c400741c104d01c940082c1881c00f005038006030091051074250015807003242c0259403401d0340140ea001d6056511400e200a00060510541c0c0d01050740c0d00f68402c5205e1064000080c031152200d605031190400c0040259075150800340080d104080400026401050451113240c038506000c1d007203034018603130b55540068660b5108001c039400c072181002e003607006500303040c0d5000020400c00c01c030044174000c0982000345407035858090411401e43e84030700c16141c03c1ca0010411141c01a045030361010300c800d030052440c588446072400600c416284c9005c034000204100540541c010100ca01c514016102088402d8413003003508042086c40c4941c54080d4810754000c6501e0800707019403a0024060f041403200c01950081d9030010182406200d59103007804101e00303003030040c2000040c1403002c03402c008125100c3c00340d00051819034000681802c2c1034503036000c10700c55141c2d9070480300e6400080000c2e09030303810039203003154403940071040a07031040782811b00c041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364756951 1250 364755701 364755737
    0x2130503010608061906050a06111606021e100212040c05030a0b010506130e0a1a0d0b06010f0e040c05070210032a0306080105150306010807060801090b1903060b01 72
    0x14007903c1e02000108800e43d920074101c20082c944040c984000c80c0c580d0000100c0381c640c482000b001e000d090b00c910b541008081c00c818540f6519080860958500b00c00c1000116004203001440c000c680704005400c0c034818001501e0f1030304c80c140b03a40005100155011035940110a0315014a1040c552401d031640d540080680c0e13841d8255003c1d201c4004100100500c2c501440201242e400080782504025601c0915200d205022119078500d1a202d00a40740d50903a0900050340311402190b03030426002840e05d400040500007000d035070511000c5810546e101f40116008004a18001e00c2800324030500840100180c1064104031701619441c804c44600710700a0051410040b01448494110441000c1c108440ba14801d124001e056507200c000c55030150a001d00c030f11503440580a68004e2202c082450314051050384001002d401c482410700140b40d000351181d0444000d80404075201103003000017a045290700e10051450004080d0000c104003071074100e044500030917200c4480e16941785c2c001c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364758201 1250 364756951 364756961
    0xa1202150a1e02090d0b04060b191202010503130c1d07080f15060c0703350a0305060a0e040615090c0915031d0303040203070b070201020c0907140406030213050301 72
    0x40591842c0340e90007500314040b1540503006104d4014035141e1198125150b035800d0410070381d02640c0701512400b82c0c05160a021188407260b09418000303803c0140360081180340402072040090404c20000007240c0001422041a4110b903009400101401d66907481c40c40e0300f44002880900348444800002d14150045801e03a00c500595200d46d52156510807030805c0006540c1704a5602a00900c160602e420003004880301461048004214200460848850b00c07601e80001000c04080078484451f0b8a24003002e0380c45050f00ca04010949449140010303100f42d4050700002c800d14088410002030100642044500150301c2d000c04110640b9109550180c0312600c0e80440070500070002041040102103109004078624640050b44204070340c400d940b0790300d8032486040030303074004802e010551a00340420002440b02c06502407030316140d40d0000c3d4444189040040c4903c042c03000095a0a00030101c00c0194000074254540c1ca6440d88405030083d04455200e400c0e850032040003065a046c14030507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364759451 1250 364758201 364758221
    0x170c06011203080f24040e0f011a0603090d030e120706020703090f050a1a12010f0608070203090918120a1805030613080f040302060a05030109140f070f020a1202150a 73
    0x380c60121443ea809032003584103210103800940d2010742e80c0420505010300561003101e40d0010410101c48000c426201d0b4401a00d94850072f01003050007060100000c642a28522600b0046403241441c09244c0c2011040000268807c800065850400a96070b004103079652080c1c03244c4a500343c82e203120003888540360140c1500150281c500340007044440c3d1503000000c1000345902c2c502911046c4100e40f5102c280e10070b080042c25001d05201300f40d044840e0660010391440218184900d007400600d0601018000c0b00d0702c8801024070446680d41400350380008101c0b80f80041c2d0320701c0d01ca0401082d00c2952842610b41101c1000f011511340380101d007480c090984080c11650103141030721000d1a81d03104020004c0014010400003005892b48005030207035440c55100e213a1250300d05461781c01074410840381c030f0702000d40c3d2004200d50304603403122144c1c10400900d4000030300307103001c00180e283c0300079880c2c00b411016240b00c0505086a002440c01c050303002c8449500c400752120541003041c0d41c2c0c1b07500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364760701 1250 364759451 364759471
    0x105010609140f04060806040201090b091f050c01050c0414010503040807020108100806011511060403021f0f0f05160f0806010c030905120606030127170c06011203080f 74
    0x30204400c40084110840301c00004007a00c00c0403c070000003c0488685503c2000c040c0c000c68108030544d07820030300800c0102001d2001c03625000088002400c0034001000044400314030803a5841c103144610256840504d02c00020441420000440318281d04288241101d1550015140240d548210142c900990340044400d00b4182a58019070340c1e540014000381e034541c80d050340028500070130080503000b00300282d10100c1d80740134038500501c010210340b030b03401c0b09a1249003070000103640000d1000d14030311075014030030f88450a0011403001e05140c41c2c00c0401107040282c0c00241c442140d00017030180c0c0d1203a03c101f0405207611010f1340e8114840da0050007099809000603025400b07410880c0c034141c0701c2d24107032140300e0300c1e0f8000841c0c03040c5541e00c400540e071010082000340d040c24490890344040403000000710300080d01e0821000000c40400400968054a2072514040200141c1b10600a004207942043da11010740d094800002c46064000800303a00c00b207580c44031038910050189072180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364761951 1250 364760701 364760717
    0x406050409020322030f1707050a030504080d0f150504060b0d0b0103090f0f02031509031e070c06020a050c010309080910020a2001020f061006120b100c1401050106 72
    0x50100d030003500020504c0301c2c40d0f0f85041682e02d1040c029001c108141d40f098070342c10345803504081c009041200e0f00b103ea03819420b41c04140440395030801c0964500d44c01916011805540300d240c001c80301c0c052140224992410880901c408690741c3c4c005a800c2c00a00011a1409580300100b0058900e0f6100d2603421200411194804900940040b0b80d1a04181404503040340aa690420b0100f02c1c4042a65490302c00100d090031458148011a1501d0000d0200345050804d2000244c0380d11400d441782c0f400b40c0d2061805d07002100c2c80300588030442c0d009410340c00e0403aa5000c003e5150200710004a8003402108851000e960207842a00807450b000112541048084000d110b0300500c050050415031082014110005600120b201251191240d02c1810034694400181c94440c00e90320091480d000340d410801c2d02484840d220b8101c410925050810b4000610305600801c1141d1456400c042001c100c5a58550003003d05c1902a1040c11529003000c1807101e010300300c41080c050400041d81c0f81c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364763201 1250 364761951 364761959
    0x70602010e070e180a02060a0c020f0301140a0e01060305060103060e0f03250204092a0e1e040c090501090501061b0b2701050123240313060c020a1704060504 69
    0x1c007a03030b800c030384d0ba010b0486240740825000141584c200700074403800140340b90703006811410b01c000841e61119040e8000c2c400d000c64070100c481003900003045540c00a603100c0724121041f200750803407802583c0140580c0c000303507124180003020f07081d041e4007039000c0c0c0b0602c0a8184010b030000300320790342c2909615111311a507003a110040d0310b803458144143d0b4440d4031041d9840c0030800ca010504000c1007100d031403203804081d11000e1b0340a004140d22049071440c1c0d00041021036111064402d040d0840e08034030300c0e05a903442c42c00d52038604540e0484044103207010000b1905809581c03100e07040c1c1d016500c481c071190204540440b00c8405518000b4040074005000c40c0c1d00301d40c0780390344003401c10301401f0740c00705403002d0060304d4211042680806004254040114548442605001160082518400c140c0104a0103811302104050b00340c84003400000000740100f41d06500480b03806078030410034801503031600c20003580c8940355081503417102041d0240341022020f01049508481c8561030301c9050078a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364764451 1250 364763201 364763221
    0x50303040f15020a030905010b0d020105030408130308070b01030204060e0115031a1203070b07140a0f0e120d0f031a190e01081f02250c090e070602010e070e 69
    0x1480303040702c0c0a079050803102c1c040c1c02c0c180083c4c48a4015683c00151030f107000d0414a094401140c440e2b40210991b151100160340e1040c04c80e0b0f40240c1000225a03641000034041c030400384140e001400d02007003c20014100514108054103d038002c542c14000c0320344814484150b0942886402800022810b034250345a003c0d0704118203a000001350344134060040740208110501441101c10385810004d014420861041001ca8020b41d240c0b8011a03034172462413840ea500d10030641c01c01d00744851050710130b0300d0343e201e190003410b8450301510300951401051002551604810b08040c0400c0c01c120040c194076100380f0404000f446401d8400d900ca884c9003040c0b1400c100d03000d4111504031180040402e010305020364131402056504010050003980d015841204000902c100c20220700401144013041aa00a4003082400c55511240301d0206803a0024105656501c40e0400c1404d16801440c0c0034800314030032044518640082c0913540304907141079160240381c040c800d40450840301003002804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364765701 1250 364764451 364764473
    0x11a0d030c030905060c0a150c0905092a09040c17070c08070c0b0309061f050411070c060809190507031101121104050a05010c2d020603041203060e0405030304 70
    0x100038180f840205450350003185c1d0540c0900548052548038003550410480f0f241011a203c2000b244200407150400c5030017814000c0600c1054031500c603000100ba04908108161060604004040159510450440450b5402904800c0d01c11450300502c100303214060714141c00c40034213001b03903580255611507050343c0070b0442d4582078400c0300c800c1c40340000080d525414100600b200d481800d4891400100702407030104000c00383c06100d040c520048004191408001058a0b0708440c00b0546290180403d0880e0190060160800c84000000111a5044480180100c1c1403e042e210742001c1c2c0e60400301d1024000c000207020b42d110400030030100310b20300c4202c03141000503d04080642201c44841041e2030201580d40c000380301c001005c010b1031800a9400c80204030a00b441700d4020900d07101c64180d101d0650a2035203880c02800c0c8515000c0b942400b01082c10b9000f07180607200d06250804d6082d6035203000c0000042454a100824603011600c0d01c0b51103540d01200035403450b80c4035030f9501c0c1100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364766951 1250 364765701 364765703
    0x4020a0e130206070602030a060501020f030406121b030e07170a0b1302100f02060618060111070f0b03010e01050307030510020a02070f0312140a0905010c1407030f05011a0d030c 78
    0xc0807031900c900180d84040c0101522401a03a0258403803d0085041c8101d54a60340f24a040d50310100c141c061202c4c005c81030301c08450040c14040100c2c1d001d0603982c2c000d0550405c901d400c01c48905400a01650075910504111082e801102d6010303440d111500381e64001469403281d02d0b4000448600010442c00300f50350320002c4203940c242c5005141e404100900c0782010a0360100f1a9541c9458800b40d040009070f03884030046a100483d520110f0318070a04100c0034020b10b04002507200c1c100741a41d410440c039401040303030f8103c0c0c10b00355541720164042ea400c00e000d03241d2014a80c0000051601c8c0c00140d010540740c10601401e4007001a411020084d80015440000c2d030199240c00903c01c0d0310802004025405061000c18186d00c00c2002040704c03c101c081500c540c0ca0a00c800b100c520742c041a02d03001d4440a0801c0b0071900795070704242d1840d03040e465405c40e06120f08680401040840110142d880c3d120b00001d200040806101a00c0c604c07101c40c0140d0003959400d1000042446104624415 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364768201 1250 364766951 364766971
    0x60f090604061d010602010e0309100f0908070b0d050a0605092205060411010e0a061b0f1407080d02070303120203180105090d0e0d080a0f1e020706030e0604020a0e 72
    0x9030740d40b8610344500030342d440482c1941ca003c90040088640a010b1004445452030203036240040c0d000003d04192581e0101c9001c01283c0b1500b0300059000d03c8006000d0504c0c00300701d5054035070318840400168000607801d80524100008955850460700841c01901c0b03008220031415a924403191070041400540c0f000c40e089141c00600c04100e0901000340614001c84c8080400c004400002d003080c4d80c140307244c0e40900312a030001c200e102c2c0d108401140c0c410700c1143e04400e40c440f07402c0c103c5034002c94400c0942191403000124104240004440c0221103655007035410340f5800b0181641c4400c10f03440040d000ca04000300b400040000e0b5030045600c103a94146804041d900f14060508648013280c01513156886103840e024801c0e00a240a40e00c0c0030102e0307050400710600d80d110f1245000d041c1c04034013030225141c03904d104607004078540310600f2070440585c1440b20b5140030080d0f940500380b003003001203071904102140c0083d02041c00341c4170300d0300540b0040c00c89140412908210308000c1202e020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364769451 1250 364768201 364768211
    0x9120408101e09030201050a051f060e151603110a030215061f0e1f09030f1e0309090507030c0507170c010617070f03031b0303140106120b010503060f090604 69
    0x700d10b455201d000700c468001d50001489140140701c04003203480c0540f03007260001ca00070110680764021105c843c1510b1003890841c0c400b2440b00b000c682c500505080c0b4400146002c1014004000d10149007070380d2a000c0e50307070030303141611000d00c5c44e07161245e6030030180042e00555140800c04c0e415050243d0030500203000085032007650300440e0034058444240e600051030a04ca440c0292034a0744030310f2002c0782010030303540170311070304142c05440d21015100040809040c541d0603030a01a403d10035402c003449a6035141d2903100320f0b181c0100903003520b00802042d6841d043c04101a54400e1082d00c98503507030340c0ca60a10b0064240c4a098100c0090b1101d040d508408200b4900722500170701803c8010805601800c80c18202c40110504010302d41c0c200a80c1e801d1804410800b01e68840c2c0c00f01c003d203150016580c015412410200c002d040d048400d8410a80d51a00018006501001201c09406203035002c1200c40484001100c80b4403040d42d0b0036500601c1c400240e81b96140450149800150040c03000407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364770701 1250 364769451 364769501
    0xf130c02070518070f090b0909060f0d1a0a060f14030703061802030705100f050d06030b0403080610020d020d030c090509010b221809080d140912040810 67
    0x50700e0600e2841403803030a003860044c8444039420101941c80d000b02810305080d001d0a1101003c0507001e003d081c0b6100f50032a0f400308000f42c55540b0200000b01c000341c08009030b00403a040a4803079048000490540e28103280004d284404648104030a84a21803010210f5525081448050780c2802c0c40460b814064101e0000006c2c03480c0c400e030301c0c205998100702074120500d40100750030711880340d00090003004150501d402c1344d580a0030000c4104070504046480c0c441600f2600001c02054000420300c1d0a2074090205164124011520030703041100c0d10007010390500003c9032a5000342000e2005603120000401e00140240c00c110010081407510400c0d00740d541000824000307003a4400000c0c2d82c1d00065000260b130116001d814140d80c0d841038030399018500085841481c04400700644c0d11036850b6010000c21000381c2c2201d0700d081c1502c40030700004100d810440708a04041c1c41e101010300c1408500040462040c041e207044a19030400fa01170f542040590001811500300d101500c03903d0f04010034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364771951 1250 364770701 364770709
    0x10911030c0702061201080c10031109150408060109141f0605090d05071e060503090303011a040503012d0e030924030106050d0c030209060a0f022a0901050f130c020705 74
    0x1b0b00078020040100041c03240c0c82c0c28016010301c011024000c05013000001c0101070406012502d121005440c8411000750010a001540c040d41d0030074a6940255000010041840d8100400034448820212002d0311603291044d8081500098112300300d05160040005d05c0c00740c3c0141c049018090603056452078240e507001c2c1442c0540d0800f8112400555130f0010071001e8000d04400340ca00c0c1e0400d03d1840c1805030840b5540d000511907000d0052081d070003400c104140c00182e40c01071001800038454030780c080c01058150074204841440101007007083e50036007480c0c0e003c0e00101c264480051850001803800340f00e01c4d030b40075135520300d00403c0480c04410380040410045000b480241d44081c1c58121000010301076440941d02d04080500502000503681e541d00d04440c440d07002414000e0002604040030b9090140a141014005000b20411584680950407880441c0400c6800c03081c0c503070b00e800c00c000c0492820800c0c2c80c0c010f000d0b0b9a1004010b8580d41c0303d0550704019004a40344655a18002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364773201 1250 364771951 364771987
    0x40c0b0408150c040e010b0d110d0c0e09101811041e06090f2c1617130f0c050904080901020d021f0f180501020909010911030c070206 59
    0x7409840c2d00c02c0340312426014079040740e81e80001d49051118030345442e040c142100302138103014000c90740c0c100107144482c1030030740c1e40410035042c3d400042c41c5d282e40da0580071030300a02100d11017001146a084078130b0b55034034085072458400c9200c01070742a0458200035050311a030bc8036000c1500c0c4141d41d0301c07200d4202c0201c8030241000382038005100c030810f185880c900140c400264421014040a124280b0210001580e540c5c02d03136030315000c8086100c0140901c51151303001603500c090854448001d008001d44142d41e584610310342d940340c0b0001d103c40c001c046402640c040700d10701a070a20404c03a80300011001c81c101101c290081c2c002c0760b4001e0f01c2e000003500c1c9100071343c0c0031100244001107405440d6014001c04842850310b0001e01301e8100014100e954030507408902d00b0560b40e80c1c241900c940540c0e0707400070001030f60082403603495000c80d00d4460300039440010258800c00da01c1e0000103134810349014000014810b020841c0c00e40d00c0c0e10300035032160307000400100c3e032211040c405a20183c03201840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364774451 1250 364773201 364773209
    0xb130b1b120112020a08010c08010302151e13080304080309042324060c100e010905120408060c030106050a031503150605010f02010e030919030803160306061b0b040c0b04 75
    0xb05010010040c03040010408140d1b000741c080c0d034100583d01c0c6101d40c008007110704594050703601828210709500071408510070782c1700300203010781c0b42241d500900303100ca005082e02807a80e00020401c10b80320845c2503a28010361058140b5680100802c48050800307802c0b2004544000b0002e12541c0082048103010300421101c000c50f4001c4007a41109a480d404962003000b541540c9051810903544005515030903d072001d5140b06031a9860340c00403802c00d61110038050b400600f59444d03005018071040321507102d4400c0c0400c1d44900c402048044940c0800ca9040f105d0540380d003854070080c01000e90152000c1010b04031040100c050020208034028100900c0c28122240000c21a08110001d03115192105072442160b00d00201016050800801c0341c064000031520030030201c020040d1912003000f25000104044000310501113410440d090b41101a540c07602e0a000b9a600e9080c100c400f4041c9110a03046004072102a1010445080102e42c0150103511079464154403424106101d520540c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364775701 1250 364774451 364774469
    0x40305060c07022407020f1309060203060a05101709120a0201150b0a09031518050607030509060403090323070f0911070b010b0309150f040b130b1b1201 67
    0x100b1004500d000c40580a584070312180800c501c0c01c8404441090780030f0500c00a000341041a00440c03281d446401981240c40c40100070303c4000317002d01e04000650415507050703010714a202c101049600d04080c64495070010b940c0e665514082122621405400c00741c00700c0824010014208070621a090003044201c3c0c443c2c00218403100e50f2103503505008019804810720380011702c41d9030b00050b8003420381801c681c0c01183c429034041c0d1191a081c010a890403400d500c21003404655804c10902150036440b944143d00c007041580d0b602110283c40b0002103c000700000e44500d000c1c0b00054155112040c40c1440c00d554520b00562112501c0c5015003542201d046221640c41c108400e1449001d030301d60140e141c090381810000c4c1940c0301141e80c10103010740e00100c40d001c4001104c0e030008000b0080c0e4420343ea00c001403e0304040c40d00e40020303101950250380e04101c07000060a1402ca07561801c0f00681c1c05140d200c01c2d07680d00c26210701140c2d15014400c00aa4041190203400d0a40c1c540079400b910703405c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364776951 1250 364775701 364775707
    0x60f0a0908010603300e0d020a05060301140a0f050108040602071a04150b03011e201303020405010504020309150705120906160c0b060103230a050402010e01050414060d02040305060c 80
    0x1400700c88070305c66452004070f24204101102c04000d50003421001e06080a0b02c030300c280d071920b07031000882a084070380040d90004408000058190b102028904110000b9074210300e009032160400281110940111800300d00401c004c02e00040d400c3d4020b080c40d5009400c00c503155a801518400c0c140b2090724250b8200c015071440141d04c1080d4840d5a000c03101c218002c01c050940000c0740103a200300d54090442569a8042c1509072281d40380e03103210328500f469001640c400e00300e004c000a102d1750340002c3e406540b03001d0002c2a6410280300301e0b0f00452841009005030102030840340780d200d03c01020312080100601084100d0344c3c01030f40b0640034030111005003100785001800d029001e01007903001e50400c04180c00020106080001894000c2404e29001c12110568006822181e05203804402140d00309410000c460314541d1219003d58803d0b40c0c5c2c81c03155059540111141d00032409108148800386041507203a1511200a0036031002d540000350525903a0b488503403c000d0221a055146034dc00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364778201 1250 364776951 364776983
    0xe04030804050d0e0f1e0603040f1101052502040b030d0305150109030305030a0e03091002010902040b090105030c0d05120a020f060109051e0a1409100b040b060f0a0908010603 77
    0x512110201000515140c03805001315000209181e0160040741d02402c020301c81070103240341401c426000030302c0140c052940e90178249001c0203c034003a420213503076030750010341484440e611550855810500303180014404401504800343c0c50240320300100d03071142c0c0c0c03044082002d4505004590909410b502d0005003031400004a1114088002d50581080180c80d020700009130050192504001c0680e130001e022420703404a980396115202401e640714400c2c0300003000142d41500a0072185100f40d43c203006c07019a010900040ad1400c2c02190b90542088051488030b081c00d034450140705002e03100700d030369204a0b100351101c80d902645080006802408403140e4051041040364010852080d0400183c940b041a41a200d00b2030100c001601c07200801107041d4040f90b17040380c40800900660002207042022103182e841e03001403103140d6a036050820707031704103850140700760100088090720007480c10344e070312013504156481010100d0a00950384400701d040c0c6024443e506c050340c4a01e010600e44401c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364779451 1250 364778201 364778203
    0x3060f200f07142d0f010515040c02010f061d0c07020102060711031b060603011d0d081b0c03030708090d140f1c0603060c090f050d08040e0403080405 66
    0x501000840029010400440c0c1551500708072001680c0202c1c00c50640701c0c1140030141041444040c40e4001c40040c040c00200545028400c01e115840c50300310380b4541508600c20782a51000c81d401e0046e1079000d201a00181056042100a062248000505114464100400c035041c581010b07c4004081e1120003000800c402d8040c2c102001007c00d0b0b0401c0740c030b980005d5403000000d04c050100602810407902511041050390340c07840341003c18143c844904452a580c4001c1110707240d00c40e40c200418501041c051034800703075100a060000d4402d40b44070300401c1e01d41c82c00c00780c601091101d010103454503156004000c0c0241103190000f942c2c0d40c0c10000700042c42c064014007080b061350070486004800039004518201e03400d8000000c1d07502e81110010343c4d0340e41d000d070f41c0001c0d001064000341c1d04611305059009106680c4658820092030b40d40f00c50440d11b01e0454025181211455801402a8507003003040100305480f468210303190584904000300d119409882c118041141c0006100c20400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364780701 1250 364779451 364779491
    0x4050a1509061b06090812130302010615020a14160609030c0501050306030606010807050c07080705190b030a0f02210a0b040c0207060507050309030105130302010c090b07140703060f 80
    0x610b00030180c0e0081e40c01d124120700380f100d0000c014594070100d8004000584094416036100c02e00c140c0a1403a0101c007044242c108400d0480c015444c180001c10020f11980440c0035204a0380e00400c003d101990b03030b40e20312081075404180244992030f810340e0250700000d40503025110301d94640003000e00e1840c06002810040c2c20550504c9800c0c401c014882d2000203c0b1135210300f00b40382052141d110b40c03906841910450010341d107a03014020300400d10041c0096100d084030810348034803441003c2c20380018000000d0340552400f03042c040000c16000150341e0400c02081841d210014075240381180360300c10101d507000c2c000c60310306240820003056178a20310446618840a0300e09000064003818000e403030300c040303000d0070080c000003003000001c0c09000c005481d9445405002040117042c05410745903000041401100158200350400c2c403400d202d440901d003151040c05c0300e0350400c40995921001951001380d10115845448d00000c0450514022048100510580040d143d0b18400307015400700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364781951 1250 364780701 364780709
    0x32205060a0918091707060603060534050a1d040501030b010510020d0801061209050f030415050c0d08040201020a0611090312030c040b0f0409020406031e0c0906120204050a1509 78
    0xe813800c00361401107409624a400421400510140c0d541b01b00e2901c1002400140c01c0074004902c1c2c08100500554486100c1c08019580307015903031801e8906d4624603030310142058040c00144288140619a4011050010040002c100b454420750501000c203049605c01d80c0709588030700502004200d87d06020501070440c418a20151010345a1500094901c18040c03150000b005040c51740d800c01c408142e801504804d0740030040c1d400740a018045546e40390418002e810074940d4100c0c4510540340108110307414004000050300300100c5001c8151902c010040060f41035003c0c002001c00040e6451040e0114407505c525825203449002050620300300511044080c8103000b0400d01161603401c03002d030340813502995500743d51502030f0140340a882c026a44003141c2d080c00840c010541c0c5401d07811802c0c9481c8a90850000b03d0170021030607040e98801240c000208280d02824464940300b040b800003241c2d00a40050314282d90f0724080340c803a092592211541d80e0440351480c13601513103c02e84800134 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364783201 1250 364781951 364781999
    0x9010e0603040f140a081204022701061b23070512030f0a050403121d09060f0108061c050c09011508070c05010f11031504020a02032205060a09 63
    0x10725080c3e4503080401c42940001e050300c42613000d11200d0180820a041c51a82c0c4003e086440740e4040341000403184040e18102d208040c4603014041d0907071400b040e821252462206203140340d00e8144c00b66500c11202c00700b050810070350240c0302c0c0400c0038003084040e9103c0310800e1207c80145d00451500f040c4443d000300e032155006002d089441500007042d074906036003c0c1807066541400c50b2056a440c442e551000f0407240e49500b02a9aa40d0080070b50310a001c2080c2000500c003001804111851104840017684140007001c80071655205916903a800200606400d800207071071408d07900c483c4021041108c0c980d202d0380410344542045d01503140100b04281000321520600d40c0007a0a40000500740d204029000c031440c81803000c00d412480d001c412805042201429010018031140d0084600e0081b800c030304656071585040600c01c079401180780da80a542040120f0658044104486c1c0300c6081d005055140490325544003c0202180300194440340c0c0480d242012030408484800d00001e04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364784451 1250 364783201 364783207
    0x90a18060b0a091a0c2a041b030915063f0305070c1e05190303020d0311070507060206040c080109080f07080c0f0705010e0405101202130f0209010e06 66
    0x120b41e00009a801940d05441507850418007030513801d0b04502602c0c40c98881c2c1c0c42110341d1200c0004803200104101c10f0484038000d415502c500030320064031080b501e04000d011500c184070350200d10a5102401c0b940c80f401c100706214001c0090b1005030340550300021900a42e0340c20112076425202024012601100c8020a14254080c14410340010324140a418404000760203001c000641c200c0c0c501504c030340b01c10b4001c181d04d03080c5010041012030040c0f901032a100da220444d062800b43e504800ca80c6e055005000c9034841032401c40240040c2d52804030f21541c14805840014414003400c00a02966401000c15141504042401000a0b0b1042c1c0b0540d250415942c041071082c41190b00e140000185180c0c0c48480385805103036803007141408040c501030b404504003407001c08140d0104a078404d0303032120340802c1c10b8410441180e00c2580d000340c41c0c0d28400000c01032810b480f9800c204007070000346107903605030007100307114161408000b0000341c5e90390000386000a580c1001c81c80144090940b150b0381 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364785701 1250 364784451 364784467
    0x3030901060f050d080f0f120402010f020f280803090c04150e130804030506040515150f040c03060315150f030b0f06040e0a1a090105040206120606090a18060b 70
    0x140d4108504014105074000900d02d4040f44440040340c8200b002d00d9419a23480d6003046c5083c0d540b01e8159003c9002441da000c2d025549803000485d10705100d0f805000d000301c0421440c0c980c1c0704d420070003400c8028807880c8510700080f405010145214841c01c50182028042000401080700c1d00d66800400303244101000f0b203c506900002c0301d92007c0b14900d102c004207a541096801801698001041031090340c0410042001c0401c2c2c96007040f040c0c646105040d2100f038080e02e071364200800010342107440d035030f50380d140c600d00743e00719001040c810700b0002885034991307c400c0d0314440c0c010010711500d40c036506d01400c8040704000c85801803230300031140c408203819540e0300a03043c00b02503c0044628102c20100705590340340e5101c40c1800c0030b40d2007184c0391800701d8500601e400c10041880501e065501b0001400700406000ea54401d590080121f407401488445040741c8410261001d9004138050000760a141c441c00b85110240c0b851100450f4502d0700c02d10114107403911034104008892050020003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364786951 1250 364785701 364785709
    0x50f12040f080a030f1b0c1706090106080c01230a020304061107050618130e010c0e0904031e03060905070306050405162f01020a0f0206070503010b07030503250203030901060f05 78
    0x283e143e40f16207000040d00110860340e8a9404000502804442c94054001032051000c00d074000701040d404207807489e66803a410080d0884032a4444c06115070030a9041a00561080103100c41000782c6180c5400302c040f8041404595810140011015074400201400310640262000d2105100c000092440318142008620103002c0c00300c050103040040209541d00e0fa940311101600c20314142000c020040c0720341000c60192480190200105503440c2a80c801814017086a03441a601522039081c00d40e18609154032a8049018820130151341b040c0200e4490a07900806000c0c0016580c007140250404040101320b61000e004071b8000d035145240030161541101001c2c100300c864051800c03075010780c80050709040c4500a54043c1d5544001008850203070014415040e00915a088030041d80d42c5140c181c2d8944420301924450000034065000060301c514010b6074450403030b54603404000000600e0b102808160300305880960404802c10031310300c90911440c801040c00f02d9580c803815103008041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364788201 1250 364786951 364786967
    0x18040e010c180b361005090a0e06060a0f0c140a03120209010e06091c08120105030a17070c210b060307060e09040f02120721110d050f12040f080a03 65
    0x6014030b1014000d030700c00204c6280701d040612024160031400080b8034401031250344480f1107140303d134914101c0850880b4044d0852032264030040d00603071500f00d45020680c6c90440080501d82003082e07610a050000d100c0c1300858003070001c2e0380010410000c1c3d5140c00313050740c14890500f01d02c10b0300c140151040340c4e071322141c00d005921094600c2c55641000f81d01041075030320348100c40c0e000300030305103900760400042d00e00400c082181d491004420ba41c1316000c16440f507001c441c001d065008080c3d1a08a0207420000825000d44154031941070203941e22451840c5043d04040104c2e034103802a0600c01b1701800308911507004500300d025000c403038100f030805800b21508000750790181089800081c200243d00e4000381005030024603000005a402c11080c2c0d0702d2586000300060740000000d8441894010f0b903240c071031254045400701d154103609080c041d0a800c2d0003000e441c144030b11051400c0072001070164503290310305d2840c00c40d40d86040001036104000243e000391815801090000c3c0402e904c6828 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364789451 1250 364788201 364788247
    0x1611060f0403260a0b060702091506070b040f03020c0a082a120708010b010903031e171003110a030c03081c020f030103110a0b18040e010c180b 63
    0x6090240c4940c203084403c803600e40b0b01c24082c10642d8054180c151800b00368540b1a072203440080c000c3da4149410702005000b4400025000f044400108286a1900d9101c081d1901c0290003142400000c1c0ca91010b000c50695040e100040d0408141080c1507050000092500054032080071a0349405201a51800594040701c000c00c04803c408425900c007440c140407020f40100388540300386410342c105403283d0441c0300f10600d643c608840806a0b5000c3c1891004a0390582c95401940044e418a4464501103000840030880c941d2400d0340940c070b032001414000c00800d64070105290551806118001d084a500e6104205405081001401c41c1d56513030180c0e41e100700215103130a40c02c2d81c01c151481c4601c0fa0302134460300119144c2c003600c1120740903604880c014120010b01c08102424807401c99454010109422020440e8031401030340c080e17001c101880094070000300742840041d030f00c0c00c50b40d940c1c006000042d015000701041141c0944038201a00c0c40b0700c845454144226042e0f010605c0e080c003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364790701 1250 364789451 364789471
    0x40902070c0f1508010f0612022214100504080d0c0215030a0207170a0e040b06040902030a140f1909020f030d1e0912060b0d02030703050303161106 65
    0x288000c1084500710508004101d020040d0480607260303521494100501814540000c040a00008100e0f805014039807c50300c0c107440b401050b025800302400030b58030000b5074090210080700340720104600c182000009001201c110740500c08243c0801500382c4085520404124040c40f0510851320080349440034201c1fa41072140d29146244049051209074200c0c0320a5a8404010024001c22540041035014882d12907071004140c2c5602841003401100d441800054920301e8440403070a00341d005105181c1c0040c62141800d5a44000d40140c0c0d008035022030000b5151a4182002d8241602c8980c101716540310030b007404c1c509060440d070700d111084446664162510018400d649076507540640c0106c001d42030314000c0440400140c000030301100142c241400d1904444029441800008159010001040000c001689a00c806030950003003440d80005007d07484030060303804021000066104801458403880c000081c40e900d4280404040b00b88180801010515000400e505500401d201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364791951 1250 364790701 364790707
    0x3020705040e010920040612050d140c0d0e03010608010209010503191d0d0e151c022208060a05010b04030201031e020a0c0c0f060e06160c030303020315040908040902 73
    0x10b0b40b00b5024090551000d4591802c00325904041c1008141038903007400d041d9410f07c03525664059600d613050606d03001070000d4002409401c9864861514914a010061840c500b010090000d042c00c0600c0c6c2e0010001240c109104454103080078080d00004101d280000c500340b450140028185101c002c00701c02c044070405900c04409905540300d0058124000d28203200141c02c1180306a4485aa1541d00003241400c92016600d2500d80045951800d40701c07211803c252604d43c4440103402880f4884020769002e102c14041038401901e0420090302400c00317421040d10701020142061006003402ca180d60400c401800810064421203040340d80c2841c0004000412200d0580602001020340e240300340002103040209600020224046000b00095064141c6c0e5004840c1204441e1140501040a45080c23002d1490940c01030003030b004d0040300c45000c0752000c0d50303020030425050300b049010a40c04000e01040c03240040e5020344421003070700c003003044220a03210f90585001c2c40c415448896000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364793201 1250 364791951 364791971
    0xc03030c0c0304080102030721050405120702010c0213053c0403030902040f0c0e010201090515220308011802070b1b120907090e0a0f12032a020106060201090302070504 74
    0x100103d40040c045080210b44034101020001d240c2c1d00310b0341c400502c401000c800300303135081d82d144903035801a07034868018040240c1007005c1403100d4210303040507030611001058020143c0c41b03030305140f051080d03885000112480c1c0801c3c004c0401d42c00c4181001c544031100f80185100c00d90541c0c80c20b0007800000141201c1c0d0750361400b200945140724000350068200b50840c5034081203034218460320700306034030703000941040400121b080314a0884051301c107074001458141a58440000160011082c5070206001d00c16101202d4140202070011000603d00b540108403058000702d218008107c0280c040d803030a4100d072170310b03001c100000c0e1420310740704105481441c041004070211441019170b01c1224101e07160850303540e500c0b01c0c07880c07041698076410f1021980c903108000c55245032a940c00030242002d1a4140c54007a08001080400d009055403940520514126840100d0490380d0002c0c0c42d11540507140c100a0035103000754448015a8105000e5100183c0c01180c0700c4d040c0d4102390340010304c035844 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364794451 1250 364793201 364793203
    0x30c06010e090a0303091106210604022811030c0312010509160e03191515150c060b040603210207180f0609060602030703110601050a030807030c17040e0c0c03030c0c 73
    0x7100d501f031907103d4400142c4030701ea41c01c1396400c0205420450681000e5641c0c05081c0402d0744600c140c1c80e801c0c0741102203402e0403440108100383d400c452610308450b8102603105100d1541d403000c0e001240c0c0340e00104202d001051102400c0d809003400750342540340c509003d83d402d51401481480201800b25040205129482c1000a40e596036400590000c07143c041c2d044c00c0e551101d100550021f40c508014501c88203803140c1e1ba044c1c0c101d90030081120f4868045074800c88010030411421501c99403a02240d0045540e9170085002450060345110303e488a1850301400c880181c1d42d201003590041c031000c110001020440340e05000c10160f01054404010782d41d400242a1a042116420b150440124034141c4c0000900800740c800e440b01d1465141c5400324a0381e43c90248903032a4400ca8240301070000030b48940c060314419220382803480181c081e0b0750303408100d0320381942088000e103804182002005420182075030881c001c018160700e400100c1ca602c030303200d2100030300200038008000386419210348 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364795701 1250 364794451 364794473
    0x1602040b090117060604020310050d15151412060a1a0402030a150b190c03030e1f0c0305130803090a0506332d060408030c06010e090a030309 62
    0x5005158070402d60712103d02e01c08043e68540310072824864a4005055414a807007120300422540350801e6800d40f4103c20004020b2700c926080f04d500010b9040403000520034011084003100700030300624440d00300200c40584c0844005000e02c51400510b59181050003c00c8a0b40c10410900b400b00d03282010030480c44203c58034003c242c2e0498030000030010300c90451b82c4500e04c90309001c103030b0900503540d0b880c0c0740a0600800001e41030f02d035888002480381c00d001d0703040c4002042c402d042c04100015114a501d00304210b0310000d10090f4010b000315086d11410307100307070300650035142010031603824a000d90307160100c011000104414030001c00300e0b0f444601046410b2130680d1002c100c40c10b0746419410140307440306149003040703448094243c1c60b4540442c0c2658140760000580240e81c4407407800ca030180b01ca102903804014400c210074440b080d907243c1600030070181603248000e565651000190510b0701105a010b5000c2c0e0840c102804a0490040740c5e02c41d42a41500d00031520040905003408404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364796951 1250 364795701 364795721
    0x150f0d081e16140a170c0109080c07090507050c070e22030e0a120c140d0804081b0a061b02060c01020d1e0504030f03230f0604050a0e0a03050c03040b030f040c1505160204 75
    0xb44000ca203902c2b1030300c80040c5481c2607440301d05081c0181e45582e401a120b034082c00364068220703041183d052015030501d4041c0ba0307009130303605210750045188030141880d0000145007600042c26240e203040d1581408018100180034003d0031040544154035a1074005007140039a030211000c004800106540d0814190281c6410500d55a070369907a6021007580c03040e036143c24601b03060280b00110a5468040b103800c0485845e41c442e040d05541c0298160454803031160200e80c4a40240504814101c0903c007810791109813100000340300c00c00305030800502007480b560391160b03420704080000095000700032603c8188035007804504200212079210707244d2030701100c0d80d2803007a042d000c1007079141401e06580d000c0d0f04180c40c10885611842c0669050359400c180c8002694000c44042002078030560040030190314080640341041c0c0c4554104803680e100380c0e40043d269441405010030700950b111074000804000d030040c40d070301c241400040c1007401703191921f1282445210f116400e54549030000c101c95 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364798201 1250 364796951 364796963
    0x5030c12010b030108010524091b030a0c020f0703080901050304030504030609060f1d12090d20030f03030127180605150f0d081e16140a170c0109 64
    0x280da1650081042c0b038000340316000d555800c1c080441d9105846004c80301446101c03103244011400404e084c01010400980250f14140c2c001d41d210800c800f80301d018501404138440042842465080000d00d1310250b00d404c1840c1d40c010303020803c0060b200d6022030f5803003002070138155101e6a0742c0c20107485d00d005951029011600b46080f180401203503501c81d00c10003010b440c0410240d422071408c846094180e00078045158080d4403c5035003061000702400c000030b40200a00c200003466600c1c80c0c6000c6c12100391502c002a021600400c514040c460f5402c85da03002e4000f10b0443d07150241201c1060004803130403502c030040c50344080131210700790004160740f00741403511070090b55549018001805c1c2154112a003114018699840d0704d4540d180c1d14130003000a02850030900c203600c48aa469210306011b03205000445200002d41e8a400094150009204000996032110707040400c1d0394856080c801a203034000002c60f8000071400300801100324108511142c031280030000303007070041c881041d0113808 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364799451 1250 364798201 364798237
    0x7080a0606031e15110913090507120b0a0f09060216030e0a0f0504050703020c0d020c03120c030a120e1608010b030c0105030a05040201180306020327070605030c 71
    0x14481a9041481224403c0c1d00c0641201c2e030510b02030350040054840141001c6440b0115aa4800c40383c01a40703071086465000c1d85816a1500000d2006800441400c119601d90f4124002d010080c0000002041d080d51400a0740b28a5690085807035402400d10402c15078440c8842903402d000d50101340150341c0810304540e10381c030304a070424000c01c0c1041e0440000340d11010790503007810040d50000407100715203c0d900029060104000103801c00410f11010141e0074000c0244d030b00010000d0742d0307201c99150080e0036056180000d0605014042004003181081000502040480003003100c92051603072600380600700d442d0025001500c01000b203c0c0071449140c2d603031000c018a030028502211212070080142d100420141a1603031100e12038180404c00910000300b05130320723031b40003154010b20515000001c50f07440b4030000d40c9a0b0842c0c00c10389200350702000b0421500c1e030f0310071000d180c24030819000c1142c1850000c92552580c6a01416040100210104408002290079561109151160108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364800701 1250 364799451 364799453
    0xa0b0109022205010c0f1403040b071a010e1515040609060215040804050120030d0203060319021c110303030108010e073510090506060a060509180907080a 68
    0x3029420862600c40156546184560a40701c800d0045080325410303100e4200801664454001036000520107031042121030384281321001003800100081c19074117503130380d0311000f031070820690052203401040301c48450000188008a2800c00c20360b40105c000140303808000b02e2401251805c07100f50500480703010045008900c542c0c0000100080d42c9203a0b088490707507140418040c02d43e502c15640a800c001040100384410352142c0404035031401d6a00b020100c1d490682031443c0340d075008000c3c10450350303400b00038440a440c1c1841252a4100c0088035101041c4480e00040c1d88500503c0307a1040c1c40b11070300f400601704026180b11484c2e00e00b004054944070b41c0d4903d081ca0180c0300802000383c06000b503d03000f06181048901e00304d52003039a0640d00360709603900b110100301c1003030000c0922480c0c8540c0304251540c1849000c1c0300c0006215001520700c4d810110140440001d840c0c00074414060300b8001e080c9141c450101d4020750340709001c5400802d450f845112070a201d49038003d02014004c6100c410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364801951 1250 364800701 364800719
    0x4050d0b16030513020f030f0715120504320d02070608090610090b0102010e0109110406080d080105041a270c0c2d0703050601060e060708070609052509060b07020108040b090a0b01 79
    0x12b0329040c880d444500b07103e4022403040e8200c51089030004e080b04181c94410341c004400300302543c00e281c6d198151448002c8440108c0b403904440b60100c10043c0e000d0074081c840ea940c85080035400c40f24010007000c0a08010f0902103040383c6038002d0300c0f43c80e5528615803000d80e02c01d400003030031140d5000003009811083d042000b100860003a049008078201440003d81c20800641070004141c2d6584040c59a400c1904102c06421361003100190030700e484065600940d03806942c0c110400311700000032021400003400309180500100305052240d02440750046040b40807a03018185980c9510b11071030700c400e0540d000d100c05c680100540b4244164038003c8108400021b1840c1620341d1500c0c2d9950301e024090801030a0700c41c0c410002c005490500207400003400c03a0300900c0301544580d003a62032025041040802207140b040c01c40082c05032601041042075414450380c0040d00003608001d1514005c0e4002800d610400f8200806210840c00010180041840030121075580040c0901c0c0700d580da11944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364803201 1250 364801951 364801979
    0x1002030c011a0d0f17041202040c030b10050f07050706050a020c030601050d14010e0d020102220e13050106051509090906011a0f04050d0b16030513020f030f07 70
    0x16855880c01407030503140040400c00c0d84142d03000803c0a56071400741e9451845003801c01d5421120600e001203041d00a03803034240031304050107030301800b1a0384070380171f004101c03d881d0049114018140341841081064445800390349412481d811300540e01c03103400351640d8291059481c050a81c0c000c1810100d0210b92000042c5480440c1da4211220300200004140c8c17900002e00c40e40c1d80c0714441c014a01b001400c045130031003003030501400004008040b15445810100300581c1240180d60016403049084640c031000d500c180403507102c1c0240c0b50700f02410b03420b404001401c42c14a1004074a4488100030b400d411101c0038007806810403d5141d4030384244907094100f080000d1007003c2c0c5100280502000051306030480d0507c450542c1e10505030000310003654021001e50f004141c041001103034030b444031111984042e01c999041444c901e001d04c100c001d840c64801c0d0140c2010300f0314003840381650061900c5e9220940499034030540880c8440000d19106202d0344084640c014640d0000c1c125010001e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364804451 1250 364803201 364803217
    0x206030f011a09010207060f030f06030308010f140a060309080c010212010302180712050901060816090608070f050f1804050604170f0d0c09050910080d09030201052205100203 77
    0x1a040d502d90035018822841c0115407241d40140c1c1301210410190384207040c521003004140c200040c040e446601c0500c1034a40942042d0013040310310004000c801e0041c0403080051081955144415180341c001480b401414400c2000b0503440c1c503078070300038048410111030040010070300071540d0390041104000590740074801030b4460000e00300b14a240c0c001070900e01d4450030040c0d0310b500e8900003c01c200c0c001001c014080c14546d40da02c1d940030801c2d100c200102003043c01c451105104482c6448517010948100d44c100d40d802d03820030101005002c007442d07480e50a59004540200001050201050603080040d40b09100d40941c0780600c4240140030034018042c1d4040d50050b801014929031807143d9210f030482c0001d001c01c0421084038800704a0744500140c2441d0b1038102d026030350320030019030420020703101403441c100ca001c0c0800081c801080003012030285400e102d001030307107142c0002e8154007a50b40250b0158191441414103c6860000803001c0c02d80100f61040b4031720500c0000f5529005028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364805701 1250 364804451 364804469
    0x3110c10060506070b06130f02040b030621070303030e10020a050c06070513030f1703101e0e0f06010e0a090204050310090b0105010c08190e010f17220206030f01 71
    0x2400310709401c125045411a541011502c4171a0316094148940380302050101004a541c0f100043c0d0b200449000401c01440e4000710305172a0306200c01080b0303500003201500355120070b0030711320200c401e00702003131000c101c03501070600127060319286160358102161002009440b0344005040d198803a0040c01070130202244204540d01a40d074020141c40700e214260201c00d615004540800010b07030a0100701c524a407107250040c00c0c8407010110403100d034105950100b00c4a0141806012200c2d4200c3c161821900cdc00e401c0300e00681c40c00c2600c0d41040c02c058061000300b1108000104142d001e080d609041c040050b04402075107940f006000000d421038041c66100e8020f112030444006614054001c81640207203014441313074640310040d9034401680f0740864915005000c44c000501340b02494031040c20007511044007400d899800140342a0000072841c0510501c050300d00d407202c2d0710a20565114060a2408032066000a10003a101c04c014000075880031002040144110b8150201c90481c4c01e404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364806951 1250 364805701 364805711
    0x40822180501080718140c07120309080313061515120603120c0213140103110d030905010e0604080307080904110c0a1104020c010c0c0b10080a110103110c10 69
    0xc040c1055960070b20854400b980700402c103208509400400090491952500048090301c4045454001400720b41c1460080008a00700c800d200c02c800060b6400001ca20b01081416520303903400385107010140c056003803010860104c0040168613400601c170410900c0d01810700940c2c03264290658807180c1f00c4440051180540828407031011b0083c042030742c1c0c2c40400c0c2a00d10103080400c0b200c145e80004241d0748041000008110401c540c4680c040d2034980034699110396056040c2440c448400c85052030140080d41c2403030780442d074000e80c00c1c010795109180849030100d40700000b130010301a5410042450100144a4040100d140e00514580e42e00750740502580130500f2080307889008465a03000c0d941c12180e01c071030000d41a603103500710100000304018240300c4059185800c5420141054000c40e020710520418002c1c03186a0903440b420700100c500596080640b4191500c01c102c100400e00400381c103c1e00c480b6030080d084030340c4003000505501c1d1100400d1005c5d507607512840484000c058500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364808201 1250 364806951 364806989
    0x4080a0b07030b0f36070201060501140a08040204050c04091802030d0e06030c030604021303030e0f150f0d0b0306041b092003040501060f18060b04120b040822 70
    0x1902c4255a5603a0040138810a081c1c402e1810390181c0811130305c02c074544aa0100c2e450000c000d03103100c50090146900020350381e81401d0014007a560b8856403844810001d000740d01459520011896015605440c081026252288808075901554008981d4036082c000d8000f4000d0003418000c1086000314211030260801010684603032440d0714103143c01c2034080001480030390004008641103000544010310780483c802c0c11030b1008446030000c400146d20322003410058601280381c404840c00c11281c800e1404000c85450b2a18850340440c0e480101003c1494070254049a01403658083d02400351452482c181c82e02940319901014045907d11203008049203000c2588504540481e01947e4007a401c82300c04507103019500300034800c03182076403161000b0079618500c8100c000140170361150104441100480c42c8180e035250b80141440c0842484100030b0b41d0b404420a2090340d0f005103018840b6111818030034850320807101a00c0c10840100d0710751038102070403681d15045400c0e280d020680b803685 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364809451 1250 364808201 364808209
    0xd030e0715020a0b0907080a140c120c100201060e0f07080106030509030423040f1a241c0203070e010e04180803060a170c03010e0f0a0305090604080a0b07030b 70
    0x42009801a4403c200903c001140500d20f40c3d00940c150044410340c80da15500c040c41c1602c400c00455255084424005588404200c2c440c00800c044a50200900e09000450350312403140340b900744140481005446c00d80d000b9480b440203000072400c50b00d9140b45c10501448082030681e20480012070750000040e80d184284916070150b8000310296103414a010340d4211210010268080354502c096504c007615516441100c91001d100c00020a4010780241c500d030070134096082d250701400340050000b00701c101004180041000e03151165031509000100c51904480d00c600d440c110034400018418850341081c0031040c004402d80e24020041d60050920040e0b5420b05080c1419050021011000072212009140c1c040000b400350a1502d42d902c2e038451140e00c4201d050072540e008410749000e242802e0103a8a100c0c45440000c20007041c209103510356450000d80301404104010403460000d50324001158000c1c2000340072034070241a02d003440000a45d090303503004007284c0740507003480300703410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364810701 1250 364809451 364809479
    0x14010803070b0c12040b0a02090306100302040e07030503030f071b050610050411030f0903091c1b081209030111210a0501080a110307030609030203070b0f150103020c0f0d030e07 78
    0x43c06803601625144c40d5070303803006c0d268060544114036400384015081d9841c200112440342c04842200e5800300c0c07844c01840b04a0700d18107082050794110304024804210700200b00c0380c20010b2401144950ba0b180b40d0121884101790b00b20484000360558071509000c0700280190241a0404114030101e40e2001008215030044c205404500d10510004500c1c1018413640d5a004c50840166072906902d0b400240c0785400c214450200c8081020b5000c05114084403060b9004034a22400300401d807e2040301650b031300d041020040604400150110507480079003044018402c0000d10644035a120b100c207402107050503151414424904000444c840070a0088904a40c0341e80702600b0351074229102c40459006070305c4000d0b054818160000300181041c030820a0f658000d83c0619165500c62410411166001d4158041503c9440501ca50003000b0b0341c410150340d03404d00700140e481a00f04a03c40c01c10303408140d010b2280c0150302c2d8038414103805800001011814000392100c1d1030b141d10466030102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364811951 1250 364810701 364810717
    0x201110412060515040e01020c19030203161a01032a0e01060e06040806040803160f09050111010e06181e031602030a05010c031407110c01050a0314010803070b0c 71
    0x1d00000421000ca07446a100035084210050008034080c008008141500d00c1803e00c00002e039400140c20341d49204c00d0150403940d0716004001d804841c00c1d910001d690317008280901030b603034005849590030400c0c400711148101000340c03020291580d5a0a2100081c034002c40b9118140800c80c074039440030103240100c4415512020080045642401d200b212880d144000e01a004a4200300c041100324040081600c80c61080b203102c1d40c0c9240c070300d2804c00fa6201014080007800302981031b200c1025040b01001d400c0e550280303441449500c2800d00705025101100d003201302d50241606021102c032200070791482c04a05101291a00c4000640160003424030b0800f0350030b031750418031003a40010107043c43c1c006c801d40000c0454004041544403142100c1c0e0300000c80c0040f03a510010102001c41d10802c456115410741020081c107040841c3d86503c0b01503050990703040160000d51009220700070341c00440c0d10010340b40000c02540e141c100c02d030b41e0782d030229000b510700e80040300000745010301c0714044600ca4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364813201 1250 364811951 364811969
    0x50904110c0717070b040305100c090b480d0c03080a0e0c18071202070302190212010c080f09030405010c030c1e0b040b0f1506031506040e0702011104 66
    0xc64544044405019000c8800da2464044c2420000300840c8000181c03010398003030300191007444401c0208004a03140003048509108071030000700700703844038001556a0b0b124a42e4545000c80b615407ca5040181940070381101d2500328170a800302e40440c0302d00d042220613030701c04890303500f00203145c20384200b00c040d01c009001810003000540964440d8100034203c2401c401100c4d24161160001342c41040011071003151201c6078420000c40e69485880d0369480d0031138510840c82c140c42618004d4448841c41c1c0c0340401c0d100422801421501c540c450440d0340441c04000700322510446000402040069544107014090000401d0344100040201c1e01110016110395000c8005035030b0170360700600b03542e0301542d65041c0c4a1141d4000d0300c03001707020100e0601c10700844565107014070f0019030301c4401034040e5043c084060b0400c16510700c00f400082890720201ca84a8a9540d5003140184181d0740c10710343e0384c0241004c2070000b01d2080c044201401481c0301d80080c0038507c070016450206005034030451443c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364814451 1250 364813201 364813213
    0x10e1e13022e02100501060f0903020f0a03050f0307020f03010c0e01140c190302010e010908030601050702130f05041e020102120c01020d0e1c0203090a33050904110c 73
    0x14585140d00d4007030361807005a10111240b140c030001403050301402c0c0940c05038004484600c3c8404251140c5405481a07080102034148610310080841509010007400744071140380c0ea8111b90b030f0b6102e20100a42c0c1c400c0850354003024071901c051f160780008804901450410f10041c0c1d60b8074060054401c02d6900b6982d06221100980045900c0254105800800041048054498881409030040b40e044030f190b10075600b0032a1a0090845d810452a001c8603490607000340700050a040849030804424a481d64554a241c000906c0d001c0b41100c100404a1501d8407800160255812561180d4080e03a40d044214220f03018000415074000e10090058111301007050000b21001c02030100b040425000604003014410b484080b2400001d00c034080d5404003006400c1802240120480907129101a6050400741d0000c00d040314000c0c02060a01c5110341e00801040190000c5890240c00852020099885003071024009610000e0b00368011030800c194040451040342c2110481c008140007000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364815701 1250 364814451 364814453
    0x60e0c0109091103070807180602011b0206070906050c0c0301050108011d1609020d06090504050c030706020d0c1e0506010b1201090501030305070231020c160803072009010e1e13 78
    0x6101ba00c000c24080a00c888000030032103445c2c040da10f0030b010381415000040c0d108107558100740078052a17100d0504640c460804c000d6000d600032003000440340c0c1030034055210103503004503d04050f49221050f03003641c42c28000140030203054004202200d2408088031032005801e5000e9210450f8101010701103c20040070000b442d15a0b00512648039003180008a0a4441031160140e44050318241c80036071042c0142d5072645400d20110004010500090000841d400805440720380d000c4405000301040558500803407078a0501c66108580c402c050764051368442e46a101507411201c40c0220420200002040665251040c10305a07a019110641846401c0c1e0070070441016086003c0c0027103c000303d04144010800081c0700756140010005621600c202d4020351400160307084546000394070120410880401200300c4440a40000507203c40c10b1910346041107005518000c0e0307401c06402030000441421241203680100c1c030440340001c80038010f1811000600c81900c5c0c1250065044007114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364816951 1250 364815701 364815707
    0xc0909111303110604090e0d030b03190f210f0e0f0d08090d0206030a0c0215060105190306050d060e191709010e03010c03060807080607081602010207060e0c010909110307 75
    0x3c000d40e80000c003610f14094482d03003500281c0702c50194020041e404006560f5940340c242c094110b441c40154001d10882240100d40c40305000d4107103001d040702065441910600200d40100c901280d042031292100c6142d101c0c00800001e110110200024802c0b103014101c0e1034441447e60a032000108180300482640c0c550344a5907200e112060380c0702052018507801170f25502c0207180b04100035400055811042c0710080d06219406903070030700d46405081000945da801c4000d54102d1041c0107807024150304182800e600500030fa401c11941300d40550100d04c1000030703079004451140321101c240c54042480c0c246560082d0300b154001030003c5807195456008483c01d80150269501c14981042309c541950042421117043c175840300006500c0f0001030108660800101c4000c0c007101d001009a440c140c48020080c1c9000b07002894252200f0071041070040c1b01b501920b600981003801003041207016400180c0d45c540181c01c0d0740c04035051030070001e820320440c801c22403c0814030020602d540d445c0e50040b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364818201 1250 364816951 364816973
    0xf041101050307030e062805060315180a0506040210030509071401030908030f0405011104080c0108070309140601090e070b0f1e0c0a06050c0702060a030905100c0909111303 76
    0x500c20156680d4540d14241c0003000010700074401038030360900d9544a102c499020040c6a45c100d051f0030309100500603079850004954a4805042da094542602d0340d9546804140603d41d11ba100e40c40b5003000e0b0018000042900c5008501c05c403451000e100031140184c041d80c40803548480c10360428203082200303040b102d0304075148610501d80003901c500342c6c3d510b602c5260001d031240810000f0307074801c2104108007485010020020554617600f8a0b181a20883e69441020740490400000b2070124194a01039000315a000398010045040042c0d6040143d030f503410309120781c014aa05040c0010300d0303120007083e0340c400d407044034410300d14100150300d07600d5542e80a00b4030482801014140c100c01103c1c2a8050000242468090007980440f4242802a5040075000e010303010030412808005903210342c1110b480020a0038041046585410000d0410b10003508410407035050089007410a070780040c0200664207100800c10500420082c042614010400c0c1c00281c02c01341101032001c68210400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364819451 1250 364818201 364818211
    0x130f0f05030d15050f0d0b0415020f0a050a030501060306140433090f02040e13050705060c0f01051302060427060b12130210030e030702090f0f0f0411010503 69
    0x1260701d04a00b1108a000715001c1003580405407100388418011407800c40c1c050304001c2e078103c82110146116844070384910300d0190009048180102c9228100b00f041e8040c0c23495400503407490758946100010161180d0300074440000007910f01000401c60a0003485450240c3d0b00f17202c803c9550720b040c51b0031300005051084030401041d5070011a501e450b010b5000c0b05100551400d1000d44091a00044e0410340d03d01c1810121800d006102c14403241c0b0408030416030242500307801c441041c0e5241003050401e007554110300d4205070b000038101c2c800b240c0041c40b9840428040f0080040d0754805100d1b809042a00030300a6000c14108030801003003408403203087c500c8420f540319048030001c0d05d844104881e00c1d50300c000000134003c500c40740701c844480459584616151000c10143c4551307800900e0691071150060705161381c0e6550080800f00c100140c84007154068605e8115060890540019140c11604200c102d030240c80051109003d000fa030340d004507800f10714410401c3e1000300544244d040184 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 364820701 1250 364819451 364819453
    0x2040e0a1a061b06010b070506070306060c110f091f0524070309171501051212031f090905120a08070c0212030316110d23091e030105130f0f05 63
    0x11442c5001d01013071003070074000c120711109141c2d10b00003841c3c8641003540082c00d0382c0500d8030741381c400c11202e07810802521075240c1c4898450000c80c4020001000c0e507401c1c00c5001c1d048000c1600300300281440c0940c8241d0030f844480d001e00c00584d10010051411021406000c81400b43c1141010b48500354020b4041644a070419504842e1900010080c2c14844082c0c03401ca5441000c0e9010b0b812519a9014050030003a2a20440426110300c0103940b24044a14116a90400030005038a0422104681407660b02c403440f8011352543d07411940064810400140d80f58001c0c1d044600d00a000013049034480031007601c072002c0e144d40d140ca041d44c0440b600d820a1307070401c00100307408020503014030007180310f40c04500e0620050054520002e1050188101400241d07101364080859030b50800160040c02450b002d016803c660561800e0245010305803043d904010b2280c4000c20740500800915060075051340208019034444995058040d0500360203460f40a035240004082800d10f000b9130496070080c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 364821951 1250 364820701 364820737
    0x30e0f01060b07170f03040f0b0f0606030615130306021e040302090408070606170607021b01050715061a07051605090106080403171005030709051b030901090f0602040e0a1a06 77
    0xd000105c40d50003150101e03003c8803480070400410034111035142d08102100e410b69928a8480c01080d114400503082a10a002d44045500d919001004540341c114030804240c1d215940c80c54640042e4002d55200824840300034600d0b9010485003050350110380c3c0007007140714561116101c85081c1d520031001560910340714480441c0c00044600052080301c0c4030b800401c180d26004174001e0134440c242e041001000007a600c081d00302d80e13000c41500c0d05290030051301c005641c200040040100002d138030010380e41d606008804000c4031420050b244260013101a2460849901c0b031180845070a07002c2c175540701e084400103101d4a40300d0f40da01d50f486031207410b1140761203900900100000104880d1807074200070700c1c40140b01d10704040c4042001045176100134011801c3c840407640740040d10a1420001e0780003c00019401c100035041014890340004607000f51241d2410003c000c0c0d40a8043d00303130314903a00004145514040c2c411441c00d6444031510440c3d00f81d485007080f01030790040c021191546c100e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 364823201 1250 364821951 364821967
    0xa05060c01112703060601021f09021503011a040f09051f0905010f0b030c030a18150506040506010c02031534030b0a060206062e030e0f01060b0717 65
    0x80b8000d00d54062849458108040a050b8000042110348080740c0242c111009014169800103020340c0d8100c954001603120f020741c28540d400410340110007950004040034042030302d0400c0d100444c1a80c0300c030001015088401014240d1900c2644100318031841d055104212100b544d40c88242c0110042845541204e11114807030110307542c0e9085904015603803030042041d0540022010000c00b140b41c00c1c1c1d800c520b40b8103000219404010901c0407129103a4520703690000840300099206c0e0350111030366900700c0022440e41d004160841d201802503140030041909503000f00700b01c0081907030050082107034040e5070909010400b005081030420143c0c117a009035102d40e81030110f840c1c00f88040740510078429a10707801000d58020004090040b4010724040c85042d0340828030a130b00c8030042c5c80f4100710840c00c0c07001a1300d558a2614150555030710741a5094541c0d41500f0084201604000f151403003030201070308600f21041c40c03090520345070342044900c0010740c0c10003441c29425241c2040e6400d00041d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 364824451 1250 364823201 364823231
    0x70c080609010f182303041508092e0f02040504110705060c07020307120f06020403050a0c080f03120c040305150417070f140a120903021e0a05060c01 66
    0x1501c1c180000d03511880c40003410046071113094101480d48070407110360000e54940100360814001040442180f014407100c0c1d50f01e0030000c41c1e0007446422200340104204507002840264181c42154560140e01e204090124103502250f510410300d41c198120352101d020800c0050a40c20401c1c8400c54081c00300080f03980d070301c1c482c01e41009900044180d66034000d24009040c100014590030819800303011403809601c1c000380d294141d95001d81e0306a030501690030a03106004064a0080c0f09500028010081000100b4004049071082001000700340d2218441c0e51103071041415100c40354424000303807410b0313100422250b400102140c01145080d0700c079158103082c0550000d03880710040e02c5c8410301c001c12000c0c494034283c1500c1a0340850800181d6030700e001200b50060000f5007034040101003620a0740e17080c81007101c1d80d0307442301030b4807000001d2500140c5420703014030099120b240005580f6000b18078841340e40c00d546400600c2584180d042004200c12034003c4242c01d40250341c0d0311584c8109105d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 364825701 1250 364824451 364824463
    0xb040e0607020a0507150e12070306060f14010815010f0e03030a02010c1409010203073e100203030114061b010f0515030c0907030e0c0607140c150d02070c08 69
    0x1101e40c0502020f01460030641e1600c4026032121090310000b840103e28183c0c00280f019107464115480300344188420549447c082658001a00030342c9072a4000401d03d200c0c0366908100d4098044854050a41c04010b440481d012a10f81040c845501070500c03045d8807a9583e10142e40d182c0c10314680b4200c068010919607045008144d0150390355103042c200ca981c1104504140c3c00e045c00302d842c64014410b000039101e0003000c80c02485a445007003d5a4410001044100c0c1c80e603e203045c068052980200c8404902180c10b030490040008058001809102000f102d06a8500c0030034184134104610600c10650311640c404000e41e41300e112041c031b5407a0b0130701404e00341001c1130f0300100e0581420f00e0300300805514581687d2090344140038110303690300c0309403003298840400d007030000d240072400d51002e0810343d65111940c1d0020b4000350301010442030000210040a882040312560301c080400e0043c9a400c810740151408814000e4105103012900189241441030b05a5107204e942d48070040d14020b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 364826951 1250 364825701 364825711
    0xf0e010504060603140d02030403031d1906080601090503070e06060f0309010501051903031d0105090a120b010906032d06051302090703020f04090228110c04140a0b040e06 75
    0xfa01c1d40c00800034000640c02450b019031320b04010309411081480d01070b5492190307100007400e205040d24a1a031204029020710111140601500c51004418110740c0c07000f54540600008a152000404e0302544189150020b40c1c40290040c0311883c1032941c0030359101c40041069610030030402201d5803801c0c040002d54060b200d1640049160350400003004014007140300c0c0c6000201d80024100046a40190359035a1010300039100500094a0320040340c4510412031103036000142038000107a0428440104114540145e20780800359884052182c1520f286100240c01c0b07404482e031804d01c56109550301590303540c600c04070001551a0b81d49500584030111120000340c40250503040c19810101520782d0b00c200949411480c0064590000400740210b0003102c1c88035602242440190809402100c01c80344a0310940a4442d12000d0041c0840303120040a422401400300007c82418240580702d582c0480022483d6155a40d00c0302c8401441ca820405502035228444006002c0c42886085d00036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 364828201 1250 364826951 364826963
    0x30a0e01110a0315240206010801090b0f100905010b0405011407080418020702092509080712080408011103070f1707260c0901021e0d0809031c0b0405010b070c090f0e010504 76
    0xc2c0080c5c0d800b0307080601c16071000a83d0703410038440700c00061007203c021380d0000d1400e0540c0c90944503000d1120f0b0103540345d003240c14050b103050004a40b50000c130010f8412100240d803902d10132600346c003600c0120f0080c0c00b001002228103210910100c05a140315000d40c483d2000c00504000d26500007414401c41500c050600003081d0051140c503850382c089a1113070304440d0401d19115071414104031303a20703d2107220340902044100300000800c50040e040b10001e01c450b10080c0031301d03047d04000c05600c2e401610f140002c102e0014200019034000c49421920050701c407020702c903550f2044e40c1610018040303e456000d400d9030101c4401c0b504000070016000710b01c01504c003920b07800c00000191400588803120894800b00030b954074003411000a0b41080d10705245003070029502c803007015524501070700718191080304041483e2502c1503003030b80c48003c980da4129800c0c02a039a03115100b11031803041040c00b0703100721000041841080450f8014191445544500103a030880f40150282101c005690884038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 364829451 1250 364828201 364828259
    0x6081b0f13210b0702010e0610140d11091003120207090b0a03020f1302070c0312090e07021c02100606031b0201020306130b1c030302030a0e01110a0315 67
    0x8211600d040060805040c4002c6041c00040c94507070b803181c25010007420f1480c010006a40f65200390450361001c541801100c5141c1001d0300c281080e090540074003298115518403422003441e041181030300b45500985165160710810062085016008107282c0e001010440d000001541c0740c503420002452542c0607084807402c0c01c45800c10743d600720303008510403000d0300f005101507601d15414800d003100440c0c1c5811940304904210f00680601075001d81021500400001480981c0e011090401d105684c0ca074040d68481d006507800e03810555403040140d00405500e1102c500b60040e03484604000d004035000082c1507a22001074580d0b641100d4002a1141400780041c40010b0014481340c0c1c241c002542907252400114141c0c81c4a54482c0e1007081e220140142541c84800411b0310b00a00b2344003c401e40e10503410040d0107940251f0b24a0401c0b840c0c8890907403800c1040c821481d0380790a81e242da500c2c000310440e04034040c1148400020b2000d0403190009408000e040a4000300f80900e048542 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 364830701 1250 364829451 364829467
    0x12120603100209100c060902041503050d02061e09070b0d02070302070803120c0d020d02040303110c0f0f0613080f0a02090915040f0f060f02031b040f06081b0f 70
    0xc1407030161000c1445482c010702c44041156519115002010490700e404e503034010141c01c013036000e80f94691019403c14501518900f14400e40e00310a820359000340300302c8241d10301c8000201e0f84c541c2c088601030044a68102c2c80300d10351850000040d00241820104d071040790721909446000d50010034400304084d4009218410550140b00010080141002550601000c508400b070304100c0182071510068001448052a01c030303541c151401c4500c02401191a6a160303d0040e0450000c2034604101e0b04c02d21042150754034101907060108280504094040f1001e02c0a12140d07030041a101d0124188020011480c04010020845c3c20001c020007031641040600500240060140c000710300c6401180032041c1444504015503041588942c00e0b0740d0b003145600306001d02c0e02065000401700f500b800f41c500000d01081e00a940110341580340d00c018800c40c080f10140034401c510548a0641c00b00c00b080203240e000e902d40d283d02401b8040441d581c141c000f100860301360b10000818440300e6020880314 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 364831951 1250 364830701 364830703
    0x10e0d0909050f011a130323010b01020c150702180a0c140301060e01090302040212090f0a3c0507140607021327050106030b160f080912120603 63
    0x300200300c1d40c241005a8100801c3c0030008550501039040319082681341c074402c80380001c2c01c4030000f925221200e545a03440c0d01e8101000c100582091294030840b12070940c128030188910a40040140c0051442080d01c038140040304401120700d81800a0520454000d03072034200480c201c0f0344007041759515600d0408200c02c100e03107581d107203902080b41c0480c2500c000007984040b41d040d40d2050415006c83c03c0a81d00407a001c68854100a4001d030001c03590000d82c004c1040c845008070740700000e90715110130180c4d210759503103021f5001518800e62041224880c40d0000f8240c07131460b003d10b0030400fa02c00141d08007405809059011200c81c0e200000c00c0044508051010000d484211001841c010726a000620441103001b10740c00341582d0b4103500c000071300c880c1a0019052002c1d070300b406a40340060901074000c082c10321041d610b805074100002ca00325030500307802412840b00e4407502c84440b43d07460304480401004105800e80d00ca504c12042149080401400e030135a81003190746000d00d00713003081c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 364833201 1250 364831951 364831967
    0x1c030305010317070c0e1b0f0924070803060a03050706020607020c0f0112150918050c040506060f1608120a18050d0e030c0d0503070309060509030606130b03010e0d 72
    0x2c0d2003e280c14420b840004804602c442c0c2151401c00083e54030352a01e080020200ca44c0c0c40e95014807000000c0c0c1541610032810180070010011107400c624a1080244200010011024082498030400c410000904c03d031000c0d5401c01e0300a40344404998403544c500d07281c601640c10001c0541d000d08100500140d040020462054082e26601c1d0b061442000180c2003001d00c060024000e41c41d070404100d552202c00300500184960001401040140041c1259400d01c038441656280190100d0f440136092030f002d00d9000f02d0006d04428138081484824034281d4200482d11500c2d03030b45c423180e503001261240d8003400c140402c04543c0d43d200d0410740361040450b14280c2200a40702c4640c0c80b910081f4202080390144101982400c0d081c2d40441d9000074104a03144602a60020810191100b840000006061800e2003a1940c01000d43c65000030345860140c01202035042c0d0128000510904141c001c0c420600f00c008400708502103484002400d4600c14400e54103181c0c4135440e0030302da0950184003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 364834451 1250 364833201 364833233
    0x204030c0f0b0d0f0209280801021801050a120f060918051002180306040b0702010b09040f030f1202031602061b0d050702070510020106080706170f04021c0303050103 73
    0xe501d468900e85004600240100c4a44400c0d196480079090301d101c400d80c044418841000b0401c0002a030341d98642c0319a00f500980050303452003007400101e0b00070014400c5419510f42a01100f00403a560310044407103a10203a1420104440c141d00b036942160980140e6101448003400070031810309051020701200d458180040e01d890f420092580807036408a4603410084580e1005a501c1c0317480846260b004140e580c6c6c80e130b01440740ca8200418080d07541c1d1080c0c0138a04550003405071506400400010000507070b0007038140207059615500180c041d56007085148000c2c20100303072141406801408903002220130035000c0f030200d520119444d5050103613540c803512041e13041e042180070b00b0000c0c40e5030007054a401150350b6104042400c0600803c84403006040c0200394030310741d1112200c001d002e010b039441070782d2092040d0760300801c0641c0101d25521030590076100c204401e580300c403490703c8401c1e00a030040e03030040301d07114075a01ca4042202821091900948020030b49500d18a03014024401c1010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 364835701 1250 364834451 364834469
    0x30912030108030c010c0323062b0c0f060807050c0c06030c090f03030406141606050903071a160e010e0303041d060603090604030c0302011e061509030b1611030309010204030c 77
    0x701ca0100b0702d181000c2300040046001c08959101000b0501b9010051000002020180300340700c0300c800800c4180c0300da540f088005600903544c0c1d2400d42c1c1d022119004580c00300d116000056107083c4200c0240120301380c903004440c0221011401304940340d005490080084800103041d1404e4100740d900714aa2004c258000e5203040d1524600070820020780340b445104800c0001c3d1188141d18080312a03070030035007104040044d420301510442c0c0ea544003520446145102000c0f0700541074005501d40e200b61445c51401d811090681030171140d4119007030420307040c03081d8440580b546490810240024000803141c010070703a4500541020114401003249104400400401c03e903c00d000c12180c3c0c21a80c035060031281e11000d1710b400d80c09401d440311007048902c1800a81c0087c210150001c6049456407000d00360003461899080707035441d03202c1c00040d1402c000303100458480c02c0e185050300c0d4550f9003890300c400c074070303510403916801c5510544844605a4000c1000e1060029401100c07009080c2c141c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 364836951 1250 364835701 364835711
    0x8130b070515100909050a02040f0219020601050d110d0c030605310b06130f022104020306070f0e040905101b0e1e0301020a0f020d0c020312030912030108030c010c03 73
    0x5200c0209a140c60300035207081c45e8a03a4404070070400c00708040400981d0040090000307d440c407003024000e421030613842c105c1b80080301c00480c00500105400d8140e44018006401c18103958890001001800949503000381740c00b6083d030b0103e54469002ca015510800e07012035181852050b032800d034425400203081300c1d0074500b50b840c6010214580c2c6080359038000c5005400d0390f5020001891074140903042e2100d00d00700740c0c140544010f5940107110700d4541103181308410b2034121140f072110707804641c001c4d01507201001041d0344501402040000300700c0340c40c2051401007640041825900a0101142e21b688413400c03c0340c0380c150718001d40316044049101135402c0340c1c0c0c0d1b0400070505446800c1c4a40640180451043c5851142c06037149100f00a00295500c19414100a0a0818214600c00180990404400b41902c02c9021120707441d00200180203030b685507801c000003684094001200c511900e84c070364061818150186009082c540e01031a00c905200723071564256803c18403103404052400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 364838201 1250 364836951 364836961
    0x1050601020f01060f180209030708010615030b13110903030a02060a0b0105030f04080a090b16050d05030c040504230f1005010504061706010215090309010912020f060708130b070515 80
    0x11207030401c41c6d41d4401d030070111070188404200244204d00c02c43d03406009502010801000542055044404903803140426266030300e0700b2001c45000b4042c8544c80120a645208240f60682100c0208114251402c0c40c00c100100002c2c5140e01c54124100560030103400c01c180c015940c8102d011030320080c24150b00c2c5150030561074611140081004101040101c1d8070601c0c10722030001c070405000c0324440c0580e1081503d50002c201c1c500c04a04039914810901607004642c4160f00b03a0340107182200703409040900300020840601076100d00024801010060609061a80b000250007610b072802d0303403540390802c40780f0b2483c1c140e0960010f506019042108028942e40000c1c845610b80e40180b44000ba6210300c0c004034242100c5604900c2105c46110038403a10b22004001000301c0c176003d88410888541d102c2000359038604201001c0c2d1b205828095031440303410080024210103124a039068038289040c0c10f01c401c1d10b49280c03c450744890b00841c00da820414100700314200311407181e00b101241e10782 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 364839451 1250 364838201 364838219
    0x3060109060b2502060f03090f0a020102100f0f0609060314011116050a050a0b071206150f05130308090108150d12050c030c03030a0c08011d0408090d0501050601020f0106 75
    0x42da00d401c5140c41d0b502c4000003118419005000f07100da80244403540d20310350840f10700441c2d0401d0300c1803101e5000d04240d01509000014138048840d9041e0041c0044582d00511040240002010b071040d4646401c4024240390351403140c000600406440040c00d642542840080310390000d003280c600d41e140a40068141d00d03440d05503208001c4211400c60b05034541e00d0100d04001407140003c1040c4100d0301c0090411240c60029813082e5850780d601d914070321294030040b054074140d110b0010403014515640c0d80480c4500b40c112205610790500e0303841d21048400d004000d081d40c0d8000e03901c0e03c501046078541503034440340300d035002b00e140c480c450044540000090b414107071481000380044102d080780401c503402807055070141000603040d0398403801c44030007040d00c90f4400c5910703140f0075184c4242d1031072450087c11000c1c10380c1c041001f1802c1200500d0300081000d0405001650094420300c58180e49a80c2c3c40081c030181d038450000415035040410003e860100f0306142c034444c80e41021010301031601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 364840701 1250 364839451 364839457
    0x70b0310050402090609101e050a1413051c110901080c010c1b12050f031908280209120d0203220509040506092418100c030b03060109060b 61
    0x101c11100142e440c0c003c040000e4440c868442510b03044507002080924958005040c008100f90000300301c184108a4401100c141c443d0340a984041503210103200c02c10001480500b03140103415000500c02500e07440013038003000c40c005c5c14106a040c245006070030050400300409040509407032038001d075414180d03040d460b0380740209568104030b1751422081c1809a140c030b40044907114a841100125101e842c1c00c10100030070103040d98280308001c900c0800345000000c80720310406141d03c0c0c3c0384160b000700c0c0442d9446005031411141e040001c141410301c841e0b5915084148040c964010b954500020a01540084030240009545c2215001d030919a80100272144146040d04042981030545c2d054401e80400a81256821824480801042100005155000345c24002c00c170380340032005929103062140350410700c108850110021031407a04038005101c080e00048410769030f803500c14000c82c0044a144540140c0000d03110901c020180c1014003645014010501e4248010750415941622502c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 364841951 1250 364840701 364840709
    0x2007081f06122102011d01060918050c010c030c0804090e0607090b030a0c0c0b07020d020f1903080603010912030c180506040608062d01030b0904031e0509041d070b0310 74
    0x404a0f10490072064070130f601041d41e80b0f02c56243c5035165810307940c02600820301c900030340080515003c14550068040c124460006500c02e00170311501d007140004607034031245900110144641c40b030b507a80009001c0746c050030103060010f47c0024101055030740c0a140400c081c20304404c0c8512810140601c0710042e04996020b807103000c0106452074a80c1c800ca61a184806000e440200030070248440c20b540400c1250700c84000f5407c80308107005c2d044582b5107680165104040c00800c518210740064014007185034407801c01000044c00c00482e07100e2074400808080050000b99441d070603080c4e1a900014070210041415154035a03850429000c200203200b1400360704140b00204000039102c0d43c4426148142400d550044000484080301607451404d111900d207001c60700b0101a001c850802c034410341e21982d056559980d85036844668503072401307880b118510801100300300c0d551030758580c1d00032500f0000c100341c03030580d603458291010380c01c00d4260381201b00c601104106108003010544111400d43e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 364843201 1250 364841951 364841993
    0x151605190c21110f03070b090103050705040e01050f0f1206041e32070308031e1603090302010e010e0601030209010603060e04120504030c0e0414010c2007081f0612 72
    0x48020680043c10ba004207140c0654180f20300000030821003039131f00150110b501e003a02c0074030041d1a00c02c0c003901e46000700d01686d841c80c0481801004076150681c4142054840500f0910540078020003141c2c0580030120003000c1a8018814881000001c1d60300d00b040003000b00700d08000e00d469030358401c2c114060001c200128403020b607071100601e44030341d40c04100c21181390480c0c6404bd624509641070b6041218401e17440a000300348184040710354000b5510540d0280301c03400245400500640081c00c12070000e808666940052894000c000d11940c008440030800401181d891481000708044050300704604240c1000d80400a0800c5142030581143e0301056001003036443c810101d909000750750000d0040b1503d4280041c42965180303003240900c0c00707200c0306d800c0e4012180c0701a09862401c031b61180000d0942210400f040443c003080e190072a070040503030701d030f40f80c0d1030124620341000d4000e90440c100760301881000e16120340c441e0800138010303052030003514034031901e40900d144840c8910404c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 364844451 1250 364843201 364843223
    0x804020a1208190e0a09051b031e0108010b010509041e0e0312060607050607051b1024080c060c150108030c0601060c030905010302030903280207080c151605190c21 72
    0x6038840c1400210161008c0640b07075803a494005e01c600480301c079150156100c01c420703c0000c1415041070080e03003e58076040e1901d624050805003800b000740110007013122080314080c5c2015041c0000c0c021603269000c90401152200045000c40b00783c16800761200303115039000c09c14180095408190903502c10803e007803880e1140740000d07000441c0a030004d061040d82c061640c4a0b0540340203513020445504481d0602d41c0030120300a10512016403d010351403003544000c940d890725161050041c0410760002c02561600b50300403412180c2440c0a0300020026000410700c1140240c040000a00406082c641419004803544015109a0340348c003c06040580000019051500400445400d141007108200d80d4290346203a580c10008550990b03801801a0f4030002044070000035440c2240400a102a000c502034124442d40356201b0400081c4020144001c3d0000c01d00500035445210455015100c07440a00c2c03030b2000c84803055407c2621020300c50b084445058130066044660703e90310040d9540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 364845701 1250 364844451 364844461
    0x1030902030a0b09160e091023130311060c040b0d1814060c120c13030506070801030b0f0405030706090318090f0c0e030d0804020a1208190e0a0905 65
    0x204001c0d102c0000740c800303d404014000c80e0040000c10341180c40301081130b111040d07254450281d040c601600d001c04284d000403400d03042001640c0c05440038001c00501003030b403102003080c502e40d4008111400c01b04c50340b843d03012074141508444a2076001d00e007000a80700390f190210740c03218140130300d0264501c803140110f807500884401d0f42c0034075400d202c03410b0b0104503d249460200c00258180d90074141e04d00840000c50307026010181a20411030a40d91400700301e540d41360800240e074200c004840250542800000042a400d0000a000daa0999580780c01ca41c11070070109070818000d80084200d0744840c0c1000040761011043e1082d65602c0003011816039000d0404540702d8511941c001d42124140c13400140c0303400158001603068a49400900414020f01015503d18030603d8006805420601e00881d80a1150103d9648140300400700000a0344031419051044a20300c4121120000080c441108a0403503254a00705e06862809031003d0101c800894443c03441e42c440d8880705078840c00420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 364846951 1250 364845701 364845703
    0x418020706020c011a040b0f09100b0f0309010c140412050c0307140406090b0303070f0c09020712021005101205100908031f0302060a080619152007050103090203 71
    0x340c800c0c0d00040255290902200d45034000c00c032a5504002d038490f68a441c14090415000b0f59003001e00041c01508001c01c0002072110103d0018140c941c0d2030191500803907204d40301400780c4101110494415203900e000781e00c0318219100c046d00001440b84024200020700c0106c0103c4059520304d003864604a2031503e800c1e45840b900030b0146505000b030f40c1700402c3c001c1c2003800700401c04908030b0301409455540d0340d11108461032508000e4050304100300900210750300c0c4000303002075840750001803100c0e40e4402c0300340103d810034081207401402c6c48000da840198100911a04001d011800304480d003007804000d9100c0d400f074414005d0340c90206080105119040c0100001e2001d00c042c140800c1e00d052500382503d078811500800100558a20580040441036803481a40d501801091804d942c0800560f0301300c500420b4154030015002143d001c40701403003d0240248003501210324049181a0301a2a0701041d0384000c042205003404070804150000f600740449400b0300b800200009940042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 364848201 1250 364846951 364846957
    0x123180103231005061305060702060c0a030507020a150f0e03070308210702030a1704020f120a170702010504090213030b0c0a1b030804032106080318030111041802 72
    0x11200611a050802002c0c209201c16100e860650200040c5a40340d03420444540150510342c20f07000b030304c3c40c0c0901060030039078024214540014965402c12190a02d02031a2000f0818120001040071070b8580c118103000c03400750f01400c680601b0300002c1a004100031702d225449090302c401c01000c804a003000761000d102080141d0741264140e5501c0361245400c00c95503d000881c8540042003c0c000b43d503c0c0c0c40842552088040e40d900c0b00034108218110007603060002c3c3c0103030380c4426140540c00300c5507546408440100040c03405418000d090342000c2da081c01c200811070103c501c0c1001182c005070791050844055030b01548005880f054041c403814610b54403078100a160400310750a000c1c00d9000030026140b28cc940e41d03541420311020403001c405070300682000502148810340880c4c0004d0280290240304a40c03603140075001a944100c0c4015281c0603804001c0b00c0c0c100044420400340c242c1c46241c0900d00035802800a2110411091281e120b94860b460500000c8150340340d50028940413 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 364849451 1250 364848201 364848221
    0x403020d02090a02041703090f0306070503040312060e0901230105010e090405030c03031806011409010b0a02102f1603050c070506040e0603060f0606040b0703120f0603020123180103 80
    0x1b80c0300c41080c07403c0c285c80e9030780d11800b0024411001c3c010300140350f05e80041c07118460700095031040e003903444a540607130314181410601c02801d5104c0c8400306071039281500301031060b0b01c4100003150428400c41000e40700b056900c41c0c012100041001030000b660810440d4111800076504006140d0311750411609500a01541e01c2580c0000010301203850744c118401c6241090510036103c0f1079a0f44c440020320804c0b210302d601d4101c000389004106880c030000103000620030b0b50044c1d5461018000c501001c079200001a40c03031041d008106a041850302c0c0c00302905910307a1460041c900104400c0240e1141031441c80103080100014031412011300902c03104008180180995854980b600101e50b000902203078128024411f14000500d51603240d6107250140340041c100e00e1520341408080780c00d940c000d42050f814007159000441044400d4412409410210305002584608602c00102540c09109444c1030082c0c2c50031040240d050408100d801e04040048226607110781c2c1c000507800340120000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 364850701 1250 364849451 364849469
    0x301060513030506040c0f0f15050d1e020409060e0603100506150c03120a09030c151d01020705070b03040507091512030207080c010309170711031c02060c0403020d02090a0204 77
    0x81440104591b40c0b0b40d0405075504052481c25040c1c480c9104034146070035105a08801e03406a01c90502e07503011b040107100440f1040b03c04100f002040c041d280803160300000c9240c440da030000b0104071060040c0f140101034605140c40040908180d00041c2d6220484161542607d582d40003050316640d940d403c0c002c010840005080d02ea90041d40301c01d0312508280011195151090300082c0d81861612400148980c0b684801340b03092038548503010a140c005120040c16961001495103005c500e203412280414208009a6240454074089040020540c043c002c0100e013842800300003400810410151003d141002417800500702e02c0c1040100c040d44012046915209140309140e40810514142c41c101c404072060a08117900450844a0680c0f0150840c1c0200b500300c3d0702140f00304010320b0079a0184030031040079901d003000a0704240e0507152400c07484d590301ca8030064080d0144040c0d944841743c6001c40e030401d071654022641107802841c00030b101e08501400100d00c5078072030381900c0140507010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 364851951 1250 364850701 364850713
    0x305040e0c1303080706050a0b0607060e0106080f330f040206090d030314010e0601120203060d0c0e16090f030b13051006080c0405070f0c11060d06180e0303010605130305 75
    0x401c1ca03e001742d00180342595420309000010b201c54a450181d600c50900c094012442c002840e01d80c08010808066006480d540300c10340040e59040802000749e100d540340010b080c158141d44200c07482402469000803100350030480c0c2c020020b00e10a10160303c5000072441d500140d603540f002464510440340d94070b600040486610f024168958499400e0700e1801038200c02603621000044c040c448100c540030300289840180d19200c0151b9009035810081c040c0852520200c1952258480c8955800c11440e12150800f00120009411901c0c0c02100c11400e04064070313410482700e880303403454030f020141c6110003c50205941c050744142031454940c000c001d035411500f660113501c001c0c00007403081c04142d100d040040000d85c501480b90300e000d408243c5400e40caa080102040c0d17440c40002206481c2080d295241840c5c54848500038412400d0740c103000140c07c2e0400090a14400007040300042c3c9a152903030007890840b00104581c1914403074140740392140d80c0c412070321038120510342004096000302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 364853201 1250 364851951 364851953
    0x30903020409030e0f0405010e0a0e0f0604051c05070203030906090d151a06091003090203150a200c120f040b0f040512150106181d01031401090305040e0c1303 70
    0x10130b00c400c0e00007400722900d40d407454030782d001c000a0396000c4c040c0c0c1042103110004218100c0705075104402c00c01d4444203469201090054960401500311010f0303032207030800d0700302e0702690f014600e10100c0c0380083e09200781016229004030340d403405088500c40c020300001864400651b9021481c40f511584480012002d214110003034001d0444540ea248900508810104443c0f4058081d1600f4010140c1001d030394055108080300074100140090b6018004c0c5104e0304411404099003912038010a00046000242c140ea90815030343c00312070407100098103011100b40004081440c001c040c04901009c0d0329801030002e0000a44103ea000d1f001103100051241100340e1140c01800459a048801a121400d003401554803442048180d0401d0101e240062011900a000e0310401c6044400f241c010181ca460b0007010640a0a044082c104401c4c0010010404111403600d01c112812000748a040e20a0703502412500590041e90310314880c400000c1e0107030215400740c641000c01540b40c08002035907 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 364854451 1250 364853201 364853207
    0x3051305060d090201020105060f15031b0c03090102060105010801121202010b1914060309030f0c0a0204020d14070908030406080910021c15030f0f020f040614180c1603090302040903 80
    0x2a01c43c0403800745d402d05002a40030b15100c000c0009150025043c5214000d1107110b62031550310003031600c1e50304810904210080e03440b6001600719640303004019603a0381c0c2d8181c00039113404016031000d410801001c0041c440001c500005400865010300810519500b2490680c0541503014a140d0004822901502c01c000c00d42242000c4a10180b09640541442c000744202880b080399000001ea00420400d80200d0001c8010074030340b00000155044001d082e400039051381d00964540000c241c54100d0704416289410480360048000d041100b603a6250500c229128021441030506104001c030020311807800c00e20a01c908601c08010456031080320000f1400001034070040030004510b440c00ca101d80c07403401d001c00c0003626049021500307441003503a04c0900c40303429030f60f040342c01c100c1943c0d40d64000d031254003a40c4050a4041843c00c074142c04042888210044607500b94904440c010601400c0c09444d001c482d60049031015541c03000d025818140d60303201c0f50f43d100a4100b46401032410038998 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 364855701 1250 364854451 364854461
    0x120903140d0c120b10110a0204061d0906070f0e01020708010501080601240801052b0c05012601051c0804090606030f0c0e06181201020a03150b040303051305060d 71
    0x515485501584a16050340000c940a14140f242c1041701e0300710b0000c42c6030040461014092140c003c480c880311165022500b078580c3e90340200c8590000309071040740d91105009195100c1c1014005154500d04080b0041c1201170300a00c0030284941d003400c2c680586d200b804600042c02c0520000c0c8080e50390b4005483e5a55400d00c80c191400585500c955134a03046806881940c400c3e56403044111390801040020303450b51403076034014101ca8a11000005c1c01c1815444848034026100320f42040c0c42c000002d04034a40c5446074084440b40010850400441e44141e0781c103691040d10340342d050b00c25182d00d0403aa036511400c081c28031200807600003070020554110030309440e0540c0c2c0a110380d0b00300111003001d684c0349070400c8000c605c403828100c54508240c2d001d0024074051050040706810000c0208008180c8451303a040b0b00e075000a460406076405010f4002906c01000c00301c0c181d54a010b4043c0e400340500d00000701041400104030158070b41c210308082c0a030a005040513a110354003260100108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 364856951 1250 364855701 364855721
    0xb0103091b060f0215011806030f0308010e01090209090a11070206040923010b0a21060608100e06060d3b0d18090908040806040f06061401120903140d 66
    0x3985452480f10090710103da0461443e01c8058012607030303400c4c0401c0c04008042d8007004569185c0e00c2d00000301003411480180802d50090b11002440d50410004034401383e0140c002014490040107080c507561104c240c4c15074040628000041c40c00301c24040580b5900c50050007950150b40854003080004aa901010700103c0340f00b1265146801d03551407032152039003403060780c920800038009810340300d005241d180c140c0c103000101441070710f442e9003014044a002d90011f8000603280c808011403c80010450f03405040e841c1c04400c2e80c2d00c3d01000090440c45040e244003000d1391101d0342e4881c1046140f1070496919502c010404840e214280401c0c01c1118850090741140f1071300c00d510324298040d00e0380c803a0034011140c00ea0105401c150030800034210f0303244211082c40c1e0030403000071081003d0064a0041d44500044400104107050105c15030b6242c0d00302020150f8020700d540b01d683c2e040b454005204603185408031301c005071401c09580b501d448001d521040d00000855281e04803140d4401c180f11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 364858201 1250 364856951 364856957
    0xc0503011a04021614064c0e071205060a0b0403080a2c01020c010c0209070507081c0501080d0806060301050d05031201080f0709060b0301051221091e0a090b0103091b06 74
    0x20f2242e04a02c1f81074002c98444100301d5880200b01c0308100b204100305510342048003070314070001981c504845406401c100ca501e00001c010012200c909407440c058240c02074400c5861003810340c2820032960761842140b0004086440001300604000c0c05200807007401010301d242d2007031104035070a0342030380c000350840c00e40d0041c0a041c043c1c01d995070185031802001034000c1c1c441e0301c580d81d03102c6060300c1036400407106407051201804011030031058980d9245144000380000300c3c09500d403c0701c0c0c0e85003454058040c41400711503020040a9107540050f2411500f0440d00d030310b1140c00714180141103218040e000042580c03100004204902c0008142c00e038100c19004843c05542e894030484201d94144c003411542500800040159290007070000c030200c402d0320103a4002d500e01410b00210240d140c04012032102c07021814840600e045090300114078500c46180d07030100c608900090681243e0b004040d0002d030340309100300b00e83c7d200303a210000c040d512a4901590458800e008e8005c0a0103200b80000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 364859451 1250 364858201 364858231
    0x3030c080708100902030a02070803010312020609060c03072a0c0f0503030c1c1b0f0204060e060306060111010e16050a0506160f11060409090c0503011a0402161406 72
    0x2405201d242c0c040d20401c0c40f01400ca001c0b03800c0c01ca684020354806095044580d03000e101c00c0300450a01e82c000c500031032181c4001d03110130005800c00382c1000742c001c0c52000b483c2c00401c01c1280416040007102d80c0980586840e80c1444140b600c0003031140244802490181d070b2400c40c81c001c1003003031010303501555503d40720580000e513184101641c0340b09000c0e04c020f150704414206200141c2d002103888003405582030030051185004188048001162415146101030b403410a0640c2084c0c81140c01a06d81b40c132030542d0318600034000c240d071940040c090074100900c0501e0449048030a41c0300b041c2d51790f911010395014980342003c40d807103c4a00c0c0110351007545e400032f00050502e08002214480014990041d00422650b02c4281c200030440009540341c408480703050030603641c1c1c0f800401c090302030390900140700c4c00d0b241401d4083c1001c1c0c0d001030340203a1420008075402c200800c07400a24400031140540d642c1c544024211903801c6291000b800025403040e0100e9074403000c28000c1c8110b81c14010031034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 364860701 1250 364859451 364859461
    0x110310021303080d1b1d04060f1203020a05010507270602060601120204090501030b04060b0904111905130207050613020108190b12031902150c0319060303030c08 71
    0x4124452030700100c031055a400400c000203488440580903070b29000070300180b010001c0c020a001c040c0c451011100042c035808840ba90b04043c0d4050141c80c030001e0314100300d91401c109415814042c54000c1d120000c3d02e0f6048101094400c0203e95551580080280041d01b4400030141000c10f002c0d81c80e0a5115915040814001c2076003c00401c668507503000f010207403039801c01901d05841e840d10010240e80c00308404510645903028003070007584150346e00001480c2500340b03401103034882d00c111403080106405000204010303c940c0d040b241c030115484400c68020480d070503940c00c00b66100a400c101c4648159056012550140611768000c0042da000e9641e0011a40c40d01081c10100901083e880c4020880e1800010038107016051200740000d680120b95001610342c2d802c0c28003540b0107910018103101350341d44110741d40d8461003043c0001c00702c081031200c408106131801010b11041410200018502c044528208a190402c0d540100250b94803410014080e200450074840481c0c040404a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 364861951 1250 364860701 364860733
    0x2162102130e0c13050907090b0d0506070f0813030f080606090a080f01050108120d1104182a0225030206030408031b0f070f030504090e0c031002030603031801090b071103 75
    0x5441b45a5030345c040c0200504040160380201210344100c1d070020700380e400c0c600009101f0030001d030040c522500c0300c5000809601008050303050051107403058842800407035000030303003050310f4441c801c0450a2030b0b55207550745000309031a401407040a5030702560f031800c0010b010f0804607041c59080341c620020b2180e03030b80354001c10380d880c110b10311031032400356007042000582141544544a0541d040c042c1610740340c0d80d80000e921070901000210b4030b450703a44542c14502c400c109600041c0d5880142941c410400602d8040c2d1162407440b040c1c0c0084061114529084140c20202000b031540140066140d04140c1841c00550b04229021000c0c0b1043c0a540b00060480d4403e48400e8016a5003d61800e40c1d5a911651070801140e0200c05210042c400030580c103051303000d2302c0b6401c2d0642005240300d0b4289805c040c40c103503056221f8514944100140b0059840c00b00489903a4002c014000c1c504c285260012103110409610980c1c2445001ca10903003080313581c10030401203110850131107603801c0710745100d9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 364863201 1250 364861951 364861961
    0x190314070c02180a06030b0c130501020c130504020303191e0305060d080c0106050306011203031401030218070e150a020d02300d02070501020a02162102130e0c13 71
    0x41c0d0703c81c124110100b40ba01001260702e82c001c000380c8000c900a80d4981d6031002a05043e20b40d0303102400302080c03d007030b10030750100200002c3c5024030050501040e048007081742204518403412299403590001410754a080003285d0344000c41540c1e4a0041e600f9410052030000c24803c074011005490711300300f03209482405101d004080052004807803480641e02c107034443e404051421210354030380000040d41c1e030301030140900a00602c030401010b4501440c000f030032203007036160100410351400018009a03c8200c100c90fa0242440082c174602d0b128800143c6909090a00895000c4e18840801d00a100958040c0a0720030193b0212400106041000e903198a102070304040d066031824007168000d41c40810b0f550704000d82800d21482c00d65410198802d0ba44861829205a900020a040c04550404c80444403a28884007000b0300c45c200f41c1c69190010303998000222409074006040c0030740d9540000e030451580151b4007000840021040b0a485490300f580c13041c82401c481d0184441000c103405170b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 364864451 1250 364863201 364863203
    0x6010908070308190e09090609010e060c160201050c0d03020d0b040209030606240403120206010608010303170c040902030a0507080601030b0f21060c0d060f12030305070302190314070c 81
    0x41500300341071202c0888501300340051203405c200c01c5909090240d125a03080a000c0c17007110000d031205161401c492030035902460110442035200d013042284481d450000d56407082e40c1ca80c003290995a55000480c0c0c180122440d810540c021285440941b540690023044c404102150500100c0140c2c0100000ca000b41074215800d6008040090032500d0114000200c172183c1015030046003100e088a010b00d03400c00e401c216400190203040c1c00882c1d4040202c1341c010166450848100e41c10b44c1e80090000d40e0248224a400301c0940c0820843c03030340d8409541c061b10031082e04640301e02c2d00c0856070001e040b003580d1000c0481c1608012800c0755100b0701a130080c0100141c25901c00703060a8090110744d503080c0400103910410040202082c3d00107010b1035004820b4069410b1301c0b0031f074400081c030440f04254400c207120551440104242d50405020000040d094140000c00c0c5d9198031041c1e0103840b52001e208600c90094410703410007074050b80b0002d11000c021111004613500e201080e0346e030003c8c06078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 364865701 1250 364864451 364864463
    0x306030303181a060604080709090501050112031407030e0d050c1810172113060c030903030302030a110a020d091706010506220e090607030510210c03030305060109080703 75
    0x40804007203e007016100e0f41001d40601601d1070283e40780c18040c10408590045603e00780c842000c175040c801c00740211405005d400c4515a41305806990103098800c0101c44214200c0c00842c10710189801002d00a14070880900200c0b000140d0389400394072140e0000d0503920031410541051900131b04081c03070b01c0c0b141e4502c2414095003410315604000c00708511510b030156124052000c0d80c3e40c1481464459030101c2c000c11140c50741c0c202c0c400e1004865013600060108288600404042980020300350120b94240c10b0059a903100e20b00c05030080d11420700c81c00b02040c1e000078041880c9a0000c0e082248041360380d90b420400e5194003401c02000402480c1c4003041d44420014003040c58800020800d0000c500800740001100340d20104a18141e03501c0f4101904004080003020402401050390192651a00300043d103070819000041007481e006041025024005100c405a1490401c41c02540c1101048540c143e480c42c0c001c001d0002100c1e5903000800244000400c4400095604260b0b81d11003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 364866951 1250 364865701 364865723
    0x907080601050d021201020a05121302030a0f0302010e070b130b040b0f0c0a0b01080a2001020604200607061b05040b040605072d05190515091507030603030318 70
    0x2008100c0010521041a64841c0c01761424120070b02c02440208540030f49a100c01340c40703c50b0f0034a900e500c03d20007001d0020a000d107081d242c5c010381c2c0100d41c0141896012840030102c00b80f5003400c0380100440f407502001880780b000301242600c0c06101400c1400d05e00781881700c003c1d84644112040703025070312030288440f2091140e0307000c20707070024082c12001d56058100c4403002180d03203d920040700b080e4011103040d04070601c100107220f0107601142c403072040a00100280d11820000039514180100701403d5182c000810410f9a4000c00c10000d40c1d03500102219203469003410110001d01c5500c10042c1801005c440045809016000303031411508103401103400c06141000540d900e5001070011500340700c0485170880d2070804010704111840603011034902214107450000c0c80c01184c20908000002548524070009000240d8181511404203a05a20383c8400002529244101000409003108882080401d03039050f030041302100d000e96800d1101d0b01039910105900c01c00740d440600408151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 364868201 1250 364866951 364866959
    0x1a07170a0b1f0221040609151d0a080102070b1e040201080a0b01140403060b240a1d0a080f060a0203010e060f13020c0114010509130f11090c070b0907080601 69
    0x6404030740540b82071801a6020460b0080000c400e14a4015100907100c8010a0038000d140d4020113007030140c01429144070301142c00f9100600780107901c42a058807565400340c0103000d51980c1d0552002000003500a545030f814a10b00702c520250f00302e8180d605400c046140038041c6247c11b000500654060f1180b10b8507849042850740600b680040d51418004829890f19088101400400c0198001c100001e1514210740402c650894648135601070a101500007521460801d0200c0d152111030b070410710306440c00c0c00101a02000c8480005500c04a4141c0c000313a4200040781c8010380c45000c2043e14626034407200d02d4000c03400300b0f01496110384000c5000a080d81080c400c01d40d403801b801008644002c0c102a0a40e09a90041342880e066035141c00500d4410350034030b0b4985000d450116084106403a01c51100306401e050800060728244884c100c83e0140080c0c50039a080585000c0d14000a9182c0b400680e441c2e83e0101d9001c0340d40128900014541050200310700c4180c1c0c0e2802d003d4030709070f460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 364869451 1250 364868201 364868239
    0x141b0c0a0e0c180d060606030f0b06180f1305060102190302030406030c20030a0e010302070206030402060f07060905010b280501050c100203010f050a0509090307030302071a07170a0b 80
    0x10040240402040800a510f081c0c2d03181d08098080c144510004a0700b42d08101c801000d482c04202c06c00441400d212090845d40e80f243c050310811800e4440d13001c03018042c24002000c0c2c182c2d03d82c940740c1104015105813002c04a5130026841a0380c2a021148111204880540b44aa401e4070260041e0010700c0103205152103a000700511045510f045030070005d80044020759814504215162603000140702c040e00c0e40c001e0040300c8480c13000d007011420070700c1d40c1e00443e00c14400104002c1c85801c0c000b0b00c00344041c62000546440c04c4d04040104000c404a00d401c43c001c01948004521519011000c6200030340c40b0010f230303800e980720004255252444c000055030075412480606030940600e40f0304a1001003248042d50080041c0c401c0e014402c0e28040c1807140611280e0030590240114000b00250402e00104944102c0e6043c500107031f0f101c9185c01c04000e020212201d40c020701a0179403d010344145d00c56035102082c00b5500e290302040e2680780800048540b030009007038000d410400c080c0c0110300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 364870701 1250 364869451 364869457
    0xe0405011e05010207060c0f21080714090603011e1706060108010909020d03120b0d050c0f04060f0e0c040308071505010506031506030c0c06040309030b0912040312141b0c0a0e0c 78
    0x40304494600501c03451484010000058400d08000604842d040002496010424415031903607611200e237041042d1740840c54034801402549007550311003080314070080003000480010141d1440054850400c0e040094880a054505c1400200c0c2a400410113074101c0c8a8027040960042020b00207640a0b0fa0a9401070211b60788405080e90b01e4828440c00e44501038440d030b80e94483e4001e084e0840c050401c101e0b402500c0c03884203001d075261107418400d229040c074407002a5a00c4c1d5070300c0a10703070781c50600c042c0040c0f080380c00003041c040d40803404400b000301008651a0100c0e040314180f0035a80c0390020305c18030740411508200003494003c080341150078844001d60700104401410307441c0607480904145880001da90440c001200c1410420500008560741034000c0051b0f000303095500b0842d2090f05403400380380000f03031880050a244088241c05410a42030f0110b58030801611400310071a0800b02401200b00300d80c084c0240d003040e66241c5800e098150546012424000300340c0c50702c500c8250150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 364871951 1250 364870701 364870703
    0xb150d0308060d0204060b0c011b0509150c100c02010e010b0a060c0f020d030e030f010b0a140112060801020c0d05070c0b0705101e0b010309210e0405011e05010207060c0f 75
    0xf695511550303002d80c66074002c0d10041d010209610b0b645000384540e0b00d00312101d5080c21508040000c484644680d0300204031035103018111903c00e8400c146610602c818854484415114402c1404030311100344c058101d00d492011940080204600240c45a4240ca002c03034903050340312a2083c2c06103c054040c0c100c48050380d014003800c0c40b1140c01a400708205682c0c0f29020340108a00010340240b504d000c020f01d840c0d20500e10000e010030031809000c113890041b24001e00c6c0c540c801c00c41d40414641d10de00401c81c0001201c200501034959542d462600079440710810403000e010741c1d440c160b0a18013031021074014546c49507000c208c65141c8811107195411101c001c407000d00614404c10031141880c0900949030101251840744807510b03418000c1240d055000030b034189801c1554050201e000702001040902c405da200c01d0f24101501801c42c0e403c003221030700c25800342c07501c4000308005805010294048881e0403080c039082d0344407801a030380c0300c0305445180e0004840b0080c0c500010003c400b410042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 364873201 1250 364871951 364871959
    0x9050a0b2a1e01090c060c0c03020f12011b08130305030f0405010603080c0303010f091406040509070f030311010e0c0607060b030c091f27021e040806040b150d030806 73
    0x124118103802c00a0786111210b00326182c1d112480e5406101503d51510002c00050801906100d595660410380b40e200d8840a880351060202104d01600c0709418031003d218100000c00c00d00d00b440340d0386000f0440f0303a403c840005105200044210306243c1009032000d405844490466503001c0c0c80005183c0c0040003291a9503e035580000000c0c4c059002e00003100a00002e55100c1d1f04005004680403290707407020710210705094000282108029910f500280150307408142680c812407a6460024950b0000010380003000002082c0b55020101a0351043c2c100c009124602c81e041500c1e42c0c0701f10b40e40c031840c2c4c80b000410001c0002070280e4000064004007606843d141e4010301c00280514104951100000048103551743c0400c2c048015179015100c0031911400380c4031840500169000c84a41c80d0b608654001034078414205106d090f00014881c409a06540b181c41e030443d15142d04080c0c0d0100e50242c0c100303002c42c00c603002c110760300801240003818a96412075107490443e600c2e00064100f40e00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 364874451 1250 364873201 364873213
    0x501140903090d0f06360f02010c020a03080f0a0e1e0111010e03030703020301030615180e030f041205100b030604060f1503031d090c0910020304120309050a0b2a 71
    0x148050080800940b03403aa61b61520211900c01240c548840d403c4e0001d070010f25241560000d441691032041342138080c038240d01d41d40075610100b0001404c0343c1000e070140201080e0000d003500700c10001c0a501241c0d50f0396800540c104d00a11200c0070101c4240914940103000b000e0a6501c0740001585200e043e000204980740155a002d055900541c2d000d400250008010b100740011405403181601800d002c00703456900d050f60400094101c40b014500c555120450700c0d81000c1c0403c181c07054014002d024540d031302d40d500c0c580141205251801c5520f40100c45003182c030b800513032264811450002d4054150740d501d5603208002003484c41c0000880340da540f03555220408014510034051486038032079100301e1001180c00100c070360745081180e01c10b400c10f03410002d01c107090f1001c0d2484224152440c80c071003008080c050f410741c00349400031070207150104405010701d0341c40401c0004031542034803800e10303240d118807039450948110711001c8022014070180d1540b20401b500c19101c0e1003e0350042e108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 364875701 1250 364874451 364874453
    0x5060105070615030b25030c05070b1306050c070f0b070512151207080703110d05030a05070b0105010f05180f03030f0d0605030607090902160b040f0501140903090d0f 73
    0xc201d81103c0da101c2001c080206040c010400c0e0740c40290f0304a62034403004510700708007040128007101454105020951514a542d5080b4060000d4413942940300203140e245140038044840300307001004041d00c1e2282041d001ca000f295490b0204d82010741c0101b4990320386e04031307906e0f103540d04100901488104081003111611501c04150085d004200602c0c0e04950041c8110401003904191500a5483d40186104101ba800002039500850f58824100d94001e8000c2e000104000004000603001c1d000000700107480c2903201e030041100b288912110085a600d40c0c1c01100d0700c0e0f1001d11000c010a00c200301c0c08194030381302500030f00000b100421684a203080d2502013415038000014405100e0f5000c60f008240740d40310300a04003d004250300421301858202c40051241c0c01c035100704160320f1303400078401d400611140710020708603401000d05952414680b8045c3c010000015080c0d90b03e500e0302070f20f0300300d44108400f45401808480e00440c01d0903158030400001251968048400c00640d00500e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 364876951 1250 364875701 364875713
    0xc05040e0711010c05030702070512010204170f0106210204092103090203010b040c0c030c05070819021201091106090a09090507061106040812060d02040908031009020f07060506010507 81
    0xd4480c03031940e554602215040307101c007800d403180d0440580a0160510070008580c0d4002405021600c0403200700b2401c54040b005180240300d41e41101450107070f0350884a034bda580004094542c458120001c0108030340c0e80200311020883ca80d4036886401c0c0000c1e108025280c070b43c000410342e9016810006d03513201c00c50035650f0400000c81e28580070079200e800d4141507250a01c80c42805040c00c1d2000d000301c07d496400180070ac0a0303040d008050119500000061090811006000c2c24003071040b10100501c04441203d0040c0347c0504a114540201e601891a00180240880d866104840400b042001c00c10844140c0001000640003041841c3c0003646201c1801041c1d03005010b40050500c25040010007401c84191104525066004c42c2c00e1000040b08070045541241d6540a421440d0b224040000c840001e070700030196016003400c80c01c1e0184510400110300503001160f4505d559a40e49804500340c2c004e038003d003c4075440501c610070100f90140c20031507004005261440c500130715580c2d04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 364878201 1250 364876951 364876979
    0x4031e020124090b04060311011412010b070b0a0b03072106141b030103080702101e02010f0e0c03030d020c010204053114181911040b010516060c0504 66
    0x1c0300d8007102c21901009008018410000c0d000c40036a424814181580c0341d4444598032a4002810020714158204821341040c065850b9030080582070000340d6940c0400002d150002e440a54a100800c2c4c080b0b03100d20b03030740e124103822020f018000c0d044c2d80b031600048600b01c2030f070401005000c00c524030103100010800d1246030b05180f41001c0c0394603d41450703070503032150209200c0400b4a0800130001030001c0b403405002c0e52446941142c010311a0702030000f00715404192180c1032801203650b1081e01510507010b421040300790303003504400c001c008003100c6420350b01e6840d1901d058068000b002001409202c64004184a861080015140c260ba4402040d41000c0120601e16070914604071100c5040c02520f8114812000150600001d21111400071082401038882400c0c018004200500e04c2070a00c0b20007098010041601558001400d21240301e004600381c940c401e510382003200d44903601410650340c040c18621903481800e00240e446070011b180c4e603107046041c04000c2c440066070714070107440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 364879451 1250 364878201 364878251
    0x60a0603030f08190f021c060f0e0901060b0301080d110c010c0f0507080a0f0b150109090e0f030a09061103030702120307020a0c12200303030a09060b0415050a060804031e0201 77
    0x401030340c03283c1e45102c403a200303500800211f13030704ca0500380d040183c0e414000d003072416240620b80501040d280c529266004101d95842111081808800020900b001003040042450603880b050100d0104001031038840c160403103d00d012880305d1041e900404d84041c0760300501e600c26821569816110a0403a01d80700d0031305400c80381d440c6003040c40030801500c0340c079160b0820780000c107003242081014006443c64102e40500b0359241e60303d400a400d01c45080182c0c0324040c440e5000c0d00d035980e1181030300400c6030040c0d0040502144150001503148032001013101c0c41070307803964081c0040c01c00541c61f914640d030002d81000d08611580a02c1d401203610048108010074031006601a03500040c0f070401021800e10414540c00c412140c0302d00c189403000720489034010600800046c44d8542c80c6841c100421240c0c820b83d0300b142c90101295a02c03441c2441c0e0310240c410480304c0320074040d46d5240c21504d074542118014000391105101400101e4038848803002241d850002241c4160110920300d81a0b4019034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 364880701 1250 364879451 364879481
    0x405121606050a120f0f06171603021008040201090e07052710030f18050102120105030604080901030c0504030f0323040305120901050919030302060a0603030f0819 72
    0x1000d1201088240308890052607107080c014207000407410007901c08140c10254002c0300b82ca4070641038030100d01d68003504520300c035542d0820480341c0710380d00d42c102c00d0f40d501c5e400d18840c801c80300d045905035039958184040702e90050000c5001c401c0c10404440e2540058003c0741800409900410308180340303144c0500c508513682e02c10b42c90f00d00340080900808004d6048524100314018002801d4990300c101111002d0316083c00704518032101c0400c4001e1410440301c05000c01c0070b0407403c04004040d0000e00b80805240c0300c0c05a1a40c88004040d150042a100109030f001c0400403040750b94000d41203201100c1a0341025820140c1d20345a4045452001d1421070015600396440d0200100c600300c48030740040d4040c1c4080c18681169a81c0b9030b6003911002058807000b0100d052006a84075004552050f07401902d0172848015040c00310145500d00e000c100c016005940010b1103a007194400d10b003c41e505550b0700314124944080c00d0341c0341040541a0001c200710113003051103010450250245c041160a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 364881951 1250 364880701 364880713
    0x6040f050609120615130e210c0f100507050418050903070b1608090d020d11010e010c050304050705090f0726091b0d081210090504030f0e101e0203040512 68
    0x2041008400c3da403442c0c4240546054054031481c20009a114002501c00701c1d42540d0808c88001030307109002d800061141e52003548980e43c1803540124541482441f80e001c1404161551042915207001e11f0060b40c20314000d40908140c20f013465001250407064890980b440c00b04503466601113075500b1034405000b440c0a008829640d40c0c40000c040c0d0096101d03000c2d01200255180094442c3c400100303800c20064240200003054000303500c1076000e91000f500800480450302400351a03504100d80984042c0180d50740013446040c040301c0340e48901c0c0035201101c0240da41e4a020b86550000b02ca1510160b07080d414604c04040733030000b0150040000400800b0440c0042c8848051380e02120860381c02a40d14408007000070b92104150f50401c61380311259038013640d03644240304c045032403540075131400d03801d15040c8418540c1200c600a80c6d50020b036107101c14a807002c014400111801d40d1180001010790740c80740044000140714200300020b0f0300c1030300c0c42d0a49e2000080e54007846017080103681d42000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 364883201 1250 364881951 364881991
    0x80a0b010512011a0105070c0b070c06120207021807020a0b010807260312130b070504050a170705040b0402040306140a05220816060216020f06040f0506091206 70
    0x111800051001555009001300708940c4038190060a034800c2c0d5505103d404035500c001c11803c20704880103010108441600d4030458142040c1001052003580c01142241701c1c11a1031051034002c580345140c01a0260704c1c102c00300240c80f04c03080b030001c00100c21405900020380000d00c2c00c1c0e061034002c1099000401e51141880041c481480e810b00b1490788464400e007581807441d201100b510343d0a901c0c150701034016500c0510114405070580c00040c18501c1ea40e04200c0b03803a80080141003a65421345410f00c94036110556040c0782c10050b03040c003003039034818081000f00345061780000c2c44180001e0405070510395281ea510b025241c20091070105110808204465100e491140700e5100a04082c40000d10920000c1c6803a5140d0310302002c0c18024000540803440c5201c542c2c15481248c1c0507004540e150808104d40008080e1440100c0c8107a141d40c0c80c1d00704034902102030343d085d2014541403403440d070b20300f00820440354070420203190019010701840701d07001c8051080314890054550001d10b28401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 364884451 1250 364883201 364883209
    0x312030e1b0f01021614010c0209071220031614070609020411030c0703050304030315060305040b0705130b090d02030703050d030b0301020f0307031503210311040b03060d0804080a0b0105 82
    0x42e25020354115170003180610300060150420004a54030622110f050306090001200c080c103200705c002e0b400510300428003820300c0e444010007212440052080000d05010f464450107029240d0820603202c40510128000340710700a1494000035a034148042c14243d014080e02c40c90300810f00c140d5170b440c0d5502c180003c0d420309029681c0e070b603401340d240c103441e40c500002030480b01c1c01903041c003508101011000904040c000d42c40307214519600701c000000c040e034440b03008010780021602100d8051184000c41c8036240100c0564046465030240800f6150500d40d118410f43c10804401c0da0288518045801584080c04540301460040000d000840300005014040d03600301c052481c0a0381c810032404401c9078440003943d804c0442c502d00400d0000410000034510f50b4541c201410215600303005046040f010708820030000c01c1518140700141440c90302076103038020ba101c0c42841e0380040000808030b180101c8205007075445644041e0400c1d40b280c1d02c0302d00d010b95000d4101c0e50410760038014809441c2c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 364885701 1250 364884451 364884469
    0x603150c03050609040f0b0c0d050a0204031103060c0405150904020403050d111b01030b01110105090705040c0905030a2301021306140a020721060e0c01030e160312030e1b 75
    0x20903144000e160802d6506d20403451048000075111071a4540458641ca44042c00c948203140d40e24414000b90800d958544000d40c09407008860341100c032110602c0b5070801050040c45002e200304640d05240c6818180105000c0d8022145600c05040102595035035841c0b01510256004800515410b2070030f000c0a0840078175001c10803503da1000103040080d1415180300d00d2082020f290108640610000582d20b252a540443c251542000c007001941c2800040300c0b0300b02d5a0455041c01004541d100585219006004498042c1c12214402020a0103100441c201c0003001416007215070022800c0c47c00c81c0c01c810320001d4a0b10b4107540800c4190741c802003488101c1e900034495482d0085540c8003030f594629910610540c00440c102c8460644552000300c503205800103001e010b400400042d440d25100302c24940c2d4086440c1000c41d00524400195403003a940d4040c8190300300c40c0c110348402210050b2401c00c8020107031078141c6039100d01814400d441039a500d042001030000244410040c44030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 364886951 1250 364885701 364885711
    0x70f03030b0603010e01152a0b0a0905030403060e0a02060a090e0a0212063a0227130501060f17070b0c0c01110102040504240f05010c0311010603150c0305 68
    0x43c0014000c62030081069411281240c680031181190b00300140c9100440380f00c0c044c50060307000e4250800c100140e0002070900d00c603c40b044c0c0c880c0c2e07030091405e04403803154201420f1a4401c0c481440010785a51004405a6642c3e00b112080080c55001488583c00b03100c0000000e1081d65007040902c1b1102900703900401900e4066043c0000843c1c0c01070141c2c0000d0100d0f105071038603400e85480c1c400c0018001d607840c00d51800b008003a481404e0400005000d02c900f01c0c040c1001c00006024484149124250480810300d0402103481d8410040c441d1449500c00355095581da400004d80755034404000c60051502200501c0c502c14001442e03408c03d03115502c06003484030100300c0090350341070224031240310400074200400d004c0505500980240959006035801c1450440036805070300b0003045050245030f120003020a1180c40b00015a0000400c0c03084502081c8964040c100080c002e005442c1c010320f111000040c81c1e0303901e46500600352002c01d40050b00302e5454002e03010722603043c06042d9001e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 364888201 1250 364886951 364886959
    0x40614040909082d03070f141305130b010c0813080303040b010303080703053903250207060909050c0c0a030e120714090c0c0f07060e1e0405130206070f03030b 70
    0x488280d03e0755813036600c80207100b48208102d4002c0c025075140202010700f4401074071644141c0352600601d00a80038080c50051502c80c981e000607150900a50707000301000501c060355082d05060782580c681845820152401503000184600410444000c10180d4850390041211401e079501d1401c02909044026016104142c10a820094141031100301d80414503e8054100c8580808548010400300b051108187e101c0d400424003403040c0307144001062017803d0302d0041d6106000b1140607a50303001c9a100340004100181800c002440840d480254403040150380245803100e0402c000342020b1303903000d0440124400c2c415079034a5041020510f168581c480d0010502c15050009118240340100d068901c500b5542c00000e032041206425180503a01c0362040750041e0494400c80c2d500c40d02030703001d80750014030182225845850121410280214070307104041c0d10141c480140700103010000c04030300c499032500d0040c1005803100c3c0d00410031140219144141c880240ca0001c080d148140841d80c42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 364889451 1250 364888201 364888267
    0x708150a0507080f01030803060d02030f0105150a0e010b18040507080712110301120804030b01240509090414010e0312250210090f1502120a0204080304061404090908 73
    0x60b2004c240041c0b81500d81000e000c68481d80d8805c000b90040e108404025014002c1e040280380c0701c1d105406c0140158040303040b55004100c0d82041c4500000e55104004200d20b44000420004414000a04034510b009034030114009442c4003140035901d040d2029400a20b050041100f5517603c142c0783d85d075140c0d08003418429622440f0150000e0b00042c0690030b001040d0390b40c40410880080101c48c000c5a014448043d65a07498200700c1c3c5136114103071000f0904100450040c10203201b64103c40c48003d00404030350094803107840c3c1200c142c540b5015880c103036503196134804004101300050035041040340e00c08825490280c0350302080d00d00406042c071112850405207000150003040380c81e02011250710024051100c0c3c200120340c0c3c071a004010b00ba0101046a9021080a80e00142040c01e00a0310780f60042e103d65500c0012480b440c070840c006500305000601c0090311410141072602c4514561504081d141c00c0590221200c94000305c45000002912103000340301c8804e08150440707a04070b0044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 364890701 1250 364889451 364889461
    0x91101142b0b0a0608010e0705070b0103030e03100e0d030e0a020913110d20030d0503010510030f0501060203040e010e0714031e04060b0424030b090708150a050708 72
    0x244504220304030300790a00a80d04011620000e9111000c0c9200c01451194a40d5403150060715051080c040c04640071034020000307003034500400072100000d62007820a5802d85c40c1d91021500d549904498070340c10b00915030080e000c40418052050aa800e43c0060140f90403084405411140568802d00e1590801c480702805a0f88000c07025500c0b5040d500300c488240102d1800102d0110000c082e180d1243c2103501d001c0600075404013000c482100010140c074407441c0001015a140c481d80c010307070001141080103000e641001c04a076202241d46060210707000301c03800c05c60410703100241c00810050f8400f29040180700e141c500701c84e00416100070310010340c0c141480700604662200303c0e40403541e2400804240b000d4543c3d209403128441090b820541800e26150150103458610481032250f42000904d003110380a40e580200e0b00e00310000f00e0004d051442d40c031160381c107400614001150180440000d1420000c0c00f462500e6800c1120038440351400c1034802e0100d400c0500854104421101001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 364891951 1250 364890701 364890727
    0xd090504140f070908030c16170c1507050f031e040b0307200a0f0b0903090f0405060406080601060807170108030a0311090402040f030209060f09070806031009110114 73
    0x254200c2c81402d5054901c0e0b82d444000d5803138070365661003000e03540b00c0002d60301c880000c08504552046102ca42d072a80e0305035100403510100e4100e034040c419a030450000b00c0c21924158200d6842e500306100c10314140501c41d1038150400105606909054200140104042040301c04400f89480400e424504050509040c01c01d1030100502c00340c140450480b60a81034141202056000756614080316411034043c5404c00c078074218094212141540503010407034021010003071325482c07407020f000585580c3c620300402003d004080c1c651500255103080115020000b40b1a05010303066035220259a03040140000b0305050313080c000141c50328030000c01480b5584001c0300700d4814a2162401055000810442d407482d40325040060354058400100010645013542d005811a4022a003180c0c1c0da80d500028000c10042d0010b8043c9e000c4d84000014400d280101516a0032800107400c0b54265907200c82c21000311102c407e0181c41041074240104001c0d80d01096030380c0101101d815450600c11004861 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 364893201 1250 364891951 364891991
    0xa0f03120504302003070603020901020d05090a0b07120f0c021f11100606110105222108010905070906020d0f05090d1a0a020301030c06050d0b09090d090504 69
    0x716600d044036800c50442c494049032050f6109030480000c00501000380844c1c90900b035160012800390003109000a01c01e07000c1c0c030a075180b180041c0c001d03280745c03105508104c50540c0b0491400c1d500c1802e090b0049001d214480252010621813050b222584400840183c902d06101d0300c0d140400c69016030b242c0042e2910380402041d08540401300c000341d5844c24082c0c07286a82005550070511403452903404800c03450f0807076021607516407a04040d400c90092014240d40080710103403599514012030380c1040003203008002090380140741c001045a0b400741a41d084100c0080b014000807101001404101d0851007150740240340e0b41464130040380342181c080d41720380690414200780001c00718480d003294081e00454650b400004c1140581c418945840b00da022891009042c92005650004814960910849060300c1c3c0001004000a1404104941c00e510a46440281c15150540391445845039850640114140c40c00f900e040c40c00e04000420814039640940d00c51802c2650440040d40c0000007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 364894451 1250 364893201 364893239
    0xb130f060b01020a021801050a1410050a0516060b0a0603091703100e04060e1501060c11041e1b020c1e01050f040e1f060512060109050a0f03120504 65
    0x718100c003020006038100031032070001039000f0341e80e041001003e841464400e070580d40700301c44248041c1c0d155401d0140168000700c0440e082a2088140448580548040d080c0d1405500e000c0703240141c01c22240c40440d804540840c0d0040d294807041c0c015241c4600408046c149078a801c10440301c85071108041030b80b2107503035100112400008500c04480e1440400050949400144064200351401d04002d02c0c41c0c00c002c040a01859420700c1c602c0c2e880d0b82242e41203401d195901020290300e510340100300c01181a0580e80190f0b55070100000c038020300451181e148201500054103901403102191040f400c04a050442d00454203281066444a182404070280040c1c40885005040c00688452280d0312070121000c8001c240000c180d43d44224003849140c103480d440a60340030074240b52981d2085030044c28045902841480c03902c2036225079042d88200d0515148140c681e8030004510810650f40000d104200079500500a0050503d401d4446400750711340a0f180c43d1401d111a00504907001c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 364895701 1250 364894451 364894463
    0xe0f06190b24210f070c05061f090509010c031a0a0b09040f021603090503191103010b130b030105060d020a030f050c030d031b020f03040510021204060503040b130f 72
    0x10301520402c0c49415079100481180d94011080744036402e07030000840454039a031818580b140010395040c452810140000d602c50014481610b038005460b5103881d00c1710700701c1c11a0032150170004403007034a4050345010383c08100c00001ca05c1c03480c030401016551400701e0070900074915612010f8689820f00744500f15107200842c95168141480014040d00307103800c200c8007150001c03c0a14900000c0c4501c50400f5102c0d84411440726551424103172624000d9602e8006101da804a44021980c81c0e5000460340c44028000619802140e00183c040301c40c170040c103c0c007540c3d11241c1418609091043c41d40040f01140c6900007050b0a90010704105094003005004e1403d1035595820000e04100403501040020252540000d0304c000041c0142084000b8501d280122401260300b203002003401c86501008001031803a1601389028071540c40e0102e0152011840340c0e6508030389000700a0003070700240c03120b607541c141e0301e04140c1859071311074101902001107400c441c0074040008916128403024258845 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 364896951 1250 364895701 364895749
    0x1a03160201321f141201050f010e160512070e0a0905010911070507030323120a050109020903100c05070f05030d0b2b060e1f110702010c11040e0f06190b 67
    0x13030100e81030400030f03862050345601b1b00c000d00c6550a0060010780c1a01c03229420f0b4100ba90b070381c150028800b80b4040d82c0030041001008000070300000c261056512640b01d04100c0c0d1001550004224210705550100e40042d6484d80180311100c16030240c02d8110000144003824814140c89407915030486100050910410b80d941e1907204802005011642081c0009680c0f50700c1110b9092082e08811a081c1d00654038040001c2551607591080e2044070313502900071300f0750241407240305d07001308010540c020034041c05001090010340341d00d010002e8144039801542e02c03290380207000382c280d95401551520814101c00b01540d200d452055035200ca85101d80030f03d18074003ca08094006007404500c6003024000c0030f581e0400c50644d448892421590220104200001c2c2482e900e29406440c2c0000c1c0010f520804d00c2002c6044400000b840701c90061000071401c0340c01055514040701c0025509543c1c005504000d80c4241051044100544442040c44280030500c00502a994030740c00c0c0042d240320344 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 364898201 1250 364896951 364896989
    0x20f0309060a031409030d0b0108010311300f011107020105250212010c080703051005040b0f04060e040519110405250302070c1a03160201321f 63
    0x4e0701310540665885004640c5030805105064a030344c0801100603081d410540b400e490740d445201445d048030f401804041107100c0c1d0400f0032401c031044580c61000d403440c00700110400d00150002c8808000400003c2000000b0400341500b9160140c041c044107510520034500943d80040c2180c0b001c40000b5007100064141d110182017060003040065008160f840c2d088082106c154018546a00c6640f501c61090703035805400c070283d41b41228202c00c440c2407150204080e00700b0740c014082d00e000041ca410064011100407901703d91056000d0403451b05904280014490140118202034040003004d01103080f4907154080f0b07a25141075494021941c84001842424504c0080e40d80114140c1000c40c2143d46207034010041d4210319421349040c0100000091007a502c0070307025180040c0f59850302d00b141c1d11180c1d49508905d15040c0312055549400c0d080c0e8400c6c602040003c401400101d04800340200400c08080144000749242c1d2400b0311030907d11000000f8011341c40c101c4c1c0700307511441805030700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364899451 1250 364898201 364898207
    0x30a1b05060406020d0b0f0f12010b18010608010b0703020c0d020315160f051216050d05012705072102040f080f012d0906110d0903030c020f0309060a 66
    0x620a0151050203150203100410140342c0092820140000050042c5811842040b00700d0384048946980901c803052440340b141081140070503507a02c070000000364115814081426158404440c1000414590040c0581c1d50407007442d901406c10400c140d801d080544c0d50295864981c1c400c00c600c00c940310181002107650400c071a046001140e4480c03140d9050510b100e8040151407411000487c071032014821256219a086d0385c2001c281024503581c50b00ca030074411000304500c4071101c0c1000020090190030030114055035008000300024441c100c21300c030340c1c0300200c503d40c1540000c400d4241801d00003182c1e445018050b20745001c0741011131405c8041d4012000344526808503000c559003500c0060800c0000c070b418501c00c07124030002d00891201e0701003100d1000c44480c4107083c90b0aa400716441300d000c1c85d0700c544101481210000b41c0001801c0c2d103c8115004445260b00982c0c42d400030344101a494010720040340b00c280001e202c4250b20320341c10742e00c0340182c0802901501010541c2c81840e48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364900701 1250 364899451 364899497
    0xc0a0e0906130c0e0f010c020915030a02180a0b06030c0d0c051909050a0e09060c0705150103050a0201031a0105091c0f03020d021209060901050c01090203070b041701060602030a 78
    0x120004082003070210009011308000c0300c1c1c0d06058440c50300d464524031594024060284100e6006080c400c042d500c1d0036a000d003508210b5900340c0c16206540250005841d0000130021503601c0007000102c40c80d20740f10800980d14104c40308d83c040c80007131041c0518a649030003503580b07209002002140c030804100c0300300d07400c3c055111440215031603048060a229004402401528010744400514a0300ea80002c0303181d80054407018130342d0b84441c1c006100c800b04040908100352254007a294401d4003003d010745c008800b03030019186130f00024080400c56800d4450248800c001102c2d200e01700100c8400a4118090035110502440780c45440e4002185113076008001c01d07030300100d03910010043c0d06000390f0300c2204200000251044844040618492109940000310010042d0b407501940c8001100c280c0c000484050355592121545030060b94148854000b42800e00903681c1c455252405100006680204210443e490840c0601c00c0c00c1c2e0100445015140c0c60030035110f440040846054070076 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364901951 1250 364900701 364900729
    0x120906030601030906110738091212010608100807060f05091206071704020901061b150e15010b0a1107170109020f09060d240509030702090c0a0e0906 66
    0x51801c001b404003221403502821400e405014178161081100318a0017200048000460420303025602040300110b1040010f948041628103644e145000381c00002c00a17000003100541013080d450062050a40c01000e85501003034603078402e18401d2900398103640300c04143c0a61410030a042c000b483c03881d40254100d03110100043c1a12154043c40c04500307441d84400d4031441c0025842c003020802600f2020300700703400f594000740800382507403a0910517550a16104409204940c8030100b18001c9203d801d14986256282d000100340380321660081420300301907140e40101c400c84480103001c0c0c0ca08100983d1081041402c1040c20305d14111441881c1c529640e01c4410750310082d850b000f206c032034103410500302284240c52808030500401e0400c0030084040380c049400900301c14160021803400d45101c030004c0490140e802225003500c410805488007103d183d8070f194000107010301141006003115131b00000808800303041403810034000303101150b1030980c244102100b00100e1801c2c4c4c2c1e003c50601288d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364903201 1250 364901951 364901963
    0x1c0c0302160804031a09060c03180f070f050303040e010909050a1401020d06050d0503120c190207030b070504080d030906110301061d0103110a05031012030216081209060306010309 79
    0x810328050310382d0f9205000488146210709080c00340a2051070902e4094648071000d810142d030b4150400030103400082c0400301c1510301202c0241701950510103400503401c1100503080c414288042c076a40680158032540c081c1c0e1040208000b20410000b090b415111005001f244000e40350908515103d041c2e40c0c041c04001c842100040d00c29015401024082c204503020b108003595681004850808910064169001004103686031a4403541c10f0ba400792401c1007290425500800c1e0000b0040d0a000740030140e0702c2041c1c10310600440e00003966014510340b4107103181c181425140c13a1249a4060260f00b0b05480c1c0c0420802c000d41d030f41149410f04400b105550b140d6030348400c0103000c440900c00302e04029551349030b0320840394424051000307200c00312401031307150040300d200440b404d40c001048034034603051100b00415480b415030703880c04181d80640d0040c079001184040c403160640b4194480c10f02540107a5825580701c2c0708509903400084200d030240d07165a1543d00580c090400404000d2074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364904451 1250 364903201 364903237
    0xc19080f030711190201080103032d03020a0e0904170a1106190b0405091f0e070b0901081003020a120302010f0f0f15050a05040213080609010506010e061c0c0302 71
    0x1c0903920807910003c1900110407581505800c8050b5000d541d030016001e400640c840c40140b0119000d040d400a6200345410307000b404c0d000944084110307407403507450782c0c0000e0380004005600961080a034941d11104880c001624109684c420106007040c1204045d0036902107052070520b40a4540c282e1455411800e0306c100d46401e00240c03042402c4484900c00391481e00c11400301c0c0c1d080500c501841106000c00400030f1000721609070340c20464400d89004c415440750742003102f4038820b100380c2c0c0040400b2805039440d101010000b41008400030003080d608203541d1420009640d81440d218111490528440a40b030b04505040303001d09100311003118014140041c00b003151030f403035000070003030203860754200f01c0704c40201800c3c21080098462039601940500c2e050005141641c0100500c2d99292282c0600d00e0755055410f080403412180c0704c00c00d0b556802007200a580000c032656000710200c9041c3d1900c00b608002005070b52044404080103a954540015002e020358115aa001c00ca80c00303401c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364905701 1250 364904451 364904461
    0x30d030203010f060f1b2117070e0d1703010303030617030405090c0c1501050102071403070504020d0b190515070308070c02120f1b010207060210110d110d0b01050c19080f03 76
    0x1031881c00003665082d51300701c15002101340e1003110a14423074035595610761003544582e80300f181c48001c170110007580080c80c0e08100d00000c284440160003403103c1d041580c3ca030b62443c1009405c496603903200c1425140100d09031420703d0004021601591011a02040551100c030581c40450241d4a42d10b1007a200b59142d82d83c00c80c004011450498409a003240e00680d156030f0007880c944c040095941c0c15610501041c451490590090441c998504100240098440000500010103960403a00a40c4501c1c4203005034107051200348085055282c0940c5000c040d950010400007000301036a0400115001c51411513941801500c00310705203800315050402c422000c15190549644541d0780004601110382065001140407403c0310b0f20358008d08604144a40c3c00c02c0580385068800151040801012132041c8442c4164049000c603501c0a6840d01da0a807403520480d850425403034188001840b40d404005e100090200507480d420303000d40c0114030309161468a0740a00a041405807101004101c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364906951 1250 364905701 364905713
    0xc03030c060b010207140d08070503040b0a030e0d1b0f020303191101090209070c05030d0513050606040603150e010618050f010b030f1b0c0a05010b030d030203010f060f1b 75
    0x11038540682010030480e29002c0040e03035101c0d150701c505440060b1042c2c6214440c45c1050014803c41d010f02020780c139058281c1c0c1e0301400d562058004c81e2201201180740f03051a40d00d03120f2400c0808403000180710f000d0440c0b101906200604a1040c03c50707442440c42001c0240d59145011141c1e400f0301102e85071440042288041119140001700198981e0010131003401d0501843e1f00b800d4000d0040356498690344400c072604c10b0040c02c29906031000300310b140501100c511851b4841d68085040c0742c400106858083c1c2008000b801c07132481a0300b441c5040c00450b0301c4901100301460a040001080a0718140250150402e68032404804500d0b000380c14110728a900514460606e554205c5c1150307889038139152090200303403000f480c820b51180004102490071a11270300301c10602c850319070620703044020f164540588142c0031a11a51500346144840c1030800c582d1340040c400d41015803c0d503040040c0808444141e11845081042d40c100c014150350103452101003030180304010600d001d0303143c1418 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364908201 1250 364906951 364906967
    0x1082a1518030303040f020118150203030103020109090c090918050303010314070e0702060705070609080c0f0106050d15090303091401050f070305040803040b1b0403140c1504090f06030c0303 84
    0x214400e0661070040e00224600401101d03c82e070780c04100541458001e4004440350f4040f140e00550082003210007141c40400741081d45903900048c2d0080d0b940f9030451000425605940d4403038170005040c5801a44050307001000582940d4107000c00144c5580401000100e84603014005481c40c000000088103016002c041c51500b40d403075004486400c0c1e92102c071100107002c1182c1b60b80050b0407890104044920a40c01061614041c480205000e1b00c00d0302d480019034000c502c0d5034029071180b116021850000e0268a00820041707500100b102501c1e21000f4140c0201203401402d90b40d07400610003018040d6200360395880e08503500c50003004100a00c28028a41901c2c200703404500c039400601d110380b1034058a40b01d00c0c1d005e01c03540c1c2191540d9a4440503100c025044810300a00f40450700070b90580038005d04010f50040700e5412508494548240c1441441c0c083d00e80a0300e0660980c05002c80f020049808550545900281d10000c8101540c01003007560001003090360101d00c00414198403000d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364909451 1250 364908201 364908217
    0x3060f09122a0601180203040f140a0507060e0303040e09070b0a0c0b01270c0207080609250e010e090102070c09020901080f1005040c020a0210031d01020301082a15 72
    0xc03810b201a848089981c1c6030000d101d40c02c0366101140c0c940489542d1600915041341c400c2ca2480c40581c2da40c3d41e0060800000903950005501000303a100c240441003245000910403400c0441d110900344010a48034411030084a081461640c089074402c08100450030060041074006500c1d008010b40003420108805000d51b0b02c040003600101c0c01c0f41c415804890007500002184114641c44040174028001d001c841109601400d40e0004000105103c0584078800c4a006024060b00b00070010800d00c8042c034110b1001801c15106014501c582c11010341528818444c4507600e56822880c1c1e40648210b400c003c110031020f000000e400a0503401604000c0c6013600c1e545c406a6807134808401e140d6084604000345580300700f0822440c01e056200041c4060580b0585130405540d8021614401c0d505c107030600040e503199003114440001c80450110380109a00030b40c65545405030156540c0b080c6250b0300d81202e01d1990411001c814400d480140b0003001d480e011074680c0c6641c0c280301907000005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364910701 1250 364909451 364909507
    0x10e1f081009110d230f0108011406060307050c070b0a170106022407020a0b010e1005150306191502060f010503031c0c03090f140d05070203060f0912 66
    0x80400c02c10700c540038000ca6000410f8035141051aa41015805080603004404120042c9200f036245001e10480c0c081c4075540202403c255035150481203400c43e1004d10300c2c808048402e03024011203a440a088a400000901d41103864900035906141804243d078840810b140c0001039505400360056001c210500080002c1c650b561380e628400d0361514001c2d0007a609000107012104040000c0e00c00481d0055024412501c03a080b540d030701d1801003038007a04000c4c221040c42040082d0492a0041140500030940d400d402c91008005040c440d4000a40700920441c03c0182c840c080505c1c0c91b07090310080900c00c02d4440641d80c2c1c0d9801a4070740c1070070b8400d00da600400c2c1c00003044030706002044480c82040481503c0c80c020401034404020328980192004054039007011001040b240f80c81d040c40103000c2c080220508542c00841480c00ea200916101404000c0c8001c50150383c000c50603950094040902044c0741da104141c203801e0807051070a035540a1408104510400c402400391407041482507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364911951 1250 364910701 364910731
    0x80f091e03010f090f030f05130906030501050723030901141306050c0901020d03240e0702070603060b0a050703021e0c03070b0c0705060f0f04060f200c010e1f08 71
    0x2100641c241e9404050180c0100170040c24100040c1c07055880e8120b000e95481d045051004000070706620b0412a40540e00e1103483c0c84080c024401e0030311074550070800c2401c00e1a00341124a02d00d800c2910032303050316050180040700040f140002034100100700380842e101c0318003610701001a0710100e207084105450003494a07000840f50a0000111221440c05800030b203c4100300300001c602406102c10b5040a9211000d00d407081c040c12410120061b11301c1220b03000007481d140b01e00916110f1140d20600800d810090200862020241101c2458149140140d034613103403420181d190104507190740740340c002d09481c039207030301c10300425103c188540840981e41100c4e42e0b5044181140100d0903180b4054100803c104203614090008010913140d8400d400c0c1000c0b82103204440d01c1e0070603801400803d1202c080703684400c0e0b00c00040b4a40002042c1c0010350250400900d40e40c13030401074445814040700701c080210703e564180c0b0f882511003400140c42d4612001c0b0f18010182001038681201e401016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364913201 1250 364911951 364911971
    0x6030c180901081e120d0603151b0e0415030b0603070902120a05040c0909031205011710110903010912020f0304030f0f0212160f080d0804080f091e0301 67
    0xd00203040f218083c1c02065180e0410083c16000c0c00d05800a851070f100303018400404140314400780c0300310308074000e0010340d00d4030f0f504041c005040b40f0201c4400080ca8420030046607003100750204240d0b0131a24045050b803608002180042503107e0340c072040c1081850300002041a1040410b02c603041c20740503190b400c2d41d10131196060b801904030760540220a900015814031295000551090040c101c0e2480550750300f007084100d90140b80250001030516001c54004c210758000e550050183d5151068800b11481180385c94900c03440d01c034030145465502100401703500409545c03016100400800c094141440c00a000c81c9907000c2e500094003c496515900b4032011084d101100d80245961203140710907078500c04010030310710040382d0101b00780703440c82c4011b00100030842c201140080741507815410b0501015459066900c09005176000450400303c0c554401d00180e085903000c401a526505040454006401050340641d00483c0c40c91030a0a810003a8440c0c00f51032078150b0007002000c1c42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364914451 1250 364913201 364913209
    0x3181f15030b01050f01020a0209070309050705010e0d12090b0406090305010f06030515250206090c060423060403061401140d030e0d0204090b1003050f0c090412020c06030c18 77
    0x58403016004640482c0104071a090450b071002e40d1807014415075101c0c03011036001910144094543d40d0010b40d0f100e011308200701c1c080080303101400c42400c00c40110407500c800208204002c49004000c038031039207004003250340102d644002400748614007503126511604001c1c5951910f00c0140c0d0079600708206003601e00c00a00c2041c0c1503036040406000d08810340d9821001d02100a0841d0000c0d03918800d1103085400010454040001541e020781480d04206040c83e07c0d1100e032020301841050b080208008042c807480768883c4000c40b00c401612016001000180d00b80030300c0c3c0c40981400d08042900001d001c4118509050302c052101c02d9002c52501000d000400d010284002c0c0840c0039001400294902403920003080340c130080c00820004111707a1070016024054425826002480c8418020803034103010300d18400410400400071004003000003040100c0240000d843e8644441c40c90713060f24800e00004516400103840d41d552030403e9248054140c2c0080521140078a400d140c1c0725403454 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364915701 1250 364914451 364914491
    0x80109020406050405100216030b0411010f1d13111e070201050405091504060308041a120609060a080102040f03151a01110a02130906140f04030503181f 67
    0x203015900c3c1400c150601060025080c2e5421020041d80300740c000e02d1000101c65a4800c0142d40700e880100b440d400c203490400380c9480c0c8141d10b507040c090086076074100241d0200e0714814400320f00c61113111210030080494011103040400c80e0b269400d00301100806404500103201c0c0d01c4a24110340880785484a00c000c40713024900009000803000c010400c03030751414154454201c4e0074403020340d03500038101740041c08a940503402190300100108080249081140e1520240c80250901c3c600c2c1c1030004d4603461401c0c1c5d00500343ca04c105061400b144442d11040400005031001400856860b525910395610000042c031040700c2202e04601000da4074140c6004201040112a00b405000b401d60001924410840e404803141841000030309009a41c400680781104040329038006804846400c00d501541c101080c000009070b0900b040c0420017004c5100c146e40150140b0f021500c0340c0380d841881c075442c0c42032102c809051142d800503c2c10868050780341ca69070309025104203c8120300d6034902a0309a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364916951 1250 364915701 364915709
    0xc050f070303020c0a08062a0a020f101a150c03070302070e0601170f06010203160308010f080c010c030c03022109010305091218060d230906150d060b030601080d0801090204 76
    0x140140008c11001c00040c0080401420758011581d56040205580d52198020021a00050740b0400c110020860148000400302008142c00c1c84045c1e0201c00751241c0103a5144201c1c055542e149042200782411000d84164800e4101540e40c3c0d0704d03503810020354419041c090784604c0500300011480543c015803030100c0900a80c882c00100d0381e0707440716402903044001d0109055000c01c2000d101c20344110f402c2c1c4c000745446a1900681541481095048141960000e100b0707a07000b4070a00b12503a07085000300309020790614007034146c408607150481c00c3c03c0714503654032141c50040010a280740342140241c21083e00a030b80c204001d66951403003079610a076020748072009081c20000c68130721402803521740d5a4508064071251802d00c04c41110745c00c8405100340201381c0c5011507450105c0c0801400e900d90008d501c44000c0c069410b00544207106070101c11805886020032660060404c601074103e44281d15008054940645e03544400d50744524804107801c00084040c0004134080803d4400e8609071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364918201 1250 364916951 364916953
    0x5070c0204150314070821070b07110109080904050a06230406030803130212030703140d230a0b011419090902040801020702010f0201050601120b010c050f070303020c0a08 75
    0x944100d409000040032180c00003481c215841002201081d01c1081078840204c0300802044010316088419040440140f41e00b024504200c0d100301c40304030020f054078840d5030000c200001585030304205442c2604107014400b500e50a003024001032094000160809003000e503018000d90761129000c1003142c243e40030340085a10ac1c131126100d210a9081c081d000762030090000580c050300c07600c1f0304ca802d40044448200c406050240b140031800c01410706440c00b502c190040d0b01702942c82d60302400a4051055494440d4004110a411054181c0007106000e00012840998158004103004070070000c43d2001c034040d041c240110300c0755119502a260303c1d520308524904103c1111a602441c50205905c40d08200e1203040110f80480300340700400041c01d20a00050b901c0c1098400946051200d0007105e0641e403400c0d040201c81d90b000000d00422441b40c00d00019a003041d4401a2080c2c014488040e0052107aaa1039103051080026001c2c107607030094080303920b1400440d0030000311010354020b02c030071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364919451 1250 364918201 364918217
    0x7063c0b2709010f1805121903020d0b0409050706080105030708030301174803190204110d090204050c0703050a08130f030c1a150d0602070614010801050a0507 70
    0xc00c00e424440142c104100c00700103e46800b00c1c40d030304000e0b00c1a4111020324460341c00780e50f00411404002541c14a00249600c50800b000224000c104824010001c400c0c55000a00e14a905032203903c88049803000500410070a046401c02d1a651503207400f40c500416240000494079180009840381103501c1030340150314580c00e005030200c1800c01c0e00c4030009580f00b003017a01b0000c6180c2015181c03443d14840041031046c00c040c5c0207420b068103103400b101c11102c044a40c010341c0c1d0701d000c25500c002c41042600456146100d02c085002420381441c1051001d50100c0c041c0f80c1c100d480e40000410900807141440035889166280843d0f20034828001d010038010402070b0f103120b000700f46040c3d121071004a0a02651000d88521101b5540c103a01100003800c0d401420701042404d070001d0304400c0303104504240c2480c1282c0c200101c600c1d40340a65104800f025448800c01050790101e0309080d80c80a8140141c1c050390039185080b040030f0103401c440f9402e04001481c9544075104d03003482000c041c1e59480c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364920701 1250 364919451 364919509
    0x9010b040f091e020408030a0206070f170601021c0905040e070f060c11031c1d0102030d0e0f0d0e030d080618060d0218010503010c02070b07063c0b 65
    0x200503e41d040041c03115061181c00301801d100c00d44040c200400c8200091940c07500301360740090622000030626030501500d40004ca5880d540500300c0c040002914007842010348039000145d24288900005241082c00c0002106000b684000803600f29942136405002811000a030301e500d0b00e0381405880d13800200080c0c108103030fa00c81c111250401d030140710303503802c07a1035003c020905040400d00b03191038400030b03424611744180d4040310901a03882030030308905c01001d0900c0000d45900c601a50060020380b255005000100c040c00708232624040482110030414007003401130038a40400610a109020300552042e0003400b81c40140d200d200014003044a01038428051031b010a405000030b0b4104082e44070010040e01c55201540080c54038a01d001f9180d0316060400d420340750000c07910300c11900034200c10000642c808040c0d03015140d10440c00300f46004409103414031160740c00c3d420102c0c0c4402c030035040d00d0820a410991040c1c0910380040c0007024401c000d10010400511003100305e000480e400b02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364921951 1250 364920701 364920719
    0x1215010f02063702040906050a090b0307030206131e0602010e0d050301060c03210516050c030306040c21050709050109080c0d0c1d1015050703210608060609010b040f 73
    0x400c100c050554851100700c0d040c03c3e03c1d04980094000701004d03680d40310144520f02d02207000c1802007091304000d10000b0240c4d00441d484102510000b40200d2010945140c00084440c4545c06007400030303c240380c00d0019114020b421030180c89010055443c0c48a44150814045515002c07048580c4030149103910f070035001c4484c8004104150b040000810400a00f01e0302d2206402400c481c601c001300343c605001000442c0d54808042c07000900604009400400c038002c415aa030001d41203900141403400c1500588440c2040d03042c2d980d08408000030000d101201d6031141d409580ca558035502c45985520040d030790508035000307090450f0703c513a5003040381d49402c0c00f11410003440307466001501590380c8819008121410307103034a650082c03442045001030f21507c0740002402c055803295204494083c010f030035440381f40384c050b041202c0b11548665541d98489015911040e80004012803961224095200c101c00c0e1261885826901c00014103040d1300401d480690711110010160300d89440d02030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364923201 1250 364921951 364922011
    0x30090807062412150608160e150402090d08030117010b09010e01030b09010f020f0424090506031e0403050309010c3009080409060326071104021215010f0206 69
    0x201c4001e0122030646644d0754140c0191401490894001c183c003000310601500700c5100742e08660003003214941080222141405a10741d0385200361401a555825100400c06500e40c07180c018000000000c0001296000a00d00c2c0e011280e603003008100d0030100c4c0c1c00300840020280314042c02160000014000b00e21641c1803d500020110000a85e43d58501c40d101c081e600442d1b41c0079040107000c42c04000100c01c01003440300440c0802c45080080280c0c0e0005030504809010751402140040001500f040424104070410560407080a0345881c26141c000c0980e8005c40f800c5c6815400d102101d10003e01501401d050491042d8284d1005000d884015051031100404291102d84903001c40c03000c02c455000400107081c0b06103010807110304504150a0711003541e104000380c0c204181170050820690b1050b42d8003c0e500a80d0315040843c184001400380c081d00e03403110b90300c004107014400a41201030481d000d8103001c4e00c90341c2410061600c180e840b144121840c001c1810000845e108101d04000c0c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364924451 1250 364923201 364923203
    0x12030c101107051f06080102030f040f0302150109091703091b04060b0c030c0c010c080403030804020f060d0c080a0b0d060b0d05030309010b040f0c30090807062412 72
    0xe80341c180210741c0c0f81e1914001c00ba154405000110030305019510185000d8000074002c400029459030a068000c03844490b0000c0001d800c00788070200c2c181c201842032001c0042101e154640707015a5844115801c0180003e00c02140c1240c0d0f02400008011401e0703090700d221b06401c201400c0200c5050154101c25480c0041040e030007130350340402147d18007090000e00700903020100151b40701c2c0d107040c00f0945070036009480c8074103004005904030000342c0600110380507030b58145440011501c551001c9502c884036401c004d60701503c0032030406440c112660140d60080190780e10702d81c241c0c46554803030088408600f8901e41100341c0107407000c04145285c1007020000005845582d240030385071500d0382580c0095032102c0c00c99460314080d6400f860b140c0640050103001c40c404000c50454101c0142c4481011203007000101e42081c55000c44058401130700c03500310102e200c14000c050003468064029480503504a41c020720704006a2207081401da9029000d440d50b5000350070050406005400401007400c2c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364925701 1250 364924451 364924481
    0x20909011b03050402030d08010b04060c0305190314060603010518100801020c0f01110f0720030d020f1605090105211c0f0815060a051306090512030c10 67
    0x2010780070038285200544603605680019840c201031040509004a030000403003080030312001070100b4040541110121505814856240d4415107426580e50044036108411140c00e0007802e2100ca0b055080040007001005201e012076a03640200060b500080c09920340245150101c2801d50744000301207500320628214543d00036039a01c00e01d509a078400024503003d50000c4c1c02065000400340145500c46604c14021400d20760130110f002c415029400010304240d070458866125080c9120400020301030244c10741e41013007002c503c0a5036803044000c200d80d189c0718a00d25180a00200402541038500040002c5c04c1b03030f440c000411041c410380300c14080c0070007000000100c200c10300700942003860b4019030003900490f00000001c1c5c0100d4400c440001441144804c104014000244007120280110744858444a4041085916008612650b49450084a008030b80150040c080303c040307a030200c45d44d6054003a0304191a80704e005583c80c80f452580035a045441d00c4110f90000312442d24501d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364926951 1250 364925701 364925711
    0x204060305070f0e07031a040b0f0d2001230a051605010b15070f060513050114101a0a1b061505090a0204060e121f0e0705040b03030702090901 63
    0x1403038450912840c0d0303004244080d0f07420f0f0108408001100081d5002e403042c1402c001c06800300301842e840780c001c0100301d8403d650303c0e00114006e03600c100034800c180d032001d801c0c280706003442c6c42c04585003501e03614440d4041100101036034081d84506040881190a103a407410725240105607010650803444459040c80418040300b040d49580c0f8807030240c810701510011891111100070b00100b4580c240070b00e840070804001c25408102e1400f402e8210a6200364001a03540d00ca441c0c0565070b00001c0ca00a0a9500302035903801000390201c015030047da850007406440907070b80c10030b00040c1191100400c158220130700c07105000c01d0007082c54652002040039590718800c00355980318112440881102159180402c027480b5038200840b41c154000003400c421444d09c1d003407410181c50100d150606521071028000e080c1c0f0141e806000100090403030041c0c40803c05010b880700d0b006068000c8248075603106421340003c0602e09801b4800e015140980a545010026024841c90100c0207011408940d212 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364928057 1106 364926951 364926953
    0x405091303030b060706090c080a0506040620120406060b13030b040203010b032a04090b18010e07081e0304150f0e030607090e0702060f0c0702040603 66
    0x220392184100440303450100d015141c62000d26070807900102d104810004180c0054102d60f00c101d0030910f4050700d40c40a2661061010340203085a4882804a0041229640100c0701c40c01807002d401410368601110b040140e202d0a181d00d541580c1d0010401406154420f240103800170175002c61602c07481503030f100007d003901c0c04054100d012601c049030444da0254080d5652510103001e850f00f0f804031117081204451250200000c110f03900460131a03902c1c1a10450300820b5202c0b03040070068890307011195102d8500c1040c050b4641d84c0707a40401c00203074104201e070002c1038140005c1002e201c00c1c00c0464400b51421680380c1d25940140818403080c0d510f00101086046039203030200040480b1a4100e800300c02c0c107001c071501070103007070140120350341d00809120940350034103040160340e112808202d07611402120380d421445a80c002213050900f240c0b00038903c03140020400305040381c403 = true := by decide +kernel

theorem cover : BRFrame.Cov 364748201 364928057 := by
  have h0 := BRFrame.cov_init 364748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364748201 ≤ n) (h2 : n < 364928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
