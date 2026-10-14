-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:21.86432+00:00
-- url     : https://prove2.me/submissions/37988a58-eed2-4385-9089-a26b07bd3e23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558992805 ≤ n < 559172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558994055 1250 558992805 558992857
    0x1030c020106030602070b0108010e0d08220b0420030313121a0f0402010f05030618190c080402120307080706090503120a020714010605030c120304080106120b010f0605 74
    0x20002c0e07040204a0f074400151031090000100c8654100c0d00603900a1100d440c00100c20b075240c04c1131401e9003000c04c10300404160700c1c00300c3c0b102d180544800117044009814040e11181c28026050754159003103240c800800c0c01c0424116170010344400164010342c40c00f5994030440c10310b51824440c86005c1101d0440040070408024031030305408000301a14130941c01d16010280007800290340c04c9000c5004911821400303400b540a8902c142401884c0c80c0d40e0014505840380d0240d030042c06001620750310301510f80d1000c0a44103101e0100070f02d84c0d400800e46054810f0082154681120f0903c0ba07106000d01400681108121805550b2201c8045141c44c243d01e4818034500410700304c403951244110401c42c0300842c560251201c24082c00c0d001c91000341d0400024200d614a000303c40d019009a100a03103282410b0b001e0001103101001280d1030140d03102c52660031240306030041c80040c240d1001e4001400031019605014100d406006506185040303405031031403040d5031281c900906100340d50344000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558995305 1250 558994055 558994061
    0x702032b0f02040806191506110c03030c0115080708190305090307060c02181504021305090c090307060e0906131808090315010b18120d050d0b0405130201030c0201 72
    0x700c0322900d05540715501c0d002425115082194040010130350060401d564800c207000301c00f060782941852003010384c00c1550448207c2c4803441e22100034480c0f60302c3c900b07880d28104010000c40c6100300c000111201042030707082001a4690140c403180e80b0000c1d0902042030b011401004100b120b420202d4001c4044c074095030075029000c11180d06000e40d82000a0460700083d21031581c1c0d1007100e08841c0d4440126606c014a081501c44c040c907840080e610415505060f4001d01040b102e0910002c1819582c100140b02d408044880030b00f0144045008401414104007000141c5141d00300003c40380040c401246c0d14500007042c080c8285100c1c21a0310a8401e40e50010090354003440143c104448103062004ca154403489400b800780c400c06003e110541214402681079500d01010149444149140c0800310020317040d4032035125903840d65610188a00300060aa2440c0c2504d03519101c440c603003078440482e081e5071050f40c041c1e803c0108202c04031801020103e0610350900740004c442038203407012401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558996555 1250 558995305 558995321
    0x41502060c0313231f0207030e220f0c0305180a080a0c080c0106080d03110d0f23040c0501110303040f0305190c0611070314030406020d0c0806090702032b 68
    0x14280c4909130048488808152110030f41202d101050718440071240035000c902c01d8000c0a4001201c00d41d0383c00482c0391102080d590004402c03a0740b9103914040700702c0303403c552401480c00806560303002007000c200d07054040d0301c0c0c0c040c003050b640019460514100c16190606254000c013214800500340500c81c0c0a40070058030315800000d8180c1700d000440c0094006c040741d01581801d41714501d9001c2c4040e111340030768028075900c06440c0b410042c021100c0005405000c1d40d9550440d1207000c964868a406140308401180a20b424081400c0030b00f4046540f00c1507800580c10400100312080c80c070b00001049030b4000e60b2244610074208414141101c086c003071078885140f5250b0884011302c0441d8004410b416070b50041e0001c0201c800ea56080300c51522450390010045500702241c4100300c1e0061700034560140c002c02001d890001a02c82c4501140c10040b007078000318100f88203103c074500701124415400f0699000a518291050b685012034030480c0e40303600b841309450b05110595024a800a005c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558997805 1250 558996555 558996593
    0x8030919050f1e030406050d0608150109050903180108041406011518062708150405010c0906140a110f030307021002030c0d0f1e02041502060c0313 65
    0x1005a2091500c1510346802c0c592882e0a4420000301440e0b45810355150a26818164000c2d4a018030340308095640c0e41041000404070303952183c0000e5400720901605004020344030244c4034540c10107420700101e91020704400303a1640f00f13010061800b4400030b07013100b40c0f41003400c1409032030340c4528040c020f13210108800d46c1d450007440f00024241c0910044030744422410b44501c0e001e00e0100540381817240b16032142c5000a0840081460721480710310790384035410a10f55035040381d80e84440c4240e10780002e80c1071a0020054920803c01400750a00c00c038025a40c0e00d10308005aa4a0b0260003405812060541c4000d280c0000e2003054440c041d1043c600c3c81070b062815034a01c0301c84900b031030384c4a4004449110244c00b44441c120300354371203442121701ca45615010303e4205400703002540000c103078443c008007600d5622448410600440044400044000e035401b40c1e07074504000107520b68400d80b00100d030a55104509200c0319106203402d883d40984007000003855440c0b01d040058406108003403010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558999055 1250 558997805 558997843
    0x91716033801140d020a05060903120f030411061903150302041409012a0f05040905190b010c02060301051e12030306101707030f06090f0b032107080309 67
    0x1203010203441c03020604036400214a96900120201031010300400d10000035400943c2c61030900003441c3c07560142074070392400340440303003010b92408800c502c0768011080040d4803240442003104000802e458001c3c3e5481c20784140781011404032544640300400341009041c9900c0d104107481024000940320f004680013042131100320701108141c401c113030066810000a5091440385d00c0d44100e05c00d50b000c030075000c800d100c9514440c80300c0d003152403220300c225503820032508100c0000c40f054a802950b000744411801d41c1d60403610010702d90708450021420034140300d1250301e070b4005603492609803811208140c44100b003202c040c00b50185d1f00d105140e80c04d40d0003011003c000100500010107944210303419110064050034181050f81d20908407059001c00c80215000109402d1082c1c2101c032190148084c08560141c683c1c0400007503500e1094a010280e0390307107100d0b620340c0c0750800480d00043d0000e0640200081a84021030542c811998041c0c27864000002281030103000f0010b0450303511810841d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559000305 1250 558999055 558999143
    0x1707112d0111030103060b0603130f08041518090b030a140a080307091701090807020d020d1509030305420a030605010e1602070512030c010c09171603 66
    0xa0b0711250401e02040e41d0341e520308201c590680c10428102c07401010a01e0080040e0385150b5501d8131a0080c41e08100c0705120240400596810613030041000c0c00b449486036042002d071209814480d101503801900c00f1418484040e04680b8041800e80c503554100382210300d08440707142030368907050f001e0b030380201110000410028100d90040c0c030403042d5051240e41003064044044400e081e2500b80304040d100c5501080003800520348031070301424048c401741c0014190501500c0c0c40020a5120f8109814251604000d0b810540d1504c86d4951019103043d07154254811941482021041e80e4513401015540b070031000445c1580d16980c100d0100000c080d00e40640e168038042000e01428460800c00d200d1080101e0b5070451107001c0072034002010f0340202221850013003040307600c155120034420280002c005501c40041d0038000c400705c01d1280e407142c802079460b091203404040505802c148480c4c0180070f0601c0d51f040b2000a440489410103422000d07081e142e0340c2d90100300d07440551040501640840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559001555 1250 559000305 559000331
    0x509060417030910030b03060c071505090f01140405070b0f04080109060b01030c0f1d0a1a09100503011a03060609030a030903031211041205010e06071707112d01 71
    0x100f00601c0c06442c03542d1100913001c401d40c21b40b02122400356042c0c01010020700c0000d8884040c100032402035964000c89000f00e1051411030382e0036100c040207030304410700464501000f4041d00591803002c2071001e0f4a4582502c800e40c84e495140220721140200003000c0c8009944803040d0b402508068000700500140d5182c800014600701a203c3e0100f81000383c0103032082c1c0240d560440c141c00c561030315001500b02e0101c240d8410301d956490b951210f00d00801098100340610f0b2882c2c0301c41d00c00d002070340d11040c040800027a420721810034000c0180c03c00041c00508448100d050740145a201c0807a240e4035004c0001e00035004118030203806103d410030241c01d041c2d020000c1c03012a0b0094817036480c103103411410f46050f54041e102c0303c407a104d400c03c02040003041099003801d0306409030f800012100000308946061410548907400051602180619151025020a50081140d09248803812500c081c0c0d81d0f200c1c594602409400b89011280c61049191407275035445151100c1c0080103000d40d0014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559002805 1250 559001555 559001557
    0x50606071e020a0f150e031f0f110306030d0305041e080d140105060708070f060212100509040b040605090a3c08070b040c1d040311011407050906041703 67
    0x10706038403400c1014400250b900c5130540800540300e00d034070003004045805001769641c03062248002e030140f003044030030020b40e51040e1450220342d10200d00421208500d0000005442c25805012008401002401110b03900050820310f0b1162500340031485960300d0800c405008078280c04860901c2c0095030501c04c00460100400d207882c0403020030010592460b4140060050900a05410000400801d008130f6454006071087c20f00c14516607c21308521b035555170998120251011250700d00c1010b000b80c6402480844003c2e04058506100d00d140ca6202c0c8140070304c01901c060b22591b07440340881d510001c24061491102d0308084224164400240341d040c002c4010a940d1030711114001c04000d462a0411104c10721035005210641000055210042d5000000e4800c49a51200180000e8104214601c52051200365180c10314a45403608020b801200e44400784000e5074500000302a03046086d40b00140c2082143c90695120a0ba405c0800c40c40d220390340224128558000c2c0d1841101c1c4004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559004055 1250 559002805 559002863
    0x140c070302010c021c031a0402040902120112150c030f1b093f06230114180c120a0b030d02060106140a090e0f0109200301030605060607 60
    0x1d0300070020340c1803030380080f61a280700da0300400160400b4010340c044284290415074182c00c01580a480010400780050100da02951000007215004502e180f01040e035600740e180100b28620702d64900d84910740d84c002000c2c05045103640800c1d41c6034030b0160150300c07a034420f203c0e400d5100c0c0300300045114000e044100f802008864000610510f07400700c0d17242c000034411402c82620a5240003048150b000f0260882111425500500380c1e0400f1035001c100e107802541507201210b0303498401800c03603040c3d80503103800580041172040b1000c8000348094496480d0360203014025074458500d615805118506c902c101404925220300b1002840b440300e5881d4065550309100700e040700ca90b0031000106a803035400910480d8003060440401e18100350240c0003c0030b40c41e01e64a0514200b40d15004841c42c0b184056480902444072040103004040e43c0d03100d000c03200d401e6807024090601128800d80590f1105000c010311031502c42e40811401d842e450241c0e10f45070750200c4041044a0000d03140b05600c4110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559005305 1250 559004055 559004057
    0x405040f0501170f0a02060901030e070b0433080919140714010f08060105070206040305030910020c1e0d0501050115030b010314040f03140a020304050f030304140d06140c0703 77
    0x300c101c804183c000050303400c190100c02e5002d004402c0d05c036001c01110b5044140388a060507110161003003501c3d07040c05500058442504003d4440341811070f1440c02d007614201809150300f1071080d030403e480d03158030140f000c01c0442c40e0240d101d58501707030b10301d04003121400e1740241e040080c0881800c00c500c1c0d2070340010180384842140c02c01e5544550024400c1c4404510902040301412038240441c82810b0499200350f040c104036186c625980d0202d030140d0300c603500a0b00c40ba0408039101c000c034600544054000c032035a00c0209030442410002a94207139120071a001d1000c5000c500445030b44401c40303040d0300e458101c0d008000661b5a40411848031620780698400a0b103402c025009541c001c2c815589500e07041009494641d4440e03071410300c81602c954064003840800000e07040c0c10034049009190038000f42d4041d680f694601400e0046a41ca1002e1491090300140000d000c0040c1100c3d130b44890200c11124280c0c82085418414000c100c02030b4030070382c4100c0704030800c00106420310040c95080c1c0300e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559006555 1250 559005305 559005329
    0x100801050a02090109120302032703010506010c05100218130c09170a02060a020c0a03060b0a0b0f0d05061c05010519050403021b0612010f03050f061303140405040f0501 74
    0x10707402100100c1c841c20640c1c0e4003050300054180b20b0080f20100301d40120f4441c1c0122841c0c1000340d400801d003d12207054002c0034455110812151f03003030070700030715030849400e00305410000c146a0710756407221031b600c07881d01c01658042041000d10100c2241b40d80b10340c002400800c501c0004080303040180140c204901c011400051002620981d01e40100039603030414005040c0300102c076400c0150383d62240d1040c01c2148100034404a00c0d0f030300c0004090081d40302c1d03540024038024000600030404186d40c410400e0100900100d4411002c00d002c46500c01d24409001a40b07a8540c000501100403524200c400e41009601c00410003405520540c01030403074403925240d103005111035200740d641c2103c000300140c2000c20b154024803240070060303500f4640200600e06003804a03841491a0000341c2c0301c080c0d013800b524000c00501406100b00c00d1050170000140469103010240300301e100145c40802010406044a20300203003444005950145c907004100741b0003025800f0061000e0682070080c500f034990 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559007805 1250 559006555 559006561
    0x100b040801051512120d0f182303030f090f030c010204050f040c050a0e01091809060e03130e040503190810050613030303150e190b0102071206020a1710080105 70
    0x50002c044041060414004085100e51100c0c458803035008101002c10132612001f62001c2a034036405054545041055105154501400c080d454643c00105a550f00c0310f00404461942c840482202c0d0b0040c50000d0b28105525081c40c0704c1c0c03400c0d030f100300ba10316103000108000440e08010f40040046441c1100d214402c80c01d014100002c031121180d0b51000300300c0401080d0003150080f809688105414146101003659078103480c0707450f90b0800d00300c82e5260703915503809040140510601c500d400300d0340002c5080020221a010500000e070260499401c50300c1d00003020010300300300300d4240111504041d202e010080402811070038040d900401801030102c0b011034141000c80580c0c201c2c454408c042050741d40f03540c6040e80100050240504100944003010600540c004200c0740140807059002c040b000a03101098202c0b194403c049045420031360082055884005240300c0e001e410a90059a07800d8006c015160244d5128082c094000c240c020040480f00180345130b0b084846000c0240b000d55 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559009055 1250 559007805 559007809
    0x70506330105181f1701090b06040303111f06030519050303010902090d020603010605120c090a090b0d02040c05090103060914181212042d020603100b0408010515 71
    0x411080c1955001420034040c0c602c00d01e5410010342c01d0780c40080c2446a64110303000b40310304101c448000356004100b62408400d0b20000c1c541d66140145018141000002269000100244290700c00601080260711002140398000e1041b0107290b190301064071804480a050700d40030b8401840182c41c01d0280c00176110084900b215010f000980c00400303545107a0a000116001390000d5070100c3d08140032000300342c0141c0300c5100450181c0055103c0030746a00080c9440314001c58000c042e204180e2050204248685130300040c48103407101070724003181240819020404060a03601c010394070500f06180c0002c0c56404c200244541042aa010700c503c2d42c9595209043e1200701c0c00e032407a1904d901c0006403400385e224081e50101d4044406440302d41c280b007205140305400001151141410b9030060004024111404841c0c48a0030301c02050b000e45041c865002405072410045c0c001c680010014158804080301400502460200b043c2c5aa0b290342246000700310031201d240b9001c030842140040740c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559010305 1250 559009055 559009141
    0x304030f3e0f0d060e030c0f07091803080609041104022802011514010504180b040b0a2114030c0a05070e04020a03032a0305090414010f050d08070506 66
    0x242c10141c2000d50014955503031400404210001184600050090319082c04c024003624545040013030051642c581811081e40858500714040002086000300901c0001d801c03011255100404031100b015540c0c076824002c0c8000c102c4030455074050303c0000c4010300d4200b1640da058a480756000c0c180744242128000b642292900d00d00260100c00390401003040c448913a00301001404185022401d10b5500c69100050360444a281c02c4140e85814980e5070a04003840703a10701110302140c12040d024502070561380803000005100c91075175405842d110a1040d51407000c0f06403103591003102e0b43d030241400069222840d082084803240030304400050001218540103025680040280126a185990070f507100f200034801b00103000b003400c10350f4000a4100c3c4000310031901944607180d5a034082c400300800c444e64281c110a8103030782000103000b51520b00000000b82e441c155912000f001c00f50808003028000d0700001402489641d0801c030500d6080502280a102d28283c00981070655942c00c92003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559011555 1250 559010305 559010329
    0x102030a06061409060d0b030712170304110103020310030803150f04060311010f020a0c030b180d02030a1404030501051f09050105180717040507180b030304030f3e 72
    0x3d80e1014000c0c0191490900010540c480c0f00c00c80011b01c1c1c10440d00444d080002a6125054420760061030805200842916034800003003420481d14500d002d0342c1d5074230f1040b40441d510b41015408400a039003040c8213407051000c0e50300518120f0b12803138081c051440071540410781c10300408103102c804001707080a0040071309403540701c0203854002403032100458441c0e82c0120124114480c420326107003c40d0030007440e2005140903c08101903031074585041c203000c5103c164011781c0f075401408000101907003c8180c8140c130109280036140c001051070380c0c1c9514021070700040c0c101d500c2c1130140851824510310138414017900b80e070031581c4076a88020890881d00d00744501508501a8528884000c1c0b0a503401c551001c0f050510703080051050641458081c3c0480b4203d030580d00c01c5030240502e02a008103642001c0c1500414031000f4a1500481e03181c6c082c0c0e00c00203011100c1c80c0c40e0601042450b0144000022120030b10100350500c800000380c150064000320354050028401110300c41c20f24080f2244 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559012805 1250 559011555 559011587
    0x70b0c010b190302060906070b091c1b150207150c0318050a020f040e01020316091203120e01270c050103110711030f0f010e060f010302150309010912020102030a0606 73
    0x99101c0c50354081c06141c0d400380403182d47c09007040250764009040c1610740b600a8081000804151600b1112101c040e10300e100458280109400f100f6070802041900200480d0310262440e205624880d070342c0041e0081c5000200b0082290303503000b000f0040c9a018104513881564244000e1080d1072194040c24000400504150003803e808000360403d030f030b050100905c001d000042d484240d524035508a0304107856540200a5030a201d58915902541c290042d108001c00101103140d04c0c0c2c2c1c05804010841a8812600e86035035007826680000e500c040d208084044008003142c9005500030300f2511700d00012100d48014030004903042d482442400b9110020004251920209807507010242c4d5204809030340c50300c03802158805085042c0b0506800321401e01c00882c03070720010b0000909003240101400a4171185400400150b40d5a20041d00d802000800c02c542d40d440e000c00440c05040c0201000c0c2620000c1d203094010f0a85c154001d41c4603000900c1d0400c511500d07032000f100d070420346a4001d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559014055 1250 559012805 559012849
    0x1b05010305041e0f0b01090f0b030309010225030c0303110f1513050c150403170c122206120c180513201201080d090e0402060903070b0c010b 62
    0x80001d0f0045080302c101d03010304482c001040740c0d60340344c4050f04400d03000701c0071058584a45a50b12601400b901610300c03400c4002e14144001000000d42d1500d048441b4448420781144003081c89210b103003404051500302400e10401510307400c018000e5180405076105a200f0b58400814140c004124918060a103080d040119145c014169040e25031080069032580502501c0071103981ea54410600c003211060409a01ea40c91400c085804400741d454801d2040c1003004621101d050114003101a06203048480741c44502251000c0300f15840ea0982000e2800100f201058254108100d424044400c3ca41488003000c0710a0440702150f0b00d504501060084000902c1541b80c04c054a100d072041c2910001070185a0381c51103c0a0111061030410304080041d006045801d2500e806014001a0b80188104800c0d140c004010401d688150b20314071020801260866035081b00700d902c0803030300034102c5055585a1407140115803103036400583d998a00b9480d0308050601e03134044034240d42120120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559015305 1250 559014055 559014083
    0x512030a020a02090a0e0d0818160504051b040b070c080a0309090e15040c0914011406090406081f1a060712050f0f0301080106060503040f1401181b0501030504 70
    0x1c0500e041024011074501e549134001b42d802d240702048070300e148030129540d906c028113201e071802c07020702010058050150044043d164080200c1c0310708070121f0b00180e0300000d0741c0d03940718001c07200b084c8010300001c03e0030000100002e030f440a4002401440e800359440d09246680d44000507900d0403c168000d0104074545000c00c410728590b0b1041450034000b009644041c1140d0101e0844500b08a800f1205d55214074030030b11409009206140010049241940d840c0d410904070807402c40746a04054171546000805814071b455503040703400200502030450301d60000200104158038079096941103c0f903c1e140401c00d0030301d01d04c25403138461100500801e1800c0025240e240380c0d03006414071442030080420580755000c01c4400101502007101c02c000383c895060100071402d446044d40301d203041000030300c14013011851a079038100b80706512281c07a1045442c400d56140c090482030132840000c81541c01054180310103501021100c00169003200310150302d400054003203c205907030141c10f4200070071103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559016555 1250 559015305 559015309
    0x90501093203010f06120c080610091e230907120b150904050312071d0f03071a0a08061c030c0c0308070303470406030501050708010512030a020a02 65
    0x14019000c1c01c058004650715403244259019a040c0d070740040303001c812041864040c0f05400c0d0b0070102500360107020304000d06105695101e224180c1c010001c0c01a41d6108844d0090144184038200d601080d40074031902200355400b010000f51105d1010a0b42e1040c6d001400c407400101c3c03400b05a5040b918001d00c50429511895240d40000b882c02100c109980501d4504c1c2e03640c4e0240d40d200f94400d4000310b03540e01311958a24092003019121134248040c182c55804001c1c03051400080c0444140d41030b01242103041c000038601000d55003c0070034180e8030201841d0fa951808000d003030b04e8000da115108031352600000d0100035001c00140c0b00264120b680c1d808000b9106889116025000348481c00185403030341c0320a521540300d540202c0c0031a6460100c03000c0001d2403a07821982801d030918070f074260100c03203807290740420410044031000201d02c070f10170b0160354035540090061500500208024508036002030702e800800c0c015184590110000004008000000c6603015801640942899481982 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559017805 1250 559016555 559016639
    0x70303090614040302060309010b18040b04020409061518110909010e04031707020d09150807050903010906110406140f040603020d140f15030706141b0d09050109 71
    0x64507452008200303c00000342c0c0d5060051400750049600010390048001c04210143e80039100444006240300100000b060200307100561090b01035030041840e80c03c500e081c0c40104001d52000b501c1d450900c00c082a00d2219100c4000d071032469540401800f40c3c2001c025480340521035000b07610850030300044c81095062105150041d2003402e081c082884010007021410701c044275140010b038003c030801465140c2c00b0a0220080ca000385061250038040c20004000800082c02003052010008110300d86840035031000c03030410b400580810813114101034010095200b0302c224400540d1201d03107034900d00c154804445000710744045940c5410b1521405170041d401c02c0703508a204590714103411600aa0300c408892083c07898081c81422072800c071081848000c0e105403082d000343d01c508018440141c2002111090007151210b1703c1d1107641d00041c064291780410b5905845020310708040f1852034001d04400d0940d00240c035203520850312040c0d800c8c00084540000100c448600041a07a00c0c8840741c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559019055 1250 559017805 559017827
    0xe0d08160e06033c0f0c0a0816020f030a02010911060a02070e0415050414100e150c0d06061e030b0609040b04060b040807060318020d02132004090b030703030906 71
    0x1080c401c00d03000b081c00c603c1284d003000140401c0d9207069a802c000145025100b80d5030311034210070606007040b00c3c1c103d005140070801031070184034100b00941e84c6040d5001b005461080c1c01d900084a41c0c036212840000d018110605046906048558a42c806464601d007911071f006103a40c01002c00900c0d1160b0f0085010300500156140c01c2d4881c0710400348803039806182e00c243d000d0120944003081e01c850480c500711170094000c00451804800d0840e82d10b0109000c0524081c0b010103801a41b1a000d0840d0355201d001c44090031549030000c0040d02c0c9800c0003899203d510a40c07010046c2d00c501002c02d606886140340015400034041240900c1d41c079040e404840343c50009400001d440c0d03203d0842d5292a032141d00b080107142d00600f81000f000758140240c0c1030780030304070a61141800066001c10940e020000c0000e102d06520400c410124109500a003040742e1006140c40c0046a0000400200c4d8818000c00445504042c80e203002c9050014040d4212a41541c9086405241850172540d50141e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559020305 1250 559019055 559019101
    0x70f0f03110a050702121203060409060605180105010801080312041e1a190603050604260406090302150a1719020f0306090112051c030e0d08160e0603 66
    0x207a180740703401d200c030403000d02600d108680710103075264110700400c80740f40c1a503a017815166204011103c007541e0f05e0425aa0406004e460104080b012850414043c0105401c40394021140391000300c1d0310496206120304a40c1c00380c03503244040e601c40e18003580300c3c45840c05a42009200d032011600007090003501607000c1220300100d003e903c0c0c2c1681c607107181c958508542680450543c0c18004440c410200b050461691039404010080c91a070703806407201c2c00104081c00310850900000d80700c4084101040500800c03554003030342c81342c0b200e90243c0502603e000903400b8404013400d00500023601c03011104549000e0320380c001b804896104410880d4002007180c001e010705082a503011040500242c00620406940315440385031150074480c44900582c4000e0000ca151492031010810200d1801e810030521080441d031550007000030341c05000d1196911840340301c2e4000c80400c00e0b5100c0c05540c0a04001010704030350004603002160840d043e400c1e05580480d080000c81d010302071504610022501e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559021555 1250 559020305 559020311
    0x60f0324060b03100e0108010e0a02091003020909160b12060f0f0409200f0a09020703210902010305062d0a030c060503100902032202030f030d150e070f0f03 69
    0x568101c0704a54205071364808000c4030024080c01403889000b89503024004c210020000b100100145079664100340001074054901c40000c240c41c004150000c60185402400f404070505005003400da6440d609541c074821411020b90110b02c6020510449500ca03a0503048040704e9105c440c10002d0031445e00c40d0030760f407001e2170b1409001c0ca40c880780684c40d0000d00940500f07040072010305928151340c80702e0000510a04c0e0140c0900260f1355940b00040564104410060f190703a954501941c001444650000c5902c5890160110012080c2c0024494501c04c1e0f0301440b07140c681d8130030712454180048412040c44c52590400d000800c1241d1900b5198034000c2c00c0c04146641da03124184d00c100749400007030000b003002013001586a10407240c680202030302c1030118614a04140c40e80c1001d00d001711030388818840c0803503440665a007045088180c845030340c00d8980da0441c0d220110018511845802c0071750010800021381c000074000c2d11881011039468141000104250403900e8820b4602c1c0d540515075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559022805 1250 559021555 559021559
    0x1d0f010b0f030612010c02070f0b0c07062a06051608060a0605091c110108010608010e1b09041401050a0b07050607030c050c070f06090b03070c140c030619060f032406 73
    0x4d424002c81c0008111a00500a1941049520414481aa00203000da580c00300201c034442100040c4540454030a440c0c040c2d40030805603064150f800903c2c1d01d018070000c401b001c0f1002e202840d0f00c42c3d40640c81030160391600048032042a80c1c03000342240c8a5503c420340702002c0082601070401272224103001490b1500070607001c440050030318509402034807180c4030303223000051950300314001502404007070500400640c90156038007003c040050a0044c85201a0302038154140c0c228182ca81d200e10052050003a002c407112550166039091140070b10444c14001d001401511000c12107140c540c0200c0580101c6d5a801001d401512418100c841001010031160000c10b10901c407034000b138922040c0540c501498844020300c82d5403240c1180d85001c1c01001407089240d00aa601c2140c1c1d0703884461075588030b20a0421a0508080407031694050203600c080291001c0100501c040c0302c81607650410100f512a400009810b9007404000d10904610310031715501c4403403040b580d94500e44200c3c0450655 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559024055 1250 559022805 559022839
    0x80604050a0206130e0a020c010e0a05061b09060a0201050601031b0509060a1e080114060c15060105130e06030d1803030806040204050a0306050702010c020c0105040302040f0e06011d0f010b0f0306 86
    0x7000c00c0700c40c40052640811408d0300305c1c0080c0600109410b81e500100f4110300c0c25111213031a02c80181c8104000a502030055080305000000d68130940c0340104103a84a50003028040d020700b00440361180028581038500c0c10384040e0050070181110302d80c2c0c84a0806406005200c640ea01c400d4501c024070100126404851030400d0f40c0e0310740104660380c0c0c0b03042549421800031501500c3e04190b84661801e001c81860304400040c0b41100303a03400c0b0807000094032000010390b003a200e41134201c400100c1951000c1580385190510901a1005404680306040d6044040f46c0b150b0b460030088064044c1c031041000030900c20b101d0345801032802000140b5013076440c40091054000c42d401100e0054130340b0304200d096070302031040e00d04824450010700800482c20700003c0140c0700d60300000f8451a540c0c20301c6410801560f2115041e00c400700704503071040d41c44108107001ca0035030741071004007042d00c60005210130b00c1031118607040300c07282841c44e400c04050a00140c40c03500700402c0c403a00294a005226011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559025305 1250 559024055 559024079
    0x3060f0301020c070f09291323010f0b120702030c01180201030e16060f020312181b011b060902130f0b040915180b07090f080604050a020613 62
    0x2e401e010f8002d0441a28118211041c8883da13031201c18514a44681c00b0711003042c00c002152550350100c00f010f030f8201900c000410107008100c90b28060751806030030a100301c1200c0001d000c42a101d0410505980e030f01c1040410141003401806460081800741c43c42e803d0382c103a21560050600c7c0156410b003003801c1201405c41d80151001c00c1344000b40540602956018401c0240d000c00c1500a00350307014414243d0801a0f5541c403440c01004210b150b00b4914a209000742c17601c0e03696038000c480315401d01413010402c82402c541103000d10b02602c03054002c1c840725915116035249060310380841c4520346408201070f2002e140000c0d614544c03194594401613071071000040c41942c010307034005566882c3c4218032044415403484503005504e00100c0c1c03030100f14a5604120751726000301012842059052440d40e245119040c02000c8152100074894102d801c0700540054030000c2c0e030300e0508561b03210a401d41d40d650564000d0f185070400c11940b00542441c100504200c100081c030707941070b169600d43c60454 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559026555 1250 559025305 559025317
    0x4061416061d06070503070e0d0201020703080904020403060203040f051504030206190603052509062105070b12040510110d051503070824190f060506120703050c0a050f03060f030102 80
    0x45d41c0042000b1324182c1041c143c002d1803105981800801c06140d0020b9030712a40c3d800301a0041c2c00215801035259150b030121006554414010b6440742000d280c48522443c0506e000c0720b5030f014403190007190300148141d642c855074250340103245d00d440b0160b03031003490428110040066502c13407001001069080248190740d0040900385907042400100f503803a1881c15800800455043c50f0f4104030380c012b102c0701c0021072000032004240510789450001c0c50040d082c2d005103040303040416051504000b1007601c520582c018419144001e0701380a614044841144078a0030401e41842209240070741030340016400140349910303120355900d260021740750000340c0e401900ba0b90720444600503200e14210f414561460b49030034040c1d00307081855005601d9031443c22034280066a030303034540c0c11506054210200801c801342a03207a503120805800c021100c411560f001c0480c0c24400030840c0170b0b150004407840d803d00c0b66a0a414281c1340c21240f98194000f41c10176a002e107445401e0341c0e613507901b0b02c01428 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559027805 1250 559026555 559026557
    0x712120c0c0c0503211804090503071103160e1918150507320a030f05060904173103050f06010b0d0207080d060b04061416061d0607 58
    0x907007480d18a090030607412150400c40c026049042000780016250f80182c1d040b903102c0440c5500c600742c405405c6619142c030659140e1150401c200725050020101c000c210140c05502d5408103440d6600615564034898041140c414030a80001c000d8001f80592003034116070042240c04d4941b51954100c0d0507185220180c01d500d00e00c80c5c5605041103500400444000c8150b0814002ea05d807240014166414001c5120801c011104044030342111500b2004080081c0000c1c680d00c401200000034014200c1c04800455103103840c01080301c62034540510b9100d144d01c54000b5041c840e260028910030f0300003071880d00f051941e1000c0ca02c82e110039450071083c1e581e001d6030145100c610b1414094a0000c401403101c2e0241c00c1880103101c8802d402c0c007220210f804400002d40d454640340b510101610925840a144601d0688080b1741a2104401001100c22541d24400c01c00d5140340c908195200d84012001225600f4600000061294200540c816096920034031261341281c03216080c000c0455103c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559029055 1250 559027805 559027817
    0x3190e15150a050f09060604030b131e0c03030e040204031703040515010e06091506070501060608090309060d0b01050c0307030e04140601050a1202090d0501090b06040b03030712120c 80
    0x45100c540c444001404081e044600d00802803403c000718108601c6088403c1c09050620b00040b02074031134400315401158400401126031811502e14860700c61100c804840d00c100c814007803051500d688070b0008450350800401c1324800d145a030141c994100303111580d40c1160302480700001080810508205c4c100081d45415520715052520904140c4603180d5141019429001403011944501c2c202d54400030560320749106444003035a481c1d141e401d0108107a400603000074040e08104064102d0001c5442985480360b1030b0300d03800c2c12240c40f401100311568001c0000d01500c0400b0b9060b030080c141c03a11060400340c1c03a0101c00c5084904690100c0d20640115041c0c2201643c0b40c1414442c0e811700745550b50100e101c2e400c00c400000c11900c00e0b42e005100f04980000a00201d00307460b4110360f0100002042c0e011040920300c0c12602a110361041918070400c3c48002444a08140c040c88482d0301d80100914900481656403a1508029080c03400402c08040c401542c100c0381c510583d44410401d0b2900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559030305 1250 559029055 559029061
    0x30403020415081005060607510b060408030703081005090601080a09020102073f030f050c010b040504080705060a1a043b0f070b03190e15 61
    0x40420345030a11a501d080c40c405980410440f07001054035485801c6000e008241c0ea2240c45c00502c05018038800541045421006a20340c0e0001403202c1d40d4200c1044038413104114550221910303100d5009842408031041c200c0c0e0314500001e43c2c40f2003c480c00040407207082c80d860f003125501d0341d04080b0044020030b94100600c9180040c45101800800c42103e05503514039050b8002400c051002c6c1020b5070040d158100c51085a0082c004107003c0d1001030007404194404551401d402000160782c282100058030000c00d14514004c0d41500b000d0b09030b11180307001c20404100b1103003a4400a407a8045541e190080c003081d0360b40d8010f0702e00950090030304903124546402d03c6410001e018011042062512001c440070004080c0d0340c102c113980c02c0b40d000427800c1020140c180b8030704c1d50900044001c01c001001803c0b11001c00d01c0304c0d0740c402d280c000f00d0b0b80c400213074014180e0303922107401403000032001880054146408003124103912001d001010541906003100289040c1641c1b02c26000e5070284420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559031555 1250 559030305 559030309
    0x513080f0f0a030203091e0d0303050610022d0708100b0108060d0309030803190203040602030901150614160f030f03111c0e0a0b040303060501081e0604050a150803040302 75
    0x11503080e50544020305107503101c6643c0030f9568072407650001e000b1055a0a1010034500c090fa21019101c4003605042c0424280d240c01070090a0131210741c0d11940d403456040428600c0042c000000c00421074180b900132010000e0b2601d001e050061a07209482980c02c0414031070018070058040000c1d241c404680d442c5004000340003103600030441c84c0500c0c00c1d0140a0b002c6644030822504407030300040559500d840b401071203035048009401c940c0c01039000100380020401c0b0784d80114403500481e4005c0200c0c00b0b9207456030040d12030500c6035000080c83e600410643c0180d04004110010000d18041d040c0d641d203640305404840c01110036804140782942000c5290b4060140384000f28274851401d203043c08142445200741d101071444200e0301ea0300e400f0342c00855010020801041e8100c040c040542c030b042d2800030040c100b98051079000031001ca0100743c50f10345000c417120420344481e41d2210555034540522005100c01010407410316268008400e0040224004002400503680a142c0e6a415401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559032805 1250 559031555 559031563
    0xd081b072004142806092901050c0d12140405010228020304031713150e15040618170c0405180319030b04020a03061403010c0f0e010513080f 62
    0x62000d024100340f040040784884c816031940040381030310307420740e0108a0080490050a0310380060000d54a0424400342402c1c0c15001c0c0d400800c09001c041c06120410401143e00b8017442c40c00a0582d81700341c14052210740216100c11401c65026000500c10011001d445000c1c03400762030030345d020b9500250009075034100111821800322240004e0301d08200c02e03d00299644110301c40a010710a225007500b80d200603030011904088074003c0305141943e100c00300308040e4819110300601082c04111404c0c21800c100f040d9016400710b05003d2820302d440d01c0410358500d680c1001c0100110f400c04000b11b070040c203c003054071b40d9084041c003c044c1458202c1c2070000712180034082044201504200c403000c00f60000440300c60004042e2240d080c0100000c06a0140c0b038080070b20740d0300c180041a107540391581503211500b01c4034000e180d10300305803c101c281400c075500c3d803003810000340d00c902948000d82c0c01441c0701c1d5420301041c5022403400c206982c19240c000241d03041a081034010f20052588814104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559034055 1250 559032805 559032821
    0x110d0b0301090203060a1e0f0e1c2a0605090610240e061314090a020702030a0602031314010c020706050c0d0c02040603020319060e0d081b072004 64
    0x50300801c91451590000b9075141002040310900301d4960561041082c01001036503101061250103005050854200b0b01c060000700000c64064400d18041c2c0603040c0301010740c00355428454583c10104224400000c01c10f401c1c1c81f0400b0411802a00414002801442494440c0d070307010000c1d10b07150800c0c1c1e140c09940c1109911202c445042516420303100480c0c90145800d1140c1c03414584d3b5815145e0010a8403070042c88080129a02112000242c0040c0b16021261540048503000042c1c0d60f50750419049001d142c0c00a90554040d00744400040c04560046400c01f810f10007a0402a41650310a0303c4000d00702c0d403d02c020b075140c23010000c18980400044018024a04180303003001300502c901640d5000f41c140d86800c11030b22520030015511140d110381702658019090340c400c45502414072518443c0311030700321401c914020350b0444419012422002d0550745c1c2d030b107442c0e43d44c4400c1c0c82002404080040400300c1d482c100000c000207a51100c0c100c84150660460000603070714030701040101c4280c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559035305 1250 559034055 559034059
    0x110d1e0c0807051e040b0604080105090d05030c070b060105040f090207050d111c1707030b0a1e090504023010060e040b040510020406120b0d0f0212030904110d0b 71
    0x1031010701441d030b0b80c9031110b0403c8580f13911550010010308005030160031100c002a0304400000b9011980e182c0640103d4800d8600c03100b1501050b000720012615440125440124150b046c0000e50020740582d0103945c100e101450214101515486038191600940c1c1c0010390b038641c0050b6000400000f48100d200c0c000d01400c0901400a9280f001a19010381d4081400c0d050640d040c2204802e000d400398810100a0b00c4080d00585025800903009004c10502c070f0780b20300c41140c8000740b0540001d01003560142440c0416542c0c0e4589094540a4800076100f00d81c481142a00380c50911031202695032040c0380041000754810000201905119200d036220440c18207040b0140003d80c0061044c41c0c019074000c05403005a503840c00c00da81421074031100994528000980043c21a921203d0085c42102d10340081001c002c1c120200603950945000041100641d220031070054909061101d040c18100303416240303401550300000d002c07900442080c1c551020040388000980e10795100b074501070001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559036555 1250 559035305 559035313
    0x60a0c05060f06060301050d140307031d030601151b050a1a011211120a0b01080d0e04020c0c10050c0601090c1b0506040b0907050d0803010302042304110d1e0c08 71
    0x45400404c01d18031050091034040c06c4103161805c1000b000c850042c8032a042c000c241e984903440c42c94020003808002e40788003100d00851030007103504e1601040b200d0480300340c01604081d003500400d00340c40505a084400d046682070160007000700d4024081c4081e040d2140b40150824802507040c541030039410b81003a19195002411480040d203c0f60800943c40030850b500d20446844d0512035240203d000d1004003001c11040c00001d05d10780005e85c54240302c2468860350740d4100503409201c01ca0180d05020301080d803108441c2681424050700c40141c0c81c00a1401e00d25045900f24200c1c6017482c2070313208170b50159540c4c1503410755644c03046215881000650340005444440d46030305541d5040904058000110600401c1140e0303010048130b0020300014100d4120a0810b0400c8643c0342c0092005a004900303201d80c01c4403011a5007030701010801130040c8d02c0407a454640310800c00101c2c1803c0e035070700f18041e25451804a4804102040403106d6800160700e840c2035403800c0014541c80d507001c1041580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559037805 1250 559036555 559036561
    0x305010507080403090b0f041d06040f0c08040609050705060f0307031107020105090118080a030801030b0901050f0103141203010b0306040f0c021009020402070f080c0f0622030e060a0c05060f 84
    0x5407008085088800d00e0300306d19260301548070b002995110704c2e4840b50f011f10101c1001a9a0328403007006500c1400111010083d640400741400c040d05e2000c04160005a80800002d0010b00f05500c42d046040c010000c4500c0503031500301060303055010100301c0580050210400c2003481d45406101d0042c1c540000250410700c895001a0243c042c14a6aa0612801b0340c80b04040c10800c02078035004209180c101c9511241605010306202c500780002c1d660b81c0c044500090540505001c1d00b40284401c3e0007100c480c0c1e20715100c554104a030701800d48082d01034000000f0f101c414034000b940c064150318921550340d0800c00b0801c070032100d20a6009090780e0400c034103401455008a0400c8640b250508045185062440041c00a11841c2c00c01494840c0c4040281d00f4031140300f0103010320001400c121200016021009903545404403034260b044646c2c9803070442038030303c07039100c15030a0382c82824840800c0c040d4500081c80e9400030b0301c80000140c82e0814482c24040100a080d8102c05030001c0a07404d03003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559039055 1250 559037805 559037807
    0x10030803040b0711030f040e06090c070b0702010902030312010602101406040f0609020706200f0f070515070e15030f01050d170403030e120c10080709030512040305010507080403 78
    0xc0001080a403070a0120000100c0b20307030044a1000900c003600f003e80c1e58030b000b0004074900726049801680601e20740040058100e00700049941c5c044e9000c0d0764254107101d41a510a44c840744001e0030710046540b252606c02c016141000507107004410000080400d42c10008001e10704034500d90030080301801e2035042c3d42d8030b5489042186d0420f00c140e601040e01100a14410080d08440d4010841244002152000d12410364071040c1c04c1c021800c3c034882210700300e02d402e4030140540c9034907034400300c800c000c11005404d41000918070984a10240c0e008803145021a0150078012100fa40101c0c04500705607101c4c0c40c0002ca8010085269012582542401440c1040940050244c180155034807242c1c0b1003489a40c024440030000d070a502d9aa8494407860004c0601001003081170051030104820040d54001180e00548400003800f00602e410300745900301c403001300280004040c442c5005011010800c144010400650343e0b03120b10b55614a1460481c0c21107800412602c10400c1c1502480002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559040305 1250 559039055 559039057
    0xc0804031d030a0c1503060510020312151003060501260c0703052a070e091005042405040b010509041205071a0711060a0c0509090a0603120215100308 66
    0x35403160408156610401c8042841d20007500c0c1c0207080300620090000e01c80d020300c03a240441c1402035038140202940c6170f060103001c01d01940c004000d60414403140749890f01418806030700214a82202c80d01744c28200202d842c00042c59015030009859071014030007940c11000d0807070368602e000841801215017203e11003c16001401140e03240d20001381c14418076101d80c0944070228208034a8000340c0c00c501c00b0403141411409030306001d44c06072940000b1501256228544035044080180c141c120501c1e11035070061100034400c445841c0450b0301d06035941840c120300302026550640024031030400b030502040500b41680001e1040e0f800b81d0030400054441020074164402d00d0030946c0d205c282506d0708110350030040170030100100890080001c1c0c244c0c00010341c00413911143c1521041d4840c030b4583c105440c400300c0000d0108104001022141c20030440c0180c0c440b050800000303c15031241c1d11003400321204004c10005138000c20000034500c1c0c00449647c4c015842d81000b5041c0c40c030b181e03101055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559041555 1250 559040305 559040327
    0xb0303090a0806060a3008190206040c06030c1d120d0210110405030a031202040306050c031f0e0610090e1302090f160f03090f060e1e0c040b061e0901030c080403 71
    0x6d01c00100b4008000c001e0706400352201e501050207070324503100b0080c0000303540300d1081318182d8048111303c03000200305000780700380840d0643d40d5403000e100140f800c621071844000c0c0510703590040468403000c942600140118008000c1e0f9501401c1071120003420361040da44e1000340745c03003458010001040282c1d00022901c0140e50b01d0b0401c01443d00341c043c1008000d0041c4c1d4006001c5500300780811110342c9001e001148a0329844941c0c4c0c05081403a001c8240220160007000c00e40500d100c04100d051901141910700c0101c289065943c094039400d0000d9241000ea402c1401038080340c40381d0301146840c0201c198800000d541540b070501d0074850081410101410031000e0003e0040c42d03c003054425080561885e23000304d800c04030003240d0315007280205800510301e02140109040c0c00f4010141e80060840f4401c5480208000b8400751b04010090403244461540040100100d0034403030703505071500c44010550010300c0e46902c0ba5100250031756070304200503030800c0120810800029000101028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559042805 1250 559041555 559041629
    0xd200702010305130b0a090623060120030c0a02040605060f03011e080303070e01021b131d120a0909020319270803010825090b0303090a0806060a 64
    0x140f00c0d1030b00381e0514410720341c840010305075021003001c0000d09a0b46400480280d481405c0400503100820030007562499240d00e07520075040c1c1ca101280e480e49c81114034400c0100d0b03080b0045440c001641805265500510700a80c45401050020b0103500d0301c0d02c25403004200585205180030040e04811540b4801405400003221801c10b0303c1100c60a0340c005034001d0040740088950324208008041c10540c0c2500f203031401441004008180c5d444c21021100c00703410094808401d10040160b204d028080c1c40b4450b2404060800c00110304060070440c1815202d03a00c111140d076404206001002d603c65070b0021100c0c42d0040080c4940202d65000124001c0784140000278812a000d99000b020065a4003080c0c2c20b080300c54a030001d10001d9030055040b5000e000440c0c0e9a0f101740c02c2c28164100c5805415145110016020052108103401c2402d04480007826030303141a14620001da12a0903980004241e0791244040240ba1300380071001c0310150003020740c0c43c04e01e20805141c405800e03043c0c0b60002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559044055 1250 559042805 559042811
    0x80c1801030507090e013e04050a050d020d02100f0906092d0b0307180807060e0d111005030a0f111c0216050123060303040317090301060b0d2007020103 67
    0x200c03050007035020a1f41c4a10890f00b6000000c039105242500c0c0b1707507044400030704034526620616203801050032101203460207080829042c0ca071000700300d0400005c43d002d9030000c180007a0800180d4600e40c0c90140754446842d0019114101180100201100e4200030280155140280206030950000480381a1040541841d042006800318000d4440741e001142a40000c400c0c01816900316a040d1400e8010320030300301039150384800303d580c0c0750214800d0001060800700c2038a064103108880c0b00d0340ea80130b000380d041c40030f11703040200703d80d114000d03d12800203d0100500407800b00900841c0040c4003028410300c411249003190000501c204510180d07081506034080c40a80409d80544112283d005200b18942d046400c11381d01030142640640c0c1c01008400c802189040b422444034065640500258240383c00c2d641c400d10076101c1e418440106076014007003480701d640c017401202c025062040e2025140c0c0402020403094940181c0e900040e60740303e0601c040c51290319800c1d42c506540918003c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559045305 1250 559044055 559044071
    0x10c021c050105090d12090b0c2b271502180a03050318091306020702040207060903090609050604030f06050c0f19120b09070c060b0a080c180103050709 67
    0x548004494800007041d6500b00002c2201100d40490070003050f031266101d918040458482e00c43c116101c5160003440160b600001c00d0b4800c9121020b41600420100d40c00314400f005a488503098044148800c260358442c0c00c5036408001340d100340d501c00c10f04440c006841c1412036548030095981502d070203500c29404544e840c030343c2c0ea0003002e03812900d002401041403d5201d0500035200e50040c030341c10b540b110303d01c20010be10341001c1000310310401e03c5684414210010b9608e400283d40007030310682c1d000740c080c0071000100751648100e0305075910940714011290b18120000d880f03454564451842104107000c10804a51010b0341e0340132041d48404009216951540540c0b514082c160741d81c068290042102426905c1d0045041c1184c3d040d07490710741c40140102c1401040d21600910035400a0300341c0d0100f092540075505030f030010385c425031002c2415030b40400030031001130480c2d0010071541d100d600402c03124108202c112160344c00c5408003041c150304540341c3c1c07681c881c500d04c02d0301c070079035510700340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559046555 1250 559045305 559045339
    0x6090c1e02071a0d050c1213020301060b0a051308010e03070209100f0308120f1003080717160c0801090f0f0f0b010b0a1b050d120e03030405030a02060f06010c02 71
    0x4014042c1815260118680d0380c0507007400e28580000c2401c00c1c0ca18034045c00301d2000014402901d8210405044042040d640c0441081400c4110b80081f60559211079002c128010b04002410b0071100c503980300e075159040001d04070b14072682980101007c1c1d1400000f8072019502004035402240c042c0c0d4500819294035240090095640e40100c002410b01230012040020010040c0407aa018411038480c640f20601c01c4202400213981c0c1d10400028030f80c08100003079141000c0e02d0041d018104e17200d9108120b400307810060380104080d190041001107404104400341030000082c0c404100204510500e681c1d50f560001c06010000d00f41c0d6010f1007000080001c10f101d03ca403901d40c8035040014559548000b840107800104110303012460100d006010502d60340d00d49540c00b60460010011100c5409060f43c050200c1e01041c2d44c1540c44084480a52000300001d50186100307000450352242041c80090500f080038000c0c1201501940900c4040da030711241c0800100d40440e030300c00400c0b454510b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559047805 1250 559046555 559046563
    0xf09052b05030a0509091501020a0b0702010b041b0f08040c03020f0a03170d0b060c25030609050601080c09010308120a1d070e01121a040c080a0602030a06090c1e02 72
    0x11004095200002e400e1040c1940913000d401409419103280385643c50f04410540c45668820485005030f00000c09007000c500704115140d00842c00c0d0000245c881000b1001c9015190440d016070003d03200800c01d400d040d90301c0000700a40088a03d4100390505107559040001d801d584006440303042c002401d84103940c3c6040040006540c4050f206041070116001890640c01500881c0e401074035009200c10720b07082c80801c80708060b078010b01a05c01091000b00411428a80030880d5941c20151100807000a1491040d0803d09000764002c0040350701d0300400c103182004420106003e440014010000140208282c844850f040403078552a0764890344031000620394140a071054800c01001c07042036420124214003621140003840c041c50783c8440d20b91403541200c030300042100e81e002150160b8500600d075aa40c201c1c0c82003a8a418595607880502d03c3c0801c00002960210b50001c00d002e440440e5128030300080500381c00510004501c440c001d41094079000b01e80c01380d040303042c1020200c944248 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559049055 1250 559047805 559047889
    0x80f0405031905010c0903022d12100e01150608090a0c03060b09010b0f07030305040203070915080607020c010807031806060f060e030118120507120309030f0905 71
    0x240440e403882c035241c480c0499504401d002500c0f594603001c1c808240c50f100d210004103070ba40107000e040c0c3d11008041170f8038071280f41000302600b0a00d030945908465a4825a01d16040110700083c000c1c480303c000728008540144070382d0540c0d80c2c90602906030468028030700004607001428603003010f40d03c3c0c185242c14512400401840941c1c2d0302004400c10a05610200140e001920000c04c6680c8484150450748a0034001d040585800d0000f0400648a600171582c010f1028081d5600f10741d0b540c1810702943d0a0300c885400c07039030a110040c0b0103034004004469001070a48020030751221036000117403183c040a804031042585522000c009080783d000c5045496900c1a0100083c0c3c3d80e80c1d0080b82081618050300b40051002900603182d03240c14005d01c0080d1051242d401403003441503688005090104403c01d00f8003205204d030710003040c04034101c20508203042c0c4012481c25140d2070010016019003030580d0600074042400d0000351500c2c0b82c2034030302c0d02010001b040420000d2407842042c0180c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559050305 1250 559049055 559049059
    0xb0102120d24030b09010b13150b0f04080d020a0b01031104022b1a060a0c0302190501090b090303091c02120720060f090904020402040e0f0609070201020a020a080f0405 74
    0x540d8a10008542011490843c0d000d030300c1d60040c90f100d15996500303031a12040410360102900c6407a25030014142e100d211560f0b046405007102659076640080e0f907400c641c10039400134074080f40c1042141d01c18010741036a41140d1024051410f0343e540d6078040880e0601028103c60201e50f040c001c00c0d156a8101d03800c64480c076180c2d0300a07a044a08504040710344c2242c503000720341080000f140794822502482c0910f580100024142a40001d04813110b014110f0244d00310b100b4042c21881c50740140c040450f410303000e400003041004150900404609010b401d280c403a6008204000034010003043c01060507079250000001d4480e40d070b0049141c03640241038400e054100180800c00c0180c44200602c0c552603050310140d1a21800341008076a008484025a00c000204420112072074040c003030b01d42c0035100420040c10103071a00704002701d4501c1200c68480d20810300c001e00c002450403c454680c406003a02c02503250068800b4002d465021412009220381c070040303011210924050280d41c0a4540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559051555 1250 559050305 559050341
    0x70f170a180c240c290a0b1c050c0103111b01050a1a090705090d120f020c09090a17040e07080a0e070605040501231c0f0b0102120d 58
    0x10078100341100c2c44140c4103d404040402d2031000d0340445190348140b201c819520f4042a14400d074a0f9980c0140c410a590807120b140301500d80074041d40040320900483d040034001480c410000144030307020700c6519100d1502e00030700940400142001501c0d600010003860046880d10b2407810b000c0050203500c2124128110381100080ea0000552086120b0042d81500340704030320100c44181594100c3d200d015401040c5c101c0081c01c001d00440080c001048060b112604403849500c0700c0d28001441190f400c000760f0401e5a24110f9541000403041010045480102500344410020341c4c9107200720f8002c00003140880584a03081050040d2002803140f290000860b180c0b408006011001c1119800390443c0381121099941d4000108241070302c3c540e4998610b0542040011345507142c0c40e01c0c00344455000c9100c1c602440e003c0340080d10b0440000c0001035442844a010744040c1c814081142503654070b0941d018040f070780c0c0003401d0300400407004150382c1c0c0c5500c85190300010b040408107600d01050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559052805 1250 559051555 559051601
    0xa06050a090c0b03070f0f02161401020c0a150c080c010c03090203073002240307030e030f03060118120c0302040e06090a0311010b130f05070f170a 65
    0x1264108188a078402d442c0c9000c01d5031154007007050780c001940d82e41c1c00a44c0d0401c2028085014802c40400380005004a4520340c00d01c000c455194040d0341c00c543d40d2640615181c9407196010000c010700341104403013402c203070340c00c1400802120340010302e4034040001040130507051040c00d004036100130031403400034040c1481380c1d003000d0040c0074114801ca0191080315400141e24081400780301090000106440040c281c1c032802c3c0341e0380c950410b2f043c0da0050080d5120b04144103802c0c42805014242d20fa080d4403441c0c41d12000c0c0c00c0365240c01d2101e080383c100304921410000e40e80101c0b03900c80c1c0c090801a03603c455a00400c2400c00c820342061030320900d03c0801c3c03000c2c80205141c45048178400c590a11207400c4000d00c0d00e4aa0209861120140d4000c190742c40019028005011000200e480000b44c202105c0c40082c4807046400c1e0905200303039880c20701a000c8905e40c055154040c05c4c034204018440300107000104404205084c24800e1201880403a4101d0141d8001200f10113002480c0312640c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559054055 1250 559052805 559052821
    0x403150c2313170c030609060402101202030f1f0315090c0518010306180506060f12031201080118050a0803130605180601091503140309060301080a030801050316050d03020a0605 78
    0x10f200402d1104a500c80d61000e0046440d0001e407091207145800c0107071100b621103a00380611200c0443c2d045050043c0300b10158a081c141d44050f520030a8100b00f0711049042401c10340c404100c00b500900c1d4404103001081c0003141102d040b5076031208400d6030000c1e0a503018106080614800e800103a072003059042c05004001246005d58140c9015010422902e0f0010340c4000a01042020041040d04001c001920520b0b100041c03400400300a402584001201810682158040c51104552040080060158110074410820050f11140401d0120b00c1d0315123a2964407030601d500240340e0440040010000c3c1ca01036406440243c3c481c005110b50705002c905c4084035040c40400101600c952000000c42441500a80d400b42451075200029542075032210481c540500070500d4407403008001d452803a40f0781d040118024555000138002c080e0301441c0040c081e9106900031442903101080c618800e66503030302c2c864106d40d412500f40c500e0444a180076800c2060350318029060b44d1912017000842 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559055305 1250 559054055 559054079
    0xc0a06060803130506040f0b160c060c03170408040e10030203011e0510050a120f200a0605040501020303060121051503010c14190917030403150c2313 66
    0x10a04102c00102c83e5925001400903901881c03040c01d0440340c0c040c0d020000c103807026000b4045541c440340c0c0100001c0050311030080c840d403a544007400141042c2c80c02014540c0c40600f04143c2261283d07103c0c024181529864210f00440c010315420180090102d80c1c030640182d112801154090024440c2c918090348441038400e0280c01304d86d08038105000644400d03a40450741d02628002450300780080d052580451899078074060454072402c000290700003188180701d003050205842c3c0e201d070300807204460a01441126a80c001d10a00905100038070150f1b0b004010b80b1740c0404286082c8420603078111000741a207005000700300c2c1c840d1801003801a42001100c3c1c8107420003064000340004030003000e044a215801c01190b013140441405040444082e840d0300007840d52080c589120780c0382d11403035880350288240c5001c4204da400001c0800c00c02080070740002c0200b502100800007607420a00c040c110000c1500140f02e109200308221228105101c15221014500c0c2c1103c00e1094442c1e1812400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559056555 1250 559055305 559055317
    0x80c070b0a1406031501030b151309060b0603090d0f050d020a39150219050309010b1807030903180602100b0907140304030207120308060f060309120c0a06060803 71
    0x242e00d903001425600780010a04030465031800c080c24560710710b884880700031101501c170b071600030b698003181d1080355600f41d003a0260031026000014400c0840c0f03002e80c02c0794038910016004110606c1003056140d004102200481940c0c24400d10500201008999074410b8601542940d4030120344a650b86600100c64105c80610210754a0803550101030b0103012041070382a6440d90a0020411002411040041c102030070307200400b50905e08442c80c0d59920030100c1c4c92100001d0004820458021003d00580034100c1080d1581684115150040e00142500402d0b20003416111104c110401d0310404400c07944210303110030b0745401512081d000b5164010740c40040c00080c1002901801481c00b8103640380522215100e01018a040f441c0c0d041703540e04020000e50541c040c0c0d1900040c5c1b05003d0034044036480c800d40c0d9507038691030b00c0c0c1c00300120301e481180d040340201c0f001d00801980440002c0d000000c417250113806500c81c51046103982c81c10810301c9000302414105003000800e08800409842 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559057805 1250 559056555 559056581
    0x27090f020a0e070f091811252609010507020a0503010e0d200d0c031106010e180705010206070c051e03040602060106020a08040b030403050702220b010519080c070b0a 73
    0x4400744c0200881c2d0310895402011049114081010070950465020324450b100030704103641440c020700c40d8401004614503900501040c2640003400f00f000102c81d14440d914200403200301a030154001d42280d00655102505100c070000780f5009554427140003200521004009200b01c00d80c011b805a2030f1a080041500482c1a480354410085104c0c25a0010080c01e040102924140b04600b25400a40043d09406201c000000103041500030302070903020740007001d00c95481d070a0010a0500c0d91000f003241800e240c100000130300c02c5aa0110b02c0380c0e0840d00c1c1d403600324a01c50050400740c0c2003149c0c03411a80c1d010780800721134001c5070700080080c1c01180e0b916001d40e11907130703030b15001a43c0b5101c4520006016003010002407000d507802d1006035801900a15049043c41d8450b8007040d0b1b8100703225600d507140940c003180f070b036000001030142c1401584280b0b0010b090009405d00078100f08a412414400c0c004010001410350130124165445203400420001c00750030481c823244011321250980e45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559059055 1250 559057805 559057817
    0x1305011a0f0a0311060708070b010e041403090d0204050c04080a0b271903031803030b03011107021c170a090806070f02031206150c1627090f020a0e07 66
    0x941c280382102c105002c480c0c01c4031442c440180481d00700115584050700444013140107001000200d1a85c10056010f080550744201050425041c001013441230200da8003910b078810403080c2c21548034590440300c19641a5000f04054513900d4038024907025a4200d14841d01c107a101e0300060000710003056002e0300e80f00d1403824001c0c0c000e1050b00c82a4120300e82d0900982e206116045070030002d646007003034081c0070345000140c1020629081c00507401806003a0002500c42d86034801a180030310600501342040310720b5616180655010808400243d901682c1030700c01c5008860602c88d401c0000c0d210f403958100360580e105850180a001c1170294003401020307100d007000140e1801d0040a4030300c0b00c2c0809800950400d0810944c604c0075000003000c2c1d03a04849214000701040c0b0000c0040e01682c00708401500041ca20440c00402c51005680020f864881b000d248442030080c2d1524404102255034010610b840a400c0440480070501d4009400288000c000101781114481c9640150f03820b0b6988 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559060305 1250 559059055 559059079
    0xa091118040c021c0e12060f0106020f070603020c0705094204020714030406021005060a05010e150f070602030406230610090308180a081f051305011a 66
    0x40000c6038004080c002c0541d12000007103c00c1c5030410b48040b00352401d031501d0b110f07480342080403d402159010110007564480c600340324020100181144c09081c0c5880145640c4c541e20800316582c000510408060650008800035490402c0c004200500006000d258203402c10b1102181f60344214180b40115180803180324014844074101d620b414002d0203505249840600b04010080d40403404c116410626543c50280101090000e000181419009465042100e036001d04c2a124000c00f0248580c00d0000d06000c142c0c1c0100c0380301c50000040c5c6076001200c401d0442a08284075000c0d82c0c446c020004580300c020000d160700114440d44c4a000f0502c29034510b81c02481c0c040b03030065150712002c2d81e20b5001030041d0038224207131141c1e5640f51404aa0250b1780e51a070018650000202441c60704032001005035500f89604100e006141e0b0000404942181242003080754062a07509003016407a1000301e01c00e07018082540c918a40c005000b000740c1400a4100c12108040c107400c14003425644000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559061555 1250 559060305 559060309
    0x5071502040f050f13090302030c0c0906030601090903050f04080a1208150405090a0f050102070b010503120f0a032a0806040207022422050f041b0e0a091118 69
    0x35a0100c520b1078804054041c10310003044120784081c0c07090342d082002086804040f1a40d8010180075500a4018503a0b8007083d00007103082140c4c0b680c03041d01a0000f81e040c45400d890004040f411541d010100240040c0c2601d002c4995100762031030351282580118000c070390100c003c90042c0480d403103404560400c82c0e100c40300344e44082049583c000b5100002d21402d806003860340000d0b5010501c0f0301581c04910142c0c1c1c0c2e500000160407006d880e903a40c0410000c04004042c2c00c11409028110000c209400147d007002600f841012001070900401284107031485010360443c4040252a1b048940d142200030b6950010000b8507822030002118a0013085941c245482141c01460b0050b00e2600d15504281c1d4001c901d8100c0281a070514008103c00c200402504140107082c0204542a0f081d00d454501001003c510310b9040034821490310b0303001800e18143c004010707100500c40c1401603142c0c4c0580009420046e941d88500c144c6420700c442100c5080707501005003080700440304074092007401781e02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559062805 1250 559061555 559061557
    0x41508010602030919080a060912080c0f0903121207020d0905030c0910030f0507030c0905070c06090f060f0213170d1202041508071716050c10050705071502 69
    0x1c5000d0160b0020000e126080c1894040e00c00780040740700182c4072983d5600c143c4c80c40c01d1035440c0c085d11000d035990111010402e000c42c8120205800d07250000c02e504264003856614862510400d050780c07400120501c19842c00c2c000c802507485141122521030460030400c1111640480346c201c01400359200003445a0302943c03410302602c0c80900186001d510502c180003841c00040d003100c144890280d8000300050000301c1e908450751080b000b401110f407551078070410210903034021501081c18072080025681e440300b080807480d90464800b00c0c2c446024203040c6d81a1240b030b0800b400c030504000c0c2014404140b40c009089d8040d40ca4042c0041c070b0340e10b00b058500c41c18002401031154008114000720035105a1103102d000350081d03001464503a544684810518000c080340d008a803603441002a260b811940300c00340341e1440e180340070342864001001c540300358128031180140600410035505072807003001800001600c0190030003503401d200e0b0300900f03142c100c000125000381100d056541a038410340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559064055 1250 559062805 559062809
    0x10e181f2003010504020c12040602030a02060901020913020304080c101a010806030303041403040f030f1703040f021017270a051c050d09031d0301060f120201111204150801 76
    0x414014110f90902c01040040d41c80711011404511640d60311404c0c0c0080e02c2e0090008080d103800469680d00c1d0ac1c40c000e41840380085c07007010982d1052040c40881d8640300398903568400304c03000042c2d80e541c0f2860654901d000341c2d4107110540c42401210420350340a0344c05050241543d55000218140880044440c42c00c1100c03c160142c0080c40030400054501c0e0042c0c4d5541d5104041d00c0c01e26480e69641101040310383e00070741d10102c101c7d003200c0c00d01440030100d440368852803030b0041c51860152a918420301564000074007441740101d1f000611482000741403070080742c038143e43d1058202011307a100c480e8240340c81020b805950a4004002c8040010703504009907000c400350203d4034025100c900c1b950903010750081481010000b02500d05083c0c0700741d078051407103522254800c110f01000110034416031032200b8043ea01d80360081c49580042c1100c0c034225000d5044a8004003464801240c2c840082150b4006074401c400300e84454500c0c10018100755054011903010001c41c0950495412400b8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559065305 1250 559064055 559064111
    0xf0a1a0315060f090c07030f0912242f190311130602030307020c030106050f0613091b1101020307081f210c0f0806010e181f 55
    0x8410000301d511405903a000c03400810942c0204840f0020403804582118028000c070400215901016002201a60a810546042c80c40030b03050055100e29000c0cac10314041d01140c003454007144032200c41505011b542c00c40400034002000c010322103141c018180b40c0e00c034501388540d000e4240021029015a00500990f0200020b82d41011009030020040040d032407500031005c100c5548000b140105c1c00009080fa07030b00559507890000300017410b048024801c00e1099040c00710400c01940c0741c5d1600c4511100c1128582c4ea1540300340314128811800350b002c0380c0b4481c2000032210000345000c01800c40390300d03a610f80500754402d68a6243c201d10044410f080407a01e0500855600d071301a003001d100e4096074002150242ea140c07010980c0404844090001f41026840f00da010846410180c40051058802103401242868034a0b910781105004014840c00141c000a20002c008482407501004010507a002c0c01c03a9141a000c0c41000050b034a81d8040c140900c00140070f074244c080e48030b64042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559066555 1250 559065305 559065313
    0x60306010e09040309120b01050f0d2a090c02060402030d09030f11030c0d0b0118060e070315030602031006110606010f1407020405010b030a06150807260f0a1a03 71
    0x2407410051540310141c0160104102c1440105070064890302c480c00007400b86020065544c5000c0820500c841400e1102d401501c811514500040706400809841350100c00c100707012040342821450b0348036039a4001c0314580c6c100042e280040740c000c1117080c00f0381d009a0507202c078007440c080103690b41580d40c84020400300302ca00e52100803032002d44250404510041c00c1e1040141c2c0030000130780168107040140d80e40f401c0100100020790300702c0d00034441c4900012050201500d8510500901440140780d201415150784041d4400408009990003171039000b8411522030030006c2c00308880200380c0c0a400080380908030806101c0300001141ca01c15030f0142c1d44d01010900050f0201c60001014540040c070345414400341e0300582d51360240c28080e044583c5466280e01c6c04244580a840c5107038400d405038541048041000d82d800076680780d00001c1c50130424040300d0544820883e4200e9a400c6000000419041c0705d80440c041180c18060302180c1014020524031290b0808075090380c0e00074030343c5680 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559067805 1250 559066555 559066577
    0x1201081b010815040f0501060e270403021e070905010504062304020c0318131814100203010608060f0306010506160606080a05030703030e0a030c260a02010207020a0506030601 77
    0x200c6103241580c0f1462010401541c25008004203081d11030009522143c03e4488005110503513205a441340d01c2035003200c4510300014a1050704141d45071040707030500078072045070009040c5402001000b000f010605140e4890f0085031221030384803d058040d83c03000394141800041c7c50f00d00b40c05048180c0e0312100c6d4404101e100c08819010088101c01850780040d020301440d13180540510142c04407060300020142c84100030300400c2840b01a01500c0341160b0310788100316409a0900100d0500c07140e200b040452650442a0500d10303003541404240c0e66140000f00100311a58420f240d135002d03c00a40300c032036840400004050702d40300c2c05d01600c1e1300040140101103905d0342c02c032008007146004410001c3c10345e44401c0d0150410804c2c03503040c0c96683c000180307001003692502c41c030301907841d03040003409900d2072aa80041ca09810304001401406d4603011485052a0041d00c01da0180480c9e000ca6075202a0520040d010b90003004007a4401c107031a44000409040c1201240e02c2003405a40c0c41401c52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559069055 1250 559067805 559067807
    0x10f0f060302031b1309150806010b071103010504060c0e010c030e0d031407062009060a0809010b04052a0c1c0c0803041104110a080720060c1201081b01 67
    0x500010031280304a1303003c0e044102e8402550300204591074071100c00c088030710f0030100c03103000b034030149001c200342c46d0105003041205000101c0c507213064a031450401e43c1e941e206400c00c6003d640303a8070101681546407400303020130000340750300c02c00310241e446d07d80b940c00b41c00c0000150f44403486ca070400703404074003485c032200068a001e400601005229082c9440404d014002d4114560080072080b204a070303407884003150492107000700007070240c40ca0003802d2030086440d022a81d035001d85488034090110540105d09001c20079044440d6890020380108514502401c0a01410315401c48003100c1c4c80000d401880d55080103411148442e0110300184107242c2c003a800d6007104080329400d0401c001d001c103810000a049a00214021802004d02d94000024001048200c500000b002807260b00c5c1044940140d541040340c05078010001d05207088501c1001c40c0104000388401070024081c0100310410010489610180003400c10040da44076483ea240c42d580765496008028400d080b6500c000000c03129 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559070305 1250 559069055 559069057
    0x9100e060c030309030909100303141308011505010e06070521121305371115030f0a140115090b1b0606190b0d02040e040b010e010f0f060302 62
    0x10a400340c5034600d400420081103007035400c00d99142d90385800000d0501407514040704290341000c80b08003500b150929596001c0c1000704200c145425403507020880300e80f4040e5010307070340d8003c00d00040280b08824100c0c1041030a54554003d90303012500c2e00c4e05216443c00e24100ba1036540394801c0c0242a50f070f00181c0307802c0c0c10900c5408515801142004201c1c51020b820100c0c1d4000c02031003611061107411480c00034103002c002d160415200d1410301925001c1002042c0201280340d102e0250940130845042c44010f1001205559410044226002c0403200300b00b03004511404012028081c1c0391580a209400d4848900000080d0208140144101c82ca40d010168050350035042414007950b070340c1c3c01425183c00203e4044070b180e0f41c0c15251020307036005216059002000b00c681d104400008103844031801ea40d8040c03c0015200440d61101e29942641100c0c0a04513022590a00e1700c0c2c540ba0640104009010b40c002055409000140c203d6000072400d0036100e0710720b140c03034005041c14011002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559071555 1250 559070305 559070327
    0x80d12151211153114011d040e0a0302190809090402010201090203060705041712040302120a020406150f0f02120c0c06032508040b07050a180608100506090a06050715020d0504020f060910 82
    0x15002039601f0071f10299902c0c800c02900342c183d500503100034585420081c4c10420260f4000304204143c45e1141c2c0000d086008441c1641e01c202c3d203000240d1184e00040b4010300c60508029010b10805060000e1240c0180241046404d02900c400e00b40a11501039502c035032611194002440041c80180014035082c4c02141c603002007a01103408400540d000141980c000d41d11003081d40f403060310341084041d0f00c02c0421010300c601c0d0a04d20102c04510000955800b0300b50210a02c6403404607514264032414032410090100080800d0b07264141880308440c011201b49515801400c00039151080d140108295072040d60080b04a072400d1780c480200382d038990f003c0d04d41c217810803d00b281050854007552243c007000d044c8560740d078022440c10780300e0700d02034186a07000301348944c0d030030f12005030155246030801d0300792070240c6001520b5034520321f4040c4480001082c3d5920f020300105140000e40500d6008034495402215455089240300051084622070013004907000303415044074000b201e01072402814 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559072805 1250 559071555 559071587
    0x50c0706050106080a0b01050a0e0f01030e060907170a0b0105010e120a140607020109050601030f060b031207060b04020708030a05070207080d1215121115311401 71
    0x498120190380d4881112000d030058004221402c09201102e40b8a00c60326540c01c0c0f00b8209149810298500500580a20440e00d0301c5010b071f9820071a1103901c40c2d0485040000440d0403610a41400c2c200070b41c64540b103024183c89074051040001d80b9020002e441c4204540008c400c1886900b444011101031460b01d604a4000c9141444e4000701ca00402c64083d019001c1c2030300118055410800e141403c002402c0d1004582c102801140031039004203040b411607030300c040030003c408558549100540b118900c502d6040c0280f02d00e40210760901c90041240e14401c2008114a0741c030141004204d01449001a0050405000040300303400103500c4660490405d00403207480a5803010045c0c41c100b60301c3c1c040d0000a200c0303180d4850782c3c0044c2c06004d21482051503401c3e0a141002040702001d292610058240310065115220b241ca640c1c8002c6e801c03140c6548455600c00d6500741e650888424810b58000303010381d0750320f526221003000701071a0680f1105404241c080e090176004684a11402c040c1071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559074055 1250 559072805 559072807
    0x7111309080f1812010b210d0c0f05120d0f050708160210330806040305180a060306080d020604030e041a12061909050703061122050a09140a050c 64
    0x20340d4960742d013244026581c1d291800465282c03e0301050020702103070304030600d0440e8690b6010030362004d00859080c0315032050f850180c070b040b411400c045c07503d00300f0418098018050440c000c842d5803601030041102e940d03d01428020900a03448903000c50300200c98910000729100c010a1f485402c080380307051a0041d80c030446140e0615401c421007141c064a040340e00c4240381c07030000b89180300005040c0058000f000d003102c51a84c5031000a81d2030f10300040c8000c1c100f0500103094440000405c0308a510004041d00213046a91600805001082c41e8015070020b8452055a01103036840012460710491b856035407042040280410700010302140782000030260a040500c00003519002140d5030030300800d000403c0a414100001c40054108080c0060800d08208000d00402c600149900440354001400030b03540c500d82c070747d41ca00c600440c07085d1155486940c0022501d020440e082c48240c03001103999203a03c0b13540e5540d00c0d04032a500780b501f21a8164075400546031450b1075014660090040e4501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559075305 1250 559074055 559074097
    0x2120301121515091e09050a02040e0a0506240f012c03030d20030c0f03040f1b0305010b01020c130513020303070c0e0604111c020c0307111309080f 65
    0x1e001c0580560440744c102590b0329400d449903850705180d13084109026034100088000d030b0700c50301d49940c181040030b409581c03030710078805807101e0401540600ca50844103641c2c450400502c05a45103c05001d1112200300d4503980000500e0482215151180141c5915140e0031404946090b0240e0702e01100b1a1502e00c00f994a01d85d0310140010139600144c0d02000500b0b042054510080217581104a142240140100141200c01400300c403100080280202e4491742d0b00d02d41141031411501c00203080c41003081248040c00e87c01048441668400c0e0020300002090340012665982c070071524a52240c03080da95040d0032200c035880560020321450000184064603004281b95074003aa00031900141242e200b0050401c0f9203000d10707086802100d040c0161703c1f024035a01e900f40510303c000342c07048603500e581d032444800301e5044036800c0c84100180c0c0c0e2140c1c843d0600003807044000e1113103401140c070503030000d03c0101544240d145035540903c1d45414440c4002e03503d080340d0000850b580d0a42c03661260 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559076555 1250 559075305 559075331
    0x7090b1c0f0e1203010302030d020606010525020a03110307050405070c0f11060c0616020a030906050a03141503010b062110030b0a020a0e0a030203060604021804110a021203011215 79
    0x1105101e6160030f4607880d9294903600c149494000e0590211007150002e43c18417220f0782e070007001c032000501e0351806441406a040c0c05180f00a518000003540290b240c070000040001050701040d90340c2046041d140c0d0965100d0502095a80495140e80000c100c905600b0004002d200280314a0340203901d01a200003499000ca22503920a15400d0241d51000c410003040d2000504844001c000901c058010350101d40c0d400b5141d58441d00500d0244000850b1064015100c1d9000c1c034400806800b0380011400c00c45a41e02580300044031842c0654245a450381c0e060420300c0881d0f001b1070725007600c44101c0765a2085030800202c090440c204200698400201080e42422501d0017200c9d807510040e5910305022000c0c0114845010340d40c0140340c81c120810141e513000c02d4043c0d02081c00c2c0c4026940c2d0b0b2115081c0e05040d1742001d0220742c03151910000e4011410341d02c001c2c002e0f10040c0d400b16056100f803644150400c1c042480341240c40a410012000040e40701500c104498405820105d151905208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559077805 1250 559076555 559076563
    0x180b030102030f190605132307110106080705091503030c01020a02010c0908060709150309020604180612050606042d05060906010507030504050613120b07090b1c0f0e 73
    0x64000303491081201132055085100e9004201d1854180c4100002e602d8107001ca074008130243d2072500e0f40d0350390300120041300d120326004000403c004c5844c0c0c500c92500303c0010f4041020144200c03035943c80e0250119440b8000501c1d001130701d100528806056881180d00c1070030000e00c00038141c050000303102c40c0220050174000382a80c0302c429000070820741c0040000034140e4060307030302c60746055008400740440c460f009012003081d1742985005e1710a0702d020203800ea014180200d4029049980014001019950a620130841c129012020710060b80c0da44462010490241c2c0050065002600419100e240c035600071900341c01ca0003111b03c1c02d0280b0111051103116003904071500d0390f44400c00c000091514080b815801203090030440c1c200309107900c004209000360300800703019160005201c442c0803e0b902040d002444000c82d40fa81045151600700d201420135548500460441d5802080d0b5071203110079280c50301d5440d400c1640d1100383c0080c100161400e0300240104035034031044c081b42000140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559079055 1250 559077805 559077811
    0x123090a0f140a14010e0301060522060b0a09090b010207030803012303030f160c0e0903120105010c1106090409140c13062426070f02010b010207180b03010203 70
    0x9240100007600e014128070002d1560042148a200401d5050198241e021610311161600b0f03e80300c03080c1070100d00802e0040020390002580310003800b07480c16000c084034a01c220311400258080c4442d5940b404855150b0090080010104085100600c019000c2e0b0b80a00303020041441100c18141c0e0307a4403030a01c20b40c002c1c1c001032a00001e00410309101031540880d0144402c0590041d4606070380f840e020f078014044e480700a002c8014284500081c0004c103941d1001030003240404a200742490105195a68041b240d41164103070608000980740d03003d04201c421490300f000d1200b144070648010082d203a0302a180d080d81c041da6440b5035001080e140d845c3c9484443c022401000300002800410000e15030340c5100510b91800c0490603c62480740c001e82c241704c0200c2c80003604082055031010f8404001da13515480401882170400c10140700d00c3c001c2503005400d2919040c04031101b00e0012070a80d429400040d0150340050010008030f0344011550b1000314685100141744071340c400010342640c0c016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559080305 1250 559079055 559079069
    0x1b03010b1209070b19020a12020601230109091d071404140c2a030c011b02010515190905090c040b06070515060a0528090b0123090a 58
    0x204401241c00c561491040c0c00c0400040203004041c03915418038a039210b0082140e08004005000c80c4071503008000c00e100059003c0f40e1150160201c0000a5550b13109200300c1040d003030200c044800394120f40312404540030040e0350718050356042c44d0b0702d078001d00b644141883c2400035000b60002d05000a104a0000d050140052000d40140b44200001d40d076501c4059907692510006208a6410f507404481c403000411441040701c4034403030060810754504405404080c0000507141c02c01071010340c00001c0b90106079050b032254075030260040b822940111041c0c0b254600914503201c1c41d1030800c4c020141d03001e0021071034400302d464001c84001da950950700d0112940c451501c101c2d181c0340c24060055140002c2d03e1a50800045d6143c59584001500c2501c00a058070b0021603401d458010b03080340a4080031780440c80b0060100d020700d801200c00d42c00c0020411100401051220040c000c0710311200d416990010008400e070340710060b9a550b01c2020081a400304008140741e180c1021000003010b503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559081555 1250 559080305 559080307
    0x3110a050f0f010b012001020f03010f080105010927150f0621210c0812040308060a270219021b03030403170711090a09031805010503010302091b03010b 67
    0x5079982840c0503424030b0800344507418940c98480503688610313145131b406180d900300c20341040c01e8032126009200b071810000000c100040003041c40303c0c110902d0011541c3c1c000080010780e98030000c0104943c040070140301c070100c10043c1c0440c43e0255450882030540038000058602080030b20382e81c222100c10104950007a02c5510400150f840e48003040701d448001d81a08094160300e42d225000030a0001ca40d020840c0c04032201c00c1c03820702c02c0701400d5000d5032004010b5074880b00a40002640c2038221411000504034900113071060030302c07404042c1150035844102521500b2244003401000128002c1206907a09100d04040d10a5581c2c888541d4501c40d00a8141e0303150390324414048900d8124294082c0c1d008001c104001000900000301c001c07010548a6260192843c20902c44c00b52002c4140e448410b51040c40401110f070b80c409800c0501c00d454000f400805501401d8000e58a4401c040c00b03c0e00c280010409810f011038900d03440440300000c07903405000f14010300250b8000b03070031480c07403404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559082805 1250 559081555 559081573
    0xf0420060d0e0712020108010b0a0306081501150914060901120f0b1f02030307030c0314010f140a1d040201110d050415020309220f050c09100504060c0b0403110a05 72
    0x4418002c0300081c02900c0301300d601030300c80340d00060068101841203a90348400000c0322103d1510a078440405046843c00f55a01e2100a42c422801c0c0d16003070281c7c0980f07006070301004ca503031400703400454101c3d40c040c0a40c0140d4038414042041580000120a05000b0271000c8149200040d00c100300011401010000b44060000140a040c8444480036164442040806144c503600001030b258818024074000c0765030411004101d015061003003a021800803079000109604101c2c0d152076007550501001c1c00400201311080002c0e4a08a1041490108032800f40c1c0440764403928060341d00a0040c18521a0b90b40c036000c281c0c6c54a80308000717490003d000032405000d0800710385540746080010344019403c103102c503400981000a0400d01c0d0b45150500c841444ca858000d400030000f81c0300521041105161184215a40d5440f01058038852701d210000e04400b940103000351029241195070701c075016045965240f101e060094816030600c1305420201c4540401082240c0c0340034882e1000d84682c070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559084055 1250 559082805 559082831
    0x15100c0c0b04062006010e0c07020603091c03061206020904060f080d1d09071809020a051905030c07110409060e030903010f18021932090f0420060d 65
    0x1814080030420300c0350f03020b400011003c000040340c5047d6160310000d950107480b0b04440000a100d024002504a0004020000042e40c041179080c0903010a803806021401c1d08602201165941d0081c0042850001c01d1000850000e50203480410809080000c1254482c1401d50401d00e10741c3c88103100f68003c450704a00300f9440180d940520300d101518540000e80c1400060f400140200081c08110004070b0421440c0306a515800050050186c110742d20509420000c10a9000030b03800340c02050060251081c851007001100d00c503000900e021801c2042950301c441603900c400303440c01d501c1500c40c070307100c0f0201b034151040c1010280346100942da80e240c50401d25003503400150204030410300d02034900c10500c40c62502c61420580c1224a1a00310340082c40c061001e29943d00505c00c81d003400121f0185840d0004005005481411510740004a10804100300310804841c0e4a8100413504c0c04640015060307032414400260590301391941911039404141c45420900c41c002c00d064607000c0b145240c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559085305 1250 559084055 559084067
    0x50a030e011701060e151303020a080a0c1a07060212010e10030201020c190914070809030a0c020d060207050d2102070f020607021f020a110915100c0c0b0406 69
    0x20308040c2042000c0c2c841d840c0c0500414840d10b82481300b2445140c405651710065105400020b0003499100e058000038000d2070240e03400100e020701000c00000ca04a880007800340f00e1554403071a001c0c090303402c1c256054070b00e030b801c11103004941506201c080c001032410300203465410000c214599044d80342005055a490025190084c0c0f17260300300d82400581da0100703da0b808101e0642c1c0301c041c4408409001008844190710185010345030407203000190300e003501054012045943c544980f078403560400e644a204650403400454000191000141050400e0004081c0580c2d401803c0802c903868850a1908195075007000840b035005058181c076200f0841000008003007070031401d1052a0756a5030f0641d90700c0501901c1054041400021541d407030319611040030005e030305001c15110459029540b512060012035035130710803892180c000c2c144005400c0c8944005a0301502401c60b03042800a00d02003c00d01200700b21409100d04c001c103486146000007080c0b80080700e583c0e039140020080c25 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559086555 1250 559085305 559085327
    0x928061e1b020906010c020402030405010c272c1314070b0706200403080d05181e0111040617060f010503012c0403020a06051008120d18050a03 63
    0xd112401c0000c80922800852402100b41d054840e418603484607801a1070100d01200000d6119000004000030170206400642142e01c1d151100504880140800050412141000c081c0b00d5562207081141c6181a840d507042d221219004610040035030203017141501046840080a141c6510114100142c3d41c61003030b03a07180000040c181150601c00300454030707c10361402030301c02a00d03506074511811240e030f01c01403148841c4000035922903413850320b00f4444d08503a52148003a89480006000000541c44c0c010742505030317101400f50780f001d00034202c0200c04030743c5181950390f5842d408550b502c85004010805000700d82c1312586a041c042d5415a2003000042400d401502d0a040503e0b180e60070105482c15104034400c0c3c9022243c25882803100205903100c80e41328011140140401d05401007a218020380c040e050030b102540c0d5403002c80c40391138554401c100169022054140c810403c25001d000d10401e10580861a005138004aa0140b0400c0d6810303030701074014420201c1019007204006103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559087805 1250 559086555 559086557
    0x20030f25020a030207060203130b03100807082b0c0b13170c010509010c08010b0a02030d02030c0702120a11040c021f1b030614060c0a020916170c0928061e 68
    0x21421401d5005036040704038602c0ac112110202001180808114100842c05490b50500f2078500c240c0d928651a42d03038021600ca11440f8405102180c244240508410f40c42c080c82d0300c604210030741c4d0342d4446842d03940c020070304200000c44003e04400141015003000c141c0a002c40c50f0360700c410602d080942141c401603c812200e0785041011750b440c0e034008407044c1c11203800d4102503480e03441e02d030b006905500c18104035981c40c0e8030000800a0701101900602044d50094498190008000d0003003643c6205424002c0d0100c50514200f41081c9069040001c1c07900d040d205039081c1d03120929000701880b00703414860388196101e0381ba071aa1103600c0f240120403009945000e00500d0300e003458511005a80484940c014a40003580c885031603000c10403507020340c5d40030348803003014948000801c0e9161145030221001030070001209264942208000f40100741e4032941619100c0658100003204085c0f4401d106c45010b440d80200803076411441c420020840c0362100e00b8016003241d6400d0141e604901041c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559089055 1250 559087805 559087807
    0x5041d0703020603040302030c01022a0d080a02180d150c020a150c090e0403030b030c2205101a09030607111e0313140420030f25020a030207060203 65
    0x91818800080003000c481d0140d90070340da02c0c0c885080c1282180b00c0ca0700c40b680c440d800002d000703c04603c1c07003000c0c0a00c0ca951a0030300841004c5070785400d44810700c54105a0008514401054a0544aa00418030300746c8036100540b44d0501c06001c240c0c0c1c205036031815580540001784141c0b01c80514000c0d040e424406101820108446a0ba404503061121510b481c003180d0300c00c03c140c407050041840e80064001e0005400c100e290603e8018050014400305174081d01030f2070f00366101420f1103a104c001d03640d240c00d200030b100030340035051100a01009200c1d1000c60054400090386049e0852008200450301003055038465052050601c5d01c04040c0c000810400d1a02141c40b009038007168080c4190541103e100d40d80c0e207260f442615500074064201c5003c00c00d1840050115940308040003003880940382404003500303030351081c500364140c9010811008070410002e003041d40c441d1969640b1a400b80b155020300c100d282d403e09220714260b08544050b911181401c010b060301041854000c00703c5100075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559090305 1250 559089055 559089101
    0xb010905100e18070f1512020903101512032d0e060c010e03040b0a0e03010621031b061d06190b0a08060c0423010c110f09100504 57
    0x56140600024070b8004801c402486001c1143d000340040d800818602d1071020340d0944510640b9482c0d002c071845400842c00c0203403c1600c00c003160098940d0708400801030103005021100c1c08000e05490741e40d02e64003280004002c01c54941405030310803018000d46d201d036aa0301a004a0a845815002e04200e42d22185403200b05455480811381c00078101c01d503100c680f58040c21400e940580300ca00741000507804013150109101c6c2a0700040c20111289540706e032200c1c5a0b000506089588500a48110031300402422900036a0074100c0c507101846444c10a003460032a0ba040741c3c0e0080d07402c6045941c1e0703854091000e0403442003400d4011407111003010f061107003081121009154002c014800c0e80c0da48a02240342e0b0b5650740714200c401003216000f51544d034a00147c2015580c0c0c0305018141c00458008420f04444021000f0f100d000d01042c0c455084500c110744070007170607a100c40040350344200e200c03800c902a52a036078100ca0103400c490220040b00c40c01c2ca804c10003030340d00c1e10b0b00661003a188007142d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559091555 1250 559090305 559090319
    0x6180106180b041b032f040312090807080a0b070305131103070905040507080607020d021b150a03151a030a0b0d0b0906010312260a180b01090510 64
    0x4510740e001000400160390031440b0204000c0e2409500c14915120041420540079815802540500c0462002c21010303d002d16112002075840d604450f01c1190180028030010710801d000c0c98020409003840d08085941c1c01d03480e407030000243c01c00c0455030010405a010131461803a0140c01ca101403c060110740340405105100c0e030680f100107000ca40008045140c41e403014080707403014000070b504c24456841d05091281d138541041c0709603d41d5125031000208481d01c0806c0c00d403000121540074054030f402140c4000342d007030845030b14164040d4141b20360b0200626040010415841140c802040c2e10644082d81c000680c480c4e4000100b1004100d041c404400903482101d60045d00c140000510a121b400481d0380300c55001d40080401c80b0030302c02d11404940024046040b02e1050280075490411140c0454003ca059180010109100300049004400d00c000b030a0f8440717144c05001442124401100c1c040e64841c40050703800006010041c040c0c40103500410b03503c40700b2903403c00c02440c41e04072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559092805 1250 559091555 559091579
    0x111040e06011d030a081201080a0f060903090b040303030c020c03030c12030c04030b131509020d020d1103010c0e0109090605010e060f1c0608010b0108090c0d031103030906180106 79
    0x3040718100031045020314200c101110380f802ca402005001c4452000c00783c039118455074014114a4000c1d80c015000040a20b00083d052005550018003c40700f00704960300d06006d0708590784100d0504c807441a000c111104550702410045010b9a80404e0f1003480301806030400c00b20030095802504100032174a180000061000704010a00c040d035603aa6030b401071011194061600001e10354092602480340d0907654015040b1118043c1b5aa82d81c2803c0c03d11050003282c10009000750011880851280507180100200002c1d600400d20998891845000a0301f103138020500303240440c3c564401c8450b90350303000c20b41c00e01403d400c078400c1254906140028148241074950720340300700e0000035030b41c03031003c0181c007a900c0c05801408502007145200007103001802d02c42c05011720760b40c40d04102d090598442c2542d0740c040c91880c400b0b04032000000f03051090b00c202101098081c4004400b0202e100d040c100001c4d482242e5a401500c02d0b428011811202541c07445008140d913030601d1000c0c1b05038a0b90003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559094055 1250 559092805 559092811
    0x80d050601082221090608090601050108010b090d0b0705130f1d13050106080105151816030b180136050709210b130b040f0620040303020111040e 64
    0x3800c60340d0f10301000c2c640800c0c400c526040101c0b9004c880368504404a8012007002e040d101c483d201c0c07541603903410500c00e41c0d45800344035441c0001d9080d8010030010765500010084a640945072507140c04c59a01c504400f0007042d10100000381000511b092000b0030703040c1403405444c540564040d8a440d01c01c54048071154401071540e085103500200f00110541a20b503c4421384c0013000b0302101c0d540d15052802014216001d624030078004101c0080d81c80c051031001042600c0700d459054648428010ba5008000902810141a82d811441ca82542c07091030800840ca8074000c06082503041c800508250540003c4008a45040039002d8601140c1204048494465484001a155291a0125005a00395010b1201c2e80780f45200c207032814001c000700d07021441c0101c0350f8806a8854000800360010103420160013003200801180c0051440e83d1440c41c1a030241102080f0606407404850381e0781120460300b10700c884005000c2080580a0040d844c0c2804842d10352030901e0320300520009090001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559095305 1250 559094055 559094101
    0x50c09060102160b070501050105042d020409091110170106030903090302040905010c080603190305090f0405091b010504150e01090312050903100e0a14010e0109080d05060108 77
    0x400181140c1d108000040143c82c001840080481d41c6458440c400c0e4081c0d0801e6605508000000c12541440d01400407004101815626240e00409103440384406040c41200b0440d020000064115154020103001c0c5000b00440310010b8000c008000000000724400c00c10321059039038105001c0d4600402d20304460940c180402c0d215168030301225003410b03d40000398803e16143b4000c0070300005610920b81034038262101410713910348004050740d440700d00800b10010721541b001000028418000342824000181411488103000c00004040c0c40088401b40c0c4294402e07582070a00a4800b24194483d40c000e003041880c046c1464800045000764264942c20310211550348041c507482441c0104c000e40c1c010303404400761035030068010051b0307000540d860300c20320032040881d21410013849106248042d040040c01041000c0c0d461701240020050003207425503a030300f07a0101d451001c2c042c2c58402d40c81405003d42d40d900d100035100c00c13100e014011030304104c018810030002c0b9040c250f11683c2400c038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559096555 1250 559095305 559095319
    0x6080703020108040f320c0f0307061103040305010e0d080109060b04030303110c101a0102012307050403050d08040309090e060403030e03040504150501091a0a050d060b2206020307050c 81
    0x4030303081c0a0b117150248080f08034044013070022410f0042441c40418408060402a50ba6001008040207809408d000056038183c000a208020050140d07141044101901d01640e052690720b23250942100e02c13948440280342c020881d507804180d800700d45c7c513003d4800d03810b040000b5070409002c1c801370300403404028149a035030042840c0c501724840c00d0b2080b03000f200302140e2200800c2d00d144005000c1c080b04000c1c0035090f800144a417503006006d070348900c0300043c1103c1014001194810400d92000c1c00e00020303c0300c2000040003280c070510008a0707021303681d260b21106007402d00c1e0081c282040d40d0301080c03005c0d1802042e9801c0e031001090703103074229400d4600403072104d00d40400c9500718801e40c0e01807507019160800c0c4003420f1040054031400c8842c02d8031100040c4e5034902c8141441d245540250801140410030100303494010000f6000310300c244040000d9039902c811001060b5800f500020740c043d40400030000c81018010303042005030045201650900380341d65142c3c5c2d1780d400548501c0d41b050719 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559097805 1250 559096555 559096583
    0x3009050409020a0302270c0a0c0b04020a050a0b0306031006060c02101806020105041202030307080f0a20270102030f0309030c01020f03070f0c0b06060a09270608070302010804 77
    0x148102d42d0f80080c5130002e21000750b100c41c1000001280e038946446107001801e1a000900c002e0b03a6500761000075003161582034000b020340d540d041c04a41c0c02841241c0c04001c2040114154a9a20040c009802d44012459890509034201403501a90700c0380351040504090040c088682e004039a200d0340c5a050b50b00880036442da440030790348000791390071800d500d20502400040d040d5054100c40d008601070b007040a0b203840469000c0746c0701d01c0100d03030b020081b8071181d002c50805441e84030b1241c1d025a1580d00059941740340721f0300d100305031591000302c80c0b0030101040b00c07005140315050f0b020149508818041c41200f05100207500c9014540d82042c1c4101c01000044a03880280304403000e89080000031581e4071640040c180a07904280c994600048041002601e4030f8050710003000c80640042c03801041c2ea5807030381080b0060b441200140704001700301400094001c00d1400e4000220700800201402c00c080c0f007150411a0396540c05143c15074400f243c00c00151f40c100740411b0300700d030300304d400703003600351 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559099055 1250 559097805 559097809
    0x40303080907090c020a1b080a0807080708160519110d060209060a02010c09170606041805010c230f030615160b0114010e01080c030604110403300905040902 69
    0x342e600c1d400128040c0c108000540d095a0216480008078070414803500214003299440070040e400380102c03c0f0700e0303100116080211f10010040c0201e0381c4582c500360318048140c1d603101c009402040f003403160416040072880400100388041b081c00e210034030203010411000c3e250221010400120680a00c000f42d40f07890502c0200d4048803080c02d40501180c1e43c9140c8984001e00a00d09034010800007400940045565040c0038a140200142c040081240d51507040401004001400c400426003c2c070310055000184280540181c2e0b40c40c40d1202c41800c03968038500c0c004008058884201c100c020032105407401c982d2000e59821240070f40c1d010109403a1517149149a208800000d802d0074030b96420310341040000b1040e54141c80d00318001c11040c00035100150707018840c207401c00d8046408072000590701845030000e1680048000c0000c240e06030309401c6540150312030340040d2165116607003903e01d004940d010310341c02d41d51082c0c01454a81f0181300001c103401c0c1d0070301a80340714a888609400643d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559100305 1250 559099055 559099063
    0xb13050c0c01060b040f06113c011e0c08190e06190f020712030b060d1a090115080c0a02070b0a030f06080105130221010c120506060901050403030809 66
    0x705446100070070003a91500c60100031030b001441190044010200040350403071090714401c4c0d11000302001040c0d41c4a500e820381e07119041040207000c150103800641a0306000c07405e4004440381004000084120980a42c5c40c0702e140054103500b5810700300b048040d003140c0d00540f40c1d540030038200e0f460600845100a500c0192203041d0074800c9900c612414420742002400e203031142009250020050b544c20000d510050f800350507006002c0e4200f954507074204070302a07081101c1da83e00c024072080c40c001440d003210003100c10b2411100c1c10702e60740c5854000c031403c00010013130242c5034084a0510b510008400104061001040c02400403004905032089074001c1094502500e01c230740181e81c583c116240010003c003016108081c1450900e500054040018404d203401130300ca408800c1c1040c5695000d0140c500700480d00689001c4440340b0310141c8880070b01c10950300e401940e68001c184854214503200b621009010300384580020030407042180e803c0411101200d030300d810300f442c080c1c1da81e103641410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 559101555 1250 559100305 559100317
    0x150403030806120102030f0f010e190213051002070e180c1504051f12060501020c010507020a0f1e0f05090f1e0405031b280c0906080a020f0102010b13050c 68
    0x1103600110034082203071900084144200903a859860803130f0303031341c811a0380040e0b02a2181e81400700412180c034bd9003059a0000c02c45041c0104e1a45244c5a40780041080c100b0741c00041c1700181c102d52020302203031304640322280e0012664101100b240403992900d544900e9903050303051280d0b08003625000c8110464041d50002c00005100d61403c00e620041d81d0701150851000764001204904200303091048c034070800054403410790003800d016400300010b5505921400090364400e19071a4005003400ea02044603009e00113001d110b02c04458440d52900c400c664035084860102c0c0c4d0180103104a0f00c9034580c03d940300814140640843d15820214507820040b074482d052400e400e4420442030000004c001c0078440782501942c00122080e082040e201c0440048444034a40c03d0781c00580398074181c40e0a000300354040d21641e404560344102c030f0004c441e602d0f030250303255070000c990b51003d624062810110290013030000b40071088407074000030011a0052400195180d6620100d86140103c50035074003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 559102805 1250 559101555 559101589
    0xb0310021c050103121106070e060c030c010e0705030c06031918020918070f030b01171603110102010506012a031e021005071106150301020906040308120105150403030806 75
    0x4203e50f1207003001041c01c450700d1600303000b08414080d0100900070000b4218852101a80c1e10010744403c0c608108459020b041c0707481b041d00c01400044000c110a2040030044804c0c80028101d8a280500303150a100134040c54610650050007007001d0404100d6015041501000c0c00140310140030603a00311074100c00030040d4000b00203000b044400c145640c405690400f032501110405913803a4401c01c640b0180f40001081c5d02d03030700e00042111040c2d15641105600b43c64003540c00801110b03038a04980b4880d80d000f5a10003203511a44822940c0a128440c1c01050a00c0c100942d1503000a0000c01140e00c4140007140c074800c17803048402d141c03041c5800e603d1604e2140c0e850044402c0524025610001640e200782c1d01071409000c699010300030b5140c1d80412041c10701401a550b10242c10206114100b01c43d0764065400b00041c4030645e46900040014610403040d060b107441103040038030f400c13001c141c0203180030703844a140f527140036a203560540e4110380e410700e0044400c1d610340010801007004244104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 559104055 1250 559102805 559102811
    0x90c1205010b031e010620010e0a080301061d06070311070302030607050715050105010c021314070507060e010917070804050423092a0d0c06021f0b0310021c 69
    0x1054031401100110302400105280071400300001c0851800c41310300784500300108a2003114100403000302418101c140c0314640000408104140b9030b00d052000a4034100e514110000c010b00000e904000c004a52448401b031000e83d1038290000f11b842c0344540e000180500c030100c8ca07aa505603104018001c091070b801b4054400c641403460014005030441c03507040701d00c3d55903a41c080184c400703503104082c12544145e540201e0051281c017480580c0c000d811018584c0f98403000740340250264031504034001d0480f40d40f0ba50b503130817840c149001210340c502e00c19070f1540d04000710100401d5200d00e98054944010100790756071b010070302e04071005c1d02c0740b40d000c140c000d41080386207203030904881403042c1c12040701103007212503545401c0401d0b1103244072621200e00b00b01c4a400b001801010303409040703248001402d0140e070042e8544807042c2d03031a01544a0401a03110032131708001c441240c010000b050009030381c24021101c05174006511601c071504070f508030300d501190841c0011407000e085554154140c500f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 559105305 1250 559104055 559104059
    0x110604050a240f0509190206030f0c040b0a020a12081506030903040504050406060311100503010b09061c050601110a03140c0a08040909120903021c1b0f031104060f090c120501 77
    0x10380080d26040750706014602881c5006248110401b8038040902d0b8001d04192455640803000105000003511034811240240310106811041e00c004205109240c2c0003020300c0e140615012054102400d0208104146d040034849692611150040c00400441e241c81d2030303071b8400389028614007660380120390080c1030130184000e0014941c403038000c0e40d0241411061900d4400207116607814240300180006104100420150b181c11000e850709040c001c0115262125070004208460405003071002440d0f0750350700380b041561700b14505144115402c000380010008545010303080211801c11250118400a45600ca900c020b0144000c90b42d0303c1115140c60b9030305c03a41c6c141d0082100318003ca41d940440e255200c042401452420101da07030040c00e0390f0ba40b0072a0010110810340d002c4007243c1c566040c2d15042c81291320350b000000549040c510b54a00e00f490343c10a5a510896101d0303240c02186000c6090041c1180391401d5001c1d02c02641d000704016689107800c584d0400030300ba81c02c0202c0e21700000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 559106555 1250 559105305 559105331
    0xe0609180105100203190c050a02060729010612090203012307021204140f01030921140a091a0f0f0d0506010306080304060309080405041b110604050a24 67
    0xe441c1030b190150ba0315000c40b80540f40503662440f400b10401e01240b541d0b266040c0c0d841c4034100c0389110520920a40e1030381501c03503001c1032164008041c100c424645c403450524186540381c400d90b41e0305921030f404468a524080003c0d1916220f8000c800c0741580382c84010055403825000004d880011706031408580c1254922018202001e452078001801000e40084d502d82c089401c0e40c0546000040d000c044111003010030102c0120301d910a4103060f2116409030201d140e40139100313850000d05200b0515240038040003820900a407034100c0b00041c003030181c51080356103d020503090300c41941401d40229900744070304e03203140102c0c45203c240d03040014210000525440c0944840d516003442400703503480c0ea40c01941910064050b444055009010400000d0b12135080a403005e4000c440a41c0381c180c40354085000d0f208000764081000c1401a240420b140d032020603039061000c0071007e450281480e80d10252100714901024100f61448a00559141030100e89080d4065030250100706800203114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 559107805 1250 559106555 559106599
    0x403050322020d121706101d044b0b15180906030307030c03050a1206091a090c390d2616090510022b0f0e0609 49
    0x20340000140240d00404281d40c5d00c02c496805103400400c840b01121626008442c00e060407098138031a0760f0350364101010358480e44107420b01e240c0f072441440803040790b40100302d01c0c0d08030b5500410150300032600500206003003071103022010740865401041c003900160000300222802d000000b101d5800061942e03880003008104c203050b0340b041e100c1081c159240001c15480e8040d6140260200c0d410712102c10000e07110714002d107007028060802c80c5800140040300d03411183d01d604150151659045804001000c00e00039000780c031821909041c07a8545001c071030b420750140650020044071404105010520810a1540020b84640d80e8405405802101c2c540e1340b04032030144404100c40d840680340022401050032a640c180000d0080ca030303101c2581c82e40c6020010300021040007009140401d0b1a036820803c0513006170158010a4000045d401200a000e1002c503101c0c0045100c107000f6411a800c88511124480c0030b05081c4800c0018a02150681c4500d600c0d160344062080d204042443c0b030741d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 559109055 1250 559107805 559107833
    0x8280206070917330a0e010c030203040302030702010c0501150e0405071203120b010c06110306091506040302010c15020705030309070504090b071b020a06050a02100207241515170403050322020d 85
    0xc6c0c02407001c2c903001c100503001c03844155000b40050f00b0400241c40503502503500d03406290311440000400348600034000c82240000c2d0010403c060241082c401481000c2001001a2400003030038940d0441c10f0750040d28910640440c081c075140c68440010311680074542800c01d15800c20710074000c100040e13414100e69401111094402c0040c1d0703000c641481d0303000780110071f0700e000500802c1c82c2c2070440d0010f50310050b4130300d4200c40742080d2000f2450180158005082030900c00e1004503100c0c101800c09609100c03140c1c1046008919008801d000b0800c0050215000045070a140b40c009401c1141c8160034901d00d070b40a9040040120005240c0b40d10400506c55000b6907801c0d500021080c0071504180c1c4181b40f0702400ca0300d0305001244400d0150080d0305180101e0810000740e18520300e0002200d0260b5034040314040966510800a80b50050701002c80001c81003510001450150303400b0f8214040640382c2076200c4015040c0c07003022440d00702d0303c1060f1600100109500c00840c5002d0901410507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 559110305 1250 559109055 559109081
    0x3020405040c080709090f06080307211803060c020c0d08090117090c010f1707031409150f07020f030706230f0408280206070917330a 59
    0xb03158108461094482d640a00c66070303910214001d107001c9480b0068822492190b054560303031800058034110400c01440c00e24401c45580b0a0f84954948400700e401c3c0310b100000034014070800c8c40c0c400c0c1c4c0540841506480d8040b100091307c1c1c403c80320480c545800140c8440e0882c02c00743c6141d041c0140e02018114800099981d4100030051440b91010300c40c1c10b640d06001640021142c0c0d400758010b071700c0400120060325105001010003c014440f9035000d4600101107640d4000c4a450a8030710301405901c504507200034001100d525070500c0070814010000c0d081003440501082a5510074401e040656104c2c20450b0b803961154200700c40140f40c9518609800c02481c614150542d4480c0301140c402c242960390f5003440d03a1151103185003035200c00c8031a4420030686000d41ca0104540c4060070240030707a13900610251500c1007010701700c1d03035154005ca00a6548690042001800011003001107855100c09481103101c00e030840561800080700c0840c4c2405103810805249036070f41c040c0c10350040c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 559111555 1250 559110305 559110311
    0x60302180a0b04060303020316020d020a090b0f09150d03090b070317010503010605030a030305191a041104050f010509040f020a1107060c0b040618150207020103060f050d2904030302040504 83
    0x121401c000132552140310082c007580041c0649011405d00204082605001808808040741640e00007081710905810400c2c6050ba15050240c250515006402803030758103581c0351800703060108000c0450039104000b1403151600c100c1850070036100c1c6048500030200080d0140d25150146005420703080308185111f07035044068000070301403905004082c1100c0000d000b800d441e4802c0d440c2107001d41801440c3c103068030444103041d0f50344031440c071648078020b0b4182071035100120705008210650f6800c0d03280c401040c03400d01080c00b003503859407502059000c0c03d007800743d9160340e10400305014000105800405510104402c1c962a821083e00e060340c11880c03064440c09a2180b00a9921141101000e4085100c1c1780002c0c00060540c2d00804900e903001c11100c410080c195111030070340001000e40c00c11103070041058421541c142c02800f000d054154039081c205420a804145460004000a8005928110107601c03032038410404003480180d50644989901c0c2504014010750700c644900c4e4080c0b40707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 559112805 1250 559111555 559111571
    0x20705060903130e101a18010914060903010b0a0603060509010815072f03130503120313031205041b09200d02090603040605100b031315060302180a 65
    0x207400701c101c4600399140002030020a0405020120700000189500420f10a1a9020070782211007122943e456010140a035601c0445040a22030741d107000c1c4282c1d05020400c4011701c07140d40780d4814000d00210a595150f1120340000c002409411002c8403160011288040403d290341c0c5500001c0543d0025501504207980c1c640304259030744484108486a030f610b00000c5a4450310580f406010360a654641c0318180c10b62020541482e0750340603a03507840b5400002c02a500001d03030350402004000840c050586141107131200b0480b440006c0c88000705a21451180003010b00030b0309040c4840f2009101041585002d01d0250b1001541c0050862040c0c40c0f044002090000d9000c0c4550804040c0762224148040a1a4200b15005007198080c9543c00f44050b0b880c50311600d010b1031003240980b03804105c5081c07500d01128001d0300794110030b40d2081d04100b0091000c00b5104c2c24441e4a42c0000d01c018803088000180c8024070b059000250b00450142050090540c0407442c035029400b14082005505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 559114055 1250 559112805 559112821
    0xc030901020f030309150c0405270c0a0c060203040807050a06050a050a05271002180a050f030712020a0f080a020a080f0c130e010603140f07240c02060d02070506 71
    0x20004907016035141d84201c01c4101c05494281d03a21f60811804540d0b20700b00790315000010408141d5030f444048005404040b804141c4821243d290041260600d544c9003880e0008014500309128001405580d00000410300b041074040840d5585034016066601c60040c030f26045c40a081c0540d158404c0c54100f00103d0701c01c980034840c16015030300c4948402e4a90204141c807030f4410715190310030320715400303810204011041c5500090813800c1c140c4c19101e682d0020070041025141c0580c00280c0901c1203641c1084c0682ca0000d00c1900b5030752a450b010141d11080d10005600103184e8006d428046024000040c40c80000035800c82881c3c4226140e07400c02d5120001a503403000384803510040c5900c940745959a82c2841d0716504000001d0f5140400c01800d14401107080d554590700031035a03004902075401c0548024801c03501c400c0b528401a041e0280f402a0000030140000c00303070040d40d04808042081d00780207181c20000340754040d10701360315500c44260400080d0040442584c07613015500004803d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 559115305 1250 559114055 559114057
    0x20d0b16031a0f0301140a1d032b060803040e010603180201120c0c0203010501080313140609060a170109061e080607181706071205130201030b13020c030901020f03 72
    0x80c4005001c0d07010089000d4041000d40c0c0c610705a0141c16540e030300c5030404004104405d0521887d2240390111b015056400e400400742c89102a40c00d054005008503020a0070b8031107001001146125503002c4050000000c0b80140619400302c5501e200003e00014407900780c800240c12204552010032540c001c5507a0640401c9655400030b001880c014224484224030b03900c00d0244405a16250801401560220b400c6a5081c0c000d07014a0740702080344590001d002c101140907100c00c00c0c50070506200040480d40500540c2c013142d2082002043c40140e19100d1a460b240617001a1501081e0307586d1024180000d081600034024052107845407a156100d945c1842000c0302c00c844010283d036611071a08403509442c298a01281620f039410004032801c4085442d46040304410240405003090400901a00c0010341c801d41464203000401c0400081d40c0c001024198082c2408a04024202c000400690f481e016100d40789202159403001c810002000e86009034081e001c407284060b044d9005996 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 559116555 1250 559115305 559115321
    0x101101050a0b01141806130b0403080403110105040806011413290612220f03030506100e010e040c03150b120906040b1801090b0903070605060901061d0d020d0b1603 72
    0x1030b0170040d40f00010a81005401011100390400040110940b41c40c400e040d290f110394001c3d0b40d10031000c80c00b48140000061000d596141c00d092481c541442c244810362039071414400ca001e9820072941250f140e440300c003c500c40c03403d44040e0400440ba0100384102d032299058020090307840a5008098441c100a4100c50107220700000fa8415541d40c0d50070902ca85c09030514070f0500300310024801000940d81c148a0100c0ea1003902c0c046124a81f0505021488144403042d43c104400002d281e14140d8210310750303514240e400c0c1c901080c1901d40d810141c010740701209010403428111400050504104070240003010f5002c5482c1c1081c0e2214819155114000c4d2405801d00e0500302c08501032414405054050503a0400081500d180540b148066001e040700c040440d508000703410003c111480c8540d0354012403c44040d541035040c000001d01605070400848a0950b06da5019440380c0e440c44001c0d078031654000c040c10b04200080c80c1c4080741040075141c1e00c10105026171820210750003400b400f90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 559117805 1250 559116555 559116577
    0x80904061e08161707030f0f060b1f0503041a280e0303071211041205010506090c19090f030f1e1a0c12150312120105101101050a0b0114 60
    0x850141084004040c2d0b44c400000b1507194031480c007000000540c0302e9181e42c1e00d240a01100c0c03d5030300c102e0908206030307103843c0a507600c94500e080040302100d003601040e88ad11000d034a0041d80b00d645505d046c80f9040e8a24850302004c00e9188100710280741244c1c908288040300f540c004090b40156801c00055402000d00c80e40c0301d0b0030500008604612076045201010395410300801c00d03443c00c034444045e03944141c100c0e00d0800c02d14840c42d4140b010034010917170424001c1d0341e0343c040d03440e007030202c6000c5000b0400c0c2822010320050061030468811218a4098a0f500c0d17034510b491aa00e28007071500c1d00014800320b4001030b82d44d9007100a800301304004030120790402c07582450568009414030700d6400041145548a000b40444031080404068152040340c0c0c445208411340a0101058078044103001c90304603d1f07004201e40b200d42c28030b6416003030455900f80c0b411804002544001e0b54200c82d03a052880d901d40c07034141000122001030700040c54904080e2a000a144201c01016170f2038451482014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 559119055 1250 559117805 559117843
    0x3002180a1a0a020a1a0105150307090620150f01170709021b0a0c030501150b0d0203040f0b0702070303081308121009140105040501050a03020d0807080904061e08 71
    0x240100115000702007850b0188151041510700da81c500e503400f09101d10004254942c100140020309000090300c0ca4072003a00b40e410b0451038000c07070040c9500440d0103200104080009400750204620040c0b44d10320710210261542e44603449928146900c040700c40a8094161a000145070742c1d684484076095114038001e000680e04017010178006e580074059540203070110f08614410400280400204144a1640c2c0c440080c61410320074255410001036590040ca24681000b8000e6a2011120714907070841001d80c0366035841c00c0c084d0140e080d040c0c0c05880d60041c8c40410802d15800b14600095030310035182c00c0322603100c01030203403290506444010322a2a042003400c20480710101d04c50f0b4040001e1100c00c4410340c40f600b40c5010f075000610000c2c0540711480052205113428080c0c039024000c04e480d200d81c120721319000200140444000500708201c0004d00006028141e800c07180c40b060b01401c1444510399500c000d16401c11008400000300030444004110b4507800b00e000010580040399030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 559120305 1250 559119055 559119089
    0xf0b0d11091e090610020a06020306030a0b0112060501150c030c02031212012103080604051807080703030201110910050c1005010e060301050a0b06030a0c0507060903020625020d3002180a 82
    0x900950022f00800d51620440030b0400016490b06001406400c400030409950065864200c040c1c81041c1c104440f60307880449045201a031013152144026014a803040c0e2412090001c03a060142010300c44030403080000320680c030a9050074a4604856011b084c150b800700d0240c2c440403001005d1800100090080d0000c0b40c3d1616080d008035811803900c1c4c036109242c5540d01000c034600503043d4469065604840b5040080c10380a107d00892140d104c00b50030b203400c44040c000344956003141061000d0110204035645886000c110400a610b01c03240b0421855854641c0440070003070840f1814440d60904000031403040301800386c0440740802803c050304540325609900c010b020907000760700c2040010700c00440402c3d038a0107901c074014001d4001e4411400e00d095000b42013602c45c06140455000c1202c0c0000d41640013030941c00c60340c050324020780b5440340da000062102c40704c50a8845045c1c2e01e0303d1140c81240b01a07008110170350000c1801242d8018a00a2124001d2540710300c9451413104044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 559121555 1250 559120305 559120313
    0x81210090c020307140f060703050907050301060b03131a0c0712030b0906060f0f0f040303030528020310230a14060909060d0f0303050403090f0b0d11091e090610020a 73
    0x405c0c419440d078502079942880111852500d8941c0444504001a4841e001d00141007010300080004c0c0009400a1280905000541000380700150440c03c0b002140b4402405206d4950101500340c00d0303504030028181001d031203c00d81da810070141982d0070003400f900c03458000e0013031042181e12280a4540440c40e903d0204001498114202404080c00c0401c014501800c00c04001c007a60701440e01040d07111402c42c04c00504503480104111b00440503940724450944d8071044005e51305000000c00341e642d5941c0340f003402c1e20a43c1e40c0e1110001c0c00255841e110f0044c40e034035850042c01e0054812040e519610314004035400c013070701c034126084001000341c04440c1c10801e424981c085d02c09007400c0b40f0324030b00c4c1ea1202c019140c40b0800360006650b48050100f01340d445030b0218020b060040c2e80109550070310420f01441d00c110390360001a261b0700c00c076020003a8880d005603006d01100400441c0300403403005036040c104044c1441584a15a8080000c81e2841c10b9103203681f000c0310f1035004203d101b8031903807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 559122805 1250 559121555 559121573
    0x908100c0216030c0305070b030f04080a09050d0602031801050112080322080a091a1227250f05090a06030210110c0d050c011209081210090c020307 65
    0x1109801c42c058403000290303080040c00400000c500c6011403900e590300c0c0d42442030400409811203254900d00f04140002c6030310f99400260810b410000f40ca95448240c0710544080c00c1030382c03081c0d40007284002c0080c280310040e4003940c0304048105082030134041d00c000312400c9074403d01070920072014600e03d00c1c2c04520a600916485052050b040b0095a01400b1580d0703003104403501215941d4001079a5030000303a211070010000d0401c1c00343c40008005105584000f8040c41903220b01035480c88000420700808401e03840032020071864900d4007210310b05206c0740c84080550300342008a402460300954005050b415004450302c0d103001c044038900300402c021609401415400400d0b4a403040070001d46c2c0c45d080d0b08040f15096484032440d41061980690824841d139840d075109180c1c480d50780b000b051000c070303068040007424a030074204c4003c0604150000c0500307a0b0080d040c0d20010a038503007040800c5c006c080c020b00d00e0480301205269602140f80c1503030001c0240d040180c009000e141d0000c0c0b20f40e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 559124055 1250 559122805 559122821
    0xd06180f050603070f061112070501270c12111009050a050a0e01031202120c060a1404112701030b010501080f04080901140f030a0518010603020109051002240f07090810 74
    0x2000307072040b190107464148d43ca0b03040814207543d00e035900c0c00f05c500c044440e800e030141214110031100e41922a252660140402c49219084d00090181c80c03107800c100c21012000703504207009080e0124030420100080ca22101ca010785c0f801340c0e2100c2000310302e038600f00f080c11086a4900340301310b4061b801e6907a400741c08141d040e80c000641c800d040c0c00e17603001d0780c010001e007990081141c02040c03240f43c50001c80c1c09480d01c4007803a800d000d05c504140000b0648030000a12003ca0a6030302c1e40b1440503920800380c010007201c0c00c3c60800300c02d0400100c104040c200e82103040f660700760b03129401a100c410100c0840b40041d40d00804484082040e43d15a5010ba0300e014503038100400c140d81040380ca1400303034500d0b610803036031215816580ea042001c10f49190008200c5100c40c1c800800070a800d5500103020001c05d0300580380300d090003154258010b8070130030150307036100b10000c0070400080700c461101415481c2600c10b103006c210480002803916104401150464100c0b100400c1e1100c040381c0c1d0800101059 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 559125305 1250 559124055 559124087
    0x31706040b0d2904050d031d03271306030c0b03070206011215020c0303070210021e0304060e120d0b01030203060a1e030b160207050603090705060d06180f050603070f06 74
    0x2c445240c10718200905568030560044000c0d01400342c030184010203c55014510260b803045103200e00c0008c0304001f050780d14044240d40e0100060075042e0458844010040c840d5500040d481e810004002ca16040103081728030805085104507120061040680000c80300000180c0c4800e004109030400c12542c151203038040c40e600404804a0440715003030703030302203501215146d20000a000203150704015007250100f00c4c00e0b086062100c0d90011100c1e44c880000b08588444001c00840c040c0b05640d448041115074150032134803070344401c040c0c2c240150441c6684100c80c0749410030109855000303000300ca01c21800140111a55410024400120551603000408980b0701041c00300024281420090142418035501c0b141c9182d0418000d1a0440a13045140101400e105001d405600007840c50706440b0b04807401511802e0102c0448003d0041e03a1000c02104995a10045007aa260b4082600e440e01c0c2101403005a0301c120038035680394140e01c035800b6690003441041088038803a100c44c21a490030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 559126555 1250 559125305 559125353
    0xa0e0412050d02030f040320030a21020d0603021903020918010905060405061902130b0304140114193305040518210f07030c050a031706040b0d 63
    0x1030800c2c5049030000c60740e412104404505120030305804c11038000d0340c0d40c607803d8128034010410f16034544a019500c1d188040c0400420703070205901c0d4082e0380c000c103406200021512803400b001c400d4041c1149110903401851818180000007020344c0c0042c040e03e801400b2090540c4800030030390500e910b00e600b900d070503550f40c1d2100000920180704c201d00850042000303001c2818085002443c602841c030204030103502c10001a0099140400100115515002c1c02c1da282c0d902e9003032819000301c00718003ea403c2d510380462420224001c610190090503000420613001001851240c210b6104140310000c0d0b0500c0748042e03000050740003c5400e440c000030688039206541d40080350a0761015100740050b00200040c21041c80000c204440c09a000c3c2e0b81d00145410809200110600c241e00c6030881d2640b0000b40a07060501445190b24070f16840000c59590142c9401c005024019034802c1c000140b01c03013400300c0c10514040c00390b6101d1510040a00703440400c16074698100c1c0c0d00000b01c542d10403078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 559127805 1250 559126555 559126567
    0x70c0302031e091306150e0a1202030f070f140109081b0f120307020405130f080c2d0106090e0c1c020406120506061507060515120706020c0a0e041205 66
    0xc8128410364082c4a000c0049005c0c0d09040300c811051000f10444410014420004005903032440300882c01c1760880300f00685880480e00200e030a084407a06101481d200d650000286004485130103800c90303c2c9510a1140000f130107004440342d911030312500f28103610040c0019083c180b0308403016114000100280c400c03151400101c0c2c02d00c0640d41ca02012504040303141030a504060140a40c0709030114004210360040340e4540104905506000e4000b0101103500c07640d1400401c00202071540780b030345800c44440c0f003203000a212090041050099400e0003400a91000326010344580802d240004c0c2440780050402c5c844855a01119410f03d0741046514002689407845100c000c0c00d02e400d0201e903420202e050851612002506c0640185c107414a141d40d18040b12381aa03840c1940048081000c0d100c0803451103994042e81030072540096440000142c220b40014100200d0729540c0a035000c550103c8204007581109120b81c1d1141950900042c0000308520196121f005981c102542032030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 559129055 1250 559127805 559127809
    0x10e16060315152a08070b0a02070c14011b110d05030405131d030909040605340f0e090105010e06040e0103030c0605090d0c030305060d081201030308070c0302031e09 73
    0x800d48201d038081050800c0402201400c840c1d030b10005044e9840b401d0062007940d035070100500c00d40c0310240a84940d0000328241d00c082e48c04507800a82c0201c00d0718400f988a0781d840e84410001c00311140801e07411003240404910301b0034460f601d680c00888079004418036100740018200511000c0350280003c0101103a15030322065800c0066054410009201d03116045100403490b031110201c2e40c80d40144403603603460350381620080e0b2184c0d2101c0d0100751a192103108140760028030200701c0c0d082d51081c2015601c408a80801519420780d03996030f41e04052100b90075250502c0d0000d819400000410042c0b100d54010310350105c0c1c3c0300c3d01a20356807a19035a00881c000c085020b130400c500043d00980e0500c1403200c2c0d07004954204030307020050b003408006c1040c003a00758240040001d0034503071904c002480503070300d41800000d0300d504003040d00da0703c000441002d060765000b400114080360561010500b41c512030340ca0121400e5050b00203510b40f04030400080d0b11104181718492000c601000913043c03075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 559130305 1250 559129055 559129079
    0x103050618040b0601020705122d010207050c030c0d0c0b07081b010f150501021b030c100305090609010b030a0f05071a0a030608010b0f0d080405030d080405010e16060315 75
    0x80c5010707003081105401d20740002410000c0980c0309600c9410702d1024802c080c9c8020172012540110402071001c02d0300309601d5075078803c2200841d1011544041052400d00c03070007282204d40c182c0c044013525049002030f07080205261001c4d2016202ca001c1d4107090207008034080080001c40d014010140c2441c1d001e510303001180f4071411070911607944800c0b0801404800b400b5600c01c04680503410110b003800c000c0000e685a1002c11000141c011103c0b0350b0103561410300900001d03100251400d903450500100c05409804140c030100354501c201c0f000148800018400c0c00e00102c8000d01500a5101c1c0d61079001c0001c03042001503d160246d8140001c4258041d141e071400c2041c60702034691510580700d006030445103550301a9080741d042c54070103c0319541e40020404941e0048641005000140c00c0602150180d0341003150107100382e000c51404980c00042c6d15101e68072a000a105400e0300160f615210043e0351450f891400702c000c0c0c1030040030700039041444400a0081e03031000c201c0c1c0d200c2c006015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 559131555 1250 559130305 559130311
    0x1b03050a0e07060c030908010516120b060f0711271e04150e06090709020f0904020a030915020a08040f05010e1002041d04080910050d06030503190813020103050618 72
    0x20801306540c9130201600070014074020030100b0001c001d0740c54080d20000b0404c05c540f886500704805605110680003840c4c2c801403070f014002c0c04d01e6881e240010921000344d071020320305464a80100751f00c08154501960158240c0d1140059441c1e800c0004440030700341c00b4054054000780d05c0f4141d440c1200318201d60024841da004e1040795510614075207501081340d650303849401e5150040000c0103042c00703000038000200c03041440010303030300c0e88416403000c15070085040c010381c000c0c0001051078941380d240d0007030001c5d1070041003040180c1143c0940308040b441803900c9070b00452071050008003c41c0a4401c0b59402c2ca000d60300202d4000c0c0d5000200f41020b1020400c44901c990104051028905103040000400e801d0703413584401d81002d484100e01400f40c514030910075696040d0490b038241c46101a6201642c51040502000b5100d2800c90703101e4000241e8404c1c40e00d0a6171a528280b441404441c1c006d07001082810004040c80d0011809841300400054000b0700200c143c040c0b0107182c1c1c6080344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 559132805 1250 559131555 559131557
    0x8010207061e020702030c130f0e0c1009320607050604110a05030c1201060e09070e07080103210e0303071119050603010b0c0c0d05030a02060a1b03050a0e0706 70
    0xb03091649144180a201d4200e9500c0100a105121180c0144c9002928104c00c80084940403004244480c40f94043c112180360304442c80c2c04c0440c8058044000695004445800c80f10161006400c441c1181c287c5401d04c180b401d03100390614001e0124011030308605d0302c040344440c0b640c00072540d4004180b0545c800c441c1126550b00013000c00090151000e28903040180441d031210100e89098000f0382c3d0303810783c418003520600c96101d0945000000350b01c58002411020f4481440e032034801c0006440704a9882047c003c500c0d140f00080300b251242400505a940c4910600031403412400b03107094801e040ca01c604140003032202000f0301e1355010006001a284502011400d5010060500406210700306030403503286a117120070301042e07481109a030705503401c0d5412640c58409442d40549499a0482c0340341e00320b910100e0f003c05219010000703220281e001d400302ca056494a40c15a01221513040310050102e07803828400040784d01c0394000c42c1d009a060040881c03600c02c030303020704ea09009a0b644064 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 559134055 1250 559132805 559132811
    0xd08100f062007050303090f03071a0a110726070e0109091103060f070c0c0f0e0411100f0c030e04050c0c060f06100e0d050a082a070b0901090801020706 67
    0x10540084a070b0410040700750320310203400900d103010007003681c80c01a030f000280300700b81030740c011881c41e201081401e00402d101701c0d0403442080401c204445540c0103001850000c0d2a066000390f04042c00920308003110a200301c2e8600000200b60395508016034101c80c0f103014044d08000060003803c105219001c2e2101480001e0480c06600c2e19803901403501d01d1140c00cc0d0041c2080090000f0202e028543c025620301308071100f00b81501d13041400b481d0fa5003050001d00140840483c0468803245210b12440c4140c1300302114101d42010810980c0c00c0d040154000303818140c0511402e482030300da00b000e1910a0515000050043c00010155642118400400a404618207000507c1041100d41000710004601d03038038100303a000700d440909409010f1003400750b00070002100d07031140002808010340003801d0b150b442c2e142e860110704036403103014132840245203030049151002088a80d100303402c0c07605009103800d600d0601500c09503001b4015040c14001102c00001d60400280024450b10344250800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 559135305 1250 559134055 559134077
    0x61b030a0f05011520030a0503040c21020a05010c02150d0e060103060903030b060418051510081501090602150a090f0809032a040504060b03100905060c03090d08100f06 74
    0x45c1400d00306008100f0b1012401a5518851004000c1300e482d0807203442e060b56aa0307210704044003101ca165001049000241d2508414082858400c05420303100f00c4000c00d2955860700110381c00d83c211b0350080e601500388515018003403c81c43c0204280d4100000201c1c1001c6151590b0b41441001d0f070066602949400d012800c141d410301c900f02c8101c000311201401e060402c607000d4141000d0454150103183e40d140881d000e0805500c0140a4280003041000d44020000c5c00424290040c0c403502c0c030444400342034090a60103502d0300c4080c1c8090380e00800c1040400c000204166002901003402c43c1c0d59400444041201c5080080301ca6003d401c42ca6528002038080c180f030712410040c42c0103040a00c088614855022411044007090222404505520355040c503c00419000004d40c2e03040c8910480d08101040c640c10102c0c000e4001c0b0241e85031690351750a0300c49035100c1181c408070b0f81e07004007040f80c5d04140a9044c0c03a800558018030307804290348901e25440d501c80d13580c20120100c0c0c049080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 559136555 1250 559135305 559135307
    0x151f1d010801050c0d09021504060302070c08010e030d0f06030206032a040303050d0c020c19050a1a07030f02120a08011811041a0d020d0b030f061b030a0f050115 71
    0x1050041c61994003c105a140881c2c000405000d4514158000b03520f6450704030955481c04400c052901d0f0510340199a640d41d400040c000394401842162140c2e02c00c40000342003d018400c803c424403000000d14039000005412200801c030443e115403400ba5900b5010015894000183d07100c1d00b0380c945202c0341d40100804111845440030041c0520501c01c210910020390f0240641d608003203001008109000c0c800e5050342484500000c90350070a40b8002040b522007940c00703100003280e00603551001460346070490002400c40b0140702200c09242007000c00d0000e8031800e0f81d900c000080c1c7c03040d90410065104c40c100f0541c07280400034002404c2000500c00c0c0d581c1c1541c03c001c1200d00100422040a00c0015407a503030081d807088101e08180c05400020300da910904854805408500440d501d00f0b00c400603030001c11003121890301078810310158408a800c0060842c2c05041003140d5004440c81510544c90140c1c4010010b6540907111001e10720340c1501400f40300d02900003900f40014420812038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 559137805 1250 559136555 559136609
    0x21b06091507020c1e040f020417030301050a0b0304020a031e1e0314090a0b0705030c0c09040f0809060f0c0a0203061608060d0611040f0501080109020705151f 70
    0x1d12244086003014800c032a9000110390040c00d005a484241920500c640000da1420090b07003e1341050900d80d8a03941d4400c90b40c02481914200340c82000710001d28400d807680c0780000d01405400c012007070400d11003010014007460f48603200801c2c400c2440e40782d54030b0383d1403040d01c0800721700700c204046c0c0140c040241d116102c405096654a65081c00700082c0c46c024600c40d804510316450000c00916860320341c55012240010381407403000320355140c06528000d030380c03a03211034015491030003894841103892500780341d02405140c00a041d207107030301465150030004d076104409407039110354200000c680400784000904511180318000c0c240c25025070043c0350a0000c0102025105815100608051900400c140d50040e00c10f440315003209031145001d4000340003000c0003000c4240013140010f017400c0c1f910682000d032102a03031008040d991fa410f211007a406450001000750308206810300551640d010f82c03561102d40000108a2100c2c50035100e000b401a641100c61f409402078564a0036020750301c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 559139055 1250 559137805 559137823
    0x130e0a030e030d1b060b01140703020f0f060c0406030c0302091305091e2d06040b160905010e0d0309051f0e06040302010c08070510020315040e072601021b0609 70
    0x8213050304490504140705100341042900140390913500d00341414a64480c00c652030b000f0402d040016135401132410702030750b28191801c05043c90321820032400241c1e400803c10301d001c4e00e032094110b418242068016000390464200007000c0660034413542d801030392845038103c031014441c900000c142c1407042c411410801b03858151000a1612244032035108000101781040355040080e01f41041c00f070211f556280c12504020501e548038078818801408126200035015040305c0c42080c81d284d651400640d403054040c4541030110340081844201c0b801c140f0004031130075104e450009122a110b00028100b0128519006082d040030a0032054640d00038020600380c000c00c9403214101881d59000800203141a00700400482002c1198010071008101c40d880c0c3d2845044190746078a40b0301c2d1640107080d00506128401c038105001c2008005e000304103034054420b06407a594424030304100c0030101801036403100c2400d43d400c10580c80b00c080c05c032801c40c0320320080b48058000c500b040e00740d03246811252 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 559140305 1250 559139055 559139057
    0x1605010f030606050418060306020304030314090c01051806070218070f0513091d06090607091211010e0f06040803070c05030607080a092d05011d0c130e0a030e030d 72
    0xc00c50030f10449800c441501d048030100b003402e2812070351a903801c2004e00042e5200030300d40390000c4241300c10550180c10422003520040b040207100c0d41c4070300345079075a42d403956805404900f0820454148400c030003c8030825800c05804546411095808129540f4415040081c42c000410900c2411980100c100c5c180c00308618080b800c0401403c0415000000c0388200349011380d039411480000d000b01c5558003000f90708941a50418a4000301032034442c02e00700d58a10004100e44408208000140d840c0c140c4e0302d030426000c490040c0711600644000f084403112980c482d4500b8462240e40d0b44210083c0090100c1201854954001c3c0c0b404980440242d000248250071407410000196400b034000f0750b0086161001040226680c20540340d51041c000440f2004d00c40c0000b6803402c43c2e1040e40181c80d1034450b400030070075198440580d80d00000c241e190a10560490b000c10001440c003c00c075002c8406207028005542c90380780d40c042d03140006d01441140843c815800e511090325007403128080c04480d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 559141555 1250 559140305 559140311
    0x201060504091703091f0203010801060e070e0d150f1b050903060c070606090903030e100b030c0105090a1e18060317130f060c050610050d020d11031605010f03 70
    0x650b0352070800d159069840f4a0f4205808400034094134010030408980c4d091200300b1803021401c0b000084007941c400d020b00b0b000c660170074000090341240700110703074815203481c3c0e629219081a2400c00c0130022003039400f82d5030b802c4007c0a10015a0341481034850840515100240031a400341000344514680850241407150520400417140c802080c1d5940c403806e2064419520b0700d01d45800002001507030442405540b40c11100400c258050303208a00c0c00580d00c0c1103461903a44450b0240c29500075146640c1c04d900300312001106035005201400b06203000400c0070020b80e440d400041d100c20720301c0091050b40501c84500b0010104a41342081c1440c9100c00300b07000103415615503c154002c02610034005c030000042050128010b00c000c08060449003609941240d03440c580201000b0f80d50304260303118015034000c80c1c1030840301d4980104650014001100d162106c5d002c01200844440c004c0d035403018000040084c964050211102c40d145003190600036504141c00107045042c401008018146 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 559142805 1250 559141555 559141571
    0x20c010903030b0a06171003050111070317042d142104080d0c031b05070614180616241d120d020c010614031218062b0501060201060504 60
    0x1612944000c0380e0003c00b120f020003501c0351f250f10300c0c00c00c0c0a41d10250455107032800203100c1c6008040101401030281d5110b00c200001c803004145080c0d0117644c0140344145402c0da0b14904038099510861010b550f04002c80c04003d41c2d1075001d9000d04505144415410504550800e00c400b00c1c941aa01d0b4107100e603a900705418a1700c03c0360340d2140d650000b4144402c4a81210400d0311a0306c84130212000c69a010800210b40e1034121b03a18501d030300429000c601003200b0a0110314402d802d4580e00081c0e004418800035140c400d11840d44d0085070451121500d410743e090110340d17034a2800c0e000200d14440d1040104005205008542442250001d5100400c180150300680025040b09807106e8180e120390f202a039001c414000d00c42d940b45880a94207040e00020540d07454510b02540a9066083c0c40b444050f110703c843c4140300300034481c181111040011075007810200c1c040c0c10651030800c0d000300d075040d2100d4111400e595150307521040783d44590040c00001d5082c0200c4000380416201482101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 559144055 1250 559142805 559142807
    0x18050901030f0218040b360106050901150c150b10050d0b01030e0c190906090b10020d02060a020f0708030903180108130314120907090b0114040311011101020c010903030b0a06 77
    0x400b000c0c04d40544207c0020341842d0103800340642c03084240d1840d080c819441d04034015180a058140b260382d02c06c6400c1d50001600390100c04480300c203c40b1903078404980080a6413032650390481c803c04d40d0301040d078a0304640d40c04e40303c04040e0340501034a80c40d9941c40c0c072002072415050300c20000c081030401d4100402101c58100c005682002000c0440d0b509078030007011400c80417503643c65803103d80101d080881c0007030350740096030040a106800741e40d01c65400482101c00da83d01d00d03001074600d00503403084000990340482d03603002d040002090700c1ca081c07a0400079125200c130341d00180c8185a0980001541c0d60a410240c40c040ca810b090a09001915203403c03e5401005440504007901340481c030420090200300c0d00c002c543c803061039019407544500346910b11660710350707181c01810812450031802810940c010340f00c0c1400030300396040e000d01c0e160030f690315030340240c81da00155418002a6184080341041c2030010740342c000b07404800050204002c0c100242982c8811451a0145509040500c0340c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 559145305 1250 559144055 559144073
    0x200d02090411010212040f0f090c1b03140f04091b0905100e0d0c1a04270f0903080907121101030e070b04062d0e0118050901030f021804 60
    0x2904401e0b04403440c010000140d04044040b1000c140c180d10000340418540043c18400080d1002103242c1c660b06602e4604010442c5c48240e030203000b1401c114405803a00092a01c050603c0e0707c45d2614100d01d00c059040c038001c0d504100013083c0c03120342c003140c02e02095907a80f08202c2034031421428034002e03241410003c0c1c000e4907140200d03402180d418030700528050103a0070310315048138040c2ca640324406103820040c03004501406496201801d00180362815500003055134240c685c6082c500084500c01d002c4204001d404890b015003640e204c04005984c05018451040680e0080d2101503171450800ca0990400b6940e400c40c613a407015501c0c41e64082290740d142050855400e0070300144001c0c404c0929840e0041c1da90100160f5a070008021500550006070300814400100d4000110058400403030100c04016046100181d80341d81c010840d0740c403408821850384c1c7c4c1254111903d507240d01c00b0510860098009840350441e2000810450900541c40101070a0701608030040d414203949601c58 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 559146555 1250 559145305 559145311
    0x7020316020f010c02120a0515010825091401090b0a12021507050619051006020a06200c070f0605270102071d090708030f0a2703200d0209 61
    0x19400000ca02030b05900446000508a400070a88520b42000c2c4000640d56680040111600c0c003a00200c004041e00300300245041c0c90524015040c6030a003452000121032480c1080000c02a800c0ba00140be0003d51140b040520440f020900ca2036052984501c10748920b10501801500441400c1003c01c1c2e02034500441035034100e80462201c402201c0744070321402a94800350680c0100d80034040310030340c8070b4035041c2203071540c030000d004590310400140341680d01c1b03124031030140e00103000c4000001d0803588080701c03440780e1004688560010100c0d00401d6040700040ca00103a000b00310500013038101190f007400401700e41ca442d0745042e1140c112080e03118a240103114802c840e49014001e6a07000307200d00c2028202c981c125640410351003401c1c4129030400c2e200410f003070040c6540070500c448080221204881240e004500c2e09150481c100e66580103100d110385c1009002078441245001403113104c0045000713440d2030306024650903640111281503003c0381d03c42d00407400141c0040c1c4502c944070740c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 559147805 1250 559146555 559146559
    0xa0e010302162019170106050a06020a060b06090f040c090e010f050102010608011b05070c0b030f040605060102012901030b03030a1112030907060f02190b07030e0604050a060b0a2403050702031602 86
    0x31903512000e5906000d07041f1341d0403696111149420200c0c803030b03a0014011f400c0754025101071100c884e56405115071480361b0844190880190f41c00d0b01c017141440d401044841602e0315103210f42c00c1d078650380d0010604081c0c04c88910054070400411031580d09000b980041c1445000800c601c075030700001140c1100c4030081c24820b00c81c002c1703047c0c0203000ca0010440010101c01108503a00d01c0d15020001401c03104a070b04441007843c1501140d40317940305120380c030303030040c1554601482d140031003c0a41442d0312017210a41019140c1c01c0704030154038244064404e80c14151282800300d00d4400105003008114102c10000107c24401c004107400006802c504840140c10462102c01004404a0500d9001d40072041d071001010700c40070401907100d10451180d20700342d80c2082001d1183c19490788814080d00c014080340c0c0482484d00108a10764020307004640b0052145500c030b590b656543c4a030780c1403600c810100107540d0071620329030794050203a9036101c00030707202039443c02c1004008000307c900035502c064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 559149055 1250 559147805 559147829
    0xf03210403050c010f0f1d070905090c131505032b12180204180818060903060901020a08070804020325050607080c0d11030a0e010302162019 62
    0x2001e06001d4401c035180c0d010003100a00080c1ca0603e2640050200d0b042901045d5250008203100360702428014800c071001c090240c41c0052404100c4405004090591502805092541c01e500c0d5541d6181d07800095030400003240f040303042d120028501103598089030103904884201180d0280010303000d0303d990084400d070300881c01c01110407943c00107003d070031a004615010080a03030702c10140d5103042c4213100b110b00f030003840c7c190300e040c0d6030110f2039410080000c0d105001c1451a0b00c2400b104406000b8060b01c29070412001d440041e01d0300d007050f6044070f0640d500048142c12158030114150348070a807828034440381c0c1821343c0429a103410070000d4120034120000000c02c2d005d2401241001400d0040080e0b480c6e401c60b04001a10750b00078002c402251040c4031030b1480c444c0c081c1c0e86411000660601450600c0d100e12400d403044c3c0302c0440803d0405608002c11411902c035078885285031402486401400d070901a5071401501841480601c00c0416503a00601099a54102070a0322802d140503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 559150305 1250 559149055 559149061
    0x50307030c02010b181902180f03121b10020304020609040f09020303191205060a0314010b040929220305210907090c08010303050f090301060906080f0321 68
    0x300d004141280321380d81d01c40a0396203944030101a1a60044c01048680c0c000d40103005038060202c01c0384a414405400305441c24858a094940b15034124148180501030761800504440001801e60200720900806141030b180c155030141c0c204048180700c24042403c51843c2015000640300d402600d00c5c840c03085445881c0e012001010f6044100d0142e40a004c8a403a44064003840f0100c2c1054481080058001820a01098101d00130540540e002034a0080e0780c07821034a8a005528403c0005a2299202c01802d0070703545403441038040e01390007400c0f0407542c080d1040c00344107000008032200440c4d012200a0040510001071707448600c4802c00e1500352203c1d003520381610140204120014013840d848090002090300d9112580301d5580407003580c20160704c5091040032105040c041100040c1f8140040c40004c1c0030b000107001c1461712012081c01c2c01044400603003581c200390002d46280d91165000c00110b01c1c10010380503121405009541030440040780004508008052081d6401000703001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 559151555 1250 559150305 559150307
    0x30c06170c09120d03020306030c0d02090403050c1e0714090f15010905040203040c0e01060207031a1510110c0607050c0d0615030f03140c06270a0c050a09050601050307030c 76
    0x4100e1143c01100075100c0040b0b0180000d0000e40003110b24030f001c0d001e5640107000a15141d02c2c0107a803594000e1003014552641e81701141c050b080451200020721132007090311b99446c03a02d42060307128240c2200504920741000c20f0761102e0925400e82c0d6000d6a40300d17081c8141041c5812403980c0c40102030a6000501c200800100c807032078196804a9001480041408248094803003114180d0784142c2e200340150740d0752442240d0307511080c40003a00034003100710100c0c40103130640b4100b9040104840c080c0d0403031280000240e030303040c2c0e03019503500442c19514075000851014840d005004000b00d811a081c030b005512110344565004401d00d10917100c0c006668100700310743d4089901f0303c0f001c5000c03441050320791804134524a50240b00740c01050701c18100c202650034410403a44c0403508800500b20544a1600100c1c600f01a0213140007084040d0006030803849082140c99042030240302c1480c0f03210300d014144008041c036900321460140c286000c204903a60031200711303a0000490300d400600e840300104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 559152805 1250 559151555 559151569
    0xa060903030f1a03010b01140a0522080a0b07020c1003200408030c072301300204050f15032205010f1d060103030818011b050301030c06170c09 63
    0x1c151070380074603110700f01d0100080701c404152038480540081082c0c101100040d00e0810303030b40da104002d58600308403602c1054481c00251a210000301c806460200743c20102810300d616540080e4107640c00302130b03900240290032420316041002400a01014084100891b02e414002441c01c0181520b640101501482c0c0d501c10101c071603004500c1a81f5280c585041507204d42c490030054007d40328001001c00e242c81070790303a0440c80c0c0c0080707455010765202203001900d00291890940200541c0400400b02018034200d503400e141000000051303440c4c0c280020481038016806031940940100b8058154820000c000c49070050482003c2d080e400d9154840b403c1c02244c4401e0040065003010324402d40b8840c16040300600d5143c00d0b01d941031080c10024040e503a521700344805800900a1004960702803c1883e8182e8040b88940021a42c0d200d14284102c0c94a8800305500001d00d0004c010028420304032010300c094082d91a08066000804504803901032000c0d042c220034420000f21007000c3d5850107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 559154055 1250 559152805 559152821
    0x80d0905100518070b2a01020d0908040609080606030607031503080d020414060c2a030a050c030f1506010e0105120a090201140a05040b070c031a01050102010614030a06090303 77
    0x40402d200520b001034000d801d841ca0b203108045148030310b280c0807030303001c08400568855400112464922140d070302c0780084801603402c03466010355401c0100c0d43d1150503d004a990544c081c070040c6646074905480206429506d5101702802d81244080c05041ea40109055821460307a01d0042601c0e884076007070390240750095000800c4201300081d030171003491054004c0d1080b10400c1d004120b000c40110244500d0344508441c4251030f030003090546c00100d001801c05c0515020020200041c00d0201c800f081c540000c1d50307403d9035940c1c003004400380140b0b000c101c1d070542031010b40094040444c61034550703400320b00c020300300b1414840304030030a4080741d00c240b060b43c280327419a50304e44945052850a0100426074040c00740d0008051244900f401c00d501d03411070701119016a070f81443c1c03500c0c0c08410311060f0040c00c8121080880e0750340010106401c0842008540854031042e00c82d54504000a400c5a5240d0b100c0c20103400881c400b002030350350225500c00c2c06608444080f89280182c542100207042c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 559155305 1250 559154055 559154083
    0x90f0b150a0e070311041409270106031101020a030f081f0603140709080d14090301090b07180e01030b06011e120e0105090a0f060603060212061c080d0905 68
    0x1c1c1d5800600400c00c200d20901807045510100945050704001510070712841c007178050510969402c07900e042c2400046240d2001040c14103500510f00803d030040e20601421141d012691038280178000d02158208904124400340000c0901c00c800d6580030381540c28483c0c007034092007540c200280c800d00400c1c00003001a0001e4024118094407040e000e0002d04403014071088c42c1c0060000908018000d0a90005442c080030013007252a1400e203040326100d40c038203417800740860140f1144901762000d01440caa401d00c034120088551170032080081203040c030103003440419003000c1005c1294800c802c16031410750707400041e034402c2669010010b03114000f0060421020040d00c400050344181e12683c01d58a204c5101401d00044a8007503d66090f10400d40303450301650449e80742800011420050080c0a40c0f2501c004210700ea0303039880b66400c03600650720501188100c07104200161402d80781e045908511000120a07411a0b6160780700c0d58010440c1a4041c2e45c2d135403a1800c18080101708491030300ca04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 559156555 1250 559155305 559155319
    0x304051c0f052b0c02011e050d060308120a050103020a03030c0203010e060108070f0503030315120a05100b0f0d111207081c0206090601080307021c2013090f0b15 71
    0x4408440000c1d845031445440038141c0521564000c01c1c0715200707081301039805175901410002a90340030000382075070703028072002d0003c1000f0300a14280c081c0140002107009101c41030725400d2142d01e003000500020f0001c00307001d14000c010300042c0d6410002d0000d80f40c01d440c246610003002e10109005003c5010380180b20311441c03000044152000494505480358042110380c0150b0740c0091541c2e0f4081a503514070208030043e482c880300e040105904032084082421030b8089803a40e190b10f405e28003030882c0c01040e10b4540c2d502c45858188281c92041508050307405108550054940182c0606804a1184038201601c42c0c00c14094082021401901260b026940326035044011101c927808000d40b840054080d880000b50303240404034400e4100c40f9000007031403400b409942042002460f0618442c0000f1213854810041185440072501d12100c5140203181211028200304120306800703001008681440c116100082002c05a5800c80e40d00c14034804142d103860003084510b9440200032604151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 559157805 1250 559156555 559156573
    0x2103020702041b030b030a26040527060612040b04081e030a050a18030c150204120c090c0c1e02150d0e1504020108150405130605090304051c0f05 64
    0x141040f1007403c072a0540c0302040800040c0081c10303100d0250311406005001c0b880c1007210408400c403400100700285008842c0303000d84844c0060b0f1009a40c1c4410514003600d4242d100100280d080115003140b4100c030424100b0807101c41c8061000c000500080080c8202004202000240c0301500c007100404550280002d02e0381c1c600d02d100350400c4130004851814600403c0712a0340a10410003041080381c0501d00040d5151001e03116001e078080115a0151000d000e501e8510042c40500040c1c039480f1120b0b1096006e5041510124001e9001050900d242c400340120351500084007002070b40e40005441407004030b960783e030049486854000781d04140446842c04000030400e008004030300d10b982d010050f6560038022a9620800407000d06440c181410103d009176028142c100d40c03010b100c80c0394400c111480404a001d41e00156003000d0804022074202040243c1c90081640c4901e800c002035091616100010f40c1440348000310111030700030110707480c003400340c01d610030268142c0100886400c5a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 559159055 1250 559157805 559157831
    0x30106060e0418080f030912040303080601020f1b010e12070902040e1006020c010809010213030c08012301090b1f0503010f06030c0804110a0819031b210302070204 72
    0x70800c20306620841c501907403828502c407a070100741141900f0050460601d07202d030807900d050307034000b4103100414070030001d80a0b6007800000082014611a0f56404c00d6414044006491720051000d108070b50307045010ac1c4d42c0d60300243e40510010fa10b0034607001c0c0c180103400c0d0204204c1280495845034070301410001141950203034009000311548465103060030f6035000300c18180801c660060f2001600048000b081c107610840b80700307800400e01000140707402d80484640d40d480b51260f10031561882c030117104000e024401c0c0300c0c080117520a4045c0148078001e0303050a00d030019050094404860fa980d4644902d07403034141907041c2000d40c50f82d0000d107001807400c3c044e1554200348265100807045280208402d442405222105030391921241c110303885613030f14120041004012a80c100e40da28100140c41142009034100800c01e2600c0c001b0610601d003001448081c00d1459209400c401c050a0000280c1440c090000e040c1c8014001301302e0b80c100c0004501a1040384006540241801b20200e00a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 559160305 1250 559159055 559159067
    0x100807090816170319031a130c0e0f0102061303021c050405040c03020c150a0b031207060b0a1d07020c0405161d15030903090411030108010c09030b070f090503010606 73
    0x643c0c103820503203100720309000402d07990348184c0004401c045400301c0c4200507113020713821000a8200d020b018812050344000031030034070510b0a15920003281ca5424041450f600940103000c0c00e64181e440300002c1d41c2160001c0d54560003d090390403032000f020490000d041c42800382c8510b491210f01c04003c469013010006029811a011b0948100d00d000310b070700c40d03450180c8202c1341c40a0903030015004460a6404c18004448014241d41590392519203c00c07880e41c05100d03040d150a10082d0443e00d030703009030a011048540d0003600e41d008444890092081c411200109145200f884222078044d66a00d082207051082d403082648d0420700300420b1222641800703075504920700095503088a48101c080885901c0085400e0207600400c810f100510110115001558007510210460789440c14000100301260441032451890b03180100041c06440350030300a12080c1455460140322281c00d54841071102000a040c8a0521100840300000c080c000c1d0901c0d402000e004000300403040c0e6a40000e414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 559161555 1250 559160305 559160309
    0x120b180a0b0f060a060909150302040e01021b0102030108070b0c010e07150f02120a0c0201031503230304051005070f150c030e1609050601020a171206030606100807090816 75
    0x1d00580e1a0015150b070404e00d00c4031045504a5075044030585c030780600b000003065501c4c03015840500b103500101c050784903401150703a00c082510005940c0d100404011130070b076000000702903050740104010080b10000249850650301e8648985540343e03c407041085c010b15032108a50030390301601074001241070f824004100750a00580360220404080f41c01240c55509860600508100c24005800307802c0c0714138a0341c643c240c418180003407203042d28020740701030500343d600894101080790b0141d2440340d4600060900b1002e80d10056042c6800c08002030210300c403600ca2201000000b241502c2403018081c1900c0c9002e40100052503606000c00c01070b4060200b188209010a0400b405405052400503100b40c1c410080c808400b00e00d82050356450240801806043c114410030300107002080c00c0e6690114580c045a041c0e135a24801c4400101c01c403840202094800e410610130050f680d180c0882840c0110b41d1743c0382260550703444c20001c1d07642c0460341c4c200c1c85503880782c04e0300380c40e046c0f0400f41d001003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 559162805 1250 559161555 559161571
    0x61207030f0b07110604140307050601091a060a0c020402030a020f0304060912020f0303010b0a03140702030901020d03110d09021f02071d0405120a0e130b01030507050301120b180a0b 80
    0x300d0783d66503443c10f44480c1d08480343c40840e58000000500420301c0318900001e1010380c2c00aa03482c184840d290246050310a070080c41009659074852075415014a40080c1809001d58410342030004024025101303403040d08019002d590004005454070a4a5040300d55045008040503168182400c00c0c0c00180f26480c42111203840b07040400c4265400041c80369a00c6070101c0040d4a1a0b003003095105040d0050703900300042c5500e0b488101c0c4400000306400f841032a16500468441c1c00c01c138002450010207603000010300d40ba00482400001d0800100c1d01d0402d40d01c6c4002c20400400e202142c0145446014584900360000e07900c0c1e0340344d41c0402d01d0400c54200c00341107605c12139070780d101c2e210f541010b803030040559000394400018110760b00050407000c4c480c1d04128401d0b900b4800403484001421b440e204a0303c1d9546c9001d6072540e090310a10390003200e9440d240782198100300071038418060001c030190103814000001010241c100021904090124050380c0c10854207181000c0420001e0381c00d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 559164055 1250 559162805 559162823
    0x240a0806030111040501030905010f05010602031309180807050a050d17060f1f11160e070e061605030f04031b0e36060103030203090a140f0405061207030f 68
    0xd0315519050244981032191440307650719040c030380070040d0000c000b01032080f02e8554a07070301d0210003291a481183d00030402c0c2d8000d5551501140403c0e40300f00201c0d00401c1d201880d00b801c07000a5452a202202d6059002400c0350755510207007401e914101440100802e64420404461103c0c1da104020710b45402c2011510340305603c0c0e010030004444240d01e1055000294140d844030400c3c1d1203546002d810030303e03003055620a104002d00c2410003c540e035125000380308460701005032100701c6140c640d001c2074030700c4c1c0708030741182800004640744182c2c06441c610719044c00b00c04091007028812900400a4400d94039030703d030f0b03030703403520500390724070300018043c003082000300020480c01004201e8810035022021200c105a00700d8802121940c078021111403e01500180b0814441046628040d41c001e8000f10744581d0340004110441005070022400301202c007280c0980368441801c0315000c1c0b034040b03c01081c0c66503000041100451001d030a907256100321103002050200b40664949803501410b100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 559165305 1250 559164055 559164061
    0xd0f030f0b0904290a02120601031e02030a110403050f2413060f290121240b030f01060e0603040303090501020903031210080105040308070e240a08 65
    0x30404860300030042907040b484070340c0018001019109405000c808003402c0510214004104104505084611074102640002d40500240c01542d20550101003407a0501c455403e01074206040e04030a0260a03106401002041103006290015070b00b0980040d542510380b40e40e400c005541d410354108422041c086d9088204009401c409501b1044010b0074458485440f00c803500d04400000c1c403800d84200781d450f0f0304d2620072042d43c042c25010b01452150808034107801c21000c50312b9002024550f040c41000d0f442c1190311031840008041d1000c440d6000200ca406140c2c0196000c001581d100c51016104403011802e26118005140904496001c800e0280e032103160966a4019443c00a80d0095041c000100024400d40128402509c61000903080c06c0300d2802103881e40e0405c8415032408540c80341005510841900407030001d2203141c00a0186050984000e031141201501c071404029080c1010b07003144d180d041991040041080340845854040a100141c0f600a01c2d800700000b451039001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 559166555 1250 559165305 559165331
    0x1f05040e16050f0a0509130e0106050103020301140402070f050a030f08070c0c030b04061401080708010b18012108040603060602241302300d090617180d0f03 69
    0x4940c030079040e0364a60700d01c1c1c0034902400441a420103154942000020820741d0400d481d012007e40030484040c2001c20014100d10b0183d00b0b540f080c0d00428101351060004010f4182c400044c2c00502d14284d800694500c11405d00607070b00002c0c008041d0407841004203110401d83e001c400d2040c200384903a00e000b0aa150070b1411580311561041c040c00e12540b4142c14004100e03035860085c0c0244c403500c00050680c2020410f1070013648241c0c0301007111f4009400c00c102446081c010603c00d204100c0e05009904a4124140f01300032060081d02c1c4074200350360b41e8255030443c0628420031280c10080c240d441d1680e0b8a401405441a4001e0000601032900c54070192510103420086901300d5040c122040e0b5500164030980c2008050140c1c0e00418010029013140341141c1894070301e50081c0c40d013004840b106103900740340c01000d041050400c13032411810000b89a1018120040154150590031903440703d8190070410407040000710403e00881c00c42d4030200360007500b100500309982d1804c1c070030120b00c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 559167805 1250 559166555 559166581
    0x60c032203050d1d0f100b0a0315020c12030c0403110f150d1107050a0203010c050c0c011407060f1506031a150c0f06070e0a05031b1f05040e 62
    0x540107020034010311112600d810950041d0740300a2a03c0800c8001001440b10146010001152100e950300300158412051030107018840c0300303143c01d03100e180040c1e145690f081519403c01d90243c02e019804180c500d03170070005105110b400e43c0c00074a6203441c0e003081c41000d41282d200e0b20040301d4a1503a150486910301b898a1801d10811004100c0e10030084000c0e5006d4559104581c03071110f0301e0703035441034183d0914110054010b00d80a8070040402117100d10500d400c4421030b16400d8184002031044001c034010000d0075111529080c6040e601403805440040643e00601c00c0090000d41040c90f0300d0035800440e030080c038030180000303004e03c102070340d50340103400302e0340410940003603580d600e9040c400300d00302605410701803400380c04503602c1d2040310342400c0c0c200200ba4a800340c0b15003198040c0300300d955112180300c040110031680d6014161910000035a80c0d5400c01700400c0100040e4100c000310399aa0203c14084038080d031803c5040c00ea403c0000304954024056250011031990200d070b4080d035065 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 559169055 1250 559167805 559167871
    0x140105040506060d09021c080c060106030e030406121401090902032a0f0a1a0a09080133090203010f03020118080c0603040507030c090b010e09090c130e060c03 70
    0x340c585072038080d1141340e100c0074203043d460070307a080200504660600e040c0815868a81400740e00100e03100e07403428884504002044e48000201400c1c018658002c00700401240c08541c0d090801d040c4e201d0044400c40c0150100281c60800140504000542c800d62a000303000140e100301c0580303000c42c80b50010b5511916011074528a401c400703850b680014100025030151300000200781c4191749903500007491400d5165000343c4107101003c503d400300a50403410a01c0540344000080c40404500401240c0c0001001c0c0c2549617400c0da1440c204a905134501e0340009008028820365496071116188001402c80e840202d002480340d459010850010704c0800c802d03541504054402c80842100b0803c190304043c0064400c0c1c0155800000003a084410070801081b0f0200040b40121502d000034102d541d20503000f034046c2c281c2d041080701c0030101040f4101e02e0013084860600080100450f10024001040610701c0361041505200c03e4225090183d44624500d0220f40b14184001c501041c00c40401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 559170305 1250 559169055 559169059
    0x605030a03030c173303100c02070b030c0d050a33050118120203031b010b0f01030e0d051c0501030b0a230703020a0c050a14061008100b1203030406140105040506 71
    0x2c0851141180d004050030003401c0c015180740c5555041840c0003030308044058801d440304548e01d9110340c11168050188000070240d156500c1c0c19803a041e1220f0050703202c1c02c0080c1d58000d65550020f540b040c01503010800c101e00d4545000c1c2e49050001d140c1520038a00100101000d0f03c001001038690b12a056000c424101c02e15950019860f121580e400752800001c200d130301d0301051012042c0c0040180400b104001340c2000031820000d43c0042c03007c016492290641010704000082d0b80014001808440b0104a450040c1e502c1e036045031080380c1d0034441c1182c544a01d007040e00000500030200c4160b03005105203a020031091240c4c214000c520001403c00c500000400000205214001d602801c0024150708000e216010f03a0fa46450400c403241070225001403401144112440e0108246540441c0400ba030007001410107400304d580d0b01c0c07038010050001d41c64050782410350322600d4200604c01044800c40e6224105441c148000d0181e0600750054400c1200c0001050314060207650301410b00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 559171555 1250 559170305 559170331
    0xd0519061206020708250308060906282310030204030b01030b04020d060501121b12151b020f010c0e0105040e04050c06270a0609060809010605030a03030c17 69
    0x31a41d540b01c080c0d04030321000e403001c010600c2103074040600c442d00385411428a04d1549100c1c80c6524000d002240b001e0840740c06440c10700c08121158035445042d03082032070b0507215039015a4007100c02072003189150f0402c070040c1e818008400c410903c010403150340c50008403200b00b00c60205080c120304a0240d44409804036010000400110740400d408981150000e44003134880c000715240e100644e8002e034480c0c4084110b1101c40c40900c0b00740000201d114030f00480343c072892480d0906540c406035840101a21182c1007050804443c269a1700107880c42552080944803141c0c0c0d0800a51559000281d540c56542000006110248108144004480305843e8142407071304003881645019001031044910b40300ba082c4404d07069684070003502031515400a050200c1c503c00c540c200e5000072204a5a0046807151400c4c8082500000d224080d202c0602e03100c5170a580d40c42085015260071380c82a43c16000c4c0101e8103060540c5900f02040600440d1200480010304c405203045059007141c0e1115801c034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 559172661 1106 559171555 559171589
    0xc180b010e030c1509091f080a031403091e010c0e030601050f0603060d0f081b2b0e03330f040308070903080d051906 52
    0xa01e04203400c106440c021036515000354a5580c41900c01c900340c100303220455010b5501040006014080d1400c08008440c0a005800c0c0c62006200071103002182d100e0001500308004d80d4142c0ea002140e00100b50700b002c0c00e03000945110000c0c041c044030a20f4264000d03443c420344002d0074000250311900e020303014000c04c1802c0b800a00a8002000400103035840744214240300c1710a50701141c0d01e54400c0b000031080c00c040c00b0b00406d4852104840e03000d11414401030000315070201814400e18031480c651958498580403a6030103906406004d050f1b40c01d0041c1628208030050030140086400540060704142e000b1021040c10020506004c5860f02010201e0101100001d40c43c40302d4140607505060b000f00040c00034051281e09004103001910030b2900000440e04004102d46451000300e602c405001c040d90030070201da0094080c541109004e1050b201280c00c803402c0107070345c42 = true := by decide +kernel

theorem cover : BRFrame.Cov 558992805 559172661 := by
  have h0 := BRFrame.cov_init 558992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558992805 ≤ n) (h2 : n < 559172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
