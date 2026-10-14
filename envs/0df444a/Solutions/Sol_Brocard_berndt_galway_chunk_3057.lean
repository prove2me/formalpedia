-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:20.551121+00:00
-- url     : https://prove2.me/submissions/ce2993b1-e42a-47bf-a4c9-79f4c203e03c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 549640287 ≤ n < 549820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 549641537 1250 549640287 549640307
    0x201060e061005040e07081e010e0f061903050706110c060a180b2101050415050118080604050c0a0f080c01080c040b07061d01060303080c03061207060c0507060f 71
    0x82d592040800e80b0700328100c5140c40359401ca55108061403080c44601a80100b240c1d105211a20301d040408540c0c2c17000782404e107820300c16071f13406001c00d20100705d030780c2150900e65800a100800b410055682140c0501c1e42941c44e6109031610303002100c041019a030080508482030b0b94071006000010390304000140b5500aa039124070412000000c0b0000743ca5a940c1e0503800741c050a82c1c8251034041c540c0244908501d5841c0c80301310315081d04000238132030a090003540c00c050310489100a09074100001120700c0c820123a0f010200d100342da00300081c1050203011007802640560003a021400c065400d02c800344c8000c2e480107010348680c070801c200c5008040340c81030340c0d1a4240782510903a15101c0118801d4090768000b02ea0000000801c1340411696604c0a48c3c4090507031480f12458043c15405401c071401840301402054080d400580c0b414a40c80085030b00c400000d0a2480c100c4801d80c44920b00b04c151b070483d4000c00e0010395141c2c1400010007a0340c00902c100c5c580408540380800e0020104d03940 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 549642787 1250 549641537 549641539
    0x109080d0218120706030b01170f0408090d03090905060d050706080601030b10030509010c0504050d11040e1e070f0f06032c030a1b08030103080a020c0d11100201060e06 74
    0x400b141900341d42d41c403858016802400203003001020303100982c10607203500c400d200d0080403030310b0410918507550090503400c0b410024665602056079031141d9101c10754800070011961100d00702b11070003140c4e99072041100c0704c60081e50350072441340c14a00d482d021a98007801452040185481190000e940040c4101c00d884080c03078002881c0d101c1d04010f90207070424101e902d41c410490710b1603010150b80359006500c40c0400c00000d21003072480e040d0940d0284038600900d5080f034096040000031800342c0202001d24240038100140e4030080c94002400c0662084223600c01c02011441084044010848103000d00446110b00c00c0e0b191074040c9000c65501c0394800d01003810344940c84000480c10300000380440c0700807a0b583c2c0554070405140d5545030750200c40c3c0400400e02155001c5140070502c81620483c43c0d0101c2c149140d40d08507150066290010185202148110001d80003d5100c1d504620003151180ca400b244041210741000040308007001c440b0116850300c0340401c00414912401908810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 549644037 1250 549642787 549642791
    0x902090d0f1b1d0f01050a09180f050c1003020a050406030c020309030703050706030e0a020d0f080408100209041a280902041e0f0617060a0306051311030109080d 71
    0x8000e2400c110a140602c9101e86501982c1c4400941e022010809030348200031040b080100d9600d160000707581010a0240980110031070005100e0640c0c6540b02e4991702810880d01554006141e4a2036902c240a0000710b503e40c20000d440c085c0c90428800f9001a40450b0505500304521420018a03038000c512a140425407280c0d07441071080d0083c001c85540350005015100300c19186d0038810341e1581248074660000b0700d080403038154002d000c0b426080d40d42c0e00505803d24081c490300c030201d1140b00c0c8031041e20b180da001c1000044030300e010007108481c40c441d12009601e516400b810002203441040c81d5080c2c0c010a4036005040c4c0e681e00d4415400303407151b900030b813000042e03052403045040b00c1030300b0502d2990720000e000700d401410525407070719003c0c00d5005e1080c40c60b1200c0300c0d11a0b0920910035600486d600810a902d914414800207601400182c01c105d51140d030381e20b0741000c6d44c000703589034002800c024090710103110700411403504200c0150002d1049148650f9840c0307540c41a0318000c0c070038907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 549645287 1250 549644037 549644063
    0xc030307260f0c06043e061902060105040c0519030908090604060207030203060705070302120309100f090b100b090402160c03080d060905070e060c010b091e010902090d 74
    0x412410030742c1c80304681642d181d929820b4008045680c0d140560301950003034480c1001c41480d000041502c0300780320104181130380c1240c018494210b48400e005400b0390008043c405900601500440d500d08011907038024000d552411040c4822190341c61404030402204128102c07001703811103c0107803440c2c0946030016201a50b410009014014070312229030010700050001080c070743c00140d980a03640220103544150300c0b069002c2d21103205e0b6080040c0584c0188a00c4040034800c0c001a5500c10340038000d440711505d03000070840c00c4400e100c14080603550b4500c003800a1101446040740d01c907030200441d44c040c03414188034115074000d902c4a68403403500022300c0c100c550b106510401e00b8941c0154002c41054032850507a100350460038100080c50b250542c0041d031a4001d000d0305004420340d48960282860500904c1401d61003113903403e0056480b03810025141d00c80030b03c528858007040304000c1000d06040035000c0c10443c181c2c0603001450041c80018001e540d0a04035101c007540c0210205102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 549646537 1250 549645287 549645353
    0x10c090302330c07081617070e180d0e01050f090a0b07060920010c020609040e120a030605010311180316091401150c06020309010e07030602040302030c030307 70
    0x142c61407110080303a40c80381528807030b009007100251502c07850040940342081d8032054040d5490450414010021140d103a041080c401c00090300d42c0300100f46000d4030f1a00d42c442c44012282a03043c1c4601e2140003c1c0030780c0d054101001d119641e0501100d1030002c5c2c0480704000024410700503103001401c02c040015000d8481d0790340e4545c0b03000401801c00200c0d00c80d240c6080040c0245441c5205440b5408030b00f510b490545400c1484500c01141611651041d4941d502800b0841d04210381c0160003d6840750b00e24042e8504214a400e11440c4009051b51450388000040c00e4400f180d00c01810b15003000c1c1100001ca8050b130070f8845c4202081083c000c075806200000f8540402802d04498416010760003103000704150304901c43c0c42001d00c481d0310007130740d0342d5410003d070340498040a000078002c03c000e500041c94580055400031502e03000400d4100d1000001420001030b903100b101c0703031980080c080085003418004042c00100460240d030600041d92503800c4065000b012220010a48031440698 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 549647787 1250 549646537 549646579
    0x1a0601050c0115290304030f0e061b0705030f0c06130f06050720090a09030306230306010801050c0f0c010f0227040204080a060b03011d060f060102010c090302 70
    0x405002100a01019a0041888a5034041e901541d1085401c0d1000c44103002d0f81020300c6a08000039441c054030719903850b1000c42d2105c0340c0c100380c08c5c2041000200300c40700ea0349001c050603084807004001c0d840600310060482ca0021551310682c02074000d0056007080102c00700f411150014103643d07180c0d4415401d81c14000c0b191f0143c000ba41603c00b8110040740403544100a00b58480c4241018a10502d070100c1c4814010340d00503a403580203031f40790009100504d95810181c503003803103420080b07099500e030401460f61014030180310404065684c2d003000946010400c090040110700000c010314100710420641c2e0b48209504140e681d000000c4207544c2960035400307400e507105844811529040e08030a060398a1580c420240c06080b00c41d540700f14145003500c2140d0888240400510100348280d50301c00141159a422a525550703454451540212182c2e20040750180351000d000c40345040101508400005040c00b03046a00d001d411240564201c80b580c000e41f60100ca0001c0c085035850100c0039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 549649037 1250 549647787 549647797
    0x101d0c21060403170912070f02130c0203070203060a05010305070b0a020a150207030f0e010f0309020d0c06020105090609120a031e06140a080c1305060607050a11040501121a060105 79
    0x30481c490041048181940400358120100e8880081c0c0301e103860380c0c0031440e500c0d002d0009010484004219181c000340f0b511003504035203031000d003000592004580c070b00b00440d0f010101c51b03005030304009210310440c41c06101c0654043c9840100b0460355045849441c0d40d8849402025071568002881013030a6008209200c551540285840b0580d80f14000c10806900700030401c4010544e803248507000c203402010468600d1f001a50380146a070482a02203015082c520340c2640c000402018900c04500316110700e070054542741e0004610743c1400840c2a2400070024515481600600440c4445010700340841c1c0585143d8540413484407074660113504005100c404148001c0d1404000084414010454500600d41151203051880da9603542c9600c03480c3c620079465011007448441c0030300d04156405160804c001400c542c1c103008450350303054034007032043c0c0c416075541416010310041d51800380219405449115408030031b0018555818600504134440e6000c072118203400910182d2103241a19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549650287 1250 549649037 549649099
    0xa020a050304091d0303092d01050901060e06090c040303050a09080610030b01090c140708040b07031e0e01020c0909011b050409050901050702030f0307090b0c101d0c 73
    0x29a4480d5039040c504000c02101640d031300b00c103801c80f0510007150404416203125440c0540540981811009015445040102c08080c80042c040750002e01c04801d11134142300b031070702c4000028401e0502c800c05500e0140245414460710142c404c0000d0305c542403007903400326581400c20381d89407034200d00c0a8440c60f405411040b150b01c108800c1240b5265901044400c0302e00800c107038030f039a0341c84607080d0041e22a0600020701180c5100b940518503040c0e84014038810340a459542d00b050344800e4030b0206644072201c02c0e030004401d82c214900903110780c20104200d480300d007840c0068681e40e90001c3e481d944501d00d4248140c0444002501406007900400123855059142d14012242c2c6c003400340081c0c000740a02c1d024280f5102c00580054014469503008081d690010350800710924440c102135800144807c3c204a203500000440b0704400e40076150044011015050340884840014101c50090b124045180080d8030101380c09080469654200c2c0400da40c1c0d860b07500001030100041c0003d0150f04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 549651537 1250 549650287 549650293
    0x602070206070303021903020c0c0f060d110d181112280303150806010308070311060124180b0a0203040e040f03080c0f0a1d040e0106060f09030803040201050a020a05 73
    0x408200f551590050180642d02002a50100701042080b0300703d00607202c0c1d031fa0740c550090940c842545000c041fa10345044000701242e00d01031081203140d09403860f845c054032036140c001c58040b10340c2d00e084c00351842307602e13008030350404603201929401d10706038002d041d6500980392036103040d064510500680e48260b100e0701000395103d91001b110020761440c20030035400640703403400300044008809080b0007111009001040c0c16405c42c0c940c04282c0e8010383c802c03018000005004a0612028414107000301590160a02c1281c8600f04c8803880d030074440700c00ca041048420140c01c805461007200015522400102c0b600c0d0320385180141e1462245030041c0304603401c004104420401c500c44600000c5200766a0601140c891107510310b118061541c441c10015000e1002c0101c0c98851220103800c4003aa00b01d608004600201213011500a800c40b50902d945451081c012103821131f45034174a100c95868211801e03440c5803100c038038600014100038104003001804840c0e0520800414001c66000415 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 549652787 1250 549651537 549651547
    0x30a0212010803090103060e1501080c12190e0d2001060909150c050f07110d02090f01150207030c0302040e16090b032a0f06130b180a030f0f0602070206 67
    0x440e0380d00c0c4c11031280c0341e0000e402c000c03011030b4a0040b6071406001e89200d144d030101c24130040c0019988004c005000d80000201880004544a0040e610a000d507411404a140c50054200c4103030940d502cbd031b002c1c055545c0c080b800500c09154090504092020720f07080c0701803008400600c141c09403400741d00451055003000d901500f03001c61981108602c0480f45000c02803183c4885042d20140604941202046003d0002c034010440091300b000c4860002410503e1824040c0c0c0040c02c00300040d40c0e100c0d0b01380074050050240741d641403d402c142030312074001096910b1544c2d845802801c1e542c00001e001d40c0e29003c01f001c3d4000100082807226114024103840c154450a5000081c101c111000d8071920891911520144294290300031414140580c0405a0081070520446407407031003555030044002c00c244a104145580808050507a15441c5690381d400c2012204005064441c0c03e842101e09600c01c00003d44801040c00c0c0c003e41c027030040c0314224040d09044000340548000a504154001031f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 549654037 1250 549652787 549652799
    0x2061512030f040f0f120f051203160201060503190f05010605041b1202090901050904111023030c07120c0f0609030305180706030f0f0c0f02060702030703050f030a021201 75
    0x181068a42c000b000050321503503208400b070910458481c960b100d20b61581e8101c08107c80a454140c3c080c01441103500c01c01d00b030030f80c4003800d6008440405154800301d0308410070550a000e418021f020481c02044800d00345008a0171001101e20018801c2c842c5d244140100032080d00800d000b000000c20801c02105081c000f15900300440701300c000054402e4400d5078441c2c07460307c2552102040603020b45a141e007480c0603c01c0d6800007400541b061540d5141010b0300c0c0d0b86201c20340e104c90401d9624031800b40101004440506108032400507505410b004120a00e0140c805540000c0e0300554410400e543c0d809040c1d0700a1980c10b0040d1501d2250780f001800e0002a40002d64458820303a02082a59103258a03400e8250380d01420028981054400b04a03c9109030054034001900030800a06010082c100104580700c041c2000c001ca080c070480e84403200c1d0180135880e0301ca941d1340051454040e29070343c024440c0c81183c881000c440c02c0480400d6001d089541a40c0a001c0040c006111558581c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 549655287 1250 549654037 549654067
    0x3170705010b06072a141201201909150c030221210405150414030c012003040f20060c100b0618041d01050f09010e0c0307150c020d030f0e0906010206151203 69
    0x80300e030b0152b01c0422404480079441005030004542200b1101c030b28841401030f084800c088680c070168118800c0001040d52500e1550b001d0044001120030307a907461000b510303900d900c41304070321158000b030440c2d1081001040d0f0200c0c02d401091510015041140c3c0d40d4a4a44840707500040600110712000c00c0340c0c081c0c1c100541c4540009024141040310504800006244510040300c0013089a010704460800092800d14401e02060301c1c1d201001144d0044030110f0540e07006007441184039800040154001c9a66100f83e211503501603403441d02c2c041801741040c220800e683c030010301842d0356108007007840780308221514482010b4002802642082034a1203c0741a090319110141d500c0c1103048410203100149041d60403a002e8003801d00689401c1c1e05290304030407a5034035400c2c400c409070701c800140d03204070400303030344601c030341c80c0e8580145061000402e00f90819254030302500360001401400da80006101e030b0701c40045289055400b103c180412405822144100580e21012400c81480312001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 549656537 1250 549655287 549655297
    0x109020d06050a05130e01020910020c1801030b0f0705070b0f04201005030a0f2a1d10020c040c090315050103170705010b06072a14120120 61
    0x1600180a4035440b02d00f0031040031003a1043c40c0d80001e0960700d040c180c0040740c201141ca020305c85c1c001414002e800002c0340701d0100303440009005812149003c001442d04041c061750303007188101c41072555811552480740d004800360642814845000000749040d2288045032429070b485121540142809202c0d511501e0f01503034100c1d0b54210020750390b000460990141072a030f1100505101900a50f000240c03055840038203e502116191602004c0a1119005090000785507030b4150315002c400900c0121401d010b07072005400c10130742ea001400003180030841c8400e0780c80202c4815400d0041581d00746d15000b0007158140d001400d1000345ea20841d000304440c02101e0003100e603009103004021921080303031401d0200402c020010040c60390342e00003a8002d441020b20440000900e4051080060403d0f000f503241191203915035a00d07404060300c0c1c00240388490030011070038280f041c2410701c410060003000380c415001726910b201013519460250080f0a807075104802c180300d6100262900c1120b030b805 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 549657787 1250 549656537 549656557
    0x60e07060e13050601081906080f0d08070201020c071401210507030f0b0901030f02060f07060b01030b1c0647100206010b0a0504030813150203090d080c010e06010902 73
    0x120042542e01e1200380c0c0945032050764141d5603510941e54412101191480ca001c40440d100d41d9503c003c60925010444801010b102c50014801401d0348400245107441c000e02c2c0000716401409541c890030b0000540e03c0a881070040b546205101036001218040900709195844001550360900d545401d07a004500844007642e05005041484070b00d9010780d90320b2040035801c0b100200c0104007298840c148841070a100030409407a0030000c03413200c3c8041d00800b10a1750020703035407481c0010a40c2c1510540f80d82074019200c080d0001c02c00d292042c0022280e88010307150a0700e42d850400700249440e10702204400704403c0100308440c0030400c1313881140440740f10000800414289140e07240050408440d04a10b44c010003650307083c2020350f0140d401c103411040030f001061202000003000e00019003d000d4100d07000b0045189000950b640001c1d68050031000c1d50800c01c008005921104640050150402c1440340d80d0901d400c0e00d01c0c0100400c01120607180284800441c407803855030020b10232058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 549659037 1250 549657787 549657799
    0x2060f09040f0f0b0303181c0506070e09130305070b10120606140108040804120501140a2003090c0d021f0807230423220f0606020705010c060e07060e 66
    0xc0030344c14142d5a1003468401280c121940e016204607190812448583c0c07201c000d0505055003280e5a52841c011080c1d50311000305595010182050038000705066003c0008404002c0500702c0d601c01501d80d200c0c41c0e10141050307101400040842c10300e64000b50003402c004001010f006441e046c003400401c4107014902030504000d050344950361180c50501d02503038110324075600e414034000d03000740c0e03035110104101c1e015501c0c0c030703202c5002d20480581039209a111344800701e02860300c410a18024401844903840a44060041c45010300000403480d59000b01603449192034440742c00040c110712417420207240030326030a030317450a20968412031031806000d09456102000c41035902d0020410407901d4000400d41c0c00b44010411508040d8031012984686442ca9442c546a10081001c2c1803e031140c0c480c1c0404144c100c2c2e540c809651040418064484c0c804102e110301b081c030000c1d1034081c20b01c1406e0400480042040c1440142d1b070100c9100062841240d087c5a03a0f224083d00ca0b25840400c98800e10b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 549660287 1250 549659037 549659051
    0xb160206090307080f0c0c1503330415090906020a18080d260708011a070b07050708040f260312222003010513080702060f09040f0f 58
    0x18000250b50038540c0c404d44031800e00c0411200501543c00141c0b0300030040c450004203c91540310b20030030032030708450807901903503d02e00040d0407150b10180c800609511000440c0d80d000140113120440540c02003240c0100d00a12101c06000200c0700d41d40025080d5450300216404200c00c0c0c0c0d00500300d80005441d01c81444c4408041e1000c038004a225000190700003d54a0380300718880c6440610100e61110602c4965a60080b985003841e4103c0740300010480400051000c1ca004988191b1095030180c9031600d0050156174005c3e500002800c0d40c001d0200c0807610100300036000c015078000d0b086038201c0c01e80040c1d580c3e08841c1240c098041d915014030104a500201800c04400c94001001c03030484040142c40741d03007083c40b640d55000400800c4a11000124000846203020070500310f0455000c98400c2105030308040c01c641c0040c001d00c200b030208070000c0000419003c1074820303950301210704544031490140200b1a078800e803900168001d00c0c00c00f41c15002c4081ea4401034010291318004c110320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 549661537 1250 549660287 549660301
    0x150302031e1e07060819180203064213050f010b0304120f050d020a02030d050609040b1306091707031107050f0d0f05160305010507140d05040f0b160206 67
    0x901101c05105403541040078203000c2d103805280c1d85c64002c000103c0b0780c0e0f1110300ca0700d807080440b04488814070f20101e490017540d041d4581044441c0d00700101134000d010069041015080400300f0240c8260941c1d1403801c2e00c81c010350007049443c1801c4021f450060311079243e1844900601e800ca4062035010055000842c00705210000e41e4440d541c0300e5003c481c00e0000f1201586c0d03c541000100003081402c01900d81c041c003050001d008241c40c103800550b150140c0b0042a02030b40c00050829001780c280004120119445080302500f00034010842e003a103007054101140640481207010708a114041004045100000001d1403282d00070758030394074880b000179003035519a50b0a215443c0e2160f503020800c140c3e8507016411480340c0d84581280861413059544660a1500c2d14412607020103c0d024200305104080c00f07829031090140c50800c0175084515003044081c001c201233030140680c1c420000c0c080280203802980380c2c80e0010039500983c44c0164003881c80d00c0e000c1190070010700a0750082050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 549662787 1250 549661537 549661573
    0x18011811090d110f120d0e04021207051b06130506060306070207060e0301020403060e1c090b04030803040203100f05071b050a0f0c0f0b070b0c090f04150302031e 71
    0x10755002030680103901e905403202030700c080c0a0940541d1010900007030705030a540300302404043e90950320150041101c0040b020b090800e500300c80d81e0107030b80104841015441654291540314490703061040d101d029031182020004218141040366104800078400e0050705c1070a0091410b100b00b0482e0440d42d96101819100c039400c2c0d0f1640e01584c010501401014003070580300140a00140c0014140f640e40c0e118001551010040c94009411114911441c40700c0c1c80c1c00040403000300d08200009503d016090b0f503141c4120311018204240100100302103640c240300081d900000366205104140956002e04020304042d41c2407000b203004051010b400034001c5980105a54200b03015003078100d141c0e00c541800c2002607404407240c1c1b21114000c00c0b2840013a080e100a0120b01c40910b071240d44620f080e0244110242110505c20070602c0070b00798566813031400602c2030005580210b140380d06401e250b40907502e40e0704001d603d40902001d4240203031481a480a551a0102c11100e00000d6100c00c411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 549664037 1250 549662787 549662797
    0x507021e03060c03090c0303070c050901050306040309050904060902090a0c08060406211416030611091c020f03150a050f07120509160e10061803030e18011811 70
    0x14240d00182e0029100703c0440001d107921071881c8081d1000ca03099200080c2c15548078003411694205031000a0126040441940340940000c0c0c0c01043d25041a03103000d001202e1030b208191080d00b100340050308009042e04540700041c0d0151007041c00303062251030030018200080c64040014200400a51245400d0158100b11180300810321842c9441c010000c0f210500302c002501d101000c11300e0720360540020041c04100c803042201c240000c506501e081c4080d2070003492000c4510401f0f1064412039603e001c080b4012510170400c0803010102440894020082d03000c2d1281e0500135011540d40f204100800c01e0b02c548282d20003041980d440189440c0c2510040d220000080c62000340701036400c245602182c1c206103200c2c1142d0405640004081e4946000d410685000307518609000300c000c00041c507840500300c6800e002900c0341c9000c00300d6070818030ba4880a82040b80380b03e042c100d0360b102c034103243e100c01c80303152042906580c49900a04240c082001170220b000d2404c0c0400b0140380481003550307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 549665287 1250 549664037 549664039
    0x41a120d120203040c030507030f0525060c140105100f0b03130b040c0306051501030c030c0210110f030108070608100f270c02010c0e03062707150507021e 68
    0x340000940c0d100901c001e420052003224030035042140030001c250b00b0410503004502c50000c0e1540c410341d1789401170512400400d502115001c41c0c1170a5603c0341814401015a00d16107885030395112281071144400f00309903160b640c603501c4d010038045113271403081c422815a84841c11700452195600280555440219103102c03a029030f14031030b10005612525055002806090000c07059034880d210002100c0058600d0a511440c1c4e1105c11841d503007502480110203032506041080c000c036020065100c1082042002d078140d90340e06901c08514042060b50b42d58840c86558640b25a1500c1045694540034010100820b05160004600422030b1040406a42d2031a030040189441c040800c40c0340031240541c8a9145a0a00d030251141841e10900b400c0c1881c03a40080341b903c8222601034000d04803e03032407500980040301002050710409400180c951417044c02d900d1030f010380d840782c0341c1440c0c0d41d40c0190b0740030031250702ca2400c1c103940100604003850080319102004d402a04a032243d08142d07261007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 549666537 1250 549665287 549665297
    0xc020606030f06091207030c060e1b03160303050903010f050903030709080706020a06020d1103040c1806030b0c030907030c031b0e06031504021908030c07211b05041a120d 75
    0x21703e980c0110102030203010b03110b0b041c0381c0c030350a08603605d1606882241c190a003040d800b6a90066040344c0030008205ca0b01c00540152800303d03c1e0032210f00c01a80c02d80005010b1020005414005440940c4884074001c410035007000182024000152a940140c80040000d001800d0108402c0c901243ca07004840c0281c005003c2c640a990380c40019411010618107110358130201c0e405492014001544503a206109a114482c01c02c0304016401005155040c00c091405d80c00b80700040c080101a90440b8070382c8001e80c0c59641d6070540324500140c0750801040014150400410021442d1240d080d2010743e081828116448004c0520f02c090b040382c0c80d55143c2e004440c00c00450110042188d04030b40040c00101d4030301e0f82c00003016082c4c02140e2143c641c0f5480000e00015640c2d040c050720000d00300f6615140c6003584654941c0408400c6880c002d0b11304581e40c8000b041e4070b1401d1424000030040503100f1b000d091540c42903481014410705100d03000d06000110725a200d600405c08405e12039058540b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 549667787 1250 549666537 549666553
    0x60c0102090f04050906040f020120250515130803040303020d03051e040311070e10140301050103211e03020d0b01020601360e030c070e101502010207060c020606030f0609 75
    0xc1c000c031203005814241d050140d890b4049849003c40384100040c1c2c58440300a101c00380d21f0003a00303014330044030350301d030001d4503000400d00086e82d030007191510b62a09000684d40301c0003400101c810032105d0b036005244612000400008154010802940a20081d201084a5501c80a032080031002c00014960380300e083d4000203000a004001031030300143c00d001100c903c640c40740745c0c101c00701d01d0581d0f8020a01060400801c000480004600c1c00040309030b00a0249516543c1c071130001c001c03841c5105140f2207a00020b0043e15206600c030b44076442001c0000d02c10b0700421140070b030080d0301400041012a090074440c11155000099040c100e0745442c9594034003400e407035500301c4050300e035580b50070740c01700590000b045107201400340040b41c05c8100041c540c0c4030740084441c1d18021449e401000d14160704010001c0306011004013104582c541c0b100e42404903d8220100e0081c03151000003040c1600e002c0c03021218550000c0c605115501c25400c0341c00e600c240328007142d519501122183d00b990b0140c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 549669037 1250 549667787 549667793
    0x1d010914041202010e0105010305062406030a18080301030309150201021806180a030b090705011d01080402010c02040e0105061315140d0c08060f0a1e0515060c0102090f0405090604 79
    0x2082c0500740b69200016200e00740d22100707030a4400a130300940c1d141e4084010300c0324400f00b880441e0074004040100d800010000008251140001004035480344d0381ca8010520f0410f0307490403142040c0d0710060341c03a5070b9a145c2ca0068501c9446005042c91f00303112411240085e40148201c0380900d0441c0d01c5169061101d5040240641c40242070710200034803803140740741c19260041d128024500c142d42c001018a45014642d2404d03045170b0280d810001c08220001100c400303220b03030506c008003e01e000c0c0c21565480c00162040c01c0407000007500140390041e9001d9942c81903020301e0003020103c48200d14144100c880900341c540d41807694642540c2607800300f0000000c4004500c62800103040c19801e00ea20352114100c80000303034001203407900042c08001c91969016110303940030011000c10486500c0315580d050142007184049200d9581d20004a00c0a84108200c981d1502d402081c603a6036107240f01e9014003031342015101d83e0003119180300045035882c050107000c0c81062001c000708843d980c1e41d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 549670287 1250 549669037 549669053
    0x9040506030304091404050c03010606142515050a0203100506030a1409030a030501080a0b0a05090a06060803040617041101120222080613050d0f0e06041d01091404 72
    0x902116410b00c010000042d41301c106006200c41ea0420304440c682519180c1801c600348840460380510a91400009006468200c1403ea40c1c44a480401d140c94203615100046e10051044e00716206400c4c008040b81040700c2d1004000e040e030209002480580c841340c0300c0078240d00050300d0865285041041c10300980c1082c402035540b040b140d450104208800d040c2e03180260700d064a403616150000503840f8801501806064014014800144030440042d190500c014802810a4401d1521800421144070080010303601c5240c0110042152035980c1649944d0796000d40b00d040c0110b02e90241c030001060041848910490300510100030442c004401100d644e0142001400415800d00044d02e402107100031030b0300b808132200b503040e0215003441500c51070200300400300d01c94240d0280000300042c0e800b0601d4090917040342440744042c4100d00e8151445050105101d4100501080000b40c0c01d15140c5420010070a00042241036600c404469060f50506c03030112084035a24408500011642 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 549671537 1250 549670287 549670291
    0x405012c06132307030b0a0f0803070201030207020d052e110a0c1a1e0108160e15061c0c050a020a11011b05061605090108010302060a030e030408010c031a06090405 72
    0x4040010f00740720b9918409101100640792000069503500482d1400c2c103204410303502500300c202c015030000c1d160003200b50703480c4141c00b130080c100343d00411342d0710454850240886459034401d0580310b040114210020300c281e454940100f199050b500812440c0125101e800c28120022010515195065005451222000508071242d04801c1c813071440350f114003031102c1e00816107140361305009400701000000b40b40060b009028a90005001c40030303c42a20001c0304100e481039810726000e607507010300d110b42d200740d409030464008800203642030500440f060000e024034201c000401c02070b100040100c0d141e0091105020251f0b100030105030120f045001c1d256203c0d107051503c14800070b18000c0751241d40c0d0390004200c50660044003805142c006507100080040c5083c0340c681d0034404c1500000b82650018403002c1e0042d10009603074181c03644a90070001118060104a039600d566800781da87c02401c00050410002c0d140007036444c8080d4040004280340b001c0107141c90f0400c160081040010540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 549672787 1250 549671537 549671561
    0x30b0a061409041508060703060510090e28020706050619030b0f27030901090603020f040605030c1204030207080c0102120307120b19060e0603090d14090405012c0613 73
    0x26a84c000101500200601c070b118501c269004207446151005020000507548004814031003600f80901417800c1001d10140c0c06001c3c08001d08032042c80010340c620200118052841c0720380000350740424032480c4e13000240903e1090b5020345680b085a0001070780b8046600000b004680d229010608404509240d00d40203800444a00110207a05d500c0300c0341100b2806400341c580e0404113594010b9078112440c2c41c01400749080c1503140802c48240e08510b48258000c080600c080400820001c0d40c8500548502c00610a1811840e00b414200650703181c1091054145070b10400c00180e103554800704400e01340107d0f0741c44440c02c50716081000c0c8c800e050025849031180f60f680391041c0040d0b64001d007007054814110007020711a03040ca0340060880700c3c0b07c440c0310b00910003001401039080c000640c56903490714500e4611400c0e101038881406a1207488281507109007040008508190881e40d0448038130b02c68010180313540200c5601d81d44000e012030f03805600042009103c101d031714003070308000c07043e0700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 549674037 1250 549672787 549672821
    0x3030f04022e08041b05061903020f0c0307050f0a110d020111100b03010b030f070504110d02031e06120a080906070c080105010303090e0903040323030307030b0a06140904 75
    0x305140c1c041e41400000c0540314005009030060100b0f010751030080c0c1c4e0040320b06004050210b0704050201d030403441424000e2020f0101c219008c62580e200e40d040d80c5900d0b81c0003100d079540c2c1d034880013515a240c00041d402e030740c0c6015489802c03566901c002641d081d1140c4c41a9010110070240f410849084a405000c0e0305000d204042040380d00414450040030741140b01e0005645810b4005140c2110310707860b00b06000c0d41c460360f4281e28001c000078000e411540304423400f041030007280325509068000c081c04104120f0010081c04a03c403942810b481c484242c00f0384000043d0341d054204580f4500500c0c0f101d0440d04604529800700d0740c0d0100808070907070042c1c100d9242c10580d80cbe40c181c2c0c190b80c0c2da0080c1880c2c0d550f42e006000b09940605944000c001040c0300b04410700f4071103c450344a2046100040140c141900c10740d4a205091420314480701a01d410390b6103902d0054070250160241801081c41220170740b1021030083d01035000341050920070b401e07482c1080c00083c01d000003040e14a2070032200780 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 549675287 1250 549674037 549674089
    0xf010f150e04020c0601080118050a060b0102030f0a0c1e0f0308061f020a020a05010305311e0b09010c0905090405250303020706090501050d0207020f092703030f0402 73
    0x2880b503000070040500320380000c014035850300e0b035058211416071131744054008a16122001042c3d001031011005034124500080b031402440050b0318611400320203442e0b0b844041001e20b00103070000115070300c803406490480d842d2910b60110800100174010014030b0003d1034811035002c030f44100e208513404a00078201580c4406051a00000136881b0b01c480f800581c00001c03d401141413501941005200c2070038244001e003014030380d80e0035005402d101c080b10004048003202601e4016100700040300d80181560114100b24411019404468001551001016801700307001000503c6805600801c0717a03031381141507040204125042c1005402510b0b140f00700c0b00c900143d41e011141c070154018540c00701060321880e502d0068144001d540c060350034003040d141d04020faa60040b0455032200100c0e4001271340c4c1c803600c0c4001200042c901601e10b030000c0c0c0c0e07c401c000c038600703c00e6018980140c0c58091880382c0504040a40c0e0746c3c0c402140c114070710b02109c102103001414083c00c0d80d8811010f03400f2600c405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 549676537 1250 549675287 549675289
    0xf0c0203010603060f0204051c120f0507060908030a180b010b180303030112020112020301080a02311e09050d030915051509091903050f040512150f010f150e 69
    0xd01c02c150052001700c0d9002078100a2460b00b480c0c0c4040104481408845211003501c8035440710110052910500c14681d2405c40050311501c11a01026032000b0100480f11140c00c0c04a469001215820041480c00380f82e81c503100d4404014007911039204080c215240e00748511810b6541001265000c591804441c8214641d001e001441c007a000343c45020707410035094000189000100c0c24803038500307881000184900d40740400c03620403140c2c06643c1040040701501c00303910f551107025030307221160716032101d403a08100407a0000d0f20400901120015624001e8444100300e800780a4003c03d198010702c00c3c1141d042c0281c203c1d640e401c4c0178103c0341400c06644c607000801d0702c1c07044030003406854220701703134950174503211442030b421a013848000c050000054110407100c0700e00000190078460b0108140881d820448111f801911001d41034031071070401b00001d1540c075031081d034034003002503140800901822074165842d4100c90300350268000c024604000301c112005075102d64810850381255180356 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 549677787 1250 549676537 549676541
    0x90806040f020f0d020a0324021801022a04052d09061f05090402030307021c0605130b070305101a03011a090d110f0a0b0d0c051606020904090515100806070f0c020301060306 76
    0x40d10b2b0780c0308034040d84249208002070030000c180c54241010107155000414882030440e40c111241004d480001e06a111202a202c6c800e18046081c5150404c020700d00f101d05c604e0104c0c0d41d000741c07201d0f070031a12252508107121000c807001444084200aa489040085140425202d50428000b40075a40703014015008503220880605d01018030000c100454001c02c005441644d40c000002c40000301c140045903654610858054030b60720030507444801289204103005804802021030304100102d00b0101070003030056410903ca2810b00400c2e150b2111a905c91050846e50281c0004000d2208000150f6a800001c2c5011007401e8002c0e582003600300070340d2517000103000030b000410301154030703241410040c0f4151180c02c0a81e0381040001d00c07040d00e0340d907a1042d401c60465448038015031a410f054010034000e01d00038501070100c0c462017402d4100300003203006e2907000e42e03030b2150503182d06910b0b00010340e580c3d0f0301624400c000854014040c0c0f442e902c11103034102c46500c004c0012460b95030340e84031181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 549679037 1250 549677787 549677797
    0xf0402041e091104060e040f1d060c07030f20030a0305011404110307110c06221703040312110f011508010b0904080307090806040f020f0d020a032402 66
    0x48080384104806030181c0c20000804001d00140500303110182d01c0000c01c0586000383d1064100b804400001d01c44580c0d22a00148490032560800304499080141c04002c00b600c001241d200c40c0c058440490f90385181c000840e0f00d540d41540300c08200c800d082030119021000328940b0802000300e040c01750b051800c00d0004100903103059801140039410f2500180000d58401c405030b10131850001702604490540c2e069aa029400c0c6c200384110740c06110030703903050082176010301e9805940001c84c00300d01d2960403900c2000d09a104880e43c0055105e10340040c141c0c8817015405202c0d4400e01c000c000141d003450b20620098030781d1428005000313980040070710381005980e020460340d4545002c503181c64154105840102500301c000c1c070282d9400320210300c2402c03000d00050a0b459000000408090290120308028030522040f51064038007400c00100a0300300c00c4c0c04900c140c0241403a1500c0c1c2c500700e010f41034090340007040404004c4c515924030340f80100343c0110303080c504000362251004a801d480600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 549680287 1250 549679037 549679049
    0xf03031204121214060f040f0203100f1a0904020702060c0d020c03061608041e020a1202100507150c090506040f030c05040522080f0c0d0207080c030a0209060f040204 73
    0x280202c80c000300003a003000d209150029419242c98100600380d09540d50850300008203594502200302c049000c00d003d09108080c900c2c46038000401e000190680386605003c80b109040c000c80c02ca51101516200c4250300e18103035800404c01d00000031b00386490b50003032404910082600740382c0044500c0040c10440d0401442d80940c02004480400c0d003414031505511a800d5050440e90b0480420050000040a000035000b0300d12072490861750102c1046100c0c0541d002050a007045d680d802e0800d02c12828414201c0c0600c00f10482c100070700b0301400655034080d51120307200c50109004440c07030004090042c1100100000f1030800902a22084003c1026105c0500c454412509604020301c0c1c02c040e0350b014601492400040214100702c0f180748414580d0514034030381803100701d1b040c10200341c041c3d00701c0e4000d9060002007064280300e002912002094154080d02c0c0b04a90f285030080d02c850160042d1601a00500102c0b001842c100540c680d0020004004004100d20f07070010500300e8000750400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 549681537 1250 549680287 549680303
    0x60f090c060806090f09250f0b0301031a010f060c051018030306050d0210050a05040510090302090f190b0a0e0a0504210c0308270102030610030603020603060f03031204 74
    0x11200509000850a500580a046412580c201541c0b12540d0342014a02003142c1c503a101058020091040c2119000f4241c07010208e800300e4440a00c035600b503100b8070048591481010824004279040c1903030904840c0d410412000722860300806498641c036500040300c2d03070b0180d20883d0181e01c00e0751050300600100490074040c40480c40c50040c08442260300007034418405a083c8400507601e50b5000424004035280140e01c03500366140070f607030500598025651254800075035802c040d5000d86c513841102e00880b0b0b8000741e40c6410300c4c01c00404200360380d45402000c0842070403c8206298003c200490300103800400a00c2e6207140c10540f4120603520039190030303180c5040c03100340015101148140041980001140303011100041c25071000450001e0a0184803000034601030680d00b002d502c82c00000c400302d003081415407003980c000d51003142c407140301c1c1034050118500309119120f22000d4036409046079103191500c504000003141031b00302e101e40c503100c10014601d0b000c24006990f80910b11400203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 549682787 1250 549681537 549681541
    0x403020114280501080c010f050c0f10050a0c020a030f020c06030f0907170c0d03090b070309090606050c0a152a14030708151f1707020c030a060f090c0608 68
    0x8070410030400b2000e122902030030800140003188010420803000f401c01d003050461003000c20010b07aa41d00030103406100a000f0006540b0440201086086820417822000c0010703950f940382800488000d1020304005a00c107840d64800240101d11500c131088031401101c6074054104002005070744115040c03100c0c0d6007550180640700707034104025005443d101c40740c512006000c0c481580d507240c01100c40c51141d03699095400a1500410100c0050403170386401503aa51705604001e40045024030030368226038034011000030f1607403150041c1c0d128014040e024240070040354580c1c0c00c003080d00344440030405036160b0040358041c0060417807020b003200b201a01d44000c01101c2000d007290b42e40130050100b1590800400032002c2d800780c450ba910469203800e00c0d10071603206000c80e8009045503015403c11200300e024074480d603042101c0c0450740c00c40103580c261a548a0104a89840c8100001501644100c1100000464a800c044114120761800240905d882d4039403a540d5a01544100042084542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 549684037 1250 549682787 549682831
    0x4060f0c0c1104110a05160b04080a08010905010503030a21020309160f0605070204090f050f01020d060f0308030735040b10050306061521013206030403020114 70
    0xd040c0d0b01d080b00484081003a9030100148500d60312910815808004000a881712845280349403000382c40d0300002038101d24070741450a103601e0f82c00300c800c0c0400304141400001e1400003a0144c41d050301e0000c1c0285007000e5054400703a40d0a1706144a98480d50001d4004074a190343c2c0d440079500c40c0e00d01c2d0004050221100b24410111111038101c240300e8449a00103101c41c1d900101110843c50b419200001d4140c45402c14503100d00d145240141503000304c007000405803c054000d002d0080181108000c6256911310b0008081f5040c40028904c000600001d050300e03002d0122002d190900e441c0310f03480d00302504c2c40310740c0c10f54070808031241500f21b06007403100f0710000340c4c0d40690014078454044240340c2400e000035a034a00041109115035070803416140b20704000801d03506800d514203241070098540d03401c2c074003010509009064104040c000c0e07609422810214090315500c4245036030100c54640402c1c0440c540c4010300c1a0255901c94541050444030310800511034030f80a40d01000f005204c0d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 549685287 1250 549684037 549684053
    0x2030106231e010207060f0e03070b090a12120f17100e0603060405101107020423090307120c031413080f03040308040923150f060307080f04060f0c0c 66
    0x802c00e40e1075451140035420143d0f00024580c003075500d68101804211060b07101100c4094911040750b4042c040d10000280c51100762028056076241100d95002e03058490042d1400c0204000c0054400000c56042a0000340910040d07400f0100c43e28202514141c43e200100d08042d080d203481501411400701004010000d103e55500410110050001030800d502e40031758130701044400002c2c03e5a0b0b41c40000c4244080d000725050207a02910910400b444032405214500c000ca51010390301d048000015011040407045900b060f40c00141c1c2c4042c4855040101c51040103c041141844020840182c080e1188009007d11110283c1451041c5082114590816804c2c802c0b0581942c0240810f20002d0480420b40d02a515046030000340c4030501d80104400c070b010303134015100c5490030344103005070702c4c400183d0742001d04070130b0750102c0206040c217080c00400d00c030031103412001aa2250200b14603480500030340c2c1d081400b03154017060031b01e8150307008800c4880b81060400400c0580301a9000c2003824 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 549686537 1250 549685287 549685309
    0x20403081b150c030a0c11011517070b070602090406090e16050f030325020411070302150606030601030c11010c1d180619091a0f2b0203010623 63
    0x10a9482c190f00788650600c80a020207003000390036603106d0340343c502441c1c0f18150503500303146184002d01096102c4445045458058080d0a105d98141c11012102810008401049401c40c1d50708a02d8000e80340c0303454000750882d40055901545a040c00240c481141c000e00380510b01e050058010b0494a5005190044066025074041d00c0e0b4030301040815034022041e505244c01500f8035443c0002d617000c032580351070a9203200a5005140c54030308982d51115801404e41d45220307408844c202050401035402c2c112003222001d0740701c1001c00000c0c0391540f00c0d4001c51380003440d03400d20512031125100081d083d00c050b841590f000420341e1030f41460301d48880c2c0c50a40025001e84d5070408420280da200641103e00a0a5902450345095403071501410140382d131000301104903040264818003141040040f0180301d00c2c500c11201404001030303034135051040d4a54911a00502601c2c01010300780350703000c84120a0140d9242d56074050000d22200030266254402072001000800a007401c0300300080d001d82 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 549687787 1250 549686537 549686563
    0x715090c090e0a1e11090702030a0906022d0a0c0b0c0d030e06010618080d05040e010501031b030506010c020d0c05040507081605091f020a0203011803051c020403081b 73
    0x2011403c0041501161030b902890741d140c0016038580d015061000d41500207000c819004071624080268480d03010001d00880702d881d80d2540040c40da9004220b944800d40020784110a40c1d00c40c181c0c0448042070b00250f03d031400314080c0c560358950ba445e103d961040c0d80d4000400c9080c00107040051040500145008070500e040401800ca080804995a000705020341000d22001042104041f02c40c040600000c10140d0205c4104001c4488020500d4100340304865000d00c1100001c24950b000e8010704101e01c800c002400c8850f0240740c0114003070a00600705505200c03559055001503203034a41f49031100e6005811400032240b610f400d010032a100100036608022042d400d000410369280b10f2011030590b140350154850f0b10381800101e00141c51500309080f440600c10001507580c0114082c5001070086008000f15600284216000201e48000030002402013180396548442d5881c60240c554140703130014186a101d603110401ca5010f0060465111140308004400907402c000242581c12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 549689037 1250 549687787 549687793
    0x905041a01180e0408070303021603030911010f08040b18161503110403030c052a09012304050406020c0d0c1707110f030a020406060c0311070b040b0715090c090e 71
    0x225203c0507101c503800260005041180006440c024144690107444c24940004001004011039241c060300400d1400800c035880200052420169030140c01c60040c420100d44900515039100d68400c041488000d014210820341c9480e4805071100404c118240b40104c0a50840c047e41480b10085142860b044c048007010b0408144101c98064201900c08595050030a01c9020010303103005810407594600c0700c40310340f9003003603c3c4000100021141c000d0b140103030380703014559881e90703041600140f5440456240000030074084500341072581c0003d511078042d210060500c0c01003140c050500d4401041a400100f11620060610002400e0391410f400c0d00602903192503010303650040040102000c60b0b124000f000700030304060b02e0134440b5154042c1d0040c810406c9035268003018102e600f041c60203130300150415506034140c01700090034a050325808048036060624120008049030b0004900b103a20324000c01f04400382c0c0b64035004510400c0d110b043d0b482c01d468101071500c0c0c101d0310708041170031a81d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 549690287 1250 549689037 549689039
    0x7050a03081e070812010504241e053102090f01030f090b0412030b120a02060c030705070603051504020910120b130203150307030506010e04030905041a0118 69
    0x1110700007224000308070070802c48228410185a8410760140c0d0401501c0c101c0300040085120000e6201c05040e00c1c0d04460410946440c444032010402c0070044e00410301c0601c8509100121201905041d034040300c1e0710740000076480e080410000d98040b00c0c0e000001c4070f03810729800c02c0340c0d0f070002d44481c9012002c0110706000701000007410401109603843d050584e540400c0d00074030f005400c00da982a4205001a000d400e107480c00c058090583c159040002e841d160010000d80b80420740804028028070003849020007035001c01c10140e1004042c111390388001c00680000075000d02a543c0104504e860008951503c0410811003050013286680710320300c10007150040c1c0d90361f80240780751000c0c02e21f0035058003108010f9400c02080340d104c425a2003107855414445194040e0000c610030311500108040402ea1b140500d95241c005000080207900090f0040c04807a03083c0c00306c164058000d1400807032007580e4601013011180d24800141d80b10503002d107400d465507009100002d11191030007100b8145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 549691537 1250 549690287 549690293
    0x40c08090709110702030d0e211203250c0510060b0307030c0207170109020a080a03090308070309090501060c0b010b031017030702060307091502070501170703110a1107050a03 77
    0x2a80d402c1c0659040303590398a6a0110715540f40040e56a40c03680a8211800304c07600c0c00f0081c0800c50300707601c80f80c41110790350070403040050b0050030247d0741801500100151b42c0c51240368005508000d010022844501404001c8844110030550b41c510240c0c8a01d03c081c249400c2c502d041076009803c0d20301daa82840d400b00030b45080501101d6005040d850001348005000d802217080c00c0c2130740c1c4106402d03072104800121103001075011804451085800346602c90707452074250380310183d032200940452540340007000030800e90740052803014428540310110300c2d203c030031540c1207403820781003600081c041c100c0740d604020400810070b002d1b00b00d2114040c15483c4c8458084c2000905000e075611070441c5d101c2240d80d20108005981009a00130002138681c941014010042c441510403c40b40302d4035640380c5065680040780b51019118103039141c0b08140910050003449000141c078060070036031394a8220450940d440d000d01510b491a41d540e180444204001034500440b580000b03103e464100020400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 549692787 1250 549691537 549691543
    0x305010b031909020a05100527100f090b040914090c0319050f19200a06080c09030d0302130f080d081801180303061d0f06040b030a0c05040c0809 64
    0x100c0602e030078010802d00410720204a00055590185400c030082d64040c0c4210b41d00300024010040818002e8000c200c828030401000c00500c1081d00d4015015909081010344180d0380c08501d5522410801c1d4234503600c0d03280e04000d9105910400d01d0f680d0f29010000312601c420305164100280100911906045c400000e4803214080c00d00c0e01041451050002000401d014080e01c41052006854000d1003452400008405004080b43d104150719641c9103480c1c06038482422240005d0b2400e9449410030f4000c2e00d00f054043c0c10164010b2041c070400c1c02039581004501a034100039900940c5480300440300900584068010280341c4044d10b0051110740300c00201c80803c14904c1c5815406a216011010782d010740d8510302c803030b0079420724440c500d411211032003080c0107900c20754081040075a01d0400b5030f41d280030502e6088034040c44c480820300b40071180074501e42208009000040100607900080d10300f80141da801c0b9144c520202c0d04105524052280b8580c1c0304041c2046801c62a01108440d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 549694037 1250 549692787 549692821
    0x406020c2d090702010f020c0607020c01080f0a021303050105090d09080102280917060603150f0a0c0311070b01030c08060103031e02150a1406040b060924070c03030305010b03 77
    0x400307040742c48000f41d9414404d400c5841032090040c030855846480ca5105601d400c01240c580340036207d00346a02c0140d5101d6000c0b14807074044031180407113a0b1039540c5402c0c00b1f50f10101c6020a00b0040c0390020ac0800c80a204150150b800c17000144042c420554000c1d01ca81143d500c04291a48148400c0c0c1c60710307400036180780c0b840c01a03180d00d03882c0e103d112505a45241d016000000064661001000380c514000784c5ca5004100407000c480101b4181f000b9030259a02c21036100d03144100c400042848030803541c004000307404503400e0215105600d0b003110365407500416019a07a2100c50380040007071186420b501405003003500702501003507056403800340444100c3d100c03015a1f08040300c1c903480101d01c01d014440394070b01090010303141ca08140b0100d1002c1c0007004004a50745071880003143c420b00c3d00b481080c40a2002405d424104100c00b0200200c160002c465598140c0181110720006035004005010321486040101c0d126030075804c009040b03034030507040014900020024824032000c2c0f4070001c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 549695287 1250 549694037 549694039
    0x12070306212a170606040603111002100c030605120102030c121513050f07030b03100c050f030a0606082206020a020f0604081e120114060c030406020c2d 67
    0x10091480c142004010348072040c03110000c1c4410381404903020942590083d814402001122640c5c1c9800c1c0c00c120403186223210062181211140d0701d800c40c03c001500031100050741c0180c61903044480304080c280e542c2c410309000001e90303c05081c409860700c0c400c141000d8892000031400c0d464221920103591184210960b24204035000085544048003107001d02000003403c560b000c01d01d499280e00248c503040e201103101d6811307000041c411740c1c0700b481072804c0c03c1e0005004118401c0c0c5604004020040c107001803040007010130100c003002804200860007400740160004005281c03500041035810302509842607240c4581182c400d0078043d01c410400f0640007600143da625810718181d1814091090381aa82d010b0b8000b04814400a100508180f000031400c40014451202090711a8403c102c8810058000a401400041c00c012420340b9000800340105140c6040b8003030491039500242d001400690000031403031a9410201c455600031840020f03000700030005011100c020002d200801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 549696537 1250 549695287 549695303
    0x30408060f0c0715060906080114011404090f1101231c0b13060e06060c030f0d09020307030c1d0103021c030201020f0403050a0b01062607050f1207030621 68
    0x402d02010342a4100c03686254050302c0d0010302003101c00b981c4060540e91184c401c000d442c0020016005506001d0810122540840c80c04944c0c20101c190103610b000301000794205942c1c0c0321300300001e2207203407801c00224040c2c145180000c0600000400c400484c00284c130740800e061005500c241d503148151000c402c11006501c0072040070b982030743c00410b0303e413265690040c10921080c102c5015503010034140d46d072403404000140e8500c002e0040c0c92103820055002c65004100b0300207102115000350a1540042da4042212903850f0002440c00b0400e070401c2d601c60211035002c02003441c880300b0780c00d12050342c1f01e601d20f9903615540025042c0074040e000c0040c241c55142400040601c01c1d4121456817079407a4001d0340303a944030304056540302408002110f04032513010020450900071441828207421358005201c84040a90307101c250408007130100d10a1060501c1414100510100503023030368061903484d030149140c0076800405642107540610794400c000030310008242c8540c000c40c000e00c0d0b003142ca1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 549697787 1250 549696537 549696541
    0x903030c0f060203070806030d0906021506131d010501050109030c0302060315030601170705030105041e0c05040c0507020301051302060d021c0e06011d09030414040902180711030408060f 82
    0x30301649010507200800440c400000c00041039000b074001d1340030b21010707401c648046452200540f0302a0250041601581c07201e2055400d00406440380740d400031000c0c0c103843c01d500d55095100242c50311354040c0018503614401c55400308900b48940c500400d001d103801900141380d500c40303111503c0c0c90301000c0e016010020029400c0c02c40e0a8a4507841c02d0045d08440a41da51000310f00181c1c480007038070003c9801142d000044900e01401140d000e542c00090410301d04a074201400850b903e0b1101c00c540510003860005001e658a208200e0340c050313640c4a060b9180b4580c410107084843c020000e2109110320403e100158480800741c501d0001103000050351018a003541040d0300c80241c02142c40107003040307442c20900d10701090342e5041341d500c20b200301c4500490f000300f00c580b0700c0c1c100e0303081d0102e43c030601040140c0c1b000c1c0310318268401006800040c801c40790350042110484003440310400040150b0500c580544d10600041042010101541c1841c0c01c1562241c1c507840054500d064060078400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 549699037 1250 549697787 549697793
    0x18030b0a0b0f0d14070801060f051c05150609010504021806032e081204080a02011412040b150d110f120307050601050f0f0102030d0f0b030a060e06160903030c 70
    0x90300101c610801445081c280c1d00c20300c0d011155412594048040c5e002e0400b0014445105001c0d010540d4090b60f11058018107041c20701c00381508950b9045804d0001c0300d8403d01068051200754902444d160315081d041c64290207100c00d020040c0c2c0954000c0d0710401010446a20079488015170000403102256251100785080c9000c0d241945224402510581a8141c40ba80c1c0c0303100c0c00840f5a060207840d116140500c03c00c405005074403403030b80300d078104081e00c500540c41104800c100c20301d0f00c0509402e0101c0000c40d4900c4440440e02202c0c1c007500f0205000c40360904070016640801e0441e010540310400e940c6048000f200407458500480d030b0b60150840d6036907402410006500444202c94036a4442d0401e075541d11420300c100d5001e12000d8140b052903041c0341481c04590703441a002989000c0e814064078000b40b2192140d00307085555000036070301c2558140300090300d0900404011907a4001d4106690400304085d00340c0d0100f070140d5020400d017503080758041080f640c044c08c02c1a860000e9003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 549700287 1250 549699037 549699049
    0x7030902040b03100e06010801141b120a020a090e060a0504020c01020403020405090706031109012c1903020406050f0307050904030c0503070b0106020c09041520040906030318030b0a0b 81
    0xe4801035042c040c1c40c130424203884141e44145004090034003190ba180c3d0740c940d031140c200c0743d416244c012003d55100019200d400554140c9050300d0055a84618089000c148420701c81001c1c0c4400c44003540000d21000c440d03030322079400e00203040000581086030521000164926055200d13441c00380343c008c103000140200c2941a10002d54000d80240114034106c1402c5480d00c0c024000c03030012925040385216581c05141c296152a0410385401204150005100c001e41c2406805220801800d12402e590380d25566007110406003403401c1035103103d08600c100b0081d0b45164004034029142c0d003049a80c0b65a0000e00d20341220f1040e5241006512541400c940010000704094118400040c54904002e00b260f403ea04a510316801c1d0750f0f4031000c007400c200501105450260110380080b6088040108c587e21041031030341d500000354044402034048462641040d070145c0f60184c1c0c0da000030801d264001c0c52410090118082c08072110341540d4444000302c0c40030708040c0c000365580f2400051510b8032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 549701537 1250 549700287 549700301
    0x714060705030a08100b0405010806010318051e0f0f071202180c0306010e060309070317120901020406030b061e1e1204050f0f1c02010924110c060703090204 69
    0x4058943e140401400a010b542c0300f40c80d20700c90322900c240002036000302a000e60381555816554120359072100f10045001c2c00d5540c0c04010180c00d111484000140d00300400060346e07402d01804460324081c211681d0814201603c80074841d00310a00d00400d164010030100103442ca03c40f0789841042c460700218003040414211610004d51180500142d25884005140704080076a100b0340800e1104083c03001902007580d88410aa1050b002480060382c00e641c140004e081040d00141040c60400d100340d00c1c000282c60fa404181d500090621500f0381c0750081a60040c0144d40103460121500e0600d00070200c20480c0c240440350100345903101100321000003000c035000b40d8201d52150803141c1003c0900c071003036500300d407a44a601010700c5c62420204110202c01040c1000d0502c02c0c1800000a00d00150b1400603011035588040c1840014213800c0c405801c0c0c0d0390031a40c81598405074096104403010024a06e405650a02c8501060400010401d6010000307140200c0d5008040c40440c01070149 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 549702787 1250 549701537 549701543
    0x5160305130906051c020d02040e1903030504050f06070906080c0403080703120507091a07050313030c03030e010311032d090a06050a020909161e0f0f030e07140607 72
    0x10700324000603030290703a4022405a070300443d04c60009000d0700360141d1482660000081d0002c1c034020441026251907400443c4000124090b510040c1341100c980d405d5001d01c031012000300750789030240030501c40104000c203180482c140c01084c04c2c1c182044064031340803e074400c074404c0100d072500040000c4040800d480045a00c1000551100322514002e454258403a0700d200b40e40b03141000055203288140070640490f0b41c0101079585214810b0000d10780c0354410384080d40c061004202040131382c00d10441900003107000d044030740340b010b0440c42c00a04062030462904d04140c00c1c044c0b851203c01000003103c1c0c128250400150509a00001890105042410b1034404610b510304004015002082e440049442000c040050b60388640d000350032402510602ca0b0028052000030f12106110a1016040103960070300000b8a69500c03650182250442c50f1580020b084020140c8429000013010821102ca41001e1000360021050b0343c0d61070240b4803405080c00540105040151600401c5500c0705070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 549704037 1250 549702787 549702817
    0xc140703021f061e0f05012303010b1e07030e04090201020a02030105090105011502030f1603050c060903090103050c161712130c0806041703100b0304060c0e03010c05160305 76
    0x4482c98480c000340003e100e0003e190684c80f000360485030b0b51140316002d4400704000b000406081000440da80c0000d07280c41945800001c090b0102103000c00d010314001c2c600f0b1141c2c0741d510319400310000c9540354030f607003003801049c0c06102413400250403040ca158a01c00a6800068000701800101e00d8a406050080d405501e0a410300c2202803064100300c2c166151003008c95091003540104030380d83c0c07141c03040051070400188022920100f81302010107000c3d0081c03600b14144204000781da810141c041d900d0000325072001510401ca9601802121f902140c810030481c01c1045132810180d01050041c80248501c10407500301220056038415201c6400000301c0c1100340346032880b20946000000b150a45034100b256400080500000a2031441250b01c80300244400200300d0f8428095040907001d281d00400e000e00100d40c0ca0f08180c0334610803402400d02040f00f00c941e04016000c0305001c0340850199041c12200850150844200c0c1c0b40007000c0d0506012418250a08a0341800b84261001130b0705 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 549705287 1250 549704037 549704083
    0x10513090f06230f0102070605030c0306030f0304080a05060f16120f060f0e0c130e060a0306181502030601020a0f020402090411040f081c3f06090c14070302 69
    0x3c04904048401e511094444040810310400107aa80c3c074100d2041d20000307001040000c40c003503121000b0b07581100000e012034a10201842d1241e09680282d000400564458051b02e4280181041107503002164040729a100381046980c80e10207132204600070b814042400d1814607120420f90103428440c0040d001000043c0d241c2e1040e82280e0b4482c410000020456400b280711088140101d6101010030f10002003e1841c0548160206400521483d8490020000040401da550046000d00b0030001d1079019001d07600c0ca00748406222901c20f0080c0684180104856a6000154001c840303410200901043c66035100280181c0b14982201d82c05c2410424000300c0000d041d0302800585d030010481580c41510748003582d0362140d0504a0400120f0002e110301d9500d401421900c81186115001000600d101c041c800c4141342d00c82d84c000038816040d661880305407164811440a442500400c0c04900d01e0184000c0100c1141c3c440d10742c01a00020f00c0303d0425000300005c0040d0640140000c03001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 549706537 1250 549705287 549705329
    0x51b07030b0109061d06010c1709040501170d090602120702040e19050f0c09010303050a1e02071a0c0606151303120f0c020102121c0207051b010513090f06 68
    0x6805144a618251700c400c02e80456500303402e1411a00c1450107944858190005032111000c0495000392440170715402c0042c40542c1e201da00031a4041e01030b40d40b80c0943c03901010040c515150f0460f140b003041000400301800880c6e4042215074810310690225902c0f0320485c00082c1c010240386c041c0d081d946c42a0100e0300c032145004a400741c42d041c080c50a17501c40142c4880d0a40d04c1752042e41c4065448003101d001800000e020f0f10250070340c203410340b4090312901d87c40300045030901040001c42026a00c0450108513407405070395040340400d06090401d050004d256000f03650785002070849445501640601d0f0301d242441c80c1510350400303005441d034075a5652400c044440201d080100300001d00011642e00d101d03800340d034203800c0e045d9041e4010000860010b41441541d00306101e0780847c950f503503202403c501254009440744034000d1010300b84410007504c100d8920030742102410706210003403040e040ea010714003506d10b0840714968808291210300c2e458039002440c050b00b08001900c880c035183c50032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 549707787 1250 549706537 549706541
    0x6112a120d03050612060406090611070c05100203040806061e190303030f050903030402090402030f0d0503091605060a0e0402091509030c0103020c03070f05010b0913050c010807051b07030b0109 85
    0x320600e140c5041040b501c0d8a005e1091040d800000d0170700a9001c6004500081e0f55580484400b600503040010346490100e503d00c0d403a404004191182d025290f402c0c045450701480390b0110b20788900085140c9468030414607103032400141003c0c400d01548421619480d0140c8a95240c864020880c01000b03151207501d1042c011240000d80c00a0b2034014203400c00d075000d120f0f450081c100d4400960070350f0f42d65400c001600200a0080317030180601c81c405603800740100450341031134060303881d02e03071b281d282c00c0c900586400b2a200e03140f01c0038074030a1000c1009494483c1159800209450070743c402d070348140c0c00b0902a1041444550f007240c901c12038402600c500304050900f04508406a6081d40403041c0118203a0041581045440d007081208070000b41002c100b0b60401c1c0d01c940000714208400c1000602c2c1d640b011140582600c941e042003004121050241c0d960710b00007420094001e0409800040c9980200741586081c0c120944a80015070307030410200c001107500c40d1840b00070f90386410003240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 549709037 1250 549707787 549707803
    0x13031505060a0501120b0a0806010f0602060604091e0311160914070e0d0204060b0415110706020601051314011e05010c110d08160807020a06112a12 65
    0x150549000c01140c000d1a1681090701260310594980c401102403408200091a085119562264105100084e840c1052180a00a200c880141080d83e464880b010703060180062215100700c3c90444585e00140221403034001c00070104e50348001c0004c45142c292a20100c07845c2450151150780e9960042c400c2428410054401000d010300243c07031805100021001d003a030701100416000b40c100b03171441c00c100c1c450710b0700540001e00210703405940340c02c028030381d900c075070000d0500c042210031960002c0d4000c100540c41c01220720040080e1880c00c2c000075143d50040c01510310403410192403004a42440d00400c0182a120440107601e50351605006800c040d00383d20000f04056000000503958040d6805035030f443d0704004625a901807000400060b404400b608840310300c410b0082d020030b5010071008441c0284900c2c2d149548107400c1c0100100511654000030030801c1c607441c0507044040108166046041c21101c01d103900d208034007044504043d0590544d08000510b91040c0c84c10f00005001d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 549710287 1250 549709037 549709073
    0xc04030b1b070f230d110a0b01030c090e0303130305090112050f010305010501060f02060402100c170903150c07021311070302160803030112080304031812060b0105032a1303 76
    0x14104e01000b1011900041c1e891303003100080d04003014450419001d0100c1d070240500d400280e0b400308030650358501c0403007001e070400e030780d03d41450500707009103c40c600c21864000b010100a50035868454404c05041c1c0e41c0482c0101041701c04254203070705900607008003c401d0b1128070184901d2800480e40e0003160070922081c0d429600b080b00006190b0f024028040f04c10764140d0241002d80d8560702484000c80490046100b0040c03009070074008900c1d900801007260401c0c484603a502c40483c2c08040c5030246100442c1c10903901d141c00c0c051001030b82802c0b5503049a042c8e034210941022072940c00c00600302025080c1d081d1000255a40806502041c4102d4800702041e590f1042525128099940c1c0001d010312004001d005905002050303000b0301469015100e454403803c1d1703a4074442c28100502c89070340148102c0c2900c481175420458507000302980c846080c83c01c1800c0d032a00ca400c6062000c100b0030000c02d10100785005000100d00f54040701c2e11032500c1258100900d80d645042c0799800c80c0c5c02010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 549711537 1250 549710287 549710303
    0xf0903030b060a23040e090f15131509080d0b040f0b030c010c21090303020f0109031d0a091d070e190b030f010608240c04030b1b070f 59
    0x410985086070903a03042402c0c55070303103184201c140d4401d01c40da11405203a28000313000501c8009201c95400780c400e4450041070010b0003041440c0641c039407130003401c035202d2a810700c04041000801050b407443c07240416000b00b2142e10500d040003802c0d000344080b4402904906000914900d074051640050f40c8220082e42c08014441c003d0b010401180c1c040000c15034150805d4020700c600d507100707010b6130301564010a40c48101d00200440c3c4c9800e00c4000c40380201085c0443d000300203141d0180b248002c0c044800009008641950354020544440d8401008003809a85e2003c44241c40c6e000501c3d000d480c000341c00700503418128040d040d03030000200341990f15224007000072601288011015016940b00001200c04594100680015000603030409405104051482c803c0d404c00340660b00080410801030511281004802580d00b02c12000d501e84040c12803007409440c2c180c4000300e508494101d54100c0c0640c98031410080c0c0b40745614459048400042505800c0c000b08500704a00c1c58418000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 549712787 1250 549711537 549711551
    0x7110a06020c12060405060a0b0a0f03050601150f080402040f0204081b0f0a060206060f0409120305090c011803060207030e12010605011e020a020d26091003020909010311060d0f090303 81
    0x3e610342c0c64038100d5008195801c03940209114481d180c001d00d4040000905045440b9150900340d00c04070388551094078154041d0700100102c02402140d85242881c80c0790048420315400c0c806881d0200140000f0f00455580821036074102d100e605690150021000b07070350980d02c421030701d140d440e1810008244940101d0b0359510b8949407a024500842d81190054541a0345060411070703a0981c140d120f5401c50f45400604000034480ca6080f0700103081a20002260305149201d00e29004254035103e06114a00c05090801022280c903034003200c0d4482c0000da96040203150843d40000919101a0410340455241d400c0c2c46040d001300381a14401c0c6d0303903543c1c050080740c0c50074030422a0351902c9002d0707080701c0d0041015007064207031a0360407030140144000080030420903980910b030118160a4172000410310803d680b4000c000c50b0000e13140d603e82035042c101c180340081c0d03080d2010710000b049203002e0543d228481e00c50070241c03401100c2c99a8204801d80c01c48030382c070006d000361500c100c0c0000d2914803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 549714037 1250 549712787 549712819
    0x11040503070e10030b09070e041202010f0c0c060905010609020a0c060b040203150d050f120d0501080d080f0a0e12030403180b0414120d170a050403021207110a06020c 73
    0xc0100e210355032580c0300340c3c0040d2440e01c4d4080c4140024006102501585030b020030038040b1052000c0c06035200e903650041503111018020f0840340d6070071894000b40d00b001c030130b4102654032042c144c03240d50300888006840b48a6103440da00400880e4800d14055001107803405580d030b0401404000d03039010313200911082d0301d070404010403840100ca2641002c0d0181c0d1202c020740c20300f0012840390078802d200b1030720401010f048441c6005440c0c01ca90000082c002800060f0700041c4c020180140307554001080c840058490250041100500d941618503152001a0b000700180c0c201c2d41400c00e03904152602c0004100e9015240d904c100c600b41c0224040042c82491003010020f490111003031204d5550034035050040070408240c121a540e9880070428801130704168003841950038480ca00c1e212821a0015054059601c000c000d085c10981850101040080b0381c0224000720190381200200380d50380c1c550300d040e070f102911242a503074201c2142c400c003141c4c1d00c1e000180441641001c444000e40c540b0418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 549715287 1250 549714037 549714059
    0x90907080105060d18021e0a0e01080d050307091e0603051303021209030312090715020307151d0105070207180204080309090c0702090c0a170405150a0608011104050307 74
    0x3202c0c850700503804115004103545550700c103441500d184008038059800c2d580000e004020804d10025907800f81c0f07440088103142c50f04088000348915440c4d00b2596251540c41500c0d01c0c40380b03020100344000000014500381c0300d201c108014100005040e21410030541ca07006650065000b40e50101c0d2420000c145e2240101d2503281c4842d47c140d0040c903042d460710107404010380003007034a16014841403240f01c48100c0420b1025100c0c400311001031415a1501405009025440c1c1400b402e5402c1000a180031038252940402d401509010101c1e050032166800341d510904c00c500340b20035518180600408a41c04101c00701203617442500040031401e00c0d6240ca040b0303c6a4410f14401d58010043ea4049080c8989141d074081551501e150401c440307500811200d0b41c080300e44840c50880066415006900a01c141c03400101c40e44282446140c10b0b0380d19903840070002000c0411407011310004110b01220b800c07240240084400034400314010f08409403854019000e01882406100300c0810400408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 549716537 1250 549715287 549715289
    0x5040b10080c011416050c031c0815032a01080702030f072607211b0201110c030706020f121218030702040213090e0a030819060f06050909070801 64
    0x10700040c0540c02c0d0588010350760455034100030b032000101408843c00210400c604504698003c0d40a03002c1e00120000f0541095046504001800540540400c00581c04030410768050302031042000320075401e0700002d01d4002e04007581408122000298a0285001d0400e010030b10000e0321441c40e640c645d88800d0340c581c01002d070601010780d4148054004640b039110070081c07032014010341d000021001c080110749076000c0d01c2c054440204a0502210120503d01035184030404c5140c4900502c4407001004103100c4661806410044c00c1d1038007142070042800192a1120000e00b102c030403958074030b000394440d6082c1e41e00a5442c005c3c50030004055035110111100c9010a800139003182d47c500003140381404002010000d2440240407000042c0c80350f10040c42d00da045001a0003560b460804501c041da001d403c02c101c00354004000b03a10000b42c018100c01c2d0030900c21403c80007500c0d80f0300003030001040707640d20203181e030f10000500080e01d40c0c02000070590380209440c400d81a5459a105403540802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 549717787 1250 549716537 549716549
    0x71101030509120a180f031505070210241e05060c0c010c03050708040303050301090c0e01020703030e01050d060b07050c190605090103140f0105040609090b0f04081b0105040b10 78
    0xc4009030f80b03000002a002028212510b0402443c489071216444c8009509034001035402c008208041c001c3c041a042403800041c40f1400034402890526002500c940e0302c50388507001c4603143c440c1d24a0502c600100302c043d03100c42400c00c07032166584100341030080c801c1d644561414180c98a0104850801e141102e00b9030011100038460044a20300460703c54804240c1681045418403982c0d00003601c5500800046003c1d5540c0c549079410847d41104403400d0441540c10720903041700c4000181d802080103001c60ba0182484110000c41000580c0c462243ea8003043c0c44070300c0c20740041007948840380902802405030302282c054691080a00c580303d0b65208010000072100c000420810b44610020000e1405c1854007140d04824020b040701c40901c240d81c1021000d031407200600090a01e8821345004120010040c015120b517134884401c041e6002c0c050300c0040b08104002000d0058410840d07000c560b107200049519155100c54030b008060686003151003142d03400c0031030314070710711001d1420980740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 549719037 1250 549717787 549717793
    0x30c031a010c021e06030f091e15060114070503130504050402031e010b0607142116171207030b060a05090f18070203041707060c02120106050312071101030509 70
    0x2d1540800c00d462104000140740c8958000c07415a40f42c86800286004240c00c0381c00501c00d082c2801403030300385100c009040340ca03004e1182c0f84078405d00d000601031600d2100418408170a480b10401246c0c95000c540340c1d41860b010010b060b41c01c0081c00801402d44160701600702d00da054881c4c00f0802940d90540d8003a40c9540300d202c62410101c0c110f1208a40841d00c1c8000049416004020400d40c0d08180001e0303d894000c0c5280903014001440042d030b186103074014118013400303209192600d03401440d10361000c01c0c81c000840c404022006100c9582400300e82644d41c0c94840c180d070990351100044034014006402c00e80c0010150800f8429502613000c10381314a4100940c01c000d018441c40c2a06189038805601c04040d440c00c040140030b9805070003a5400355540e181851030142080e01180008250f550003020100074581d03000038030781070495044a03501d0412042912103405071104d41c1002d0340c540604034031441140706c81c40003024014800c4070440e004002c00c00040d82200c400303c5446645030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549720287 1250 549719037 549719057
    0x13030809012a09050406032306040b01060c03020a05010515030d05070203030a0806041d0c040b030c30031602010e040903090504110408070306050a1514010503070509040507030c031a01 81
    0x80040c4208a0320b07038051510a0b003490713560002030191021540280e40c2104035004040d4008610302c40c0200d042ca032600184007504080c1d803803005000303051040c0c0301040707129082d01d4109442400100310301c42c1c01c90300a0106060040a0160044404d00c00354801d11415282d501c0090082c8203407800584c00801960030201d5004040e103401d07400a00b11a40941d4800700c220140520313948101e0718041d01c4000303217512038081081c84204e8030202009072080d40018031100380e0740d8501c06400d020290008486050500c0c03402001745c00302a01040d5080c500000c01da115592001591600126000341d030ba480034001c2d138906101c1100c11540307029000403450601406a41480c0d00001e08026031060001e00e81940c802c0180c0c1484200e8200300d03061341d181c00a0001c0303103060340948040300c21b0800c00d01c2002449e08071002c0400c030404144e18184040071001514560285003650007124000d0300c18062464070060050060100c1d584d801c2c04646824003c05800e1040440201c401c1c0341a1600b0b0f1043e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549721537 1250 549720287 549720341
    0xc080705120a06080f01060e13021e011b11150f16140d20010e19031e080a0c03050c0702041104051017010b030f0402060a0c02091303080901 62
    0xd4100106401c01c0b490302d441d40002c0309001007000725070100c030a5000180140c100440d0ba2051a006850b84400c14446014400542d4480f2114100e0f0403204012001ca00303021001a26815413091308035810b1141d241001007444a001304094900100301c9200220010307980010417640988400c0c03a415450612000340c20000f0b101441201c035005030401070a40111001c0240307010107500e4060002207001c100b841022180d102401c0384c098403500203000f800b040e04c909070707625030820002c4030350020b80009100905010300820400d0010624524000e4410741e032000e030034001c00340ca05400b01860f040c00c4480152092042c03c0c0120f1801d0122490031f00d16408110141180600403101400c00b0000014590b841d05680918003a2a071035220000360720000c84200c04005030700c107080a07a0f080040115076a0380c1c1001d41e90103981240c030a0380300c044803202180d500c8403815000350000d52000c00d06c1084600c0e80b20106503603110f5540c2c0074082d0350ba01032003402d80d00c1307070040042c1a9002c48840705070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549722787 1250 549721537 549721567
    0x30c1517070e150408100516020a0210030b031c081e06130e01020d06080708160909060f061404151d040311030d150b090d15021e040602010c080705 65
    0x40b0081c014000803181c804031101c8551503101e82d001c840c5a0b4405070031800c0c0c6c240d141c0120740d8803003038241101a200c401c091003e0344a141040d07009104030011400e440303601b4080e6221451104001c0d048030b4803002680300074030500c100080110300ac24203074000503024200074418440582024580d140b180d0f2a07010500250a05070001c0518864851282c0310042c942440a810025890748020400310325201b2414240440d039040400c035504802520709070003c281100754105e490b540800034201c266820204024910302200048081c1403074000203008440030140f003440e0388101c4007000951642060300c204100c1031710484000468040d4018900900943c0480c0c1c00b90107414140c2d5500c1c1040e2035541141c0c4882c4050b1000c3d65a11500a09000002c3e4541d02801054048074074041c2210006000c00c80b11480081002c0035000300c425401c8040c0c1c055982075090141c030013051800c1d107829108650868002c0d0340056185c0807801080512480e0107034003c200326100c080c50616044081c1300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549724037 1250 549722787 549722807
    0x3060f0402030a0f051006080c030c0f03040206040305030d0618090c051c05070f0312030b060313060b0d0c080607090b030a0b0d0803010902120106030606050d0902030109080301030c151707 83
    0x8610743d070310300031000350f04c050003181c1c40362505881d5281003606054004e40b4004029250456003e024810040c1500c4003900316068101020720207520b032341e900e100107000307031040b5000141140000b042400e40c09416800000c00d4901e03101030007080c2a0740d141d03814100c0e88541c80103402481e81d45001c20050802076103101e00140f0324414000c000070300b078030b50b1403400300d196010070720860713541908005100314410780c070f141000b052405119059030f00700051164080580175102200c0d002c1920810841194400d1604c1c0303201600d000c20442690600b001d0300c06d00d9115210450107514002985d041c0300c3d001c15816920b03a0250203083d074440030708a00040294032002900002800845000301e40c29070b010318000c7c002640c0150351540c03c112030801200069200300185800c19070207000300c2c0e81010030744600b140a5500040c0b00c1031103000180c0940b60100d0054501080000048184010540780700c00b0b1712076401c1070020f081c402e403104440401c02e0b0103c1c0304d0841e80010210700c4281c81482141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549725287 1250 549724037 549724051
    0x31506090a03110414071709070302010f0807020708011b0306050f03030418060b0d1d0c01021906060e04110a08060411060d022107090b09031b01121a01030b0603060f040203 76
    0x6451140c0c1d05560385c11101502c61070003040305c0305070208140c2c48400c48658010200c03800f40071814178560019107216000034a04c0207010f00d070b0000584051080100c103004140300002888107030741c07040004152081d0200b41e4400241440c01c0801d0034103100259414281d409002149031500e854001c404010403040200c47c540e864600000e140c0710014080d00c64044050000505884447e401c91030064110040d0f0009400110561a140c0c0e00450060000c4100018510380140d207882c02400400c0c185e0070600204039042c2c02d001c207100000c032403d15620720a07103040900c40d440703d40a0f0303507900007194020002d110308140c05c0e01d54200600603010b0340310a1f403400350800840048001060b40d009035000c894160320020450100c1d0f0051130440140b09019403903181550600109440e10100c165082d451862444185d07410f034810403043c0c1a21201b02c004208840c003401c0c1240a00d10700000a500007400d1207003040c01443c0101c01c80f80179a03c000c2c0303000d050003540030070700020f500020081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549726537 1250 549725287 549725291
    0x111180a030606062c030a0605100906080610062a0c0503030d0e1612080306010e0607150b04020c0c09092806050a020903030711061e031506090a031104 67
    0x10000e981802041d0240019072501d04e03030041810901e041c3d50100170769141e08500c03200400300280c1c801181824110b03800001c0400c103079a0701b00d40c0030003461003a480385040500d01000040c1042c2d0101e146402008290726401d01a0341e0b600c0200e40f400c0381c1021006d180c803101c041c581c40800e658030341c070300341a4410f261002e003059032840041e0544d084142c917071b11203d0721503041800090b424000ca50462041080307142c2e506082010943c01c4001c03406c1c0c020100c100010200ea190381c010b168611641400078082c42d51049940f500d0515181390f0894586214200f162180700740c90036000340c40030f01d92000300404031908148200400c000024001060b60701824403944480082c400d80721140c50744c070004944280446180200880f41c00070050640544140980c0c0b00d40e41e0080700710761200e904511144004105400001c00300c0c441c40607c4e0f0b001140b034200c461802d413904c00c06103100300d0612400d40d901020701800d005180c0f140131303401ea41c00031070320f802440004e050960440c050ba10207400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549727787 1250 549726537 549726539
    0x2303060a1206110f070309080d0e01120e010501150909060506030f0a060f0603020a11210307171e070c02150c0309100201050910020c03040302090a020c0a060e0f0111180a 75
    0x6402c5075541300403280c802440000842100303042d00030b01d8030703002452036500500e10440b03d40d40041002d100e000c4064104581004840c040b22000c0d080007052041280013007016581d9410303e102d0304c41030740220340e0105030302403000a0b200401c0d2059004403080038045a20b10b0307881d0b00c40c89044100003401c1e400865036400c030204a4103205c0c801c000c0a0b01c0a130720700507643c051300c840c090314030301d41e6a0f120003480c0c0c00350382442113292059502e030b44240c0001e41031540720b40f0b4004c4180ca1081c414200c02ca00101d2510810040400230304a0040707200d0031070b1001c840340d1182c24007103507601154840a500401a0451207446803500c200401b99242400203507414100403e0003d2000c00a080034000189c0d11401400324400084c40b00c1c114615111008500d880030001015850b030145200c080d10540d01e9000180c1d40402030b4044844103004501a911290490300c0d0100040440d0b00c44044680300f400603085181505100349068ac00108a100d41810700154801d40b08402030720b107035a00141e40b098 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549729037 1250 549727787 549727811
    0x110d050f030a090b0c0319050408030a080f1302030a032a0b09060c070c03022b0629090a05130c090506040b010311030411040209030d2303060a1206 65
    0x161062011400015540d100c680c014024045415504444c80c1820104210b03d9400070010449185c0340c410103450401402903542610b1034012a40001031901001510300c0c0441d5024900030302c64031090410030819110203a01603103008a040000f5010790101482c070001c640039502d140041e6001e080800ca9190fa01c00c445010042c2d81d1030112030290780740040c0400c3c4d1a092220f1a4882010164030b400d003225521510300f001c40030f10000c0c1c040e9940c820b03903a45150f0303505142d00b0400c1a1b0070100d41c03500340c00e1815400420307064031528940d54800442e5a0140104c4001e4070a0940c010100204c540b90321480100034171010703084203640da04900900d00000c0060f90200c00800c50880300145916100d0140b20a86085000890405180144400c1981e607800d0a494025070018290781d003035003034403001c500248107400f42180e052040002220b0695400310990b0121454a0042210401c11015910540c042652080d51010070280e0501c0459a13503d5170b005000d01a0724042030703482c1904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549730287 1250 549729037 549729043
    0x206040311120a1d011106130611040b0904060b03010b180409020405040804060305010f03031706031615020c04020c03120c0906070b151e040e03040515040509010f050904110d05 78
    0x41005400f00d80c004c04940c48689600a542910990a0a000c6082c10f04070030038940368180200b441c01031090311038030501404599032148031402e80f002400756589403035801c000720035080303a01018072443c00d080300462848141c40659040700c0a50592500b009060b12270b05e12481c1c0814078840d08240d84611181c0560b07514000e00c0e002e60300600c4291365030350134504c0c01015120144c06c900c19a2443c6282000000d84c003a4800c049140da051141206480d02c50000b4200886a4500c103968005140041406180441000122529902141d1150191405010581c0907044040c0640d40003880442600b034405000d4962200d56510301620781102180000d9154001c5c00b01607580200c05001c00200e401c1d00c000d0302c11281b0b01100d8030303034442d580d05642c20b001145103401180141d449646001143d0f00410656018120042c80250441e0602c0100b00d0380303400c10700c00d55114249800000681c1460194490159100601510f0f030940c1d403602c0c1d02d84400d600c0002903800189806117640455014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549731537 1250 549730287 549730297
    0x30126010609060512030f0a050c010e0f0d021905120a12020316031413112403150d0506130c030203060a140601030b01020c090901060b0a030902130c020604031112 72
    0x1401d0000f0750310309040c00e1220704e08010100c950280d0041002c0c402c01000c1405070b500010061801c141e8500c007a03403030399026100c40000c003100c2c3d10400c01018a0305a01055440002c240c82d1b00720f0f034402804000d4440b4041340c1c14800b401a802400e9080206101403000302134001160503c9804100e00b415203208036030080f40c00d01d003102c4204411400140e851300918882d180715460b0325200f41004141600e20002c001e034014102034a02800d03850320740b00e502002d545030641e20308040c0504400c050f020142ea01c11218641044070044600d0490b01e050007025103000c5d00403001b4140e594907080094050032a0100585040207440c100100680c1c0c1000254030038144242c001c1090040000017074880c10001e00f0160601d410b008030942c1a9a00080c03a0f00b9841c011295418a61140c04d030b07060050a03160041c0d5907042c000035035009c03040e415400156101d44251442600c1d0070b172515035a03045440b100300b14401600080e0205012074811042c0c0304005010405442da29041074103018442e602c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549732787 1250 549731537 549731549
    0x909140303040f060605010806010e0d15020c1e0a080715110412060c0e0f0411280e04060b0a03050402040608010f0b01180b0f0f12070c05061b0301260106 68
    0x5005141c3e010000540207207402840b085c24454298180100041c0c0b40c6400306010364014142c0348000c10038446210700f0742c502c480301190115900c3c2c441880c019114500003100042d038503041d441080801200198513448660000c1955003843c50701e50780c28604c2044240c0400c1e007540c0700c00c11b050780f0000c10001000205101c142c3c1c2c182d00101450540140d400c880c407060240a03590b640681542c4541086040088040b43c0028807490b01c448030420314052a2844103000711414061034208000c40e208900d03002550300c64440e8203030f5103400c00007074845501030394036186d0b42408550007013400390f00000e410900c0100040790040c3c07603c0b1411b0846000c07200d680c4007951560b040810a50b00507141c00350f0710201050540f00e49080c041c49101612131030502d04030340e2800180722040c2080300c6040c0e17200307051056145c0c8114100f914008101000e1014240c400d40a140041218a0664000c201c00318401e40d05c601d041d0317880d00b00c540c0c2c240b2401c100884c41424000840c101d00020030301c16040503240b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549734037 1250 549732787 549732803
    0x30b040b091c080910110901030c200102340b071101090804090c052106010519030c141905091503010e090106170303011211030d0c060e0c0109090914030304 69
    0x240c8044c0540c40c0414050918641a00c2c00d078070311186016140417a0000034003030070701048452103100100d0350403e011800e200724200c10042030105c4441034000704407801c1e2080d002e41804450341910110070341e0b05400c3c4082d280e00343c0c14040018200050007588041a418140a410ba40351700d0f290a460b2040e404031540000010b080c4025481031103000c8d846c03946072511a061201202c1c4940381c999019880007030a0001c07000180e280e81c41402110301020a1200307042d540a038400c0060040d001241100300401d0001032280b01020109065600018510b80b8001414030384010036184c035400102c140390050400c40c14020401c0c9100000c60082c208ca1812540c149800010309084940c1908913603c3e11800d900c020300014000030603a815126500203850710500141340c983d54940c1080e24180e003600410380a840902d401410348900341b4000d000a1100e02a0381d072855842d010018507a90118580200500c182c01155200e1489540b140803055050809006102e155410031034044031090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549735287 1250 549734037 549734041
    0xa081b0403062013030c0b090a1809021c05010c260a330510020607051c060e06040f060f0e091e0609120a080103060e0a0605070903110a030b040b091c08 67
    0x6c4005401401000d581090a0a01010720009482c01d00d10303206d160031010900d54030203200c1c9003540c00000d46035030041040c007a480200f100d43e2090140c001c4280d40b194a00702c056220329009100c2040485c080142006d590054908044401071004c0d0290802555a48025006504108a40c42c540ca0112612020a4101c648544544019410003400b8100d210030881d8450740000340c0a40204440c14003a440d11603440d602c0054408000064810900701071000500a041c02c024a000c0c140650b0144003404c00b00d08003800343e459500c07641440b160f1041c01005000038180c0001d40200b409000d48000032140568101280903220049416030016000c5c4580741508002100154990580c46410310050f038030054145d2300d0504c40a40b000341c0b47c081440c50f04000380180515244d0200d010445402c10a0004014081a0008960f02c151409501280d46040182c100803a0381c802402640c940d903a640d540114036010f0106442c510130400311004402c01c07811000d2400501d581d9108140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549736537 1250 549735287 549735293
    0x90b15120a080405100e0a0f0501020c04060509130204020d06080d0f09050d12020a0c240302090a0306111605033609070e040905030a081b040306201303 67
    0x1414a030032031818640d0000c40260000b85200e825101160300840d4079000c0420258000e950072800c0296243d40700309070550103c3c007400002060b01c03d60700c0a900300c8450404650500c021a1428000d041c0d00c603405200013500d400a00c1243c5c4201c40c40600054107264130940030038181c9009411040c41a0040c070140301002d90b0103414118904420303e8292500b505e00f0300410790701100070b500589951400c1120a003058001c100c1507000c0d592110000314515034521444601c6400d00400391030105100c2c50344114144280240c4514000081c06101e40034034503561240100000b08507840c0e522801e1100a0602690290b0201564052406550f031440c00c00400b40c5005180142c084055042032200c641c54401044400400081583c1c0f81c505900c070340e0020b0b102c2410840455601a0400180c0c00420102001a002402e49500c03480c05584684295880346514074905114403281440308001003141c60708040d080e003458080c804420070444082d4900d60b801076038841c603c100703040c00400030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549737787 1250 549736537 549736549
    0x1f0902010e060f0d0f1d0606010905010234080a030306261506010201180807050714010f030c0905060a05130801051b2a1c030209061606090b15 63
    0x3490204590321403a00030302680007505401041d6003c1812940c03004c00c520031168650003483c200c1b44466003a0340d8084400401665a20121071282c0003e130034446c0018a940000cc0700b403100c041209981103e011480d00441081d40002c8451442c464110710005000d03205028003c400c80c000e68012442d0390428086500000400d0100240f405900301c0e4508e0b1a007011410420b9006d181544501580354000100e001d40724490800b14242c200411500c1041401130003401494400c40603142044d5585900101008041d04602c1c0490700c00140707441080d210358060145c0c110b050a2100365a0380f613034041000c5801caa00214042107002811400358400c02c0c41d94401400000c0082c81186000da5034068401e50f03405c41c1c405800000700d800061800c1c00b200340c0003400c0c060f410f040d9181c4c003410300c03c0c0e503603001a03800312500310400540800322602c0b90085840e21680034208500d4904c0b641c03210441700b01e1100c401e60b801591000e8442c0041c0550302180d010310614000c2e01d140019031410400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549739037 1250 549737787 549737807
    0x2310151d010905060d180b010609031e050c090a02040b040e040614010522020904090506060111070302010e0105070305120103061a0d0b04060b0d060e0102071103030c070311031f090201 81
    0x206104440c2e90800c02039440c2002c4884650a00340c02140c00600740050074680d488802d0014010b04d0240c00124082e6800b44480044034044d40502290050088090000003048000503019400000b80072210f8100058a140c01c41440d620052400755103400781d600b103070826001154a0902c45081c0018003c0c14080c9400402400082c884c0c02e503d04800245044002040c075140720104402c2c170101e4600e60790580305c01003405442489503407928070b000e039210304013154043e004c2030880c03401d5400d9200025015003541c2e07060b110f01540044960041d501c1d81c2024104500b080b40800801c00640124850036000f50311070b0001203410755400710066104052040c426015040041c00500401d040091580e0041e0700301800064400e4041c012540030160a4000742c41d013401c110520148160550050030b460b40100016038044222a00b0103880344200c201c50f10055111090034008601003040e80b05c0c04600003001c980248c098041c465010308a1070301c1c001d0241c1d0313996601106658102c0141d117 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549740287 1250 549739037 549739039
    0x5070305160519090b0d02090f1b0f03060904080714160623090f030a08070c0b030f04030f0e0a0f03060b03060705040612060b18010e03012310151d 65
    0x2c1541040788040f00c00c0e14085124650901e512800340004644900103116120340c0c029010990500d000203040c1d0303002c0c0c800d481c0f03000307403403240100454000144029104078150710504941b458468204010303201d0380240040d0b544000412903400000c0e6880d0b5141c3d0041c0200015041c1d804140440115034980303540002d080c810011051180701d0b105e400b070b414030740d181ca061041e00c0b1040f120102c0c4043c52803548103600b41c403860344c0130004d004500c07014092040c418410b002503e504e070b0030711814500040d280d0311000d0800381c01240000f405024615554541c0c0d16010246000700800682c11070f08070307070003051614031002081c000d00103640180340200380301340c0c020201410000d0004090344541e1180c2e40801214003c0c19815031801d4015200600c0c50642550725507031440c042903101a82c4440e0a4045000d000c40079005040600491504404481c015100609003040c451a402802803804210082d1450701007207003404100d1080c0707000c800e41c3c0c8200fa01440442c2c10b84840c002e0f05001c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549741537 1250 549740287 549740299
    0x10e01020102040f030b09030705121e180d060b1e0108010f2d1a091201270201030e03130305061e0403030c0c02040c02101103010e01060516050703051605 68
    0x40c01074801d92000304c012070781d01144c103404594070000b0090441c041c044005106004003e0304048601203040600001c0d4082d1039450b00305032a10120b29514464261440103800e20b40ca42c480080c035101203103d20300c5e0b007c0c0101181c84881400007650506450702078003203580e4a6001d03003101e560f0220134580501844001101743ca410328818041110700d0100018803034880840c40d5643d8079803030a100c801882280c032542c10030103000603803202079000801054000c2c041d10745007161000050080c00419906940400c0080c80340c031518080e01151141e06a0605481e031000c00703400e15080000308074405420504880c11030031880c11900b000006000d1250402126824425100e01070142d182c0107070303250800084000e52040261445485070001035801803a06809100381900403e40d83e1540003002000c0081c8141000f42c030010b804207014803ca0092014014051140154001c00c2111182410540020031030341d00d4602c4c010803500111402c4c0c2102d24070380040014401480080c2404a410f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549742787 1250 549741537 549741539
    0x503010f0503150112030207030f050705100305070f0302090f0303040e090c060717030a1103130501051303051822090606061b20040905070e060a24050f0406020c010e0102010204 78
    0x1030100c0c1045c0242d10b0490740e0700008504043c000c020007001190310101c101e01c40b00380d60501d507803500d2003841118080c5004d5850464414841c1c45054030409454491030209140604100d0083d0481c06e44075420890025201030035582c204054001040711034040c81d21803903c0c41c5624280041819100d004602c144903250004902550034544810b2456550380c4940d94245c04130058000c5004a000400f0000180301030245801c45085e0480c1c004d000901c03e644412904402d03119003504094000b987c1803015800514040c040000c0d86440200345048c060480d144150074420b001d5000c0a540c1d43e46e508100c100318840c006c20008041c0303070905030944890788503200341001840e01c004255400310204014954407504c4654151b07030014004004136266850180c1c2d40d07100ca801050080407407000002c4061900400c200b05464048800415510700c4109a00c0b20101d442c0840060240034003403061645810b0001c0c00c0240341c00d600070b0100903400800500025882100302d411a401040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549744037 1250 549742787 549742813
    0xe0d030501060c1b03020a03060b09060a0515070c0906080a03020f030301051c0501271106030610080a11121e011a070201021c031b02010507020d080618070503010f0503 74
    0x2581c10290300180d01500c1304000c810140c00300c0190b40c00095100311208404414058541c0c4413010100080e03036444c42c551100c60400c00b110301036204071544440b100c0d10a200440700403000e49040c030311884c1620b007410744074007040c02034031980e400c0a05680d000c418641d0500d41e04008154684440c8006149554181800310318415117910b460486031010189400c1088001d5005050040b1405c000140c5003079003884010384410300c410144d55150748416044018035107101100c1c003030703040204900c00700c0c0c032080d100341c4958400a1141d03038580e03680c035a1306584030040760091121200510704102140f508000300308040018401074a03011200c0310061184190748006c0351f64480036400010746800b031a100413840c1032a000c0e0702111441c1d01140e02e05c1c03070340d07055000002c0380180c03c0120307070094444e000205d080b12812034070580164460361000d00c90ba030113a04415040140a44041c0401c0300d248014a400d11047d0782101c006640007004101c010940c80d02200a020200c000e4050000d00d01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549745287 1250 549744037 549744047
    0xe07021501060c0809130903091d0c0d05090703150618020712140904020f09030705030a0c03060c14070506070807090522020c0609100f0b010f08040212100e0d03050106 74
    0x10001d010010010f03641d15185d9031080c150006c007200040610042c89549030041510140384204244900400030340d114400800e40000d10980300255800c0c10001c0b280464005081c005e408a8800e002c0c443d00803000c141900750100e4185250200422b00d40e14081c0301c0d4a4000003580400c500b03070700c113010042c005642a02048a001d195107041000c050007d07220b484a441050700160f4031900c0043e0301c840400104e40507040d4180100d041d100c82a54980c20700d6105c5078035620040a00d42e03152402d00010b24145e04c03814000000b442c01245000410030380c02c0041e8807046040c1c0c2d181d40400d003000581c541c03117413079650f208040c2c1c40c0c9000c1c501c1c503000114080d050101e843e801141070481100f21035403c0c40d4151403401e081002164040c0c1000c0b500c1944032540424403440d014101141c02c00002424018443c07090011794812010b1401d680c2d040380e0041d00a001240d01c50801402c0c02c40408003004000c00761021290002880303854121154980100818904280750500004104054200c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549746537 1250 549745287 549745307
    0x1b0e01020d03050a020903240604051b03090703121715030d110307081603090605031303050304030c02030607112533050d0e060405061602030c070e0702150106 70
    0x82e09000c40c0315114030f06200042d00881046a405100e0000c0c41c0c150601601350f14181e40b141280045100d80704c840038442a10400c03502e0039440b40000c6591110b104848005552020021054405243c2c03203580b15207944841100c808000f8044052218000300560207180d042092185a4690001381d20f0101e5190003003042c001c01800300e08000c1d00e14060b001e100701d03061507074000295075441038451180d16a41c105100c0c15000104103100101c2c90724086d0b0220b90007074620341c0840c082000c041e0ba04503215440101b0031806c000703448140c0f02c01601c081000f64000c0c481a00d80c0c070101c0d0001c40b03515113412980e8641603052175011400c84030f130f26141040700c0305071030078900c41c050014841c000800131400c0f00469070412200030b10107444071a40c031602030404280c040700d061083d6401040c40669594040d00c015203030740c020300d020498071042203003034212002440c0152805c0446d040d090609015582c4d20140804101004000549505100c0300c010511450384888140d410702c54010300c65920 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549747787 1250 549746537 549746563
    0x80706020c160305340902120f0408160218010806160c110d080f0301090b01091d0106180801051303020c090f130822090f090f020d0c03050601091b0e0102 68
    0x1800800c01c1040740c000a1040c9441046032180801d591b030f00040c5c0300962018a036644640018008604007208010506d0f024640001d5203504281c3c5040c0c03108040302c120700c0100c0e44002c10300710b444450380c003101c2c0f010b008001600180046241c411a01100b10752220b0040007009a15155440010947c1800c01c908500c2a561004684042e1410080710b100e56441c0800441c800300000032a001140c202e01c00e83d180071303600c0784111551030481d454400c81148503586290152030040c000c503841345c2d00307c4450382c1301032501c10040c5550f00303100e030f003161026a5017258607101003d0000c1416010425803103094010f40744e021061a1042d121741070060041c2501c1400641c552020007400204416100d892011480c08030160036990000404820584a010442ca0811031043c2c0855084d100d0b035030041da00008101d03060082070303007005445c2e83d0000d001c40d0080f11310180130000c00c100f04400b41c00f0b002433840001d9001c4041900c07000d40c00c00d40d001002007141e180d013070320905e90740070074510041c1c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549749037 1250 549747787 549747823
    0x4120905101d0609030a0c030501060f0302131e06030b0109050112050604060b130525030203071706041401030f0b06040c0905040b011e05120915010303050c0a080706020c160305 78
    0x12000340082e07040d04c90300f0583e6500d442042c0790342d070900040006d54003c5901ca00300801650b0303a1175001c0d21011000d440069031007800009000201c0595800c400c400c0b10f0076414842810020304805812070382103810503146514a00d0041c010403126104450141c4004841c5200603d1280c0d01d60380d0720000140010902e039101c01c3c3c0b006160325003400f01a150741000d00d0030701051400c123a041100007034110b02501c141c03103201c0d8409800d900034402c6034050900d03641c448030344c0d101520541d8810400a80b02c16002603650410107038103141506801d0186103d24036842040d0100c0c01c3c070f140c80e030b400a4000340c0b0803841e0500c1e01c14215081040316048440031b0301d001c6004104a4010388600d101c1c5101c0c2e00c403154100f03604040b281e501c100180503c16404280d402c454659072421980c950360030840c0d100080d424401480800e00410141c242913000908880b800030403a40e4540e6250800d102c04c07140250040303584a076900d82070107251904150481840c2a45165848440e0303105a52510350003d50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549750287 1250 549749037 549749087
    0xb0a031e0c180c030b09090316080408010f020a0f14030402040b1206040501060816050901060e03120a0e040e0309030c060906040f030b100e04110411120412090510 72
    0x4041e0035030305002000b00400c804035403441040c03601d01610595150034002483c00c00c031083c0d285080e841c1903000e000c3c0ca0000b1030070490650f07084085110240c8059a0490741800005901d80c401d010304c10f498500c840e0b0150319190380000240804203c0c2d68074000780907101003065214043c2d070090f02c2e8069011500400c00b80ca240b40469803400c0b88805008203030113a41c4c01c000c24020f05411410840d00f078401114080898440e013407100c4034250090a60083c801d00c0100305152141c0e1180e148550020709032459516035804015082c1d012900ca9000300300117245048051074203203c3c41c3c0403054420041d51401c940b4200080d11041009a561321500c00410403160980700c500a0741e014240c0030704164050b50700c908260503001c0c0c2c2150848040c56034014082041c002541000380110b52192288100716071840400010308107030925001407403014469240b4881070204454081e500407840d0012020b004079009140d20a9900058000c0503200e07004135100d81e2000f50702681140c060780140f00c0f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549751537 1250 549750287 549750293
    0xc081507081306022b020403020a030f05030f0a081b0708030601120609060e0f0108150c1c2a02010515010c0c09020f040e010909030c020915030303090d030b0a031e 72
    0xc10310303040003403c0c00c4c0c0b01140c9854409410001c1c00300e44d584094220055034203440184069100350700009400c00000201000000c00c101c900800c0f4a215001352403c0c184130100046a98000041ca4070015a00c80c05008601c54000205030011001d41d0134540380501d241c640714840e100151155040003103512161003558075540c42070b03000c0c03c0c10580034007420750380390070b641624501920b07401034100d101c50000411110000d031081701d4110f40b500140700c40d961004844d1807500f000700303504603022000740d030508000034a1162101c141128070800346841d0321210040b688414000c2e00c030055a14200c00d0044614460381e10081500c1c0c24038007480c982c07469207000e440f5800340350302c01d00045002103040f0800303000c4000604203460201c54901196030381c42c1d4190040e65120503011700401c2d0300c1d200f40c0f8054280000400d6101100240c04070510030481c001c00d2035580211484100c81d0840214160303003c0d81800781e489003400480f00103900c107045881e01c036142d107500001c9189080d98004c42d4020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549752787 1250 549751537 549751561
    0x50c1803070b03070e03060105030a110105070303140a050f090105040b010b0d060906080102220b09121c050a030f140a052203090614120c030a090501050907030c08150708 75
    0xc2c10901c2c4046441c0c0c1044640500080103000019220b4004c00001113040d060024543c0c03006038015400400c08800040192100d61240710180c0416440d60394105150008004403401030b003040c0c1c80000c0c54034014080c403a003144040c00399846a41840184408102c1c18001141910209010140d88100408149000300244c0e40200001410002d000404c941c0c19805443c580d0718142c40c1110040000d1800080404980541c480c204014056241681050038980740351024500c200e0360015410680041e03a03a01030103079032000941c00100440043d525020310070080104401c10301c0307441c820341c442010100000b850400055903c000095400c4210030715081c3c01402c0340802d00300f201e076605004005c043d203405110042008002000c0f08040f07210b00b180c95030032582c900903c82d0b40790104980301550001c0d068003c00ca4071401d83c0350201c0d200b1300c40c0a0284400c0f800902455195240051703980005500400140c4c2103860040c8010707802d040a103a01800a10744103401da50341c01c0b8a11a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549754037 1250 549752787 549752789
    0x1b020916020307050708060106110303250309050f01150902040311040c02150403110d0905061602030102040b04170706110607030c14030a090c0b130b0c0c0d081804050c180307 77
    0x40c41981720006000e00f003c140c00c0d05a46107640c4c0e0000c840301d038410f150f5a9210580701c18840900540460162410595018080c6900d40c52f000c617010025844031450541c0030501c15a50307940d0349001c0500d05500705002c00c01081c54a6041d0b04041c91611620352855100c0b0410f40a80c0c2c94414104905101780300f001000d51340c852031300f070107400c0600b0000e0500c1c0d01c4c2c4c0303010549441150001510079000d201c1c010700f12400181428074042d1200c4540d00d402c6030400d03040b601341d074085c0004030391036981d40c0142003d00340904009000245070395031280345c1f000a500c05010321406035407102401f000030409a521011030b04001c03494690500c8219981600c2a541003040c44001c800e121642d01c1c06e822140030240105001000b080c0c80b102c0d05c28051003210321038075212070385140c02c110340700c41d8002400040c4610000c0d113a0340b4244001081d840d1910f60801c40720240c0014000033403890310310f500403d51105a0b8104081d10d4550003d0382c0740d11503003511443e07241d045100d1808554041201034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549755287 1250 549754037 549754043
    0x6090a0b0612130c0806012c010b0c0a0501020433020c06070c12060b0909012c0c040603140d020105060d230109030801150509150c030f191b020916020307 68
    0x4244544c1d402038103882d61028014070722a8080044080d050001400004523050003d03642c00301180d107030130300c076a1455011429020080c083c8000520100d9420710151000309600d0b1598107035440d0010300c42c0001860910650340304102105011500b550010302c481b2010020b64400340e8400090412070803024040d404015403203600f01c108400c000194006008800c1d003640c1c01c000645035071000b5401da80c038581c15900e0760f400c0f54032509040b214840f0070303840807030a10781a10903400b50721002c213050303d0564109442600c44a00d400051600c100700c400002e00c414230003000103003002800921001a012000745c01c10100307208601c2c0c5900c4000c0c00862004104000300404da0280c900600b0b054001d1081e082a0840301065502881c091421200342083c02005a070900003540d8a541280e04122680a010303c8203001c5030980301042401041489141f288110f821a00301400400404007041104101d580c010307088401a12008000e0390000040070015100483c031035001c80c6540100c100103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549756537 1250 549755287 549755303
    0xf110601031a091b040c0905030106080606010207061107060c024209150703031b0810210b09030d1a0f0d031b0f080d020306090a0b061213 61
    0x104100002e02d1a050914000341a050150b07603000d906a2940d009280302c8455408501c00203210349060f5100e14072007505400e042c40b401d41c844011a08417141c2c0c1c2c01013a2160b2054003448592768040026900510142c03604001307039040040c0a64503224584640c03802e00480c86100001c554540103c01410b25000b0840d9040e0001848a42d160031030f13040001540344800080683c1c05650b900c111a088000a8082c1e00d0302d02d09100300410b564002c800c16000c05544400c041040c405024001c01c1544042d41c1b40780940c02c24080038401141c86a204c91050b401c00f00015860b00040d401a02c480c1d0740040031f0010644d94161024158401e40c8280d2515520380b11034070500040921588900520503100c0c1c61a8175180d80c24481d05010307002015010a42c2030704481e07014600175160800c1c0c1880340c041c0510041065580d01260b42040c045080400d40100400205041c075540d145e601482c5d030b51003441400090070102c0d140340700c0c1c106071aa040c1c04402c0003410340704070640c85891641d070242d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549757787 1250 549756537 549756539
    0xa0c03020f03242d04260a050319020418050708040b010b0d0b060a02030a0908010501060e091e0f072721080705070509010e0903040b0a0e12010b0307051f0f110601 72
    0x101d204660380c1214200c41c4040030509440400041b01c140c0b0006500801d1400c0c50541c4801c0c058440d03400040840c00e50301071803030841820510a0029100401e2030709140f810040c42500e192060b86d1004080f1020803811404200105048600d10b5045803980c4158540e9654a182200060644195442e80001c0005111208035500000420050ba425918400d8482d140d400328ad00f44c0c0d00a206540001e00c03c000c8404032403400c0700c0312680091140b40e0001e4981414514046000801c81e40c4c082d0311640f01e810040c9060300034819200c50f1300641104070a82180448010b68110280600e80f091101c6e43c41a01c07401c415200300c084106d810000313039900c86c1748a207080c0755a03c0817805170901a5108074000034826116040b410300501d040b0001e58146400e01308880300c590000282d943c02c012499031440000c0d12102e0300b496400e142e000000c030325649980b0034540b5048155000b14015030005c1d84d25020200c1182c1054403120ba2850f00310555039201204403815460410310115500030400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549759037 1250 549757787 549757861
    0x4050c0414010501030f060b0d02130915030c060c032a0507080604121b030509130516110f1b0d1415010f06120f06080a0c03020f0324 59
    0x11001d040b0f0700240e80a0245a562003101001c0c0c4106128924101400380810002e002d45a009010507281d0b003c0c4001205955000030401e80d60041e40c4414550340801c024014480003414810292500e801c094400280c16680242a444c10301c50f01202d407041600700b0060003070b514806180558000381110012512000000d80b00c0320195070440e046007610000702409409501000d41011442c80b411024010f561402d4410307501220080d540508100c4800302d4400d0300c1d119160251401b803000004041c0d2048014001c1c40c428a00000c2c2c5030302601c0720358601c1c1c2d00001c501c2d07808003c880c1c91407108581c10001c0741c44001c06240c01481c0c50040901e12000f00340000e003003110b1552030800349602c0c0c3d0b40d54180c4001801240100d00c00140e1100e24101e404900f030300140b0b10011804800241984d884145c03a081a031a07440480f050342c0250b0b1704201703518001039101100c40f000c03005031050b18a0f035401003907202c0320f5450115a20040394001010010b01c01d0b800c6d56180041040f190582040b48 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549760287 1250 549759037 549759071
    0x10200c010e060601181a0909010902070302010c0504050f0d150e1501051f1112040f06020622020904050a0516060809010c02192f090f0402030a080304050c04 69
    0x411940701c248108000184a03611035925400800391480f824130080d41050030f0708008120040041040d9041000100466158012602c0c002c5c0b00308600161980744624000b07094400c403540440402c80240024030965031003442d022440c0f00308a0f00c0d6580c2000e1072918000000041c0c484400881c600351900130180c0012403100c0701e0800100404a0580c0c071002040207211010403618100400b40c086d503500341e40654699008050711100b02d94254001c00100080c0e94025000340c004076107150001c0100580411000e44c016a07000000c920710240c034a10302c00c0d184d0000602034480d01442d40841c0612100b030103105103285d001820341d40704424943c0400500c211601c210300020388041d00250402d4810302c240540c1c40100e50251600503a2891584049001c59409488241010085001450401c0e00845c10740c4018801d00d41505422020816040001400c4440c1040c00e0b00c200320040e500031407400d07034240d40488102d0300c80d181c904015203000085044150081e03e06440000d00351412 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549761537 1250 549760287 549760301
    0x60f010f06030c080a0c030902030a0c060905040b15130308070b04021503101403100f06090608030a020c040f0609020304050c0f030312011202010309082b0c0210200c01 74
    0x900d44050005540d031a00300c00b2103601003580b000050100000c81c004008940040c400074249190106800440b034000908102021800303d506442d00d180410036150000b0703035417006240032a0308205200c2e201d00407814409080500503010303640041c04101c1c003120990002c01560b04894429111003461502081c411070645040e881003440303001101c00c0c01052011281b01340350710441034101c0c0e860014880600044520030b66454020399092900b46544c9100701d000303012110b0404a80d00385008001c41c12100c15410000e136035002080154a100d40010302205e402c0b50581e40062a12007030103101c4002c101641100500c070f8000404e0206004000445080c8040c040780c884401d803076040c0c20165684100780c503c0382ca01c40004010000c131840f00380681c044034010305022a44010301e946001c002d41c08410f050151740202d07502d0400b003060929043c5800183d0100400c00c1d1a403e15001c1d41c1da124418601800e2a1160405041e00641202c4940482000548240c4134a56401803901034460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549762787 1250 549761537 549761549
    0x33007020f0c060304030e1210020a0507110f0d080a090b19020c091603090f050304120b060a14090712020a0e13050f19090f0807020108070801050109140a08060f01 72
    0x6841d002c00607440d100040303078001c641c951680361803003000c0d0b41032206405100d20000301d18024810451516406400180100020b80e078403582e0313400242c0780c4007072a01102e030303042402025480c40303040c4a45c03684081000c249420230080f680b1440f58007800c031144071181d00030100010010a62801601423100300507107041d619001c2c0d0b41c010401c4424014800000c03030300c00b164280b0040e86d0260540c040d600c6948228000c1c16100c0c000515034440714503590151f4081212240201a05000c0c800001e0a5a0f0801e008135604e21100d0b24101d00200f00d90f1050382d14038460020180403640c0e00b4000c08401c03640200200040d900d030395a20758060594034021104074055403180f030349140100301d188182849100c10045100301c644591018451864a14104506541d5a0012800031500e80e070030003034002e03200d6120b1b140d40307003130600c00141140c001a181d50244168400103208130303a0040042c00c151441002103441d00780b107080005210904a81c40074203140a1601846101078600070b00364140c0d44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549764037 1250 549762787 549762793
    0x18012a0305070e220612050c03060c1926040323070503160215070c0302040b0105070b0609280c030b0a0b090d060204180c0305010512033007020f 64
    0x640c11206030f510f00d84030181c407540081088002c0508a80407103009080020070640080c040d9180e0754880c03c280441b0700107403030642c4000f8181060749410450a5404050044c80a0408200071504040502c02125001c14410682480080b940190740c4001e00c0740d54001d2141c40c94101800c01030501018a42240520084210072561070f42e00d40c400c413003d40364014010361811620315031400303030f40100d40d50485c0d01c40d1010034101e4a8581c5e01700900311072400703a242c0e41c01c42d0f85548104011911340e0380185051200911045000c00c0000d00265480881501c2c1010700e40e070303140344914140c100c20f40740403c00d0700c0f04100b0080c1140c455000e0301e40e000e40c5803800c10009102408028861240740304800d5101401c00c40c421403828500d5801420602c540303005414036845529010b0000003501d00d00052a69490511410a6060090b103005080c241c580b0b80000200c0c21000d910f84c80384a0100c50f40c8010083c058070504400d0710480c180607901d01503a0380900f04413400035160005040340c1c211500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549765287 1250 549764037 549764041
    0xb03100506010207151e1e0f0e010c12030911030f06041e08030a020918040b1b03090a060b0d0b010608090f011401122613080307080318012a0305 64
    0x12800c0b90341d8480c2c607000e03440c1c080049040520030407805080c0340c2d204040100c8094541001c40c480041074015413030036208c4500520750104024200d035072302408a0304210580408002041410102801c86030480c0740101d104074082c20301c000700c84442c0b0107182d0507118a4688980c450340100307060313025074824050004520214903600c0c000e0119035102030700309030003000410144900c6031300604554030061300d121925204e490107042404c4003110192003601038502041203c00c2110481d09040c0c1b031034281c203811400c00750354050359092419002031030a95505452611540c0314583c440c8280d90000d102d085d29a1134071230081035101c040c0c40442841c442c40b4035102036020107005d9150307800d1100203c803045a05e40f5040c140400030260003030b110300c2d484407014a003500025652046c0c0b2802c2e040e0b1150350f66540c41c072003c0c540c01d4070352000720960020721142d000510740030b08890f04050b191201011703c00c00110f015004207254903162801070384035007044003001000411500c880006840420040e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549766537 1250 549765287 549765299
    0xc0c03100203151012050a0f0c110c0f0a09050103261206060901030f050a02190e03030a2f06060a12030e04020c100e0304090509070e190b03100506010207 68
    0x281c0010f071100c00504070002081d95290410410802c0480c06614201041d2099005458121101502c00325105a00d40328050b511003100e0040054007401450207640241075134500035103135a000302c44c45d4820180086040e0550750b901132a0009416500020001541c0d245440c516409800c0091200c6d414002001001094060242d40001036814a03150190f500d11040188940c0301040050506540c0c0408140e40711103803080e148a030541100c0140e84d03c1c00d62040d8201804003500d10000c200c0700822031415070f113010040c0e440b00d6000e403c1581d1541071000701c0c07000300507080103018034201c0d01e406882c21130304000400700e0207000d003030320710130349840e1903004c0604e1064149801030081100d00026110900707061f0b001380b54400c0310303c00b590820300c02c1ea2840c0041c0d070039507060310718a540701013400e21102c5020710400d84c1010074030004010706031030010f40c25143c0400078040f90840540598400c081d504036088005a40001010f9885070400d00300440018141511890300600c5400b03004102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549767787 1250 549766537 549766541
    0x9130507080606070c05010318080d0e0633030c060c07090b04020c1908090d0c030203100b030d05130510080928110324010e0a02071707030903080c0c0310 68
    0x130369900243c10001c03842c01c120042d00036200078510358003186114840c030804510032074003401d5808500c600110f20062242c29003031501c0d20182c000d0082c1e0685d03400d4035803000c0c1c40d08041100124480c608440c0c100b10301c40060308009164803510380009000400c600050070205e0050140c1707140034800c04c0094810300c00c0c0b000324040c000d2050860f038040c0c01150942ca4008081e608070340e02c03401d01e25203080040c00105040d40b550f280111654201501c040c0214038040c841300c070f90201a04010450040c0d0302c40080d03910450301c4d8040b81032200001d6101454025a9111800b0b07000c003a00c0302d80080a01840240b611408070303005401ca0040320700700c401003e40c0d8180b611032005884440705401d125911030540369002041865890310410a001c5160507901d80e0059130a1050b04075203090358540308441e13007076200040c0200d4240d441003040000148a0803e0301c0b151894800c00e168840d50180ba042c3c0e079101c5260405840a05c000c00e411481c11000160780031070040581c1540d9000d040b2143c1501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549769037 1250 549767787 549767797
    0x602030702100c0f0c15080a0c0819060e01140319020a05041a10022416110309090c0a140708090607030c1707031403060d03030e0309130507080606 65
    0x140c489990002292001e215050b1220042d0241c58040b41d01440c507078483c80800c1c850f0344881c44c806c8120083d2180c07103400542c4194001c45000080c002c0d6403408078014040d6000420340081c4100d2003001c0808403100d580414054548103240e07803141e50f104d11724080c2030564880340070b10900c11030500240d501c0c82d100322031000507406400581481e08140c1081f0103000c0365041c0c21511032500d9501802079882c025040303016100d80d0041c20001030a003408009501060300e8513002c18038168140a0841e420072203990f082c103200d28003001051407103503180e030440c4030300801d881e88450002d061200e80c5c1c40c900001c05002080341c84a1811030303220f0307030006803a00800101030250a003d0128000e50305112004040d0a41309140401c00001c80d80d4501007003445038400b86150b004049045010181c100a61300000c000b542c0940b03085281071400030b00e0303000201400800b056142c41584088081c1007055a031405402050740d901c042c4808030070002041d00300e406000081049011038843d050200c2160307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549770287 1250 549769037 549769039
    0x90903070b01060305071b0f0b01050a0e060105070c080609101d030403110411030a0501081011030a0b1f1d0904020a03110120061b0a0c0b041e031101060602030702 72
    0x201c07568a001015801041c00820390003e0240c8492410301507095000895402c0b4400d60680341c440c4407504246014000503000340380078142c1c2d00c0081c480300d031041101590040c000d10b449076441605142c4510600c10b030b0351010645225450500545600c0407425800c1142014410040d85404480501000110104820058200700424408522400d151105503000600081414601d000080155603c100e80f070458242da240c0041c004400300380030300d85909089410902050558644078800c511010709290382050390f5100078a0f4507204d0483c65801506824411400c41c0d66002010340710809051483d18000c481e002454802c0c034108200c0b40c010ba0b0050212071074a810b5941d010300c101401300d02c01d410302044074002050500d001ca180303190060541d024040d40e09003000480c107851608004c41000070340c14002c800549509c442c09a14242d081154098283c869090001100110b10514950340d280e8405040078142c0080c801001540840000c000c5985d940504985a004500000b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549771537 1250 549770287 549770303
    0xd0c0801050a030f080c060f150105041d0901060503120702030c0a08070b0703210b090609060906130f0c090302030d050f0703050306010e031e0c0603060d02060a0c0602070f0209090307 81
    0x140042800b11540c032a660380305081146c9880c00040c04546851802c8030300004451061041003014241500d030561070500c00e08286040c41c0c100094210303902c545050101000710300a0000d0704081c07003500407000802c00035003500c00e4600703208880c00060303012440603402071142007050409801c1c411120303011103a503100a090050306103020200d682d44452400c0c3c2c100311400e40a01d400201c48844180685800e180001da5004100d0521000c2000103002e50301c6203081c40b0400071651600500c81d40e124404440c0b250b4000220780508005082019802421900e030400c41100980c002c03281100b524000c504a07420201440c80072600341c40b035801c3c08507480909015410020340a50060358006005041460f0301e070501301c010034900f000c864080c48445034544ac101d10600c80521403a800e80e0000e6a01178a14039201d03010030400c49543d08006e015003400610b07014058860421b242c500742c1e204d107003959142c002e41031001c030081c02c815003a44034000c00ca0120b800400c0010458101a90040c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549772787 1250 549771537 549771539
    0x40b060103020c0330070e1e12070e180708030d050a14040b0412141b071703071a0f04060902030c0414011401020a02060301030f0c05090c0d0c0801050a 67
    0x110301a403c8145200f01a200c1803000c0d030782c01c0c0982d40048601640822550151015411100c40b01001c094811410300403010091640ca4490881e111400d00303020160021980d0042c1c0030503500c00684020500d24060050007041600382c4181c02070040a00b00358000400504c0390a250b10303000321f4400d1089560041041480311131140e08410791218400200103446591a1090144500121f404607160381c149810802080561400600e000903185841c1c080c0030460011300f803643c421111510750380101310500044250003048041c01a004269403581a1960604285c0c0c0d80e4028141c00c80307401d004007070044001c002c0d921030144110300c407210194194440d51141e40080003405010b98140c045c5441001c1d1070388403400348406104842d8940f42456151015079001c8262009031281190040c040d800003582da4074094038150383e00100380315040030751842c0101c020001a807126810a134810b040003200b540810140c202242540303c01e024101c0345903400c84900c00c003401941d50003500800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549774037 1250 549772787 549772789
    0x14030c01020a0b06190e0a0f0c0c06050a0609090f0b1b0d2a0e01030b030703050a081c0c030b04150302030d0f0201142503151703070f0308100509040b06 67
    0xd0004d800140141072542058600c090700341d00a46290850820b445010007030021004051160541c00015031104201c1c00c40304180040c04a801060007805042e1140c001c224100d0403035200c0300040044900401c043c50f002d10341025001403108041d181043d640000070702c1c4030a006d46103000d17189540f8115292441c031946040040100c0641d44c0d0242800390348080d1580c0030000b07848031100c640c0e100c40c1340c0864440d000405588121203d18000d80144c0020000241c0000752213052650059000d621103007100040400030184120900485c0c0c14016421b2215806910203064070034286c13001e004040c1b0b1000a003210306a28800207400d41d01120b03624242034032507000400218014130000c83c0784110307504440c0b8041030a803082c00d0408401030307600182607103d041d0310b0041c280b41c2c00c0c14010815510300d00328107044603210700f14818244482813112041c040c000c490300701d035100c080a1502840c070300700205207800445182e47c484880d400c0100301303860a40042d0b44519400240c802c1940d079440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549775287 1250 549774037 549774053
    0x90a031a1e04151509020408120c030a030c020f06070f0905030f0a02060901020102070602030108010c020f1203040b070c02120105010f140f06090109050303030708150901080c1018080714030c01020a 87
    0x20140521303038440b51004d0505241e41810018190754101503100e50510340b0305402c0c440c00440d90130884030100212141e4000203c203540803000c09080014407401f0209003079003002011300522429004140402510700e40100c18908019240e903982e0105907152030a140e500c070843e0a14448a90091076035800610b4800c0041050310b41c103100240c00d0800a9444078241d030401e811964281e51511481d500040d03040001088400382c88000f8014420500307040310940c44042d10240010502d800003c079098004e409260416034082e00c1402e4a10411203e507000744428040ca03102030f10342100028002514034400044d101c030040010241c00260703410000c440d800380c0e2149040c011025800140caa5040c0302940c4502100d4803110300f00d00e041890094840101603645114912117401802005000030f0740c0b2400742c000b511402c1582440f464150b0302202e2151541160070f0940c00302203803e40012590b20102c0310380f891840c00101c4410700301a1503903500c2d09050f005134000e140e2000030440039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549776537 1250 549775287 549775313
    0x8030c070603092f1302071a0106090e06010e1e03010507050f12180a030c1e1716060f0605030c04020a0e0d0807061104050f0301060303021c05090a031a1e04 69
    0x40640c400081c4d0030720700420500182840c000144507804110801070014201c0d500d8071110790601950000c0d814614054803a00142c05245800001c4030000b4100340d014801c031186049009000710541660310001d195460f840c008558041d5007400f002c940000c3c02a002e80f0801c1600020407824848109521003150200610103840222070b075509003464007051060884103806070b40c0e514860961410241408480300c2d100703c0903080c00d40170b14008580380c40e14040800300038004a0b6682e004820385040311045010707014110f5490300700180d4054140d170b44800101c4000342c00307884e594074205d004c1104034000c000c600070124800c1d585a80c00d501d0311828a081d040e201310001401c00102c3d403150740c201c505c10300c4060f400307000c005014449442d20980700c0c0101e800882c028011103007103580003500c500825040c02082c0903002540c4000c40d0040007511034900707001d0805a091590390a04d20b45100143c0c0d00701491000800108400c8903150b809442d20510070203801956484035550380c3c40010070707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549777787 1250 549776537 549776603
    0x3050d0e0f1311030a020301060206220f020102030d05090d1103030402090a0e070911040e091908030709050324180a0f080403080309060603010b1207030204150e0108030c07060309 79
    0x56202c1c54080000f011000e5409103107400b10040c0c483d81040000303460300034081c0000440b420030141050240c0000405005103903444210f41103c40ca403803005030314502804610040c034a08000400c40c0740c17007000856002081144e6100c0d149290500c549641701e2000742d40294004404000003180c807200c5410960802a401c0d0032a0b40c10756031101414111a04551760098486001a04006115004003c5a000442039000d0030082c84a80114042c085c0b59440c000e003038a9002c000a01300a0180d80300c2070081c00d01809a8051034884441a003200118918116944a407140440c03211154840940391140b40440207110b5000d07151075012240c400c0040842da140c90802010000403800c001950049484100800640c2845001c050940300002c4509024808000c8600d030040e00024980b800c40381c05650000d0b5030050f100300300710070028a40250400c010240700018180b20000001c0012a0300c1c00182c0c0c45564989500710240c1e51001c802510300c2c26803410044048a01d2141c03100900700c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549779037 1250 549777787 549777791
    0x31412060f030708150a0b01111c021014040b0708010b04060e0f13140a021905031008030a1709060105010804030305100302030613031d0108040311010908030103080403050d0e0f13 79
    0x613441c05814a0082d03454071622030880c140c000e2000d640c10500880d0402c01003400c188511015040c8010b50303802050364419141c09880403075000c958000d201380c10501c05648000d2003c00781003000515450310075201120701400c4540000c54a42c0709518060680e000041d600b0301d803910b00358023240d00d03040d014200c5512005125031101241d1700d040340501425151003012400810110800d02c0340071000302180759050040080c903002c0c002c0d124481329003c190b400c003552a500e0340414400c0c0b0201e1500025801d120014105021541042e002c0d9404200d1101105180e41d0320041c030754031404280700709070128100401060010b402608a0340e809a40201c0b04105640d503600001d15044007524100800c40c1300802d81c90034183d200000c0610307441c001031003c0306199003600003004e129004001800704200f40d030a0385002e40003074222103500c0b900a489075449503102d041c40d00803640142b20464140c030500000144c1071380034410802405000070095035040100b0414000d406000c80c20110b0266 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549780287 1250 549779037 549779039
    0x60c080f0d05040f20030304060f0504030506071106150d0605131209060f020f190c0b0c1b0108090c1e060712090f0f12060e0d0c031412060f0307 64
    0x310881c440d05118500130070003001413500c40d003420308881c5080c0900c180c12040b038504044258400000310303011150f241c90524201100d1000c12181c60195400c003c1180c01f0b45400c0c0007805a000c210784102d49802c00c00d580c0c59440705c2889400c4001d01d0a13140d48c111041003141408a5202d07444181d000501c140c541809008980d01c00c0a800c3d100d08107c0c0103d50410010f02221b039205540c080d4200b200d00040202503017100405076150100280110903408222745441041240400c4200030f04800790010344413200340310f02a86600c49442600b10341062000c07820003d41c403482c40180207141c1840980781d180e081c80240310300d03443ca1001702030001603002250865074a4510042990034001c8040340d000f0081101e0050a2032010741c4400d03011114180d081c40070300c210a21080031a0760304c1b4841c581c0c02032940303812005032000c61130301c000c24068007240c41502c540185048040611a581e8100a000700820383e110038040d000c10050b80d84290b500140d410f0030514501e2544c1c29000b13045500903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549781537 1250 549780287 549780307
    0xb07030215180a0332070b0601140703081b18040c050910090e0c040605032404060e060415080307140c04061205010e1903030506150d0204170304060c080f 68
    0x1c41e0141c0803c400080c0002c83c5904810a8651007803445c046000070091204c6405581c40010b0080980190007031a180001c1217451380583c10500200c2401c45005444028508021300514811202d0504450b4180c41c00d001910031481255101e1220344484c00e90248880300b800002c2603100c090b02e091140400c070044203903840a591210b54011a9903c08142d42003c1408a4201d4080c21002d12240d00340000c0c405160024160380d80410000c0d03282142000c00207050f00081e40d9000c00ca900b061401c0c01c08505011480700c0f4510038642541c0a0150710380c202c020f2038822002c1e104080094205000e00e1001500c0d051300b68000004401c100c032170384202000024120750707088d408040300031408000101003110a0180c0403c0c112441c02911600c003103c810318800c0c40504000804060b5075200040b075603624816092415171200d40d425881e000165071003002580640160520140840070004900e2000400c840a82c0e181c4e40e240c914424040e0344c2d550a54101051030740200209000381940307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549782787 1250 549781537 549781543
    0xc03090f0807060207080304080c010c030c02090406020403020f0d0228150201051b090303120421081e01120303020304140f0705040f02030708040b070c051501060201060b0703021518 80
    0x703055040058182c0b60303e040c00180c0340c00d92070351000c0b5568109000400c8607200215940c40f81c03200038200411000e010349000c03186131502d090000d51100100b420f010900c4040c0d0f0142c0260791003619501140d144410402028400c4000025402100e8454a10f04240d0300c1001e24601580e018142e00d5654070340c442440ca2607540208000181e55030801c0040c14065a203001c0f000614103100c4910785054880401d459114401351014103a000101150400c40b46420340c8012064518071120480e040036401099444180e55040311604c603820501081c403501801c445c103c6042d0701130039900001e5943c00750040d4000a01c1070703801402c2c840d01c00d03c200d40103004ca2417202a0381400303040070302e08101c100411a1003106c41c1d0a4510320500810441e41d4000c0071503034225421030b02050080da210401100c0c5c80c02c141d44000c2007401010003c09180c0414214141611030f250024041c494844241003294003c0d1080a03005a10120101e005668840308039608a0080a0b040310605c8000c2a103600d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549784037 1250 549782787 549782789
    0x501360b1c0b06090c040f0623070c0302010908010605010c150b15090a0605030f0a1a03031305130b100c0c0e0106050a0e2403060d0c2709030f0c03090f 67
    0x100c800b400d0040081a24105030380b250711000800c200303814517003015543c42d09143e560041c1028001060b4003910802185488038803090750b01414156144480c0c070f49180158501d10003280030503041c0d100071681c050306019101c01e031241070f583d240c40c01c003080c3c483e0051032003801c0084520030303502d0b90300701516102c4091141d507000c01300c081c0070307a40e401d00b9003400921801a400340c0d00700b14050042c03100c2d41c41a06801a0802c090620114000d603029100268035122203ca07298544000154030045072515000c01040351f600712074980e0324801c27003410042510052003084cc1e02c41d5818103505a003900510b0075210250090030714000381c54503800d944a29400a0308640d010500c041001304100e9030081c12504090800d40e91102180b134080203d0b001a201a1480381104902000069031516911070301d00202e41c204009012169a40410301e054501c401c00c0c40d0710000040101000301003050162880451f8181d98800308003400080480d4000d05021084040082805002880d02c190460101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549785287 1250 549784037 549784043
    0xa0303020607080a02030403091415030a0f0b030c0102070605180301090f1e020a05041e0c03020c1b01080408031503011e060806040b0a1d010f0501360b1c 68
    0x41118100b031007002e000b24030000c3c80400303190b00400405c40003a40c09201d40307003140d50040d07840300c109159400294041c556644610000341010040001c5c1034155040075514030501101000f04141e25018561103035445203005015030711090b01000030350b101f40d004102c4d0119520768803222410700c000203404d40c0c2c411141070700c402c2101c203161800d02622101c29050390f001c40c403819540c4d034016808907908c10310a11480b8450303a86c0d010fa48036034120400c8141018004030300100540c03c1c004038060029000b8000c611b015100d826041510002d02c01c03107025501c0c2e0140c40e030007081c1d500c0c1c2d9110002580014000a0682c09486d001d5205803400d0143d144015184820f440854443d107444004482d820f5000c0e001070340c008000d10011034046a6107030341005401e10301158070900481e0840700414003800700d400d190320713207094083c00150b15800f0605903124400e5001ca00c444401c01d586042c0ca1806901201d03061a10600483e50308d16842905601005001d0329110303c1d440c0c01d10140c0d00d41c032110907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549786537 1250 549785287 549785293
    0x219030803061809100c020a050105040f030816140906070b25050901050f0d0902030706081014030d1d060d020d0c140307030e070906032604050112090f020a030302 72
    0x11105500d0450910300000c4040e024a140300c0c07401600c0e03140c0c1c075a184071003c41440c1c2c1c0c0c2c2d00220307801d40c0300303118200c4050b80002c0240450703346803500c0445038920340c030207400003802c50f00442c500c10480c22000b50000070036603c90381c007100d803107101902640c03010104503444042001500c1c0007c00d1481c0c02880f41c007a9080091340d00d051071001c0c54200303521040c90b07810800c00b04172480c89070782c1080540d0481e905800c581d07516103070700c515100020030180b44041d605201c1d0010004029a01c00040707413140f20542c43ea1224503075246d03c0800562500c041e640d50680052a41011440c40346403902c07002241d441d1100894410000840c010340c2c84054484040b940004d80801c940099015024801c001c600d00000e0b00740e10468012a140400303007103502016221a180700e5080020400b90000e030075450410008980c0c1ca107020161107020b4002200a0307124641c0c510141e000000640d0100c48068541c4110118020028001049281011102e41250212503c05a2505040300b00998465001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549787787 1250 549786537 549786541
    0xb07020d120513080c07090204260c0d030f030f0e0c090f0f040206030c041a09090601080115030c030608010609151202060a080a1e150503070b03010b03040219030803 73
    0x8001c010340040801480c5035410081401080750710602c81c060003d400c400c010340c440b01700a080904101c142d41c0180301c2c0600101b40458034100c0e81114445070070340111018922104000300e10744a03103c0d071081681c4501c0040f100c101013401200b5079250707038a29180005010360500e1072282221511122101594000e92a408550400555280e0001c2a03000400058906915000341d2424003c2c0001c7c0140004004100c4004000041d60302802c0b00000c0d4081000304022580141e802021145204a68910114480d540662041ea050310b5401e030b50030b04600001401540075001740720b0580304240d50f903030000502e10020300c03860014005001d0301003040c0003400e6503200b0001d42138000340300984a9154a600690f01c40044400da1822400c21b0b070038aa49400c0803000800200c122100000b44e00c4600a104800e03030b07441000080c610f0504003503460f403503038141035440e0403138012003108040c02c20046c0545c04c0800051540140f0081c0784103071003255007041c0c4030310703104c01d51040300c2414011003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549789037 1250 549787787 549787813
    0xf0e0f0421091802031b0c0708070e060a0b18240d020d1415010e041d0d2c040b1203040b0d0b0619080a021b030c2b0e010c0b0702 57
    0x500c61040f209220b40660550a00700790074960100e40a808441a05000078a40600c082c144032180061507200150b0b001ca654079020a00c000c68101c40003032141c8603107000485c40c44404010307030700717041395412a070f80074500b6600910208080d0741044142810742c1c94140f0480c491468003c103110802c0f1071016880302d41581c3c40109071540d40e44403000608800d81000303082c48104032151241c1e842444c0c1040b2840340d200110b00107000b18130304510030064100f0003000c4500300245030344200d8003907990301c090a23050984160354401403a03509000c200c141e10103201a0f1400b600032201c040300007441480c1500005a0003441c65100d0f0f0710184250305c0204200745422018400c100c4c640c1003e88000c3d1428100e0094140520407210400c41800180d90210f00c042115506491500c0c80164a10b1280d0304600ea03201d607242c101e4410b50002e48502c5d44d0520032039842014541248403584034541d400a8900000e580444075000410b0400c840151410301051000c642240142055005003c00307941da11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549790287 1250 549789037 549789059
    0x1d03120723010e1005100f060315080304060905130b1f032703082707032303041a0706060e01061701080c10120e030909010f0e0f042109 60
    0x500410740030303450500d41200041c4040740582003205090b40000b0207a0301d80c000514034604c60b4103c00c030300c21410000852200d806030f2000c006000c802c881c0a64090395030742e1082d40d920580c0100301c0020300500c81080103003000d800003480c60800b0389020607008541000f240d4030b08869590010120005c0b00c00c42c00c50783d018460820b94001203a0181c1000312944091540d103c5011001000c01c00000c000404506500c4400c0300742c014024081c0071000700e00490381c0d6032810350380401d503084440c011004200d0003201c015284840756990156040601e48902c54020080030036100a504a04000d150000344151040b440502031001c00c807081941002e0b001010103040e104200704402402005001644000a103041071a0084480450320030b0500c50454900c1e55100c00081e8050804d14100403092011000c1c002c20001642c95407813680c0d841c071703811860814030301c905103007400c000020808108860140c0c56000b4028251600f100c01c0c00d00328000702007044452a00080c003030703032030600074401da40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549791537 1250 549790287 549790343
    0x3030f0417030f0316170a0606030c0513031b0e01180b0d050703060c230c240703090309051210050a06141201091505011a07031d031207 60
    0x100011400c125901d008200c81d0712001d017104440e0850000c0205200d8411440c2044c4283e44144000701c504000c454139010340703140d00450020906059190b8001131055094408102c80085001001491600c42c000000002d00c902044242016800b2600c0d0803171544860081841d20740d43e000e0030040c1c0055000b00c480c03000043c3c0c480c0003210b950b907000c5080040d890003540d400110000d643c00c052182910840311881d0300124041c2d00080195800030800e001d444040d800d0021b66010100b2102c59000411050050402e410480d40114660174420740c0070130303043c0e44a42050f0a03241d4840d0b002820004c090741c541c500c01d41c44108140c2001c0c440e4041c241d00301404100a0140500b8040c0801e04440243c69841c05801a04103d4010344025040408071035000118a0b500084030580000a890240036242d544600346000010700c0d6070020071686010f400da50341208c0c1c0314040d81c0004140380110743e519414841c074484580d126140320028090603226041c0d81441c800786510059880f000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549792787 1250 549791537 549791579
    0xa020108130206071101020f01090602090405010608060915060f0408010507201506030322150f120b0a050a09021b060f01060807030216030e0108090d1d03010204030203030f04 77
    0x218071101001038a40c40f041d00e85040c1c4c000c684602c003d0841c00100e00d03011005240305000e6003882c500c4030900a07154002d090f28282590180200e80e241c0200381d516881c2075498a400400c0301000a04074000b4106490050b40b008040303a2030845040008051a04250080c2e650b5954071428419103d401410102180c81042c04058098002000d226202c10317510980340300080201002800300c4e5418402c42d505019402c802601c41705001c44201c13000101b07030003000300d440b01a440b03142d0418007a09880780658141c0c5d59a414264004a800000d0400c400150fa0484d08100020a02d692445a084080c1228000041e203a0032000320320310300464070543c8500c0e150400d800340158075101c102c80d541507801d5410b060203251a0840120001d03c51180c078107108038400c1070000e0405a210070300c109043c109903118111034480e00754964a03520b5241241004c643d0440d0108403607100b064071040001c10080005017055a6a00840c3c10341d03200d80e0000c8030018000134140003000c0492000700300350907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549794037 1250 549792787 549792811
    0x6160e0a2c010b0f1305120d0906020622111e040c0c02030312040305280e0303161202011e02030a11120601030f111207030c1809090305040b0c0a020108 67
    0x100d803561240040c4580448044941c0b0001602c59175481a0074a000040401610400042007581200b680310b080d00103000000924441e000200d007480051402d0040c01d048210781600c00d681d00085190307071030804003110140300041911546540309861948030071800340900c800c080c008802c01c001c64942540500620120994001c00340c0c8002041c1c8005441c211055885da0b251070800ba06c050082040310307000310714580441d07603240806c046180b00c201d585441c2c00070111802000c1545078020545002510151851100d020800c44505c44070f6016450000091001c080d00414a0009051180700c3d04142c0000034003441204a20071203002202d41c0d42154100103980003820054180980ba850401d9120001c50314420300c540d00030301101c25051403c0d5a40c443c0401c1040300480c04807000c00210303240500c40d2900a015043c529805545404141d041605180e00d0000524031840b081c0c0c10494203202c003158030034186004195a100000007003000c110140300041c40f801000b0700340c1103059 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549795287 1250 549794037 549794039
    0x10908070b0301170a080a02010b0906040504050a0605070509030d090503060f0705120c090d030c06060f1208210c030f100506071e05030d0b040f0b010206160e0a2c01 73
    0x500080c1543d065612100b201060780c41c2d602d4603a0301e00400b01502070600c0740300103582c1c1c0c481901580680c07100f000590f1500c42c0c40e6140d4040100311101150040c01d160450b816960020300c81ea032109074019a141041401c08140c1000f1900e006200784464001c2601800c09101500d410040035030322000c202c1c81c0c40d00f14548844024040c0c0185014200d07030212140100c4e040c16480340c1502ea0481029105000b8188241001080c0e4095110142d030b0700c0345000d40120300b00082a109500f07842c0d0480012240103890b60b254200c80c3d000c8002428504c0c16100e0b82d08001c109901c0351801221000764064990406640a000c0140e0141c1508601808036008000c1030300c0340c405407040c46810101c0d006000c14080100651618060301c020070b40d01000660401c541000d9116184130341d130940e020040080319000700e000f15801049401d0160f80840c8c0020402c01c00c920100c540b4244504d0230742101f0302c0d0540450682150381d00144d80c205080e801ca2444840342229026184041480c284819 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549796537 1250 549795287 549795299
    0xa03113006030c010c0c08030d02030a0e1c0f110f0109030f05041a210a050907060327150507170919080c030912010b040501151b020d08030a0b01090807 67
    0x207511800001d030500003031445c40d00901c0352110303030355005150500030760780e40e841c1c1c03518240d009500460360000d01601e0324103e4001c1d0385000480045942e2051180c4441000348801603408441d90b860b504208070a840c0907010405050180c01c04041510300045110145450017400030700c801a07020b41040414001004000c0800001400450034100180c0e40d9184040401c500a40200e900c47c00c0c0b90010028030080300625131040344100c0c040002d80319103a4a449086094950040c0c0c1109195074405a240e801d54504011442e1a403241b1036400601144c0c000c1641554000c42d150360200b0a80010320507607003d120b640c603512a610b40050000d0709110007002a0380d41e50031801401c00c0f08041401120510108211410040005c1c60306400c9028249802d0282c44081000c1d8040c50030031000049080d0710224a44400f0351a44401d04540085000c260309103100000030391b03009008490303a1000c81c1d1008011409224001008140403540c00005000240309500a40c21684078000420030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549797787 1250 549796537 549796543
    0x61201060c1401020703020619060303090e0709030b01153b04020405150d110c060a1a040203010e0a060f05212401180612080a0311300603 61
    0x1540c01506014851840e9414640358640b80c0e00201c14003503100103048005c0c0340d00080e17140d03c80e002c004a00841c19014141800680e00301e4400140409d541d82030512103602c1c1e14146540c00b10744c0f80380084000d0b5607920340c5520080283d0007204000b000860151520750b0002c0c040d42081d03c524001d201c011400070406981c03041c003003454030f106621a0707141d1105a84580440d40103090080043c0c030310802c5500c400025610085650b6505841d000c5559421518901034640090003480502142e0356100f078a9000342c01c2010b034590584109072004000b503503a0344040d6019119072140800c40c1d00d840609201282c0300f64024040049240078208419601d151000c40c10200c01040314501010f4071240c0c0b8901011040d003d0480d0307000580b0f803003a140c00050310070f04032204040000e00380d2031003003800300403a41c85000700030105a81d11503440109603110b0052002420794030700040e4000942c03005e500b0316007258402e141144030380100545403100007012100f030041e00f904c0c2c400003410400000781c1d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549799037 1250 549797787 549797789
    0x25020c0a090216020306011716030f0f0804030c06080402030d080c03150d0507080f100b01090303110c0901090c18180b0a090203070201090b0f060102100203090304120818061201 78
    0x541e0005080f64460200302002c0c0c1c05a90302038225107055031508408110716160360070b4190a84265440d80240c1c0e1139001d40501141d40100421000c10096200c10701821890300c0f055400d02010440003000890075103088006000b503035100115803c00e407041504041011200d0b000308440c020500060b0900360007281d400031491192425042c4c280700114580c010510703001342490048050001b614070000ca80d094699000f1016610022101d9100c041142e107d0f0f40c0c0310f400541e000b00d081c4000790044040ca031414103c1021180c81042c6000000c81c10361090b00445070468888820b10202130f0018030040d40718551402803500d55003400b01620b8840e080c60340b008592a12801d560f00c40740c441c044804060041c40d402555640350862001c3e0203080092030880b801005a400505800307280d0300c006000d43d4059024044501c5212081406504080c01100c000c0c0401c2100003941c4800301c040e020000d100b41480c0303844001601c9a101003064003055039010301c604004110324100c000c0c0c8058 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549800287 1250 549799037 549799049
    0x3070c21081f140a17030a08060d0b01060c0c05030a050c0102071a070204020a03060807090b09010504050609041407270501050301051006030e030724060b0f1b0c030625020c0a 77
    0x2506100d1074800158510203140d212400248030701c2417141e6003a00c04001000c0c0000720f501c40c031080f41c56200038050014100b60f00689010b01e50070040c07042c14031585242d88014018001011929140c4000034200700c2114012603060380328801943c105d50701408a03400510040e11060411000d110107088036104104000340b00e40e5000424426260003503210b13101811101c13040307a0f562600c96841900504c2000c03040d9102d01602000043e034ad291a004061091201801503134041e200d50380c4d182400c2d40707461020f00d024010100041407080c2c2090925032001c040032400d00c00b007014044c40c5021910180c00c0380d03000341d042404120345c1c5c55111102e1402c8401c6031030001054803000741c2031801c40c010941c0080198185840b01c495410034041c500c501140d2011040050030b81d01d5081a080d4440d101c40a56002c03c01c2c0038401052a01350a0300007030b0752150040d18072804076500041e043c03100c212500010241d12a0408a040d2010104105008164002405604021800500350250502c620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549801537 1250 549800287 549800309
    0x90103060b0f0c1e0d051608030f1e1012150f0b1305090a080307030b04060909120c0b0a0b18100602070b0405031e0c0d03051e03060f0603070c21081f 66
    0x7e06003012501e00c0e11000c840d000501180c90341800e01d1440e003500000d480484409100b1040310486c1c140d01035065001c1e58600a20040350f502e03000030501d48001445064460595030000700c000d03c0500e010300da5407683c0002e030015444c00d10408010245614040541c1494a090301b00a1000d400040a1180b1034000b1086501e81d5030340c0f10124060180000116009410041d00081244094200610192045021036002500c000044441508904024020416a80206400400503803200b0144800500600304a04034107114215110007624501c0c04d850052030100304403641030105602909a0340080780c9002c1c07034480004c0d5681c440d0014002081c01e500407403200f24008000c410100b02c0003600e545200e0010341005411600b18010040001840b8002c4050b108106c0e07080b039204003002014484210300c6001440081d4000820360300a01000c210310350081001840c0c507420310020302e40d0090300c0b40e0041c1341c010b09a410103010406510b60000080b1210380b01d148901e41a42e01c10044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549802787 1250 549801537 549801547
    0x10503061903050a030f3e030418140c07120912050114060105040321051b1c0e09040201031122080c1005070602090103060b0f0c1e0d05 60
    0x38445000440c4050044450a0070010410502040444180d402500c822100b12201c03081601d1901c240c2904041048210102140c4000300425032075120f00801840b4a0001c1c0b4441035a155038416001114814401e90601700d80b10140d028059225441d194055881d01307006455130040d0040c900c0040046a50b40c0e5140744003031150102500500d100c10b120f52502c2e8550038550b00034007503a8450317400d200c2c02c580050600d502a5045404a0b6070064001005640d0050500c0c00419010b0044080000801c000505914542d00047c4080b00040241800011207400228030400d46280402031003400c013000c0d2119030b01d40301055405902801c02003041414031940c0061407141e40c045100000e9043d540000403001c030310010341a00d00c080d04030359400c0c84120420800104403604000014020040c68000500a4000c2c011698060401040e440d807034040000c0b9a07001104030709107103100420418501201000010984401c0041c249000c94202c0c80c11900c0716400a064814080c002075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549804037 1250 549802787 549802789
    0x5060a05090c090103110a0503060637080706080106031514040f0213031703040507031212090303020901080f01080601060c0f020a1707171b030102210109140603030901050306 77
    0x2c041c2024140040c585840d41d0303101d00d4007a91594a800c40e0b140039004803100802c15050001d011400f5110081c124220b1484200030400b404000c209000c3c5200c00080d0301e1f061a42c10300c100d0002408105025200140c10a200209904416406902054280080ca1700d8406c000d00780981951000681c24403a0300494011801409055040b260910701c0042e0f11141c40001850000c1031307d1240000e00180e00208801801c0341c0020345001e406d98101210400014a494528520b925400d080c06190484580d60007001c036103400205038003107500015121950360713002c8003ea40c0031b0300e40110031201d075043c0845541e64003030501480042c803814110846c2808048910400c4140d402009000c2c030136160f01603507203241d68441451140388114000410480030f00040309d444002490b0003005101c122f10100340c031000b4085021a0155030800c8180b803108104110522003040a682c038218a51400301c803441102e43e440800c1e10380c041104144442650044211a005002460155100d4480300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549805287 1250 549804037 549804043
    0x12090f121f0e0c0a0503060f060111070f0e01050105270303090a090b01030e03070503031f0914070f210903030e0f01060602100207030f0c030909110304060e070305060a0509 76
    0x81609450381d40d0414801c041106980c1004040e8102c1c1e005407120b621816080c042006a80e0161070303455040030000402c3e804403a22000e6018505241400c0c40c140d01c410389908041d02500048410040743c030052045150300c0a00b540108030a182c9103180424000c1071141e45a00c0c10744050000911800d40d401d00d03a001c004f0707146141c50090003844401c2c5d039032420900500100401c0c0e400300741000400c1030160f10220541c0c00145d004005549036551329110f4000060104008001042c2c04030f1000c46c0154031881800032044120044020b81d06000d00d01802581c100c40d000d00400c0385a40b140c8400340703c0600c00c0061010f000c9004184402180f5043c1c0151030150650301c418411042e42d118580350541000c0c0840740301e502954508e40030b52051000782c3c0305e2140d001d804203041d90309451100788110161164a4017a00e000b02c41e06481d41110780691303240c48603008610740040140003d1004620070b0ba611041c0342d50007007a20600d1540c80c1612841c004004004169a0314001110b0000038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549806537 1250 549805287 549805303
    0x406142806080d030b0f06040b390f010b10022a03121806120601050d0b0406170f01060f0b0313020415060305060f0906060c01180506040512090f12 65
    0x400151035260380030140050040100404842c400d810242c2204a5400e009049034144c4600400310352601d44d0158a01d172b044611180d154040001801d000301c29005d41d58205040f1000070b00162421070b09102495080d81c003c190094401c100000b900d02400c5d40000705070001186a14030540c0c4105000200910200410b2003690103002d40071415034800e100c00300a0003e03020741242d0394030f900d0340790302071103d140141081c015292210b007010448540c011400761181092001c004a1000342c8600460280c50240c0e2103e4200080350016103135240040c090451a00540c80082200131301d042c0101050560600c60850507180010208501910460301d000e070154018100340500c400b4614103900c1c2070850721407180082c1c58078001c10001e141665040b10701000013400d64042c1d44810301000201c0e40800f140c1e1131550340c3d96a07228020702607280d9119030540600050b181c07502e881d09040e410039544950001d580d100c100000122a914045407020841c030079034407240c030014168001880c01c850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549807787 1250 549806537 549806549
    0x180302060403080c1903020c011209211b02090109110f0408070e07032a090806100302041d19080708030a090c080d050304060e0106031401050406142806 67
    0xd0100030302001000500624444c0b60454824a4084895030101c0300c603094000c0050700070032003c00c0e42e584100418150f2542c21500059402c6255230340000c9440729a1104009141d00c1c2081e81c0100d41041a02a2160158a049080305e403194005600e40f035050284e582c12036500e80200103024450800d03280001c5401e410720b50b50b19160f425250b62000248582d0a28110903000a4070861103401240581a0751282d0344402590103032500c40d0149500c1140010015500e20010750303000304010350b038000c0b017081c0c110066103804c600511060341c1c40e12062072201000180307868020800042c01d5540410070200000d4011510700d804107003446108005402104080244480040954090a0041e00c00c410003440039944100054882c50248042408030f00180002400704490f5080348400850f44000010070302e80701d9540b03034102409000c585a0680d036880800c82048203901c60f030150410344404040c0c2c1440c0c9a490300842c51141c500006580f400044044d07924003254108401a0035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549809037 1250 549807787 549807799
    0xb0c07050904030c0615350102040605130e0c030a09080d020c15012403051b12191104030213060305060c0d0f060b090d030516240605010f180302 64
    0xb82820014605050040181d5005180c01c0c1d480480e510303007200303000450380c0c5211a40b07580c0c04000c41041c1141c00e480404c1940c1030000019200e070413028401400500f0050b21180e44800c0700049030481c003061030700054011240c40c018424001004016a91302804a8201140000d49413501f451b41d80681c03194060180c1c004641022050404100144100b1341001c40c160f03c1d82e6070303002c040c0c1440b06400079003440b00d0307103140744841091098121a501021343c105070000442d1800420945078448103061340381c21846402c3c8800c454182228645408042d0014001000a048859043e10407440001d129007001c030507959444948d50000002550814250380d030074a800001c00f0440d6100d0316070424683d1520020261000180c89884207840946901c103007041c81d030005204070314080c84000d805010040c0090140340c0c01d0050318000350392284100c50326000c03034030100c0300110070541190b8110305d05000c4280202d980c440d880c03280e0102c440c508802650540f00065a8240744d541010390005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549810287 1250 549809037 549809041
    0x513120c0804030b0a0f110a030b030304050310021e0a0f0302031e01150e032802180709051e0f010509130e0a110102060415051015090e07030c090b0c070509 69
    0x4c81000000392180e07049440c1806680030321070711503080722502c0c010380342050028820718a045220340d2040351412409000c49290075202c4d0000f81c03a0006000c1e10580c000d0300000d01d4003000844d015011001c90032640340300d00303011519001030401d5903c204c0c0407040584c0800020b8500c040314640002e096084040180156150b0480710b001c0c0801c044802c0c0407070541d02e070246244c200015032424500c2c43e2860003143c5220240c00807000742c3c03580310070781e48004103d45584e07503100030000303182c0200982c1d207842c0105484c10090200c44101c100c03101d0140b00c40078529050319120b00e012484400000d191040c1c2c2d41c0340c200e0008410600700e10b0092449443d000d07454a4031b150000d18a000d071809201d010078a50502c1c2d004903a03810044500818208103803a40c007400c03069903088603810a80d417204000e08562181c2c00c4524000020300481d0005900007000c204010004182580007055441c052007030b6850841c010301b1240003407040388030b010710024035226041014000c0c500503140042c2000058 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549811537 1250 549810287 549810293
    0x903020a060c052107020f0d0e0a1703160602040816050f090613020a1e050a08090c2103040e070c0b012324031305100513120c080403 59
    0x20103a014088a03842e01d09907110b000c56000e442968a0311443d210b03004013104003922000b000c0e90700500b5180c15403080102c4080100400d0107114406007950340d5184006ca4050104140705240e03074481d01400702d206003250a00703400802111a800c0c1d030b01c0441d148030b424514110000f44036030760101c4000d0041c02d1200c1600001c3d0b030824011600100c5050f003203044148108808400309441c0c1542c0128103e50800402c600340e0040c00c5001150b0400300c051101072a10641d104e4100d104800c0014000101d20361400d80102c0d03100d42040c141c4008065801c100d0020a070307107403440f140030301c4c1c4151549581d01d1190b00c101708580c060a00707260740c04100d05100c100a030108801d00811103001074610008541550b544101c0405000314028160b0305490020501090714061855641d8001c0342c01c7e00d0f514280450f40081d0700481416617030000300c00f2642005800c010100d00c00107050303424002880001009603200785840c40c0c01059802e007024403060309851045000c18006c0c8203c0c0301150000c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549812787 1250 549811537 549811543
    0x7271802040501030509030f09190e041a15031f0207050f030405030f0c03060613020706050c032a040605030c0d0c020114070305040209181f05040210020f071a040306090302 76
    0x40b240282c034188059281c210303030503450b0f000310a42c4892051050241c0c2407a46000c0300d041c03a03008981c2c0d402d1000700e61103d2003410420710480b002d451100d401062041c03c240303440380300d070b601030030b43c05041d81d04072500f0b00025112a007400001c85850307071141225482245035811581f6060f0f01608913000f02850300b0b50562030341c1061103294400e0003841a1060045e0000c2a80d0001103001000b8160564508040180c4442100003100410f503003440450002503542c403070380380200c0481d40c44944910300411018001c1d0142241c41c3c420400041c94911603111403029142951b181c0e0070515101d580e001c00c007400c0c5024011010703c11a08000d0360030b840c00d4065006000031200d00450300c1c2c02c0d9807a0700003030b02a1082030301e0003500810904001a81c6822441c0e03400c00b20705040f000c1d03c0c10111545074541030440480b4061054076525004d210440c075150f40d0f03100e4020070500142400d0340c1c030200b03090384450702482040d88060316072009036000c28400044902450380f00c1c50401000003035040080d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549814037 1250 549812787 549812789
    0xc1203090f06180d030c030603120810080c1e0301091a01031a0621030c1b091617060f121f15120204020702040219030c080727180204 59
    0x1c03090142c0750110b000e030206a0102c06400700e1a50060010300705248044000700400c00700780041643e1000040000349000f480c0180142c80e560310743c96182403224042840b194284c0c4076000c0d5130b00860f005441c03921040011102d176030000c5605a01e18031040c000c01c0c00b424403444000d010300300802032600002d094101080c140d901845040c00321008003002c044082009075a484e501c42c05e07200b11401d0410032100c0060900c411003007601d04107500c02000a2600d80c01d01c81c6c5441404600003c098581070414880340d01400a80704450910020080a84a0101006000e92554019002a010341c890113410012484098045044503002e800e04070307201d0011201080c50440154140324180146001d5296a001c8814202c2103882c40c141d510f410146103460101d801035024005800960f4039031001e002c14504140c80400b04079082c0c2c1d0000c084410308a003000a000e148403d1213802c9a1119040480440544000c100c0d00e0403086022007406050b440704a9070fa03980684903610b0b0341140c0140c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549815287 1250 549814037 549814063
    0x30b04060b0402210f100510031506050a0e0303120c03090a0215030a0c020c0112092d0b0a090308060d030507170c0705030304120b072106050907110709020c120309 72
    0x30381070761517102052a00300b4081d5000d0b09400840c3c0c4052100b4501100300401034481801c0005000500300100c64100030554002d0700450310102e62540388a401519103500c1c02021030255241c00d001012820345800e0182101c05002000300c00219803034001c1058030045500101058200101070a4070b00d415401100d01c03c920300d003003001000300305000103120516500c058603001d4040d14200398150080c500c451090352070300016a420022004010815504001c1013190a281c1c051103041924941c5c1c07024260f80300142c605101603000c640d001c00c00d01d80102c022144410003800505003141c060003840009443d0061413000301c2080307903000c001060207401800980345026940c500309038980c01184100d80050b291081c004001643e21840940d01840c01c0c10540ba0108440705d0807000c260828001e504c07419510303941448245003400718143e200d00c10b0310b4810080002403456a4840c0e442e031080401103500425030340c0804909000c9600c2a16403201000c0c0c81345001b445195948030340d00000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549816537 1250 549815287 549815347
    0x160501021b01020a090e10030c0803092d011b08120402040c05070503031807170105040309050901030816020102120c0a1101030207030f0e030717010c08070315030b04060b0402 77
    0x60302214074180291a4080d80a45035000900d190141c00104008010295201c0020080021000404984504014254007002140c90750303407103410301016102e980b4031210b034044003518051101280e50080319100e082840c0c18603106041854140050b82d10100052900c080491102c00010360350b2101407280d8001c44051000044c0700c0e03c02d40340d520502001030701a400c1040010b0b01d0601003179480b00d400b0350f82000c5030099641c405120880d10080c100c1d24507184d4580040c84289a0f00c8100180030300402c903078003035003945142d032104298071520904045841030740807004156030081c8642c5c04004191100d0f1655001010030003911500001d0040713404c03082c106607014165101307109a4425036819240e042c4500c0141d181512155a010320595051140b074070f001c5507a600d61148040074100e003d0012a100580182c0030b4600310005180004040c51720a02001130740000703540303200720b0341c10448184217500d1394103100c8080c0801c10815038001d800051180d0f80c2140c0c0031451a0540041c03088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549817787 1250 549816537 549816577
    0x150519031a090907081e100507090e0403020f06090a0c08012f0904090b010501020f0a12030b0303190e01090e19180f1113060b0301090b030316050102 66
    0x819000c448104000198a508092480419003400018181c100c0e80e00030071900d82e15507840300c15203804180c200e0720b0300e000074000510b0f00c3d400b020091080b4032a41000b042c001440d00c00d0f0006c14007601c51082007814500d20010070305040c001d000300550712012400f41c806919001030b010741e03a914408000c41d000c0d006140001200c0b80c041c4144612710408030360710f03d412042405600e00500307030200000e94009081080300a25074492241d49105071152020400c907602d058006420315143c100300c3c583c11b40280ca0b200300081d080c544c01400d019210f040003e201c00d4210301003031850080051580a545070079250f8500160811039a10100c03c090340e03608a46034032100d04464955050f103d400c41403460045040881000c1e81145da185090800500c0d00b24195481c0e0514523041c541050b602ca2500c808101e0a5042400c4140b41581c0c0550040c4a0b0078030b08440500d1510052040c4c01680380da40c490703014143d5090080350300b4400032054103101c0c503030a13081140c001d610006032609104e040b580 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549819037 1250 549817787 549817837
    0xe1201020301080d18230a050130061d010305071a040e0c09040212090f1f0b06090303340b04020f0a080d0804060b0105160312061505 59
    0x807a41641c010300041c2400c40300030102550100350355807200b075101303c02500125228002c90841c241003070700c56960201d00030a4400f44100c1d1046600140d04001a83c2c030b002c008a08a18401c0d18444000c07040d140d0f21089001d002030091100d0741016030140028080062041c000e0005141620f000b031040d100a1030361000003c0d83c4054004c604c00350f04034140b10400c0342030012078240b0740c805201b0280a1821810074001001c0764415004458543e6014081c014000020840501e100a8400044c41d00d0100380d02d80445420090040c180096100e1f091000a62142c1040d01e904000c040c00b16601c0b12140f0a140e4611241042030706402000e00801a40310f485075040b240249810248903415a1107940034000708580c8003a8883d001400e103a0700242e2140200078040d04003980f50b8900e600f501f00307031a180080d20b9008410b141002030500c00301c0c1c00d10001400021080d45c0c035081021345203d021040da03002e81450ba00c20244881040c01c0100d402c2c1d00000103041c03103d001c130700c44850780d540c580b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 549820143 1106 549819037 549819041
    0x9040612060b06041d06030c1221090607260f180f0603061c08031512150a09080903010501080106180b010c0f0303020c0d0e1201 57
    0x214800c0910005204100319070804403100c40c5010700d0030020a1202d004010542040115000803070925078040054100051000d4940b08458403405e11f41901c1d00300300c2c03018171704401352800c000154001d24002c80f004860300604007070504896494001180090f440459114421081d014480001140103002d01d02586020243d660780caa6110200c0340052014280c000d08503112425080d03903e010035030b0307070100d0195140c03030f0013640308040341100813400b110140c14018000144144951403219505148509540c0540038824428005550754001c3c012140384040301340115000c5617580d0004602c00d4054001e2a0800401500280c02c4880031f920110b65130795079040812104102254015a01e402d541042200001c0080080c1c64401480310050590742d03040888403c050190b0b050700e1004001c80c00704c0d41c0c0e14410380400360180310755482c482d00c1000c0c20400c1d581205014 = true := by decide +kernel

theorem cover : BRFrame.Cov 549640287 549820143 := by
  have h0 := BRFrame.cov_init 549640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 549640287 ≤ n) (h2 : n < 549820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
