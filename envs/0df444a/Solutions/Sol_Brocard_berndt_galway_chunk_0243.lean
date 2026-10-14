-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:42:03.530018+00:00
-- url     : https://prove2.me/submissions/de94bb94-2382-4ac8-a2a8-bfeb46cacf6b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 43525184 ≤ n < 43705040 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 43526434 1250 43525184 43525187
    0x402130e0d0309030201050a2c0115030803060f0103090b150a1802031506040303090303030203040602070b070c0501051f03030e06070c06020a110306060607031809050a0b040617030301050114040f1412010b01 91
    0x209c100c021101400c0008841161025000d0010b1244149400c1650b00b004000e04c802440114000d510840b22504500001c6006405440400d04007a01011074540007030800d5059180c00c22001000a2603210101e40312079500511040111200411603404400c001e019100765010303410703001084a100d800c280c6940da0080c400c140b2404001c04060300800030070200310207601a1140c88d540402c0c15111441c012030001c1090202c41301c103070707070542c2890041020010400318105070b0403041d00003041094115242a56070480390600d040d000241044110302145d20070310000003a04460b406011110b10604011395440b5089010502c44e80101c4140060b07a50340b60308994140d60f050903c00c8552501e92003a08450441d5885440c1c41c0d814503007049203050f050340c0482d00d9000112010440300383c94003240f4605103c0e006402025a008100500c003540c040c41004002c01000d102151074103803074000300e00580c1080e034401210740b018461307440361a24042260b100441d5440c0b000b0002c06030580300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 43527684 1250 43526434 43526471
    0xe040c030c18082802130b040b0a0f06050702010c02030703050703020a08030c0304150c0c0602010b120a080d18050118060c0503060307051203090409080301031205120402130e0d0309030201050a 85
    0x31450f00d14121380480700084d004007505504883d001040d101d4030a00484600c4068040d80000903c150728003500c20021340380014851086c2c8404e2000592098242070054074103038403d050a9051183c02c3c4950300040c0e60030405a8091351180001d13100386459481800501d8035550854101d030f400901107804416000801c2d201151403104055500e415001030070383c0c21483c3c080014040c05040d107800f00d06250150801c0030031000c1922448244460601031a80b03860300f1980c014282c072010460000c41d4480ea800480285c50072951901c420011a070760182103e241c42c0350003480140c0f00d00260203000c06071007400d200d42d82a0400c41d20391308c1e09400017611164039015041c4941c4004201682c040b808100740d03070b804940500f08011032540e0341040d8185400034801140e60104080300000628400c0c820b941000615089807182602c5983c2040705000c800240c0ca42c45540d200f01158204504002d541d81c003034555200020001001d00f402420745500504550510781495000d40401812a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 43528934 1250 43527684 43527703
    0x60b0d05030910050403150b030601090b0609190b0301060201050f0604020c0a02090a0618020421021003091b0e040201081014010507140a05150603010b0609040b010e040c030c1808 79
    0x3da00c1481040411015140c2e40155000078050550b8180144201c5c800740d884403510b100210304586003031b03130387c5c800d403006a84031031082ca81c00050a020140c824102281c50988140c2141e9100c850300e0345408038101c064009034488070050b0b440d4418400d00740382410440c0d0700247c055809500c0c02d0b03800602c603581e0b2626910000c1c010400500007032005c0250358000b40241c8001250005032108003040301c4040d4100f4041c402d08188140146040030790700125108680703501500e805c070b401001c60000c0e0010801c0070b50580781e26108016502c4514262400f01001d0a40c42c2480601401c09000050008400410a410204107641e003031200d46008100441c001409180c5596501c650b0b01c0d141c1e60040b60340c68041014451014000700b00030340070070080e0207070b1b6021480c05861b40c0e0b0402014243d4802d01c00030740d0015010170021034103040c00c2e0000d08403145c0c1814200c03042000350003c5422546641c04140000b40c1e11000c00e04c143d079109041c030710103e0002002502080c28030101d035841d544003d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 43530184 1250 43528934 43528939
    0x3050d0c0e0d080d0e030c0706090503240c19080103060b04060614130e0c030f0c13050402070602091e040f020c0607030203070c14031201060c0c0302060904090b04080403060b0d050309 81
    0x4518032002e13441e40d8001544041d10081a03e803190060031545d60f0f40e00c0c035805007602060703452601040509000400003103e407814440702c807501081c8490b000100002030042c9c0c032440001c20245c48003101d0034410b1070b400c0b0001d41e5062080d40c034508007513080b07640d00c000e80e5101d141480800c00150b030380802c03801145c0800119403035840b540b8205e0883c52401e282e21034070034100668104260081000003a5120b01c20040c640800e075a40c154403084a84034001c580c1824200d80c040a0000b800e02c0d50142512a10038400181742c440c619000510301c101c0d10b0030910550712880403204007402c05000b00e0030240b41001d030a50030302510495007611290f00822800c1010382c007000140046100c1d4601042090300301d0440c445c0708031450120b03900ca501c214401003041a030b8100000740b083c4185900108140c00050780c0496608503030800219611104826502540761300d9640c4c0840e0045000a0142c0c0c85010b20964032031440ca000345c283e030752088800e03104030b21406814002c51404000c0b1040350008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 43531434 1250 43530184 43530187
    0x30e010e010309151a0a0815060d050303090106091104050a0b03040206040f030819080106080a05180d0903020a061803110d060212070216050a06030b060f0703050d0c0e0d08 76
    0x1603a0040300100341600d8040c00002035008841420080b95100300c68820f0302e500000007034010305007404140d0400d032040d0703030150380140c0b001c1c1c202d171078411a415044000108541c0d1000040d496540c0303150402e8400c110113964a0304200900e001e40d02c00c1207034120164201c1410a4600070010b03c001d001072045240c1e4410010001c0e00715540d02044034090440011020b1403261641404401a005685285800c00e90f412060342c416005810050407075070540e07605400d03a500c0c0300c0040090140a480140101103625100c00d1540301801a40e546171340c20341e159600c0030b1840c010042d41c040941e000c41c0900502c6400810b000e04a150903e00762904280200c50002f2040081017804a00b200302070682c500c007148801c0c440ca580c001144c05001c0d01d03821a110000040b0503468031a04511825a120410400c1000881e0003074010001d06840109141d0414540310325100290740300b0384089001610010701a840c0c03855600c5042400d2240f03207440b07009641600089050081e0079000a00321020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 43532684 1250 43531434 43531457
    0x1a060306040f06031a010504090c0b0c10050106050d1a0303091012020a050921031c1b020f070602010e0c01120209040608060603010612080702010305040302190809090106020109030e01 81
    0x22a5041111040d03880402003001551303c2c00c0650310b00b1541420b0000449507980001401d107044d00408443e640c011450300c84082c5040040c403026406150720038120700900100030a0043e56114240c000c200548809503183c020b8040349045a000766526840300c8000c4040c034816031000405d40e446240b090300c41c0300c910760760b0b4030f41503500c2e421004040c4100340c0000783d40b6000580c040302624504c50252240e254000f0b00303200203140f0740d04c40b42c9581c003154820f100d4541a200c140d02d88880c10407040e0310008003150400c1140e06414801e11f8007401681c42200c21184117a000c201d408010141e51001708801002c15185549a0101e400f140e410440ea45101050380592a811a100380000500030040c3c4da03594080c0d503444440899645110f03510707010002070b2803060701e480102501d0340f01a50074501010f9070f00550050402130810740c1144504100383c107030109100d00030f210a40c0075840881d11010180204100c56005030050421079041980440010742c20200c0d222000609080061900e003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 43533934 1250 43532684 43532689
    0x10f03020909031306030c030e0a0b04030516020406030807020306010f030c051905120115060c0305030420030f0303060301150e0411040b061605070501050403080a050d0f050f060f01031a060306 85
    0x520280e80c0c5402000c0200040c45d9074040e4454000441340f9241400360f401c040703265980300d2090f0107000d01281c080702d0010340024400c20040908500101843c00c0c02d00171500890100c0340c0b103030005c640400d000507008003546010030025005007c006d100d43c074414150350b140161602d0a00c01d86029032440c01d080191526822004401391001821000540e0781c03a0180700d01034071810f000340307030700442240020541c0c5101b901d44404940c0c01d512554079640b00d5035103910300034041c46001c0d081941c0c6076000c4817290740c0a01010b130f41d56030b44600550300d0307040850805084600151003440f1010310356104000c00c40c0000c120705c1d400758020315101070144211001c5405003804103141c5600c14000100b018180e0035004082c2c08980c02440ac0f6080d0319254001035138140700ba030001a26030f100500c000b400e254402c00040400d1515070902068110410b40341506444064802e0000b0980042c10000e050401d000b62401e8584240303010310100f000c01451040d07100081c521303036004810000000f400343c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 43535184 1250 43533934 43533937
    0x4050f010e07090605060f1c14090d031b02070b0c01020f03010e01030b220f020103091e1109060d1b03150b0306160504060f0207030803010e10080c03060a0203060f0a060e0f0102010203010f0302090903 88
    0x1d803192700c1e425a941c0740950103030703481d07006800c4801d000c40d1500914412101c4000310700c401020841d00103040b0310b8280b0601b10104d400caa00c00320f05540d020804400205036082c0518000c044409039910154150314054001e45d5000701241e0b00a00912950501c100340e2060301c0d0034594004060316861540f500040703000c1d00e01224060700c2100b064000409000d100b0101d6813010380241003612110f02514200026603400395030f41640088c060141d01c01280d04840411103102400d0000341d01c0766500c0d502c1119041540124648080d621032a103552410140031944d840741502e0743c0c6491094000750003034101e00a601404081043d40720748150840d00070130054000d15040024143c9941c1e5030702960725000c00849020340c41611034500082c0302038000404405114006015043d140d660f003011030000e420050a5507401210b071888040c5907190b950314035000d00700b160390b45101c010841c41404200c01d480c018041c116841003004000c0010380c4c04000050b80e9044440410546449030b016103035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 43536434 1250 43535184 43535201
    0xf01110406051b0d02160905090a03140c0703062a0804060513081209011107080f1309020a0c0519020d0206070305070804090501050102070509070f0804050f010e07090605060f1c 78
    0x3d4491140a406119000030f41c032220720b4003100da00d20f00c5945504091040e10f00503110782d1416400b076580080000d001c0e469050304000000b981609000c1c6910b44146814a07541c1b0a48031150341c0d50411011402402a101d5411068040820800340b90722000704070400061020340550f642d000414808203246404010454105030340680f201501c1015000401007520030b50490762806881a026a803c1c2c001d56aa882c0c03c102414240a605420b01c18268807d00400c200880f001c040842d1b50071140c0b02a24880010790380d012081031081c07a00c20300d4034681400c0709001120340407103040165140305c0003030f81883d419102180c49509a240a603448c0c01620b2000308408004940454003294961005040b2030003607003216141c0d69920184086004140d07101c0000488100850050074010f11102c0e4005106500b01d807610225601c49600310792012003e080260001141040040514040d02e00035001c2250380514000c00c0036481080c51040c10005000c03480d903030001d40074943c0075501820300f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 43537684 1250 43536434 43536487
    0xc0c0a0321020d06091505030a06020a0306240905010216290301030506040521030f10030501020d0f05091209150403050601031a07020606090105190306020c01060501020f0111040605 80
    0x4a511102d18030001521540c09450100392405240980c6d03402d07040c00700b0b01101d41c00381c060080340806841d02c001070b6202001380f006143d191000007402c0150442414005c410114051b00b043c11140c0c8001c20032409507120604640c030621070840388481046a03942150386420300d14110305908011007401d0a030303a0034400c501d0364001c0700010a20a02040c0b0f1842184204107841c883c41c0101d02e1001032460f87e20714071032188414400991a4501001c074290031850030f030032004105549070385190070799006544903523040e07403034614004041e4183e010303040c0c00041007005403030a0681450810054020312040d58070545c0c603c603010300040c030002c0803100030b980c010065603440d686130300700080b0f18103d0f20745100607030050780002040280301050042c0035140080c0400002d910349020481c8440c2c609445440e0404100c03030000008095100401c1d580c841c0c1e00c00403620390315040004e81046a42101040240d0411a00d1905000010100c505450103424441c0e100d0500c1d113404204602035084000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 43538934 1250 43537684 43537687
    0x3060106020703140d12050a09020d050706030b06040503030315130c030515010e0307030b060112090f11010801031a0c040504020c1f0204230f090f04030201050c0c0a032102 76
    0xa05a81c08124501943d018020490f2802c05900d0090750b1200401000c90000e8821480322111640c0c07500041d801000309a004074000341c69800040b9403101c0040229416441983c0030001103425004401036500102c0b034080c00d1925201c00f0984070f103c02403294503102070110140340141d5907500c0000211500d42d00170400b2120042d4058000d00c016034000d040080064050030f010340c4134000030100c000b00070f0003401940d8a0355644060705800a0900d070306000403d100158280c0c200d1090028140c0a443c0708c04203007549003040d404001b04076030002c0c100041c0c0c5c00140701260140d0081102e80d5a0704c108421286d0365074010801034060341e0403866000340000313662000031100040b484811a04030361103072076059108200a08921462003403080c040c4212840d500b003040500494000001702402d41500030740c40300006000c68404a850710035840041040c04185a030901c40c1d5940901ca1819003864039207085401652184240c0c0024200003450b181000b50345403255081e0200501c901e82075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43540184 1250 43538934 43538939
    0x60a0b09060405091c05070b13080912190803010302091302060403030e0a0302120f06070f0c0305070204060b070c0806070203040317071502030c091807230705030301120302010e0703050303070f0905030601 90
    0x10502c0d4080707d0241c920003801030102c2c054045050750320800f1a0300c481414603204051040c8019410320006000b018040c091950904150702108403c3e01172060b450217560f9811441042135240700a051442503150310130300310f001030719a20122815660181022190100084009000070019030030082d0040e00300521040c500318002042500e1103070300d4080d80c486550b69041103030340c000c0e44150100040c003203001c1000840d000f20300811341c441c00a44041219911009011980c1c0d21001003155030000c401c00820031034034240183c0e5003210a0b4405149010310315110310500100c624100b445902c000a0360300204250040b11040041c0d80c040700755204e10301148000001e4101c1c4244074001d000c0b9810300c0103840000408544144140d40780e80d84505100c07994980c0c2020095107400c50203504010600c0811001c201440c0284111041c282c140303141468000e0a6690144000300554010780e0f0034000200040103a035071204c024a84014038140101d0104c03061109a84640c0c1c041c000d20001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43541434 1250 43540184 43540187
    0x33030d0801060813020a090c0302040923070503041502031504050103050106142b0503070b01150e041803030c03060f1706010e010608040215090301050a0e060a0b09060405091c 77
    0x55040ba210782d20b60308071540e11003004803c0b2003980400254840d0b0304003004e001c0041690f008991068440c5801800c050303e0740f00301411a08510f81124000d01c0d21000e058608000c1849079500136803030300e4010704500340b9590b840c042c006c20034090b2107155008400078042801400821912103402042071109507036038180280200300a000e007031000c1c3e418064280c2d20b8240007032842400c40310032024254540c0181c0d4100e400e50201c0c18101d505000400c05040800c16410140d4041c14400c02c200e01c9518010901400c000105503c0328040ca0500807248101c042984240044940508008c00c0c2c6028103042100106000d412686500c01489400b19441a001c0c8507065810024402c0b21000d03600e41e2056002441d0034422400044c09020024005003809010341550641c017001d000e0411035039400013400d461003252800b400d1607881c0d00001401d0010002140c000d1410481000211480f5000c00c00c446030043c42d0500498031031002c100c840c2407c0007110809200d00415200c0205c00300e40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43542684 1250 43541434 43541447
    0xf1a010303030c031109041d030a020706120b240c0a050307060f0212010b09030115170c091017100c0f08010504050c03040615050307060507020102010608010533030d 73
    0x100741c000900c0c003d00840182d000e0b12a14511301043c2941a05100390030007007001400b511201c48500f00b90000d00c2c0c000c41d16040014150f0a0101c1d0040d0645a00f003130001460704c4516024081c069080c00200c58280d00d4143d9551042c010349a4000d500b40c603083d0b180b60031841641c071841c116100701c445010500601201500c40e0764812101440754101d01e203900c0c4143c2c000ca00454501e51010b000411107008405d004040e01d40b006800070684291110002c40742c2292641301001d1614003103a5a460b806052040f40f036050002c0b241d000d6582411094610307031a5483c0a04003060b6030b6a9103181c90140204105d0580701041034040c40030b251119001080710380c5482c10314021030054400400c2500d003030b009403480b407821403213060b05694650b1075150103040080105801544055008522900c0038419140078140c2501c905a840260b403000901312071003a4058102a450082480b03410b1003503000c1c840c01502d107040ca00c91174070b51303c081c0020601e031030515003903040c072030300c804c0e0b8030348681000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43543934 1250 43542684 43542689
    0xc0a120302120a0209100c06110d0b01020c0307030b0a020c0a0f2d0506070c020d0507030302060108070605090d12050d1401170309030a080c0109080d021306020f100203040f1a01 78
    0xd82d00d0126180c00c80740d2000d0340a04d2045583c00190040e00c00d2a16214214a01d030300e6001d0200814400040c520059440c0d01248040c21010b44822182e00039580401c210140301070103500424005145854901020801502400c803c3d500000c0e0484500810030031302c2d40682d048025194150900d243c00c1690700c40c5a0340c038a02c00600c0e4a01881c25200c0c0c0208049110f41110140c403042d40c44200c2202e031044441c10499009043c403400801040081021001851080e00181002d5060090940c50061103501908c10048200f02c5607203030340c580c1442c0300706039a480002038001420f8600700b6941c501610b402d1504441c1380c10760502d913218804a110b41218611258a04c02000091020b40c1300d124595030740342c1517071124140100003558103005210701e03400c41c0000103c090302c50342e43c0242036103d2591244000d40100700070f545280303e0601d04c0000c003032900041c00d00503040e00f811034941394001350f000075595000c40018188521a90359004140e403007003d13a00b048601101500d0245002e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43545184 1250 43543934 43543957
    0x1020d02040503010606090e0c0f0c1b0909010b0a050609040207051504030306090504030c1b0807080102030612060702070303030519110a0201060504020a050d0b0d0203031201090c080112080c0a120302 88
    0x4240003d050b07007d06424800d4641c0c08e514680d0555503800c0d25420360340201c0113a442d000c0104810b285130182401900380c006c405103400508c4c1d511034400c02c40c50f10005081d516140e4541501810300d036031003840c1c0d08100c4d1419640b00342c0b03841c58500068028026032030060054025000c0f4080c0ca10000c1280c24441e6209840c10411075440301c20281c1101c004440c020007103520b010001d070228555540c2046100131310f46501c50032f161143c1c032490400304da6510004007690040140110341c0307404e44202ca0301c9508880201540e25052000954411841c0f20150900d680c0d030300410042d100220305041c42104038002400003c11603104580154440c4603401c2c015482c0000104480c0b0f0140216813035000155035480c01d20b4442d404000090104207021a403001c0864150f03401600c0503c051700300201e2026840c54550724012031802540d40814070281000507001c01409640407040346201007940100b00e22741c0304c0000c108420704d81000f900001e008948210410921958160014541815a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43546434 1250 43545184 43545191
    0x5010e1501060302070b13210e18040b010b0703030b030a0b0708071d130905010501030614010b0703020a030e0f03070f090b03010204080a03180902190306080606030a0b150301020d0204050301 84
    0x2d52030308900702e00450400512200c07416000c250f4114603800b9a0646c00e01400740c0d100c600b15101417100319160010940b00c0404c882001c0300a0504d4002061042d803803440080c40f82c07600d801c0d07684c1002c280c014051460010004a0b854050600c00e900c84c0740984405021142201d40b5810300b041c1200044070444001240000002c0c00c092107202c0802c481e01c02d081c19000e00c0c03800d0000304400b407040c2101032541907558403c0030003c01d20900031725000714000d000c00901003042c01b40f0003403031a038141c01c1074030701032010002c01c1d0009600041104029425240c003062210040300000c0f8413440c04514140e040c460700901285852101045c002181d0604004205106481082c1401d030300852003000c031584c000202e09808030740209160410109000c2002d00f605460b0314040040380c1210541181444413426021400d681521800c1c020342910360041040d8501400021360341c40895400518030050a4045840c81e00240030349402c00c40002d00070b54030b40c03d074101d440380250080c1c80764031321035800d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43547684 1250 43546434 43546439
    0x20301050f030114160203131503141003020108040f0212010e071a0702060a05040806010306060326030a0b13090f050105010506040b04090c0e150307170c040501081305010e1501 78
    0x103052180040d215942610301c002e139528000e178003030144c420072480c0302135010404c04203a4520400214101404e01045034541c031002c0020b0080271900340124041e1380303207003c7c0b003440095800c1420400c1200c1d8246820701543c1d580e4545900002c40e11315000f50081914001c021409106400c81c0d40f058807690122030000b07507140204005448540681d02c4040030401c0810054101040102103400d01400e03c60301c0c250381d5800203460300800740d100341d40c40d641d51032050003040310f0411010040180303042d10710f2010011100607592440007910700e514a694600d018810754940f2111000301c800c07008030030001c540311030414240c243c502d22012a42940390070004101441c040301540e0546052010650402e03003800d8401d4010700d105610041808040c03120200c51703a4030b0010001807034001020b040e4503400c08c024064840c1c0c0c410403000740c3c1d02c0c0309181000740041450f01502e04541092a200d24241c948036065a0505c60100f0041c4c4594281030701a4031038880058844e46070b020a03260945107070ba = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43548934 1250 43547684 43547689
    0x709020708030601031a1e04090b0702030d0c08012402120d0b03150c090108130507030309030605070806010e0d170c0a14030c07050103050403020c030601060e0a0b070b01090903050d0e01020301050f 87
    0x706e0051074130381d11030011022280c0440e1042c0070320a0020b030262002402102c0780c0c848810030b80302150b24500581c00002c990a5603031080c0101c01e40c0000340c1c1849051035060040d501841c41d01030403003080b000c0c00b10380c280007010310800644001054000f902071392822443d91034400b518400100c18000d12405040101c020700c0f12101e1780c45209410101c40c01c08039003400440d0404e10203052184070510084950010503014010800214426160211100d1861038400e0542d28010302d40e400344105081004150b0340c001d00b680c100c041c4100c031030a8610704c40c0d2405028114080d408820810000714144810020026940480c2070003911a4840703135142600080e5280700c0e466282000f50080c410411283d4060f80149401c41d22a005079261080c0780d802003480c0c11004d034480400500100b0800441c0d050001c1524007600000f034070036241c12031b41d40714001110010300c103110b021503030f030764424060600c244140c0b00c08800c00003003404403000703814007030307020f50020301580d4860344128041c04500e1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43550184 1250 43548934 43548971
    0x102010e0303060f06030402031c02060708220b0a020c0703080901030b031f150b0304050604030305060307050312090105131202100503040f020409110a0905040b0c07031d03070902070803060103 85
    0x3c50009040c2c40c0b4149500c404c1c0040c44d08044d02c201e8043c82000f00301c40b1080c21400c100c8103101c100354018482c5161451000700541c1d00900301400504a0303400b150f11020b0611011005503422908680003130f16001207400091140007e000c0450207020004010440c051004228080b0243d9060000070b161a0825841c1e19428103d0414410382240401c10640c00750400030300c00001f10b451000c0c1c9580c7d414400d5040d8001c460484880d00030008000030550944540360b0010400d80042c0b00c0c3c141000082030755a45000484c3c140311074081003409030b0360b00c113070101c500d04800b407500000140c4c2d58000d20604448080c0c8200d1040c9007012400010f148550b0960384100d4200e08800b0079a10580c007400b0040207400d4007501c04148000310241162103071080840203040049000441d85418103110880c81d034043c140142c1c2c2c490412500021981c0300c91010340102000d8415205194110700080c9040e03d40c2d4005280103002080394410b100300c24000c1c61180c0343c00e032018401c3d00c2845c1c00a4814 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43551434 1250 43550184 43550191
    0xd110a0503041104090f030c051006120311070f0305070303020c0105030403050d18060e0f070b090105190c06060308030601020d0306050901090c030b18041205070203060c0702010522050102010e0303 87
    0x48050000501051252115104100001d04001191602510390740b12181c0446c03c00d4020032801c51a00782001020403ca81d800b03a00104200015401d010030b46a0840310340d01c0103002c00a00c0902c04941c0c0005026000c02844c1110101c60343d580e90780b0f070440d1902683c1c881500903020300a0a41c01035400b407005c0b00c0c8140c3d410b64070b92b881c040b0004075980042c09680c401882022030071195100090385486a9001a9100c1c4000d1040c1c071004000340e8034095454220740d450326000c3c014192642d8002c003d440540102c0c01c2e51400c0e21903200800c4400400342007000d4600d5007000b2000003401714400c000c50003150f080c0c2c00d480302c000340b40d80242d044da409440b03815000b110410040108100c1070344000c0040c20289800b2a915562000090026561413090302456850f0030900c401c1104507a0201090205403c0150500c0081c0e00000e0311204010031421103000000764440843e80f0501c11980f44100e07003103120107000340c83c07054400d80420130700816000d0340c6041c030610041c1703030f0000c1034a10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43552684 1250 43551434 43551437
    0x6090a021f0201020d090804050a06090f09231003020f0f0109061b0515151203070b0403030b030607090503071e09020703030b060d05100f1d0c0d110d110a 68
    0x24122100750344400300e414902000c1045550a10081c003120015006107610140a44a8036480d64285400c02c0212161030380003805101c00c0040030020314010303841d032104a51400c200000d02002c06c659290050103002032683c1d09142560800a203180448000b8042c0e038029507800050441210500040e140c042c164903000c18920041003212500c80e165100b10302c102402c1c0b4040030300155032100d20744100c080d544c5d488180c1c440c04000100503006404008102c040710088007100c0713034000c01d41c1c49104000019101c910001c000500f418041d42024040040160440d05c42d4508820000c0400c111801114030a020740705000541c0380b0309070309402c0684070056864421a103032206c1c1c50001d5000c030908905058580360401e8203655040080c0064000480012030380740342c84c452491030030310a50060002c5580d800000e01154018089050110900d56543c0c1d0080c0caa5000d8400513000348100000d40504210301d0590360088000030b00343c0018030350810700c282c00d10403011300150b0088154200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43553934 1250 43552684 43552699
    0x150907080411041b11010c0c02010c0305091804140124050d1b030803010f05031b010f2003040518090a030807031113050f0a03030f0c050c03060a0e06090a02 69
    0x6021414002c141100d29030000c0c8001348803020300d40f403014102da070704050b030340810350008484203071807801e0049084050711480d01c2e540340300c0d4135400078190b404141c40c003504209001c01c1680590b11004008028800f028410302924039161420720043c0006480203060382d420540b840c204d400e101c4041d07410b001e90607000e9409980c00c5c10140324444600940699291720001500c4d21440c18213120030000d58028504180d4175814a444520100f595a00840c0260702c0008002c8840300315108402d00c106013480d1001c9002c8400d0001c84d0540c03245c0b44a0b0146180c0e90303040e0340b03c0c210000000c10131140c0940f0008071005412190040e02d06045405402607003010f000000081e2040e016903912030140c1c01c0000d950070000c2103d20301c0c1d400603135000d80807540490741800180703446084507400000407950351581c1c0703082d030342d00030003600840d102c44c0c09128421515404002040c410a07402640c0602111306914000400b000a80490008046c003405a40c1c049990404003091003c001a0043c0c00c0e032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43555184 1250 43553934 43553941
    0x612060b010c020f120102071505040203060c1309020306030c03010606030204060f081006030e0a062903060907050f0a0e09010c090f0b0f090d05010c02060402030f0718090203030702031515090708 86
    0xc400c45d21410340d09402075500700051000110010350031482041c5549002403549081c0c410f01d85072400c050b00130454444140800c890002d401181501603408407200540c0340e441d81c0740400d00e40845074031010f40c154201440801c0680d45980500102e5540340d80e84c0b40000e1014070151070b00281668900740340091018107108042c001c0d04000030b00a400d60487e0f0700920349840d141d00704c031580105460004c0c4580c0101c90415070045600074281021805070035181030803006240d4604040c8121401060000342c0540aa5100c0e8180c4008040796407001540d49021540b03540242501c18039a8041180c401d800701d00c00300c180341030700b0640d0f0700001002c0c07400d041d00f045840f0703942000c4002030380801503401e6040010404c1c00340c0b02da0f001c1c454000348003c1c2054410142010b080c000480725603404584100034040d090140481c480614040020300e0002d1800030070309610401034081d400d0f00c1140000c4280004d40d13902c031846128032250b2517241e40241809c012081009480c0c00c4000b0b0a0b82010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43556434 1250 43555184 43555189
    0x1050403020d020f19060f0e09070807050f120a06060306080607050706090f03030903030b06090d0b090a0c080616020a080703030203090a06180605060d0507120302030405040612060b010c020f 84
    0x303900d0004100498031904107000501724000581e0300798a41c2900c5800708051604800c1341d82d81d03054142840c0038100075003404203450280040c80d90702041180400b04011034041c100b1510504118036649550b914072480242e5144002c0c0c81d0558030710700c1c20100080152007845503001341c44610000d80180e445080040300c0300e07000000700340c44655580c0080d10004124403400003106100c1c0d240482d56400d1420054100c50700b2034001800b0303070000c01440060fa80c4556000c101c0070b03440142c009860f00c55190035890201c00c0e0200510140d812500890403800c0020002e2162403003000072050490316840c103d07180d1010010041c00d9100610072200003d0280c0c01031540401c103503080340d404090766217482060fa0107000020f00c015104885c00d8050014a020b82984040152803142c41d00c03002e503603095540c05c5079200d6211910030051008041501c06d104540080c60024002d0100b192607903440c0300b46959000c42182c0c250300e85280310016502400c00180000e800610701200c24211206 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43557684 1250 43556434 43556449
    0x50708060106020d35061305101811070309081011090609010e0406060503071106010315020304080c010501030b01090e160b0c0f1516020303010308030a0b0a03080c0105160e0105040302 81
    0x1c80320b051540d1081c0b038900d07403c1740c030101e0f0510540e40004003416003404002d0146140030f00c2280d2640d10300301070800c002040f0b50381c0040220340c610001184528448009140280a0b000040b1140b80c1e000039100e0a15501030004000e4800800c241e844c01401d01761201d0440d6150319031307510402e03c203001401213460040041c0036944010b05280341510781d0107002804441d842d0b04108013080c03021003800001d55100060b400c0700c4091400801d0030713505684a0000d900100294503012030340000005042141200650360103100c0360b0020301c443d5860f86407810b00300300c0901400780c0f424508110201860030015400c407101c02c80b850701d0b610541c10581200c000d40e108405440c52840703203409061a001040010602d017840815403a94a410040d400510308a015408802151300a20062010401640440c1d03005400e288000404079005c0c0302040c001d14017a40003034250840410900400001904041d00c1500c4000d44150103440e45003080d503420348050302d240d0000d0410712003072006007407080c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43558934 1250 43557684 43557707
    0xc01030902180405070806010b040302010c020d0201030207140c181302190b0a090305070b03041e050a1202060601030c0305130b091002070503250b0604020306010c0501020a0903050708060106020d 86
    0x1091541290504082c0481111054030704458560203001d0402510100b40134150140802215081c5001e01d5030f00001c207200e00b0f4410103840f402d40002c14004680c02681101c403a554800304050b8501c041c1c3c1442a1202c03800d520890040070500a81042d8a1681c6c0010b80328004586c12000410015000e200c1030764410200200325080405d004078945a01001030700c0d510325a13135524494941107160460070050207600148040d41d051043c840001e10030a0380342e841c0e803881c91282a1906e25230600c1e500d0192091006005040f6042d80c0b0700c1642c1d404500c1c2840b60100b07883c280902e50074035000f00d04860003120b0060f540e07481c040030b06002508040085801065140c122000c659011094108984c03020a040300d056000141d03810120540040645600b1305240051340c400442e0344441b059103030b00400c40f91045034000700141a40e80074000c400ba41641040085403036107816500900140c03506d000c01e81d1144212180000c0c0205c002036118140e44c0b10394098803a0203015107043d11603e2000c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43560184 1250 43558934 43558939
    0x20907030c031119090506030c0f070f0803010e0a0e060609060d050c19050109060e06090f030a0c03060614060f07080a0c0807061d0307020d110f0d110f030303090c01030902 76
    0x30200c08404444002c044c09102e46003c000401150340f00c800503209158035401503009101c14001c0081c0e84401c082555084586248080d5940c0540e00d440307502c10b90340c0f550040050700040000300d40040c404038500c3c03080118500401c02c4e800c2942085a98070411a209a03000210600041c042c0c02c1408171041d0302d520540886151408000000710319a0581d00c2135060300441c0c41003000b85603030116280004120904205900001d20008034055203d01203c090049400306514409500d04001d40010182c01c008400720315034980c504100540f066110f0003000c2204a9043c1c2400d103008412210041044a411442c2015990710b005480e005003018030140251b405018000c240000c1c0102079413071141200140210448503401d003000070703c90744a40341d135005200100058036050600d86200d034100d00d203c96150039180009445001c42c4c1d4149812500c0c02800301e04202411642c0d0b44c5142003160072251502001c0d0605540e03010455411140303601a10301900c0d594002d50000f071360355002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43561434 1250 43560184 43560191
    0x60512060721060312081303090b07020d05010509010902150406021011090a09020a02010c0306051c0c090c1101050f100b0a0504050d030e0f09010810050c0d090302030705010c030207020907030c03 86
    0x1c0e51003280480d050b0b43d1068905c480309004426025078040d5246503c00d0000c0c412100310307000b545008001901d0f40c001c4141e211800640c68040d0b642e04803001c00015070040086c01545866801540607013a012000c03809401c84020800310031500c4420340e000d4034169070040c500c00481c0300d034000103081d00a103410740b244d8081100c00e04c0c6845080c2c40301c2c0980700d005409a500c4900001c02821a844a4120001c05181040c244081c0e590110b00f008050001c1071103401120381424407200b96019070340682a0741c0e1600d41d43d101c88940080008410340c0c40e1200070050380e0340b0781c031030704c030814808a42420418007100b07414441c5508a50151244101600c0c0a50409403035001096416000b20f0040e004a041100343ea0900d15001d0340d0461010717020f54507100a540340002c01582e854170f035074804102e01d4883c000030b4880801841515104407588c1000d11203000c04d4100691a40d02260003581c40794202110700c0c40c103078042e00843c1e19080d40600320031426612100704500900964034254100b544 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43562684 1250 43561434 43561487
    0x7020d050319110a0e03060c04030f020301061518140306040201050f070b010e01080c04061a0c0a02060f1b01020414040506030a02040609020a030b0f0306040b131205040501030605120607 82
    0xb110700c1101c007080c030b0051900e0b90300c03095040040c02848520300814803d0340031130200015202403006403411aa48111101c040c81c00b20710009000d03140c6030f000101124000d40c01c11781c00c213a000c1c2ca89d515140c3c241186420058551040001034201c40c00c0d801e0700355006074085001544644010f010000041008070b00f4400b00395076a4800010a07032141c000c1c1200c440060021100c140300c19840084201c130100499032500a0074106624608803e8040920201e1074a84070101880381c0604070f50300400595407122090f840390200e8110110b090f0351070918404c5841103090510031a825105a664a03140c108034141c01c000c05840b0050880e50940035200c00c81c00180c65a015020140403030160241c0c642c3c00302540242190000700c400b6210380c00c0300c003150b170698401107044d50300650001e41060b15541c034500701c0c61501d0703401c2100500b1403441048080c9402e13481409041502c600b45d8084c8900e036034550800160300310303029900c0e80c00d0300320b18003198a0900800365004007403000d0780700b20103001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43563934 1250 43562684 43562731
    0xd03140301080303011505070510050604060503011407080919060c0311030702150604060e01030f0305040e090a0203070512030a0806130903031a1206040b040602070804080d0e0907020d0503 83
    0x8100ba030001d40300e0350011005105100c2e0702e80f0b40c0d441c0481c0e103242483c100003494541543d0740c2c10124042c00056520b80c0031601d19101c0b908964081c10000c1c0090084401c00f49601c58825412204140000c142002058a1400c0400d928001d00c5039168106103004040d1a910f0083c4003c054040500d039440002c240d2503580000910f1040616070090000c20702500c3d0070141c130a40040c0a68491894034030140b0000c1480b00d60705065a030090340c18901c01c42e262805440c1c610841d004206032007032070002c1001c7c0c800b000503007440b198400d03800e4036600e9503039005210030b4541600700c08517a41c20a1002c1d90200d8428140150700500080110130b0380d418a041d01c0c1d0444001050560000ba01d0300103502500d440301052140464080d45c2000c0710030440c030541d5403500c0707025000a02c4854858007242c188003990301600e003280d40180e07040e546c41c1d580304000c1c0d980e9984984090042080300401403001c2c946103030568071940442c4c02400c80259420800c4403141c2c402007109101d201c0d50b100380c00703665 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43565184 1250 43563934 43563937
    0x9180d05130306110c0105010602010b01050d0e030d0501032001030b091324090b10060507080a02070b030a060e0a27020a03120f02160b0d0504150e0607030b06030103110d0314 77
    0x104d400990b41ca17500d080200d0001d00f9150145c11090944e030400c805202d4990703004007101c2d5000ea2018000580202c4400c4140c11031290400101a0508100001c014880d0280b60081c041c0c0c1d5481400c107510ba04500154140c88020103000d51054900002440e0254100014028107102d0114210941c5103901d072407a481080f6001c44107420b64452079042040000038100b07401030701a802e515880c5181c2000180300f4820940010b01c074500104999034014000c001420180c102c2002c038940f2850307c200c0311401420345204a4880d14070440108040201d14405c1c881007a040701416421113804040800303c0402d6081c049800420307902c00000400d12410307000142c1d401c59969403224510003d002442c0c000d01a440d2090120820002c000c0c00040e4400c407001e54405541c003041d03d035103908000c1c504405030f5030070340301c2e0505101205851100109100344107051a440c2004a00c84120602c03801e8002404006c0040340c07142d0041002e03150088002c2070b0103109141600000c056141000c200703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43566434 1250 43565184 43565201
    0x30402030118060509070e100605131208091003090f1101020708010207060501050103050708070f030f0e19060609090b180f03070605070206010b030c09041d07030507030209180d05130306 82
    0x890307a4034024440e010360b040c40006d004052200a01c00c1c2070800060185800341c2d244550000c0c410001008409203201c4e4500c80010000796400c1c03070800966041130903907988200384940c841c540400c40540c02d03500a2080c0341c2202c0e00a1807a242d0310800740c1d202c3c030100c1201d00740300e419846540000100c0c0302090000304401440350b1000304035075140100160603030b00060029000d000c840c40412144a81c44452100013601da4a0082404503079480080d0042410324502c000600407924620300454080000c3c4a44d80d1181600b044000d548400344400c80c2d00c0d101c0300500746580d1002007020040d0310342c4e1803502c040044040c0c07121a10121112440c5910503a41202c01984460402c070595406204042c01483d8149440d8518580401011294031031030207880e00c41d542e03402a08900c2c056926250500d50036410440740c9132a140e0402d181c0d40c40c1c840c4012071281d54508000b86089a6a802a41162041400801202090781400d0340d40d40c110a1540041c100c0e4044000049802402003500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43567684 1250 43566434 43566443
    0x8031e13140a050307050105030a05043801060201020c0307080906040f1d0109021305120c0604090f0b030a030c0308040311030703030c1706090c0a020f03030108160905010b0f030402030118 83
    0x10058510002d111144400f40c2c0214481e4000d21010071403640c111040340d52102c2d04d0170b00060703c0d5440f442c0c030f44a06010029110708030141d06000300d29030034a40c509200000344100c030043c0140c0e683d00049091748142c100308403041e003060009000103072091000d8111000c00030801c9007030a4540c002c0882c0383c50f003a03104000c425400203d494002c1d2603444020f0140000080c20351900e880c118011414101c030b031203114090f2101d0440f068030381c14140f040081d800301c002c0002b55965a07601d0300001070201c1559044a891400c2c0c10b03250325140c0000c2c400ca103507a040c0c0315462808000c1e1001d5441480091003a014441d10406100401c801400140b1070144a5200024440400400201000c1d203030b07034134115582d4044040c0103c03562040f140f00d50010114400507659507002d08200d003800f41c42000d407112840b000c030021882e4034002c00e0341c455690b15801d6800c540d5a44850f00e10980c5c40a20030070900030420442c103c0800c044200440d03000340050b001048003441c1c40c0e03014203c03480000382601c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43568934 1250 43567684 43567709
    0x1a0913020406080a02040e010e0a18060b03010b0102070510080c0d020c010c0906180e0a0b090109061505070c05090403030b03060f0105010801080c0a120c1a030f010f08031e13 77
    0x480e0700302007919013102c5410400c50501d41454000129160180903984a404038000014141c00f180d800c10440e4050419079201e12100b2403600e000a849807a000714401e50801802c40c0c21035100040b11310854000400a034800c01500200b55040c000c041c240e6100400d0410545225040500042c01201600c00000034011501c40000b40b04416940015040044485078070405105040d0800107646000c0700d0040e0070b072626810f860040c803504800940100313108000190b00c90703031a0b00041c11904a01030b44110b040071000c08460b0f070710880c1c2d0300401c0015026000d1256081036011298803621074200000c020701c40c140000d107414000c4902d62440f54807000103000075640aa1103030300401c0d4040040919516810001c0c0c5003031040d00440304401900f0244100780400000322070028951075401034070038400c078540d8039081d030300c120384644002c3e03252030000809500c020440320891b071941c1d01441c01d003036591804098007890080c8064030700e24140039044c480100d4544000040048480c1d01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43570184 1250 43568934 43568939
    0xc030618011206050c0306130b0415030b0109050601030c080703050402010c02040501090c030b0303090319111504140d020a0b0714011109150306091f03050a060212100305071a09130204 81
    0x3002d03200000c000004605040c1b050112540b9030790b10407405911111000300d01420098003140c000c2580300c0c518000071040c1000003080c46182c040d0326050b0b4403040014010340c1d4070103005406480e200c3d000400080c07091000100c0300e034030070b501103a0442c1c414035041241000f140c001406503682038201000b41661071a021140c540c0511588442c0b603025009141410701880000b5111925107183d0069040e0299040042240ca0050840105001030024081d59001da2070703031040c1e40007070140c0c031a42512a0705500b458600201c4c101a21a07008100c64661410014011103a4000d410210741c4242c48852015a62000f0700852600340c8111b600c261319200100300300011044400f02c0150b44400401c20310400b40c49011032207038055041110180b0910342c0c043c00007074100e02944042c09a003e40070b11041040b48a40040074440c42c110640713a01500c42c083d400c0000384c45448010207a60040c0810085078610300c008809880614503040d08181d0b084c0c0202d80c036a5000c0b441e00d0841ea5000506 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43571434 1250 43570184 43570193
    0xd03050901020d02060405030f09010302040f0308070c060503090304150c0f050f100501140103090c0305010509060106031a010f120b15030405070f0605090f0f040212040b06010c05060c0306180112 86
    0x1160031050861008100c00d046c03d80394640c40e842210b260790403034080007852900d5039010360100d0740208150440004003503903a041580160b0003c0b00111f800b081071807000500307540f1901c02e50780a07002400181d49440d19100b8103d0b50482c010300442d051003204882100820b03c070602140d40e89003d403001d0070742c010301d10342c0040c10403039008141c1e00800d05e004018000c150f90040b400300c0303021080c200000c40c0341150401501018031548000c116600381030410030050350202d40d0904a03001914140140a00e44c503504100c1e05d40050f407070b40007684905103048014403e560f4040d0282d039060b07000568401050200ba100200003c2c0744940e003000000340410000c0c1000a10014941c1d4036090b4485410324400501a100e10410a84560000c1100b10300c4c82c1d032150411410850700601c115034610f030700545002d40c410f0442d41981d05240b16000200c0c90350151055200b116030240141c8a247e4401d041002c05410160505030003012070034103c10740c1c4040900c2c40303020b01400d4051100910140c80d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43572684 1250 43571434 43571443
    0x6100501050f0d0b190303020c090c04150c11040c0c02030609030a0206010612020f03090604120f020a06110708030c03090d14040b031803030709061205130210030b0d0305090102 78
    0x4541000400c104840e0850880d209803050200c00d840086108020400001d1761005485040d8141c00d40d120000010950002100145501c040c1d95030710140d0399800d5550100e005900c1421200908109070480320b074898018404103500c00d060010808514902050803920207124510229024113480350a52804020440c3e212078118001d62900d480000005c2d268071041c850101801000c0480050109598069a0032a0741e4911100d0b03d030301d8010310442d80c41200769000d490032154412215030242c030403103218a00c032a15800030038030f04085030350b4200240255400714041403024418003001078481d000460181d443c203000d00e6100d0500044203810459a46460020f0060314608030800304c041109031811036141d0150280c50741d40c1c021345000c52105220350f4680720f000c00010084002e402015240a840c00c0f6038510618490b011083d004858058402c005140d42e11210f910040c540b001c079145c0c04040b145008941087d09002003251901540c004501260000c00e090201e035a0402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43573934 1250 43572684 43572689
    0x9050d02010b0411090d0305030414010c0f080703050c03070c020f130c170609012709080c0d0302161106040b04120204050f15060901030902060706020406030608160510090302120610 80
    0x4e0000303181c054483c1c0011081d9100302801800c0c000044001001e00180704c080e24015100d03a4000d101c000d100040c010190350316503170780d030b40420120000304040e41e1081c820907111f07030895050b80745036865440d02901d10f02c03846041244c0c41512125400080e480c0e402c1c0210b01da5500c1c0e0400b04007401d071210060448500d2100124022080c1e0040040643e901034205045900b40f0034480403000d440d00403990030b124021410b04503e0300340740c0c0003020068084002e007043e1800300d0964204c4a100041201a4803580c92f1030b40d4820001650007003c02ea011541c55250311380140003900d0640c0c0c5658160894001758880c084188006605c2429401c103406a16800414000d2000e00b034a400041d142821049114041c0908008906040c1c20f0b4040d030310121501d500140002c1e2128058544400a98030a000c0e060029080c04d03400103a44900140c00321800c00303400740030080c0c2404c000034001e950360031284000030050f01c50400400360325a20b01e80050102036501610040c502102042145007456 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43575184 1250 43573934 43573961
    0x9060d0602070c09110c07150306080a030f0f020c0a0e1312020703110f130e12070b0a0e06070512070e040e03120c03010b0405060c030d020a020a05010501080606010512070309050d02010b04 83
    0x101b01c410805080840d10030103480c01c0207100c110101c009201180100042d80092000c0c0c0300380840c103024190480e00501c182d80d695560070ba036003003030394000b00d848420403004541c209184001c2803001a00c40002d8035449400740a242e8060136890725003080c46000004030202581200c0400d00500c500c81100c0e5150030f10540e44444005400030100d5008018484c400601581d14182d542c0c441d039050018a1501030800c82e40c0f0340322405814800d00c10310095901412151412240b40f000c45030104000307101e00c14030b07101c0e20304000d02d894103001c0c00080144080d0422841c0c0ca1116480c0d61039200f8a401203110340000c507111500d1030b401c01c8080174054038005003048103000401660607090b045030280c803030580c4c07065128101c24225070b10318000c8820110802c0c0c00422890481a0b001412805a80c000c0c8000c2c800b590b03030351070400c1d25003030f0507590301c0e000503010029210184826160717207070055040d180000e07240310603441c0e05040807030b61001000181d440745030f041ca0030701c1c1c140200c14490805 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43576434 1250 43575184 43575187
    0x10c0c03110706090e0402030f03040906060801050909070302011b0f0b06090a060e0601052b0e1e0d050a0c050609070f0807080a0611070b01030606090f020a09030209060d0602070c0911 81
    0x8000c00070300b0f07921301ca01c20010082041000141191003d025420a1030040d80803a5103840c1c40b811480050b0000d8000c0c10005100c400001406d450310360505801150040050072000d4195001140e5602d44140c05034080507100000c0e0002480da0540000541e0103114044c101e402d0001c1000203a5401a0101d0103040c100141404040340114041c5c1d000042403c105940d000002c3e500643c110100c2c404082484600c40803401562171a040843d44140600c140c4c0c8100040e003803c0340c44101070140c5040c03c0c3d4440e034200c104180c020ba00520a02c015401d1140c14003000750b940707900d0300034200c17050315281e00440000c00100410039000405403403c000034050302c90414288541d600310b041000342600b619900356450000c295012200026001002d076012581c403418000040c0009118150b207075890b00184c0c2c0481c00e030705d00c00c0e41c0201c0050358407000311601d16000c2110804c40601941d40c00384003481101c0c0000d07032520052054501c20110b012120f450058442c08550f0412103107868000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43577684 1250 43576434 43576439
    0x5090102070e07020709050906060406082a04060504180201020105060102150f0a141305060a0c0c0204090215120a0e0d02030409050a0213090f050106051314030f010c0c031107 77
    0x30003240810941c0d100c10348040c91a43d844900701d141060035840341c1e0550303151409000250a000c5150f91240c50141e805020003662240c0c019507488800c0c03480380300642ca0b000c141c0e41a058007844081911001400411080c1c0c0351400202102ca001d40103201202e420001d18045580a01400354801024000707480070240343c2e034400301c440c00b0007030a080324072200e240020202061a8400301c44100c104107605200c1c80e280c107001c0385210307200354140c030b09214000000d00154403074040e105002800e981c400b80705000650030700c8098502114101d9001511317426180c2c011581c1e2000d4030700040d4010b11604103041c0801030404566000c21103141d9600b21907105007696400004583c00c4501030400011b996440c2240b5000038042d204182c000414a283c0024850695800c00d02c410403940c17030104500d03680d80800b551140f003a6008a203071000010002c000400c3d03850b07600318240501a09840c01d180540151a08503510040b044001c1000710601c841816031066010308031107a1200101202070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43578934 1250 43577684 43577687
    0x40b0a061b0606120c0e090c0d0f02040605030d030b040b03030f0f18031002030103060c0e030c010c0c030c0b12090a020d020d08130311040c180b09011110060312050901 74
    0x61110021103a1180203000d4408114055000f01d0084c52100508a502c403620b107007080281880e8812801c50b100004c0101d0318042000c14a021000401000681c5900309641d82400101480506031380c85980c9010001d4292814089800c03042242e50f000100d445a0b08100000c48003100c108502aa1041c405060420382d04403c031040520340c03e41c215211180020f20b50892a600c080c1c4603094021450b00250000303813a00910305a80c0310720070a0085004903402201c044100c054903980c103501c01c0203070420319405085503040c41c5001e0064a40700310b0b140d44804150300410741c8034400c8004002007003004032524250294009607100058040d01c0c61903000100d00c5600d0b180040d1040c016006c1000c100034010084402c040c03c0c1f2201d138200641d1300d0400140e016034600840b0701940c1020700005403e44907a00010b820b0b51400350081070503040400c610381e160401c4114a040c008a24000030403c0e40402c01c0b0881c05c4070b9030101140f12420343c580482c84400018a40050010a10008016a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43580184 1250 43578934 43578947
    0xc0102160f030b130804031a090a03080a020c0309120705010f02030403081e090418050f12030a02160c030b06012d231204050609070f060e130203090a02040b0a06 71
    0x100d410000500254803440c0700910758184c0b13140e0013000084002000400c000b810504140240207400c030903003141e542d420302d031600c42d52242ca004001802c803a00103095001507601800c0e80340134003801c482c2407403c601e0202c0c0041d00403d040003480d500c884000c10682d82c0c040600e4042c12524030186042c540b1b1540c400010f4020b00349040c40307900c2e41406600300603100720140c0d130300400010030a021010ba41c21042014040302a815511802105004580b03d03000140140c2d03029290000c451455540c140344034000e401c0400c0c00c1c07080d0f0034009a0880407827420036100000d540184143e84060030004009421502c8421104070200d81105082845110040ba50480311510b41004414101400c03803620040c05290040c5042c24000705003100070300c1100c0e59161241d403140f0300320f58031501c900c003106940b0b500900c120403003035101e8201030002c9481200304807480d0700040e10a41582100032864402d981088502502035805244c140d001d610700b901034160318003000d448060101d4280400108417 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43581434 1250 43580184 43580189
    0x507030c0801060e070e060904020a0305040501060e06130f0605060f030a0c0c08040e060109031718032b02030903060708061f05090f0604051003090201020607051306111501080c0102160f 82
    0x902c006d1515054041d00c0c1ca004407050719078014421582c2e01ca040030060f004040507901a9140d40c43d0503c00316480500408d2540502c100030503003035144020003151405000003015491105444000005090701d1703c00181c01c2840000c032210b512898200007940071686030f517240c0b10810068a46082c085140c600c111819110901a400c50301d586407801179944c001aa440249044040800e00c100f0b202e400000c0d241c080306d03c907481800b07001c50400300340e590740c1c3c000384c481c403000c0346018008681c030b4415502061124690068030b040c40741070000a41000740890761000803589401c2080850314010201c0e0b80c1c501702c03020f5003070700b645607060000701540900300701d85018604903102c1d00030540c1d035071003510000c0c00024904950141505d030010080d0000032012805846580301141c0901e000710103507141404100d1110140394a4040211403030215150000c41600610f00344001180d0480d01c824040e1001d43c0c0113200342210000024502400d0a0003201c1c00912044180000d030152440a400c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43582684 1250 43581434 43581437
    0x30309120f0c0f0305090a03060b10050301180506011101090b06150703080c130305010e0f0606010903110906010309120201050709090204270e0610030204050c0403051504080c0a0507030c0801060e07 87
    0x103e5031a249025a1207200b0019410780c0402c3e0480700008021a507040245070040c00e90701c005449072820340c02c1d40c3d82d0100303000b40b0801a1107010510600025540f0850388004145400075002d201101443e00f10b504108c81610088180401c1040c14200f402503400d004411002c50b5107000401c0d01c0081c031511029002d020400000240400304074a00c604c94809160080000c0100741c410100003541c40090b814030785900d0152400280103517000b54021801c40e604130004801c0865004100121000000c0100741450b90300c20100f8041440c650102251032055000040c05040a583c040d1013524a030303002e800c0302401044140444034800310f00c015600d01d6400c0b8003160310300c0e058a10000d0412801c1084040c4235000410404031501c942071411079000fa03c6c1085140c80345003010703095219500015142c0e03407110000b001c1190300200020380c45070040c030150303007000043d2210340d041c4500c800b82a10f499004d08800d2003880351114901c4000c040341c90007000144c0c50000c0280034003000912010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43583934 1250 43582684 43582703
    0x1202010807090812040305060601050304150b130f0b0a050301050c090111030721030c05070c0302100e04050108030c060906040c0b0d06030c090501090c0207030b060f03030408010603030309120f0c 86
    0x1080c0600869607600500340400941300360034520100b0040c0f90700503200c2070301d151003983d0104013154001c0d0200c80c011604400d6070ba100d0000c00032480003a200c00f417402600003d41100c240200b00b40b900c505075400c2c60a05000c1031004030380302003028000094000da0312903407610301405100280d410403140406020708058840302c1104584070300b18007480c0c4018140c080304d003c081401c040200040c1e2000406514100050100411304488078000d884004146039a095820300140c0f8041030550501901841d01c01c61611036107020905441d0280e0003294581d10100d01c0d1815454203000b0140d00ca0880c000610302850709440319024686240719400103041c0c0050400c68079411504840081c40e002002640b50a50b00e1142a000b82001d100e5110042e242048060307800b44045000401c42e03420000f210f050761150801c1000301d8016201c0b8070343c544401c000001e4041000c0c011080214001e4074005007000f05410301c0c40040a5035210350041150350381a1018054000c2c215150460f0801000e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43585184 1250 43583934 43583941
    0xb0a05060f150903010212040b0f0f0106120207051006090c110303071b0605040506060906061801030f14010305010212091618060509041b170c121c0c06050606030112020108 76
    0x5030341c801e150f04079806500000701c940c000034101c82c403d8000d9100c2c0e04a128a03580e40040300040e5881680c911000d802100010822180300b00082e80320000000d40c0103107862003640d80c051400341352001e03880070030f0389811042024056074800d0718840422402c00303212070701141c0580c0d0349030f1100030320039418019000d64040c400a0017402c40780c1c1c003640c4082c08020b24141401e10540c5c1c1c0f482250280e11540c0b50800050480c00c00109850380d246c20843c2204800d000d100c0154041c0848140514500d5074900d15106c050542084c107034001c0d801032000503640c1200e2904000c0e0f840c4000e2a480243d80a0780c0c195012441280c4070000f12809442920814452a000c2101800c0c5503402182d0140706002071100303101d0341d074982d034848005a5a03440019a43d580324200810700340c240e80b001607045000720500c03074244401000c1e40031a0100c01d580f0741c002e00d03001c19403003904002d41290004569100720720402c07541d4071985410140c200c2c2c0941c1590b02d0704410100024690070024100280380010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43586434 1250 43585184 43585219
    0x603090118050325080a0804140d080604051005030604060506011202070b09010f0b010903030c021f0c03020c09060a090902130615020c090610050c030d180b0a05060f 73
    0x1607a4240d240c82149101c03194504006549801c03001441304a2506410711403c8180034408514095900060703e90a10800940980315140014804c1d20401008815400c0c1200c00f03000750210080799031208070340ca00b04617080c0001c60b0380040500b000d24000100600c11950700040f0542c2c0306920032004035040c2d039501e0048403001600b42e0031000d0700e0300205a01c0308110240080500c90314851008011400d0740c6051881583e102e00801800714607060310601c00b10741700310b454000c0c050014084071040c2800e41d03002507620700070400400c0002d08000d100420140c2c10310103440d410304125407180180c1030a200003132425885200c0e107002a80d030750b800c0400310b4070740789550038081103540406c100d41a9124103459441c61000241030040c001c1d000c0081ca9032901d0942140034170030240c48102c001050140580c0d141d4405031064030544003e1154400700ca10901681c000b04071048012198500c552401072100c071000350500040500704400c202c00c0fa21882a4104000340417920f81d219111002d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43587684 1250 43586434 43586441
    0x40b0d0e010c0e01081b0a03090812010f050108010815010605070303090f03080a06090614090c0720040c020f10020a05070213060e091203040b2e0311030c030a0206030901 75
    0x10550110750801001080007500251460444038081e2540d003c0c5588030b00d1442d50419080340200101c01060040c039420600c6603020400091042291500d01000130f0505d0070320040c26030003607602042c4c940c024416943c0c402c41044c01008075400401c0d0000c0143c04880c0494014040c40c1c0801c1000300b241da042c1442a08903100c800d4200c40391252a80c03860030001d240701411500c81c84080d042c440f0010300b80d6402e125031310031a84e51401d21a03d8507a0300301040300020024101c00140c40307050200e040404c10745210b06044107171100c1032180885004080c44155030003101c40c2000e640181822000129010a044808100c40800166115102e44003901d15015906000e5040f855442001c42d2a8025606c480196604000203450325500e0062290b07a42c860200e000c04c0d0b01e841403003c14000303034101701e1b80c64100ca02045803000081c111044541d10309001c9140c140f100341402000c000b404010504404866801d0b000f91911101c88004695551204d010007400780000000196000e4070070750 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43588934 1250 43587684 43587701
    0x311030c030f0415050f01061803080f03040303230a05060904030c0201110f070b37030509120307020a0605010602070b0703080a020c24010803090a0e04140d0c11030303040503040b0d 80
    0x401040241055035540c40c4000c1b0034001d04003c0b5910a0b4000e507801c0d0b500310801d084031381c41203400b460b000b0110020031182d000544114245910361038000301c07030b42e600441040600360422042d56580380c519030b100165800580b1190040c0368020074040402c2d405502d8000051302800c0a020806503042c0062030442c1610482c950781c02500381c0410911a04401050b07101c0c0003517066840010710703900c0107802201d0aa00345c0d008509a03090002d0440c0240c002070b0b4440c40c0401a42d401f6600c13941c0c00c03541035008452020068015100070b00803c40184140b40c0501f0319480140b281390b0520126046910404030003509200c6100d000070009612078040301c4507804a102900c01c8c4080c013901d03c0400c80c2405101d0354445480c41d0000c500b04074000180c68521900401900c1c405150200701c0c00030304401381c003c4e2821400061940d00c060704c1008016466022075a031000040e1a605000b45140c000c0400244260070400500020075800015a800e0351501c400d8a6900c016407e1040002c00760003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43590184 1250 43588934 43588973
    0x603060a140310020406020d0e04020c071502030f040308031e0105012007080d0c05071502030d0222141201020c061518071d040513060c1803050a030311030c030f04 72
    0x380110358036030b0208009040341d0302358680050394280d030000c110581c0202c00403080c850344183c40410214041d8613544c0014000c038015645050015000104194801c0d0010781c0c044100000744500c00d600d036110001601f6040d54038071101d5042000080055020303039040000340740c07413070b803981e50540088c440900200581ca0842d40480d1900701e0162250680240541d040d004040303000504e918100ca0302c7c081450598041d514250046442000940240d0008084100c1c02842410240004c1c44420054441102c030050f080b031380320080081c43e0340c0030740f03052515900601007140c0110000640e41d40240ca640d40300c02d61240b038071021903000b10380ca00c03510038491035034400c0c410000c2d0068611405c0d0808951012140000b034014441a07640541c2c0c5c8007541d10b1040307481c50210314507901003070142c40140b400010001d040c103900d0790071138140d802c180c80070707008042a0000c05030144140c2c01911100d403400c2d400e40c5002980c24606000051800301802e46c920005010042030b41914480c50076107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43591434 1250 43590184 43590187
    0x1109120604030813030903020d0804180b030f0d140309030903060411090f07080703050a0b03100614090103080d090204060b0a03020903151303031503120203030a0b0603060a14031002 80
    0x8408206a549105550541c04542110042100405001941c03240b0503015290b600c1801d1443d42844812909600f0a403441c070313001d01c03021400d030104011000d00308000410118606942004050900e240e440c895200d0703034841d0721075051301c540000401c00b080c140e54201c0d40e169a26014564158810118116414040d983c00c100402407045014690b00c1010740706010b07661355900c0e10b40249001511101c020400700d00000b10914031940049a00038000400441c40454482c007292a01c01800100c2c00020b0f00c0b4542408460343d5480c804102031000c6842100652440d1a2142148035010901405a40700c008540664a45412a80040c801c000c1c2840d41c43d0b0811000400035041815054070902542110f61541d64543c1203c501500d004070702d400c1c4051640e07802368014111801c9400d0000d130740c0140000450114440054070000640103141d6030b14121040303008407071403013201c144141003d00901400780c68180c80c000542e02c0b00c0a000c0722102900001030b01c0c0141c1ca00844007a40d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43592684 1250 43591434 43591459
    0x906120103030807090f050a09050702010f0608070806090d0527092e030506220c060203030403080a1505041a1908120f0d0c18080c120f0a061109 64
    0x380001490b2084d03032140e0301c80c1a07068030743c4420107802070303180b06165010980040c248000030442e480203401050358000024840c140124920580d401c5501164460b00040703400c000d22039052007125802500400504a25050018080c20b580140028019040c528800194100106080c4031055190003086c4505501d4140711008041d50361000c02480301d04608000d00700302106070484000e4076840005400c85c0d58901c540c42d0020040d80303c9414400c607402c9440004111405142000303007101e54042c5669203042d04020b00603140c0503009402c0c2c80e160a1300c00d554180000d00c04019100120307808500040c100365404c1e00401290070442e4030000c1782c654404286844148141114059000c0d141c0121301d10241c3d40903401a14007140f184a000c000c0008411090f0b4803000005215040c681680c11545102d00c1d000300441d0411035040d403004c007040c031003890050b01451040e510080240460680310000b15103c4100e01c00c000c100b20f495010503054424042c05441c0b12480182562140380c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43593934 1250 43592684 43592687
    0x1a0603030d0e0309040b060a0e0402090301060f090e06070f080c0a050d020307030b031b060f0706021b0610050f06071101051603050d0c0c081207020109020a03050a0203070f060e06090612010303 85
    0x20302544213030344910314100f4400c07514203001059a02e261059212140e28042000610010350300485000703500d9543e40e64081003685e1500038540203411002000140c00054480c202d242c8034024180506121500309552072040d030204030581c3c40b01ea83c0e005a034603400006000d92b4603024107003861480c0344c0007200700103140e079065000c0400020100c0440c0c1c01e01c0d058507030078a400300403402e4090b0462010403030030b4445051100201015032140710014a410440c3c45490768010034400c101450307800135414812081842007948010709030442340c0410741c401b104005a100e00c522440104890440104404142e005600341c81d03800c03c2d01804a4004035607464001d040360700c00b0700004680c80c0762500301d4503c0b0b132099190720a866130100d0400c0c680341604520580007000102234004664032044401c0c0180ca8007150140114440c0b001028a0402d500c1054200304894000b540240041502048100d500200740741c03207407d00355110766172600b480c00807892510681451540c840b600400000416 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43595184 1250 43593934 43593937
    0x70204051801050f16180503060f0109050717040209071e050c07080a02011b061509060302040b010f020706110a0605040302160f18050604020c15070e06071a0603030d0e03 75
    0x30300840020400c56407400c420101c1c0d03080c2a18207445d4800d480a010103242d0003a001c0040080c0ba900c0e9081e100c40c1d885c0f0001b41b404600301d42e812202c44a0704010401c0c1c0e41d003402420380108035400c02600300c4100310086070b5050030091010740f14040b504003180f6090b009070550024002c0200c03c1c1282401030441c02391140e0f21181e0340000500c510307800000c900380040b4004200e10390583d2605064a404c8004103089420401d0a48415640e4a10200c401c5442030300d102c0280004071020401c146103004010440354103e015505103c003aa107104a5240c1c00300ea1102694a50304003003120400740c0d58800d2901e070000344010584c500d000280003d264000030900c01210003048a00e02c85a1106e0707040d00d410718a4071a0300d4801c090100358142c040d000d0f80146078031840107400142484040e1000b03038504188002805c070b08140481c00d10090f103501008455204000350340d00c601e040c145a8032064491a000194055080c1c1e140110f00703a03542c180125508500c03801e41c20f01c40e0711034a0b8103107031700c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43596434 1250 43595184 43595221
    0x307060e010905120604081b06090a0c14010e0405071b080d05060a06170705070807110108010911071101020c060408071509061b0302030405040e01140a060b030412020307020405 78
    0x1c64919000000c0c40d02d06003501c03502104c0d000c005846507803035640c0c851615400030198803d102907044ca80755a0b0345010030140d445000201c00a0101c00d03400e090552080100d9042420f5420441d0b034030394070998200f0881b548402c015140007075940e80b030030000c0350b80c108000c8044003001c0c00c4000b9002441381c201c004d0694501d02c0c41c02040740e034603224100086008548210340c04100039129a48450f41000240c90b070150380c90600e280740030200e5490202c2d0b43c1c0b00c0703441121420480b0700300000d5540d00a894038058681d02404104141750144401c4041c0203404006240e0101d8a0311074141c4c1c0d00c01d000381c0e00703009030180c181a00d854444140c107032501040e0241030003c1c4c007540c2d1742010140c410303510b80c4200d034100e407500d10b002c6070b200701d1800100510110540951108000c001095100d0f48184245040145c0002802c80410020340342c0c1000003270100310325507003045020f1000801100441e90456801100802202807080c4160308500441a010b0750052416007004644020400c40c0000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43597684 1250 43596434 43596437
    0x1302040e07030c050405010504061503020304050a140f010b0909070b18040e0607030509010b0603060f01090b0d151202010509091302090c0d180b160c0c0b090109060302070f0f020f0307060e01 84
    0x856238075a82400220b0b035080c820520910740768003145030094060303802503800c180103030242ca00c0c1790115156030000e2100003004a000d03500c1102a4a4501c100784240306030030404444a035024200001d95585d195000d003e540b84014001660411440031800d8442070704d400507005110001c9069150b51700c40e1411210400440e0500c000070f41c0101042c0320f40d040b400c00042c03c150960303c4445c01e115004040210041c1808407982c80803982e0030a000203855540c68080700410b02a130507803403280f20114903030322900e680c0107200d690f500141e0700402030f02c0121005940e100d03010342d25241d481d02110040300019400a80c52000e1010b00341e02240202644e4840b460240704905042000b58001ea070b03d0b40004d0618410400403864207480344445034120503042ca0700c460b4081c0c00e0744490070344c80f0b00e46d84004000381c8001801c511658014042074001e06031030030110309002082e01c54072595903440000400542034001c0403002c654070020a005502c1c40601240c844030340301c0001809007980c50880c0360 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43598934 1250 43597684 43597691
    0x40501091406010b0712020102070b09070614120103060c090f03031d0f091501030908030a090b13050d030f11180f060403050a020402030c09100504050901090209091302040e07030c0504 81
    0xc64581c00010030604a88903200214504141c0f0340701c0340b825001c1501c1e10000c41d502040071001048000d0b0005000c0d01030030001e8800076103003201c0540111010a04184101414024050f1402d600166103046980180340404d1080142d0411507030080150050580e041c42c440003c014540c1c0035420642c00640e0035403074412004100c0c204103000c14180144c2341c3c03209060000528409014000380081c000605000c5168409641c81c440b05030011558050800d5450f148107040c4260f152030785070071094002c2d5690b4440c0c0e8544905417130b683d174902c44100741600d0740d4200c2d02d0b080150b400810700c2070f0b01c0040700f0f44a02c20440d41e60010741c0c041403030501c1510303c41c06d42c4840e031411100301c50840b54820000c010002a035401e05c40a0340008007601d00b480e4050110900300d440c0c454500005217065510103645d0b90a083c101304c0c2184042c1c202340f094610602c500819515080300c240d802428640840e0140d41039031000030050a5214180411405214000010400c0703408014007500c00848061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43600184 1250 43598934 43598963
    0x30507030605030307020d06110d0912030c080103060c090e070e0a0609050f150d020301080601080f060f0c1e042601050702031b07080303070507050d0206070207170304090504050109 80
    0xc50699500b8050715a164104000010041c81c060800000302c61190001045890004108e6150303608540903009915880328401020444480c056096143c2039042c108460b000300000140040340c1408000d0801c0d55032107200c0380c100c2c022440f03c0f00034240368810b00c096203032240c801000000030000c004c0c050422518081096409882d42a0030f40b20042c10181c40b4203c03540c00c02041c18440b52002000c031404221103031500c03907a07000450207004010003d090b2540341c4501c2078501070883c1404003180c2c014100784805400391124031130700040d000c16540d444110001140800b043c10041104400a0009000901c420200702d01502a49400555551181c01c017480e10300341c030401c444150060300b0411001e42940c1000d1901c00b058104e88040712000754880070b6141c695441a10071802213500481c191040000c10401401d0100741c034400b400c00c0d801c01302e4001e5510781d1280500341312200d54858406000c0000c100f51402015642010701182c18181800c600074441600165a09401c15030a07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43601434 1250 43600184 43600187
    0x15010e0c0c06073c051804020c0304080d03020c03030606030705090301090c080f210c10060306020409180b010528030b040507060f050301050d02010309020306040b09061003050309040f0e1c030507 86
    0x5203800c01a0009100040b030800e030508403000d0b400f40300e94008201b40d481c0c2c1e104090b00c0c0c92002d0302d00c1038002e10041d41d0700c5080104e03032850300c03048040c5e54042600400c03522145100110659401a42c01d44010b9140e80314208244c480e40031740e07a00290158606030228040c00b61b403214100407110740c034081d00c120b00c0d61040a43c0d2902090361100d010b071501d50070030100c00d168050080040180341d00503240c0107000da01c0002b054503103680c030a907056500801d05100751601e0744506052180001002401d50030280d80303280021505214951250041e028540d034a0f6150354402e0180f10440360130240503039260301e444203a40d101920252070314801e0038004981d8034003400000a0005a6032a082d045070b00e400100b00f03c40700300b0041281095121100e00005880030460710307000b1442602c2139a4a403a1200485252050003031000c0404140e007041040491008411a01c010100f550040341a2104080700c1020308080003008030b9901c100c950000207242e800c41c0f068500e803503940d4144803540301d0410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43602684 1250 43601434 43601507
    0x5090f071b020d020f0a0503030706020315040209031506130905071802120c0d020f0406020d0201140601092303071707060816050a030b03060112031115010e0c0c0607 73
    0x1402034001040fa080e10380035150040c0e4543d24480000c01c2905030685400200342140c0064904881e2540c010003403124075220342d012a14901c0c001c0d2000c50410020000003552000800b1301d20b00d440a8080128196446a9610741300040507124107004500e03ca20b0070130307030341d2903140b00c2c2e80c1d0b202805e0b6a2401d9260540d00031540414020003c0440303585840000c4440c940c403c0f010205401c1d030030002d1500e03040d8180040d000815030303600a049030042d0241e029003515035a2058502008240040080680c0c0144d0840103031880300190500b07604a40040704204040c203058a64144929000080c88418010b12280d02d025a501a114026501c0304181c070a034109403000b0030640344c041401803034948500064810380c0e81915011a003040c100011a051078000e80140030a0100002c03103600345034000490640301401f0f00c3c014614103048964400e00464103000326400034640304046000c104650b000d84104e140e034107003a5030f501c0c280b84002800046c041040110481846554032520f40750151 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43603934 1250 43602684 43602737
    0x60b070204051305030403020622031a070201150b1605030c0c12060405030702061602040606020c010f090f0611070308030705030411030105040201120f1413110d1101031505090f07 79
    0x9501b003c0c1554200442c46d007101103020010b28140d01d0715114181180025002036000b20948031085000000ea030420120042080055a050001c0a0b804000c1048000116540d01305001c0d251800940f101190451010300900b0170700c408160301e00401e4ac049225a0a610122200c000c03c00e58119090345519085030090069082401101e015003450380082040d40102d042d0b0b0030301c4500030b030b000a00f221050741013040168400d50701181c065030403494a545007032503814010801e514000500358411454013034201004041b0001402c1403000b009030b8006180d00c60300e0f494491404c030900038025042100d040d118180390340120307001c2d8181072041900803501a511211003040031080a0094560a00c0b64407447d65a080c8039116401d2821080c0d01030007620b01314500801050a0407024400e541c02120b120302d52646294000400e03a1320b101210700d03005c0c20040740703600055101303a03040101c40e4000c2d0340001c440001c1100c1c80c407108140c684114540e40f00c501920000054082c01954401c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43605184 1250 43603934 43603943
    0x1806053102030a0e010e0d0201180b060f0409080f0304030e0a0815100f09020304060c0201050c03011e0509040f03020d03060b070803130501110a0801050f01050d0b010c06060b0702040513 82
    0x50038a294038150780040d9440070503a400440c031084896607607401c40e1210030202a25800c52860390103240c0d07080c040c40c4000d420b1020300d00c1007610b1949075002c02c0c0d140540120311500a4001c500302d40d4960303030808014107030080c011a4a0301d14681031009250701c222811000289841d2080d2010710309440030b00103aa110310014031004c4981d41c00c0001c901000340807103034100340da0440010124200e2138880041c0c03e880d40b003d41c1f241443d150000c180d07080c080b02c2d8419a41050100301d2100598801e490454014401c00046503c460003881c44111441d0445900a43c4907402c000a1000e40c8a0041c034051103036085610403c490300c0110111800c0f8012200c00da01e081002078003085090b00034542164040c000c06070b10b80300d16a2454210303040518104000000451003210341a0810b9500303005180590b01c00000040500009140f031040100300350f845640d034580030300c0c26485441803143e003541c0030000700132072074540f040070f8800c0d0461300d012072049040000240503e40251030b01000c40303500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43606434 1250 43605184 43605259
    0x21010806043c030207032103061a03060120010c0e0102240c0d020d06170f01021e0307030b1815041104060809030f03040c06080105030604030c110a180605 68
    0x74452440e241e0b01d072150090b802c61080c0000440030485c3d007408804140809960400307080518080501507400513032002603258445000c4072110301c1800c044030340c400d40900e050303124442c2200350301350401c14041080c00c0a40c41d240c0c1d0f0b0795040d600007100905000f000d03000c4030491180c1201c85041d200310761050309500b141140c0418007208083c07002d0301210403901c101500b00b40308213030072908640c0d050340818038038480069501d0582805000c10310500a000000b9860003100600d02c4118a8011204946e00000000003450640c401c3e1701411824070000c0004400346800320f0f1000008a058035071591060700745168076441e01c0c20788561940322a0b90300c0d0345805c00d441c1803002d031a0142e0040210030140020800c0300d18000914000b184600e100d2050111182d062050040c46411305130400e1340698080c0d01400f01180d00b040c03414464990000960320310440c80004900310001d55405000d031400c1000000f00086841d4000301b054030001d50343d490030500a50f0304028000741c1d00e03080e041c26810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43607684 1250 43606434 43606523
    0x60818070510050d0e0703020f010f2727050106090806040803090c0604060513050a030201120c120c030902040b09010e1603090807050307060507080105152101080604 73
    0x24642c0048500b00da02e07080c01800c001da056000000d0b24003110355010180c0140000344110b281082d9200700f0f8031002c7c600300d03205c16050302c0060050901115160940b4098442c40c203181b804000808014200110f0300c0340b084500401010003210b0f003010044000f0b401c00d0b001040d40d40c440d0719448115840c1d4030081802d62650f0b110426560302c05000e02103140528400c0700360941350305008100502a80c2c1c0c0b01561101040320004078900741d9080244140e01d00d00c2c4c01c0016030303400203210440c00441070700012840c0000c84151400099092012442400c0201e800c0b0304541643c0084002030027030346c0c1400801c400c10100910408240164580b0490f1000815207409030204074140d40c40c0141000185003007541c454280c1608402c4048555a00019403603041100c580a550380040f1302e030a000c1d40c254100000180076004c5003507029a00c410108140d1058070140102580030700c082e00010100d540c541921546031602150309454010b60040c050309401425104401d402000210f009140c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43608934 1250 43607684 43607689
    0x90b2103090603090102160b0702011113061b12030e0f030301061b030905181f03082205041107120c080d05090c1201050a11040312080c0708070305040608180705 71
    0x40010b032103080c4d03540d400d00050400c5001440c0740b01c8041d0282014400c2440c100c00007c0c20744402d564800070b0350302e09028071807200b804c40c2e0381c0d5000c1c0c03413140c1000305d070002c0781c15040d140700000120050425502020101400b9030542e0161a0130581d03002581d07003a01510781200d59038882032250000090b00000c5051000600d280080c1986100c0e24007001201c4d941e00c0060041c85095049590f0084540c05001e4a0000081c151115404140e4441b1140c0d10310b456110507030181103d08000e0001c28500040420845001030015060040c0100400c00030b600e484180341c0c0085008868510176502c0102d0785034003440102030110b031311424003071601d058008504041e0001602d282c80030320510607224101e648010201410205104c0000352910380045280107580c5150f03100750004604000610205042d541c070546505070070b0421f045962959902003a003803040071006002c0403004100c2400705640301004104499503542c0b1070426480d40740c4007000c3d140040c46048004c1c0d0101000700f1860 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43610184 1250 43608934 43608937
    0xf0306060906070609150501060c0f1203020f1306090506040e010504110405031509010c1803120507020a060c0506180d030b0102010e0703032d05121003020604090b21030906 76
    0x103507009010541040042e688420644e0780383d4200722030012120b041103445180c24410760b40103155078945148040c0b29038440420030452040c0c0030b891a2608042c1110003402a011112082d00c01102e842c0e40c0c007580c01040c4000301e42c43c05204001281e4820000e0286041e0003903605451071000d00c04a907034a404100401400c2162040c07507020400d100c0005c041e642444203400e80745052103181114607080f03480c203003101d03851542941404a5120002d50102e0443c0301101500c0d030002c042001d08590702c405503414001d506000798000035085021445a90081403040e65a2182e01103403011313181e0605c1307503d171080080242c90441d03000008a0804601c241c121819405040c000010540e5a07100e20070f080c13100076007064003c140d0003185d00804507161b000d0a03113402c41c03060848202101080c0010064800e1801c00e03094000c0f0003000c204009083c0e04080005d55000b0103d650300c9603904020b001034084c5480744c911401c40700c42c1c403030310000008200851507511000a14600101907040100742d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43611434 1250 43610184 43610197
    0x709050a060b0d020c011803030504020a090c050906030411030307050a060506090705180409150b011b020307060f090902030703050702061b0405040f0e010c020307050d0f080721111c020f030606 85
    0x25648400c0031000a440391400ea1f0a554025600480c10b440d10740140200b801c201d501c481d04040c600351440010f00d03400429104108800c507202650780d15103080100448558000d81030303140c000040e5203010843c0000b8000003c0e841544140010fa440000300844690708945030340103c0c60070031030901c03040d0104551980b8940c00400001e00842541c49843c0308500402d40101d001d691414100c196680010704901301c00d41142c440c242480b581d90110345c64803880e200364014481039001c020380d814042c0310804082c106000d021074503494000d100a0103800141d402c54094090754001c1003040d03c1d42000350310400c81070b00a0500d0035203040b06210080480251503c1000da81d000502d00c000c070203005030700d000701e9543e0066403154007a00380b06041c1082c1038042c50070712040001042085400070142a0320100b1820000c0c40c04101d20000090f50b003d0700c0b113132052946010581f065010481020b0a500ca0000045c09160b05c44c000c1e1200c100e1040c0c2404141c02007061000841d0f030b1600d41c005252 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43612684 1250 43611434 43611457
    0x5040504081309020d0e010908090f01090e09010203060a0506030708040b0a0b120102040515120f19090c060905030a0305041e0515120a050105060703030902030c120709050a060b0d02 80
    0x9050400820b154061010740c024003005500003034128000103a900070441d40c0f0300440000c20080903641e0ba0b6a00038071806d41c0c03840c0070b140c41c140c82c03041c0380c0e000d144540000c0160394080920f5191010300705d0b000350301c11102c143c402c942c1e02c000440c0794204501076903c580301c80d88a421864465807901480980001c022101c4036881e6444800d190b1a03c2002c42c030410582000540c945040074100705031140b40514a14004500b405600c040448201065802240c40c2e03150842903101c007901008003040d180c82c15695541003040190812012088100840d0081c0d60f65142e040e0b120401c040d11380381d600c203002d400248140300602c1b4034199003400d10b1091128006411409a482010541880e182103a100b00d801010880304c40c210704000080d40d021003500c40030840c941c14880081e45602408001404040e600d10444003152020003121120040050004900b082c241003581e54035039042c082c229030103040c2004608004180c1c003450003921b41b04240300f420415a6010381d0000d4010042804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43613934 1250 43612684 43612687
    0x40e12070506090705012c03011811150348030106021006060504290d020711030a0c030f1502041205010c020705010206010b1e120708070c0c0504050408 67
    0x515154000010015944100301030101e51500c01040381c01c4c2481988894140400b410210015401840c4000e0f415282070600388142c4000401080c0105034100341c4403081c6030810503203001d200e6082d01c0841407080072544040c880c01510b6210b10b4500059900c7c40d1456405500342070040d5035640c00c105220700304080e03a0b040e603424048500080721130404800401c0c0c8000014880d00d0b034140101181e607812032509000c0e551030709500400511462050404100650802e41d400340754642440503e021301d4188a5198800340d8015002540120b00c04c0310710400c00002068213080c0800e080000a400c05001100c035445c4d40c5407000c2025040381c2c00c0342c0c4402e80309242104103003d440a48041e1403110310000c01c6808514205084813904e00200040d03500541040055071b0b800035040b4190f5400c2c13204a078071014000300c08e40710b030350542e00b5003440a00c012541140c841403041401d44150900e80e221409a1030352801034030f660100c82c50281840d800900184400e04094100a410922851149 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43615184 1250 43613934 43613953
    0x30b040c0f0806151e030105030d020d0915110a0c081902060405010f0203070605090a17190e03010209030303150406150c0803040f02030a1209090209010e13060305030a08100906060806040e 83
    0x140d400754414644c40d41751302d03c080014801401c082000c00899240383c0028004807a2421000c0c1120b5107620900d00b100b200020840702c228400c8071000088071944084039100023083c0b400000460582c082d03848030380309140000840c0c00b1946c1e103544100d50050f218134030b020b0610004448051505856006510040082e100080c5179442041e2040c8102009480c0d84a0b151920079000d1182581d25051441e05000d0301c46c14842800c40f9031802001810b201095091140c08607019000b800742d4031368980004420441d0b401e0901c80c0121504004490811100e601d8008901440080a0f00b100014100300032040c0001c0100b401103400c10f0217064640c000c04d040c0d1b40002c2c54843d05030021128000380c1013220403096002034000001c0d013102c982c2582081440c000007842086900246c601c01c0503150102507213500564001805107800109803070303031020f8000300500f10b0342041c0c84040382041d043c07000140e003c1c00380c821101594069601c07280b55486d010b04120150028101e0a103842c003544061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43616434 1250 43615184 43615207
    0x80a030c060c0201060b1c150e0601020d0314061e0618040b1005180414042906030a020616050601080303010303110106140904020a09020d0c03051605120c04050a06030b040c0f080615 80
    0xc0e0014003042762192a0b0b0300e000800241851484c15a0302c05040c10000601c0e0240c1030500f00c66400300b81504c0800c5d0950742d0540542080b4940251603070055000540e407200d1140005420030809000d60b000e100e4100c0300c009006a81180050050000c1c8050041c0c1410500d4a42180c01da02c000800c0459400c00260701c5105020065400701d401d014268011001c44d60445580d076032400b0060160001494920003213134480f2801c00c4028400c50300010441d10100d001c590010800b500103044602a603100c015032581c030f9000b8002540410454807646a01060500400040d0740301100b41905100e100d00c1405011000500100ea1000400d94041224001880500401c1c685590041864075903d00040d04491019110007030518941000d05a1141c0050445e90445402c2d042006c891307507001c4109001d40174981040d94000403040c2c00040329907254000e10115403044130100040028008203503242c0d01c40140703d01c04142c6500015400e490928401203c0c0803921001c0ca00d0281d00091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43617684 1250 43616434 43616471
    0x601020a0b0a0f060b0a030c0804081e070609141203160c050c030604050606040e030702060301030201050f070b010605040608150307150504030602030a061401050f0d02030709080a030c060c0201060b1c 88
    0x8000c5d1140c0001c03d04158040d0305014821000200d403c0c10945400d040c0c452010b2403240031060702c803000e100803014514542c2030701207902080d045402006820501c0c50f0100803d450f0f540c0c0010b461103841241490b9032a5002100e000e40301c1c4144120840000400071303940c66070301c03100549580c06044150041c0362030a11001d03118500c42c40240c1800d00e001c9080104480400d00b080300560b0041c4156070040c3c60b802d00326415a070702401e02c0da0700c880325490f60202a200b030b0940108031080e10000014115003150140c025502c468440780200d680750400c6e1031034054654102d41d85603000780010064141a45100c1c100104249003c1e485c00f40c49440c3c0f0300590b8000d61307610340d0841da9a4800c000d0000c01c1003482180220900e04a80341c4001c407075010f10180180c0c2490600c0e2540080490240da00400c0284010405d640689403009901e060141540c05641015a60035042011030840148103200c0d00741a1030000b1011801e100301102102c03048202c180c1700c04091541e880e081000c03c1d000e0791 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43618934 1250 43617684 43617689
    0x709150207080138041104030804030501051e040b09011d0601080c03010e0a060e0a06051302090a0510260106150216060c020f010905060c010f0605090601020a0b0a0f06 74
    0x3001440c03203602e08014103007100d2502c644681a425001e00e0042d804c0a444510100408003416a403200746454000800500004074904061031000a0000420034404003601c05c4038010402040941e42d004125070100410b240700700b5480303500c40c0010300080d4a503a00c01e41c20480c840d00000d14070b5402250710040d00740b0b038500f0901640c052001001480300c104900310070100f044d00280300c2e04120200d101e03690050841d00422203a21808040540034040040b030101a410220500550a0500120f0280c090280c0b0907801182d070000082c4034030615004150089030f0340100710103e40d20700900c618a0000344013502d038a41c0610b60403002d40582c2402a01d028043c03004418140b601d03082d402a207083c07900e00c1c4140901b03e41c1e04081000a80089034102c074a50150340d1440a002c441e40120782000c44d980005510510104d01503101d0401544044803043e003149007000344503288e03020886c0c4501708a0f0f955006901929084001038071500b1a01d030410480480811100c403086001419120b030798 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43620184 1250 43618934 43618937
    0x8150901140f030d17040501020c060f040201110d0f0c0602090306040b09060703060b0403080903160902090a0611060c070203160303020604030305010905070906080c07060f0504110312090405070915 87
    0x8400851078542d010248055007100101030200860001030803481c2540f4201100101101c005018000207404803400708401100741c0c1d419180c11402d01c44c171150240c2e0180c0c00180055981642c400b80056001c43c0c0840d0380d101c6c1a05044910350403610000000c0e0308a603510380134049003501e61820011117029a00c54079003000c0e80c0c5050309601d45002d000a19110405042c85400c018a90011041314182d0740c201460950358552080880d2078150f180e940c4031500c4000c1c2c240000d6686281d80030342140482121244519941d0305001c5440f920f1500f6540c00a4202c403000c18543c414410040818072f2010301907607a4000c01340310b950144c070b82d0795200b81c01680155080004260380b40c4202405851040820050b50500c810000d04420740c82c0120000e00c1400d030045003444441c9001d44080b45c0d03000b0010700400c918040d0510180100b038404031405071100c04940c481c1d18020840303842c084440b8450a040260307510030400a88009400c40003849030b944000b003440b0003d07291044851219 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43621434 1250 43620184 43620209
    0x1209010c0f08090f0a0f050607060e030c0c030705030309060d020327030903070918120905040608011401080d080a020d02120702150f07170a0b2d0d02090708150901 72
    0x3e80500c500f058202c5905031240e0072110040c4012245440c901041c0e8200f5950281c4444440c03401000600d03074500111230354840460042400100003400b644003000640a0740e000a90703400505540340200030340c15038041014004940042e24940c041c0da40403030305480410003030000c284600401e040302070350700c0c64a81001034510140d0800300414001444510010801c1c03a50b5220b412200010001c401441000d035003202c0c80310288210034100145c540100f0403c02656103d80960081c2104000d281c8610304403000055484e8001c21031440105058075010f095645031229032000754044039945280d5603081c4034030410040a50540c610458164000f000705500c00d400903000350744010840101e0030404020482e8460323024070ba0106410040700c030b45800b074a43c0c41d18400980220100950050240217030144c0d444103c40b400203911828141104550722240b0500200300e8810102a400460184c041b40080d88100030095100741e0340403c9003108480e134400159074290a03808001c1d1045c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43622684 1250 43621434 43621447
    0x403080f070b060a0b040b070f02040c0906020f0106080d111009080405041802010509040c021203040804170705031902040f0603050c030c010305060310090318150807030c021209010c0f08 82
    0x51815264000c1c1040320701010052510070b0000170f0344124055990300c0480408e1750400c0100c50300c00200c1c5207500070804d02c0390036281311005040000912628005204558400940b0401031054209840914001c0c0c501d1119402080c3c400c01480c0304801802e2180503c8201040d04a10540407010300c03a072006551185010100410f540c5e090030b41c1000b900c90040c043c00182c1e00481140d800040960740414240054a01641800ca81c0743c1c1440d6071070400801c000400050a000744140c0d40f665203a60249031300490444e599104a014668141e0302511440141851030251910014801080842c09a10383c0c0c120304252080c1e03034000c46032940311244500203490284895100d07a1001e2804010618003240080d54038540d40c0c803a0719002e40e498020105061040c2c80d040c158030b40c100c0c401150150b41b4280443d044d01ca003544e020002c1c101d42c000ca00d80921902698540b400c20b40e0080a408420242d80c2c480c80d40003140040c1802903612402d00010380f00e41102e0300e114065454a0744890 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43623934 1250 43622684 43622693
    0x51501030b0f220204030b0a0f060e09030d020711030d18060318080306042301050306010b0a0f0f090f030503190801080a030f03020d06030b06120129060403080f07 72
    0xa1450040c2031003245114506080c40d190488500f03030181e4410124841c10030740e0000c1c0b000030b00c603640024020301240d00404c55070544540100120303100820007040150b65400d01000d0544040c1d03501c0d5503903041080300640a4003181c025080c59800345000a603030b41c2203080000e180c042100d8000004c00c12410030004101207405844008125500b800c0c04440d50064100c000c4500362507001f040c215008c0f0225102e600d80345d020890f0014041d4401440000c0340c600d03030b01c0b646004d104941c070038420000040396866a4206031303410141c07251078654003000d03401029500110310005175030402001c0a4006803e480004400c40113500174030155955142400c0c5040303500f0a9030035140284072049004002c1c030b400004641c042981c040c54100d41e01c2c081031808801921500480c0d03810755040c0407000c0140001c04000358060034040b20090780745e000c02098203090b600d000c01d0304007000700403110710307038030403583c1d00c456040660010b218521300354896a27800e410760018603444c0100c040c041032500401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43625184 1250 43623934 43623941
    0x5210612010b010903030c0c08070314010e0705060d020904090816050705190e04050a0204060b09031504021309080904050c040e0a0209060304023d020c01030603121b0605150103 78
    0x54462500034040b1040030800a8040e000600c0010b08204220902074284401d401c000c4014010f550283c58042d507803410685ca4640c3c0f401d4641055503c0e110b403082524200066003411590080c1140e4107200001c0110002900324a64158019403580c45440c00900c4a030024901000c01c0203244804c28403a04181d45806220b4215901421000074584075803002500c00d8001c903081040700a280796aa454583c0c100f070410744000b03410604050f004160120004041e0041d244180c0c2212612081d20b1011b01e4042c0c003d40d000794204641088002500c00d00d80c000d4140749001e00b682c5072608103c00c01090488504551400c481ea001140501c007812031001c0c103d4000c035444100703504003000c0200240c1e16202c05403000348107a00d40300e031710010310501e4a1011034103c0c0c1e1a060b0b2826000030072122084a0709000c400c40140501c1c149c0ca01a980a44138401c03c1d03135041400c030301c2d085812142c02d58500f03010201c00382e12505018407800c00107082d8001c0d184190708020b4111083c104110025065 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43626434 1250 43625184 43625209
    0xb0106020f1506060403122109110105070b06040c051e07050c0108010605041806050409031707090e0a0c1107030c0e0703090506161101020d020403020a0f030201050f0703052106 78
    0x1d00ba030041444095621841036078107498120001c06020006050291400400041004130200c40c0141c60207092055034003080300c8d40d00440c00a04031100040c0115198807808000801240742c401c0841c601d41410b91054061700d0941c1041458404800c00f910011400761510305251100000d200341000301c1808041180c0340300b820304050550510401a203680114002c10384075410a4000070080e400a4210350010800a4000c0026141c02d04000b0641c00140c010401012031000210b110248074110700341c11940403001c011802d8491504200180c50745400160070000c170014402c80201060010400841c0314064644103075260003004482818000d140c80305140c90b10385a02d010038004148942e008644480304e0700340070030b0350b00309940302200c403420030751b5561000c10101c81c0c1524a42c000c00550f0b008541c8858120f40c2c0701e02c00905a5110b0000034001801070000c071031448113810203400202c2c80790500c5801e2001caa07540041da01d681c0034068240311503d0040c0030303650401c038291600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43627684 1250 43626434 43626463
    0x406140103020306040f110909010504060b010206060f06030910050907060201050601020102120f07020703140c0913030f120b040513030e030106030c060f11060106050717040501020601060e04090b0106020f 90
    0x281985550000780c1c82c1c0d84020000740038140e4100701c1108101c1070104103072801e40300070300d9169542000d880307040c000e05080314200c40785c81c1340038a101c0466000185951040900405146019011030305100868101802146080c0f007000000c4600c1c0420f4000e4601c00c2d14590014071400345800e00007400c0d200007502560659204110040341244c14003421079002400300e08071001c0340c8907003508901d03216056202074500c0c442203202d1015000e0101e2000c4181c0412140c02c0c1d0750340c45000c010b200f04080d001000340819551040a545140600048030300e4031072003100010324608100c0490709854044480103050744c03420201004050700b186100074860003c0d002003001030b056a46612108140f0300600f41803207400000000e83c9803181c80a60040414002582c1203565194000b80442e004107100301c80b007642101d0b002ca041c800202c1075a0440c1c2d4141e0040c500c3d40d1030444140c0d6940b12903c85640c0081d120b02d00c1c44003094003102654002c3c407265009220401140c5022070420310700080088 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43628934 1250 43627684 43627721
    0x403030905120f06040506090706090803180307081c0f05030f06061b031605070e19021303080a0903021302040501080a05090102070f0b0106030c0302090d0611130b030406 75
    0x101003039100c0005815039809591007407a001e2003240442c42c1c0701d407141d024002445414204000c1080209026000f03c441c9002c5856040c1c0b00e100030360340442c660003031081950042c400407181d2811507481d0200c1c404094107441c11a510b0714016400c0c107101424407100a40c02d01007180d070700d03544a000449210702c585004e5040d400d080d10101c2c51010085c11052140300701082d4017022041d0f0343d120030159502c1030700300c2e039a85482d655807404a410344402990385010781c40b03001a40e071b0754240c2d0151250141480d42610070010410f400000c3d0002005001d042e42d100f4804000103030508024584038070507032030740740c4114903610400000c10214942505801d0040c40304001c0f59800c4044e80d030308581214030214165841d4aa00c1c2d009004813240940a001c840e00a203080c000d0504541d03041c0c41443c0d4041c0b2038130782010815000d034800c1d0800c50742c00110100401d804a805c0b030707002c03901c0c3e4480c58441d01e15000980001c140802441e401501803900000140b104100040c030516400e51804032003071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43630184 1250 43628934 43628939
    0x301080c010503160309061d07080601090507050d150306020a02060f011e050f130c050315040b09070804021915020f070303080414070e01090c020d020c0a15140403060209090c04 78
    0x102c01007031304400e071000d040d1241d4880c8108119030b084000340000080514420780c480652907980c505070ba10540c90507024a01c000b2940200501850784619515211035242042180141000340701c6014404d08020a4810100000d21750340001d08021030302d80d004118074200700010071203998060380403401000050161188d81c0a00340340340003c0701c8080303c0000304820250003144810f0b00c1c01c0071003400c143c40c00034404801c40d084000380d409008c80006c6050401c03900014081110b481d40292648108c1040004880610a5041552048c40a0300c1d9590030035010340a0307000c4035803030342023817000359049000c44c8101e950400901c00303460b961070700420846295480180c0307556400b40010340b09502c1e464000b0070710724007040b00500418602a561840e987e54022502c0101882c0002800500400540c0000e5034030000d510740300144002e0854604515252050810034076141c0444c00744440c0310142030b501c00e6000060001180900c00159990112400b0000c06a00c010700c4601d6681c03052005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43631434 1250 43630184 43630201
    0x20102040e160e09012702091201090b100b04120203011b020f0c060315060a020a080d0906050901020c0d030b191701050106080f04020f04020c030a0c0203370204060e07050301080c010503 82
    0x590411004003c1c440510f09206c0000c029104220f0501d421402074800e080c481c2e201544010f8141d0b014120f2100181c8030130314605030b12140742c403c2c20700800b010f1005100086940d099030740114802400003a0010505201405043c80000200c0c0940c028a0402564a906202969213000219032442ca1882c01d402400202c46a14420312b01481c0003060000d019402041210f04203600304514076120107220324240094804000f04550443c14180810a20b500500a41e4159000e4a021300003100304454100c00408500706403c1d409403a0180a402c115900f85041001d8640300d0030380300102c10704d0032000742900c806134042c804001e2810308200ca00d460b9042c078941c100354105da1020400d801d40700007801a01a0a1111445000002e01c440b2a240c002c045090541d209900384e07401100b0b031802502da140d100c4404a100240c180e048050200c1c50020310608803807000708000b94540d144c8200e580c0d10360f821110313100841c00c000010b01018030108003241054000746003092440c0b501082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43632684 1250 43631434 43631459
    0x90d0f0e03030d050403020a020a09051006030b0907030b0103060b07061b020307021c0f0b0117070501020f0705090415020c031b0120032a070c0f050904020907020102040e160e0901 79
    0xe1000c4544d840000c14205482032082c0411941c000f084000c4454440d810500100030580702d2403000001b030400001c105000e800745200220009251102c690f80e0800150060000d079490607041640d61310f40441d03a000d10300050700d03000d40502d030000f50860300c40c21244005801d4245100075580180860801a0744035552452003840c41c0003102d080460703600d020708404d80300d66402041c440b008400403511040f1406040480c4040d00110790206507250016a1106594048084560002d18082c099424515081c0d5040340c80b038021402e044540301ca00c00c04a8014604440c0c29420001d001ca180d41040c408018460107604002c1004007102c40b0b1a000c014440c882e02c040d011400710000c1e0b00d41c0c6903460059041c112440869825182003442801d4075885000110b800800508010801c400442c0d116402d581c005410480161115000c010240d400207001a04564003000045210000141c6c3e160244075014103070b449000da4040040c2003c1d4000c505079024450300d0b0010000e8860140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43633934 1250 43632684 43632697
    0xb04030302011a0d15020f04141906022d0601090504140102040b040e041103010c0908121309021b120403060506010e030a0201030b2b0c0605040305070302040203060105040e090d0f0e0303 82
    0x16170125502c14102001c8000c0d001d0704841c42c0d2050404580011105680742d1281e41c5440304482140d48050b0144000c16444440d02440b001a880f20f9005801e800c0000501024101d00b46c10000d1200158150686003100036082500d0440c0c0b204140420000d80b0020300a45c6160300c002507081c94104024540140914459004003410100105042c0031f00e44429446001d0050001e024010000c00040c10358440c1c1e120701c051601c03400400c00710b05960102540c0300d9056007401c1c00007643c5803001820194004550802203ca4980064907001c1400c101e500f00f4500c00245043d100d03855810554200e800c02401c5c1410700855204400b4035580204105000780d9090a0005800c100000803440c0c0c2240e07410100120f00307001d48000084e1440d084044d5105118820b80440c031900c6203c2140c10340103c0c0b0008000342d102e0b00c02800145401c0c1c005d180d20600600d4064145903444140c400400000d85070401641c1101c0d140c41c0186610100d0000e600c1c10705d041121491441d50042035483c400c070f8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43635184 1250 43633934 43633943
    0x1b1208070b100305030c010501030b07180b0a140a03050406110711012109030c11010c0807030c0812010b090102010606030506130504170c0601240c03081b040b04030302011a0d 77
    0x5000151a803201e8080c40c1c2c09150010b0480f030b29810620003160081100780020754000e4400f00001c1d4a06102c0c804e042e07040315a420500b00da8600d8664a100180c000344512410b221806a106401d0b114041c041c1540d05802d50700803034941400e0074103008036440c1c0c414035070b035810701044034401103005816200c84840c0c007131801515924200569007a51401060420180e600b0241c03414281913201f4013807005540200b940c0f41c3c640314258019140c1890241005007410410311244000c2130040200c060018040c904162800400b03201c00550584243c020110111011485420950f030901c6144041c00359410104480d00789030000660110300b003210b60f06a251030700001002c200c2902c0500c154040c4042c005515440d030b1400310b907180c4009024200341d040c038a05c01c030419001152030120102501d52102e182242301600c0480b95002c3c014460030303c00310614145503a080c10b090003000140074510b6200d44490542c82c00a0039102003010000d100c00005904948559414501c4200130f03601 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43636434 1250 43635184 43635203
    0x70b0423011b1b05070f0e0108010b030a03050f04090c0504030614070207090b0f030a03090e090309010c0b0a0e120c070b0403080405090403180f0306060608040b2d041b120807 77
    0x4034070000600c0f0286900041c801d000300c02c0000b5055015407000e0060700e01030000241180c4c3c880f01c109081355661510907a05600000c3d031900440d025400500c404000f40c0070b180d1400b070325803900000340c80d4070501e8000040c0c0b0006d010014031000744105d411140c0f2130fa08410182c00c001d03400a5a900450080c3c1c001940d4404192602e9a6021441c0010007000f40a40e5146041801c0182902c4164401d80558011031030000b210f5600c040111409001d0503150640b40103000e468101004200825800e8440d80c0c503120160300407010401da4203100682000c181e0b40d0403550b002c85060400992007145901300c01e01043c400614040181c3e01070302c1041d60080034030350b9a0700703049640f00c1d200a403c645072001c00e41c010586a02e01d032031f40819030f07014040500400b9950034003121411003c490247c8920801e03800328400c1e03140c8880000380032180100842d00680100d07c1c0d0141980c0030364040f90310015010483d0080b41a0141d0030001300b940d0388140d041801c0644512045201e6040f00a000916 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43637684 1250 43636434 43636457
    0xe18160303050a02071802030105150a09031b090905010e0c0f090613110d06080c1804020409081e03040215070f14031c09030806060c070b0f070b0423011b 68
    0x10170803503a0002c0c400d84942e44e1040030102100c9000354400e01401340600101d0030f5002200c000801211031503115551219a01c5196454000c0030300300c40b0408041c4220402c1000a04108500076810b40b00d00071000050414079114180707150002140609001e44c0a04113140121707503502c280961700180c20364070340f03000c11002c40d0803900510b21422041300307c010200305a401100740d90300c070905580c4200c040340c98082c08074007040303100a403a20022040f84240e500080060606410030100c2a100e800010b040100b40300502c902c400c4600d08048883c00c020040005500d41142680e0b480114000002c0c50f0108a8446200300b6100602c058201d4035510350403410100d00300708481c01c03800c2640c14080000d01001e10440500310342401079002860745800f144080c81c2903c12035046107501801000640d1510520b20300c1c4c0c0c1c000c1790b0807100341c035028889080460100003d9500c1079101d40540c03030b10080341c0c004007000316084142002c486da14003511082c40003040c150610484800d0b0901401a20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43638934 1250 43637684 43637687
    0xc030d08130c0303080405060a020f030a1805060a14010f12120e0307090c020d030b0105090409060605090a140c030c03010e0612010908040f08030f041505130e18160303050a 76
    0x306020710082095001a50000c2890352044109004521550a44900c1c0d224040c0712411380c0503480143c2192035042011602080041d40007421604038208a00001c20307080d10358a0810100300d41c0031030516250342020070748000c000005405031010340460001070307042000b050580c581140700140a4060f901d404089503000d09401220000010100c40e2443e49980501000d000b2510000f00503204001400641c17902078010b160009206940e070a06003041f010030080580341c40c01c41607604699030301002c05c60b0740722112820310580520758089403c860442c0161480c01d4010f210142d610803d000b4400201034510849044030245409a40103446d000c0000c2e075407007190f8507407407001e42c44c0c20307a0305042242d442d018000710780d1995208003503ea5100c071130303035140e1281c000360080068040005003c852690142c4600c54031181c80e0041c10b201004d41c40151882c6150020005008c03a08100b01e600c0300004902c402004094000d0507000b44078009030700b03401046001c000d081c0540800c0c0b801526 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43640184 1250 43638934 43638961
    0x212040219032f0409050c010807050d0509030436020315030303040606050f0a2607030203070605040f090b0612190603060e060703090507120807080a03050a06080c030d08 75
    0x25a00440c4050300402168034803c0c81d01520030104500a012006101c55882d051041d0315410b50080c014010600840004441c00c14005246000344401030003c4c0800120314443c00303110b200e000b001035a66500b001c8000c516900aa03941131000c8016a242109400c101a0700c4c1041e1403c2500268407030f1550007040c02c4055001c00c0540c2c0510000c401c00c8140421508084d003203031826900b494000c000c3c181401030040131030050a21300d01d50000750043e02c1c043c174100b02d0100c1c00008251140a5120b500007800c0003c0d5910800000358041350034406881d244007a84000c1030719070010000f1120903000300c0c103180517807001c441d109910031000403080c203414404480b030304281802c01c12250383c0703d10b400401031141d8000010144075507030005000728042d2082c01c08094022000700029464150048082c98100c0f10840c0c80c3d60090105c440024034680181c01410b003035880106a62408051242c01c5554591040074550300c01b50550960b1744010820108980c090320f07022403e9a200c00160092 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 43641434 1250 43640184 43640189
    0xf09050907030917090607020d050c030d081509040201270b04080f01110a0804020d0305070611030a05060d0b130c12030e01020f0604030e0f0112050109050105030d030212040219 78
    0x103000301040201065041d0b000485151180340384070080e0a56407000d03840b501a84008607003081d01000306402514210546680d424458821504200d0f0b50601007801c1c1002000d260f00829003190900800000c00381d5642000c6d4800e5811582d81e02d49a000201280c2c01222111900c0c12503c4e801002c64913828403140152000d00c04555546666485080d51040d4510404056510341120701d00d124a04008070b840c01c1c45207984030585e41e103440c2c003004400d4a0004003201070140030404100018950701070080050180ca0501d5164070302040d203e0b0507684014041d501c114a010b82040001d80d100180f681c10171014018a8034035103403860207841041d442c0d08aa002c941440100d001010380c003840005869a081c2c7c03d50300320b503000c41c010698441d41503034003c1c086030b101c080e20710003810314252841d81e100c0c05241c400010040c5041e6542198000e8100c4481140c031007005001038142080080220307002c6180452816507940618482400088c10003480341000080c50300040c0c0c00010300501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 43642684 1250 43641434 43641439
    0x7080105090c1306050d0e0c0603011a0d0c050304060b0f130f06030f050303040201030b2209020d061407020706090308030a0b040902060a020c0411030f1302060c07030f060f0501080703030f0905 85
    0x881c00d8445101800c82d0304042c2c6d50500840c108a00400f40030004103020150480140c402801c50b42000301a01200701401d2140c0081300703050012503a100710394011078039101c0b00ca4907199668201401d04c00251944140c00e94041c2c1200b40a0340640e0306c2d015949810301200010001c3d90300350350380c1d486000e01182d502c042c111881000500313007070080c04002180694402d8a00700310303601002042c001c101003c82105105107c80811018002035203070450b048444c401440004608026600d49044a00c00c0003007000d0009450100258140c04001c224050280c0c4c3c01d2092030720b0319558584000f88001800ea0348566111071842200391601e8002c401c6079a40145107984a11024030000d50303d542550b0101e124030b00704100c1c1c0f40060f81040440e4081d965111030941d46582c1c8155000c4040e00e2030380c0803a0450410020000e00c3d0100784007a0001d035101d014040400301c00d90070680181c4500c1ea2500343d590b86840010400f2120005440b02166032504149004401101d0b055800c2000c580c00b0a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 43643934 1250 43642684 43642717
    0x3020a09020a0c320618060106090b0304050705120109020111030c0307030e0a09020c0d020c0109050612040c0302100201140c040f0501080406020409051005120a1709030a02120604031707080105090c 87
    0x204c402d8400b00701e00b480ba40c03142101c2100960240c030300c03e9880000303219807004642806400d100c2c5064102c000e6500600078003c4512495a403c041030810401d0034240c00031765500c010410031983e000e401441146e5446006500708030580041645901c2a000d00800b0300c07003040d00c1d040d60f81d2114452100203105448086403540c0706410042e890341c003c00d00300d03001400740607014606903020b80c20b550141c07075001e030655043c14450603002d000004007a000796540c510307078800000180c0d504414a8140080c0b0740c00880c0a1080040c05185000e016105145a01c000d01c402c1c4841e00c1950030300e0084800074a008135190700d035410b05200a22440d00b08409842c1407004120041400f4011801140c0080e990400c619080e4501c25803292502c0710014481e440d0000390701b4280d000c0101030718480344000e0070340c0c00b02d12041e4001031b41c0010f0180c6100d0340d0b400c410200310501d40c000c2d0701480c02d4100d8035002002890400001498100140252885003044202140c980c1d04d080c0c0a990b90b012501c2d0048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 43645184 1250 43643934 43644023
    0x1b070221030a08070206100b0a030902030a0516170a06051f03060504030809010c021c0e1221040303080a0515040c08060307080c0108011202040902030304030c03020a09020a0c 77
    0x8503102d5120840e55030200e00e800022861251000403001e10400c85549411030090034807071440580d92244221804154031101200051307038050085001141c407400090400c0300c805d40000007a00ac181d0304c445031705601e261101003420f40c04a510b40c1141e901c050300003820382e40c0c1400da003200c0d0440c403503020109104032001b1040085a0340050f005901a0b1900380880da036602000e42610600e015150040c1c1117903102c200d58850100030450201802e0030f080c40d06d2070341100410402005e00807040303040e42c403040642c0070003442c2c003440b1258280b0401c84545810b040d0f0301c010b80358003405022440d6242d80c4900050f40640e9104a6042d0140020401d00c1200320692000b084c2e00300545001d403090040f00c1d400201d8040004140509a106840e229010780c0381c110b001d03d401010780003c0e41c0080d2036128000040c1d5041c402840650b22620191000600f1030052060145d51a0800180b8510410134600041d810100854030950300c1012042c007100d101079070480142c0500c07400310500920391201e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 43646434 1250 43645184 43645249
    0x120f08030103060203191a0409021309060614010e0a060807031b0c0506060a06020a110a1d07090e0105010c02060706090819030e0a080a23070309030b0f1b0702 70
    0x860140044040400041c1c02c80204a011159005280187c0858068410304541020341204c66418001400d02c601139803500c41c081c00351504d42d03408840182e50b03240e062000076030309001c466a0100a103007500c030000d0160003040007090207002d50001e20040c80c0006104522a4114081c40703c0e003c13625820b02505903202030031401c42c83c00c1c00c40d1103025034400101e40c0d0621103800d0f030440f141a40207102051994548a13584034003581e145030000410000441d54240c460010040641800742e015901e1820030001002c05107a03402c0a81b60b09686001081542e920003146488140c040311596606c016910b000002046441c50080c411000810303250755040d04080c0039040b42a05880078810b110300140d0701622401c8008000304140300c1441000c0c0038034840c02c40403160010000c000d04a560301404045e459403c840011000580740d00303800d10070440841c8240d9000f00a590002000c1d0500306c9a29080d00d0b0900c40c01104520301185079015546c98041c2900220302402c0c00a03a4141034264 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 43647684 1250 43646434 43646437
    0xa030801030b1e010605070f1a07120e030a05030c090405010b030709080a1a071106090a150e0a03030b01020312040b06040506061c020721090819050304120f080301030602 75
    0x20645002ea1440c000900380c200010b200c080306035544540300010b07800c1c4031080e00c06030858502075620202698600c000902e0341c100b5a0901d4142001c80c080d1464810002001421003101b690f442e036080c009018000b010000660f80c00c901c003401c1039900d994408141c42e2941c00307500001c6520500b040700018007280c180e0300443c0581c140d070743c80f01303003072516640540d54940944000400b50380440c800403154980c070664080d001011450100c054420700c180d8103140c40003d40701d8030ba41d0f4108480500420035198181a00350070510010301846503201e03211603c481121030003030181521103101e04410b80c401d208039031480141910055940c00c00382001f42c00301c0012240c15010780d2604d40410f0885ca855010781c0c5034407a40e01d0503038280a50602c0d405c0b010b07400018049032601c2040c02d0040240c040c44004428150300741e520032404520307001700c0c03d15014140e00c505c0000c042c4070740c41001003031010085405030303490700f450411200172925125a0005a5400240a07000040004020000d0540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 43648934 1250 43647684 43647689
    0x60f031005040c0509130b0409080d0b010305072c01030219030f060e0c03010b0d02070602070803250203070b041103010903050d110310050f041103100f0b070c0303080907080a030801 80
    0xa60803c610711404105071100e2162040c03044d401100b03401050200a665000001e04c24006007000c5608030344c5654840d5250000010291a00e480f8079080c02c1c40d50f4140b0500358040c0305403230241000f15800f00c40c20400b110f042504805201034030311308603159000c0e80441e5882080e0040900c2c1500755a10014001d000540310b58481c942803a00009141400d940414050500141c0c1c03140385034a03000d04400154040300203a841c4136002e20841d404100c552020706501406140150f5132880c00315611030500134910059000c0d020245803c4880d0b0368000141d81445a21202050385034a0b036040c0061031006049a89500d0b60038a4804801c140d400381c003030f15001450103c10b200100a1a00c072403003500003122030355404640309800300690703d04030007003a60300003000d84005105040c45070400201d6000b05c038484442c0d2180d504c208030311030120b1184130081030b036a100d880c1024140d6030f40a02d401854072020341002140004550714034024800340d001809150215100002103283c081d203a0802407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 43650184 1250 43648934 43648939
    0x20f030a02010e0712110904050708030f09090a05090304140103020424090603020306011b080d0606110705010311030406020702190e0f0f04050705040f060905011707080d020307020d02060f031005 86
    0x6070001a00d110700e14064180350764400b10740a1b24442d07240501c0780320342004200340d1302c1c0e2041c5100020080b805000608280c0302000f1030a9991405106001200340c0140000254078038181c10000c1504000c026981600c111100035503000c010080124040e020f07581084192441a01c014007440d00c0007a1076001010480d00c0b05000141e5401e0107804900040b070700c05021850203040305156100342703000060700b2803007007040f5410060003210720b60484405400160200d0083c081c851803200040040900801c004d02e03080c402401005041c0560780400380c402042540c000c81c0c41021503a4480780311040c094070110301d58500350369511a20241e038081c1e6000a442d80110302180d0000064071a4505c260340090040031200d2401e014400142207454405000a84e5440013040c1e0b403c10380075040c02440e2031500041c000d0081c0d10424241520b42d07001008550001a9030710499401200b92515250100c407009115001c40c00032604c2031288045904134202c00000304078040051420010980303005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 43651434 1250 43650184 43650193
    0x2030f060a0e060708061009031b030636020f030a0809040510050607031d040204030c030506060102150103060b0d0b0708041a0601120b0609030a030804060f020f030a0507020f030a02010e 82
    0x9034601e00fa20303024242c2d49a40060060b00004215050408418044c8100b61800e410320300c0e582d48a030b503c00150382040807a460b9412204006120071406030481a1548410109800c1c5085403d200c1043c480d80d0454a50442014454155500d00000c031000c410050141d4064105614049070240e00204110f88250302c0c000220380711448691501c1c2c1603800240041d4601346140c0c60680c0c8004c8401810440e010503800c01800c2600c441c00640015407180c903400c00030300d040d40307095030078150010060784c11035102c280c2c8498070142b90000d00d811a03400c100c0008440e0925800f04010030390006010b0140148501400030040e0b0042440d88070324014a1404580b1404e1a40c03c51020710648240d03002800325049421510000c3c2c0c820300a0020040009182882c0b410100381041030050059010580302400c100134041c16000d01c4210114502d408c500d4240e0801102c0c005000103040350b9110f9a840700010000b80c0204040075040c41d0180889848502131000240a07005e04080001d1a004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 43652684 1250 43651434 43651451
    0x80312010e011d060f0310110d0f051501110307020402160203060a05090d030b0a0e010815010602120a08070302072103060608060d0b0408040b0304050c10110d03020f0702030f060a 79
    0x50070102094414115642c504090301c424040145600c074050382c01e68580950034800d0002c0c451f61203003440700454004a1030321600402481c1040b83c0030103a02070790040c1010100180f0b00e4000510700c0d2074180c2402c1007551510302040301403643c040d10400a4210b8400103082c81030556010200805034403c0b0b089032060b5440210308015030300d060b18600740641c00800d140c080340340a0381045c552103401502c09910070b90b9408094007980c9080e405150160000315030604541c40804049000d000c0c103000400c0035582c20401440980b2a10360340204200210307010960b41c500c40c0d0101c130741568100f5041400140702010303e00c48118600e440401091400b44001400d0b8014007403244280001000d0040c0304020740c41e14668844003c0003180c01c0b400030000850483c1d03103d006540510700580003001c03030340300403010700000c130003801000d10138011091240b0100000000b440c01101d80c50b07281c09600c40c0301070443c5085601681d400258103003d0b20b01d240c108010000741540c491804004207001111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 43653934 1250 43652684 43652699
    0x130e0906100603022b02090a031a100303080403050304170a030f0515090a090f020d0b010303031a030d0f0302090a03050c03010507110303070804030c0605010312120204151404080312010e01 83
    0x1140305e44120240f078100c103030b1000d03103490095545801e51204e0300240c0781c14203d40000f04e0f80310303c94204503140088840c1c3c0100150010080f00c0e0310a111030369a124540c1991805068088000c00003410003400000103807c2007400781d0604910030561004075141d024204001e0041c000b030610216002d40b4080000d0611444002c008911400c0540000e4880e00c40307400c100e0180824100139100180d861400c0801a101c1c5805050b1990050821410035419842d0045c00c0e10b60441d410405101d009406650701d0380d0101f07a41051601c1b9040495554400440690103400b8040c60300c0e520088012001041c00303070200794618030001c202c0c001c000c0b964030540b0503280f442c0500803443c001c0d88140300040c88940a201d005401070b0003420851b03420032080d95204180d071401d80007110598110000c5030092908000e010b44101440801035050a04140e81c0c0c40890200045090810144522406140a10004450140240030305803669054030319090500c20f20300384102e000e8405d99000008058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 43655184 1250 43653934 43653937
    0x216180c051306051b15010e060d11010e0102011508010e010f020315060f0d05010f0608060312090f0a050607030f021606020a08030a0e011a010f030504021005130e090610060302 78
    0x1050308070500b06400b8244401142c05800a0f003c541c40600c40700c240035a44401040f451682d05c0340380c1e01c0198550705003102529800300146c0014004c103410322120f00012120480020b6541c1d007860314400100700c0b01d00403805041171000140c2c4120121a0201d0f0140e819040781082c4100708009020540e6892502c00c12031104464102010408060048c12490084024451101070031022401c003000c4002990442e6402c0c1d001c0e20f445000150b0420060390861802d69001904038003030000f07407050710590200c0784140500c0900c10301044003680441d0f03449070309074005400003400300c40d203070325072890040c10b00c050780d4400d400540314528400c00200c20040591003510b600e42e028202c071014540e50840c4982010b0204040544c443c140b0007800c1c0f1342445058a05480f070404403010410500002d02003a900b900107a0030142850104000b513100d00070084d54202d8039242a9580d003044244280c082284c0307402844612142c8818005c44000010f441d50080c020f821801c181b0f50355401003a8102d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 43656434 1250 43655184 43655197
    0x40f170d060f05240c0d0201140903090a0e060307080a06020403020102210703030f020c0d12060603020c031b0f1608060c18010305060109080316060501050a030203100506010216180c05 81
    0x4540ba45804c010504a01c80107400c1c50040045014140405400f500b4100643c0550b0f07030700140c1d9995070110780303081c0b448041600141d15102551912510b400411f00c90032050183c10070142c454008101d09450410900c80200907070810341382c8009692030031002039449444181c0c014890703e2381041010b407800b41554018003070088a03d2a00b02c00d5541980a01024100b5245c00f039424000580740d800144140c0c50b042c019651040410301011426038115820717030308200105403050241018200b000030849450822000c24608070b080a010340504c2c1691241c0b60a01d00d0180c040b104000c000395100d01e500b80c40d07104090b101299500350400d0010301900301c0c903c00c2e81d84200ca103001154001d074003031074015a06141030075000c0c3d2501100c1d4034640c440001c0e1480c83c0d00c624882c0b4184100d52180c00e014bc00c00719070b855030041c551f80001e42d03200d44107a918040740c1d58503c04140940e00800031720380d4211206010004044d030b901380000c0d00c5400440d0703800c5249c0c10407100504480c4510200d82c132 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 43657684 1250 43656434 43656439
    0x7060f17040f020d06020c01060b0a021905030405060f040611030a0e27070e01030b04090803010308160f0b1801050403020706120e0102030c071506061205040f170d060f05 75
    0x1140c19000328008580501900903103010b03401000803000350719003407a00e2040b0780c0070301009685ca0703a04094103400c40d0034590007880d4858040c41000d40c002c0d800b1480201070817840b060400041c442d410568118441c0f540b11036403091000138103140c1080801c0103401211281c1e280e020304401440f08550301c91007628a40000642d41c1c46000403d03180c200c81c13205004803c0815a05521803410800340303640700a44003500405c06c4001034a80c40c0da80340c080c180001105a5060100403055901c085007400107000040030802c010444503500c1c5404007840f01c000383c004106004820075410b00d0816107a0942d11181d503140a03020345d0101c280c050003400e01507070341a8003c1c810180f900d40c0071503e40100c1411458116102d0185800540d42400034602401c0d03c02d00310781d40c60701c007441d1200b400c00c0d15621450740035080c410304111440d0032000b1081c00740c00e41e45000c541d91741c0300e00d0040d01d00742e24140d0091220440040c078820200405d00641500c01d210704040010940790719034900803442ca4070a40e136 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 43658934 1250 43657684 43657697
    0x60e060405040e031606051b0c06010b030c0c01020a05040303090e0f0c0a1b0506070f021b0108060d05011518090b01090207081e07060f060b0d110d020d060807060f 72
    0x31410554807216030120a41c1c00d80c0c0c01d0000313840c41c01e00c460041c071406507000c507212000c0c407620703100359940e00444401610a844c900001e4500264440ac014401c020240802000140c440800d2008542041003154000c5503900003420014000390480d02050300054030703091002c25001c90030540b0502032900f05c220300106035922800c24440b40d00801003581000041e0744114811030074400d03ca914544500050070192501540003005822010b20315000c42d40030000003c4c01000803407160120042c00c2ca0100c60664070035010a8410210b10001000f41d0f282c5140512402d08240b0311005032032049100c5550000400211025610a4540541556001001085144090b07401000414401c902d05401c3c10368503d01c19500401c2803803840d1514500040c440c08000782840303400308201d203282c810800241460209180c0b802042d11100d080ca64518506521008000039a0100c142c611820b654600c104202c40e00604082c1c400ca070041d124401020030f155000b028404185840c50b83d410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 43660184 1250 43658934 43658939
    0x2a0c06041706070801060e090a0216062304020d060e0c09090607121104051e0d050a030201050606033606010602010204030c0f0506160f020d031e0c03050f0d15090e07060e0604 77
    0x40c8c0e03404003801d42e010039942041414404c0c19a94034489140d07008103000541c900441c04a45028003619296112004000b0100001a51501c40082e01507400081c0041c2d0030448900042c5091074900c182030b03202c0d44010400c0b98070f940000b8032078465242030b61120380701c004180c20130050701d00309030b00c00e424150140814401406d000302c01c0001c105002d456024034880a002040603140c4000301960580c00254030f0105043d0240282504240262040c40c0f03545000c1c0e02c0f0a0400488101c2d080c11007d0f50038580c800c4481c213100202000c5a100706455003560f443c0e00290007940641310403580040844c2e000600c21a04c603084204440303001d00788a1615510310480c103035003a82d403d4111444c0e010a002040540c4807032140e83d40117031198950316000448207583c5002007100507028410070481c1c00c05080003036886810740b800038412a003020307103490400020710080c0c0311221950442440d12540042c005c0f4481e0801d0140d403070741e001642e40180e1182001c58035040100074880d0062000c1208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 43661434 1250 43660184 43660189
    0x10f050a030c12021201030b130b0115030e060a0b0a05011707031d1c0324150c171209030a02031903060302032509022a0c06041706070801060e 63
    0x40c2d8064022072038540b0b4181803c6001c074080340c2290b40d0080030090740600500400420121041c0c025480074001c1480701d41603030741d21284000500074003280c11041d0000441d07040c040d03000500600c50361010f4840754984020440020710320154003030f01c41c40c100c0c10001100c0d400f681d06a404201000c02c42a0729545940b0146c0141c8099025041d50b5103084940901140042c0210700031440c801e2425540d03c803054000a0a032590303c52000c40d120805025030310064104080c0c5000c0380c0800c95285a1080b44207010b4421500c1c08002410001d00d01c8207c01012084800500c00035028660700e10042e02d03000c0960340e40c0d02443e0703501d2000d41e104000c09000c48014400600d9910003d01c0c010032103a44a42c042402c16a442c8900f240e600300d40e1000410314500754000710090040b1a40440c2450302c1503907460401520130049110750304845110080c564400d10849400320341c0076186039681c039500d01c0c009880890f110100040ca01600d400b0070982e61003402c0317042c12641243c0e40c03c501c0d40b0581d800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 43662684 1250 43661434 43661441
    0x20d05120f1003020303031e0601050f070620182803080d1e020705010609050c160c091805010506010201090b04020907020c0a06050a02010b0a061b0f0206030406020307020c010f050a03 81
    0x511842c5000ca200040181d4040000314820b1a5141e11481e001407144010565120060811414418180401060200b03540140d030300380d940092011903001c20300340a0180c0c80b40742400b901c0e0241d030000754040c0501480c0d001445075110540d121782c0e0950b03a201401c4030300c0f0356065220400083c96076040000c038044402401141c18610b80008140600c444202c10316210310451054103900030032007600340314081c8a50b80041c855001c00340464902000c5054641c810400c1505101000d081d4410a021340420548041c0c4100003007080005c26103d400300b06488141811100ea40c20140080c0c0c2c10751040c0517244542d640001c1350301e00e9446644c2000b8411000400c0041148100c1076029425a00d0401d03150040c1680d807525503031040b42040003829102070484c140c0c000c51036085c0421030240e00c0880c2100c400c5150040070f48200d0f43c0d16140101c2d1b0440f0b40b01135030002000c410b00040c081990300030b5001d420203400300d40b145e201e05801903030301c2002d500d0550003241c030603c00050103600030741 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 43663934 1250 43662684 43662691
    0x3060112080904091101080601080903090409050132090a020a0302040b03011407120e0105060904030e0312030403080a2f0c070506040801020409060b030907140612090d020d05120f 79
    0x6601420518201e01050031111046130560b0300d109000c021100658100c24401d41025081c0f030f04082c01c0c41c02c02103041c1d0340c1c40754900880c041d90f42e0b42c480c0c1c414031200b03501c4500046030705030144042c0700c561400384909000802e98111416808400720b13034481c0380000e03101040f80e405001c1c4000c003440e680030130000700400d84586406549846081200100c07201c0b50318401e00302502c448500d80700708020101207548904801e2800d80c900f2091121540e200d000041d44981e142ca01003a04400940210741803800e0040b01c01c00c100e0001c030610007010f030040e0b44c062007142c040c48100460603904c0000281c84092152501d01d80c0c080132072041070070384c1003001485044181070440d200307590340340003003865507120780d01c03280c0581d501040034031104031180a10760081005400c2a400c505024109035124891440b0b90055100300000114090300c4080964251024411070700060307180c0312a00b07071344900350310141a005000f1980021146030103102507465500ea104024581c9598050b860301d5400c6018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 43665184 1250 43663934 43663943
    0x1202040b031014010c030816050f1612090b07020904081e070209060a050105030106050307030b090703021c0606050906090414070507050706020d050304060203150307121b0503060112 80
    0x204800309000c0344240040d401110b080c00c60380c0e4158602a0a48a88440725040074104000d4900610109601c0100160031007240b02c1002c2c5006180c030000d603000e104030480700000d24000b00341628146400790841d00c40310f0040c0100d07101c2448200742100e00080303030b001b1188a81000e20a1601504041a0b52540148100d5000d49000307031030404884241100002d80f210741100041d89011804c0928044d500100d080d507003d0112820180040c0286c0814002c0c0340c00c1240200000342d00341c0c8039402030010842c016124661b5070a01e01c200070003070340c44843d40c0c0041c1a964890048102c1c968481c5808840321031b6644c60903c090303c0d04000c0142e00100f00264080e4881640f150b504000300d101034001d44241d01e034159104520310308641800c0065200030203642080c07da20494582102c03c81e0b13030182e031050005035a41c2d03803800d141d50900c4200000c0c40d054800c02c40085011002c409144c1c0c0700c11b015110400d00d02d0281d441d02c0c00078181d10b0141f1034054001100400080c1c1d480484126400d00c01d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 43666434 1250 43665184 43665187
    0x90910030b25080604060f090b21060601050319050403050307031b050d0902132309150402100320031f0f03020108090a1a071b1208060307050901030503090108060315071202 76
    0x1f40e01180c0203180d4503401000e5281d81d1400a420940b03845201260104550410f4005400180c1c21090f01c0741070041643d410300ca0000b001481507e0300c90b401b142e24441c894801c001904017070400070001c0d0000c903007070004a0310704a02005034440d1445100000e03c034907517485290a203c4411f004c003a110140040703030050b541d095002d00900d00c0303000e05422001d400c03402c00000d02641401800c8403002502514403600907100e80c03401030b420501d0b400d9200b41c041e100e804074100041c608070000e2000181c41d080c00300071800d6542e02000a90021030055162a40e440c800744074a882d1280c2c07041c60351181002400702c110302000154050320034140d0040008054992010203a211b400c4080740c142c4e105c400e1030721441d00300503810350085205036002e855000344054a41b074540d0b030a5121032501c134452081c000c07141c000641396901000740402410003d4843c03106960b4900d4055607a4203e40034840c00305160f140021182d00700060041008540140c0e070390f550b40c8940300140c4055030040d5482c3c203203640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 43667684 1250 43666434 43666439
    0x60f0902030703080a0c08040b070606060c0510110903060708040605070f0203070605090102041707051c080304240e031905032502030912250b040504020f090910030b2508060406 78
    0x40d100c010300010300851009c0355558040c1e1601c0802c03101c40360007000902c000b0082c20390200f81c000400046c0d2810140000413078030701c05800707030b1302d64080d81050a6040c03280c0e2042011aa510032680c6028910515050149841e2140107036094050b0604281c0182d00900c1034602103041a003005810507803d0f8001840d16440f1281d8603110304481100101550010707804004c203090800c1900d10042c0c000020003180c1083e561565400e01c80034101902503507034881210000014110041c00c0e20801007820040d820100260310b8403504a01c09821318600a44081449c3c43e000b9000c6901c26400b88040080f2031410322400403e070102c01403078004601c02406015041c3c0c99a443c1512075802050050a50442c101001642c101e075100c1883c9140c4130601c030402c4440d0960041c0d60640e4411100503842d2140c1410340f99440c0a00c00d00340b580200c04c6014080340c09405c3c0d9040056130300840410306660740e181004880100301c0309014400c21402d40d0100e2800d4400c1f000c1070380194000f000031a10b40d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 43668934 1250 43667684 43667693
    0xc0418050109050304030506070201060b093109020a150f0f0315032301060312030c0314040b1e040201020a031d1002010b10031109010818010906020304060f0902030703080a0c 77
    0x2c40080341103c0c0740d800002c1c10f000b4000104007291340214a44000c1c030400f400c2006c0706045010305402e8600404500d0911003900020440081c5240070700d0000c000c1d00c50490760010054030f030112081c0d00580d803998011034960081400306001c07520300c4e260700311040e01810080381c801d0400a40d0400300b59558142c410740f903071610f81c40c1c00218016111920a0f40c03014015900d82540540e5005880e0b241590800018000c04005070500304181000102d80c1c0c07100d075054001e080000c0f248902e021954081008002042c980355004040400c408846c80c0c0780121010440e4405407006805607000400f0036000910550010721f51304209801140305200c0c103004905074550010508015035110101165a42043c400700e032010380706450f0030b10041614280e50051403151a4206040008800000d410041241c0800b0610000740008010a0301c031424124001d4000392801c032482ea09105024030801820b0089014140e0018044c00d000c030304d15500e64a4940c402d203414030921205954400204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 43670184 1250 43668934 43668941
    0xf030708100903030b041814070806040f030906080403081605040503010f05010806091603150e030a0c020306060607050d0e1c03080411040c050a050d020405040906020a080a0203090c04180501 84
    0x40c074141021690310160b240103401d440072201c21030300641c90040903807100701d01c207204c042c12242c205680b0712240b0b040c1002030f410300b44075400080346d501c220707000e100070080086450584180603590301442d60703403249811a40804150303805000540102c02081d0590121103102031451050304120340b815555001107030035160641d03c0e4a003265a00e03c01001070141c10b025081e48a80d00070081d20211038070010840c0780518500ec046c1131408000c4107640d41e188a13078003401c030040000c4100c07600c0f696a008014a19a40c0c26400c81c042d000d4803012078040c4c02d0110940300701c5541715010307107000440902e04558031140190380c02d9101962113441c5a4030262585524202d900a0b955203c9500e4103003403101800c0507021001b40501d240014055965a01c01c0a5461890951a010b03a0300da0004c0c0001001e40666008940d2192411480908000196008050780000c40c2c0366100e2598902d802041280022240608140c2102d0500c8140745003942c00301a42c0d0309203554004400115407212401c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 43671434 1250 43670184 43670203
    0x3050a09030b0a1d01201602060f040f051504060503041b0b04090608030a0c0221061509090f12070c09050703050f0c030103030c02090a02070b0703021305040e06060f030708 76
    0x3169207039144d414810b0a036001c0e10031000078400034022104803552021100800d00d4059480c48804991000c0e030400098144540c250001c03c03440d162030000713207002800c1e442845074084034841c4072800500c3d824003c00072082c24039001c07285030402c0d1500c1410f840ba0781c030052085910440c0d2140b0001608103d20741d1101401450050076222400c055502e8221061900408000d500500c60350a80395403011440d0880d03681a03d540080683c614020030507580103c21304101da00950040002244210258152042c400c5400f00c5c09900c81209082d1a2620441c0c4045190016650582010501c1009018080c0b060601d000c88c10340d0b400044040300e0003516000c0000e41c40d502440080f8030f070110300f103030004104100305256526560b005032440c0d2003001c00a000742d030100005007030a4400e6041e560850741050f9203031440c0c6800700e4000c0c001d610212103486142018400071809080600c17a43c01454a140d000709501d80355042084030f44148680c8481d07051143d240040b50302c1000b231000245 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 43672684 1250 43671434 43671451
    0xc23030405031002070b0a110c0d0210050c070f08030c160b0402210718020d090302010b090a090503160219121a040203030a0309060204050a0b09040c020601050d03050a09030b 77
    0x45a078281001c00d41016207038004011240d006208000200e5281c100d00d50300041c40510001d00802e0811f00c83c2c2c418007802210707000b9802000b011032500e54000c2040458032240500802455841e6507580740306024950019100d01d0a158901e40058050401581c2101600751800d0400a4504402090301300490040b00c07100c001d42d0a0004600740454080c1244416030440c040740d440180d02d1039511100344c801d444083c040a030341aa1400c1041c0e040740d01401c80f440f028000344a89d410080e000c1d100c0500700704e015103d0312000a0340184d451003200c185a43c031002641c03424271500201600c0506241c402d9034000410004184517100021003103004000482c031082c81400d03c1d09007242d0703004000030340340c014006101c10000160b50103c112045458103041c0000d88032007a0400ca07000303000c0c030341001d60013405802000c610081800c000d004012002c540500590305204030403621b44100f8810035810501c01d031303803400001b8050000b0b402e5a802e1450000e00e010303603985400210380320a03904c850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 43673934 1250 43672684 43672687
    0x12050f0105010918082b020901110d09030f05030c03031008010608030a0f180503011107021201060303020d050a030e0d090503010b0108040c050d020f03070e06190e04030c2303 77
    0x844160003802450b00501c40d1440c1082040c90002c000b00c003950028800400950f00000c01803005d408515012000c6a00c0c41a5074448814a1a410b00203600c0311480d2800300d4038130f0b249800d035002c00280c0c0c0807101c0c0c03e503690590518079650301e1034201d43c0050b800316054042030200748000e1800304007862150b4440b0481e03100252424101d582152000d0b000341d00190802c0242041e810f0b0030010144402116107031035400d60b0480c104092032584c894200d2941542403001f401000440034020f46a424022202003854079100302c203141c00c130f500e00d200090243c0c000046101b0080e0148028200104140c01d010446160000d45c0900307040c1c60700c0650b4042035141c43d040c00700d41801d11900f0b0100302c00b828014000e04003500c0c0d8100443c45442024031a82044d40e00c00210b480744c0907480100007000d0204d40c021030705c80800c081c1d81c4204403090740c01800034101610880180560321011070b080311020000741e440b40d88086032024040c007005c0d03c1e0042e14003000d0701c0c540c40ca60400c00e0100e101d00041c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 43675184 1250 43673934 43673953
    0x901060e010605040b03040809010e04090809100503040f0209060d08030a1a1012050c0702040203090307030e0a0303080f0a02070209090c0a06030b06030115020c06030709090c08090a0201181205 85
    0x810380c410040e00000204401031100b070001034880401c4035000303500f010019454410711070040321a12810032a09800a090000038001c10945c4030140015102c00c948041d840c0009242c212650f0004a0f0060583c001001c84a00541031041d6201d8112001820800c50540e05031500784407580182d6111100c555a0703200142802c402020900381032408403200340c600000420010300c0d11a0044900d4401c0e65100c011451411740b41c405c44105560260066461f4a4080c02c29a00d13600410000d0b00440c285216480c240d2511900500540707a05031110540c0383c40700007031562012001001d00c0c0c403031075003080030402596880c008a4410181b8a0040090006040c1030000280d820b6101c00d0a040c181403203c07907030b41d03070f0344043d05c0c1503482115004580c480a484200e00e844141c600b11034202c400001402801c035801038201d015982c0015050101901c070b00022507920340120b42011007500f10300350074001584603a080703000e102d0035000e0441c034030307030311100810301c5001c17002c600700d601c0e60000b5440c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 43676434 1250 43675184 43675199
    0x41820010e090408030f06031c08010f050301020f121e01080a050c040c020d0806060f0406051e12190e0f030702090a090507050607140303010b04030516061b0317090106 74
    0x750360030403000b41c802d1046414190758076030103400042e01e00b031360000c02c01c0300103180e0b6201080164607010380b0720950039809490038405000350a0a000302c00c903500c80e611011410381814000c41d1117a01c0703400130701480d014000b48144103119010f844e691608009200e051412404100314501801180c2c0207420490310603d042c0e440c003021069010301642c01c06d40000c54450b0042003001108a031400c1c120456030310100010720074400e2400309070101e440410040b6090354443c0203040ca0806181045402c1c800c0711100099030300400000907203400e14940002e8190f140c0e40d1101010040400c0701066a884000c41c01d810300400b1200352003d9400403d00c03c00f51f00d4045412a04040038042c10840d00025488068840182d401003d000302000240102003180d0900e45400308001c02080c0c036100c0d40c41d0b0300100510f5000340300c2074840340b043c6581e445c1c84540554445080b5529501c40318030110700100112008001550281c0078880005100d00458421300c1a1600c100d0461000280b02401c00d5034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 43677684 1250 43676434 43676447
    0x302040e0708010e01050d020409080703080907080a0b0a0903110601032a050310020f040807030b011805060f040c05040b03040c0e0c0307020a020d06060b07050106030b09030a020c04182001 83
    0x9240030805104010009004c00e915a03d040d15001e0700d43c0c144102c100d00110b409030101d02c0b00104502e0300086c0081c1450381c032002c80380c020414241a1002290b9814260359982c001c500c026100d03824500100b0f656028590005112a100e400d2241d051b452180340305052000980c42901c0c28101c0411440c00d0f50302100074494a0f401c8180038958030303810300b00402e907640052180ea2040c1a80024400c42910710407060f01c00600861003100c2c442030312840c10708422903080c8207050380c1118217001500e00c000d207401102e114410144c41000e141c010142000082c20034845028180441048081100c0da2240001c42c0310354050702d0f5074081d003454500000303000040180007540f6500280f09200f20307140e003c101a03c5254044a080b0b804000d581040340040c00c155005581c50880007840c0c0082103019004001140d01944030140540d441d18080d58a9204030307183c400068103c0e0303030b00b040d042c545944010840b840c032868150481109503134401c101c1c6a01220010582296064000c0e59a8080c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 43678934 1250 43677684 43677691
    0x1050a06030807060c0924021506011d01030e121e0c121c0f0905010608010506030706050705070503031303060506151c090b13022718030408010c0302040e 68
    0x10100005403070341d11601c401e80240d5070020459501d8a0041e02c0142c820b0f0100070181c00701003501c506996403e06d200300e2140b00b500b42e04001d4000c41080301c0209030b841050318810101a110040703542d903890380a00d08503101c085050f0501d0f940701000e400c0c83c0380c104505c0d000c4a0104030269580c964001e0500890a2803404c10301c50207400300507092000e00007044c841110716104801d40d840306620b1400c41c003a103420041d80380704107150900070740c01013605801c4901018086c8000300303c01521a1011820382d03c080780c80c43c0e05030b80924810000c40b44507000900001c2e01880a8602c0c0d252034400203411a849101c1510701400490024800c0c080d0b98451140c102504035040d1401058507103032400c00d8001c18075a0007402c5850129802242c60582250510740e6000c007d803955490f0140070321a41100080050380103141007a5158185c80004c1101d0341e80c4040360f0f403c040b0644d500361b0190f511f1075003140d00b04190f00050000058030402400b40b80b9002800e52400368989007840818406080001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 43680184 1250 43678934 43678951
    0xf030703050c0d050316060614030d05030105011101150b03010303090b030f01090905032101080c06030103050604110a15050a1b02100e01022506020706020a110108060d02030d020106080105 83
    0x950040001030070000b20200e25410664031001050181d0400500b1402000720080c0c4801c05034011404000d116440002a07404150410806280100038035542c1e0042c4144080880c00030801442150700440403030110f516498004607030080a103070380c1654020540e01103d08c0c070070044014801c164010f000e180282456080690540c901441d00690414061040482e41036450442d0f01c1404030900c11124181070341d00701a00c1100c56030840f0401d0020074410000342d40140010361483d1302e001d10450b8101c0707410000400c415120390312070290704031451400c3ea0340300c03c01d04030000785054807c1e100e07640e058081e220103885070113011025040782002c4a0303c0d0001d0010708400700050361107182040e0703c0e06c3d02c1d151004058842500503460700f080c1e40704910403034000300001d0001000d0340d1046002e0701e0742682501d0496a035038905903600c00315620024010039072403102c100d0a520480c88181c0c090402489071220410b0303070300464101508801e0010041c0d45601003400000e109004940d00211304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 43681434 1250 43680184 43680193
    0x8040e04110d0308041118091e01020702030318030f0a060504020103050105010c050307060c110726030901090e07051c0504020a06180b0d150e100b03150d0201030e0106060e0f03 78
    0xe070343c00511450f8000c100170131044034991688490745441e0019140b0f00f54882210310213007800c60b0015510616180e810b40340c0e00c81181403d00411040c0241c550155000d0011810000b0109010705445000e22410780c240c4240c50314043c81036000c101e03130f1000358003503400021f03039041078000141a03401c141c03c994140721841000e1400220008100c0301d640d030b00304070002920031440c4412036040300184095011481199804200c0c400c5003208804a07040074076400c2e880d007010450701c2c2d490f80690546140440c0814a04000c000b00d1580b58950150452810500d4005082c0405d5210503815406c8040c1640c4ca408000441c00c020383c068001d088541044043c2c03000103401407c55041d180a2032161100225242046444907008804c83c000b0400d2003071411343c1c81d400805500c2a0846001d034130440e00080c001140c60721002102c0c010302009540c05003d61510090028020ba0100c080307040543e80c007041c6807a12401c2c450031026200542e24040540800c00400c030703003089007903a0f051207a000b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 43682684 1250 43681434 43681459
    0x1404200907090302010c060f0606120510080606010c0f050703060b041d03180409050f030a0206010611031818010308030108010b0306060307090e0a06020a0801090f0c020a03050f0708040e0411 84
    0x400c040b140301142c0d424070300a01002841d103003000c00b402c0300303148000c100703410050003040c02a041a80e03560780c90a444820000c40d600c0c03500c41c018800302845011260382042c0701060700d552190080d0440c00d07004285c040111382c0e156a51602d806002c0d842038518a9427448404007910740303805200d682ea441030000140d0b0ba002100091380b40d01c909000d03404102c0401c4071951480d15a504100700c21600807080d41c040c0c81c0c1e04000c403512a4071404e140300041c080c0070004a01d150080142c1c01282c103c00b0002c41c1440300b001e25491400050030300c0c881d40240c0c01400c0032190001400f40d240a113104551482c2c5952400600a00b0344a10700100d40c405d41044042184075100010100d086858030b91000c549200401d001c1801c000540744050170980c000180c00034550307040a00a030480d0036501041048500303c0b104c1c10201c4120800359401078000b40102d0b0042446200036103070380785182840301d03d811407645c1c0c0c0b038505034095071110740c2c0568100308000500c41001c042c01c4400c0010b0303d1040500c00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 43683934 1250 43682684 43682687
    0x30c0f0f1410030f0b0409050307030f02060f01050103050c1204050a0203010b030309150702010519020109020117010b071b0504090605041a0c161505180c0114090906041404200907 79
    0x380801800400c165030b400713045a0340075068200c0140448050800c1112000c20b05003c2d80340e6000c0f0300240c001c0b46800300d407104184c2c8001040c030320541c8845e40a00881c7d00b000d0044010b800c0c094a8900c2c00d250500c1806e698054a4808130b01443c031890082245031242d10500d8252800e41602c3c81c1700c1c0d0000c0c4102010381c0c44030541000d20350800c0c0c0ca10b50355406c080c80182e80c14003401c24005400410b002c40014615015800803840c54001d07254280c111803503484815a8600902500c00d00f107600340503810000311415801c403402c0740d42c210034140d400e460b14040b408441d003000c410345a690310740c02480144401c9002000036856411031102451804402d299428421040803820201c000745002e418001d5100c041346080d03100c0d10041c0040d091800d50041c016440d0740e103121060040341d402541c40e40c018031302011004080004039003454210f0081080520b0000c00c2d41c1d4125441d1400035589210400c01c0b24071862082505510038410b120600242041f0720142e50f015980c030354117000809 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 43685184 1250 43683934 43683949
    0x2010501080d1407020315010e010306050108010504020f040902040905030307020a0b0901060f0303140904050f01090c0e100c020a0801110a02070906050904080703050903060420010813020910030c0f0f14 89
    0x82c80440003c0e68a80280c40407910700590703030810f500400100f900101d1100403c1c540541201e01424003400707541d88501c0c446088900503140298031542d80c0c000e01a0301d0a16400c43e54540340002c1c00000c0f40e081036109d03641507038030881e1540010707000140d40c40c0401c031003522550380006c1d840c03000b088450305000480c4103c003e903001c003909103c05000d10301e1581000c60101c50240a02401c103220604042e003401ca1598420701401040c141000c0041d01910311a5058044c5504010550801c0c8010410b041d1800c40500301d0a030707009019110003043d000800d0084468050302c80e111540e40740c80c1000000c2c14401c25401c8048071604114040040703030744000c8c5043d04a5003055640b075898280b0f10b01541c9034818030080343d400d40074060412082c48503600c82508900b80089020044c019120f0044071403641c02c903006005420000000e60240c1843c1455560094401c10488215034032910703048400c56942d4000310500c2e40d890341c2070195504d0ae9404000802088120b25440b404c14000103800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 43686434 1250 43685184 43685207
    0x9080f031b070b0f04051002150c1305150c0606191404061508010608010b04030206040e0601020a0818031c081302130c030614060304050709050910061502010501080d 73
    0x1038106658030003006450900034140240f40c001010b556854540608000507045071056600c43d881910900100b1030002c5244a140400784a54a10b180c0ea80d207000b0700c1e2600120f84040d0941e4007000d0200d12525a0048058038900803d1030139199000d88600c1454110020000c40c003170f40314100b8941500c062200ca24064880314410b914001c83c0c0480810007e15203544a262150040300c0c40b078508039081207140f4183c5100f40c0d580600d23607803620300b50300c01c5119a00c402900500c00700410020405c2c00b107030b01900064144140c560781b0035581c8400d000c9400408001f4a080c814a2103030200303140400c070b042140040c480044490411520001d03041030700040030030403041c0b51803101d00c3c1103683c0c00700e0b166686800400c08001c120444600100280704c24001e0300c18030b903a00c03115400c05107481e074243c911481c0d0201c020848142054100005400040d0484003a0702c20180344e01c41d00c44041c020707030b4044c1a00481034100c11180000090039940c041c0d000390003942061034105030241e80019a00ba1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 43687684 1250 43686434 43686457
    0x10e100509120a0f020c010302031003020609040b04060b0415020d0e041a060307051b03041a0a050403020303040314010516091518060309030f030b09070c060b1f09080f03 75
    0x51075607039164010309220711209a45064000040d445080c0d81e0408101c40031400f8039401c41c0e40000c1d1800040d0128802524803800c0c9030003040b820401450018018006654060004a030241c80800480c040e2415a044038008a002041c1031100c0945100c1050221601d0310040040d40840c2c1006480c0e03860508510b030046846a50301c1e14000c46000f0320240700000030700120b503a8030344040020302030340213601000d8490100e174171000d0346044000140c1d01510000080c0405003025902011455401528103501313100040c0300c0027000d41c0c0c040c009400158058100700220400d112107040c2156002002e103461242616850040305070b1000741030f020b032030f04142403e2032100d003c0016210001c04000e05014408500b1000c01c11581c107070441541d0b103200f1340303462004698030841501651104a0303625003040000000501252080760040d000d02e01540b000a000341c009000700d508110604c090648541d203104080d2887ca922891900007001440081e1007003602c1d0100d242d88070b00c9044ac0701070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 43688934 1250 43687684 43687691
    0x3120a05160602090d080a020d080402030d0e0a080102070501060e01090e0607110c12012a0f0e04060806040c0311060f0913140108100c0f080a11091003050f09010e10 73
    0x80401200c2e40c1220130107900201001d0024606181c40e0702554003114403c80140213650100302290301428465000c3ca80c01005424640684101241c0144801c2e02d4940e0055a10302d0026040c40c003131004102a5000388004250707035081849a120391101a481041c69600d4481080030b80880032480d540c02201c1403034090308a0800903203061600904060540e07112301c0e02070420700d10312015800101c00d1003100c480140b618840e81c983d85260704400039240045122003055420080c07040c0c1c120846100300a00004a280d1142c9c0c17070f02e241041c1110100c0703403041010018820705c0302408403602495006c81c4e01d03e1070b1003004c2658400d107005250a060003800c542600100c1c54100c2d42000301100046424041c442da951011260303614104046103200358901000c00240c1032082d501400c01b0213007a11002556120001c02a00030803051200c1d4041e06070030310248856603100ca400d40c642c2c00702aa40821503013481e01c1c21200060000d41210810781c0f4252282005d4100410b0344010811141c1001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 43690184 1250 43688934 43688977
    0x31a091509100e0a02030712050a0b07020a17030603070f06050f0d0608030c1507090501080601050a0207030602030c0a021e0703031805090711061e0c0f1b070503120a05 74
    0x1842d2a000c800490702c614206428034003150400105458803500031000c440c001580d4100c0d4081542101c28060f0241d0130031405107010400d5400c542c0d4014820341304a5004038840c1d101e90400c2020f41803d14440c20000041c0b2507a444e0410031500034181c0d09a140031a00c0c40d00c24007070081e105416864035041004208240f54179000c2d4005401491941c007a65542c4001c050f900d5100ca03028040042e1020540c80400d6070300d0312482c010703010340f041a107800d502500c4500046d02c2c0c980011901c1c50131403146601c0440010700500280d03000b1400340a84a80311070f00302401a0034441652544012400b0088144481d050005014412203806080040300081040701948949403550400c5030080300150900070480d0380154004084a088400ea40942e128480800f07120480c680754500111000004200e950940d03e00416421344541c0400745019042c14103001c10301140c8004074503a4100030000c10460500f80594200c50760300080303051400100100c0a407007406581d0354075100c0822200903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 43691434 1250 43690184 43690201
    0x40e060f060a110a080408010b10030b100c0f021806030f3c01020403050309040e160306050612010603050c040e070b03070507171c0e030f03060906031504050601031a0915 75
    0x1410010b50004445e559a540b5102180d01038003481090500601131118a12010f5102c0e21854901520040c4420481c20940c4002c0b00e09006040c1c0c00d0303504882d000100c1c03006030341d8100d00010034640b0070780300740f524600351040606144a031641c0d280250170a045140b816440180c41014814a054000341ca48403644004078100d041249100481c0d0300c0000d02005101c400406000b1a203411117013400400303001e5580d90307103850300e50041c40304410701c4000500014003907800c103a920410281001444002c400025420f6903481c0e8815078a41e040104d0064403070409000d285010040030009002e914984117904d096840000e2034201040000728010040004111346144c0b103001ca405e001d03885032010030140c4902080e802007082d815190102c0c0040b8010044150740f41c00c0c07040b0300d000b4207555a16040c0032006a00901003541406003d8405080c00030340a0300344e026a000b1801004158190315204911070003020051175601c40c80010441801800504107008568851a1003c2a10f80b0080c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 43692684 1250 43691434 43691443
    0x408070213150906080c01120e010903120e011b18030606080102031905010501050f0705010b09010b071101090506031305010f11090a0506040b07020907090317040e060f060a11 77
    0x80d484031a40c0e603076800a007801d8010100a5100380c040414880e41e078a1500100e030107900c604070840c0c010a40300c2e00e15600400000c2c5044110310030126010a840e54154211201170344120081240c03c1070030540280c041c40740d00d4171441590020071010000c4130800701c01e01a02d00c07080c03007004031001051018a9009041500440d8006800e0140326150000700e8003030340080781d50031600007040b21406038031222801114103d40741a101c092400412585080e9240d02642e0f00b42d4644d0f4039140200c2e19a1601200c03e4000c009030710911751101e140b4070700038600d0081c800045040000918003844282e4071001120381242040c106441c4a040078504640900000b001221400345803140c4401c0310b0700d02500403c10810201d0b00c215181c0d031607130100103081c0a1400f40b080c0142d4107118907001030038034803420740d0401c0003420704180300b640d26620f040c00075081214210313010902080412161003941d032802d40103c4119051250182e400c070101e0500d004186c5885d00700101c004841002c0d900600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 43693934 1250 43692684 43692697
    0x906021c0b04090b270d0c1203050708010b0702150c0706180f0506091206100f1a03040809030f030a03021c090b0601031d030403050303010e0708040c05010f09050402030901050f0106020102090f090408 88
    0x801b6a07404034106280903000e604880e4080d5804410002c048542c6441380c45450700c44c215688681c1c01c4e503402c00d104d06001e90004a82243c01c0380c0e462001e01c4032012000d02400103004444000c06001e0308084005103100d1049541d450880e500d544180001040352000300c4c180e80341501ca144e1100113510008810514403c103450f001d001e208184040c24017040b0b03890342580d014510201c00f45507030700d401c003500d445a502c21146142040c00810b001900e8040240082840101200c00d604c0309603940c6800e42d80700a252001080d8001001d80c0102c6447d4501c0341003400c00382e4200017042064541c148200002050700c2d04165032850645140c9403c61001400a408081103d0b2180d4803843c0855480d03200b030040b103034401482c00009a0140c45600400e2096601c9001da0000500d0171005503482018906003000b40401500c0110326a1034034805144506182c40000c40c2501b0a05030b2503003c88010b810032000c590040055040b1601d40c4c4842040c03024040e260300956a645007041d00050242d503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 43695184 1250 43693934 43694011
    0x3060409020406150c02030f03120c0a020f030d05040210050711040b041104061101050a0506060f03070e1512010b090a030b090c030a0b010303030e0d1205060102010906021c0b04090b 80
    0xd5000000f2145d0211070403110354030076800c851580502003030807070340e078000ea0488585155007000000c2980000001074552145140101c541c0312001c0305049040d40c11801a2600c0c4681c2e9500704025032901c00c4044001e0300050403d245001540d46803000070f000080d40c03a500503611000c0c103a80176100c07903200d0819114902501c0362900e803900002000c00c00c43d0220719105d03608007008103050b0305240c8900c60113540001c00c1700d45440219a00c4240c6608000d220300d080c024003040300c0080c0e417100c0310300503c001c1d2110360442e0f132409200e500e0b0000e590306802c0300d50320141c24814402c1136169040742800b0382c0e0304000900c0c0b65559a480e42032400b0a003030601038040c001e035007100041003e242c4903a4141c9105c0d460034031021451005a0b030b03580004c5030f9001c00244030240203041109055000c0307500540184004154803c1646031202641c0c001780074200b118100c5258106044003034440e05101120840e000d100c10381c3c860f22040d00c00b04000d407078404003001d00c4150b614154070303030b404450440604 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 43696434 1250 43695184 43695209
    0x601020c10030b0909070f150e1e100201060e0615071209080609010c0507030c0615032303070c050103151707090f0902090417040801110c0f0f0303060409020406 71
    0x3841c801405030411a011034041c039502e0002c00c10b039681c0440c0c1344042d5804604012022840d200585000c51804e0900500b030000926400500b0f44030305c0b541001c400403c08040d5200854002030140c0030051442a0045914140f4284420038680310300c5900120103c408807550840038603094894411b5071402400d0902c80c0d850505030907000b5042c4003c40b0040c2064941e155078602c480ca080e02c1d801d81184000034400c120b58400640130b40314071680070b4021600020652568880b100080609400540d040002c0081c045d4001d5414003520421400481c0a5810a00c90f50380da113072540428005d030340c10705440d0341c0020b840c024001a031100500c440c0017101c281b030f01e4410380540c41c0c82c440c0c0520340f051400e00c078003540c940c10f0754003a1b030202d95070150000c0d81541d0b841d01c5039a50140340f13002c1078846650400000810341000d0213550350f90079101e1788182ea15007c6060051403c908080405c10382d40208980254549001c02500c0c1d000b07000340c4010990140c00e20008004003171617008107815644 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 43697684 1250 43696434 43696459
    0xc03130e010915060207060c110409060b030f0c06042d0902040f0f05010c021504080a030305010807051017060607060e03030907090203010f0329090609070911120601020c 75
    0x166409601e04036400b8020412040c03009012060b00f030049400380c41d01580c13180c0c0c2c080102c944101070940c0000c0c012805040d03440006030000301510700d654000d844031919861510b0320b501e420f021802c1c48518030002854481c0380c9802041c0e031806284a0401d4000c3d208288034404450300c00c4d82051b480c400800c400c461902c80d45103000a400a01a15551340a548004507003140c02c503500c0c60640340141c681c1428400e03141d081083c000c690000000c0c0c110350901002402820405c800d0350210320a49012400398103104004c0e15104540c0d011503c50004985070749407154102c00d215011200310301d40c0051319982c88003c9482c510070078800070305051034890407203248000800a180140108400c1d540c0750b40e5280c2c02d1a0a0340801c1c06244500c0eaa10002040000cbc4004642a01041014401c07442c000c140c40e000c010074042111841659049a03040011200040c04150042d09483c101000303031030040c4400000c54000c4c0e41154111600e060041200c0740e008100600003884001c100350000d40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 43698934 1250 43697684 43697699
    0x111010b0301110c060c180402090a030206130503011b0512040611070b04061a0307060c0c050a0b0705070e07050a0f0210050901020901030c11060402010509011b0803190c140c0313 79
    0x14001a41035946009001c081020280a1b03400c071440450070b080d22801c0b403241c50023040004d61021400c1a0b2011149034000010703100d82c006801c0c590784518840e00304924090505007900c021f07d410084941d1680921b00c123072900030050b503160022015482215589070715245000f86034072001d5840051001c02d41c5810803070704013081442244100400c1c041c0e40800c0c4a400c44c05968460002d6240e00000020701c8000c1c81040d801c51304030f00855114020940c4c543c0490111061a000384200081c0094540148401084030500a1410540c50980342c9094030009145009544d50319080041c1c1e01460141c081c802c0141c050141c0c003046c0f08020340d0908154840c001d42c0b1103ca00c2d80440e082c50800d00000e8060340e507017002009201c005c0d0001d662a81c0c01100c117641b2409081b4140a5052941c0074840030000044d480303144039600d4559a410801c4505028801003518032080c6404c0c8030ba6150915800703840c1d9003404805034003d81d21180f09411007030540c010b100ca4940701810040c0006900b0f07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 43700184 1250 43698934 43698937
    0x81e16081c050702070501050c010605041a010311031003120e030d23040308030c0a02070816090f0902030c0112110d1416021b03010204030b07050325020a020111010b030111 76
    0x8810008090361581c115007403055890032205800542c02280081121b035008030002c0ca510b02034100000b8095480e100000d0448400206006060350084c50b000b140c1d5030948100c002c942c0310200f5107411850856606054040301380801442c01c0080c3e400000405c0c05141074a00c0c03000c00800f50b820554107603000905001c809541003240c802101d1320034201840040c1258181c81d00709640e5480c0d96103017044410240e00c42400300046100d14000007494142c1404900a81c1d281c41e11024541440c1a01180544a9016510140c2c1d89800c0c45103005a03030000f22004402000e00300f01520114132000140185240518070307941e1072002807480b031116042d038003080b004d24910030410703055111022001c000c004803200a10260340501074828044200b4450480d00000050000d441c15842e81d03a505281882950302c000032070000706c140406100c000f042000c080c1c0604170f02d20124104000025580d12074960b029060002e0224a00803408081d003004200c890050300904c0141e40ca0000800d16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 43701434 1250 43700184 43700197
    0x904050403081b1c0203060d080403030c060f02040b0d09020f0a0b0901021203040525030606060306050405150a060f03020c070b0307080a140c030a020717030a18081e1608 75
    0x14110b019092107499100c0009403441008130f29100c1d007040c42c4440810000790300181c0001da0041c2400c030944001140e00004101031803103951a06080c4600b4034202090b0341001000010050041c0f00510980c0742400541c0d19150028201080d007503a140049101f82034225922600030707848441c04031380f8503401001006000003e80c00c641c0310303804815023040b00740400e0b10010071941048600c40700c0c01c0700283e48c81c0005040103281202032540c0f07aa03a241100d034160b10140c00b20340c5400c010403080c0350134032815602c0030250500d844011120030014254180ca07000342d00510015841c441c018038440e50649090044d10822904d0382c9460b2070500800e0741080352001c00041503800061082e55850050701c402400390f07050521a61521298080b440e0401080a000346500303109c1000031500c0c0c00030344209000170008030380c2c2d24189a0140000c3c1d03912181082191842c2045603000180300404465204004003400d55161aa00c203050715240f094811100c81c1e0019210b07540240403004c2c008043c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 43702684 1250 43701434 43701451
    0xf04021b010e0d1d0a031112030d050109060611070b0d0618060f050a08030d0203041e0b1501050a020316050703050703080307080a061409040305041511070b0309060714090405040308 80
    0x41030807010b6040c0034107944c11500a50444000c003020000907403500225070076100c0040882c0032040b1a8000ca500c1c51300040c031215822912a0300401001010344200c4010f443c040c81e086201c0c00d50590410342d150094490340341e5281b00004c55291008039035100cac070064100c211108000323244903203010000d0500c1e401782c40c6c00c031482d20900040c9031408000282c1100c0c8000069818004002ea480c3c00070341000b841540c18403c15595802d0885100700c0c010301891050113a10383c2e6041204403150183c1030409640e0500604102d661003558002096419041620f400b240d1b2040706803a01504181060b8801406403082420100401146101452051519030769204160f070352010680e054070071911840d00088e14110081c0110704044104562160007800d0151402d80e4032405455200080144040041c00c2c0f10000521030800f84403840080c2061241c150460905080721500c400b00a0400030500100c0107860b260403070324405403010031400600411040c50503040140041f0001c4a0303030b01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 43703934 1250 43702684 43702697
    0x10213050415030605090a020406081515032d07031202010b040605181f0b07020f0306090c01050307031401151b050d0e190801022104020f04021b010e0d 67
    0x211400c140c40303144141545116034020b064515210140100405054101c6da4000c02004e64003585640c003658000b490100c1c028060710071706c0c0c480c08594003c003802902000c04100c000d40411b40e0002000c60b481041000000d5a5000c4403580c2c00381965407d44201e0240038200002082c0051280d081c41a8501ca40082c020004000708000031110300b0b000c2c2c540c0c44140208a020040300400380a64007402d000711000d110003000c0400b03500d410039944203401c581000a1703101e04604001c00c109264034400c0d401403e45040800c000764840c000c0820445c100080840003800a51003a0440c481d14143c2c100b003464a56114400c0020f159444001d400c04201004043c00c0c0c0e40c42e0f0407400c09070813078001000c1d110481c09441b0459400d4030500d02258807083ca0100d844850403021900c0380200f0008000517038580c000d0080c80009115072a0801030381c0d00c207404000140c0c071200402c2081e00c600f01c60041e903855055120101e02d850b1070100088540c80c1c200c6080401c0700c005105000c02406441e1072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 43705040 1106 43703934 43703939
    0x1e0313080607020714060304020108061306030c050a08030304030807110312010e040308090a05030909220506090601080102040b0414150f040f120201050a0804170a02010213 76
    0x20141a0001010b019a42d60108480c800401d191500b004030401c0100c001440d50000600c0641480a41c00000e41199146c045003030b03203a0006203041107019143d003016040181c0314000c8500070840c4a5020403081800801e5074415035040e50707a40e22654130100300312000700703d0f040c0c0100d072448180305014500c200c44a8080c06400c004600b4500c0d840e250600401e00c11020304440d045410100220020a0001c401c5601c0440f00b911204050348440c1180c2000c021482c485a900851a00c5413000704040411707000d0250b101c41c4200d505603601d039034104d4200d200ea4442e0380300c102000c0008105d804c3d10820440780800c4000e000c15024401c04511120b594010202e628810b00006814400c3c40300000160001c0c2c501c15482110b2980b0550000c2e0062081d03c01a405128680000030100b100e6a1444096029854800380e15494440c202901035008151203064000da0364002 = true := by decide +kernel

theorem cover : BRFrame.Cov 43525184 43705040 := by
  have h0 := BRFrame.cov_init 43525184
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43525184 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 43525184 ≤ n) (h2 : n < 43705040) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
