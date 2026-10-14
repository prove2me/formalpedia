-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:08:17.497107+00:00
-- url     : https://prove2.me/submissions/669d8d14-35fb-44ac-8e7c-ff55c8acf51f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 193705035 ≤ n < 193884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 193706285 1250 193705035 193705037
    0x190f020102070b0306010507060504051906050906071103071104060929030c1e041b210c12020d0608100209040b090405070314030909072604170711151207 68
    0x108500b07211000806500c523040c009400d040d229800708007803007004d110001201c401c0440c0c04110b00c81034600071002e84000c13075000c0c940c0e0080e40700258540d030040203044441c07036245001e141360a1241d6110004400d0326410ba81d00a50b90b0000810032005520441402d011a051843d02d40c1d038132590740300c80c503090341041c49004c0d030084603c2d0100d945032050368100b800031465003655220f8510002c10020102280c0c00c9511421540d07010200365000420061840c03030140305e08030f6903400c0308208003d84d20000c0300400020300c440300c590b050560560140409160880010548540e00c0317400e1494510880920562a81d0000b00c0d01128940341c42402c2134081c1c142e9684116151640300c40744c80350f50300e00c8080d00b000316402c00515210804d00483c0c0e40c090006160345150709001c41300621019124101c02c1c900713098541c04480c005400110b040c07007168003a044082041c500d032054150780c1c1120314211840074503c030003030700580d036038101c00c088408500003c562500500c02c44840d01c40c0380070349000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 193707535 1250 193706285 193706287
    0x604091e0b06030c0c0c041a0108010e0403051b0a0611030a0e15061c0606240206090d030b03010906050a0504232503152a12050603190f020102070b 65
    0x40000c2d2103500940b64001d25980b6a1600d400c0c40450082c1015107800829600074600101080d00e541d5403140100d80c12403e0340c40300c400c0c2c1c1c1c94801c1c6c0a02101d0a44000e00469030174020714903142c00341654902c0b025072803025100514602c0c2c0e1940180c9a1040b035900d03500b8004400c1010140c460322402032000340f400010031200c05541d000c00540b060213401203010b07111680301040c8010f200f030804852260305c80350420010740c0d01d0141c03016404d4076a018203090407000c2c4d850780d5803a200080c1180642c0304000504180c04610405070000c010700e489203600365403030b4450342c00450f2042c170400744070b0b41254001148a2a080c50100300a2024100300d0034080c1c1007090f0402e811708009402d1150301c00c01c80307529010f00700e00780c15000c04000c141c2c8010425440d08510b990400c50303c1e04180741e45a00d458820000c0d0030b0400c0803503100580094088000f4100710302c40140c40e0981d0700f01d5501705c40054103643c850704d8410204262650038844c1503540020440412045513410090003000b000110005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 193708785 1250 193707535 193707551
    0x13020d0b2a1201030602090d0b0c03010306050a091109090708100504110306040b0403140906030a090210080105030c040515190612020301050901030b09010e06090a0c0e0403080408180604091e 84
    0x254a6040042c00302410407070340841d20301f00c180c540c6210201100d421480311240c82c42d001d102c000081d03100740030840e02c4500340000708000060b1402600e42c20340e400f5951a050300601402c1c00b130366550052080d0038510500c0c03c0042c844809000e40c585201c01c145000c03c0c00e1400b410882c070000c0c444010302d802940b01400b0840855503c00d0300c00c0d08283d041ca000f035009444202624528000c907445254001c0b0000706005510059a2100310300034030035620407800f201142000d95240e2001d1240d150075401800ca1310516191642c441940322140c580d41962507400d0700c4c049003559a00c0b480100401d0780400c010301002340c1201076428030040c05282546550b0412000c0340c1215418070000301802d010340003140d0f55500030b402c410451482402101c0f031500e400391076181e0312100d1902c29141811071307803070100d065a1060000c0e4032071b941549419006440380da680d1803840c2c1c03220101c130b030100510f00c800e0006030b500c03040140000d10100c04007264801d190150280d19080d008070780c1844c24074100780 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 193710035 1250 193708785 193708807
    0x150f0909070612020f0a0e090a0509100c020f0106030c061106090703020103110c060f01090c0503010317250f0308010b09010e060c2503050c06070b13020d0b2a 70
    0x128402d8542c1031620000b000c000000110207801000c50309551a00040350f040c07035655000c200c19105420440781000d1030b4540e0000d000c2111000c1d074801c10560003900800d00b0f095a50342182074410310500c129418281c1c0b0341c2c0c1e29401c48803da00210303540d07115481c5c10818941e10413030010350044041c003c0d1815081c0500c01d2a5186c0580c403009051544603410310b4030300c82c0440c00303075000b851444040c0c400c103140080f040c3c01c1e00003090147c0d1283d9840c1c82103144040d0311580c10740b4180c9500901d803111060340210a403825420280d500440c403102083c420480540742c282c4005107600c500310a5814458a19020b010100160404115480e0034491920260b0b132000110070301041c160303001c644d40c0781e5002404c0e040110aa181c2200c0e2894490700d64000002000903170210780c058402d5038034000450003040028419030801800c13211031034001c94206040884000a610b03c010a9a140d6200780d541e405041101100e8860700402c104c482001013180c2246280044103041139030ba490401032000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 193711285 1250 193710035 193710043
    0xb03150f0402040908030f18160b0f190e0907030902010e040c03110c100b040204050d080c01091203050405070602031c0513050109120906050301050901030609050a0605150f0909 78
    0x8511400490100800e042d912642d1100c40125040040280c1d0783c64411600e100c1040107071084032940c507142c488402d8148021401f1081c1c0e800c860124404036103080d00f140c449400600840042050400049106100c4c1d158000d900c580e480c0c0391440340f8810002003020b011001082c01c0c042c54245169000142e074400c0702d0459402d4200c42c001984925110101e001300080c9401d0100c44000043d040b6501000050600c0300d4851400300303006a0040700d0501c810f90181d0701c58640c101c003288280000090341da0005d07000c0b640d24440001a003c0c641d803180c0398100200c90041e001300365100d00748030610005000c00c00c00f61403e8002107241607054001d540204100303080b1200c0e07542e940c5c0045125403c08601d02d41c082030f0408003e01c5072110030304106140c00e1a058208021a6210600040c0c0c5401750040d07074102c400042101007568a103444d02805440d90040449203030241071013010020f2040e2045a01856100b00a0f10580700c0c03030b0b4244104000784290325403140046608200000344e00003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 193712535 1250 193711285 193711291
    0x15030706050901031d1207020415050604051e150301140a030314090409080d0222060207030f0312141905090c100207080d05091003021e0a09030b15040b0315 69
    0x1c13900045244003080d1229080e51400d0000c1480d0140c40340340740c800c4420401030301c0224022a0100128030101d0210000c034881d5100c2d40341c000000340400c000618206041c001100c503d602984901c85015001034a00c1e0f100c108000a940c8011005200068043c100280747d40702c140c800e0104c07641103843c042d01c0c2c4202e03c65500129040080c1c11111500c0e0b580055000750303440900b041c2c4a414600402000c1d4201440850303465445d0b207145a440d804240040342120440c4c4c0103020118115260180e1050b0040b4080c0c092004500e10500524890702c2061046e4034014a181c04a00f070240b040c542050a540b803503e0305038204001d00218203800f24400707042c032008075141e24020055460603800c0c01c0195106400d14000c0c407000454043d0881d005110f005011100001107414869081d1704901645000c0b100600c0034240b0302d00c1508a0400034071801c8002c0c10441e4515507a640ca2005541c0100c0b460b94a00c8540d4103044c285041ca070068000e0090210b001d0b000914810400da21084002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 193713785 1250 193712535 193712537
    0xc0e150609060c0a050d020105071806050307030608061312020102070b0f040212030f03071701080a1101030b0d110324160e040e0f10050106050a0513090e0615030706050901 76
    0x1400d1a031560b5440032285450303401420381e00d280e030482c104251030340c81210030794015500340f800140140b0300c210007c100c030852241d0028030045c180b200031120f07038100500d205c040c144d6444002c9031646041003901c0c8200100400340303e00418504e40072052407180c8204e4000d585c0184226800203148945450303015840b04005280342d5114000245003100f0b40803864028000001c81152000c0c000c1c2c002c0d440758119413204800183d0841440c070254801b4030400c14203030848135804c0000b403400202e00100610502d40420001002d5000403030809025104a0354174070303040c900110a0809110141303480302a0740c0f42e02c1600c2030002800c1c401042c014250503810b02035408032f1103842e02800100000d104058020001480119902c50f61403900e404030341c1c46846420030240c0e448200d405243d040c1c6040d0307950729007444148030040e602c541000c82404200e4011000114440541d4461035411403a14401041c090418803c201304552000b4003050003900191801e11101d80c025040b00d60030102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 193715035 1250 193713785 193713787
    0xc110d0e0d0b040b0a0606050313080307030902030d0f1b050d12090b04080a02011a0f040c02030405060d02031008031e09041b030203090c010c0b18030705010c0206040c0e1506 77
    0x101000565880300004002d081d4440c002c140014044904486480740c40c2d201401c200680e1220720030b03541d0380030403142c40e125040c40c440c980c80000d12020295030000900e060201d0500700c140e000030b04264011075120002041c541d1805545988944d00810380401660340e800c5030905a1916034543d060085003400780f082036041030220315120340c4a061079980000300055541003520300002c0c0d5601c15068030f4010342c00c0074181c41074104034082d850703041c10b00141081900501c0c94180009882c0d0030b1920030a41c0401e010002d11612410000d01040e50300001c01039032480d200795200d6080d1401d0b0801036141e07100780882c0c6c1e8002c8a1417503004602603155600d503202c0d5905000a400b130700f2030704149810030f0852407801c091035170035802860042c030f0b000d000d540034a65004011104032900c408041c1050b8080b1001c04c14100e9540120b2140700c0360181920302e00034042d2540303030031f6586508c2e6050044c2d00603002c00080c4240362402c030014000c15060156642000d090200700e0308031444d40c0900c1454 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 193716285 1250 193715035 193715057
    0x50c120c04080109030e090601080f0f09030405030604060e06070507080d051302130510120b01090c03180302070e0708012706170307020a0f03120c0305040e04150c110d 74
    0x112003080d600103101c900000d200202951400411240c900909540154281804500190702443d0280e10420701054924402c0c1e8902c100712054031405840c42c543c0780010400030072181c800f4800d0600c107502500020520003103044d021740c500340000b032050041000900c00da800103064070702128a00c510351100030405481c3e070214060704202d10840258001c05102d02007403013403443c0d0441445880561000030341c2d182c0e1241350342030079110f03500014005001d44005000034245540000c5284c0e155207000201000502001c01c0f007680740b1030058001da44021410030000c070360b080714198806058a09603005d540741281388084904810803824031400464403050130306040f0340c04500100410060b40c10880101c81c0c4503902c0360701010701030303005402c180004925009142d81c080b044a5100300099000c80d0940d804545035001e1550031000c0200820001a540d0403c2c4a898012070088a011002201412941080340c2540b90fa03002482071608034150903100104104110341000c2c01e224003020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 193717535 1250 193716285 193716301
    0x4020d030c03030626061f0608040809060f12061f110c092a070305040501081306021b060703091106070201020f03030109021b0c030d030902061201060f0201060504050c12 75
    0x340364011790503220000c040d400290540309259a05080500b003a90070a0b290842c2ea45562403260280c480c282c0c61801007003200300d2003010940c1c0d1040c00b984c0041d0804030840c0c00076426a024405030156450082060214502c10b0703e4002d1700b00100702c0d10360702034a0305000842880000e4022203424400d1010f0b018003640d0040c403201109450050142d0054949070f0301204540442030f9034403d03212001a000c54101d6000821181e01e140c0640f0303814107040c600703070045400003002400d1541204036400c159002484c00d0000c0c091001c8a02d00f001c1d040d801030040c8515280d8000c200008041c2008a07203000b203604580c041c0070480b0180e0707156a4680c040d000503441c0c901750f081c4000e05480000000201d06409901400d40368104242440713501862030080c9a60f07860b0b03840902d031303da00805801d0b001c80303000340e008068180c805095903082c407038101400c0022080c26030003040814044030016620319420f00c200005010f040b43e0401050400c160404054000e41502410702e60851000c241c0c1d80f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193718785 1250 193717535 193717541
    0x812070f201507120c020604080414031906090614040c050609010516060e0d0206071b0606050d1209051005070602130f030804091a010c020f1212040f06050304020d030c0303 76
    0x20310010006030319401c1c0424020b02c04d45500d00300c0c2504034507105252000c01c2c40410064050307504070001038240380c140300751425030484950030654148118903d1100d10b0803040c3d0800c006600030440001e07051184e081510a503508a0080441e0984da841048000b903030025481040e600240c070a0b680302c1e0054001680e1714410450300c003048a42003c0d22404004094000114089a58041c0c588400076030000380d0b540e0034103580b100081503a902c612403484501001c0d910b91240208000301c3c0c090b6a58001c2085807280c90810386158512110a6030100d03040f01c0301c0f00007880140e0f030a010b40140f8940090260090800003085d07160002989281010b20b052801c0142290001103e0156a20320380507e06030b02c5031044504403420840d20582040303401c0b51050304204183c5690403007603980d500700644428500d9019900070039002c507481548400b0040e80f0310301c40310202c41990b240c7c145803021210700d40540c0440308000c800c104000041c2c5600981d1307201d0f19071504081c00c44048030b01d029806 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193720035 1250 193718785 193718803
    0x60c0312180503040f09020f07120e13150b160303240f0305010b0405010e071809020408011a10021509100c17061002030405010c1403070812070f20 65
    0x1040c031001c4407001c207001000c0010001c0312420525207503c0750703036800010300340e008050761440d80c51014054500452030412480004100c90b1030141c580d0302030000003814401c00c82482880b8036a80c0c4400c100b00c1e0040500100160041c40266800c040413034968003c40441010000d04060315200704010010581c90798140f08407142601d10310454442d0307031209003060280310a654640c20552036201d642805c0c41783e581680c03d0f035500300d03141d07940c0c0b000190b0b40c640656001280207450340c140043c81d01001d201501c003801c0102d0000c580001880001c2c601c5e6070b001e1404902c1000641500c0071065000241d4043c154061250400c01d9074031060004d0602c401810420501c90600c1000e02240742d10a0f81c00c224400c1180d19114591a0b038018815004044c55400000da403003000300740302640c00340c250f14045030f10481e050464150b05516103400c5402400003220071481c0421072150910030114455485040f03842c4c000401d0500031001407094400c00400b1000d00102110380c48500d800b07001d01d2038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193721285 1250 193720035 193720061
    0x2070306020d050403080c030402100f0509040c030b010f05121302060f19260c0d06030203150f2a160506040b09010b0301090f0204020306030f0a03020312010609060c0312 75
    0x1d102c5150300e030594040d00b002c0b10708030700041c907810018804541030400c2d640101d070040c1143c4004086150140c901410543c0d403201441424003200700c2c5a5982c0c05640403035459036070081002900140007408051081078072105001040c840f40c000c0c40c641c03007181c1364000d40300d459000008500e8008603045100b802d0010b804c01d0340000e0881d400f2030f00d010240008200701c2cae5509030254140d9169450132254140070f5001c1c0079000340410340800d80d12000e004645601c040c00240075590390b0010f850040090098080f0050b50301c10414a1400605040d5104005244d2181080c200846044650040d83c002207801c590208002216021038110042c0b0240d1080c112015420641001c10703008038100c400104035824049007800904060140080c159804045400704910300e07400c003c00394200030662a0988105d01c00001041001c0100d806894000d801035a1b5800c0c845140b080c1201d0140c02804c18802001000c11070594840c0b1410030880d0075140049192014001441c05071042c502000c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193722535 1250 193721285 193721287
    0x20d0c030f20010f0804020420040e0a0c0306210501060b0d02091509010903020418240609060509010909030207051207060e2709010f09060501061701030203030f0a0207030602 77
    0x100400829403012031030200b07030214012075100040c2c01103550506085502c0f0002d00e4a501003801810503400c614800b00e84000e04140d14070466100002640042c0d10041315400c1d00400d00290380707140e201e0552003010a107424091542082c141190f090820b0306240103d610007801142402001e43c0079801030b20480e50265078801c011401d00019400030749030a4440c0454111b043c0c4820201000c55045460685500f84001e00d1a002c0100510b42c03a010040c00408562103000010000c1010004021015040c0c1c40041e071035400760300880e005e5130030010f01c0c1b6181c500c06001e40d40d102102070781194920200411095251f01e0103d052603070035484070350040b80038144001c00b0200440c0792000d684160340c424100c2c03402c0c9000c1104036a12060240e16125802c0510000742617a101000c1d03002c00b0b030174000b00b40656410342a07800c44403d03040644100742e40c0da0051200315440303000d070780161141180c451000e5041d03400103074481c400d800ca03041507103000040c00100b042c02440720358002d51300982c1c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193723785 1250 193722535 193722563
    0x150c110d0c0302190f0501050a030e030c0d11070302060913020d110405010f0201060b07060c18030803011401031a01050d060b030103060f0b010f02032b09050114150102030304020d0c03 81
    0x40e2401079290104074855058030260613109648440c40d2000c8900038011203040c0c91810005440c01e41c4110045010903840354604244601c040000740a8410b203c0000c0c80039080041c4c00600c1424031141c58401508940c404002503681d00056544142c1c044440074445a82c00d0950340c001c0c0310b01c201110b107480c14503042280c102a000050412100e0a882e1070154610faa40100e0803280705000d2110001e00c1400040c000c91002c1d4828843c0d03240d1401d1030620b005920000002400856000b2034000400000500451881d071009000040d0282401c3c00340d5403101299540d04805521404d041280101d9a403108004680240005200d00401c0540da540c40e8203003a005043c052000e040141d0070300c02600c03155489000e03403840740985a4007071400d18903808000c0d440d0001c241a1400d031a031041100b0714609840c0c2c450040400d118000000d50040c1c40804907081d0340c00100b003920300010345010008981d0700070044070b03841641182d4820a005061500030900c10441c1c20141c502c2c400b41d01d030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193725035 1250 193723785 193723793
    0x31104020f22180903081f0e090109051006210213180b01060c020901060c03020c130b0306010902040612090f0f03020a140a240b041e0f020301150c110d 67
    0x2c18054600d010740c070200c441d55160312201030310040345008000919540000c2c3d13090140b400101000310b03c040103801030381c2d40d4400a001816042d2800c08803030350b40d2000341041000402070031010010066051107441e2078040b1003829200c600520030201e16106501c801159102e00f0001080d0603440020004440c6a80311800c0c4611440e40803118044903200102d48140914000c100c1c80c1da00925448141e803c00b101102c070382c144020110150701c00c0c07480c061103a54890300c03a001406414400006d560044604143c942003041c1e100056a42c8100010310146503c148a903041a80c8a40003050f010042d03c0e20800e415101d50313028099881003000c0104059002c01c84041a0340526501c85415041481039500e4500ca984000c095082d005281481a00c5030a03000c0d0540d885200300155044550010a0942c2c150301c0c90350b0040c982214818041d480148541020351009a4017142558140500e0800740c0301018490b4041c003039004000802c200c490030385404d110b0740c0a068441d00307402c6490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193726285 1250 193725035 193725097
    0x9080304081e010509030316020a0b04111f0f05070201052a0601060203031509070e03070905090709020c1b0d0f150b040213060807021e03030a1104031104020f 70
    0x364502842c11800c030b480b04031541401114022407042019514603140c41d400c401b0420b00107175010040d070180031241c4010540c039245072441103026103500b5102ca44880100700001c40110600101081608885105158007940750604040c0031305120350b0707a040600041c0d6a50050300e5003400c4d40c8001120110304506001d0880141c0c0c80b00d5811201184d0f00d900303041e0f850b40411a00c051414241e91007400309468542d0764950014a5400c0c810711242410001c81d0034403034260070a901e26a00ca009000000d4000c00041d401080038603401c6003000d00c9441010f8851550000d101c0491100d183c04940d20340c1e172080d242c464543e2001c003e940404880ca003030480142c0c0400029885403a056410ba8031303044c0350085400342001580501c03c110f0402e0401c0d580d030030340030b0103050842c0310702211000d010f0005001e00c21078050501c021500c901d0450406800c0e90b22400e490000000c05000c2040040c103154141400d0b040c0865000d0b85030f003940f010310380d50350041c40800b25206141d4221207050401c121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193727535 1250 193726285 193726303
    0xc040303020106052202030a020c0d020f06060d0b130318060306050a050a0e180f010c0206150a1a0f160f03120501050607060506042c0f0715030203070908030408 71
    0x140080c80f5407a0307640100f21002903c5043c3c4456440040c04400703680300c0700d40c029a0311a280d540010300700b8007600d292914107110030821402603480010b60000103002001055486041103440c002d454181d90380d0300c0e109180280070402e5815108210b442054080d45110902d0302c03414104c3d20340c00355210001805440d00d40301d4607014440c41c1d4804074590924803110760940c0c9500ca10384c480b0380c9500042000508501c0b01d9612140545170503c1c01c0c500080c09100f0f580342c680d134003e00307642c28056120940059600030003403148010324001c00c0a01c0f01c0a403041d00e030031151101035441e41d2000351420b50b14490040307610303d02400c0411040401c200400141d007443d003c0d0340c8641d03154181d40203942c103e076020301486a116a00340072080010f0000d030089584400054408501030002102c0d0ba164400c1103940142d0642e51040d629800c1c140800c4450700a03600c850041424a10300800591203048940c00700c42050307000030008040c940100d50600040c0311440c101c0342e98540e120081501c41c0c0b511 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193728785 1250 193727535 193727537
    0xa03090c1d01090e071a090d0c0b0702090903040e131b0b0d05090d0518041d010204080d05031006030b060903120409061410030506011803031706010807092c0c040303 73
    0xb00001000130a000101070081c0c0303402d000790704034505410f43c0d12055500001c0a441e030024000c0085400075034031084210042004071451501c1b209548100021020002c0c141c2d205a44280300410010903003403011600075180449805d036142c6c1500b800c1d1108103d01d01102c0c170b41030b440da000142c03054030500207060241d55404204529210421240c0c0c0303c100440414001138400c0c0a89030b400c1903520750200d0710220081001402000b10120303052034100100b00440c41c0c6e580860200a045000e11a6184160040c83c00c54694a800b001d070307030001109800b980042507951013014420351210b10459403030500050448010a00700546110240e0080c060030542c0d03030500500107004000050742c1075481c2d82c02821190329500c000b408600500e40201558101300003440481412610182d405003d14003ea42d5403242c02015030920f0b4181c0000f5201e5810031200341c040040080c1d0109088051340d012054a4143e03050450108070b40904e810002c1c900184042c0074007440004207802801240d1103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193730035 1250 193728785 193728791
    0x203090a121d04180201050c01020c120a1b0c090506010903080721050702090f0a090807030e03010c080c12040312020d0515030307030207141507080a030b12030a03090c1d0109 77
    0xc0000e10059411040e00b54440c020a40b14010040d1f02035006880100e4104000604000b140340e8003514002000309440036582002910f1034070580c0c09540b48924114000c1d12100c116980e40d50320380d0708012407107035a540a81d10404030310142e119010040080d60030221558458010f4102103001740c50086030700c50030707007075003040480103074040c030b098810032900104a800d00380d858031101e0905907001004203050700d03039407082c52002a21810290541c0350003583d5141400340c40030140b500b100e043ca61070f04d080c4508030701040070201141086840c056000400c16096407100c3c60207840e40144031034640d10044c000b04851811140c1c03580b196104011048001c2c100d0840c0c48245500c81c030072018044c0068120440900c002114000f0140c2c0454000c1d0400c40040280d0320045c140e178010f02000c0350601c0000032840c1c892a49400341c44c04d07000044501201c11009250a241d0342d200e404061014544c4540b07015003031144503918940100004960380340c0c080110700d109000d151b0240224007410385 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193731285 1250 193730035 193730087
    0x30828080f01150203070f020315130c052e031508010209150a2003120a1e060501080601030f09050f03041d10050d080c07091a0415090203090a12 64
    0x101090f550340e40311041d4000e1450084180c5900c035407008009003d030707010b100e0041201805141031000034030072101080b01e44581c941f10b15103800180543c0d40840d2050b6041c101100c2c94505201c003800392443d8401c10010760841c1c044095001d8408003030040c003480c040340d8001800c044107400400307040d40c04680740711485051810325007041c080c00c03404000103010741c88600180010000d420144030800d0b01143c1c180040da6410782d5508a045440342c1c3e800b5140e0801041403449070341191440607800c42d05011141c00c100c0020300144000300014101500c1e103004001100d01070b03111003031803500031050740c85a0380000605070b80c0354040e02c07030200c070002080001a580144070002500407012600c101c0200c0e4a010100400c01a071288243c61800c402c20110311409001c204000007060026800300d00c2010007850744241c1e280030645180250709001171010314070403007002201a0f07001900011f89a032103c40c5000d240540c0076600800300300d1295980d46245030011815020a1501c07484401004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193732535 1250 193731285 193731299
    0x909010b03072309070207030f0807030f08040f1b050301060b040e06010c1101030f0e010e1f0c02060613020f0307020a1b12020904050f0d09030215040e01030828080f01 74
    0x440d85519840c141c40c10f8401c184503203419499103030000407038412109560307240c2d11090b40d01004108101d80b001e0000519800309500424040114211400d200341580303040d40b42c1800c5140e400e4001486003011303440b454030410608503d01f0140c24064000c02c030440d00c40007903030003e91040c010040640d04801c0010200d40c0324038081103016500031035600c1e03490740e00001500030700001d001e40904182c5030403402403010b0091050714103140003640188100354100e9420f207202d010541d07181001c00d00f4102003da4054001a01d030745c1150041e01e1405098101d1609a002806404003e601c641800030505c00003e40c001007007a406030040c00e0118082514201d40044140c0c0752241070401e81010b01c00c02c000d0b01d02890b816500601550654150342d90310001d05007020030f6480e540c0c000c0f81e0130903070501c00c0d42044940515a070864000542c500740c10f00707003049030112051000518000002500e44102c1400e00f0f801d501aa00c0c84600a002401040016140035400c03941040c1681e46900006155 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193733785 1250 193732535 193732559
    0x7120b040b0c04060512102c0c0a20070803030f16020d08010618080106090603150e0601030210020106081c030f0c0509010c020d08040312020706080c040b0d0b0909010b0307 76
    0x441307580d158a841c2030382a039525008820002c3c42007000300743c04000000d1140b0244035081d030b5542c8406c40403101e40701022000425a07006080e10303502c400d0034055092101d4110050110f03a040250182c10201d20f00c1c1c8001349800d0864110100314000401400f4014201100450260007140e021002c084401c01e002c983d10025100540001051100100405802030f401954520800c1c40e44030581da0700c4440050070350f44164800010356a5a00c410010312031011501c60580401e0341e001e006600c030b96200141d035101d0600029108a9101101c900424000d500034001030440100b5901540c000311881c501c40481d2444550109040ca14000000c280d03500c06c55201388455144e00f41020a008011603406001d54022a00070064810b000f0201d00e021024200451080040001007000c43d44024180111540010203010820061054076202030f002c5e101619240f41d01941c9901060b140503001c3c0000401c22508907112500380140c2c5103041d04904820b8030240c00b21500aa40c4642200c0c3d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193735035 1250 193733785 193733789
    0x15060f0207030b090102190206060a050d020d080a02030d09030903021201020c10050a0608071503060b030906060f04091b0302041104180213081f0f1a09040507120b040b0c04 76
    0x107800c90407040c400541ca2030066a0001040400181040e12100641440c400d12080e0030300541d000d00204219031500c1c44030074000d04825103502c507100d0000ea02248420140c40e000502034400410201e21492080056070700100271607402b400954600c1c2005001419a4002a4082c08100c0d50503a00c1e0441402103d941c0c1c0e080c90010031b5a1040c155150300140009000040856210280012128010000d480107415071800402103440d041801408681d82c59100c0094034200307104100290501041d81d541c0114240c8005400c17509240014004200584004143c50400e020407c15181c01c074050300c0940f03109440802000c02c000c0301c05015405a03210769513503512003035026040c00c100340e0003414110902d00c000d00942621070242030b080801084c03c200a0418011072401200c085000c3c1d545c40b400c6900b4100545011101c852010300030030500c5500401c03581b00402e0422a00f00048002412800c185080707131140c6d4500f002e280d030b406440540d01036502802083d10840a40102c0303007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193736285 1250 193735035 193735037
    0x1e09050c160201050f040b031012081e040b03070c0314190e060d020c100b01030b0603070c1a0702011a030601080a0f0302070504050c0406030c090e1504020906070615060f 75
    0x2081110040241d95001e0784103a089040010074008403540f050005c01400c043c00104030019124134001e40003030358102042d070049240c0f4402420a1000c06c1c00c1c00c1c1256842c1400314086105081c0329500080c061055030301c0345000000000400440c0b075404400300074024820381d2081710400c400700702d0500b1800740000c0c00403a03540d80e50b20340e00103901500c403c415400019007814108505103003000200c0cac101003100c0420380c018001103010311400d4031540401003000d003010000801000085040c80c04001c11030424464456081c2e0284204c501d8201c1801055007881c000380e140103131009000c2c04980c03c16000c00da225424603078880c5004035045060b0b6007445d00500e0300300038a840c0d4205140e4081800d4040d402801e402203071a403940d00405102d094410442c81d60f484c5002c01c001c040350500300d132800800110036414498610806040354000c14410101c1e604075000200042c02842140c0009500200000340082002140e40001c110402d20a00d1001d5103980c4020540d5128151820a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193737535 1250 193736285 193736287
    0x80f04051b0f040501030f02010f02070e01090b061201080c0f0301020f310e0708090105060907260411090c04150f031d0f0d050c0705090a0b09011e09050c 68
    0x10120500040160300041c0241000c08265407000800e003250003e0b00240c8210807940740704420342d60882c02a424414042c401000c03268034000c0110390815040c05401c540c191292005043c540d00c600503a0344081d40f0112121442d65544030b50341c0d449420210b454050070429626000600d010b100351590342a07044c0c501c61600d10898030300e07209601d00300c1c80c100c20303a15042d034000082201c040c00c00000e0038174842008003078240020041c2c0f4440005007840a1a0b04000820601e81c55803880c45411201e54142080c00d801000074030145075645a4403102c8403090703e0304010902c40d43e1940760320800e07800d8414400300d45412020103524401d81c001d5080f659428048601414400e1504100e1100b9502c1d00281e078107014100002e101d12116905086a401512180c44000b801e0000040046490070039a01d020101c24500c1c1c1c540d420383c03242600c01d0881600260102c00560812024035400074480400741d82c403000d560b001c41c140d04110001202d46000c001c140150340b84075050041614580071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193738785 1250 193737535 193737553
    0xa050705040c140301150216120f03020f16090c0804030818070e0f0618100e1008120c0d080f340f03050903040b040b0a030b030304090c080f0405 64
    0x4040600340c12842d12041280c0c84511054180460000c0d40c040c102c04040704121b0520910300a10741050008100380070a90b0200411480f054168006c10f00c640c0201c000301da201e082c3c00d099082103806165501c040c0a06107110721100480c031000801d070703800d0b003800b04080565094100c4991100b19001008241e403940458500301c048040288407241d0b81c070031a4100b0380c8584a1080940060383da130b0500403103503010300c4000c0c40d00300c49507000d442011a503201c261a00302c0d804104111305120300420380300d0341c0010a045882045103c5c0103000e845c0f040f40e03182c01200103600b000e680007410b05441750181c155413030441446846220700441c2100006010758075800c207600806064070210f070424155030f5103a443d902e0b401c1c1005091192540d1502146c18018403400341c140c0390b000381126210740003040b0601c16019140305440c160762880030700644901e0046810340c01040c4034644e881d0305120210b4005005071068001016204803039171601c182c0e840d03002d05400c022006171002480303604207180c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193740035 1250 193738785 193738789
    0x5240f0c030c070f240f0b0a050f130c26010b0306150c0607050408071d0c0a180b0a0e0405060112020d111204030318050604021c02040212090706020a050705 69
    0x1800f045402000e542c00403404503950303440c6a072600000d200c403d86400210801008403841b40500e04e01e041e410034072124140c807000503501350395030080501c10134124071030416a840e0400c4005c00b00c17110344c104225104001038050845480040c43c0340000341c0d07078020400400b4012180e10f04071050010080e06646801c0100111034001a4083c0000c030000c1c801281c2d0f220080011502a150701e407201075445052201c49401c00180c0d81000c95405094218004500f5100e0701e9180e000c2019002c650301c1c0e0460002c11100100c501c2150100c00a245c04c0201e2003100380e00003004015002d84403000c003001b0300001c2c031050f61800c54103240400c0c01c0b03001320f000c140b816030010007081020040002c0c84a07200c0383c00c0e1030304d6000b03c0711220400e9005400c00082640500c508a60b0700d421038640c910940706551515511100100001d0007401c1100b2101040740c41c1d041e054441a600030002d41d02d410341c0b008047c16500e41120503230b00c1c900c1404000070340d550000c1032001c240c58110014145960234001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193741285 1250 193740035 193740037
    0x30e071206050c04290f0a0c02030709020c07360e010c08040206030402010c15020708070507060c0209150616050105160f050d15080703030804060b060310060c020d05240f0c030c 78
    0x40011754001d0200500401060090001c00c110b40e06500c4005058156006240c03500a42c0c3c0c00ca248514410400348078142e03070008511741216911700c16000418075842203907044022807401c030888840c1c5288290001c6000c0d0300050501b000d404001c1007840810f1004481e000c4059502940100c01007002c2000765201d1015503001ca405000c0810b08251001171020032603019000540d0705040100b13410701023010522044005181500e040d000e05107054000415044000d01040c13182516000602d1036600c6080c140c0c0c9810401041c000e00400440c10301c42d001e403e04a81d4500038549001c15000d41c98098214071030440020343d125800d00d0640861140100204180ba10070600c05000004410204001100c050351203036441c880030703061500e848026607182c1c0055a2146405204002000745400705020498555140c580002100d41c004903031050104e010140c014000c01c5074407500380c41d49080101d500b00d86aa103180702540c0314489426008800d544484c1490f904102048030074017404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193742535 1250 193741285 193741349
    0x121a070914010314130302070f05031207060905010207141519020702040b090a0e070603020711101701030b100e06030705091f030506010f1e0e07030e071206050c04 72
    0xc100010f030742c0c1c124020b1301c4804004451900b0090041455507003055418001d03140204510303002400000e0518000070789541040034080a00ba801003100024400785822122034140c0050003196621283d003400130750070004c0d81800c8010711447c0d001810070180c1d08000351017044980c43e44144c143c03103010a080030307500010059030b0158641244071a2682c514040900440460400003100c01b81c84800c0303420b001c403d9000304241441400844049005024100b00b0100104d030a101c858800420568294402c800280c200048500002c810044905841d60003101c0b18800050801c2d03031454108140c0c601200d102c1d0309500440c504100e00e051900c199608a10b036045c00408080705040e003540c20b690728bd03005070b035207a10040041080d9000303038101001411074010382c003418000d50b44120040603102c0c41645001d5085400241d8414400e50010000302d05400c19180c3c00e41e80c03950300800c16409038400f580c40a1070000456005003642e022141200e84000000c0b02403800707071503800f040350455 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193743785 1250 193742535 193742537
    0x3080106030e010929010e07020a03050a2f070f1d041113020306100c03021f020904060b03010807090e06180c04091a010603020a0e1908010501121a07091401 69
    0xc80145001544030843e5248143e05c902010401d054100c510140803041a808803d031508540b0a0003011035000c5038040001c1c2c0c040c02d00a40c0c804c030700c55040b21040007440441c40441c220500702c4c9010b0b50354529220202c0380d41400c861905440d0950b030302c042c441a03c00c1a9103076015911032109008403021186c0d06c24021a40012205040780100303030038000751000c000c5081d43c0001000b8a80c580a60030f45d07440c0100340360044401407503940c081c2d80d0342400b015080f8000d0b40c48000e0400094035404079640d0080207403050000507507800001713460303810038081c014940c043d404010851520320310403240d0b8030740448004c15040c0c403881c07008540f03100d0300d245003c0c2d580030380a907041560721207000741c000041c884c58550000510780f119002c00d659040c7c10001c201030040083c0c6038280d42c0b00c5681d001c2024111140b6000c44000c0d03552404451841d4841042c0d03500b08000014524001d0003442d110368000e8451059100d00e140441c41c0081d01142c440001c504009801d014980c824500c00d15240e0341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193745035 1250 193743785 193743791
    0x4080d0309080c1603050f030306090c0d0b030f0102040f0b0304031403100e01030804030b0610050a11030909011e09060501050d020906070b01270905120705070f0801060312080403080106030e01 85
    0x801400242040d4a50060004c10700c00e040c0c003001044420025500030284000246096050500001d8444440980004503846020884502c030b8603059102c50b6100400800300c0e89100c3d031040046000c4d402c1b9200324040c0c0c2d40d030024000713040c0d108201107a2240d949603488114000e903803280c080d01504080c002d203d11072030b075040c00f096203001e0b035006a000c3c40c083c083e00c1c0d407141c3c9146846020600c0041066004100c0005034179141900f16003903c08019513810070700f50041c0300740011351030360040d280599803020100c000015140049015035035108008101da101c0203440304c0c00d40c4e086e2807041c0701e0140050401c20514076068803e5001e80300c00c0800500e0f00e880d2100a48441841c6082030700048030441040107840c4000c0312032940c44240d8900e108080c40740c050141c43d02c0d40c41e03e5402e815041030940002d0080100401804480050038880010a85141d211622140204064007045950040003003011011a0098002501c0384d9031540e42c040c0b66038203040e0110080e0000820010307441d92 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193746285 1250 193745035 193745047
    0x1902040e07090e070f150c0204050702010e0a0b070314090307061509020a09050a05010e150906070f0b061309150e0c060d0b0f0609130203070e1005030f010b04080d030908 75
    0x25024243c401c0d03c165005001072070400011060000f500c0e4804c400c50040101300703013081a040080709200035012600040d1590702c0342000d0340034215000903038845014018464041241d0703000400e008020982e030801080e0900040380280410039034844861b42d0003030101900107030040d080310380e0542c54040c40f8400595502038180c240e802160400b4085210324100780031038100203034890001e100c01d1030700101e8410705c003007c1122034407545100c1d045c08000181081c0f0f66280c04007264186130703005035941c517180494100302d2052007096550612600c40320030f80a603c0502ca01804400d1a0072440c501d5034142c1e00d241100040c4400701000183d405420b100044940e1020040d1001554000c008541003550404100c0324400e4401c01501c01d01040c4007201131622500340c04004464031250059407074403165010398604285500080d0b11046d502c140541c880d900401442c09209600b5000c1503d9803244a80e512600890040900c0e9520075401aa0703440e100f6046044030601800d600751800c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193747535 1250 193746285 193746299
    0x20c0c06070f0b060613030201081e190501060e010f0e180106050a02120705070b03040c030c180e01060302030c1309060c020a140d1b1104050906181902040e07 70
    0x78000d00d9003030341d0090700400c40006000760740c0f40e45a440402100c000d03140440c0c408800546948600020f070400014000080c041072245165110b1071943c100240994903101622842e80140140c00042a44c10240002a424010001800814016110b851400c00d000c40704440c054050a6000d91080408408108401c5440f110601a0100e42d07103996441da69480c0183c80e02c00cc215180000303482c2004400c1c08164041424416603a84200c42980c0317444504100038215115007000e40b4071450b642000980508010808200d41700e0b10406000480c0c940008034200c0c2e841d0711003e134040d001280e4901161030240402c0b420000100b100282414807a00d40e10221000e44140e0300140c3d02c1408410144905079003201c251020440c000e100304000508020812180101101d4041503400180010031031103a40100c0e00c680d026000700070b01c0c98008007450b42c0781c106440c0051004501200442c210001054003084a1010a01c40c91300c00780c15400e110040082d5060740b0380b01d0080e020082a05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193748785 1250 193747535 193747537
    0x312050d0e010f0e06040b040b06130f1e1e020a02030d1d120304030912020105040503060906010311041a0f0301090f030e01021204060f0f050d06031b050d02060d020c0c06 75
    0x690390703800008244640400312000c440c0b40110b0724110354804e01c10800000e4030040b03107a500c65881804407500d6110765001c542c003110510501c9100b03038185260805610307910742c48040f0b2201da245540d00d0100440c00743c0d00496003141001c0304002203a211103004034055800400b0000441c0c4100d9103405008241d10003102c2c0d102c91506045c517204030300d41d407840c14204040d140b0344941c11540c0703103142800da402070306e040903910031404003a10000c000401d586c0107000382c0d0010311000d82511240c2c41c0000300e25841d11024003045544000890f05509681003504c04c254900315444803882c204000001000513601c12052500e5041d92250220000103504118201c03500c1d04c84d0320362803840c810441c0068240b01402c4095202484c0a200030092668001e580e4088141c1e5420142000703542190304546500c03031a10503002082c200400041002648088048030390011100c0b03405803900c442c108440e030109000301039400039042c8a0190200c03041e80c0101070500400007100d9000801c80042052 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193750035 1250 193748785 193748801
    0x60e090c0906010e04140f060907080a0b03030d2a0219020d1e0803070212070b06010e01112e051b0c0307050d0f1d010207150203090a120507090507090312050d 70
    0x41409031040c8007041c00160341c0d060b04a20b0440c1d09e00340c04c2c50301803402400342400510150040b615880c1030401034a00788119821148448414407442080d140d614802402c1d1180300c1d00103a00c1000d0f020409480401d800400c00700210070000441419008c1000801c07404605881d1840c800101b10030b1070811f0301c42284560320445405441b840c10034000f07410702c04550000c04a0744800c100c0c060026a5241501d0b43c0002d0074205255508009401210ba1070f50240c401e070200e2142401030140c4101a40d4450b004648641031140cd4920511103d0107a03001030325941700031101200d885444000000c0640741d440c03059400c882c280411602e40c280383ca2180340c02540450080c50100c00c2d0b8681c004190f000d5682070000e100240c0e07050b0f00000f035440e402c41c41201d2159000c6200e15803c14420710407201c42180040c02d45408649944080c071520390041000c072428443c08400060003051401000d1040c030b00c58440000c054030b1074844d81e020301c021510f02801c101d000c01424850010900c03510350 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193751285 1250 193750035 193750061
    0x21b010c020f0d090b030406090f0b01090e0c2718010606080109060909030c14070504050103050f0d021204050d0807050118140a1130030d060e090c0906010e04 70
    0x100d00c0c107080d04118101410901c0440c04c00180311070620641c11148100d980142d031100000400d802c1034145140c074403080b510010300b100784c50000002d01c00040d4010f40d14140300c88080d14100d035007010401040c03502c07500b196180383c0044810b0031880e800c602d074400c0d8004401b0b01c0d84200d03207400302200e5003126461f420040210388180d005004d40181032150b0030240c111110100550903040e00d020b080c0c007150103001003012210703030a2206085018090b03030300200000b41090095503100c1c608143c56004c00d001d107404522816007041405840010000c5440b02a01d070002c1c50542008144070f0700a02c0b4038001c1d5a102020011800010000d12941301032851030003010171105110314111034000c0440f40f025506600401040f80801c449102034015450304030b0710308a03076818242900d150b01041c0c1000c410408260a003400d92100080001c140000c2e00700350801480d5141c0c034040303001d000c044c0c90a042da6405484c0104860901c04200c030f0308109c050401000b4031003070000180554116068200d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193752535 1250 193751285 193751293
    0xc0203091f02010b04020702060d0903231206101b03140309032205130e010b0a0b070b09011b0c11040c020705090a0c080402060f090904120206060307080709021b010c02 74
    0x1240242d080c403c08108410458065160210a0300025064001e00c003210103002d588004e0101054015842c07144842c5440700c4c181d0041851035001016500440381d074010600408000a5641c600403101804d84103140d100d24054100340e05204c190300c0c01201d411030a000a003150180101d10540c00b443c45100828010b541d43c98141d0000b40100007010303e0ba4081b40e801c3c1d041070005a55021080015151001c4000703800f002c0d0410240c0035040d18803c980e04855000301c0850000b00701001060b515005482c14a1180c0340e8018075801c27241844e0b00d5075086441c00128022442c0300d0602c10709200c1c080c00b80c103400542d520b0b0001c0c0c00c071201944800056403200001704060b080543d001030344182c940c5010070182c80300020107806104010700007407080d10001780c0d0b1a9190110821380d1561907002d0404002850305103854224605620a100054461a800500103181c00180c000c03c0c2c90802003c1c0591030300e0001490069000002030340005024119210700c1003c09214081d60898154020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193753785 1250 193752535 193752589
    0x303021006050a0b0d090602131e0305060a09050106030212030324090105010e030c0406060f02010c0e330d0209040e01051b0901140d090b070f09030f020a030f050105060a08010b130c020309 83
    0x190024042b040300f42d1420140c0800c081000c00c4010485541c03040070345001042c10101854240d0041010b6040258441502c0c01c1c0070b00700000000244d840f5011507000b0700700448060590a041140000c1899803000b4a04010305c21948900e11050768000c0241c00c032843d85514100103800d03588142c0041c000658420a01d00103103609002e00e0042e4285420a4104500701c0400700d0b8181c2c0f032001e51550819600d104445c1811507410903d800719a003820a56200c00d01e1240c104e010354001a0f0140c4103a00b03000f031100d0b540350184039460041141d48034201c481c2c0710640407100035410180826050040341c405518030300c030703c0c00001c0070503c01000001070000711a14140303403c41c00c0509584100000c03000349410300e0350030681003010340350441d81a20a8007a603200084c05008541c0008241040c1144000100041504a54000c10003100d500e403009865014540c00c0b291a26803090748408004103100c0c03d11030640c445050402c4a10640c4d14100e845004500c100c4c44081040344404041c401e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193755035 1250 193753785 193753799
    0xa0c0204140a0b0316060903020907020f0f0307050c100203070b0a020415020127050604141c0314070531080619060f0b0409020d0b12070303021006050a0b0d09060213 73
    0xc05c14002402d1020500e40a0801c04014443d99590000a00a0804601240c112402040101081c10000c4212600d014151200640f030350044941100c5c248201d800c20901890600b154034045640343c1d00071410500701792940d01c041540078103481e07d919420400842e1101c07001540e2445810640c00202c0c55004042400d2052001000441c3ccc1d09200c2000b0007000032004500c880d0082d400c212503945407580121241d040c50003412003207104148135000e20502c25056000b0354072414640888012a603100181038800b0b2141c3d451854100c1d40c0407400301c2c86040c42c1144411094520038140c8001510380c3e10035803600c081600c102c51100440444c4075848801401400c01910440c0c2d00f0384003281c82c0a1038001540100d0103540005a00481d03403410315401644000d81440e801001c41d10350403403801c03800351503a04500042d40107008903000052030080500952044420140c642c0760b0040ca0007814401e81d4001d082c1d281d03905d03521aa00d40020440e1400541030503108101e04107016840c041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193756285 1250 193755035 193755043
    0xe0a1409030315120c090114030d02060105030706050c01150303030b030601060504061b0201020c03070b03070e0a0f1a130e0a18150513051002030609060d080a0c0204140a0b03 77
    0x320103980c0398810030400411200c4034143d2241c604082e80c0000114158500160034140408000c0b90040004400080c00c8070347c1000c50500c0c2d003815410b6451020280c0c0003203846d00401d025951b050341c440300040021034800c0e0010862000240000503180c044804120210000c0364015400a5103480c2180d110346410700c841401032446042c018a0146480c4020700444034914511102103009509401964024854040c410b103000b02600d00590320b6001c5008590010340b2554006094084030803010306100c81c2078425203103107184401101e842d140130108c142040c00b80030405d40b602402000d1111f102d80100c0c1e80684202002c210310b519001c5101c00440d48000064440c0551008540e000304809221641400ca5080d0703000c9482d40d10034200140310151303444010454400c120a40402024581c00f42d8050001102c0308800390703c980c1c00f0400490362001015250000402031180f80c1c600509200050a02c0904045044812800400321149040740c1c845402e544800c1e10110a01d8144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193757535 1250 193756285 193756291
    0x90609050105040c09080d14040b030403120f060803071205130f0e0c09090a0e0309060d06090b030303060102030a03180609030302030a0f1802040902150304050a0308060a0e130201090e0a14 83
    0x11900c00d1710a850304141981ea180740d11240000c0c032840702041203c2d141000110340160903600e460790b0b40c9040c07a01e001440361075a2075295103a24909110001d08441074064201211581002103060061070f44030350140b2201d500c0b001d0706214003008419184104d1070218402842e007512a80300403450410364284014000307094503510a410000e444182d40e8605842b600031402c0d40001500c107030390b114902d1852140340040d5038040d03008544201d4034402500300909440c26401c0502c68020743c1c01c1803541d44d00060314040c2c05a04284001c43d0003071b12961080300180202c003401c5004101940f140403c442901c44c0540c00250004100a515403071380c01050442058074008203d4450320510103a200b540004000b44030b079450344407400540d680c0c010310807014000e07040e41d5560390909107041d0350740345603d040440c0829000b0000409070300d02140980100c62032131000303400a070f548801040c2c1150142d64120305002083d10301042559512254503c5081c589200080341030340d40c4906034880b1401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193758785 1250 193757535 193757537
    0x6051209010501271e09061512080c01140c0304120c0507090905011113030210050f0702010309020d0615050a09110f09150f0702090708040b060f0a090609050105040c 73
    0x440104050160a680d8005246200c005034000c144c2e004403000140a002d104214015543c59040300c5802d050340c4286001c03441071004000340d0f00c200c0d1703604442c50303011702c00c2d0801c03503840003072180c0030030031a1008100501c20035000041384280030105407001d04c4191051240200044104020807034100c0b0103908821040c1000c0000d803203180d075580e0380c84440c0c1c041c000340d00b40c03920006410028250888004c0100340c40344184c0b111144044150816000d12059110718070240742c40449501620840d410b400d203002d039007880c142e110340055006d032800c0f4400320380200d10402a40e02203103c0e403040014100022182c2a041450030b0100140195507070841d402c0c0c0d525190b0038400e007441030000c661114804540090300c0f460041c001136104490300d03a0201e00d007a80020600710458400c0000c0c4181072080740c00020350f0b107800d0800c03680c411049800821078888038020505600e014014003a40c40001420000c4040d08c591203a400d0f03821541c0039561650315640140254078090142010802407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193760035 1250 193758785 193758791
    0x180703060b101704200a120204140c030115120c08060109060203040503031b01060803070503070b010f030f02010818150103021c03050a050f2701121a090603160605120901 75
    0x30030500f0310f00c02d400c080c0005201c407422603071030b0070307404021400684429001041e05076041d07951200aa0400a4040c04a00c503a1800a8107000262070004440c000c83c00c4024207421603081180c0d020203464003c07124000c0c02103108101c01030304200e016107a4030507601d03a034041d02802c2c000c0000d004601e03103420000540d0014071041c03003207031800000e60348035080e400c0446000c0094080c41d1401001c050b00014014000000c034882440720000080401a00c141000600761b82d84200c01c9000e42d0701408000c001c040d10b541144007542c03041c1d403156082052a00a60340d00074125882e20714114031a0100b03240c60724510010001d511342500d5624000d5070b03591121a0219981d0b07030050451061540120074400085090500e0130241d40030346202c0044c00781c980c6050342081000ca0000200010064006419000d240c2e8036060580074407106030704403031280709a0300c0d030880808c0b40d0a500140550703014407440818070906447c4c520001f00030310998446031758031030052010015040c0d00034030219160381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193761285 1250 193760035 193760057
    0x306011208031e01121a0411010507050c1e030606040b031915060306020306120f10090204020702030601090e0d02030c0c010806040e01050a0b0102010b0901030b040b180703060b10 79
    0x4a80000c40d00390507802540c0a036250b481ca481c601554520410312550101c5100003c10039070190b100091039980121981036240c0340d942c5161000340307012a0002c080300d09440d0302c00a554090406445071510070020b94102c1c02e41000895400381c6000b0148034030303292800b014003540c00c05202007604003900780c9090000e51940c1020ce6500e28480c44000400b4160482d000d007401000080041e080c214400e0900c1683c0d42c03400e1090127504195649446800800303404c048208001404016140c07004d000b900c118002542100024520420242c3c2c20940800030034006903804c0c04013074042c1040d07881c000b0307070003400070505850201010048130640d030080000c0c4003c650009030000200e0400d28110b0100c0d039130071f0082000f43c1148099640796609201c00e0108612468000444425023a03008004400e0600b0410405800030704c00074002603503030800314000c112012a00d651040c01c07090b40108405207103103030382d203401600d500540703d0311355501c0142003600c2c5c07402ca03d051000b890b15026071941 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193762535 1250 193761285 193761299
    0x613120e03010e1b0a24020703050f030417150a0b04020d020c0604060b060c060105060d09080c01050906060114090402070501110a170609040812060a26011b0207030305130509011211030601 83
    0x2902c2540b03a13001b907440100e841c800d00341c420007014020b1503014081e110a042444401da640750031a00681d0031400c0303c0216003010100000d00000358036061086151580c440302001d00040018a100c40d0b0426005c0140025450b0301303000a184202158006010f00e2400781002400c60f03c400107114499403040202030b0400710b000440761b041d1041100c4040d9103071140040c010051515010007003408201150000f100c242c103501040c0329181d03038000d5501e41d5440c94011a80c6c00710660801c03144020a02c01c09600c0e0405502408615108030300025a001c1104e80c1e020550300403119840c00a5010502088101b1440d540b26421540075291000d240c1080d03a10b1400501030b00d00402a80840c540005000e5070303940103681c0041001031000036500c030105003981000d40c1244461484c0d50b003401e00b2202d03480c81901c5442000309aa601030703c0c0302e41c11960104c66991200f008030040000c21040854141d0b03840304020300a020502c4c9010b080340c894501003001c020102c46082c400c0c2c0025004102c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193763785 1250 193762535 193762559
    0x106020c061902190503180f01020a0314070f0c060201271128090b0d05150c040f240906320a08040506090613120e03010e1b0a 56
    0x190442d01206180580c000100e1904c2c96009560903c4841410f0708414481c001c4010142c16040905800395117040c00f0502800d0301c2c014074081e0041c2e0204080c000428441c00c804601c607050203180324546000e54031508594902c9581c20f80700181195420041c0a0b0244217024082c04005404603030b941c40b154401c1210421001c003d0128824501e1000c05541c1310900c60745c1e04080c07042c40741c85600103c102103140c000b45000758041940707024044a5185848030300c0c1d42e1055407086c020300c1d0f40c09080c200e0004079200074015250840c2c09000101c0e0100d206c1ca03079000a00850000a080d0440d001c0c803010000040b284c0c034406000d8400400d01c802903002e4040c001d40114600340c000091200150210b00f0103000d1a0442c42d8034001c1a048101c40d8840c01881c0100c0c0507004071011703500d80c041140c1c0c035440240c51440c018885d000c2204000741d071340304581d5950440390600402c110f561001103800e6031400340c543d2540f6001445440070078412500000c204d69802d5400968440c01c0c11100f14203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193765035 1250 193763785 193763797
    0xc100c110703210318030203090f04150306020a0c0602072d110103020c0304031a060a0812122716350a300c05031605010e030703020a0501050106020c06 67
    0x20075000100802000d004c3c0d088200440403201070014416083d00b8001d444c0e80144800303a01c980781c0341892813003c1c03801c2e00800d1455071080c643c41d600300c2c0c03440c1d941400940c440000682400200c0c0600c0010401c0307803014084980c015203445260009903e04008032268005404070891510310b4035a000c101e4140c60510354110a080040e0360f911540c0022b4954000c41d44004c19240c211105129039800d0342c02e1035070081d10b050380c28a00d0651200c15103a241d00034464141d015140500180c420310700380080d41c903004041070b60301c455102000741d4500c1000303003c03030745810541d44112280500c5182504c85000285200d807100340051030400c2250300d5044180b00e407602040b07100d85c017140b500507050011034503c542c00850016805210905025486414681540c180000074641c80c145c0e4042c2c41600c041c80da0100107989456a40005131417860381114043d03546650707581208048050403c01071a4040c003c1d00204100859440c0c02030948005030090340c210b4104a00e0911941c41d40070a0f600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193766285 1250 193765035 193765073
    0x40f0609050f07080c0307050109061704030c1401021903020414150f030106080106020705031501030b1003080c16050d05060c030702010e010c0e1003050709090c02030c100c110703 79
    0x1014045810040c0c03820110982181e400d0140c00400a0361301400107801e40200c0c2d0070360903a90b005035035100544455046200c5c50010500107680444525042206150b0081c464104590700206a0300c41b600420f1000d0030144180c0e50016002014500b03850300e80d4802c0c41c0a00c1c0c10b5140604103a4040441c041da4803c49000f00100040e08890b043c0305070540706e03c111100340058483d80c1d1500c3c0144100028032500025000c2d1141c013190b83c0c10040340c0fa040c80e852105400195900c1e541e140b186141c0e0017415081c0d00c16071a8800b10000d0110802000321881c0f040c0286103151101c20320441015145e0b2104d807088203080c00c0b05000030004507240e41e0100e1600c1c211030712a9148002640135001940d2400c02d6540781180a6903d56002514078149030000d40d98000c0340b41519809400311281626142c020400000d01003041d04a00d4014640070411032040d01e04240c0041d106515000407031441002031500c030941c50319910342c4440e000c0486083c070760060114034a1911221000f15441041c90 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193767535 1250 193766285 193766291
    0x150d0c180e15040b090a05030901050c0c040e1e01061a030606190818060f0606090a030b0c070b090a12030506040b19090e07030312020313210e09040f06 67
    0x398030000c00c0c0d400800c10300071901c00e03115224490b4031441010042200c0c121081c046200c00300781104400910b07030040300d5014000314904540840191269009951140c24074892060b88a8540c0c596004104185c4100001080700050403480c02d00c0502128900251503858005c003000301c41c00402000034520f50b00e080356a6070744c9507134002c02d005104000c20315008000e8112500b03417803a8002550b501c10030707001015420005001a80c2510360500750b5680c1010940c0c40c000c5401458081300030810f01900600454846540c0e541c1c10b840d4120894920045200104110341800044000190700251001c00303020410001d503201220180341d9401c0c40201a034401c000f8034291115404280501c0380100003529103801081e20445007a654029020241d040601c110b03001c0c100040d0f0001a41d9050312285d00d141604100f21000307400041607600c9440040d003420340440e0841c000c5032000d0700c803031006c0031b60341c034211402410303c0110145040c0540024400c22001c02d210345416020301781d12040c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193768785 1250 193767535 193767569
    0xf0f060c1c03020a02031e0424080a020a0c030807020106090617010e0c030303010e04110d150f15050402030a150f0806060d0f081b0102030c0a1e0507170f04060305150d0c 75
    0x29107054008c03600110442c0042405006041161040805c07104955940f8405143d0f41e102c107590030f9001d0008031801094000100500003401090f680c0c0e80101e00e40300010f02690b4650012040d10f416500c0488020040900c0000c0d0046c02c0c010450b45c006040c005240003802c10b00426940d100520480d008401024041010000c80c800740c00200c880042c210001a06a07040c4454000707400c80000700364078070b44010440c0c004110f015085201c8074215600c0511441d02d01403202951008114102240d55100c0108810011501e814050000d00032030300042410108070300e1400602030034481c07054950150301c40004141c0f050001b03109500054080d160074016258451220f80c2e9000003681c0d500110410101460601c0a000302c0c005aa5413800143c202c80000c2003025900c410760400a9010410000810100c4419045000c0c03a1072000b882e1a40c41c0744101440d410503081140042d46540c1448101000054440842d0030100d0701da83c6444025658805034441c4c9100d0f180c40036520843c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193770035 1250 193768785 193768837
    0x20c0108090c06030a0501140f0105041401020f07080708070e0f0a021b0a0b060f040e060402010c0203120a0306060e0f010207140d06020c0c0109170a020f0f060c1c03020a0203 77
    0x20b440420b038041d01c0b02d51a420240d042030003030719090080c9030003140c2d1203201041500c1d0003004034000b80c0040c1c440e03902d000d04020341d02c4034811400c02140d055105028942c0c03500741c810001c0000038a001c0b806454442d040241c1c031801e11071142d0140040c03580c05014040c00110b02e03080c940c0c01912048006030340e403035801d06d210070b08060244402c03264004d903101d410a210442d519903104410458148402c245008108411240805101312155026100040055000f03c0303160541320300040c2120003902a1102d40d40f1540d010640400c0000d0f01c0f04400c0003025000010403002c50800c540c1c1e50000f03083c1100013543c814103445100303a0350040814001c01a2a82d03500c40c441680c00c48030540d80e4031035185100d07568140c801d054500159113840001540c070b000c40e6400b208060703080b0181c0110700d0540c003007281714214005050f502c004030801181099850800901c40c128440c000f4003d1184040f10440c20801d10000030418540100915048641d0210031a1045520824135034030036100011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193771285 1250 193770035 193770043
    0x10806070e180a0e0c011b020f06040e070201020903010b0a0b0a20010606030b0306090607090b090301111b010506010e03070611071508160c08040303052101170c03030307020c010809 80
    0x141055060410600f840040c020300c1d0003840c1e101201904690382e24841e10300448004124040103012444100c00e407000501d02810340c64440c400003440c403403c3c142c9030034003c546418181e40080c00740c2e40c0010a402141000c0c080c00d071908404680c0c44030094544010840759106100c0d044041160144000154034000e80501054605801c0200101600c403900034005103101640c00e4868414038002a928420010b6460b22514280c0c0d580906036141c0040ca070362030f0700b124804581c55500e03025040c8082a100c00a043d1049092991409580c0132043d11821030380064030142c10848142500c94050314002000d200320f0341c6a00d8400e40030002d07006100d0401c2c2490704110040201003c440200d598004d410074000d107a034170310700b201d10102d0000950703221a540d4401044030768144020008280510090440780c3e4032035003004804203040c41300800c078143c240c1001c05115224603045059807030403c2044401c007410360080d4a181054000603545151010455040000341c200159150200340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193772535 1250 193771285 193771309
    0x18030c060804150e0c03070f21140105280b060f0c010902090103050a0302070e0118050a021e0406090602010509030d1e0501060f1b02010e060d060308040f031a010806070e 75
    0x101c0421180f013600c1c0314540ca8014440072284244109800425090000601d1108079210f84c105e25950101c041c0101104512501701502c84000b004003406078018280100303071046004042c41a4180c100914010902a40000d80202e0380e14200201103180c445808840811004040b0b15440f88140041d0390301502c0074032002900070b80c2620001013000000a40a1941e034417036020f41d0764458a0f841030540700707102481050f040b04d800389100d04115059034090354008034200c00140c40c0c204900b54030119400c0510b80c400c06040f0000d001c001c0980d0058804019007482c0c40280258200041e07115038900a401c800b0108030307071b9940607544141d030040602258103041401400302d980d40d818042d00500d0603139441c1c800705a0680032403072020305070360510b043e556050315606100c0d5100720a00000d43c11490804c80345a690f50b4000c0041151440030340028002602e2012000e41549040c10302d444545104044110281006001958022440380e620651a1410200260701040050303e80c12100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193773785 1250 193772535 193772573
    0xc0b0c0c030c0a050d02060f13170a09090e03070f0206090f030d0309020a05060403120f02030c0a060501090b04020304050604150219111c0f03020d061a040618030c060804 75
    0x1403401100b12000c2410310342c1c240a4800e6031041c1c0b581085c02d03a12101d04072500c1d0802c90000000601101c00980c0821030030f40151516961084003da2002160b44009034290100b000318404010003007560181001100d00d0b400911f043c0200b5964100c141003040030024406e1101051030210780e2100440c000c4540ca00408680303440e010924081c00401c0e003c0d46c140e0042266a6002c1072508096003224212130b07002042c210b00820341041119240416982042140410000c800304444204183d4940c680034900001d002c1d4035241064080362429210b0740d0007a0b005004010210300701003001c030350280d00b190640f6004111a81150001e00c2a8070402414039030030650880407540c82504e89138001c207110204c6031600042084500301c1080d502c42e034000103040900e202200f070b01c6500901a150011000492a070b0703155814001c0d0506129880d201c001c00115003000220340c450300d20b01c2c9031281040f01c80f11980c259254415602c2a03402200c0a00c401d100101e0100f041c2d60341c14090a00318 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193775035 1250 193773785 193773787
    0xb0d020702030a020612041406150f030c1314060a050f010f0e1809010e0604080301050d03020309060c2104150c11030f0d030b0103230709090c032a0c0b0c0c03 70
    0x103c401244030751b40150780543d810b5070340030003800c41034000141d030b00d00848079003c030000441c258200300205848031920640d01402000d80c603031142d8681050300708181c05151008038907030a8003c1c0551f11000001c003914030420310010204039540b9804044103000d113003840c0c000c0960001e8a025103100401010190b08020f030000d4203554501440307444c0e401164070100070f22400c0350f82a50140c2d0f0304000d590192810000f04010030141ca05401d0f400038407403007030042e6401c018903100052059080b2014182d0180c0081900840c0420114643c07600c10740c0009003142031501708101d0240209404100ca41404100b02c280018400703100324001c5c00050040840f0008083c002440e9120300144d403024010a0420820b8034041d0f0190107030000a50400078400c44440d0304d001c20703d21a00014100c08144000703184041400c1649001d00311402200391400f00e0100842403002c001e000d41c00902501420a055242d41810f0740600e004402c80c4e00101010b04585410800b012584100340006c030321444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193776285 1250 193775035 193775047
    0xf0703030e0a0e10091806091a0c0c030a0e0f03031c050106030b030c0f1f0e180403081b041503060f0801020304020303030a0203101521060b0d020702030a0206 70
    0x1034032a041e03440600094824550890366203884048200b019144528000381c130a5043c002c1c42c280303a02500c0728200400752400700781402d0312420201c0351050401c0c0c540e17241c0c070000e074642c0c91240881c1c0398021034440342242c0380500f6220210f49900400560000304a1400c003541c2c0742d545c8020100d030503620001c0036290703a0b0900e44106101070208120001000742010000580c02d400380c4200e81140001a0141104c941040b041241e400c240c0e541e840c1d80134040031400f11000e02800c280300c1c42c0107001d4440d11550a4030b5000c1000343e407050f410070b10100b5000030801c00000d501541c95600080d0400040d40c80010038900c514140c05190803040c2c4d85000366115050150340740c0c1141d81220014640c401559449023035150903844101e80184d0035a104001080a8000e20b600035944040118400c281f4151200e800c01c41d200360285030f1400241c2e40c081ca84429043e1440e14402c50401140d0821409190440c025628014140c4071581340e5070202d078070703415500c042c052102c44a41c000c05190740c50f9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193777535 1250 193776285 193776287
    0xd0903090b190216060e0d08042105010b030613140a05010e01021305060a0f180b040e011d0411100c0605010609061b0c05120115030803190615030e0f070303 69
    0x2c1a000b504014803640040103902065409404160340c99640c07903205000b02d00050107040051039008030782010003040005401541603401156234042c1c802e031022100880d0920a083d01c0c1c1440c6280c1c40380d000b5200344411540120005501c082d07102c003151401c0c0c0c4045004908043d1035220203403595007010703807000070200c0650003410b40040849400f0350480d210000e1208902600080b000845e000d20002284207000c0d456481000000094400d0000c1d1075109404464005c0d034064001e085040380140310901444171103e20301e0720604086038a41ca084c0d125580508943c48003540150300248401d00c2880c481d00b10320000303d800c540c5c00c3c0720380c0d41d640c1002803243c615840f504002a1000f12500020040080e92050040d00544114a054180001c000780e081c0203113048001c5641c1d030a035090022810045010080d80207203205512403800c00700307524050140309220468503203440824050340c04880c000801d90300700e0785000074044001c030144915101004c07810014500c105d6a0000c109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193778785 1250 193777535 193777567
    0x60e0304051009080a03050306060d0f0f0c170a0b01051317150114010e010e0d061d01020f0403080a02190f0203070e06010203030412020106211709060d0903090b 71
    0x110002d49110400c03070050700c400c80c0c50701064043c00301c15030802c0e60780c00080382c400c902558104000400d42d5242030010b00243c4112001c14402881554403194208a1201b080c42100c545101c503007002c00400c1c02d90a00c000a51500034030413600281d4036240480182d04c21402d841c03240c0d040501d040445616803198909261051010045234480c051200003800000c54805040318200400407807451100c0c0d0055540d401d6103c9001d040000751700508030f5a6031908041a51140103143c00210990185680014188194100641c0d40c0c0100030070322020402e2011a0304030707a0490415a2115205003080342403008002d4201007843c400d02404040c080f00000401d5290b00c00c0302101c1c20155514a01100b503070085415a0150f0000e1000030007080b56203140101ea10710500c00000c0c2151035600b9540b003180c035071100b0fa0030794180821883c108032941e03c040703e04002d4604030740e041410880004a242c801e07103010080345600d508002080600980000000c2c0c59818500c586a03403058485043c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193780035 1250 193778785 193778789
    0xa08040c0518010f0605071a13081b0f0f07051509042901030902150304030309051209040e030306090601120905011103090c0906090c070c090606050903070f0e0f13060e0304 76
    0x48001d244c40002d0035a0280d41102c4c80240c1c00781c503405004c0c3c03a00070404600d5200400f002900142c190065001400710f0300200b410b40a8124122600144464003d14100d5403080f9400c80d0307840b40e8003504100300001074060881301c00b1501c003010506e00400c0f410b00b5000e038048581d08181010034651940341c41554114400d030030004405404840c1200440545c2d61810000c3c0d08440001092400c10032000002c580c8203001c0d0074082910400f60340d030a8a0140415640710307a2203004184042c1c0f6207810301501000e1400038000314110304010b40001c12584010300241c0c140109006000066070f500e13004039540a8111008124980003041c550a1b15441220184058000c2c5248002c1034901000c0c1c01d80610406804c444039540c5140703005149611040c0261186010b60100044c441a41c0c021000a03102903a5103507124003250381072600c4c0000581044821401d242e80901c03510340d40450883c0d1003140908410100d4551120455031991103140140c400d604015031100c130100000010301c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193781285 1250 193780035 193780049
    0x402040f150f0507024b18040c060f17090615030610050103020d0905060408070203060907060c1b180902090c0c0c04020c07080706020109120c080a08040c051801 71
    0x21002c0604000f02c4042c413400f80025801142e43c000071206000c0e04401d060036402008030324040c2d084c00031203088003805504642100040d060303025556030402e91041e007403c04a50b8442c5040d42010342d60108032441d03038080c550420010308410221644940095050300c040d8000c08409810009025521964111216606840c0d03940c1822098280041e0f0107201c3d07a404605400c10b5402e000044020350700082e4121145512040507001041041c06000d0080e44581c0c0f06a640e012544140f43c20003200510341c0905411001c0f041140d5a00034505000340b60f03000b0300e00ea07800241c802d1103926031001500191110302d00102c3d85800329016510000407a4001c9480d840681d840c0c4140a5841c0314000c00305410790004d5079040c0807818a42c000e4412503081070141c403800c4e81c4445801d40b40001c19070050340180e4541c2c0140050000d0b50400c81c01c415620314104442400a0305d8490140c881c0c1c440381020050013030300150520181440f50400342500402440c00b403081901002c110010a004101c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193782535 1250 193781285 193781297
    0x50603072a0203030d05041b0b0304050609030304031403070309060608010f0b09100512010b1203030708070c020901270515011205150d030309060c170f0714090402040f15 75
    0x2400c00305a02205106a582c002d00451400d0b41c100018400303402c024000b101c070455444001510101c1a101c0755000c0c00640c0c2005442c0e02e054203240f032600e400980000d229400070014000402c0d0310101200c100383d008082d030b0781d0344e03116010203c000b41518a0b018010398508040800d070448103400051000040440900c9281664003c01c508840140c41203039801c190441e041005080c14a80c1a150a2006000041421107000400c40004005a1540b02d6400020030012010b4201c50140e81000a61031f1625071402203501044402c40180122020004500160340b4105194000c1c81800b800c007410030b0000d42011a00100401d5143c411907010480664540281c0f00315442103500c0362000c3c2d0f00848503000880c003400784212100c007094007016150007500000c00c90034000c0c2607100c07000b03644019402e80d00c00d03070841c02c6060107000300c3e9480000500380016590720207141c0d11082100240c0c10f0342d42d841940054028440c0b580709088910b90003800050300c6a100041d4654034440c2e444071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193783785 1250 193782535 193782587
    0x1061214070b2d0403050c0108160221160803010f1d15010c0803070c02040605040e0604060213030c03050d1403040503040b0901121410090b03032205060307 69
    0x500c1c1c071140035005403102c019091202001c5440d214120300c00418a00b0359039500d540000d0444682588150026282e55000040d590010b5a00083e010303809225030a440d0040d012201c8000c0d00c406031204445c85062996100101e00c00c441c9007100c040c0443e403040340b9001a55071620300c070300750424031608a202803c4000085d10811440180c205246109a900c40302c0d0344032803e4908824040759454100a1a0803400d0000b496120007180a400d40c1d071030304458480d60744100815108035800882c044c070300300f08030200001030014886411642c011000340c2c03034101a504500d42d84c0305079880584444681d0000005001001c90307442c01030802560740100030703000c9810761107061000351801480d681c8100000c2041100010290903800ca0500d0300b0000180200c90070f00c1581e41807170001c07a00810000038400c10001204160380144480317a4240003181840000039102e000d42c0e031000030941c0b08003400340e21040c50090040c015082c010306184c2c4a0802d5680103054189441c0f031f044203241d0007094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193785035 1250 193783785 193783823
    0xe1002010c020c0a06083409050a050609030303070c06110f0304020a0801050405030d0903051b0d181d0603100e030a0908030304020d060c030b030d0e0a0b040803030c0c0f010612 78
    0x1ea00a40d031550306c0700760311515000ca8921000ca040f20450042c40009600850041044104041e07040b220313130340e141c8441307040c2010400f9440441d80041e104070f404125403405a18044142c0c1c0e8003a0490608540c0c2907250700b040c3c006032250700040c5c034640000240f140e410440b54000356000d240261003800640740c41d14251822198152805080343e4024008010b001d00960401e20889100c0d1038403e0901ca4549500740030804005021000d98014403070f0f00080703650010010070000f9480103020b1206190104054042120a00340c5100240020014100f40c0341080301d508003004244040040c2050703181d2480d105c0e0080f40383c1800149404100084102e4004292801039400800c20f0005003003c2e59548010070000c0b803c2e000381038a6500002039507805001c3d41c0600400c40e256101942c4012041040c4000e5542100b60781020900051103412400801d89601c8a0050b01142d502c41010300c001e46410000000c0624941c244079000c40c08000da01d052a00d81407060070740102240c22149 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193786285 1250 193785035 193785049
    0x510090c0b030906010302210106030f14280c0e070c0209010f06140a0c05060907060e0312040306020903031b030d0501080303040b150a1d010f1a0301030605070e1002010c020c 77
    0x10b800241984407038018801f44c40c0c2a1122140c2c1d02ea074401b50072854504003805800d40300c00e54010344040100101c040c040c0321458038440c0c1101741e184007a180031103200c0c41a00c0800c21420f49400c0743c014005041c0704218081a8010141c0428040c503180d034a4050801030148074001c80882c022a0300d00300008034504141c0500d010303074425882d155208903414459402513040303014081c042040c1300026030003044c02400440d003c1c1c0054009030003c181006000380c04002a07080c02030007039004252044101c2c81000590b010760b503100c200965584d22640c0000d02e10300844035410006540701d5120070001c6400402044105c240031030602c00c41e80d07070340791844c2c60340000c03035002d00054401d800240003a024809046140003004000019540d2982214406041e07030060240c5a0b059050052144e01070000a0f50014062024030714031540756402d0107102e070702041c40000c1c42e0365116004240b4440c000c074103031202c1d907001825910040b030118400070301800c402c080030400b41c0540840c020403414225 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193787535 1250 193786285 193786291
    0x609050108010315020f090909060a1d0c04110f03010f060306060e01080f060a09020703020102041716180209060c06061e0a14060d09030f08132d0510090c0b03 70
    0x142c188640d41c1000c090300d000c1e610141c0015251b0b44100400c140942d0b030250500d0280031401c0061205152182c0040d044a01000040b40446080b80c0c00e0104d04c2c10001340d00803142030994001c030ba0081512001c140e14003585036199040a0040004141c010828511100301c030782c0d5a03000c2c0b002ca1781e20001500e81140743c41501e03000480003000075400b40c01c1c05e10819040300d005825089880c0e0b8030b14001040b60403a500890040c2d4000404114a80c1603000d140c00200c1c01e040944600c02d0102c0c0003440c103089a04c100b20b418009500304005044066065611081028205a5a43d010304100e60380391441210264130a03650100490f05a03a2a079181c10030395000a880c040c0c41078101b0f0000e405c051013207a08158041d200304030180e1030003814064140854801e8031445404190444080c02e040c00041c180100460351200581c04108280189075004042d0640540400c1101e030a003020060507038130281041c4100c49054456481c541e0280d4611400740c074804145075221800c8c07840511040d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193788785 1250 193787535 193787543
    0x1a0106180303030b01140f07060e06070804140a050709050708090a0503040506090d020a0905040308240d02030c031501080c010c020907030b0d050703031d0d020109030312110f0406090501080103 85
    0x900e814030009000380d01070698404141452451100a108201800d5015080001990001140e1b2208200e03040c09040540503003c0040e2a5a2511000051000100400c00303000b0380801c20700c203400c1200134401c500302242c10000351401e05440300300f00c402401d0f007582d4000c00103e030000000c0c803049000c1107850001c0d81c4440038514007450300d0100121034020682050b032001142c1e0030140103079242400507004100000000c520ba20306400d0240020800820451081c1111001e10650b003112444400504000f15905224001d050001c01d01d016820b0178a25018400c00b9010881082000c400504903a144411220400e20b5000111a80d90340040025004611000894115402038000610200c8050700021200032030780c0700c840c41d101c07082d40700390300ac241110901401804442c2000400190642d401c02c01c10340c255000800a0000f80700250030400d81d150300100c0e40c20190003191602c0c824103a100d854200c002050491a806071043c03401042200900241550050b60301904983d08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193790035 1250 193788785 193788827
    0x4151d01080606030a0b030604060b09060105040b0403020d060f1d190308180a0503120106030c080105030c090402060c01290301060b03011203090e0906070e04020f0702010e060d091a0106 82
    0x142c00b06100c155000034240c503100503100c20411406803810071416100d039016203004142681580b0501014070b5028042031304101041000b40701000e5880c048504807941a100d10110740801d0605500509000001050a40c02d2002400d00301e880c54000c00203005950381620f4a00701c3d55402010301301c61161004000c07c20200010b50300c1c198102002e06030500071419101c98175619603030b590841e8020007850711190020001402420341c9442100e00c0c054990428044075410840002c3d51502e411600601c640080c100190441d15160151080103901340020b01240c26440c1d240c26800791881c2500000c441444c101404900c2c0500401c2d0456001382e0031107255908000498503140102c07203094051014000000500c803140301c1e54584035024904c00b070006810040401481c02100b002c071644a41d006010341010b110a110444480c50b0382420f1032048019401301091150290082600c401c0b4540302240f41404040911290305050681610041d80c2e210303c016144050040103182221b84 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193791285 1250 193790035 193790041
    0x70b060a140d06110a02070303080a09150b032a010e03010507322b090302030406030c090b0a030e0f0105100b03250914010c120503180304151d0108 65
    0x1c00e20909009607010f0724000c64681d0f03404040425580c001d2180b800141c3c0081410020306a11801003904107004040c180002c0c041e039218030742030035a050814801c0307030b9a403c4020407954003040300c0c5040341034408000365101222844954490021108203000c180f2100f80391001d807030103101d110f10903290760b1a02000d405000e0390751103038140315141184d04021071504407050040d202e0058100ca01b0200c080c5416068039000d9000c4504100f82ea5484950500b15002d00082d004029142591031078030700003500d21501001110101620b901c0340c02c011600042c4180c2ca00e9064205220a03100e0800311800740d003401c0d21860807504211408603100407208014000c080c00704000355001810403011201d8081307400c3c49481014a1101e0315004254500010410107102481e2022000000d00300b601d002c041c903440721480001420400c104015000000400d001c185a810038221a5408212a100e07a180c04502007403006282c80e42c070116250030140b10800200414010040806a441180c652 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193792535 1250 193791285 193791289
    0x602010b130509030c01090503090f030a1a0709031401090611040b03040b0414030a0908060105030d14030603160906050a0504050103050c040c0e0d0507090c020f12160c03030302070b060a14 83
    0x405003c024250008220350500e400e03003400340607a0140204007075943d0b00c0c11442000b50715030790300602c02d0280d004a80c4220201e11005400801d070401c400b250b0405580f42030007110b000030580c000824603400700c10406c0c9440c2055000352141442800c082056510740644410740d8003c1c4c0c070440d4145002000000c0006544030380003030704030340b0500c54030042c240780250007804c42e0400d41074100000c40d401d4003000551002c100d20360040205901800384080349000040c480300a680413007008190000108900703403020008900b0000c60403482e046195116541540a0a49032041714401c045807240414a441d151046504881d4130000801c05504c01c603003404003a1200c40194170070b0000303201c5c0b2a11942c6451401c46902031041025000341030400444400b00c642d914401c0045500c121f40c010205140000ca1628418010046648070a041d07251001c4034a900d03100100304c000c1c100c0c800030405130950054524144543c07081000b40da03500341404000c4c030319889440758072107614407500780b54 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193793785 1250 193792535 193792541
    0x10501270903031401080d0f0305131e02030a080c06010504020a0c060902010c0215071704050901060c14120304051b06030613020408030711090919150b030d0302130602010b13 77
    0x714401d050104000d1449064503003144000d03070082c04a030708100c80040c0f94950000c0490030010300c5007010850307420204c1c0c140540c42c100c030b900101003172042082c6194111015210b9141c099000302110410030182c6006c9003540c0201e00300a0143c440c440002c600f914240c02038500340300d940e0340c2d40085036150740c0315100a44280141641071000d100d28403000f6807650000304803c1403100b628280d50f201e00d842c1107150980c000300201100321042c002031085a640903116811a8045c1c030744241e1001c0942040c0c0c00004040720150383d03038415105481d2901c40340710061803250340584150380e084005401449481015800c901da4060310400020300b481c544024030101003942e2410043c2003a40301c0840a2459011060507143c00c4070006189002d441c0c130048459000c11000301400c0320030008100c80c511960700502c01040030101a5407100350070502d80c8030001582005080741c0d0100d00c140e5000e0000d500030036103042c11803422080400c80b01d005000d44890f800c009032241005e0000c0402d50801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193795035 1250 193793785 193793801
    0x111060c04150816050a030902120606010210110f0901110312010510030509151513090b13121b061503050f030f0405040e030f040905090705040501060f08070e061b01050127 76
    0xa0503a40c8c1d43c54000340e00d0304402c00c8800314240000304268103040c400a03140903420341d0083c0d8900e003130032070010711900758409071541e00d011690101e40707942005c030059440700045000d1171761520000c5440c0481051600c0703c1c03070480e07005440d003241601c0624011070a44404441c03421a60f44810170f102c1070112800e40c0d95501c501403d0f010584101c0c00d40024110025450300c02d280d2940b10000708007840010600b990308210310540c102420107041d940c0704110785600d05143d007800110b4102101240c1c2142040008644c1301c207080001c481140a20201500c07940001d035a1071113000620012054004201ca42d44666600150301340b80c074280410018210381e90307442e1000c0c0014000803100c5841c141c060700c0a00790702040890709207030600e440b514150159116038032490a0400403c909174010103d402000c0d005c0c031342545283c0d00d100781603c410f00300b0f40c0ca0075000080001c1070000071410100c1003154070320160080c070140c0da1b0707102d40000d4a00d03840c58070b44400c81c03030040601c0848026440526 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193796285 1250 193795035 193795037
    0x1e090c1713080c011e0c050a170c04090c0206041704120b09070b0301060c05010b0907050412110616020a0503010b011e090b0304060204031505150607020111060c04150816050a 77
    0x11034840d0f4444820b00f5a0411440d0b0a610101d0400e40c44400303600e40260055480185042d1b410105000c3c401480510100c0142c0018407c800105410881c03070b20448001d0070458505101d40d50541c40001e5480c101164150b070703071030096402c44400e04c1d000d00458040b00c124010000e440314464840202500380504014034a01c10490002703080001880554000c1485441e20395000384181065801c3d070b04114030300b91148480340d080241c0079030031505480945140304600507401c4882e1404d69042c01e9003000301640f2540215816007800b41120030600d01303074401d440003448141c1d01c80c18103090718a40c2d01d42c14040b81001280004160103209a4128002c5c00c0c5400c000ea41e6980c400c002c1542d20644007990602d400280a0080c0184c2e08100228540b402d00c1c10420340c540707040c82d400aa404d09441e14414100040d60000f5a842510400c0030b08450005584c018101140b620b41c1d250320a10a2020f0508194290072072503019480b203903c0f80a17900814080601300400c03c685550003121440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193797535 1250 193796285 193796287
    0x50103080d0c180801060509010e010f0e1504090b19020309030412050a06111b030c060a0c0504081f060501050a02123405070f1a090105041e090c171308 67
    0x3c640d180c0c010070650007414003100001e1390606000c20720008000580200116907003800042040c4425400400111000b801e169011a00c4051701d031560150190b200a6000b41040703121f806211902c0241401038620f034103454110701020900d20f040c1c0c0411140c1c25482e400503c410403070140d4204c00051001d200d83c05440b9952203d03500d00e81114001201ca5110381c2000c00e22031001503040740c4805640303610900940c104a02d0308440c640d10391000f0910304401d40c852800c0b1820071b01407010b682c050300c4ca0340c05984610400d14107401c4469010b54a940210381048400107030740d4002c0e01221245109540034241e0800b5494580160b544441322800120b030000610500d070503078000150401d1903050013101458003290401c00e00d0122a5040329034800c5800c20100076440c1242c04086000b95815010b41c0c8840c6010010303102d90085520803604110408000c0040d00100f4a881d416656861000c0041102c1d1200494000f0034000280020003541000f260041407401695120306105210791 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193798785 1250 193797535 193797557
    0x5120d0605060a03020301031b032103110412060f050c040e1b0d0203100503070f050108180105390d0e120d0b03120a080f090a0c1203020c04050103080d0c 68
    0x80b560b954040700c00305000035030110045c820010411030307491041c400051180551410b549845103031030001c00800c0c8030403c29001c00ea2020303009810030109000c00c009003645403592400c1c22441c0140300d100032104a8503101310100004018030440c1d010f847c01410a80c2030030b082500000610001500d6192000fa4907003d960620902c2402000160716032400580c8a09100703110340398458a070b8008a1003500a0300f13040c0a07445004080808403602440c0c40c04480e1075080390b04c14658001002c0c030b100c075401e02080240d9114140000407813014041e03902004032408540366a10500c42c28540c500352481008440340d03090340e0381c000b80071009a00d401d8503140580304e1032a280035403180c006d60780c3c542c2d181c1d86035240d5442c0900c042e4000e0403040a0030740c40d01c2c010841c010324400c0020010f084e00254a4080707021070b007040080c2845c043d480110f032540e140c1c030343ca00c511111400c22001c40c010b100d07089404681d4281030003194101e81c0e1080708039080c082d460f0890000341001c1500d604c01c00200000d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193800035 1250 193798785 193798789
    0x8070504030605010f060810300606080a0506010905070203091509280504020c0d050304030c0b251107090b0402091f02060609040b04020409080405090a0506120a05120d0605 76
    0x70740f90090074040e0450100c1440c003140035080c040c005100da52616401641007082c103200b002815031052105040c407000601c40c0c4104a608582d603540a8000b9150a2000c9022400050400c1d00740b1b0044080b504d45030b0382c880303602060350421a58040160000d201c000030b203041808a10318042c1c8200b610508200d03540c00810108034001d074030703880564040000c10b520604003110581c09440107440541c40c000c21440302640c0d03000c0d000824010004000002418036115a0765248550761251f004000c43c20641c00203c0c0302640e103101c8d41080d0507502821310526004034071160480000b0f4020740812850701003640d0081c5800108541c111b40c0030401c040803650b9481051680604605480503900c3c50424002d14041000305194021101201807201147d041510389512039811100460306204030300d480107242c051a030bc40d5801c40207240c04e00082102541200384a460183d607550108404991520717556111081c000e0030b941c00103101401c040e100140100820b280342c540206103a969100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193801285 1250 193800035 193800041
    0x62d061b0607080105100c020105041a040e07030e06060f3304090204090f0b0901030f0c050411031e0c0d050a0b06040e07020106061716030e06011e090615080705040306 74
    0x80c80e200060343c5440140640c2ca000c02507a00419200e160481341050310340e00207803da1145000714850f11244c200441c00144490040b80d01910244e40d5042c0703142003500020300507140140d414011405880009045818520348103039880000804108060420713008611201120411081c52200b1080b096121450110f000780010a010040180e90310310b4100032008407100f04d000c540c04541005400c4c440e80c0e848080c078906407500b000c601c0c2d080b840180380080102c0007039400560014148070800c0181800d440181d841904c2c684d800e504c0c8519030a0501c1a500411200c010a44009005404200c10641d00407644900309a500041004000001a590307402c19070280c091440000f0400199075428051a002040e4a01b030055420031140d40416084500900310b200394a50f40c03a4282c90b040c403c1d04280200751450040e15002e584900000d070310407010044c1c04480b00c5054000040071200c5118401c02c8a90030f502c000781c00010100101c1e440714020701107000b0044103000100100b01c0342c0c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193802535 1250 193801285 193801291
    0xf0e04061203030e0304080a03051309050109090b06010c050d1b0209090d020709110904180f111008190c0203130e010510110a06050a021c05062d061b06 67
    0x10392440020201c40c0303001010386003005078283c8103802c144001c000d20100001c10b1440586e05040458071051100c140d800c080c142540a1240070b41844000114100c07243e101e50704a6028485000b415603a420054520141c964001070565100d03d0a9030070f01c62086a0004811203210321100c2a240079400107400d400090380c0401355600030003041030b9000c0d010448240181a02c480a0003081c20040d4034400e0383c028028414051a10b030380202d07403031803501c0944030141c90b0710149060400106042601310035510010140c066007403240346424060054010a00c9451b007076087e012081d2100d41024080d01510541900758030081c041c42070500b58801494024000071b19041d4850761500b000c201c884842c0001c0001881720811449928200214510001350342010300461980c42d603403c03860083c0b0031000002400f152003d05183c91401d19007059005130070840f8482a02c4588101441226411070a04031005404140703601d0b05040100113824402940803440380c040c0b03103076080740381401001c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193803785 1250 193802535 193802549
    0x60f0a09050a080c0607080108030703032304060605010809070b03042013050901051e040b0603100c11070f050d0b0903090607060e070801050c2d07030207030606080105070e010f0e0406 81
    0x810402060f080c00c20060360b01042c640303080c11f01549064903441d103d11032040d0103000c040e10350440300d01b1402c01c580c50644910007200320300c0a034540703400d00c100248254000d80f80002d5110011400c4640c0c00039440c400d88041c01001c6103151240e917154420100c000440740c111540d110904041565102d01c049050801020045800d1a14440440c00c503600188031041c045509051000250410110283d0055000342c1030103503504c510002030f24001440c1000404103040400b4800b0161380703c54060b101309032060443d0081504e03008030f055088054040e40e0f800080c19500d020100c2d00100140d9013060340e220683c3c1c501492007020400b00c0c2e020000a40c0c0c41d50b12020207900400040000100034203812000300414149041d08265a10900c0d030314404020700000380f040c03d190025803800e0143c08100d50076a6690040c60042d48400c40c0d031005950715441e00030000f401304c00c18000c4502c01c01c0d41d6a02d603503d001c1404015681d407041d80f0010b404000001d010300280d510340f4070a00001d464070f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193805035 1250 193803785 193803787
    0x50a0b130308040e040c27150b0408010c02060105030d0f05030406020706140105130b0616020a090f0b120c0102030a080403110d02030903011112010e0403050d0203150a05060304020102060f0a09050a08 88
    0x170904102c044460706a001142e0300411001c8061150303d40c6000f2029811030000c04600708600142005814209401c607448503000000e000441400551111040d1005a0207071112a1f0b62001050307250b1510321001c00c0802c1c00f071031150202c01d22400081d0390003403058100604003116501c1c1c1104440361581a0007007025001c005008a00e04206200440b05d18904c09101c0e0184850100d003ca0060012100d0182c4840c064801150f560701011009065068400c105c143c1076184020040e04a04d0290b5000c0c2200f652014032541c80466008080d19043c0c000318030301003518500316014200144140c0400c4040c011001030407405000c582c1c08802d10b03500954550000d84101400c450042e248844083e10811110701d09440c42c0c800f690441d400000c4040c02c640e0ba6003000c2d10f45c0e2103220510032003a40300108110102c80400b21120418409407a0810701c01d4503002031000d41c0c0f00079640070740960300140008500d1070414040c644d21080391000810510000d035105031602030141e41c101c0340994 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193806285 1250 193805035 193805041
    0xb0c070f062606010e0f1813030306050a0b040323030d0603030e0105071a090f070f03030207050409080d05063f010c090905040302031215150301050a0b130308040e 72
    0x203282d40c5456149254800254030700302400083d2125928601c0305008001c800030f202007a94844c50440740f86071325010030310001d140c0002820241040303554200c0110b03180c07490214640c200a00540142d88030900800e103000c1c10b41e16440702d000b08800300020f0f612001140c66100210510242009000403000030031070381d04503d405001c59000c541c80304d0410400340b12030004a14440007002c00201440302c4811306841e0b5290a50030302c441100d001c112885060800502c90020780504011203000c0e60941d54565125000c00c030554500020182800c903003400410502455035101c1a0407900080c103034003100c0200030144c100451402d100b40c2c101450036003c24210603c002c8402c1140707482030000c20100c402c0b450302a052180c58000c10004030383d2040010300701402041200d140d0004660701d501c0d01c2c030b060400002904480b07122140204021010030b00500c0340701d000c0e207042e6a0000c1081840604100103c50b03560080b20b244001c00c8041000000810041d10007000a09407441c80d00680780303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193807535 1250 193806285 193806317
    0x8040315061e05010804060914030a030c1407030e01020709050a14060a051c0c030b0a02030a0c0801030308181c03150e01080c120c120d1d0a0b0c070f06 67
    0x35032140d100c028142c2d55440069a103481141c190410343d8402d080034007650701c85d030910300c00a21f04844003c1c80d412407020414140c150000140c5100c0450740d1f010b02880c41401d5048800340c11020785813401b00000d2141c00c0000f40038507180c1d18002010f1045840d00350303403082200241e0750117440c03031100650394507030740301a0000352400264864019613541d001c2c0740c0380ca400305418a0060361f2248102c103901d1011010881c21503001002140c000441d00c10600302040450000e500c15180e4048261401d842c2442c43c42c058404a4101c0760075455210300f40c0d82d03840d9900d480c1e4001c0c4010340d0300d60091b202c0a60100c40a40070020014032255030004840c0c40303040846400106580160f003599140200400014100085012040340c0c03d48200c3d0410044a00303d5141120030005c2603841000f40c089600080000107140342c80d14220f40d900e07600e980c0c9040c1042e034a5099243d0240c0c0042c0700c01014030203054014020680c0c3d89640c0100c44001e99030300c0c0d001c8001c1c1800d4020000041201c10360003980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193808785 1250 193807535 193807541
    0x30d090c0914040503040623040b04091a0a05011101090503040f0302010801050a0f0501030f090203150a180b150d050a080c06070f0c020d02130204030609200603040605060d08040315 80
    0x702201102c14070716400c20b42c6505a41380210b01c6101c00f088041da03c441c0700f03418940c1d4a82e544012140700592a1507c07080d480740325401901400d4810752510541c52410701d503004400050207005012034003203500b060011107081e00d64542c2e00203150b48032800390000490420040000340b020b803001586481c20b6100041c86800183e1101d4803070800d1410174040c1d46516450041200c07024240028030350022100d00740644003a40340a517040c09951071008000c017400381428880c05158100700071000c94000036041c4050410300140503c44030307400040141d540080c0040f00300380000d00100f142c04881c3d40309850300300550b600b211004408111584456001c206094001c803c500300328000761142c08004000741048840071340301d000c00b410340701c0c25034840d400d06000d85418940b041d561035440f0300b00b04001c5c0040480840b1050b40e001d100703d41c4030400780c0110200460090080b0305c0d40d00d41b62100800b4141c05019940d00c0045420603000003030421000708019441140090080300c1c02c0c101c10012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193810035 1250 193808785 193808801
    0x903050c09131506230f0f01080a050403020c10020f0105160509010810030605012408011406070309090606030209030c030d02190503090a090c030e0c100315050d050c0a0b0708040504020c030d090c09 87
    0x40c031f9042e203d500b2140e0308140c3c92035210b082140000384680d10b83c01c040340b0b480388410910340c10568a03d450400c4a5020401e00380c0c40c04440028006919070b0100c0b259080c0c1c2110301d400000c3e00a202c000e400b58890107015400c000361041c2c0d111220b403603450303031401c5440c21382c030456603004290100d02c080d800001722111800c4803404d0003d4a90b140142d42180351140d03090300b522a40000810404260003104003034080d20041200300315854564001800a621408419209200300404c48015140c0001c01000c1c0c6111a4043c0c00100201180d1506282440404481c40e010a00c512030301d80d11002c590300002d1078403610225107003001c0100542122066403040c4415001200c014480b43c6540f000d1480550b124540045c0540c80041f1043d509001a048a640850011174950038800300040312403040382e0407101d10340c4041e07803400844818070503030700700404009060008000707a140a0740030306840400d00d800d40e868660694000400c4844851046916002c0c04201744205507551080404c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193811285 1250 193810035 193810039
    0xa02010905070e0103080d020901270f121221090807020a0801020c06040b06041808070c170a0201030b01030b0603070306030b151305090106150903050c09131506230f 73
    0x25411a15052087e00c548045144d4442d000101e042c0b459128014071500e591098038070390b014800080610800110710305c00c02a4500d000743c1c02107008218581d00d40da006030300841055181b420f03d0000e41d9283c2801c2d0710482007030060400610507051a0081c81c50561040103090b59502e01441040f80e94840380c0c1080310309a01c188040e045000000480542168100b6107811083d0742c0c000001c1c018003114898000410111902c60041040d1000500462842040302410f45074031009100d440f543c400b2007084059010024840142d4040e60025503041018035020603180700000c0460041d84c41500d032640000e59610040003400100307000703030750400f4852101c049525a41c030006854003801ca6505081c80f039035800031070032140095000c18020281c02080103224041c035603010304160700502c03040e11a409002e180c01d200346010079002e0310030007000c0080e400302151903c8040405c2c0d07020502e22040c40e603404001c41d48a401d0102ea00c3c404101c0c20114086122450a1001003003900701c41038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193812535 1250 193811285 193811309
    0x1060f03090f0f020604120b01031e0302060c030606270f04020a050a1206030506010803120609040b07050c0708070f08011503020d0b19090c05010f080c030106110c060a0201090507 79
    0x400010b1200c030010a4481c0c0160200074511002d000040c0360b440342d0350140d01e08901ba4250740f0701b00030041282c5812070f8080c0c001500410701203514840225805600280181c000c200014030681041c405160407000c0030b8a07d50600c48003001c0340d80c20b0f1a080d031410300b0340029820f000404e0300d4825400342c02e000050340c05504090701c0b00006032660194480d61414820982c0351840d59000d50392144c4015904141103039010350b07654001a840c1c0c3e10101d0202c0a240c1c03808001105070414040b41401160b200c130890743c0c81e94070038030115090340059058480b58010102d00066200e42080100007401d46103580c072110500e88401c0ca800c49034900c8000d1502900407108002582da0700e0300c403907031050b044545a1017aa0f00c06605980003e00c0540081c1981d1401c0f038510103011007451500113480d004e803105040c07820621005e41c4e4030201111241e00c1d25408000612100c0c0c030429040404100c80c00465041606090001d070164014032140030040c0c0d910405003003031080c200680c10041010602c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193813785 1250 193812535 193812551
    0x1d0c0111070902091306030305040501090b04050105030a090807140601080d031a060f070803070c020405090f0a0809030c03190618120c11090a090c0503030f030a0504140709020301060f03 82
    0xd81d0700c070215842400310702503021544446070307103c3c070301400e00c400c0c1d88030820402c49440740781c054078507042805034900280e2450001300c0c000300c1000448040d03910585505082d86c0d640703d6074030064aa10075040700d0414003880214009022002d46003042e01d0014041c0c5a6581040400340c5000340c0f4015000400d400e015000d03c1c0c0036640c0301d980740030050030344489903501a00402280c03280300c0e00400512848000040001c01d46e444020b0f44071180c400c0b00d00b80034685400c0e603100e5450940c046000c44030380110114100151050004040070007000d4295000c407800e08002904007180400d0a051000c544032003102007001c1c3e031141000d9408c104000c0c000130807aa44030101ca035410546a041481a150039040c00c1c80810400c05400c24002484183e046c6080c03501c4101030498084111080c40080b04081501d2a0203c191401d1003c201c20361400d42d034071107020b0005894083c009a030000b0451550f014003180500c0f8141c0941010700303002d84e0b654505000100f02020f40a1a003041510741114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193815035 1250 193813785 193813817
    0xa03090813242007030c0806070e0604080c0f1302072901080304090c020c0618100201021606020708070f0b0411180a1d011503200901150c02041d0c01 66
    0x1000f01e4042060f1040b4610040d2640b5840c036007100d54101514502008000003a01300e00001c0017445282c00b996041c64440d0000240080b0b40158090044036400c1031182e03544e64280810b0401002400810720f104403201c02d0f074410102c4e0b005c824166803080d54590310f0041d001c1209080b10300c40b590858920342640c504040c480d12030290b809030094050301c401058031818420000c4001c50f80004040540c5c2e40740059242403448000d2108a0040815660419101d4018030a07204c0c2d0f525000d0445040d403a081c0d540c000251702030b640883c0c0040c1e00740590f90120b103440301c031561007a1080220359140c0c1050704001c0300e400062401e441c45142e040412442c4503140301c106c035411a40414002c29075104c81c0c84150b0040d0103105034520701758649004600103060800d0140100c80c0110326440e10010008160b0300307241c2454480c15080364084004018035607800303d0030240d40d4240d1606501d62000350b40010f0590303441d2a52003150f03a41103c01a84008000d1000114003402400c00707482d0b140c84008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193816285 1250 193815035 193815047
    0x20c10060f031703040807120c0203061b0412051914060a020703020307030c23010c1b0f0b19050907050f0d02030a0605090307050304030602120117030f0a0309081324 73
    0xc0341c000c1c0f40c8000b001180400c90120b0603070300251b60014085040c08401d4900920504000d0800c6c0e10134440c10b40420209a8150303c0840140046c11140307252609100c0c00400401542c03200b104c0c2d6100f1109028010b0720046010307280c0c140720b8245581c8102010340d11500d0400e01a00402e00548100170ba000003d40000889100c20340c1800c080103902c3e0141000f0304424403d189941c00300003240811182c4440c19070040c45210711a4583c0b14144000d0000a03421100086000307080c5d4000030301582c0890001d00007150321012906c1306801c020440013000050321015900304480e617200c4041070100745498040c00741c00140c282e503c0707540300d14035400282d41c0308518031000d002c460b540c07004034400e44802d1040780c201c29040030480356580da0f203150540c000e50107101ea5509003400c08001281220030a034410300104c9800000b1420305882c0c6010040ca0f6106c42807040516503114011720010b168900681a69a4000c203881d41c2e0500d840c0ca0340740c40c100c0c02881001da240d034401c21240010380000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193817535 1250 193816285 193816313
    0x9080c0405060402090619082a03091f020a120203071b03200601031a07050a0f021c0e0901050910180b040203040c0611060114061c020c10060f03 64
    0x10303030104054841e8004038000f4845c603403143e600403c0010345110105644c04403154084025070700c024095039000015022586480c01c121522115140001a24868080650b03049070b452420384482051040403100704401c8091103130f40c200d4010400003500d54002a010103c0d006000040d071540c6080c001c005d0007294810203000c00f00c4154035001c000e0520459444420900c202d030500800300011844031340e56102403004481000748240d1541d10f242c0401c030051300514858136810f050400c1d03400180d035000c1d03110100004500c075050004005160000c82644804201e8543c01100f04036001072000b465016086503004144440a01c010070307428480050072140c0d00c51855207940380c1b410180000d41030782200650b202e030012040c4010310200b041040d00322010744d111003c00e1480b0700340b007503140d1100344030b69007450814081104c15410540001e00514210440f0b002020008001000880e0089079408103035a00213800014400b04510803407000c0c11602c0e418101c103030b185a0f5909a03100c069 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193818785 1250 193817535 193817539
    0x5010c080f01050111070306150906080f0309100311030717070207060e040216060e030a170c12090c030f0319050f03060118080f0109020f09070804031b06020f0a020d09080c 76
    0xc5174030081315080c1486400d018651000d001c0c040c001d40d0503c62000e000035170141c0040345103840350001e205800019080c440c070008102a42c1464004400c0282e80d8801c08840c0c820300d51a003c2c410f4201900b5401035116150b0742c0c840e5881c0042000d0340e40002d507030040c494400d40d4402a420300105410502c40303096010100c2e0090b07943c0c40b004003480354040d9040c1e002043d0506004998502810100181030044000e40e0755070740301400040c080110300c1017501c5104e0008810088400326620b450a201e038807180c504225117185c107200c40840e1600340e51581810341a040491a075181c00002c0340030348107521462070440e08100b607006105c0102d2201500340e5050065908850000c0d085110514008010700815a9101f01d10891a02d01815485a0403481104240010f034998506140c0c00382c0580315a40e41e000583c0d956540035683c00e03d03001c1c1c44a070450342410030f440001d0070600040c07250981c0122039036141c103500c80d80a890541c000d041503080c01803001080c45940e00000b042c45540b102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193820035 1250 193818785 193818797
    0xc06020a1202030a020901020609070b03010902130b13050405160206160c050a0303050a05071d010c060b0d05070302090a092415080607090807080c04051909030c05010c080f010501 79
    0x1400300151609030010396200909800402000300c02c9101d54090101c4900070703000d840d6103540d16140f072a12250903004620592400340014851405c01d90301600480040d100740c4107200f91504220026904020a0704601c5202101c0601c6582054000c464228601090040341c00f68203003c065211070008140c2d10002c0300f2110506c01c2c2a100b14400000e1542103c10b4a6003280e940c14014003504007243e00c2da45d940e0a101c04111304034802c050403005000f2848a80031110b032008011640e01c0e5144005885440c2c42d4a00900107503920707183d41800510680060280c5071071441400900d070350003000c540d0580d00d40221180810994400b1032020941c1d108181046000319400000401c2020340000703c0c1c1a81040200d0b183d68000760b42400303100180c5840c0c4145584500c070b0340d603603000c1d402140c407540c00002820040703083c0b0780c006641040b0020302458000310240004000c4a04c0d4560507400107214010700014070800b880b0380005510603250201d050320340401c2c04490601c040c8107042c10004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 193821285 1250 193820035 193820047
    0x6020c0402210f0403021209060a0320160c080105061c030212030106030605091503030d021b06040b040201110a0209070806010302130e0610020102040312030e07090e030d061202010c0602 82
    0xd0056002003820403160342003c0c14600c840040c0110b007203800318054401d010f120004103d001d410f541038620700424484c0340110f072450440c09068003d200d52026400f02c04460b800e410550064034096a01c10700c980350358400c2d41002450500154000d40445c1d24120900ca0a600c401e251041c885002c2064030b070000070103150803860503800ccd013208422683c010001003445949030300030b03600720f40007221428a5038039464a008810350450026640c03692003046050035001c01d64000e000b48500e16240d449480e1030300720040f4284242100e00311a08010b0307108020440d82c01040d522450f8078108001c10710034805d03901050300c050015081c0d00c01d000c15940092400c0e80f20f1b804840341007056400345581103540304480340c841c01054030b400d4800c4c5c0024500e081030324814420f4608881c1c11140740c1140317000624044e8000d00d0860000350f0a03008080020414003500d000d41000136050a0086036903407400c40b03000d401c5640d5a00f1044824809841510141c2e83c00007841c1021900800010b80d112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 193822535 1250 193821285 193821307
    0xe07062316060e01090b0705030708070807050408030408010c0f080f070c0609020607030315052e03090b090303060a0b040308030f0c0c010612050114010b03041502041a030a06060906020c0402 84
    0x8214608020009410003603851101c44040d0045c450b0039110701108844d42d02c440b0705c00e0300c2034002140e191001515550000e00d2041c07081c810036400070060306140c0e203800e031603c9415003558000d410500d40c980d12020351038000b40d0300200e903405504c1145048640340c1441e10448204000c042c18040401c054502a0000c1c40340a43c005070b03000da030042c210f0743c2d14500b901e030240c041c0c828400180c000c00030000002441c1d04014031000100c0600c7c01103411890140f400d0914048040b100010401d03a4451011001071200d100b518083d0350428010740c1c0b070345007170010841580e0640c4c2140d4800f1109003c1040005d0401d400e80703820009002c001c0f1016602e0b000c4c1d5000600034020120b44035802c000e0000303060902d944081c2e82c8140070b07000900140f0b0035080d00c685441420301c40d216003800100001000f1800440d440030740141840c0000d841c041d40e07903a80d000f0944101c14106241480002800903032111407003007000400d0785042140c5081d14084c0080e40711100000201d0080307800040c502a00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 193823785 1250 193822535 193822567
    0x102120705101a0306010509190504050a0b01030c140402040e04030c0321090203190c2610020a11060c09010e031c03020306030f0f12210108010e070623 67
    0x1c42d0140400c002080e00185410280b03041c0201080c000e0040e0000442c10f0b0a08116291142013444a80d800541d40c40034190024840104162400d0141031981400100074400c928020360040280704000d070706140c2120324111749110400c3c8a5032041004011019034807030040c4d4066010306151880003180c0c10240ea148844100300120124a04141c00b6039031401d170f03c443c0c9001d00940859503001070505043c00d6011401d100a4544012110100900c40350503a071015440005106001504035920381d0503e031406024141e03011940120300f900201d0340c400c070b100d011500490b00601031400e02802400340361091206541c10020711004080080c1c40802a004583c591a890501c1e504100d8070300400a42041d540340d8443e00800410040f000000140c001c0107000010240c454803179240c4003980c2c1a0300c2000b078800b00703501d20300084810a045019480c02407a0610000c9800b03045003c0310b070708002d42c50300124184541840a00340c100f6059030010078140e2101c0d0384694400d0044842404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 193825035 1250 193823785 193823803
    0x61207120311030c0a20090103020a090903201c050a0f0e04020c0f030306120703170304020d050f1005100b0409020a034508270a0b0301081005060102120705 69
    0xd129401441d010003018484c81d03c08441c0d04607500d01c42c0e06c180420041403007000c0c403010394440e070552401e111144a9234044000c55100b0304158010300504117000d04800086000070105820100c40c8029460105e10903000319041c1c7d280541c80d0204040c0060404c00e10a421401000005510000281c07075a504542d00c0e1034100b0102d13807000650580d0295298400c5a1482c0075408510902c0703038820001802c4401d9a6100d100401e1200300010266007039000104103a81c04036401400001140c8244000035140743c004020b4220070502940c64030980710040c0515100c403000c01ca04101c1e4954040a42d026100c0814000d03a43d0300461000318054000188005896904440c0b40c2c40902d14441e900000c06501c0c402d0001c808048040c1207241445c820805801510108240c0b00f0b030860140b4407280076402c09901c4428201c020300442d070200301a42080451000010052000c8842003207001950706645405000e14580400002d44510300460210204440840c0d509d04008d01030014007131b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 193826285 1250 193825035 193825057
    0x1a130b062115010c020102061303050409090305091f090b031e0c0309100501050f010c150204060225050f060d0609020a120c0903020109120f0f0b06120712031103 71
    0x200801ea500001a001002d5550039001440c421002d2103d50085003000c44080c0c05801401141d540d4401091000070712007411800c10504100106144640313106101d03186029030f0b03525072108002e030700307100c580610a00f09010340101880c00802c0301c0e0788400300505450581417225103940340c420980b1b241000c88080c26039006c122108000300f01c6400000b56126511100403900c5141030103803820120781080c00b6043d0403164002c5c6402c0c065000d0700010a0003842860220b0a05600c038408000304c0e04560044801a000790612160250100f1850942686011a91640700345080000342030b031810395019a0060031301241c000c44110a070b17800103005242042003591b0f1141c1c0148024a0381c1010300a014810340303031141c1c03002003d2040050000b03880d0b0603150041c070582040c0058841d0744109104454402c0c4601c0c02400190500e0200d008061064105000c0da003041c20800c01a04890540d4949683c00075608220460300e0b2001003210175090304004103004680a1001d003113101c0d11022030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 193827535 1250 193826285 193826317
    0x62d0112020403060506090112151116050d030b0a05031902010203121306050a14041b030c0308070203010c17160e0d03120b0111030909100302120a05011a130b06 71
    0x100b408510740051b03204030300c1140c0301c1ea10f030380c1c82d000c08031a09580d0050281560303a00180e0441503401581c8007640500000c1485810540d1032032044540c00654002215142c02100d6000c44064050060310500a401c40d5035001c041d040c64042170f40c50303400041c040c2e0450440e880320030640e4000c1c4100e0320f102070031140d000d0951400c040c1081d400800e241c401c9407010b14003000116151102d10665618643c0701d241000c003a00c46403161840d021020320020b000c001c2c1c3c2100040003c0030544000000c512684003251a141c0d0340c01010700315440d0800030402d1288030000307801c0040118085a500a0450f81c1d0411800d400d036008460889100c420181c0000c06400401d040c10b4225500c0301c612905482c041c401603c43e07c00441d42c84811140c8090b0580c418400c608440c504804250f601c12000d01039880d00c0d540c2d80d000940c5504000b0364030740141c0c000c110350f201030080c207028840c10030400c8541d810702c44c0004008500b201004166906245030340f49003c03204c590714142214100e100c50340c904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 193828785 1250 193827535 193827539
    0x311030c040806060d030c02100504270608070e010306020d090c0b030405060105030d09090504141e060601020102030402061b100c050a020618070b160c030f0b062d01120204 76
    0x2101558840e029042c07081c800d080014500340b400074603001100360305664514601859a09000094403800545414094140804903e41e00e0200f02602091001c0d9080b07031014040b0080321b002c40e01d0640240403103400c6074406101c1c000c032a001c20390449520110042e9907410b0920110014509004010010710000380c002070220410b00242d40190f0181056680503647d60041640d0f0b10558540440030a030303259410803980480f0b5000c0d590081c00381d101c89c1d8011803005a49403e00050851248408004403800f816854042101c10303800f40082c0000c40c91070505400140507401107100503010300c400744650b4001600240b00c445446041c20718148004c600c0440c02030706c150810560800180300d0b1030000b603101640014428404200200540400c0f4185442d07801c01e90b00c840c0c2003003500091961242c0c0011101c850010041d40140b041c0c0380414418a04404045400b4000d0f0b0710500e5508101400c490300c900d200399031030412a01c0c14084404c5030f001070b14407501c40c004903580c0302e10100340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 193830035 1250 193828785 193828801
    0x901140a0204030201180e0a0e0118141c05030a0c0215040305031906030b0a020304051204090510091505060d0f05041101020c060a021510031506050411040311040c031103 75
    0x150043d02d00c00d072510548a82d40c0680c490703003c0100d01c25010614901c501044000d11075074001c0c1c1050300f40740c0010440303026038881a029500c7c0014112104004081d04140411042c0100401440c15400615040583d0140207100d4000601030080c0b4658070001e00407514000c12130465401520305400f0000d20341070401901d281c01c00c50341701310749100051400b4048505446848142c3e075010000c072210b5103604030000e0094000a208541520452011803028202c04001d803004042c4e80101082625004400004a0641d035201c00e44d09030030301c900d240c4614a00c08a4100382c4006403030458a4000c0f0040050240c801c015112540d1071512051000b44030001c0d0b103480076170000b81c00b12030480700d41f0070500400340320364404940140c000a88808214440704050b640169650100101150712500c4041040381c0182030000b0659440e003040000d401c0502030b09600890041d4241c0c1041e01d103449501100001048036441a0350340c06000c03030114007075030149411900403160f00da101e243c8400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 193831285 1250 193830035 193830037
    0x80c030a1d06160c02130902060405090f090c01080c16031b03030204030c080a0c12060f050a050a2703030f06170a1a010f0509040201210603110603040b06090901140a02 74
    0x40c0200040010760b00f0345011601412a041459070b0141008078010b03100903805c00102101601241d01a09c100400100d0380c1d00c0c1c0350228092284008600c4003030034002501d500c2e18030856041810302c00c42070208540784450b0402d81c0c1c45200c0c012445200c28481d0700c2d080702c17410b241402510540c4102c9450000b40b6074140d020b0400d803440b40d000401c00d50740328941c82d47d548020080c0102087c103003000c203200c01d562070300a5106084c4500b601080d0712440303000400a840e401c89a503121140d0b948100f0600400901030f0220340e21462515030341c046c00040c00b8964598440710044c0a25440300700b0644841415030004006202403a400590824035015150312100c0054060701e081c12080303400c0c224044580e05290484905801010b0390364605400c1c00303003c550051090741805040b0340e400d00c90042500b5801c2c1e0100c40c0b0320000075942c3c00c5140090141d00240111400b0344400c1c805c1000107800043c0d841e13084002101d400509507100500c050161440400071281d00707003030340280210b010301a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 193832535 1250 193831285 193831291
    0x2180a0b09041521030c08070b19060b0306010c021206040f140105100312050d0f050711030c030a08100305010c0e040c05190f110601180c0906080c030a1d06 69
    0x30380510107122900d00202811055000c4c2060002852a08521401c011104d00016034800d0030003030f071224926207c0c0f04031908000010350300d04048400704100384502c50040044555150170401040d410100103038041d00005050741d0500885c150788400b50340d1030340300d1800c40d0242181110f05c0c03440e05281c441100304070520111500d4000d4002404038003818001e1074451607403141d1101c03041d40f80d03880300c001102c0c02c01802404e01004200810380100706000341d84a554201c1d0f4085601d0401140c0200100c411301c0381020341390818809203128045c080111850043d05182c04101e81e10752603401f030701000700703507000501e03030343ca03203059914004d0f045600508000300440b010403040505080a940c03074800c40c114842c801d644120b51508071070040b2a141003181c0540b030015200144004038924024003a040311100128407910700d45074482034040d240b0044054600600080d1402c180a0300041f0060044070b00c00d00c0c088002254041182d1103001c3c03204c07640001d49000d0342410074081e120030050f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 193833785 1250 193832535 193832539
    0xb0f120a02042f0706060e070e030d05160b09010e030703020105070f0905030d140405041d06010504020405090103080c0a080301090b0901090e03040b1e0c0303100e04030e0402180a0b09 81
    0x1c040f01040f0300c10004411000401c01c104240d10070030404004010703551000e20700710350659488a012030a86204884548281001c1d1075500111388440c080502d0802000300600070000200101000c140c2030500504400d544005141103035240c1c4100c1501400700d50320103554078480031510106045d41504410b0040c082a214078068200c3c09030115042041802210303090741c00000100000741c03180700b148081d520b803202024100340d2140002002c0d50710300c04480c41848482d505084850a05010240c0185012035003146441e19000c08506854414032019118110104d50004407000501103012103aa0140c00a0b0366036031a903816200401c0341002c07950068040400100f100302c0103220313400c1050302d00c000075410180382c558907074080d071700c1501e070303c5511600040016840071b40a009030035565619000303135482c5e10703100a43d010001e0340d6500084001d5012010700c400700e0b4000c46800b010650a840250b81c13801e004401c400c1c2441c03280525904070044030000100304a0500203130002441c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 193835035 1250 193833785 193833791
    0x7051f0f050c0703050703020106031b080609030a0903081303020402030f090c10020c040b13021207021209100e04020c060103030203042c01050906031c0f03060608070903060b0f120a0204 82
    0x14002055040320030880705840d03240b00c20816203010030700030009802c2d0356110b44000f103083e40e22640c03801c8680e91542d90401c14541241c10a00c000c44003070224130f034802c44210040d410000459001480000988006020000d0000d128141c2c4203214015102858014106560b80d04207412244d654503000c8640510314051114076041600e80448440030401040e0700130300708900761000f040014025082000d5001d22512020342c0071007000e0000e40000d042c0308019a010740f424550290510b01101d080007240703442002289015504c2e2220664255114170301b075001d114441d00402c000f803045203c0d9030640d20614000108050f4000010402d9544e01410000f4100c11381c07900520b04900f0b40c18a9160b5040c66005000c10304001c0c100c40c1e400744005084440c858080d0300740000c1c0e052805102030000d82640d0f821400c0c5901401003000500c03a0341780c40c9101d0b2903c200010300d290303c0c500009100a403a4103c10b04540da407074103030490807040106016501d00d4010961a41c80509480480c01503003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 193836285 1250 193835035 193835051
    0x2100608150a0207030801140a0302041107030e010206040b070305101706040309050d0f140109020d0f03090e0c1602040b040f0920060a080a020412050a0b0a0b030d031107051f 77
    0x240d10f000b500c81580d45616405802d9007040740c0c1d01441001a03034045c0d00800403c4000025075643e0103034280c1d109151800542d180403d06000709800707000c4c2e00190555001805000000748a0070106038841e010f0300e8005142d40351f0300d03418441030029034421405a041c0c244440a107903004101d0034040c40c42174507002e003051f0b81d4205010a50440320000741c0b00d800105d0404012a407030301c90000c101102c5100008580b9001e43c0002d810300003200080c0c0b82614654250010950005c20840242050002c889124034289014401034803070550103e059440b0f80d42c500b8115200c641002103448002481805501e1110182c14000c2506107029a075141c4001020700c0b8040e2000d40c507e0503110090400b610f003940401c0d065900f00c40240c850305819034204000a8804907c6100f280f8941c40740028080c440043d0800d400302c090050700000100d840c103240d81380c03d0707500010050540003441c00c0210b00d420b070100071040d02d8010b04401800790300850302452045c003070404000142004232102001000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 193837535 1250 193836285 193836301
    0x1208040309121554050312090c1c260901020705241303050109110f0301150501140408060a0227011202031906032405060a060f0210060815 61
    0x75440e0010303800c20b04109001400964003903540c0f0400b005030484408040a003001c11181400107054245d40a40000c0f8000b940102e0051055401c41b400100411080c860710b400181420850a140b5242c040c1160a20040010071108a80c0050464008010b0104009050042c9601501801c0d00601499201050901c1c3c000c03015064165000d404500c040f00510804085500c0650490961400d81c000040044d10034015504540c3c400c100624110782540140021074903880283c0d846641010355466000c207282603484d00712802441c142940000c601460481c0384280d800030b4085000342c0d400c002c6503042a400030700b2004d00800e009940480b40349076410502c0d250072465800104012079000c1d81c40303110b402842d000304103010400480c6445840e0901280d01c142d100b1598140c40d00c884840b0301110041714890b035006a071050141c1e1800707500103541007050340519030911441807503a0540314400c0100d800c090640f10401c1103400e86800f0303840d07503c29000d2800d20843c2240340000e807501e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 193838785 1250 193837535 193837571
    0x12040317070207061716110708010f09060b240901050708030f15030313050105090f03010f05010303140a1b0303021204030c0c06110c1012021602090c0712080403091215 74
    0x3e01200e5007480421b1010200484611310301b1f4203109914404d20f80e020450240a1051a035920490000000c40c0426460080190788062000d035120380c000da124101003407064040c0d20980444414410b0b9a4008500161224020140041d115103008001c124030700c4c000b0300d0b800d030160040c4001c034007030341107040300f015524840c1000070a0140f071000c1307040200c1c0d405000a400e90180050603041c442030070b5000302c0e00b180c41000c0d900000d20b844000410515801c0700c428500000011103152501c0d00000020746400a555205d18000440f002400141440307541a9698111b1180d03800202d42041d04008040c43d000c28020744200c491143c001850034092086014032810200c042c00c4140004410080200c0380b0741d12601c1448080b04160303810304190b2001780129035074409000342030ba00c64014445440310090802d11603240400070900800c080200000341003020b4a400c0030b181d6150710b41158850020741c0101c03540c460100c0860104482455080704003e49030030f0400c54151311046000c66 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 193840035 1250 193838785 193838791
    0x1050a020310060f0e040c0807082208072604140406030c0501120917070606051507020913020a090c030b0a0302090c130b0f0403030206100308120403170702070617 72
    0x90400b0a4100f003094024845902d145040d820001140262440800c00341c40090010000240003202040740d0560441d80d43e86d0440c00003441460300b009030360b900c07450401036440060300401011501504000c01c848030040c50006a0004040349000004005840d030030034002c1030560381e115100e901032801d044c80340b9400c580e000719200c240c152130540191f99801318448140e1620342c0328860b240c0422941e000f0a801c2c00401740300c03680d451949003064012104250040c0d4821403034441c00c045c3c4402003000380c03105240c049840d00c2442d11504240f0901c2485036500a402003104800081d8502050b40640241403640d01c0510800d1100380401089500b1400000d5210381c03c000410045d20440c800f0385000c1d006001c00504c240d0301d0707800400c0036030480c0c4c0f03072003200f400001828030805a040c000590000d80030011201c800341503035903005150180c007004492645a65000030107051181f031501100b00300600c5580e02a08003a140207440e0800da008403008201c050288811554603044420700c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 193841285 1250 193840035 193840051
    0x21c0f050609013809101107090e1b030703050708010501090b030d140c0102090405040c05030d020d0503010501050d090605100509130302191a010b0409050105010c12030506061c0e01050a0203 84
    0x40030042844201300e4030804c449841c94020140100042e0340c403009007420b11043c0580368524007030503c1c00d2003854038002d07401c01d000b000c2c1040f2070310740f001c0d4001521160506100001c071450200e01c1020074a8040154009002e61050310000540c3c0d000660105050314540c4600b441040098800d05daa10440c0d003035158001220008441c010707500c05000350880031070b004009807030250060005011f4a1060f68143d9000403020303002c0059140c2044411000b9101d40040c20034241d007608050a140814072680e41071100018141900c40302981c0000f08959000c4410815420031b00940415040ca80c011a40a40d908a0104800d0030700708189910306503060707008140c18044071068051a050700582240c00030111070301c503010003200e144030310f010b00291a0525140d5292020318015600d040e4040381c1484025201780001c2551000c64101004c02d505001c039568031802c020039594810001064154406d8a5001541a41c00d070088808420000001c1c000d60312802c560004912003030761084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 193842535 1250 193841285 193841339
    0x30a0c0509010e1009050d030306090e0f070b090402040f170705300309030a15060905130209040302070e0c04080c061809040c08011401090c0e0310021c0f05060901 72
    0x81032450030b44100704e140602890300b01e4100d03955038042001441c48000840200352100c1091004a01134480c20600005140080c00040140c200c0396450307605902540511140005600e0019102c03501110000e100d120700d83c40c500d40d511205d4001c000b411b50844507450054020006240c644282c20301c13840d45100140115201084074010601e580703030301d2000320038001030041c00903d913000d205082c003440c020f5540030071041c491056141140c03d60341010348414034120501c00602d020b101c5814981da070590300b44030f0035252400c06a00d461100d520625244103144d00b042680c1c816200904120b84078102142c946800040400140740208008610000c00c200100940340c9450510960442e0042844018081e20b640c3e400c0d0944411036503050034240e00c08010040008644285100c0c002c642c50305038290a002c60000ea1642c41c03208184c40d1040c3c0209103100c0140300711031801c0320401d607140b081161b180540440c0000e08403c94605104031140300000451440d01032200144c1c000b007074524 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 193843785 1250 193842535 193842557
    0xc040c020c1207050406060207050118060503041101030b0d120f231b030d090c0905040b0612073201020604030c02010309030327020a0617010312020a0215030a0c050901 74
    0x3000b5150600120040284260100000e50303480c0c0e8420070f0054842d60b4041d000c2c46042500140c13011500641c4c2d009103015812040112035440026a07401035844111440000307911700c0100d01504820304030907401105020407400700120160108594279468031000d00c01c003070340c00064641011405283c4104840e15190100c0040ca41b001442c0c071800410080003607200044503103103150824060300601c00d658065074030900c40201942030041052480911082c03809a0f00c20081c0707403000d01402c1c015030640180b2070600070103100078400b401030f501c04030b000d0600c62454114500d4002c0c88503c141446d07101400306d9940b01040c814840c03509521624500c1c402c80e0300442c020324800313005404050382e03940680c280e00f02c00c2d04044c00ea00e262101c18882648035004000841d02658041d0060000400008544583c24450141105c0c0c00c80e0b00c0021a5041c11800c0c1d0426000d0580290301403a410050f0f003014000101550244003001001c0101c1029a01c0035a03007071046c511120b0203c1d4082a40b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 193845035 1250 193843785 193843789
    0x61a150a11060a0902010306052d030f01090f020f01020d050a080c040e0408070b100609090902030307080f1215060d0f06080f01140a0b09041e020a03060501080c040c020c 75
    0x410384110340d85070104114035a007002504004069804418a5031a0841e403070a640e07140c0a40809000300315442d0f41034200c80d00c0001c524103018220040500703588001c0200f20341e800d00401170f00350b214000034000e0043c1e52802601003c40d00c28206c1c4145000303140ea4541c2e5100142c0c0700c61404c8a40c80b2203141c050000b50a5407041030007008004030503001c00c00890320746540c9003481d000c0d52040703094030784550b00d514081041c1c4100410031000812400c400300316841d0b12000e00c0c0c04442101d040010079451078004203046124100c0054865400000c8100e545c1c50702034000d203881c1c941c50507812640c1d240d581001d5890140c2c0308007554041c800f0700c100c1d2003000b0154802d108540b00c1c10400100642c0e03c501c0c1c2e40c00c0c1040c003840c40c1c400c1e940d142c4000d40108000741c00c1940c07048076004108012b208072000607410300400343c400b8018803c620050f209003032107502240e58060700180700040d600da4914151000d40824004d1040030300440040c4155400c0901540d00300c101d407900940803030001c90003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 193846285 1250 193845035 193845037
    0x515010f050d0b03010c08010611061021081815030f0403050d0e0604060606090b031003060905150906010501140c060a18060906060501030b0111070509070e06030f04061a15 76
    0x16142c0410380d5075001400c496074092046610b00e00890700c85801c55894000041d0254802c0c110b440e20b681c100e00200441c4502103030b50b15060310800c1a801c0d00031301c00c4180314643c030100360780d0062080b8000075461b02d02060380105004c0c2c0000c1151403000a030503070844200240800c0c2d90980c00289140c01103030009008070080c0c0100b409840700040c036400303c020310310300d0302c4001c0d20244c0384980d80b00da06101290b440910340b000b07804d2070207013146903040484003941c1d06605884050080c80d56807001c4c1c070070042d00b03110280c10100900c0c981281400c0c158002600c64038207110703041c0414032454254241403000c4003522810361050001d0603041d511007a810001c0e0503041b88945c00c0e04030704017100c07000a140d840303684810780c05041c0010f0500d003008005012a21b0310310745581842407104150244240002e0060243c42003621100e0854440c98020341b2042c0000440550190300441041100b051038503d0310312482c094001031000003036211603c5401c044040c01650007140c61070aa804090a001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 193847535 1250 193846285 193846297
    0x4031b21030807300b190501020a06020a18080c100c08031f0503151807030503250f060902101412090309040501080f060c031e1503100f0515010f05 65
    0x10301c0003010104e65480c4095031504103401d0307001c15136401e00e2080703505201d82c0b074000e0100e028208038029030070100082c0d41c401e00140020902900041d03030700780d801d110f40c1811800d4081295007070000c54884001c90389805441d5040c0e4000e8016803a110a003a00c180941036002d5006000740f0f155031941c0d030210000d002e04295403842e08514000010700360b28100a00095600001e103031058500b05003184801441c0302c4500480244d020213000d101007030300403003200c0042c0d61840c0d040c4041014801050480d602d6080080d280c545018141002d2003200d4002740c980600c2111081c46146201c20700361884400b04100c0340ea08541401061148903144001356040034207201142d04014030b9800003015640d09030001c964603003180c96181c001030000c0002907001004141850300b1442d00310810f4040c0f00c004d0702125207030502c100c0844e1120705001c8030059100000f40940d210411039241d810060401840130035951440d100004070213841002c040f284c1080142c0d40c2209050304d1031000c582c190094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 193848785 1250 193847535 193847567
    0x708070b0703021002130303111c0e041d0c130912030204030b16140903030d0e03070c090c1d06090306010305030c0c01050403020f24070501090b06010e0f06030c04031b21030807 78
    0x483c0b2b0003900c4041110200d00607030540e5031200048a0070200340020750b5804200049050341d2403111445665003c078150071130b210203580c3c14992a0305002001c002c3c2080c1c02c0081c0c04a030190300f00080180e456001841a2405900f039000e00c1d8031210f800040802c010340c2030314006040b8520100e46c0f400f0601c0100b2562500408a81c10804504041ca04580e0318016140c6075520014181d070801c0043c145403401440011400c102c51104101c0c094509289404c151180034002c414081c036a50b04d90081d1085440702078200ca00b6076840740307403e940d254011100e009051003a120340e025103610803000c44090340d9024040100c50b01780304080c0991201e042d6841d000715200000c54040146803200500042402080089850161801d0580310042c02030501410821415541d1500c3c0d101c00a028003142d4003560318a81d6513490090900301400744c1c8d08014a4003041c43d421101034011561514150303007811100111000e2051140b00481d914018020040340c00f200018900301d0003022110400303c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 193850035 1250 193848785 193848793
    0x80c03070201020d05100302100f0504031101111c080615250f20040204030b150310150503060136140a05041a0601020712050708070b070302100213030311 68
    0x1d030149400352081250044408031003111b08009602d4056141c01c032001843c14115802c400000c80141a0b04c5140005800000e00b5008003001d640328594900410f000c2505903003a4101c00c0b400a64100445c2d481680000c003510046001450001500c441003452010803030328184101102402100703281400c000c8598000301120701240314495248540c510071010000705150b400d1503400040385e0307082032071700a501c1070105100088901a5090700858401d401400e55040700001a1400c9040f0013116111810200c032810051804240902501c10440a503031060303803214110b00364501c02d00401036902081c951281101c80054100c000d40301c0d800d08000c94100108010509031400903190784001a54460411080c801803c80c4144042d0b1000da4259440c1032450000396a400c01307008481c46440b00403092410400c0030040034005160800a0383c03440b960303403403a44d08a604044003ea0140c020104060030100c2c45108844180c01068010014681507403012a40030700b034101c1c9600d2030b201d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 193851285 1250 193850035 193850047
    0x501110d1b0b010b0c070807050f040203040c03020a08030705010f0b0303070314040902040b0d05071815090314030306090c07032a050115080c010201090503030f1b070807060c020d080c0307020102 86
    0x114016941d406400c45028255840400c0c41200f482e0030895881f44840d5084048180070644d1001d0f05011440302c21240541c4a07246c600342841155580e6200035403242d1100b400042c40a07011014082480c002c42c0200210106030b0802804e6529181c4030f0766043c0c100300502000240940c84a0004070045040d00c0c0c145515103050038100d90142d0440d41305d0350808070384521084400d00581d81d0052592401890048482d06280301d507041c0340c05440358104c0e501d168010181c1c481d2007100700650304080905002c8400c40c0c4426201d0b80300780c13844c5004011010004400d520b1030022140090340c9580d13030300a0f52a9141c00c0ea01d82e12000c4d400b02201540d00c080c5000425424014600d003400f16440c40b0085924004015142c8286154000d055904160030203000c218080305883d40500017082080341540c40c0461025241061107224104400110701c3c0001c2c44540c07070203805c5a03032081004018a07503c17458140d80e21070360032441070009045040010320288000c809550041c2c00c1e400013505040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 193852535 1250 193851285 193851293
    0x1015050708070609120c05070905070203160602040e010b1801030506060706090515090a08190504081c140f0a030e1903050712080108030307030b1302160c0501110d1b 73
    0x3500c030100a032100740d01c0700c1004d01400440030b07000750001d0050900c03005850a9948541d10707491580b143c00111aa035800240740180203000701c44080c0809034440e004145a89001d0000703400c82c4c0201d19040039088000b09140e41520111400b0010304091000c0070701004c0c0c0110050320b0001d00d0b9640168091020700006080303800740c0340b07507a48204064011604140790140700160000c0c0310f458a588120400e41c013107420107003110040c01c2c0380340401061401c890b6056400c3c0c031466210680d544109407004d020023050707030114610075005540d00c151042039440c00c41c007a0f0007040112511508100300491580d800f9070700c0640054400000da07160b2000349013402103198440c100c19004502c000a00340d04004070520100031011007414044050b50600e07120f03607681c0c0001000c1009059940a00d4945a5600e80001c4080f940c009410340d078810088045600954504104a80c030500488010800d0b40c042d08400940c00d0840f8001d05210411403800c4580190705011001c002191a1522002c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 193853785 1250 193852535 193852537
    0xf06061c11041b020d031b030e070e090601091107110d020d0c06030c0e030304030f030c21030c030b01080103080d09020a031e14070b0a030e0115090c0e091015050708 73
    0x1040600820003900c0141c40c0f010781070992581c4444105481c010010301c0da9650182c010034000020b240014140e9100c0d556245003d60540200d10581e0540040100900b40080c0090580d450002c0600c076007500229600c5441c01414402401c070070400d4008d0500c1e01b05140300c030440c1b0380002c2803145501031944510f40d200d5556000700b030001c3c0e111813010810940190620b00b81e042c06078011841c19281d901e425459480c2c058005080100319049102030181000e0000d01109450803144421560004068020703d000708204000c00d050201c10010b6600032140e840c102c0343c0000748145411480708a500040c030203080308983c8200c942d0b0001c40802c050703401e04c5006041d10400f0b401100c4030b504041810f4000740c442074aa07175100c0c607001c0c03051a400702d06917048140c1608011428030b505000b1030313002d4048400818140b014507030000440c004280c004208205884d150004c0081d090001d1002c505000c44a003402c002d88000b0402c5010181d20905a4038062841c145040400c9a510003891b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 193855035 1250 193853785 193853801
    0x2e1a07120e1e131e05010f1d0f01051003060801060b04030b060907090302040c1205040b06130b0607020d020a08031b1204080a020f0a0812030103050f06061c1104 71
    0x902000311a403007a08011460014900741e40b59070300000300344440040e0b18400b494000120440d100c020342040d1610b1000ba100c880c04c8001d40a20440d0703102e508802d8030805d070707118200304224100ca8620ba20034460f07030707403034001c05101d070004503168200028000c10700d96038060081010350720040001c040c2000e00c900000382c509a0403059440c0d2079818206122031020307240300c1c40b5400803400d01c5042a0000b101d001160342c10754000c203800601400503240700b40c9027144c0c8107101c2e0a1104200410024014032740c440c110440e40d14281050403241c04007107415402409030050b60420035000546024400c0728012440280020b1405403a11612801c64100c0026080e61090781030200642420030700c034001c0180c815840850420f85451040d03603440c40d40c9000640240c801902c0d204182d1500d0044201074500c003c100d8039400802407181070554424803090750b0307600610b501003280d45004111240107040060001c001e080306502c180d075811600341d00031101c20b0812400c80b5441c1e144c50084e511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 193856285 1250 193855035 193855037
    0x281b0c0f08060108010b060a09060f050904090323042102130c050705070501020a030f031a1c14010c08040b0901020c0a06021c060e011205242e1a0712 66
    0xca50b51520010509580c0700c003102c184540070522400b23032440d6004e4080c0301140d500340740210300b0426410301518107220724003000f60040d0410032400141900f0110300d444400d00341071138071501001200b04584034000c07402210200184003401407802490800c20000c0030380000e0090080e812000d0610301200d440e03d19440100b6000320342042440b0040c440a40100802c0c000307413920b214070b56001046140c2501c6240c081c1581da1403090200c13045a003c403004041c000c1e00264298903c5a0480c0c0c20040d4039004442c6594107440842d0f03003240c10f016150881b6229140d0301d861380c444c0d548280301103400800e0152150348c280071080c3c0819040000b2003107603000c0c1d4001a55000c010b070400440403d050800c2c00308504102040005030400805181150036a8240403015074051520b242004040310390060203400a00c01c00113220700c0400311501965441c007030703404a818103418008500079a44040d1610602c407520402c43d424290408400494150b602c1600c0d01d1202da8415400c80031400c03e2034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 193857535 1250 193856285 193856293
    0xf0204060c05070603110910020a020a180b03030c06040605130605010b0909150108070513080102030a02030919050c010c02011b200f0d060c05040e010b281b0c0f08 72
    0x4000c2c07250920080c0c0250440d441c1c2880301145040120905210b61214a40508400c8a100700610300c02e00a00f890654010702039a06150303648a115407017a00080c0c0e034101c8500c3c0040c800010300d000000c42d02c004090300080c102590350f50b1150741c0180700080c1580240241c00c290000080c40500c1500d000c1c02c00000303402d8440004005004100000803c03200300b040080003401c40d10307a0040e24072584258103150031565a0041d000c0c10011240a0788900f12540c004418001d04202e190091803280c4900411146040702402040c04403c3c1c80020140c600d0300b1450395803000303500c41e0070f1440030580181400800108000c0c061464041d1003902950008440c3c2000c81d21003c0c0100c2900d6183c008030340ca4655202c001b000169440c002c8000100344681d0b440000303400c0703400750003074400500305402002003543c1d690a0010003544030b504010508a80700c032080c02e40201c40e185a03a40e2890a0380c0c2c9100f61100050b40c403900c400184010786e06407a18000c0055508034440842005d070200f45d001d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 193858785 1250 193857535 193857557
    0x15030c060203030a05060a080619110a09080d03060302010f0e060403150507020f060c0f0d0f06030804030b010b03040b010308070f020306150a24050d0e0d0c02100e0609130f020406 79
    0x101215801b80c0446d10a5013190740401041900081c0c042e0403c19a038815850f1882d00c40e000344c0180310303080130b4012a0401082200b442d035040340c041c20445800b20207662402c0301c042011011514180402800320341c4003a07082c0b1116204043e182041e82014006500d0507407a030b180e042d0307918511840780220729190006c11500d6681486070003a0541803a0081c0120f06156151a0050140e20510030800b4004135410b034161181e50001c082c0d54450060422005840b800c1c50f00882e800343c001550300289071400020080e00c00000c8911403504040e4000c2075034215036418802d94000d4506480c038032600390f60500966014400c0501886141d80c0c95601141380c06c092102c00c105a601441c02c82d10f090110707881201008170078a01c4101c444c0b0340b00d135940c5d40c885e511000402560316244914400c0800446034550028000b568440c001c0318404410f0a840a045034694403445885801040c02d10142d0001d041c0003218282a614071140411000c2c0034503030300d20498025610640000b5111081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 193860035 1250 193858785 193858801
    0x5090a09090201230f090117040b1602030a0c03030b130c120c0c08160519120e030a0c05120111030a0204050a0803070f0b18160e010807081015030c06020303 69
    0x5003444044180034024013000b200740c0503420038002c083d2444003c0e04002011139040c3c0c801c071020b6181a03010303422581c190038107080044ca00d2804880c880c402503048040e48490500020585d000703c2a540d03240070385c11001e603a00320302801950b18032136005500780745c401400c02c2c04c40c06403c1d10801581c0c2c40a03554400030310041c0a4507510001c40091001ca100c1d00fa011903405c1d000c0710209604007120001d04460b9203001c81c50f01d44075007185280300c800c0d00310680403c44c0e040d4540074040d00c10f64030702407400c01c92420035807101d1400c0343c0104500000c40c8104460b05103142d80b030354110814400000c002600080c450200d900842d1018240b5500103070a1126140882074a0b01500880c001103041044543d11121200080c00020388103001c2100000d814040710a20025180381c1d800076108061021060541c26190350b0140c0301c207000344103001094052001541c0030841d20000002e041c40000c81880000415039601d003070002d640c02c0d00700031011900ca0034070034000301550703801580d40b45030102d6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 193861285 1250 193860035 193860047
    0x1525030905010c12181106090607020a03290115211109031501060815060405040e0d08071107140f040204080d02060106090b190c060e0106030c0f031a0705090a09090201 74
    0xe003007400b059011146034089601b15665480710181514541d541d020844001055801040ea0095010404c0c41c0b0100400504030500040d0f50f040c2440302e610002d000038400d018070402d0040003005000a0420344841d48282040302c8044104506650360340d024220300016a0301c0c0d110b03109a4400001114038450038200440602c507070002410455135410078200900050b000740c4222a10004003030040310503620801128001d00c0000c004120010017000102d44030300300607822a010130201400105018001e800d100b034081d80e200040e141070781c1000800c0c5100744e181004a038128500040c9118203440717030f10080c0040c08201c002004503004a0340c00901d0804140c02c10350800800f20401c02c92464800103a030945500715401c042d000b00b01202c102c50b172110203100501440d0a040100e0496481984400305603802451801500740d1281d240084555982c40010f00e001505252a8681d0144c984c0c107507040341003850460303c0c00f074005001840004507a04021411552110341008541e0440703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 193862535 1250 193861285 193861301
    0x6010e04111e16141c080f0f0603060619030f08040812040302030706051c09080301080708060f040b0402150d0501050a091a0616080309060601021525030905010c12 72
    0x441080c501040005428456500114004c02c541440c20300344903140014402200c2400703200c600b5401346282105c0007007449405440403607001c82d41d0404181d00070800c3c400d5510441d4080c0080103691a0702003406041c00040440882c0091181700c0400014056481c644219020780803180e141c6061440c81420020b104c04103045c1c501d41080f00b0401610085052012924035040494680309e030041614000081d84200804861500d1300c0d0703004001500000e1410f0312140012102e143c1c1c2c68140c083da17070b401c1c00e85032510412038000c006000156800c80a07a402032010702070318802c80f2160002001c0b904a41c00701c2584a842d030005101c5810110031420080051110610060f424480401c06c08561115000d002c0d07400003d45502d44640740220204107544000e110343e40c0d18000340a036403161019100e4078018042c0c14040c0d60b603030101134140c0780205035441222660f89100d923001c520092510820340c042c50b0300d4a0385940403c0c400e100f0010070401e42d440382d68000041140580c111680c80c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 193863785 1250 193862535 193862587
    0x105090606010905010801270f02030702010c08060105210403050702130603020f1f08070203090607212c03010f0203090d0207081c050c0114040302030a030b0a0e04020906010e0411 79
    0x104400144400141c0e00c007003c691703090b00000d06021861000d800302740c101c0b20189000105010050758150f200582075141c179922440c65440d44001150315100b220b404150307000300c894551854400c0c0c41ca20940151113800d01d91301d80f800a5010440b11550b154400340e030300b503894200300107504003040c81c4d0062003011281d504003030107224050080c150007120fa2404100502001400e0a40208121509080b00402c0c2c140c4410607494402251444000003000d108841030555002c18028002c1c2414242801c1d81200342e003491800c3d400c80c400c0108401c6505640345c4504511140151009600a4990b0801741000c05100000a0301d4008117501c10801e903441075692800808a0780741c104034852240c0b134090707600c800400d601409000c0403100100741d4030323044052004040d0000020b1204d40c41c40c5d00c06110032a0130340100b01c40d02d840740c4101c207070a8056100150041c82c10340d4086030702c220141000650316411a000c201220940842c0c1101c0e1140025200c0040d407604c1c410514445074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 193865035 1250 193863785 193863797
    0x1809150e0112121805090115031b051905090604030c080c011106010515041a04050a0f03020102030702010f0513090f0f15170f010c080709061b030806060408010509060601090501 78
    0x21076603035100450050400c0400b0421000c00c0450455a001d1303007503005050007084150301e035071956004501c40248642940129180410a040301d6a8007040d54807824203d407105814210501840707032024414159440400c001042104070360340e540d8000d00050b60194443c2c20540d4141840300d80340a402d80348841c184000345401c0c00480300c0c00a06e841c113446098800070003c04156550465600640c1c0040448032916400200321a0140b0082c100700e50084850400c0d80da550381600740b03010b20038000680142c104011020155002c0e601e00c80500d11030b85015840c10012001079807420b4860f40000c0303100f9843d0000ca10203000c02c0d0040c0004589442c0d0b0400045407160040480d00240b88100c0c841464640b00c1e191410701e05010394888044010000e000341840040c004007024000c4030b02002241c4d40340804110184616000415040104c140583c5030a080d101541c0c4e50000502c4607078025401c0001003282c2c142030140714000c2068400901150500740000740c001069504001c0c10040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 193866285 1250 193865035 193865069
    0x9090604020d02040e01020f160308100b03070f0507021309050d14120402030c1807140a120e03040b0f0403022b0b07022e1505101809150e01 62
    0x258000b280440654115000110000018200c5000e4010f002004103030000100d001d801703040d00140c81d000c0c0c80340321340d8420b0140c0e600d0314421100c01007980a038640c0200107000140085008524040b5038618604009003001c40550013700c1403071031503203401641c07034446003141304014041043d00d03645107450420811000d651803c0482502441c5140c03103c00d00d04a000c0381c01e5413810b002240c00e03960060301c01d14022542c04200038207000d06440380300005290180e4003a1001c84041a40c2c60325242d46e032040310322045103c005003e0001e800042e400d40c00200000079142c4000e80003020982075100c10310307480300e05e10300402009003c01c1103580640000e040c0c2214445c91103102d0340b4411548041b03589000c5c1c465801c200d14081c0e10106083c00214030300729600c40c0c0e80d44201041c0d560350000e0001d1000941d011010f122144c064855950810080000000094090407582c000d0b080903500c0141065680d500030070a6400d1070000c1003080403011011b102c01e011810149014106030700400035518 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 193867535 1250 193866285 193866289
    0x70503010b010f031107080309071502030310030609030e03030309070503010e191217011701050a090314070317070503010f0b03040c0302060d1503060f060e060d0210050d0513020909060402 83
    0x2d01c0c1d102e1403c10950f54603050f400040208003a107400641000d0b0187e1249011000030750342d036803c0e004200c2124020034038004002d10010860307224055450748104a50700d1650340901510030400110b0a1144240404442e9203042024500c0f600d2904020455503141c0014075084a10b107150324440c0b80c11a890b200c007155103170381050030750320342c48448510320310400e0100300c84442054407000d40c1590940000501c0a541c6040005024019802001962102010201101e81c100c00c0200450610410400c810200c90041c10034107000f42884465200c06403240141134004948403c00b00d840400140414a0f100010710b020b44900d10805166003002d4413854641c419a2200034482ca070000b541000054540d04150354421034525125500303030300c03441e0805c080d04030311044000ca54540100002e0f0900c1283c401e0f8010340c409001c6034080d08440d020701000140300285034043c02000c10076202076206a215017440340e0203031018100300d12024030401c1102e81c00036007100c00d00e40c04041440301507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 193868785 1250 193867535 193867547
    0x30203060c0a120c03020307120e0601030b061903051c0503090c130207021201060504181119030c03050307020102010609061503150506072103020304031418061b070503010b01 77
    0x2641d6a0350a444202c11081118080003001191007002c3c2001030261500350950050750149003c1d84034801c040518003440403c8400c81c24504165030f028000400100310302c140b90642190015007131100d0304c0c000000300e9241803915401120350f40d0084100d20030f04205041c2540012034149130003851818440038103507440b00001085442020700c4e0f25800710042c0305504940a4540c00340140e10009030590200d4002c0c00b513441401e0140e800c0a40010244240f58040074402d644915000040c40f1700b481030040c010441400e5800c10501614048049000040c0075001980302d00d00840d42e42e01c4510009094568680c40044160f051400a101c0b041c400c8480c0e010529140c80c0000310f0105030b40003850b5030003681d44055013000002517403005000540d840994102e9044100d14000c45400c10124201e102c1100c0140000303208031580952105408010b0035404180c040703080c0b0000d4190006000d65110007010100c00400a103080f100c00c000303000c0c08006042c00c800030020000328000103051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 193870035 1250 193868785 193868791
    0x20a02091602031603081503010b060406031508011401080111070b040f0f170a020c0306010506041703040b04091406040b010905040c0302130306090507080c0616030c15020d0605090103020306 84
    0x80c0080030407480c8800d600c03c20990310440e0a11007411141c403528103020f400c454090f203500708000400f00718a01903060500641c6503141e00901040c1c94649008011802002e42107640e01d0180c80902d00066800000d02540540d03541c9400450600d5142c0b0000c3ca0848040b014882c40045051091501094040c2c030600e030b2150308074400104001a61820050141000a0007844050308a601c004011403d902401143d85940c00302c8140f69484000c05984003400d1052582c8184200000c5c00f4640d180649805600161000c4170300f42500d40c800310041e03801a03042560708907558000c4034211a501d0f42031a811200c02e45040085810550000707040600ad800344900454a4880480440340b090b411030743c140030000481c90340e981c0c484c5030002c00761041c0d903000e0350030340f06540c4082048400880c1150310040020072042c5484540d503840c1c8400425040b0075014025141e01150104d140000c12043d500c9042c500107948000e01d080c1c040c120b0300a608518002d01c074034001400140c60005500b50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 193871285 1250 193870035 193870051
    0x50a06090806130f0b0702070f080f0606040c09032009130b0402060903161403120f1c0e101b030b031002090415180f02030601120506150705030c0706020a0209 70
    0x40b244060304099402a90b0840002d061405c90401c1204c0780e54041454020390b03401010050311035a9991410f5903903041040c1e0312003c1e4010030041107240c58141d2001078845a24140004601d0b9030303032103106032400554911041201c0c1419019841d02d00b0000705544044881e41e641d03803c09803a1103031440000000c100034050b080c002061145590100002d051040d0000d098035815a1520f604211090800c01c655020f4820b4980d0341d11010300c03c2d0203690009200301000ca0400800c84c0703500150410401c0c8091240360766400920700d000d07051145aa03a10100e19002c00c100840ca500651003041c503001510401d0300d02140c0303400560f0b0100d00c041c001d074111100540c540c07124500040007041e494220341070520308240e001800d40200e0b074040040d08a2030500b000300000c861070f4101070344030445e10f81c6e00013840700c06840002c406a41c01240c11580183c900c0b0100d048600350050181d0000000750b036203a02c0401c031501c012500b0410750024000c0740c400f5003804440c40e40421603105004e0300d1030f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 193872535 1250 193871285 193871311
    0x5040926090301020d0e01050a0b0d030c060204030c080f0d05181908150a050115090506030a15091509090b010b030919080a0f090503061503010b060c07050a06090806 73
    0x2421002008055511101c4000c000319070320100840c01034010420103803402465401d00000a50041c002e1103045600035020b0039a201850665a049941010328101294203550034440030021076100306604c40540840c40040500c030340b07040070301d6207004c04090500e0104401000004a18042e26a84003400681500da605800711220100d00c0d9848054202e400e09200e55100d0a01c3d0303444503583c050141001417404c21403640c031004100c114070054801403010404031350b070402a03030600d03034000d41d40110342c1d902c002444020720502d000c490f41d182e13000711100740d10b4550010002c103c0d800301000400b540344041000803465550703089843d10520072a400340301c0110015422030b80c140a0003611103a4203030301601d510841d140410302c43d0042d0208c040014251070b80c42c03401500a03001c400a81e4401001001179940e42a020007104415100b15605135486500000250b10340c103014040c07105008002c0c281c07145c2418280120001c0c0d03980704c0010405480c000308901c3c0000300d00282c00280c600040e0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 193873785 1250 193872535 193872593
    0x200d0905010c060e010c090302011409030d0c0204090b0106020304050102011410091d0a0312060503010903170718032108041502030c0708070605010e01120302030921160609050409 79
    0x1880042c00740d0b94461003d542003120300300b00c050740251244242c4e271003601e48480805020702c3e4041e99026606500d6050303440030540b400080c0c042d102c900009840140007140081c0d55940f2041a85001c0c1d00800c0540c0c00820309004543c0c0a00401c0595065658100c0003460320421a0000520074401c140b15642e0300c000e030b003d01e0002c10f414a1030a64046044400e030800a140c01055001c0c14649051464505a40851030380b5041c081c0c20f1810340c16a613184004918a80050134505014190400344450611259131694001c4c40c2c00f4011070085000051914504248801142c0400f80c100b00304081c000070000010f0000c40d03031001d407100c00f442c01601c030741d60450080000e00c16a20058510000031491804000b070707a821050584981100313100d0f444e60385550f0402c2c0f000b4602e40040241c0c00034400005641001554150140d6500761400201c2603200381981c140180002c9402c0101c0c0c1070300e000e009542c3c2000f5078a00502e0191410084030b402e649400c2c10322401c045103080503002d04805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 193875035 1250 193873785 193873793
    0x70e030a0f0206120c0901030b090c0a030b0324040507060809031c1d0c030c0102070b0d0506040603061803020105091204090b01090b0a12180b040201050d0e030a200d0905010c 77
    0x2644d00b940c03807504a224150400e01c107043d210350000e015482c0040e04000000c04070341441e0065a0040c00704a11441c2002c94044003503000c3c113001110550140304145000c0c0c0c100309043c0346601c02807071218600c0301a0034903040c05070402d8010b8000d40e080c04044014001c0c5400d00008542c41d10020380402440c10b014040400702034088441281c46060130100880b04210300410015091081281258004102d034001a611119188074100a154080c0440050400c1c60303085183e1000c0e006000058894481c0e945004840080010035031204901c8010010907070244101c80e08003001d84c004086814825241400314451130050289446d11058421031303690007440e40001420392080f456488100040000b428450030b0810f11407042d0408400c41c4259001c1c0d8070303000341030b600700d846440d0b540d0365134005480542c0100300c01070589681d07841c40d03100907200307101800940311269101032a002071103265044095410f03590100702c0d04040303110b018442e000030303583c400c5400038200315000c1c01131418 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 193876285 1250 193875035 193875037
    0x9090c050f0a0c050604080c10060b09010e01020a020306040339020f0315041b14030307020d02031509241005091506040b090a0b0705030405061806070f02010206070e030a0f0206 78
    0x24000e019108017400d00040050a00c083e0a4211901c0121018803481480440a45120b4400e0138200301003003201d801c00d544920300140c4e0040040c0100e926480785640030900d090012201034001480c0098040c40c0c2110404110400c91814445400c0c804844410144280341011009200d60b00c00b594102060f1803d00105403d64000c4180e580c151900d4103100c1c9070f4040300040c00002181119000c01c0350180440718060b9008050700460a182c160340c03c0c0403000d0700c7c0c1c001c142c0c0d01d8440e4011100d80089021119403142c10241e0282c0203813101ca10503d10748140030080104081c0483d010000720390402c0380c0d1070080b50400c0300c080d60f80d510303881c0d42084a00b045041150f00f01400103400309441480b00000c0004110546501c40340d039540700081e04032406200710040007600200000c2010b86080c01c080c182240d08880d10207140c0c0c40310400102c0c00e034440e0f50120f0b881e81d10a10324106540e014001c00c0d511130080d003040b10b6403110000010740c0b5404411002007038485031070549000c0d510b0f100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 193877535 1250 193876285 193876307
    0x1207180305190303050612030715020903100e06070c15110f0d0b120303060109060e01020c060a030c021522150501030c1712121902031609090c050f0a 66
    0xc00b56041c1c8a031a540c0703000300e000c100380141c01003030624022a20504001c41060070200751400914200351207662100540451050190413a580a00c0314a050382d4052045483d0b00c10041d00c0000c1c441c50035001130b400c1c10401040501808071041c45803011540351078451642801500c000124035100b0010046e20b402000d4400b5002880481d0751100040300341d200003500c40044640503001000c09661329541c0c402290158009941c69208100d4103008045240000105005882c0c025404a000c01c2854202104903c0066100e0090a003036a030180301700400074a10000c3c0c00321038038020b00c121040d035002406407101c010791282101b0501007201c00d11401a55581020300003560349080107000e03003c01b4000d404000d08000302c8407a40392000115200c18600b5514218148100410b09140b00a80104007403a01e0010031510301c581c042d170303100a40c40344034000000d404101c00e23079400030700c3c010315a041040540d02c0d0840d00005113421405542a9015403102d5654406045504450084280e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 193878785 1250 193877535 193877543
    0x803031807060e1c240e07030816050a0206070c0e0f0c1e04050927030702090402040506010e0310020423030303010504110d05040f02011103030f1501140c06041712071803 75
    0xd2003d00705c28060441100c0260103d90410b00c581038002c07800036111103007403100034000c0c103041020001107400c013003d43c0071503800341c0c064511041d00ba40205000e40d0118030211034021042d6400d0100104440c0103039041403a030390401c0710a103000d85101110348200f02e0800c081c503804641340d42a0492810480d00035020207000704404e800c08800c40f0448071155400102808481c90303084d07040c51400030a0720340301900141a402c1c0d64503243c00303000003400003030801410060b42080c4c1c0c14054400f00440440d00002c2800169a580741a03180700c0c4420180701c00842007d15080006850307940003094070305482c8100d900140d00e0f003511940041a21980c01303030140442c1020108001c1c084031551030840381c0e0007038949103180240c50451940707030710040385d1203440c9411010204480c50800b050071844d14406050007801000c0306031028583d60031103450340c5c80c00c1d803115041004001140304403070f03c00304000e8181814010900ca8a0103d40b0006110700c04008080040c82d0704030145104681c025904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 193880035 1250 193878785 193878803
    0xb0a0608090c1f230405040b0d0803040506010501090501020706120209030c1c3c05160f0f0602010528060f1401090b040803040b0d060503070803031807060e1c 70
    0x10050b800482501c036410b04002081183e20284c080d40e44052141c00c4070403c0482c2185001c1c00d04c400c2000500540c520f4540200380c000309c040000704200d000f10b015502034002002e01c4d41c0f526000411748105604454110b4111380001c01c0880e4001030740511001c41844056207403401800445d1421a692030030780e5101c0e604c5031400482c02c503441840c6035428080c06001d01d0b00c06940900c006040b01c00d00645400301c60210701c041c8000f0002d800c0000c01403082c1e007902c2c01a132480600c085060901d8005035120b03081c1d1001001031594410314400140380350b000030704c00b031b182c03d02c0142d0008071000042c2206820500b0303082c54140003907018034040d04242d0a082880350b112001414041402e000c0140443c480c00070204501c0340741401d803822941c0c002c1c0110302e4181080c2580344075402c003100115400d500c0713041c0480d143c2e400b80710000181407039800942c0c69181850342c0015901d840b00c1b403841c6541000b035050241a5020101c00030b01070042d03425901c805e0602d002090b11074031000e009807001f01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 193881285 1250 193880035 193880059
    0x60c11120d08100b0a0c0f030c080f040602070e0903071b0915080c030a11040902130606020a210e0913140c040e0102040b09150c010e06070807030b0a0608090c 70
    0x504a25401e0043d4081086405025212090b01e6081d01c82c0c268170340086460010340c0307030000b0b09040c04404000d2003860007100700516607035840065000541c4200d814100854144452a070400602d00180090f0525140508240c0c08054891103a00409044000300505100480501040c12001000c00403410007a42900a1700c03c2c600712000c0c0158070190081d0248041c0c0740c0350014001c01d085d5000190070713084900c007404200042c9541c84040782c00c4140c18404040400045c450070300245400c0d005410b440702070b40340048144164011585403003608505007444103500c03e600c640703500c1054441e0852a25a240d001c407068a0900c0020070842c094070004140b140042101c607000d4105844c10300c01000f41e00002400d034003550162050b074010a001c0b1400b035141c040354500070314108041807840e003a00c0c01c070f40c1800d5800039184624154803580074030a004d80e01240a0781d018840e4502003085002d181c0020310b00410920800b401c1011050106240e2007083c844540b000f20021f0640e030041c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 193882535 1250 193881285 193881287
    0x12070e16110f0c0a140310021602210114090c04020a050f161101050c0c040209040902090901090c0e01060804020d02010207150c050d0314010303030c052719060c11120d 74
    0x142210685038081e00b1813441c002460700c5a01740c5404162801000380c0600d03240303200440000d401181c2045143d6441e852040003580700d203000114120114001e01c0881c0254103003450075260301111a031603000e00750080154204021808907501b4004032005a0341740e078901011035107030061000c038140100c1c0004821450780101c14802d00c016209800c940084120400195282d004400d410940c941001c103140b881c0d4907082c0d00030202e500c0300a000013010103454000c03a4050400300d07080b034011780d902c0714900140b007185400e4000520105001040f03940c10044010030280300508000e00544e032450840e02168001d00170803001e04403042c0311400342c2030a8540141442580e01d0300f60f82900a503820102c4e15442805840b91800c440400b40300300d6482c40d50218001c0a0060b2a2800c0040510080005d0720f03a80e00382c0301e82c0006041d0708005030300703000d0100700b80141e0460f0200d0800c68a10400c10803103401c102000415500101810020400344000c1030003140e10f006074150500824089031116 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 193883785 1250 193882535 193882543
    0x6010c0c0b03060f0f03030a0e1915030e0a02060703030b130c090e060d0c03170c1002030618040c06030e100f1b03060b0f03250e12070e16110f 63
    0x160f0801c0780c0102e8002d03500310510254040e081003d0390160401c1204261060041c00000140d0602900d800c145010305100312a603400c032070300300c070405610380d0a50b0301180358103000b80c0d05a440c0c0003028100d0004280d0014005200e000001800d140d180c118101d80365440411507080c0320403041d405d00510070341d000d000f850540030740102c80c4d0300300190f40420f1641c01c009018411540d030140104a400d801d644030b05002c40c0402803000070304041004656041d4905000381103101c03a40400158881c00c16100300031401030009110b51480000004200203d0451003142c5e040382e0711400e00141c0042c55050301c90410003823098012280e820700994107096080c41e4001354900b07900465003290b016110800310309072503591113281c921940c284001580c0440ca2002590001110000700c80c00307180106000c900701e802640c0c02d9001c2000001e407005030381031202e04500001c0c002c801400541b4202404014642c0b4013a08c448400e413076007200d030b00c0100d010340f001d00e0a103801d10007244d00601c0c0860001d41c0d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 193884892 1107 193883785 193883791
    0xd151104080d1103160501140a0218060d0f1104060806030d120b010e040c0e1207051309050a08030408251509021c0f061401060c080306010c0c0b03 65
    0xd241c5040d0f4502c00200344039000100300c030046800800b64445000b48110727032043c0104018406c0341020300480c541c03d0811100b10740c503401c9005006c0c00412501c0b00103809189030080c84610440ca080c0a041211256070f03e0481507603882080c15183c80040000c100418503c14604421075805e130004220300006150000d818a1a00c00142c00e40786461800d0300071070712403500c4403c0c6041000502e40340c2482000107010a910700408140c06040c1c82240314941e5548002e22000c00000344020070a0740d03000944141c0703908060a100301542e00c00817151216040c4061141c11008201d1258203d840d0007040448011152101d140d01800c8018812a030014002402c000407088040d0300f0104a0301a0601d9054000c2514048044a510890780010441007800411600754001070455040760311100c00e58994076152b006980f40881e03020020100365403018080b411b102200c0203544 = true := by decide +kernel

theorem cover : BRFrame.Cov 193705035 193884892 := by
  have h0 := BRFrame.cov_init 193705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 193705035 ≤ n) (h2 : n < 193884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
