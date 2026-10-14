-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0947
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:21:35.544975+00:00
-- url     : https://prove2.me/submissions/eb3006d6-2267-4907-84e5-a137b809aa1e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 170143884 ≤ n < 170323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 170145134 1250 170143884 170143907
    0x1030c140403030f11010c080a0b06270409020303070b0907060207080712060b09040606051f020715020331090209010c1113060f030507080105040f0b04030e090702030a 74
    0x260010000420310410611400346020003020720241510209419119401846910031404020300c0018040302d806424108203507180548241001c0d04552181801d200302e65034590212007840311098103804079201c1c04040052240d110742c81e11000e101594081000d000c445005007407544aa00b0010100b52901a00b0390014080d0b400c0082c0803c4050800308024007120304190349400c41c10441d1030414010700c0640c03601c2d030380f0010b100180410b000d1954401c00c203644041d20760100f10395446101c0a05148448820001607210790800e00c080728010020381d81001490040301e04128030820300c901c840706541242490741c000c086500307200b9100660b1050040c40540421803810101a0000741049406c0c08003510100d40c400c80c08450346c40e01c400b800145581c50008200c92500e5111540f2004110300c01a151841000320119420b40180324403801258800c0f07402503625065910b45280e250001d00c240e0611142203001802034480c50060f6201e034185038007540d959080100701400b054402d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 170146384 1250 170145134 170145137
    0x2103060b040e1e071e1407080309060a02040f0302060f0d0c111507140306130e101d0304030209040809040207032604080a1101020f130609060e0d0b040201020c150901030c 75
    0xd018071041d0780e0440003580e007401081d03a060340b03282c0403005c064400b0011601c090f40d1009000500d4010311030900059401469000160fa18944a040b81d0034160702031401a40070a42414008000500e4004000c0c282c2848000303506d4145442041030070100c07241c56000c00040f40c0c1e015032a1041c00710610a511207481041540c0302d86051070040202045260880340c040c000c0000b01049403a43c80511041c500040404240482c04100091540b900742c081c0801c244541400c0803445000c1140480c607204406040086042618503001c1080600e00600245c88805c000c000019103521a40020113056010f501d41c034401c6842e007829151a8800303c01740d006c0e20309180d400d20002910b400c04940d05140e03146020841e9040e044180c0380244103c003c1d00b03006807c000b41440c04003001084144c1200e64580710f04134a1961140c0a80d0340c6180006080e520500d8501f40c3c2001804840c41c0b40d40040c018070403112010384180101d40c0c1495006804c00c0700850205038484250f0b0300d40122405d00c040b5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 170147634 1250 170146384 170146441
    0x1c12060b040305061b04091a0a0303020d091d060d030c050307060504020112090f03080c040f08210f0a0f050705010504150b0d020102030f3004030f0c2103060b040e 72
    0xc1c00301c03016175801a030280d007030f01c6601c0b050003201d1380030442006425400b0041c40e640b0001e9603440e02950f00c405040113800402c07030300d280c00555103840114040c20f009003040151115510001005000c40c000303102202130240c2501e6403c0450010009040643c6c410344d40081c49003828000504001c2d20502c60342066130400303d9202c001000e09044400f1141e26040c503400d40d8640800c58240c90145421a04115100d82c000094009000940b0400d4107160340d10365440c0a081e03e803a1280784110310010301000020003414503614403902c4035000e031310703880d10f0401d00f42a45542c50030700792841030381e0507074000085a40c81311880341c1e14070845940310302c100d50001d05101168000307501c9000e001803004040790007065503803000e8041c00741030880c0d00450b8140054085101c140e0029041c007618141d00007424945182501c601900203100d620f50040009480000310001103201040d0481c60441019240c0e400020085c130140d0140001e040e06001c04a403615022003444440c0700310060600c0e9040340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 170148884 1250 170147634 170147671
    0x90308070813140f04090303020c01090c1a13030807031806031d030405010909050c1b0d020f0a0206030610141b150601080c03070302071208040203011a01021c12060b04030506 77
    0x1503201315403122450654000c06c0d0205a42804c1d0000d0041c140d41034955400c01149100300308410725004181c4102c0c0e510095002c1503001600224060100100300310090803c01b400490300402c060241c0621a103807820b00091101010b01c840d810b03550141c004291900141100c0b845e5218000c1c00c203074030300c00c019801c1c1132405000070200c070100e02c00d0703040c0c042c0d441c00840d0b0104c44844c00c44205218201c400520103030703510b0740a907035901212216001401511741c2070480780c0002c144002c00030b030010a0f503400c40d180e01040003000c0301d4100c2c180080c0f2494138070a40300300500b44094462319030f08032542140b5a500b0112142403000b601c519102c168950303800c010b100d03a000310380d030b41d0801c5803042503079280da8544d1801c0d8001e1050040c0030b40f00010b03115000203c0369000441c10310440c0b0075002031212081c1d004407010900b8400050340c0c050380145a490100c0c01e07401c00548010446440d003034a68140119102c800c4a481f5000142009000101442441001c002e095003107404403003034074103404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 170150134 1250 170148884 170148889
    0x2102030604030804170a030b1f050306012019021801060c02090a0e0607230301080d0c140303040b01091121060f06070609060b0a1202040b130509071404020c06011509030807081314 79
    0x100041c040c07370601c811600030f407482010304c1e6000ba8454400d5002c591000341e044105014401d040c071012842880d4002000d50105402c440141c102d4045031100c00f641d400b00e82c2001040340c0000c0c03801501c2551808001c0c179141c01080b1503405101709032101c11801d265039900c810180c01405580d03503550000c1004010b040030008040c8500c404624220709010310b02e103000342c803001845a150440d48404818401804a60841241210400c000c2005140031400d0b04141c1d43c0038016200c2006a0303031074200060020500d05950740301c0b0005207102e4a0501c5a0006002500040030036a100c0d41d5641c00310f030401150b031255070b00a020464440c07900f1032410b41c1038403000c120340390020b0107151151240c40c02a1940d01c480f18481d4060380c018002894001d080580e100424400c140034800400c650380018200741c0300701c55060743c03500050311040c1e081110010850000b00f81e81401c00c41140c8001022582c904041d10034030307104000381a500c0b0044c0700c560301401d1142c1c20070250051185032000155 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 170151384 1250 170150134 170150137
    0xc0602120a0e0f0a030c02090601050408120921030703030e16081b0a0f1203031104120303050c21180f0a050f150f0702070305010c02072102030604030804170a030b1f05 74
    0x7c0c2d048403083c4880d5100030040303e0034052940141e5107031140140e20540794403c540a009045402e030355481e2483c08009440490000d01403030350841c1c0e0010096100468405e0700440505201c041c1190850300c6c000d206401484d2003580142421303045805101110040f200110351b10301021a5500a694103082c1102c03500704051282d00414900f60810200701030113500300007071100d07154030105e41782ca0341c0303802509021441042c2100001e00d0000010489c41c1e01d841a00d40210f040c5000702441100f03900d00d0440d4090207002e03454484c0700796055110005007044000300c1c240c0c411016207401c0c21149003203817030802c062007082410380201c01e524070f420000082d11079202103014421141074586000c01d03403c21580c4e41010b002d950034034a0000d459070300064280b0480d00c0c4a1284049605094070700c1c03075048034101000303505800450100b408640f1440003240c1050144070301d08500440e8100c9042282c0c032028a0304042615a9481c01c80d528107800049610b00f4001e40c1d100f0502540b40004105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 170152634 1250 170151384 170151407
    0x16090902010212032203050a170106050f0c0a0b040615090509030703120e12030106020d020606030307030806061606090303060b0304020f1005091504080c10050a0c0602120a0e0f0a03 80
    0x283c5901200060b61441c0030040103144010316282400070000c81c2c100200f465000b205408081040c03815940e07599101024403e040390450740c0e6041c1861000520032219501480c5818000e10a0141c100b003c900e00c03080190140c0e22032180084d034030000100c0c2078010b080c10b601075000309140c1300c20803080b00c9001c8100c5003807070303814500032403001d001420010042c4582d0030000e01034400c458081c81845040c00045050340c881e0f8084817440c1a039854100d079160401c540d050342541085c003203e80041d00410f0050b0304514001e200c00d081c0060441c03030410b542e42c407a0b0b00342d40c11500c54206200707050301445500050442c56034680c3c46c40c9440d40106120321a0030003da07014120855260394010320910a698000b03400405042c0300e2080006915441e410038040c002c3ca5000390b1086890518042d21030700300c400100c0e181c51b402d101107150140c030940d0f0200d806444040c3c080000803d80c1d80480c000a2141049420010341e00d241c00580038a4606a8036000030316600186074035010a4002c01c050f8075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 170153884 1250 170152634 170152663
    0x609150907090b060d0c0c02030c0d02060904230408071b0506071101020106050d05060103110a05150c010f0e15150a42080702030307090b070303060503030a02160909020102 76
    0x48045403500483c40d98414401170312459850200001a9281d100c451890624000c034100d554a54440c410464060f00c02c050080d48020b0422210070f0341e042c140c00c0b9078140d55594541c40c0e10308805154100e40307900121000c0b43c55000000d40b40c1e003044025540c030341c0000020040d08000750f0400c004540c240c49041d001810300c44040c010400d040e8400d400c2080500405029801d1401907460002e58800c0207010071104000b5001207841c035802c0c5101160f0458600500381d0315000041410100181c1c40242c04d180706540314080c02c02040b40d81e02500174402d40d15001440382c084100b401c105c400c040608000790b807802103160304000da6160a80c3d04190b4009001d801000622034102103103c03e0088041003080100c1101d003560041d44d04500c42d2650a252200c01e056074869400b00d807203210031203890000c901950410b1241207031040141102a110b8200080e05940766000a451600208504001039202041200ca02103144a251000303000001003800300000036070000c0d40b00c0c09400c10010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 170155134 1250 170153884 170153891
    0x80112030509030a2003012009010c0609050a0b010e0603010e03190504050a03230a1a0613060e01090e011407080417040b120906040f020f130608060915090709 70
    0x4801e0f078042c000000701d03c0d4040d02d103854603d1640c03052024140132800c418840d504c3d107511040c8003a06021420791020304d104145281495450040d035042c00b18440507613140380d49004000014030100503115280d400303110340180e03940c501030013282e03c800300401c594003e904045203008c0086000044e03d0074070000c96071005000d036980d18101c0daa80941c2c0d000c5903006440d113000000340842c42c2e01d004074032200c40850041800204444a41e140340c800801003044050700c01a80388a1050007040f070304104020414a00708d0072403100301c4151100364015000c0d4041c024010811500244514031355640417a000f4060014440c0c1a500142c0380206508140055131001404100c00b100101150301d070440c0290b0b45854417814800400d411510000b0030302d00b000004103404c100c000030031600c590b0b070013001302c0c07140785043d801e000031702c00362402c05600710079000058000c00c011030003140b0160010718000c000703518107029030700d14104000004080b20361aa005100c1d003000d011940d10251000c490010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 170156384 1250 170155134 170155147
    0x9070c0f060507140d0b0f030a080f0f0408010504050705010801060c081206060403141f0b1c020f030f0f0c04060305060a0b0d02040c0206070909060f140604030516060206070801120305 81
    0x142c3e00302c0380f4140c5205030400c1c00200d40c0c5900a2581c022001b40034195070541510041c0801c5c903035284034010000c0c21544042c0187d20711520880000d0581d040500042d904269660382070710309444096500322500e07040b0200c14015540d0100318140103140314035082591407010b481c0e03041c0c41d00c5001c4151240c00300380300010300551a00c02c00c440c02103510900c0c01111520602070207031120010b002c0c40480c6c02d841c07001c0e021010943c0c00341209d0003500420301d1500b02c540943c0c0072140748100c482260864180c01504582c1c0d6800c3c4161890303c0c5095024043c0d40398038038500c5007000e0b441004240b00d5031400d0030900c0400d100040305d0768003402481c80048d43e1155500081d44144440000039841810104c4483c0095408159640101065100d064905440d0320410045d24107501502031401d044803402c001c5030062024840c40c102c4040e01207481d00d600c9890302410106580d90401e1171909031001080010350410038294805500d151190043d4180404268401707030400b0050104140802c96 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 170157634 1250 170156384 170156387
    0x150a0c0b090a02090c03041a010f09020304061103100f09020f0405120703080d1b090605192304030b07050a08010308090310150f09090b01060809070305011a09070c0f060507 76
    0x407409400401d13942143c603041004401c190300c111740890fa002c02d04040e99811449082415044c0c529030000c04400908125002009410082c402e80708251555888081e50035400e00031401140c0070010009254104000070110b0106584503620312441004081d0040401c541900d00360342c4100d501d0452000310100c0c0d90719040f1603420281214500040780f045030f5505501c440032040341c0d5800c808165611007015520100d25100fa000031510400001c1c1c4242c6604030030115000b441d040010040264a03914854032124051502d0703042d200090610074800c0395030403030740c0c4400c45141251a003400c9401c014505103061000402035079001c50720b411659020711144280f1081c4050411660025800241a0038910320585c2c01005d0440000f241ea8001405031078200b60301f03c40c0303a8441d0b91030808210b0700702c10010b0100c201070040b01d04c00300000c0c10a000380e510500c800798250007800c40f03070010030400c107034041c00003400e01c01700c1c01d0403100040080005a0400b40c110400041c2d50703650301c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 170158884 1250 170157634 170157643
    0x201140c040918050303090a12050307090605030a020c070e06030105062202210a091223090a0e0406060f0b04080c090702100e0703061b120b06190e150a0c0b09 70
    0x10b000307109000200810a1a81000231304824160164052180201c0394800030388161105542d01c0000a00002c414410356010b80001c542000c1d00300c2d0700500d1b00606491060801a003600006148042c54040c4a00ba207000d015041c4c00c11030403190300c03d0074040b1100f1001001901d001c80c2c1c68494021501c05164005240d205039a0302e18040084c02c41e241c6007040100501c2c00c450201c41200d005540b14100713512450cc510f5003084609481b01d41c80080000740040c86d00300154240c1d2045817031401140c001c0043d10020701031803040c0b801080b16400c041002c0c44000964200000100c0c081c0b10803c0000000a03864100e40300560310f42c1141e03103031010102d080ca0107080180507124104206024000e00c000f40701d0045902a020400064040522042009008440340d1000824030030b0b000680a00c5540b00f50b5080d88028940e500c1d000c81d40d5191902500c0120040c0085245595000c8844c1010401c034242c010b0f020401c185420794a03e4040d20040300b80101500250407100000c880c03030b00c20170 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 170160134 1250 170158884 170158931
    0xc07150f0501080a171303060522050d021908040501030c030b210606040603050d08070201060f0e04141c0e03010905060c0a020d0807020d030e010b04090309060201140c0409 76
    0x520520280d83c5500d03106075a240806000c6406010035804040c400ea089401d4414150700000c1e00000d05103103072280800340c10090704101c1c0e0400035800f06d00c80d4104083e64028854420f0000d05003401c0044000703402e20410208050b0b10b140c0d00040800000c035210104d900b919800d00b00014002c01d6174100300d003782400401280c02c00100354000c546244203443c02010200c02000b15001507503a0400e200c140c0e04036220082140e80410041c0002a00580d5005c2c2c0c840014400041d8656403046039200f00005a0701074802c0d00184000e01085c070010090b0b48003000740600091a1a031114955101c4900149942c0d1040204600c21141c09640c29084100c0440c0c015003281c0c6203003009a0034060a520204804001d48914218001c5107030003859814800c1242e134000d0040700042000c1038000d04000307241e5030055541c0d00c41d0078090b035a9a124071001c0da40255100342040781084006400c5490441d00b42d1801e801e241c0c104290700c0e034100c1c01c960684544030070100300008402c914059201044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 170161384 1250 170160134 170160161
    0x702030a0303060f0512030405010c02220c0f030203160302030901020d021201140d030c110111250603140406020a050903030a0e03010606030501060c110109081519050c0715 76
    0x51500c0424194150420700c180e404259441c4031080e45c42c420007200c040c01b0410361040384c0007800304000b558001e5004024407030000c0c00c07800b82c8a01d0140d035a64586061920a042c559440e401c1c218480d5010280784420350b03030b604046180d41441c441d850840440040490200354000002170300f410760070b405484045203c0c490135503c3d002060b5180c2c108090034003505151710320f0704601540c64070f4a40a4240180e4154490003841c2d0b87c0b03034944200358044581e000e810300480489101c03c1c400100042c114004944112100c104010040c2c80b0f4a5545903000c1c108141c03c2c07601c90301c1075402ca14103041c0c0150303014800581c0c400075081c0540e03d130302407080c03126814080400d0081c2404c0e003200034086400344c102c000300b000544464095080310760a000f01c1c03001030840301c4070b07200043c0e020210450a4030141030035400c036580c1e0b110b8246000944810f07401e0184501c81844407000500780300304d1050004000a0042e8a172415034a5050b002d8a2000703410300301d070030154400400499200070043c2104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 170162634 1250 170161384 170161393
    0x6030a05011503090b06120c120102090f0402070215030406020702060a0e19081b040603140f0723090411060f090306060d0203030a080714041d06010e150f0904020a080103170304020a0303110102070203 88
    0x1509e0819000b900240c507668010380d0a0310000b4914a414400c031180254000d02d00c00700141030b01000443d0350001442113a11903801c21005001da034170361000c1c248402c100d56800f40101c2080d010b004162600d80c0c40801034a80f042000c0c0301103a4041100c00c3e50401c1c1405580003407100d00001806031007190700191041041c2c080b011001a00400c021109d00c02041c21511001e5858800480c0030940790b14000c0c02c0049101d0a41031868040c0c0c1c3c01d900b00340110521510600c52100180195128141c95405050001006030a60806200c1a41d020310225489441a00f5039000300380c482c800c40504000300400b41000845040c0217907419410a49030101c0c9070b0700d603a1555070113007c80d0545501e000c07040da0280000b400640c4641508056104050023840e254907c401c079030900c43e0056038001900341000e104212040d21248080c1a041000d586c2e074012552650400800700c100115104158901c10802c01000d030311800102c1d41100c0d03040ca40a01c11409021b01e903030080c003e500b00250305004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 170163884 1250 170162634 170162659
    0xb01031119140a1701080d0504060e03010906050a021b123103030f0908010209010f18031a0402090c030702060403050d1107050d08060a080715020c06030a05011503090b06120c 77
    0x24080d4244075044491821960a46d8a90055039a9078900720404400144104402d02500b80309078058150200c02400100e00310916540310720680e281224440c01c041da01003580b5160340745608105080c0b0380c447d00074112014041c0700c1e14806104006081c1082441d001080b41404000248427680760402615000078544a01d40184264290000c001c0014466403010441c1e08040c801c4517051a016191001c0d11a4405030540350075a4411070005c03130340d15000d400400300c2e01c0503001c5801404c005102c01c119140610400c03440c0c0101614490303403408140b040200140d00007400c039030429054201176072580310301e800c180041c02031052481c41b00f90000c00c10100700300002422500b00c005ca9102c6031407070356a03070f0103201c08410740380309100c61a0700c03e840412104803820303003400400c8040d105071040008501c0219071161f000355081000d450b0b4450042259a003405504c41c0801810310b002c0c07100f1652a1180504000e01030042c40c0301c3d0366400f0503015400c0082068004100c1c029020149051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 170165134 1250 170163884 170163887
    0xe0d0503090301050a0212061519021c02010504031d0d0f050616030b0a0306020c21120705040501051909150507020102060609010308190e0d06020d0b01031119140a 72
    0x700006039282c025820500480c0f0b1807801c034020b40d0f0200c030100800e1100d076651399003040741b03ca44500c04072044a108010503201c90042c1d01c14101900364036001401040c1803603030003c488403e00004c1c075007164503180500000076807180410280c41aa0025443c110042800040c8d00148020703000f0090029540c000c01004008100a4031440000e01c0c404840c0c01d120708154141c400030301c82039502c60b4403e1350a2000030300d00c0d8003070440031140004842450348800700c480700c200d04108560420010108100d00e800c0d03138440c41d440c1e1081e10340c42c0c42400c0c507140000203070a44c02803a1402d14001d007682d4240e0000762142d0384103401000e00f01d0010078412848040903045500548050340180210400120242445808203040700c0c0e10110300c41c0750040700e51483c41c000c840514404108048800704207501c2d5200b04000b00601d00a60300143e641e55140a55012610319420f99810f0605100c0c9064007900300740e05680206d040380c4180c40341c0d108060740407660301d41d18402c242c0c60080045541401e25 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 170166384 1250 170165134 170165137
    0x3050403120903050306040903020102300907120f0303090606140f0f060d0c022407080a1e150b030a02030a0e1207200303070308150105130b030402010e0d0503 70
    0x69019803507021020341c5041485080d1000c100e03014002c140300704007045042c2060341c00848480e00074800141030900c1c0703d20444d80d01119403140402c00c3c405800340c1c181000c119070616048010300d00106000c900c0c0440f0034500390b5114001400b001c2218500c5400d041c0030342c200b0798145a20560802149440d0340c400b50364080c1c0800e07040d000d101200d21503a464200070002209520004000034100031144201a0182509908010850080018910f4030440e4034040301400b00031807251803031070f19006e03400400c9458020600c2059608020180080d00d400341c009152201c01c541d40800c4c10204803911041c000e51590100b144110000300b0004032180580c081c50003540286420700140c500c204030b40740c0d188121a141c00803403008008400000e2038880030061121090302c07100551001c4607001a0940d00243c034103802141042c02000700340d4056103000c01c000242400c0c02802c004039580041c2401005006142c1d07418030001c045030035a8041c88038074004e00001002c0314030950161900c00e449 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 170167634 1250 170166384 170166391
    0x906020c060a060603020903060604090609150b090709030305030f15060706020909060303030402060d0203040c1203030902040c180e130f081e16080a0c05060108011a091012050c0604060305 83
    0x414540f40000c00d505201340203d583ca0380008004040b180c4411040000074440034008840e10760391070141000050000300002205d12001038001071040103907003807010400c80100148200320440d8004e00010360000c003600c2d0080b900c0c4040c00b031540d4945882d002c0200421441c2540004c010400c1e40404c804c80d002408075050030742d18400240c0f29030040c560390740010749000350302c98424018468201c035650701455001e80141402c040c1655190f01644480d008200181c000a031605c03c02015070509005002c3c0039001032078aa034040748821500c1d40b244d81907001d0280d4901090022a00d40c82184004400140d00000c1c1f510744180f540c0340403080c6512100b0a0b0510b1b00c03840700b0010480f40c00300140c2e4403004511459500c4140c0070380c0d450140394001c07103e000030322092049200110302d0400000d8040d10741d90000003801c0d22000514101401024501da21441101c0c0c100440c1e030744030f541d030703481250206000d0403100034162804901345001a110715410070004940052010ba040d00080d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 170168884 1250 170167634 170167651
    0x120b1212090301060b03131202010f110301080f07050f011d030304121205040b0f09030a0605010326030606091504150f0801120302060c0901050c070b031e090706120906020c06 77
    0x1e107640300a191214003080302c04040001c0780076001c0e0045408c2a9803401000700c07030b200000d000d07011059000b0455181c603480860401010005014410f0b080110b0200851140014241c291920300010b945510980b5042c4c100f115180c9070709061394441c110704080c020300030140ca882d01d4907020520f02c1b159a112050b40da02217003071401c2810a0207003007158107461080074281c0c5800406001d405556001c8407107543c041c490000c1240202e016131280902035485000d51085891900e24000d0b034103000318841d540070003003c0052000301d41d00c1070112026a00d080c1c2d202411100c0b11b04000302c0c039009541c071806204110300c001c014a194420403012401d011071b241d0070060b9898185140090852004c000e000d039100001041454050501411b844081450006e2505008079a0541490f81c103500c0048181000300a00591650450155042083d6151045850300c1c0c0280c0d04d903603c0d102031040505200c644c61a03001f1002154001d2616aa080741040d0354909a00f00c05540c0c40200b01d45104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 170170134 1250 170168884 170168891
    0x140f060903160e2a07170d0213030c4703040609050d090b0a030f0605060409200f0a03050601021207050c0f10050a08090c03060c030f010b0a120b1212090301 69
    0x860602045900c05504400d844d450300f000d1843e078a04001a00311604904070410602c4540105130f0103000030070f03469805801c001d110340d24600d4503074090030340b541204810100b0500070581180000d2001c901080170b60b801403241d102529410003005a01074582d0743c0c4014000100014011240c000b400d600e403249003140c8034040b4841c0204d8407004107000d05d003040d210030055084082d00c00d8014500100000700e001801594540c0020015030013648030400240d12a4298800203184030003d020350004103d82c1803174602503948008151250098003810b05560f00d002c901541d200304200d04484007807050059a45103542001c50780e800c500c2c6180d600c0703604c2400402c8020b003009411000200c103140c4650342040c0c250301b82078840500040900406100300030507164150340402005020380a40241c0a65a0515a0780c40e601540142c021501c9498104008184140e21a21290405a9140d00002e42500b003100083e20301101456503401807250344842c1130705c0c201790402000e42040440081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 170171384 1250 170170134 170170171
    0x41503210206040210030507030b030f0708100b03030405121002030c2502030622020301021809010b04060801050d080705070305011b020601080c01110f01050c03060a140f060903160e 80
    0xca036520003c40c1c00a40150984502106090007908040d4010220342400b28640c802ea41c0864648181010b071140f0680c8a44010414400c050204180014152405118114540b40401d50b0be10440c46454041c45c2c03d200c0034038610b8010b100c0d060324502c0b2940c1c25582c0307041070311082d4042c0c0c2122007961000c00048024030401d031800003403e510141e0260180c1082d5480e404a0404400101c8810520210104120005980a02c02041c0b070708040f000e440120540c680c148628000d050304101d4002c60100001e106058000303100504407002142c9405460381750386031404441c000c00500400600c908640441003040640050b1204070000414485901680c40b0803684e0320000c0c0b0030601a50403024444000d0351182842800300e210180880d850f019100902c00e003194070807222051001d001109002c0c440c036107420b40e50300500b400000740c03240802c01400101440c08881885224800001700507040752010700000401581d05000d103188130b83c4c0c40700d40840010f0b0850b0300020840d90342414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 170172634 1250 170171384 170171387
    0x519110f060304020a05041a030102030c210702060c0f070501020c010f291e060406030501050319030509010327030201061d0702120309070e0108030a080c090f0f04150321 75
    0xb41da02c80d07074004001500345454039050000030202c500301000c0602594841d044562024001540290500f010844d900c220005681f0b41456540c10800304c40132424007030010b05640000e060750450810711a255a420000f11240518450244000c1c41c650000c01d221030b000f5410b51010511403180c0d0f0b000d021aa44025501c99600c01c0c02c1d070040d1540c0034501d4a0441c90410b12202012000c44500c000d5250081c0310003d0803941003580480c00180e260801400b070303802d00384584490100e001c585501c900b441994040c00902406a046041540e5002c8468000100b0100285a4807120011205214407820024040e00113400b40700c40c0c40e8032505042d0392441194060903c200860760241c60030201a201d620010b40c4060107821507882b44840104010510309160f5000b400b130f1100075a501d18034141c0c058042c00c0d00601414001c1010f100f03601450302c1d030300000030740058201e130140320040d84000050010002e44403016603580462401004201c1c1e50f42030b02008141da90405a180e2400920 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 170173884 1250 170172634 170172637
    0x20309030714010204090516030f0203240a050406080d09080c090403140708031302030c0a080c0607030c06110406021e120904021207020c0406090b0604030b040519110f06 75
    0x5005889038000c0010380302007940700c20144a01400c0701c00161505a803120210262002590105c0040a802440805168051003088460200741c1415415451310b541680080b0303c1c40c0c01101c01d808000d100b001d402e540c8000d83c01000e040001e2040151a4950350515502e800c2600214040b030f01c44540440d801c800000c61070702c0c061000381031041a0795a5907080340c0d0603004051015144600340880d90004190748091407103042020003900303011070103004252401041000c0c003806282d0002090001c100b0218200c40c0c040e005561490b600c0503d440c0071107440317819a10180c41240750400c507610f0a039403503000f44201c0e0744a500f190024940b90040e142d0403640e4030341c000d040d640984030461255000402500340741b1401080181025004e64140490120442c4d0040041e00320454001852405e842401c0250080bc14100541c41c03059010404c603120b50b00018002009590002e010800208113002c0d103408900210700e920300051802041c01c0303d400c000d06124600c800b080c1c3d24603091030070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 170175134 1250 170173884 170173891
    0x6021b0c06071403070507030501320f070e0406090501030b0105330c030d0f051003020a03110409140313090b03030304021504120b1009050403080f0a0605180f0a0203 73
    0x400d4203241c00b0700c2c0c0d0340308140707940e0440780d21820b80410b005c1c0703a001c9002844198011801400007068001c2002c9103006080120062909210443d0002c0030035210300354200c81c1d00c2403459000c9413807034031003d100f91030360f00034035105550040c20000041203410550704200d048a10502c0f241c1110390300c038020400c220500d07041c0d1000d0481c0940b91001802140c089580000f2502c100031450301405111080c00c550154520025003500d81002903185002880b41c0350b8486588245c80c06203506550026081c100c803840058520354281800c000641d170303140d1103244215403000080d61840c1e1b40a80b0725483e81c110a83c1640c09100300303000015824014001ca81031303503400602651955940d9400c1101c181500000000c80e10720a01c808155042c800700c080e11418014656008207180c0303148200300c4607449400c1560805e040009010000350403907043c94010b0310002000e085c66843d440c00b80014030aa41c0328560000c00300c203200070300c0030101849034010b03031890301c01130b400c0d644440c90320b001d912064 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 170176384 1250 170175134 170175139
    0x307050307030807090308120609010911090103090c09090f1103150105010f1809020c010f090206030c0705030906070f060506030a17071b0303030e0f0601030c09021c0906021b0c 78
    0x100034801c0000c0c825521254085020300304030801c0e545035224020380350001200c0c1d13000b10041400384000c40c82c0c6001c000740144001041402912005042c459480c0507c2900c141410740394030030728082040e20100503000e0501c40c5000c008102079400c100240602803a030a80b14071003903007104c94240c00c01040180c2d4902508084c4869a440c00004503241640790b0307806e03800c00500400307080c0103c0480e016400100f010541c050313100c42000f00c0132401c42d180001e00703040c3c081c6844101c20050301c4001c2503944c0301c14030117030080d1500340d1410b2241c1180b0035011aa50300c003600141140c1000204280e60f00c0300780c040c180030440c0d5900c0f4030515135a110200d50184c0251b4100b400d01880319034440081c441c445c41400100c59a01000503d5022480d09400c22400f090711146002d810030802c10100000b00c1401c40204a42e51646d20b420410b07800b1400342200298000415440050440c00300c0a060550303c00100003a00d0700303003000d400039000381100c3c540c03a804e4103c503100814800200f402080100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 170177634 1250 170176384 170176387
    0x103120305010e061c050703031107060815040b060c0609060109060801020c07170c030f1c0513140103020f07031101051b09131b050a0306060527030304121109070203070503 76
    0x5080c100898407170148166018080c18110030300000b0300502424005511070b403509402d0752100002e5a0410303109801000070002c118041200d45503d130525080c10103000c1d10002003039120f94000c5034032072241008030b030600c0c4074003c188805640f000940c103049543ca041c0401c5120703120b8500900381e00c030340c02d1030302c840f544820b0041c8410780c0502e146a00c881e200004503000d07440e00b90040f030308191315010028001c1d041152007603000c00720821003100d00760162508910b0150510304c0a0081c00e05401a101c00002c004000b02c000c6e4017941c1140c083c3c2c00c0007088107072500d949160013890340d62401581c18903035080c41c020030006110310032940105502c2c8100ba03800c0032051024412030a0340c41180450382c0c2c0d110080607240d03840844807540d016010303940b0280d403540f01d154090291580c5a00420400604100702c040070004404072030711440900c4c844003070700c40140d80000d103035019a810007802c0e007044090303000c200056440c04030101101a0384884241ea203102080c2e0301d0340600c41000c4c013503420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 170178884 1250 170177634 170177641
    0xb120a06080619021e04090b04090b0727091b090b07080304020303040b0f07110a05090402060c0c0604090605040f050103030509060a020709020d1a09040206040b09270103120305010e 80
    0x3c407030b404000726001100042c00d00c02010904210301c1d154140017840ca01c00020280035000413401425400303003044d84c0030b026440441d541e14500000007030662007004001e040e02d44003020f030310352800200380714801e5950b50303103489075a241d000300b42c44102240142c00703160202c920140160032802c111215600380c58104520b41d100c3c03106039400200120b905000030040440c10f04a120007415494010300d505d2a101d80c1c0b80d00d00040200310700003102d0b10030491800104802c0d9554000d0940c440d505541c05c51302e61030443e08032468044020715a6500c450045804190100d15038412003c0340c000700c40600c039500619500004940003070002500041040182440c81c0c280300d402090b8500c864411240d106554205035001c03070f00501413041c1080d45404042c0c00c100000c1201400e0031100f25005920303420076600064581c45a0b00c1080d000d408081480f00030707039440e1407101c4c940c1c58000d81e07400400e80c808a54a489040240012038064810111650034548070b071140505030780459203080960f44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170180134 1250 170178884 170178901
    0x8010b0906040b030f010501080a0908030103060906020d050f06040c03050105030d0309031403011404050106020c10110a0b18070803160204020f070609050601080606031605040905070305070b120a060806 89
    0x9011a615907004801000002005160360008611841017000341c054203504000004003441d201400811001341020002c00220b0070000880f81140d80c0190001441841031420300003074000d45048680b400d14040c20042030044440c40144035083c11281000f490b8030448003502194001c2c06400d4256010283c0303c0300144c082e6001480107406414055204110580c40300a181c2c426001286503a00480d004512401c1a0140c1c03805003880303002418202c0c52050104200034222100b8804000c10b9890034601c4074401c0c0842805140c200d82610080e11744206d0b080381e48885041c211056105144002458540100503240309a60b10b0b12100300090291f002c02c00a50002c00b10340f610100100a0000001c04c24030400080e0b0344290003401007580360849007410107a00812060181d00240340003e501d03489100c00c0001c0d9a001c40b00040c400301c50341081850310f0440d8100804920420032b0100d24002d51801400d40340904003004070081c0d540038000001e07101e0070b219021807540844003040030072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170181384 1250 170180134 170180137
    0xb01050d0f0c0b0406030605010908060601080406060b0708090a050d0305030403050c01060f1404050f07210f0c050d05060a060801060f0c120306050f060705030f0a110303070e01020606030d08010b 86
    0x80380961107000d19a4150349802d9a5034000354409400e540c000201040450b4060250000030042400c00080c054a07002c402134441d107000b0001070411440c43c00003410403550b40d204001130b00c841d8a050780c40d1190b40c0b60081981c1d200c9140700b803082455010010740d41c900142c00100191741643c0d07090460311155420344a0343c0000340c0c0415113548401c40480c1c0569021030381001813001060701d403511510b2030248070454202504104089082d0b004000320190808000c121561804150140a100858040009000142c0c2d00300d41c2c00d0900d1201841030780e1000280540a81003a0200040c2d01d0b004100000102148900c1c80440c1030342e00100701c0c0a000d508844d60742111810460300c00c2000795208105040b400f0320100200380d45000030310050510a0300002a0b01c015103070240341100c0c5031200d40d541e014908814940440005065152a01c54034500b21810b0008040f01d8036800c0421010b0204c0200081050040c45038000150b068900050f5060b20030b02d40b42ca83e14506c0e402c00f05841080d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170182634 1250 170181384 170181409
    0x1109070933050426030901050d090b070509100c020f01030c200601080d08150d1a040c0504140412030c02030405030307050708010c1d090601030b1809190b0105 70
    0x3420620112000c0c440101100010140000d42d14541d90701c1c1480702c2c5101c0f0600e81c410089440d0a0001030168082002040314040842400d106859450080300e0700701800310020001c12600c0f0300c030180001c2941000280000d07443c111620070700300341e20080440d942c030415034010398000c1e100806c030790080d4001d074048035846c03038580f03030100e10500b4840312a010042800043c0e8100d40c002d000400c00004240003c9605100f2850100300314204080080c2103550f4001a06100b026100603903820050490051445544004211800c501d80790400091101c450b2041c18095070070548074071240b00e407084100384200e610203845001000f146a049005108210840c400d52001300404a8a5501000a010018896001040c81506003581507007900c000035595002c8c4100e1444156844071141410f8000103000c0e075800c1c50036a00c0ca40100c1c050004000003075040918180c141d0024000b6400e2580b140c035501c0c00711070343e644074022540d030560041c40000c2c2203501001d006000915004903060700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170183884 1250 170182634 170182679
    0x4060204080307050d03150612050a0e0f0d021b180a0e1b120610031106040b0706140c0c0a0f0602070209101404020712030b0d050d0c11090709 63
    0x30309803125601481c551040005459540c010440034041c40d0b410301a90046091150000559918205016280034104040760805948410000380303994102e80c0090400c6040c101141d4052201c2119260bc1d80c42d1848508018051101062401103000542140c1081c2c09481c0e1101b00100d40f1484c8440c01025101c4441141c5800356005921010820284050131070088400504a0001045514510102b80280580041d020040c7c60306089a0b0003003245d406c0b9a8504141c4132400c0065082c1c46503803c0100125000b16881c803e004161f40001c1c07040105a0b00100e40d500c0d03885012a03d802200699000b0358880c544007400244203903221048544107000150600159900080030200c0845489014000c181010810071240b4101c001c24010180c8045181100c285c84000700e00d00c0c40b10000741410344071525040241c84540141000e41e0300001500c41c00032142000900c0148450f00030b551640103c40c1d01d186500c6c050f00381500034200f90710f03201c050a01d08012070f068040ca03110080d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170185134 1250 170183884 170183887
    0x110d090608070f030605030d11100c05030408160503120108192f0a0e061f1b0f050703061a04110301030f080408060f0f090307020a0611010e0f0703021008040b010905040602 76
    0x39254404000c083e1003450f0039221104200603440e1401c0c42c00e14072b80000010142816028103540d40c11004480d00a500001e14a56500300f0301a0725581440520b070041c01071000094012083c44a02c500c0d5050301c1341c54041d980c0d034412200002c58150711030a8080d0070100148031612600081141107200360710101004802c051504c00001d10050080e4082032419000d042001154544001041c20100301c2c100100340c840d1070b1000003440e20700032150003002c1c60741d030071584014841c681c290340c15000c1d401000c9a03a026244c0c500b071000790a4008008024441d250000b41c0341d4506030103401e141c415462080e0b800e6a1a42e111440d241e5140d00d026582d0300400c00001c54400e80a200c404e20401000c0c1c40d1a059040800b0f4008444000426643d001d070001d211400c0142c3e03542014100b10380d202d1400140d000784111000f40102100301d0101c03c640300d1080091826807001c941a0708503030003282e60042c02c05550600351100c440032900100700e00c800b14010b020341c941c2544411b03002801442c005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170186384 1250 170185134 170185139
    0x916030c140d0e010608120304080a0507120905031c020303191b0201021c0207080702040b1f02010e1014010e040f0210050304060518070302040f0902030607110d090608070f0306 78
    0x200554014459164001d0b224843c64440d080e090041000a101c80c03002480d4510a8100107100c80c007000c1c0004158075800144010b8503841841030740c000c1c903003001e500c1500385403c0001030006a654030450303009004d04100d200e2441010315101d00d1090941e005103140d582c420b01400e948161000c0154001079a899402d07240441107071001c000b10041d40c0006075546040c0c494100e0540d8585c4c050248280104681c00c00540e5010958000c00e50546000c1001e00c100340026001c07010210400c6034941d00210030041c215415048034219554103004d40da581c02000700d1010603603002880800c1390740602d000401c0072041d081e00310b0754024020700b96407540f0f5403070742e0000d01c1400c0c0e420701d100c00050004c4240024040140b160982006071141c039680d00340303140c0c1d0103661503e80341c0c40041e10460340c035905030502c04403d0700461246540102a0342d8140382061700a0205108181c90340c44510490344101440303800303843c900c4161121911100041d9540800488048030140d424104058861400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170187634 1250 170186384 170186417
    0x5130f06030807080a0e190b030702070513020d05090c06040e09030c030a1d010c030219020a050603070504031403030601020a0b0406020c010e0c040e0304050d020405180d020a0b060916030c 83
    0xd84043c912031944a6034440c0c402c1001080310024641141c400d0302800800403004400403040c0086480d4219425180d955040e0168145902c2c1e5110390341100340010095201525540240249002d84104100c0c81d1500360710103a880400008490308404104020700c00310352011200360340f20301c0120481b80f81c880543c0030075041d0307044810328001181e02d541c030981d032000c861914102010390070b1030304c2e0b0308034400d0383c6000703643c1e20b00280040c41c107081803000d2005540b0b0b004445805070402501d050f0792030a0130500244564818070080c0d5440f200765010359000c400200840f406640c0c160300400b800d100c1500e0b0701c21361120241080f1400b40d400c0000a0003880c0a00826260b1800c0c6400b4010b40b00381c650a2105a4291500d481c0305908104405d00565548907603101400c0d030180c0f8001016650380e0800e501070000f003580724072179200340f00103c00c00782c0e80020362101c924031580c150095502c0302010301034184801c2d5058000d40a0304407011840c50b00c40d6020440c24550f41c60682d0048002005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170188884 1250 170187634 170187637
    0x110d2a051c02030316050c120d06050303041e050d0b040210050913060303020d0c0b13030e09090304031104020f0703120b04090807170a02101109150d060f05130f060308 74
    0xc1d404003603000401001440003402d0b00307005103c145801d0051410528601943c0c582074804412962038001203482400302810707034071040282001904030f95070740e078551070045580a0200160204100790300e1003c1290705000d101c0c000308aa000d001d009203611241d01700402c00031490410002c0203810f1010008030b03038488504078415010242c0004209086041c0241000801500c0409000181c0703203500000781c0d0813503900d070302502c44190507a480840d45004c590b0010b6006865038040102401d00c0a00754021000b4001c40c1d03c240603541e008900d00f014003041e8050002d4550015000348900703004030703020346075040300b0840c00ca00004450320721500180031a61f81c01c030305517440380f8049211000c00c25042814007141140202003400c1050204009580c0c5541041e0300c00650303140c2d801500310b0420001070322210440244079800c0c94600034040c14442c0c00814680c05000e042400000c0d00080708612031083e10006880f9405001341105605c0c068034012130120300190b0354480c0003021404100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170190134 1250 170188884 170188933
    0x302090d0809042007020d0f02060a0512010801090822031b06021009020306010b0c010204241b0809150d0606030e070f0e04030c050f010c110d2a05 65
    0x90841d40701d000800612040304e004a610a003465950354005290b01240000d46041765812100b040c44500d2030b1502c1c1c50710b030564400c000e400c0300002c80c0708646c2035001000f904841e100b091035050260398031075200e400c2c0c88848202800a207810403014036403420003a450b00e60801d4058030050b10640c0ca41d10f0000c0c0240c1c4030100400101e28600074000540d05200c0085c850200d48004d2100b90b246800094543e941032003040c0345158000f5450130005130039010f440003020a004200110000240e5403141d48600980100c0003d000001c02034820492072003000c10075030402109402c003441c0c0f00c01c1c890740c01c0c904c403030301c2d80c0e080b40610603071003441c445000ea90050400d0780c0c0e003c078242124221080c60301400c0c1d0048540102040b200740a10241c0000c5694000d4041c541000005401e080050a00003402d244200650030a030510640369000303d03070b0707143c2c8078840e0b000c03158001c1000c0011a0f0020414560000020b003040d40001c03d421810b0030317000441e0040c01600c4003000842c290300c0e29042401c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170191384 1250 170190134 170190143
    0x207211403370203150109031a0603190303090b060618040b0402040308030109020702041b0f08060607020910030b09030c1f02040b0a0306030506070809031c06082422120302090d 78
    0x700b08a503d184120f408050f00c0071f0a16105090540d620580c01444421400905c04d0000c0f00141c0590350030442c00c6002504140007030000c10030f0382001000f03040d49260685003c110782c4081840d9003804021289601c00004056440c11105130030400685101070710180e000d5001d00010000c00d40c014000c1d402010707500c00c0103035034100e644148402d4039400351040103040780c2d08145001458019440c0003119901d46041c56140d600d03100060540e01900c04c010303401c40892000c1042d24000e41c9103540c10b907809201e503c1d040b580c980c0c083d581d880c410361141d881e494100460031199401c589002e029400380d00e1401504044e1034020040c101c0e000140300d08000307601c1f05820000d21509000c00ca41180541c42c201c0d0040c5841c4c40380c0c50303480c07042400d44101c900c02c00d401e204002e1502d501c404041c2640b102650a1f01011900c0d42d032130744030003144041540c102c0002180304185100090700c4503406402400d41051800e0310f90002484140d0a0501419000c004042450362a004c0e80c1408074480c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170192634 1250 170191384 170191387
    0x803060d050f1209041b0c03030c0c0c06080a15060f050702210303180601060504140f040c021f0c0206010515090306070c03110a021e01050d02072114033702 69
    0x113203800c120075501036420100c0d50030b4041106c1101e1a921080e049009909814003107094185c290040355081c07040c5202a01100a001340800c10720380c090b2031203000300308808050000c240e908440080080f030501c0b900d004108042e0389003d0047c015005800b40c140010040118551003000b11845a140d40b200700e030040d003002040154520b240503141395220b002400030b08003581441000b410301d1107140a000145103c800c003200039562141c1d000440d44030041c2c414040e29030181c8000c4e680358020780d0b04003519030048017910030b203000c14410300711002c00b19401070109910300400c2c461080100901c0c640c01090410101c5400d44040107464003d41042d0f440c140355a0701820300821210310382c44c0a11090b00308502800142c3d4a03001200071104503410042c442001c0c0303500585552242c0c1e011124010f001180c1003040c415000e0400a8880414181c034101ea5000402203400d4039048817010840b280600206000c8100c5140d6800c0c0702003130440c460180c2c0404c2503d10074000c8000c8244198540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170193884 1250 170192634 170192647
    0xb0103122a032006060315011805130c03051f050c0f070309091503170c060a0e070e01030f02030f071503050411120a031e0c11030a140a0507120803060d050f12 70
    0x40c1080341e0f030441c7d49800b40b10240f40d414402d8001040c0d0402250281c01611040450003482982c00c001030b44d40d84c0020f181030110b6070792603d079460307520300340c448003c04520b0840307814481d10301e00906210362107601115181c9202d004c03401c030207500850320540402c80f485a001c81c03000e8240c401c0c060f01c5080e003c5c4402c00c05145207451509903030240310f0682d07861030a208141c1e405a00241c00d40e00906000e10110b80c118041c40e80a24051880d444422122803143c0004180a6600d000040e114020350039500b00c51300c034181c095074401c43e47c03051a030108901d410080d805842540042d4126100e00586c4802042c90b0000500d0082d420b45403541980140b90302d1810180c012f02c0014010841c0c5404100c00103d8480141000000082c040d00342500d150410a41c2e23903080c840e14880c0d590024500986002c4058000d58402c1c07856030445181c03007100c8010a000080c81c041c030703140f26840903269281d50b64400502c900d1015405085595101d191f00d01c3c43d60140920009008010f0700710810740319039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170195134 1250 170193884 170193889
    0x150b04081f060608070c0204151e0b0c2806020c030a0806041a060309012703030b06280309051e150c030718120b0103122a03200606 58
    0x1021001e5042071185412810000b684c1c00100b490390240443c2049080d00c00c040c000b040152803440f10140003000b00b14004101015144c94014030780c00740820007403005841c1c03036107050786102d0185195115844030b00405e600c01d001005403903110301e1045004131a03030f00c01c0e96620142d0b040349404405907000803070505512607001305500d03071124040301c0c00c3c030001c5012901c40d950b4a06c08585c280c002e05002000413100c1200350482c000300004042069080307032000d0061a4440b94010301100000e0030044c0c0340ca410f1402c1c1c000d075451403d1148241c84aa014a510311804030301e20718901c818592207001e40804900240b10b06040703241c00081c2045400f07894040541000341e441000d03240164900188616025200190703940300200e0300b881a191291400300140520050303008901440c0c07039013400c600300403200d21500c2c1281e110b00c0b040d03090f01072442d0b030664001c68190400c0d03a4046210400716000c4001d1218503034818020f00b08000e0b0741c01404a103084010740340d440000305500c0391043c8000f90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170196384 1250 170195134 170195173
    0x70501021218070f062706020a02090f010807050402090102190b0105100201090b040b06151c140402010e1003060b04030c05120a0c05220905060613090b040204150b0408 74
    0x16120b08001d4280c0509000030b404080b081406000300300488925550b0f905e900d00c0d00403d0100000840124a40fa030700c1400941c1d40d0f00f5403404034052000f8502140c031101054481c1410b885182c2c0c058484103040100344070094005c0b54000c3c0c114170480004501c000d042031240c0c6403540c000d030041c003503030341c10b0a0030710490040300c0e1041411603140c66054030105000306c6031207800a0380140452507640390100014aa6114890102c41c0d04c03030009800c40f043c1d500350002c4050a054080d00b400a002c8150701702480310000c03240030303000c030b0b80f0781420403640d1900005e0140010228100080d5250315400d00e40e60581068104858406090106004a10384218003220448c0c00f43e004024200f1a03a030f03101c915214512807540240010540504081e038401000d140c52a42c3c9101046030391814144641e6036442520100d004a580002c82961320b07940c0d010345500d0307503000007841019840d01d5003444014211043d824156900600c404200c42624000030700040403514001c0c40725822200051040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170197634 1250 170196384 170196421
    0x8030a090302010b0a12060504080c06130308131e060f020a1808030906120601140c0a11010809152a03011503060e06090405010f02130f081605090702030705010212 72
    0x1034401017805c018072a980e00c01140e80715440f0b1030101c1c0c142c60b140303003c0034640603c640150701d500500d8200301d049201c881500c0004e81c029074950b1100d807074860008242c102920030240c0142407a00641400040b00710400c141c0305d201c0c000011307001e40000000350498010501c1c00000604582c185c00d40070f0044e614004c050480302c400385150070f45910005100b40710700039249104220410006405a01500320007541400200c00a582c4000508000b03850b207080301d20407291080c90500300f40c25540f24140d000e01c41e42d44503008101190441000c1400c03250002d01c0440010164800d824614048035410f4030081440300c0c6080d1a54101441c100584c2c14000e80642010310304101041124810100140c020350103965903e007549980c14124098144128001101d40c000a081c4008803407040d41a000c40301090140d0f000e15498803541500c80c008654851a404001407052040749001c0038456004810342c01200c0c60002c2030f0344e40500ba40c010070310f24194440e41c2d90402071580c10180c0b10919 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170198884 1250 170197634 170197639
    0x2071a0c040f0e01080606100c0605040b18060603060604150f0617010b090319030c0209090c030c030c0f04050603031204060b12011b05090402070203030c010f180c0b030601030908030a090302010b 86
    0x240f940c106104165a03400050a040c419807118054102c3c0c035029201c0303440b80940002d001d00a515080c01c0080c1c8115003610720301c1102d41c41c021080081180070800718000c3c1c000501501c050740f10b20017004041c10207c036001c1d20807020320000145050302040e2000041c4915105c0803004001c4190354812010140d0004110400410100e04075540c0811000e096003480da1817013010b0021810301325441c200c0080000d400884d00011321200745c0c00000e055440350412001c844440e41c5c01810306485940502400350860744441e1b447ca520301d410b8210f0355202d400a4200d90410800c1640f15503000800e50701525059030301c8a130040700d0305040c0d40d5400c1404100e0000e000070016400b5400700350b11103003092401c0280104200c1c8161743c46404039a01550000c00712a00e40604441070360080c40c00300f41d0304002038075240b00b84148007480071400610b2a08601a00d1210346082d5550f059940000c100310704050340d4190f25800145141d0207107000c2c194001000074203105505e4042d0840c1c2c4940e800a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170200134 1250 170198884 170198909
    0x4020d051f03030504050103020f12090106080606040b0d122105010e0c0703080a2409151706010e0601020a02090103050a0c0501030501180908040801060e04030905090c0d02071a0c040f 81
    0xb0100350444201d0b402c1303402c02c0c41d0040c0d031041240100e44850252080054184040c20107201c0040c8054000700180ca4404c016252103841b650300300000c50b1902140d20350449051103e5001040900c12071599500c0581043c14030640389010341064004c41030304c100507065503a4014040070a820400941c440c07030012500e4900702e0f554601809240d00100f8140c5615100c52007901c20290300219012111030284e1345610307558a903071951002d41a400440310901c059008001043c0006826042e02e40d410b0f080989000d9003046004655507034028075441c1944a010a41d03001600e8902d9010300a41c024005841c20b04c21601d05a01a143da95110504141c04c1400500c0440d1000c0401580303030102c0200000c04040c2c520b4804110300403944a00115440d10400043d8000c0c001c42d6940720b5446070b910781034030b01c0d12841040580013003643c1440340c0c0c0c0000e100c003071210760b220340c02400e0b00e038010305111340004c050a1028a40c6501101c0f144500c2c800030604004c468407200ca1500503000c0c610016 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170201384 1250 170200134 170200139
    0xc02010c060207020a030503131811070206070302070513061d04150c020a060903080718180b13090309090c0504140108100906090506120a17090f04020d051f 69
    0x8200d8600368a0140400354002541e004564503012524019a40141074a45030b0644213103c200044d42031182040d54481411a041c0b245914456800d00005a2020342d09080d010b40078040325820140d02241035220717800c00031a8a0790b42215521503e04e5042010030b9190030003000501541c0903040c0d10400d161401705110005440541c001e52403c4008400511040c5180040b440c000c009100a003001b03143c02408011325500c00c000c02c0c86400141c80c1d180060100700f1485900580034422041c40549510030f1450106203500200308032403008020001c3c510101490320304449020700c040340403403180c440c200820384030340c02042c455030300b81d00303000742030500d0045080c4070203003043c0045041001074400a044004080014405882d02500c20045240c5510400004020a0711b0092283c2d00e07400c10b4801e0703864000384620000750301400d000c80e503009203082005035801c004001c40c2d001e8030341c0f0901e0000f9180c40c8050b140010500c440031440f42442080c82006402c3ca42c2d1540183e0300c900c03400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170202634 1250 170201384 170201387
    0x60f020606090a02130b07050705010f091a0a030b1c020406090b09060d031e0801060e060304080a0e03070b0a09090e030903120c19050a050d020c03070317040e040f060c0c0201 77
    0x44a500a86600b8050380e42e100401d8624114011764001c01c24144004c990b0b41c041c840c0000d141401d1300e500303884400058058100c181c030b01c1415403144402c003103400014212a4840c1e0009820f01c80d0381d5040118400001324002244d021880980380c80300044e42c03510009500d4a401180001c00c01c0440030448611464003207940c00300010003603800381840340420b404151054081c1c00c4420700707004503000c03980c889410003403207200203104403000151180312070704403490a030341240d00482d4881a07940ca01484a90252400e030b071440b003426418020600002402c0a065005101003070190780c50300360050a003403c0c0000c6450780441e19085078410301c21480580c030001100c004100603000c2c0d01e42c070344034a001c29500e4000306200324454a0200c1c20458100000003443c0519244504141e920048030211300702c0c3e503280d000303d0b8158568844202000440d0200080315080d8200c038081c2450706484100303215210031f040c0c1d012548c03000c0012003401440f0040c031400190016030f140c27040b03409c0e00d131340c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170203884 1250 170202634 170202649
    0x50601050909130c030b091002120414071a04170d0516060605151c090b1603141015020c030304030b060f04050103080903010605010306030515190213060f020606 71
    0xd407900034000480451084600c0035240b0042030350001c000a0383e140c491804080b11601078a041c40310b40f1400c00ca10410010500942d08400d42c041a21012a0b456071101d0728542d4011620949500030031030b010402c0c017212040181485128403020303a841c2c0c43c104c100030241c1000c1000703507569042a00307841306641e805002c961002403e1020204500d00d5804c014004011780da0280d40d0100301c1c401c071440c40e8103c41010f4640b035071061308c9980c4138104042e903042c1031381c01d0941c00070803501c0145c000450a8010080f1410b1860051a00058042a01c44400f210740c40665000440451b0038804005c07504206901010402c0c0910103403044165410100741e503409180401040e40c0603920001c1e003103403960482a15034905c0204103100780e5a4900b0842d41036480042d20740d00a50815402082d2540680518801c807540b0000415041c3d441c0d000501880f00003800865503054500383e40100c0c1c2d1510300250022800c8200c081804910301000a020702003010003080c00e64004031b00300840d583d540c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170205134 1250 170203884 170203897
    0x30c03010b25050109030906080610110102070f110f0105070503040909020114120609060a08150c070507060908010609050c0a0c0212010c03020702120303011505090a0e0a0e0105060405060105 84
    0x1000701d0b440740c004040700d40140b101000c0c10340104100095100621505401840f1828000e44031000025210081210f120790100c03107198000000d4140308108034400c03000c0c0113551440000042c20322080f07940301e130190008004203481010050807052924507040340c08443c1e01e5001d003401c0749403070074035239600c0c0d180d00661040d00800c3e6a2152804156402a4602101140b055034001d82e0b403214210001620711003664200d001e002c1150000e41c103400d0100d110790030744003000000c02303100c1e4400741d00490480006100c000e0841341480b8080003c0e00801900c80640b40c2c54840501301340c2092006403c4611550050341c0319400c00c01445009804d810484a8000840ca81100c40a02d903001140504c400220205015880e000080342010751641c050410b15208643c1070f0284900004020f41c2c03400280249510313903034405042d411044c003400c0201341100024002200c102e03540c020b03004c035000d8103c034200e0f503683d190000074031840403e202d1250300c000210303004c12a40c03d00c0b40c0024414010a03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170206384 1250 170205134 170205149
    0x9070b071a13020909010c0908070518040c0e040803010e0603150708071110060f091109120c0901240206010b1c06050301020d061a0f16020120160605030c0301 70
    0x7034000c01c0c00300b660420080c40031600036218030f900f07042010406000300084500c40000841a41001c0303030320440451048100c65004150700440290010114407111000d00110f5100700e00e80000150b48141c44403141c0b0a038003c151840d00c1c1d43c9400e00c0f425110600521041c030940000b1036080400807000c0d00250030003520f1400e40c1c0075655400040d5094110600c06403a68482c48542e6030540c0350580007031054403241c44105161960b40e04201d000d40d41204075091103540140b00041d0242001000110904080b10480e181c84400e6804a807624034280c003c1b1709007182c0a072a8203116211384102c045990580d00c0204050743c034088040050380284440d0a40078201402221102c0c4425000034003e0b10f0002c008558811005e03a08500904280c031503050020055800c180b810f0007030b802500e80c104a4400308918000e031400304000f400b42d01d6001203060140950403011306002d40c0c10940c1d44046050000c100100440e03c240811865075031200081000c204104881c0b0590b83c41030740e04442c0c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170207634 1250 170206384 170206433
    0x905070303030e10092d110d0507031205071e0b04060c090801110301030b0912070305090406090f140a0b010c02040906091502031014010c02280e09070b07 68
    0x26a081c60300340101c0d5641034107420b0504030b0349000d215101500c03000c8400344030541d012544113a40866202d511304c0f42c0142041c1e4061010304040d040862320070000c14400c00580780341a880340c2e52080111182d010000c00a00c1c0451840f0400043c150b4441d804a1061036001c402c01180e5145550444002c0c0003c1410f6201c030a550740a0340100648c8020b0a0081d0080c408290391274220300b981e8209101c241ca0601000c0081448290b011602d1200c2d8680e4080d01840e24060740c4090b00c440c1e20801c8902e4100c1c1d40d55500207070304041e91180c400700182d1440c012840114065000c0c04082010b4507600c05d1a140c1680b602007607800034650341d02141d0658001c208142c090801c0401003440b044098141c20522042d0070700035a080d401148030710354060521020715210040d2a90040207072031910f02096414413450090710302410030018241c46080c9c881301140080e030080c030045003e50300c914031103121101840401c1c00240706074006020003a411900781007443e280d03003046a68100c80301d43c14180d2b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170208884 1250 170207634 170207651
    0xa05060414042a0e04110c070e04020118091b023408060412180308070b180f01090309080303040c05120c0d230c0a1404020d0f020a0909090507030303 66
    0x80d842d40d0581e10308012001c02e400350f00303c5500680019032200076144242d02d041902142c0104850950302d80d00c02900c018603507142070a40c020380d1854090401d9042c0004034480b92040c1b503401002e000030302505c440120f04800034001c04030100c1424104201550402680030401e00a03d000810300c0450081c150300b41a140d00036205280d03181608080b44c1405070b0000c11080c44420b035048a00c1c0041d56460f03543d4114200c6042209140c54000100140002c100200200c1e48602078240c01020242c0c0d0320202c00355002d032491501801e041c400750242d44400d2a40d00707240c1c10a81c180e00030610300c000340d451407401e03940b03e400d01d140c18015540714030002c0102844010040250b02107440000e0032001220350a42043c540c2004a00b0342020201981d1514a100030000302d42da041000001d0311500c0c072103040100010b1900303c00310550390829424003440c04070283c18000c018810b12290720050703440380c403004020b207494903903004004500d00706003802c000100001251401c40b40c041c50005045039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170210134 1250 170208884 170208911
    0x305031606093201020c0309060708160c170c03030d0c0908070e0402090c091323010e070305091207060c09030b0901060f090c02030d050615030c04050a0506041404 72
    0x121400042c040760542c664540d034103070b10321010340118001c1c9032021003c656844011402c3c2c1c0309040104c2142e82041c00025554200600684105445440d1050a0a49080c000110103034110025560704807003d20400000c0480e008100103003e0b0480a05410f079612400b10340c0e288600102d01d00200e03901d4085803581071090320702402500148064456142d611002488500402d8809a1050312001c0214020000440440708c142c800540036295030340c46100c20f04001c103080d2400700e00984260b07030003800030240025014003030080f0782e0400b001030800c01e60003011100020040a2103500c10300c041d001c41030924003950642d07544480082003a03a4110070032908480d20380e000a020302401d03001d00c0004501074001a0070341368500d07010568550768015020a50700b4008611016170000c108090090b03500360042540200094103800d031007540c4100303c0346d09034006c031220341081d076001c02c05001d5890135a0448004010840d801800c05040c084501e07002c0010b10b04040c4120b80c0e0300e4805d0400d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170211384 1250 170210134 170210141
    0x60f01050c0d0804021003050103032c0324070206010f03080c0304050904141623150309060f1605040915030203160503120f04120f060f0b01020d02070305031606 71
    0x3280e0400c203661641203810800343c01182d05035400c0b8455030b000c49160403ca8480c0c81624100d81c3c250b903031182068400b81d00700c1250407442690500d44a901c5442020980701001030302030003800481a010300307034500004140ca40f18007030408011500700c04010040c8060721100b24050707903006409130f543c40050800e8645988641c0c0c0c0aa500200c0110400c41400f40701c1c003e140b603184030034091310640049800b035201c1021541c06420606601c0d048810702c500680704189084003005070060f20849005198124590401c43d03a035601503000508000121100c1100940c001108140792036400c039115074090454000ca0060401d01991400300211181c4c0b44403406001f543c02500761100714642042c0c2c0c072520051070180034064458900030945903040841180d41c800c0b00729580f24101403c155020074000f0384040241c0b044440440e515001c10711900c940b5809400103000000d481c40560006810900c00414200554100c003504002043c0040100d485802c05214003a008004625049008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170212634 1250 170211384 170211397
    0x5010c0b0702030c1c1206050907030b030f03040f080d05040e070309210320161106040b040905040201140307021506011b050c030f070f05011d090a06050906030a0308060f0105 77
    0x764401d90301c08a01e405d498102c101c0c1d8012071992010600340b410412201501d07200d101d0700da00104900000751350f851003607201401da180d0060a5420071103450202910f141c05c250000302291407142010010850304200700d0404480b42c0c18204c3c2401d14040004d0700c00c00005014106064852118000b0000e11103260b43e0010038007003510044c2102620014018070720904809040c0030565001c119000034141503411034019940603132203240c02603a80d65503580003c0a1250001001e110104001c04000e0160002d42007040700000c20345001d000040071f074030f41c5880005000f0410014414203990100d581000c00c0c5040007109002d88440700101d56100f402c034203008151300303100121000c006000c00c2a2151541c02c80c1107801503c20a80e2250302e0f01d02138462881292009102046a54007420210350313440190074241341140034000120780381c4032049490a903c50360ba06401e00540c40c0030854150003540c2a00140417801c00355a0103001d16402a003d60302c00ca070702000b045056072040c8201c034032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170213884 1250 170212634 170212657
    0xb0117060105030604470307051003060506041401030507050909040204050403230409320a02130b071209051003020309010b1801030c050103020f0d09051002040b04030c0504020405010c0b070203 85
    0x20f031381d50070200c86510030b203200c005001e800480003911006d18100142c52100968000d000e86401c0b407611003080a01c0401c092100b00349502d42030002016500c400c00f600c0200603040341084444800f500040c21680000c2822040c0070301441100c5044e12503601280c0d0184d030642e80003a5544480c141a0b507034408a010281040400c00c1e41d01c142c0003010030140089a104041c203001003044407885403005880322449000707d0fa0720414107030091001203082604241170440c01407a103c2d0070340d80b070022420030b600303e240743d420300003225030030040c0068115070a20b00c40d140c0102e48a0038000025000c80c000942e4200301600440410940f000c00c0d800020300300b100034a0400550501560203400007002d1006480c40316041000003010b500900895161f0100d4810b440d1409801c00700190040481400c10307501c40c4a22120f00584103003610080010303240f1440220b44840c42c6162040d03241150b03400450065005000c100201c2c2d800951402d034499000081426540e80c50004134074500800440d1b11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170215134 1250 170213884 170213921
    0x60117060c1620061303050c0d020f2103070c060225062a050c0913031205041e0b09070603061202060912060a020304020f03010b010e060c01140a0506040b0117060105030604 76
    0x900c5d41380c00b940c0d24000c0724481c80030780da07055940d01d0811840c841d0b84c0e08003942000000c11110744030700c4c02c0b4811140c200d140c501c0c40d000749156109003a01c0e6070080441100c42d044400b00500040340c04120344810005102c0f0034004454201c403000c650021036129007000e0002c24841001c00c5400010400021402c00084d520549190f040081d82e95148124640c095000d03074001c58030f000803021154404a4241e19400d200c100c0039043d150080c03e0080068903281c2c004807140000e0300042c4000201540601340740c19140c08d15090003400d101c220b034440320034545030441c20855111a1809802419011608240c41d20f2040d40800d0301c49400b800348010501a1108000e03040c03c40e1b901441c040c500950310646900c003d14240750803200400d801c607010130f03076113080410145052402485510803d400210302d00c0119603181891400c240d42005c4440d885008014090400d4400e6442a0303a09180c0030800c20303103141d600b1030303011005842c80e0b0400800000049845c3c54a811131361141000c2850715 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170216384 1250 170215134 170215147
    0x3020d0f090e0c04090b09010b070b0c120a050403021b0a17030f0c030414010e06030a051b070605040212121801050403020d08120108120d02031008060117060c162006 73
    0x3000c40d84c00340c05108000c2c1c1c0b900281000310300f00b01403042c1c1a501c01207603461a0007801c1c2c1303a00000f01401002042e00c3d510801c101080f0045055803240580800000410541000c0ca0003a043c4009039881c0181a50f03e1424a075640c0e65000a00b411070300c0d10340307107441240403c005031411403041040f00201003070300141500003c40c0010060048403a415101a03181ea11100115a203100900d41c09a1040b01840841c0d03149200307501c41500040507855a080001e4480103c2c02290406d5100fa40d0f00c0c0c1d43d500c104412350401004d49401c251142e40680140c03000c01c1d0755003242d40030300c4000b40c461011020240181fa402a8102c030f0182d5001441408101040c0c47d00d184258083c5030541d114500752000081d962000045403a000d21040703400904090107048454003e400c000c0031381c221783e41d034503800150f4841c09010142c064894140840d09079002d82c001e0300c4c070303050029000003170b07508040110120b600003100b000448168000c04809640206180c0c1404182203003002d507a119000181d032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170217634 1250 170216384 170216401
    0x90111120a02060108011404080711191701110a09120510050412020d031424040510052106061c0c17010e0102120406020702030a08120a050f0403020d0f090e 69
    0x203843c101c5840f0030003070190940c9081e200345000808e036070003409070f0720504c080000140a480d00b0f40660754040c10802c1c40d03401c0c01c1c01c1c3e0707890030800340d0040c0040240400450850b0400707014007405050344507031451502100c13241c02000701000380300303101c00500c00e04180400c01006102d19240010604014000d0341018200750903e00400705075240075115010b950001c0500902410038245250810541507603120304904001c0c03d074003943c542140403503100c0429956901d07c16280202416610f104859041c14140b00c1c90100f18489024090001440f181810000180c56940b000c0d007502c042c0b4111102220020042045c00e07030050100c0e100c01400b040d080c14100703003480c132064200004c0c841200707099603081c00c0703200c1c102031034402c0b0f0b501c0320004020a02d00c4c2c004018192000e412603002240584800025030031102000000d42d504a041c481c15a0250145c01d4015a0920244040c1d041c1941c0103995441c0b10303c080c1c170500c1900f0710345454490044841c0310041140782c6140d030031442c04403c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170218884 1250 170217634 170217643
    0x9120304171e06040515090309031002030403180f05040c0c020607050606150403051009020105040e0c0405011e0806090415090c030605090115031b03060c08060f030f03090111120a02 80
    0x51462800c200c01c06010755440c00003d900d4042c68000c1c000c4c10080d0f01d00095001c20400c020141007003488100407070041a07d00700300105003240c003071200603128142864004d01452107050040c8500e00c00301c1c828450345e8004188442160012200000c01e60070318032040d100d00e000c1c01c40107580140042354110510002003140c501c60102121441c80d0710850f50203505050080f40805480356214002145043c1800e0703201070450344c01410100d080a642d00010000f036036041300c1100014a02103010080742d6081071081d007043e61070000210100c00409001000c1e810000c250500c038143c814041341c140b0542000800300c030704001100b407014080a0510604905607840100c0780c00e8582000204982018410390032070341c0f42040f5070401185152150703224074405031403107100c140000600000241103841489500c10720323a20741e03105e40d182c00c1003013000f80c0d034400c4405e50190300511414402410302000700c502c0080c003401d1210820040d90411890102c941e4000b201d01c0c040094903940c00c40c2c0028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170220134 1250 170218884 170218903
    0x6120209060312091e0405100f050312030604150308030c07051009050c06070c0816050102010b0f060a0c06020403020a03060e0601060f0807051b0d030e0d0309080912030417 76
    0x100e6080903500c442091550b81c540120702c070142a1824480c9030036500c1c08000d6589400307181d0f0f5038550782600700c0340060104d4200382e84c88224441c511004100a501d211441002008110080c1c0002c0701d01a10380752451100070401440f8a03541d241c0e040721040140010300c003464201207840c1c4c903450602d00402d0070f94490002510711f40300710300f000104000c041c051a002c8941c4400a400d40c1c411050a02280d40c00189040710b8000e000c1c1e6020818a2041010007001282c611000410614140000e421512140001402411009201c1c1d81540300d05d421126040c1c618902a0710a0350715003000002401a80c1000b0740c13100c4100400018010130390001021000400b09680d05a640c4406c02c0e96503c410108141c007140c0ea1000040100e40200080c00c40f503c01184003a900c690109441c1b8104002d415840300804c0e40c980d0040c01903e000c02c462582440541010450340800c5d031600302040c0181c913a20791007415040100300d02c0a000303200b52002440740c001943d103080502d08445803596001e5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170221384 1250 170220134 170220139
    0x60518070608072c100212072105130506250c06170f010b0d090b070c0501050a0c050d0c0302090d1103010b101b261c0207052a04061202 60
    0x9080b203900008541203104d1249007450107600412500d403061101004440310640150300600d1801d0032945c41100c0105001d0b0f200c2c82c1c1100d042010000102c1411844a00d1003007008400d100d0740064501d200e00f08815a2400c032402c680312081b107000c07a580c0c3c8030342c4040110b0100ca000a10300c1042860000001616002e864003a81c041c030705180c4c200c0c500401c80d000c0410f02c9010340100000f2210200502300164010b8000c5280801c075160782d0300c0c106068881e02c0000d10318141d400e041c4142881525000140c0040521004007202e0f0014902d0041101d42d040259076050800c0d1458041d81c101c8110b2000030702240040165170034190501807504d0750b250300075400c042c1042c00e1460b1101c880c6c8000080e5443c1ca01c03544440700d4040300c103c42c80c6c8000f204e0303c000c811207009403810500181e104c550110341c039180d41c443ea0481d110001100111410240500510000001a2010400040c6030795032500060b610008a000600b80010312503110f0b8201d443e04002240c101a00100010314038000e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170222634 1250 170221384 170221397
    0x504050f01110a030305041a04030c0203012906090301140907030614010509040807051e010b011b05060601051305040609060305060721020d09080c0a051c020a06051807060807 77
    0x100640c2c59820510440c01c4540100341c06000081c00383c0c2c802d58000e40910800681d045000074941c44500083d942600882c42e4589040d00310b141c240140782104007810b1040140080c1c10120320842c1e41000001e9208110110f900103968900354010485803048043d00c2266041804005490380e80601080c0c0781c007070131300001060305110400643d040340e80241204903a5034550b2941c2c1d4040e0050b0310115120301405041040e190012188051810300c3c20000282014682002426185046c4150201480388075281c1e0040b41d00440c805a2104017800c29a50b1030a014160341c3e0034079a140c001c00d80c030624209001c03070f907001141c0c4a807041c0c0384150201c0340c80341c83e100720945908a80c0c0c121001e01c4991900c1c24458909140c01403c0c100c550300c03201290941c107558801125800c030300d00080c40343d0f02880c84002808010000360344000448100102e40c0e2010260080d140d500d00b00e40a00013a448001051140118258444242601c402078a042640f030b99030003840d0748020359078100043c0c0c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170223884 1250 170222634 170222659
    0x603240608062409091302030a060203100e04080304020f0102030c011b090602011505040b01020a060f2003040f0602031015090e010605040f1206270203120a050706050603030d020a050405 82
    0x20b40d09240e22442c000f0065050030400c0d0181001345401c0e00400b038a100404000003d001038804004007110a803054401503100d2030480340e1062010710341e60000820031459010b11002c143c900c0d08503034206405590100d5035130080001030340355214940c103680c025880d05030071a00704010041d0701051040036070f585000080e0350b11400c80c260f420100c414031514ae0358a40030051490598070801d2410010700583d960750400380c41703002c11660020481079415032200c030800da0070429800c1c14a4a0400100d8103800c50800d0382720010300d03a41c01c002c002e280950000110b2025100a000407006201c1c904800e003103600a40c500a0100c1d103103204d49071480d40759800111300140140c0c01d072819030f403203400005400c0e850940401003423010400d0a98445603241110580340070042c13801240ca060140200324092013502c11301d4039069140104801000e0103218001005a015045038a11904a14003041d283c4070400000d007188215840c080d602d80c800102c0311603483d003180241c01203d0b81100d003a80d6810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170225134 1250 170223884 170223919
    0x30210030204051e13020a030501080c04230c252006071b050a1509080102090d0f05070504021804050c0306010212180d03050405040f090507060324060806 68
    0x24502501307034840244984e20640c0d80100200c28403d00c4003d002e21100c9044010030310072a8420521840000e803a40c0c0103111a40c010025043e60010942d0f0400142d0042250590004150450b0351207100c3d402c00414525032070301013910f00c0a5854071000690416100c00340c03210400400040f03682907405246104070b401100045546070303c01604e0b41e07207001003a503a0644c08d098903c1d050820300508040c0412151034104054002c0c0c1480d121291498000c130314058004002c03031344041800d1307004010307099250715060400c0a00c00d40c0044005030603030452800a05004058001070381251000c039092a01d4045280e2a9081380d2064800b0009612605011845444200e0300c160140c0c2c4000c50f02c00060800400900341c034103a071034512101034800c1000403075000940f9003c1d00007071000300302440503280c84c0c400c0c0c01014210f40310402140c0760640c0c940340c4860080c4a4174041c0b6645001c2d18401c03c46500c03090001078075a03a4040001515088080d0a03c1c0b81524902e001d8501d80d0305080441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170226384 1250 170225134 170225137
    0x60c05160f050906031501090b0406150806031605010516050309090c211b090312040e0109110a0e0111030f040f030308060d0305030f060109050904030206090d020a2a05090406060302100302 83
    0x4401401b256180c8c01c2c0f81d500405090781b61b000c140c1080c2e8a02d400900c1039402c04000110402c01e0b03640a00b24109030341003514181c40c2d1080070454890315a8100300c2c607a000303402c031001e00c02d4035000c03a12840d9440c01e00c0c40c1035004d413078200c0f5000040c0004002d503075100c11000300343c04518043e000c0d001008090300b01c441d02c10219014030003c002800f150b607962041d4000340c120180002d04455490104c4626114141c004d94084180b2080072401404006181c0c003c0b000100324191003542844c6450000400403c0e0307003840181400050140300000d240140102c0705240540740340243d0f9a90f4440301e04000341d403184000d500240001c00451451301d0700c5208003000d181c040d0307192410360b2110110342d189220b02410182c140034488900041c00c2e16040151481240640c0203000d0714604030300103504001e42d807400c3ca42103412250340c1a001888401886040301440010202e0072000d128000d00c04103445d401c0f041d40b00d00208100001c0290540050056a109840085220901b410260160f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170227634 1250 170226384 170226403
    0xd03060803040b031308040305030304020102010f0b010f14090324010501090506030a0f06030b0711160807090e0a02030f07081002030402060711181003030809070609060c05160f05090603 82
    0x89030800c110070404203c1d0b803400780d500440c1112442103240e82e55600d0300f06552056004a601c1c2d00040b0800080d5070b028415001d50030b08a440901c200842040020101a1001070f0f80c0d041c0b10140c0788d00c00e0541c4115041e1a030110000d81100d540c000005e20394810a90b402c2c0d24945101c0c40c80d0000b141d5544202510012544040c21690543c0c482c1c0b10503038041e120040744450010b81d5002d0000108100d4891a80501890740310800385000b507840003030130944411803d04054604003010000d07103030700043e00300403548103200000302d040c0050007645c04e01c560560040e5040c0300d00844080101008200c1d2800c960a03e8111003042c0c14441e030180a9000c111006580030038140004804a480101c0c5000c41100c010401d0103031340510144469619025258005c5e41561070000b48105038201d84c01c540c1040305440242403041c5000c10041c00f4542502901082015030b510400421800b04050b164071820507411142e810f4541e550700c0d105c5070f5903220311032180c0203180c04074800c0e0a022580180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170228884 1250 170227634 170227649
    0x151a040503071a070602031009051303120e0f030f0a110a020a0b07052401080706050304120f050706020c010f050c07050a02190905091c0f080f040606031a07020d0306 73
    0x81146040c00c044200c40d0607640c0c00000f0001001540b0020390b0500c002c511581c4581c000e0300c44941031203682c3c0200c4000810740711542c0d48482c0e0800121340c0160701003149403150130002c60040c0000c1c4251342042c810340d800c514036100204203040c44001060141841018030b030b58048020b07918192466031150346a074069000704000380180f21160001000723045090260b03003114a061003440010f010107240a81e40d2940d415004010b000303401091081000600d828070b0554107500301a2581c00c903c142114048050004030307860358411034040c00c00d4a035403d400990441d100e81035500c0310750180c40c095009080c2c40d443c0900042e1400d40740170507a0029a0030500403e410a015420b01c60700d03400781403102d800c000b003803840000e4002150180a00c5110320401600641c100400c6e000c5903503090b100e03588103101581d0011100e40b80d02c0326500c0e43c40303090b01c1d03214611600c840c18408001d0082da0009003e170540c1e880c18454158240000e24001d00441d0b00302d4000d0440c5040c00c40c1105c070140250030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170230134 1250 170228884 170228893
    0x1080708040605100e0403030b03070518150103090515090106060f050a0e0325030506060d051b0409120f020606090c090d020406051807030e0d120203070c020301151a040503 76
    0x203002c12603d03403000764041c2c0c40940c3c1001660702c1c0d058550392624202c0e405c0300040d0312802c464840741030a010700c00003020309075044164541c07a5450070300c11a000801c40c50711103801042c8145503a04c40d410210741070350044117640041500c9d01200c001c804088640103100d41c00c01000050f80d51090b221078000902e990b071040d0030302139043e00488280118070300b01c50385031286c0748500c0b80019801c12056200809944040c002510303500d802c0e070610f18000e200170321036480e5604020200304040b954004101003134107031041351441640010700801846501500501000558034126904480f440840c07450a07000c03078615a480c4010014006000c03504030702100700902c00900903081241c852003415100400c003042458a0f03401240300f050351107400c3d00754122442d0a010348a50180704100c42e10501402030704c0070000110000d8869502a45143d860982c000700160800d4861002c1240d4a9401802800741d540210440d0507a10818042d291b94000108114105210413004407002c8550107400740 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170231384 1250 170230134 170230141
    0x12040b0717041a030717011203091a1903090c030c0509060409050d0c050c0904050c01110d1b060b031f110c06040b09120307051905120402060f0403080d0c020c01080708 74
    0x15036107604068243d00c06c0c401e50000da00c505041c001c411074007a10074440c1445164503075060060402445910841c44c07040f0f041083d190800209046600700502120a44281100c80350110010a60307000c02404850a840011040060305401902110012602206952121003c000032580d036440d00422903840f414000500900403400329000078005d00503519607803155000301344441d004403000c9440340c000d43d4000d00b00c2d41c4c0019002521700c0140008007020844031034050104032007015076202c0214450340c540100803458200c00d607400006020389410140e8901c00418000c41781c0490364413942001d4070050200465010b0b07900000b10340c4001d2141e07499617212030403424409001d1034a0ba01034100194006c42d48a4021070051030f0369642d16a0340c01018002d4103480c250310f1407520030010100b01c95001c080704040781c15002501110003554030106940c1c0000395100340d5000505c00c400103c1c003880c40100e280e110000c000708680a50f140c01c044000112003680088a0740d03804640c1c3d17103011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170232634 1250 170231384 170231429
    0x806040507090e0705071406070f0206090a03050f0403061a0109140a0b0306120307050f06010914072d020c040b04052512060312020106090b0f0d020312040b071704 72
    0x380b0741084207405c01e145400c0040d260190502c01807949100580e0280c000d00503150744c004100309001c2c0f03444c401380ca081c1c01c109031900d86900b00040064208480072a07840414000941140d00440d40000c08202d4021088810703e420105102e0707542c045403000a00156406076202c5071629a200281271178009030402c248602950000f40801d6000034000c8003c0c0c804440400013010014001c40090001a528081040c5410350582010071940c1c14a103000800d0b00f070f28000540c00c802d00f07042c500070901d00e1141030000c401150f00704d4041d6900968203114190340215407502c122006490501108021009020540d01d0556642060018000003040c201060018513604001c030703840c02c01c030b000444081d02020b460360303a00191101c2800740302c081d0340a41c09120320002000c11402c00c0c801c5100d270b41c000075040580000000c0c0136600c089040030440d034042c040e0002400184003150384554841c10034020f140c0010300101d40f423400d0080c60300420380141e8165000c968a03071049120700b00c00c0412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170233884 1250 170232634 170232659
    0x5040218090903090603091608010b100e0d080d0b09060f0303041a070515070e0a03020307120501110406030501030c080601080c0103020c19030e130b0a06050705070b0c030901080604050709 83
    0x341030460200340003c4d012540c600c4000c5005038030110051088000e004810340555105900ca0000c985c505400c0e00225241c0301c460304500051403d111907000c00301004281e044500c084020498400081c40c40300c096040c0d4001c201c00303941529034240319640c000a0102680760b11070007a605a100348810010545100d58083c16483c000207080d00f00300003561460319002d00860410381d41d8030940100b01245074001f051024204040b40e0740c43e1070741c4c40c40d001b00351110385a00070340901132014020481440360035006a0030300c00441d03c869030781d02c0d554800140200300c20300007290b4034900400000b910b02400510780d816039060034060a040302807600190000e5121440310021400703100d951810304801c1000c03510115000ba01d5030405026418100a500e650031540089a02e1514400003e15100e500151003610680d00700156510100d0819925264030341d4080c000f41071000444054001c40840034240359442030f00c82200d541c86e20b00070070040d594220f8850000910242080020815510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170235134 1250 170233884 170233891
    0xd020303251107030b06091f03080d0b0901090606090803040602060a05070e030d0c031107030302030708070311070816090b030a030c0c05060d061e0302090f04030e12010e070504021809 81
    0x14460419020400300e10f00b00b1115030300644003901ea02c0100071050078041581c0b503008070a015101300c680960023900c0c2080c006800054154840812000d600381e25030780c404480d0603030003020044190394a0074143c010b0320180c001c80e03000611039000001c0606c030010507a0250303403054001d4071055990300182001040020002010840c103103004440c541c400b4481c41c101c0c0c20046d503c841441d005410301038002d181e41c55420304a580589400c2021aa020042d2030959600052041d80c8011ba41412941400c108008008070b014003840044c1c0704200045a2101c903c11508182d0b11030741d10844030044078020380c0da45405404c20006000000c1c410000f243d02988100010f841d02030b00c0348003194594000b0181002480e84c2c40c00284500131407a803504440041d02c003694481c03181150f01080c84604050a49401129240c020804040c043c0b05007222450014040c80001601642c919010305103103076800302e984c00394034800719003030905008550b44c007041141019460b19480041c08110381006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170236384 1250 170235134 170235137
    0x40f0e060a03140c060f0a0306081c0305060a03060c020f0c0904020a030213112b02192312040b0a20070503090a03080c070b1201090203060f030a060e0d02030325 71
    0xc3d5241c0101759500780c06480e48a890f24581031f1600c3e1403042c00307012117100c0e801610041d400003100446003401c18801543c3c91350f151801181945410300401d200400582000300490b042001c40c03800e20f540090154220011081202c0d1003049460910048000980740650020083c00341400541041c900c00c6200c0c59042c6000162840003140c00c0314990000381d8450034490180321308039901c2440800507003502000c80011460b100a11844501410f404010070007800340d1a45443c5c01c01c3c02c40140710040800413181903540f0420b00c10884602c5404a0307041360641c501801080a01440d4452844140040c45403071300456540e1940c9a015004400115528030041058a9080c0c03074060f001401507110300b030042c0d19824008466401c105c5550040301c03002030288044000c0b0348a00701014111080c1120050756522a00c0c04100c0c603a400003d9190148905c0340424108513890b4010b01900403c0400d4400b00c6440f100101c0c3c8900c4152840140d00d2500390a1190f204100c0b031400761680c259 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170237634 1250 170236384 170236393
    0xb0a0207020d3f020c18071103070b0a200307020a2a150f1107140f0315040209070f140310080a08070c0b0304050a0b060301150308040f0e060a0314 65
    0x46001c41640c00194881074001e0a00840f00d0001c00d40400c4203021440c411925408400401841c000c131200c4000c001004000000d00344500705901030084031015504600b519601c0e2904031800409000300d2224105100003129140c00c40c820f018041c1c80c024400c55000e049103c04030344400a1440b0740149842c800ca2210032003d05550910f41000c004000c2411258004103070500b01500c800c5022010b0310038050803503500582e208000c10340400391815000c075481c0803007500000c50154407015442c550988620740716403120b00340490b034141c8104d101312140281c651391180111855041c811000000c203d1030440300064014040165510540400f4000c0106981e03a16291400d11000001d89400100140220038000c8512021000e07289904a480c614140356407030a03a18100c0c0b06d40039107085d40320000300354a0742e000e4000e01c410005003901c0d200c00d6074072410110071640c41882480894960b0340070000d0744082c1c2400b49031042c1d50007804074800500e03584900b2882036164605140b140903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170238884 1250 170237634 170237693
    0x309020406080d02010f0c0206060a033002010207120315210506010b07110a0b12070314010b04060e09070c121205040b070e030708061501030906060b03040b0a0207020d 74
    0x104000102c01c500e80f580c00460068220419030702151540c0d601e50085400540401c00141c69003d000d01c01c60754001050425500c01c400740c0f03500c080100d42221042d02403154501603659054020704481d5020760401e20f06030800810640480e00f6240001a004003480340821281e002d482007801003414001c2441c1d05031981e0782e14241003003002d801c4106100404135000d0207010b214080e00380e0110b0b09460000382039003000d1410032107020322410501c02e41601c10005901070320a8101a8904040f11510951540c40300c46480344d03500540101b03800120000d00c00220761800021302401031806848803510944962a84a1308035565000042800245402804152102c0c0300da20700c118015030b9000d06608228000030480c4641400e00c512940c00081d0501014501141164000c01c07100e803000007050701c81c0016000380880c014043c000c0c1c1c1ca45400020400010300003103126901c10741c11842180c4e01d0200c5003080303008400f0080c1d00b20852100c071600041110200c008440c8041400c40c01106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170240134 1250 170238884 170238899
    0x80705030712090905010302060405040e01230921071122051e0415020c07030b04140607020a0503040b16140a050f1207061109060a080114040204050d030309020406 72
    0x18003801c0115041a040490403075515882200c420240002030414400c0303514580025105e07024074040e9600c41c1e940d80d42c40309000c4009521030104940305401007642c04880441541e01c5d200f00321510111400f88101c094081019101d010000061000006090a07801e80715410050104801aa08007610400c0440e0715680c04080b015694506000850710340b03841411129000881001c2511045007102808006101000388040000b000c2c50010385130b0220b8120b003480c00308182d1010f40000c801c401480148817004201400c810004000c60700079854200342242d4030f60f906a40a00f05400a0105014071b0b030b10340c0001c090030074240040f003262415a4841050b9007480f001c0040b11075100c401d0b001c0070003d0500c041004a00700c00040c100d030400943c03002d4003611034800010002e07681c454107090744031004416104010310203012581c443d40301c460041c0800801b80500c02c1d50f030040c400542076a24160007100e040e81c401400000300e8454075074050700030f400703220412640300f0340f00ea10101c0c0b0784 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170241384 1250 170240134 170240137
    0x70302010e032b020102281805030a02040b0f120c03010b090603031c0f0f0c031b05040314030f0304051e03130b0a0309120e01080a0501081207060f0504030905100c150908070503 78
    0x160a06205807c00c4120760703001d0311030b8107140b1310070100c0c60b4505801c025981d40072888400180e0140e40c04200440d0800004d0b0003030200c102001d502c081d00078210f41e510f1030001803171407803501d0a400030040f181d0500100221440c044500e280c0c1680208216150070240441c000348021080c0804585c8000f5420450180ca0340590030800d100d5035901488900740e03040c00340000580030030075415180c030242003000744140b0884c04084c020b029000c44088100c0b00800495003000c2e040840180c603800c1603c0d0058840d051180e000c10443c0104840d000ca010001c4200d40c004102c1c1c00100200600d868044c684a4018400d0b00090541d07840d903030740c0403a0b400e0910300300700003181c1e85400c03043d0801c00025000c2c042c00750941c100390349490014087c1d1500010030f501d10392002c10042d52030300000e142c154040c02c112182d90096506101c248401c06800c00144c0d819648100c40301035190126003001c03a5412000b01014002080b110005844054654020b84800d40107242c0c5518110361500c455145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170242634 1250 170241384 170241427
    0x150904020d031707081609082109030a0c0e070e09041103010b0916020f060103050c0607170d1e090b01150e03060903091009080309100c05010e070302010e032b020102 73
    0x86507481c000c0003460742500348055010f079071b107040001c652801d14075120fa46005040d40080801e41990030700802042001c10f81c2c0940000400310340300c0b08001d142242480720203115890721101c86001207920756004043c00054810068906076070740d81c0d652603245903005c5510410380c16544c1d42c4002c1c049a29101c500d60b00c502e250180e107004203012400020320b0079190081101590b002207005000041001c150070040c0c0c401201c41c952200458103080455020300d11a51b030019400150408600d804c1e0b80000c118000d074420085080342c15800c00b001a1102440d0080010001d84010f2008400381c40c4400341e40c4199281ca01d4844110f070001c41d10304001510001c0d842c4d480850000c3d40b03485c041c500a4500b5006103006070f074031407500f10b03180d03600c0c0241c800c441d2050a04d20900b80000d403140324501c0c13403543c01a0003071010014015083d600c80b811400268001645004249424100042c0b0369803242c00f510040d000c0c8407801c011010f040301c00c00c4091011075408000fa000710a10812000b1341c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170243884 1250 170242634 170242637
    0xf0c021305151f0207030215090d030207030c0918200d0f05010b0a030b18101b02060c03010b1b120406110c01031505010305090106180b0108150904020d031707 70
    0x164122464200100d50314641c0c018007424040d0f00520302e0341640418a20101ca5054541c804882d8800c0072201e0f0754043d280d6003d81248110816070309044d4001602000c481c043c1c0d01c140501900c80340c0c1a01502c800707070100840d0b0404020a0f90000712440d880008000d54420036134148080000001c04103101c01320706484440d20105540c0601c0800c0c884c80d00011001c40760386541e03500c1d42d03541c5044400300030a1000e13415070f106903914054400303000c1d4100c0c1f00013a003810032001c42c10501900040c21040344d200d00600c51310002540d1429020100c0e4181e070000842c40b070600e07107000000311034100518100c402e03c0c01100c25411002c44100c0c082e1003d8082601d4942d800c200ba00b440034588000d500c5424101820b18040c21400001c418420303058690a207000300e207a0744c13102c2c1d00b40c0c003401c0aa888004110144480008062010350102442a400740d0f5403400783e0b1100d2060054082c1110741896000c000071000c0746c014509003000c60461446030500310170b2815140e41c005e202e120200c0e040e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170245134 1250 170243884 170243911
    0x20f01110615040b0306070c0201050c0a1b06030c0c0206091309080f070201170f04020906030307050f0304080c0a08060705031b0a031b051204120212031006110604030f0c021305 78
    0x1080f49402d00440b0f0380304005400400852034684030042000c0401c80019042c0100001c0c980200e0101b4072100111035040340c0300c1c0c01150f02c4074074030b1124202d5904c190380003e4a012013040310780c4d205502030b00b070340ea070010850703814000340b4000c1100342c1c2081001001001c4d071380c0c005103000506203005481004801280c8507201c0b14140005001c0c3d05450b0a00314851480c1c10420101d503495005071a007194068500c0da42c2c80c1c1c2d826006c070745544a010805001841259031860a00c1c0d00040104140c8503004282c0325090030303810500003180002c1c0554242500005c001804413482100515802450603000b8840c84201140c80f1615900440384100000d849800d50103405d1108041c2000014403440c00c40d03d04041809091449400079100805124901404803007140c400c104450f01152900011640d030701f40a03c90116a1342944211000325002c0500c0500358070010501074851501520344001b030025080d000ca40301e12842d00d04a0740000020750300701c820801d52007400d1050000040c42c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170246384 1250 170245134 170245171
    0xf030503040e010f0b120a02040305150402041b02030d020d0207020d050d4d030408010b1315090b1f0e04140903040902032d070906020d0c020f011106 66
    0xc1c200b81600b1040e420025104100040681c01c401c0b224410103c0051041a489004c0c0590181c451035002801074441d080102d042c11040740084c5000303d2003100c003088200c41e001c0039401c0c0c011507081080d0158100b804030022503169078005101010594800514101880d80084c9901101110560b5160700410070080219041001c0c560b0400e101c07800c4039258801381c4140b4102427000440d00314400d80800898030320041882400d1001c421041c240c0391255201d4207010300911100143c60312480c080ca0360b400e4004040d00c69443d1180142e10100a41800c140d14800a410301566468010861403020880c0085402c501070b51070740c0665542040096100c104000d0f42c81c1c0426445032440282c0620140720400011035040320140c5e800035032070380e4800c0a59641e201e0b1005071042d00c209408858000c58500c80e09080c42800d07a600c9001000e61150b0003240e4510031001d825010424004075400946000380070f020301510140740131170038040d03111015414244192050000702e110780d01074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170247634 1250 170246384 170246399
    0xa1701051005060a030b041401080c040b0d1a1815070e19090c05040f0e16020706091202060714071505191b0b070f08090c03061603060f03050304 64
    0x256904a203090307120100c0241000c0000343c1038401c1c0741c00c000c24190742d41000542511a0780168180c00300c0461411141e42c1c1d5100c0040d191018100c0b002d01c03980c6018885806841c2c01034464003660381010807980283d045241e54114800080c00140d4041015540340303c12207001c0141114901c0025082d0341d0500300950b0140c00010035403d060b10811340c85065050711800c0c0d9403404201c031032140c2c1c0403410103440c0702c05598610a0303821028503102c000e04c0101d04a030240da080303030041c15131201d0449180401c4008a840c0e1a0500a00b000592552420010480c0902e41580140e000500c0a807402a1556070420602d2600900c8403d681140d0010043c0c1c0d43c5040e030401c0c01c0c50103400e0542c600100604117200b4081200a00c0092085d40785481641e1f030001c08049900c0340d03201d9201d40c1c250400f1003014105451440b201c10000300c04100169005401160304e00480b54082c00510041c2c40c0c40a10314042c28000b507a003020965079500c00514012030000000045008001840d1341e1800e20f0034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170248884 1250 170247634 170247641
    0x12040c03290c03070c03080712021303031808071211180708010510090e0a0b1302030a11040503150403110a03050403020a08030a0f0c060605210c030606011403150a1701 74
    0x2082c8541014410080002d0708144003030078265051070300d9101641c0794207040d03401c07070708600305480e4051012450b140c1c10504020302c0380039a8060b854940e10b2100081c0d00c2580458240500e15441c5c1180100304111079101074140c1010b031180d20100907016600002c02c1c0c9004501003805514155582402406a040713404203015003400d40c3c2c12204000c152201a080000d1842280058121030780003030f070100580e5000c1c20461900408811048610508000282d0807c3e0380d80305046140c54600010112203601311800c481000d805000200654400e4404108000b401034007805501086407400500601c0400b6a0ba0f20a48034192030720706600520144e0111a0000701c0594420402c0b01c1843c2d405c84070340c2052911070302d0403a00302001031400d100a07100b00e5011a4100104d80d400d00ea0030703101100420b4002c0d928208946035003094104040d0346500595585012031030003202d41003006000c030000c55100c1e503020707030390300119000d1000b248511070306030700412000b107041002c201c9081c400c7c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170250134 1250 170248884 170248891
    0x170d09030e03010e0a110d080304050f0d0906090e07110133050d0b090a0501051006260612010608030a050703020607080402030c09071e050405131112040c0329 70
    0x40c001c10001c604030500d950350303000121018120111840c4810229036461f503841d074440342d014000a8480c1814500315030358140300070300701505004858500d4001e51203045d141c0202d440c0e641e40c5c081c07218a010403001c1400406451142040040f8a030781c0440d80b82401102090002c03000100741800a0005122b00382100f81000d90071004060030400141e6640c440505166410001c56645503c0c1c00386114a0304c1800140200345508201c10030003c4500010b00c281150b402e40c45211750a5180815208421155500700c13051840601c041071702d5050515150070710705940000001c01503103910f595490750700440100c2d40050000103401d820945d05201c2c0540201250802a240c0c2c141a4006511100101070450044214000103140c00e84103907482a810329071007075090f00882da1207400500c96800fa006a034003605000001b1100c41c2e0300e9101d03042c030720804c141c41e05040660780003849803d128041c1040c0e8010700f040c41c001c800f00700c0401310f41c0d01c88070303d080b03803000b42c8650180c9007018400700a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170251384 1250 170250134 170250139
    0x60105041109030c040b03030c07140907030c09090b03070e0a0204050f0a06091818050705090c12062809060f05010804050309370911090616170d09030e 67
    0xa00c840036154a002583d81c1c0d1850013220041039491b505400300e8558000d240d0104698495800c1c0051240d40140020103444000d640310324569460360400e8081e034910343c65400001301815801c00043d403823948406010f010060984200c8c6a4401d6405401d1005585000c802c0d540080c040090349440074025030010070542d94552460316000d0040d000c124140700b09007046420b07087c2400107003055031060b01d20781c0381c440710000420018104070b03944980500940c1d00540d00785011606001000e015100800094090420340e907075694180b002e220020780b016a45818102c6545040820061010024040720b00e00014850b18150180070345211035800789040c44080320a000100d10007004440d10200183c54201294240d40342c0010003066440c0900143d40c0410142e119a81500d410303c07003200c603496001c2c0100d2141e1150021035100700300c19940e101004210080400440b00840c10f0f4450040703071041c0b21100401616825640940b111040f2250b4606000c0101900039604d1041c11005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170252634 1250 170251384 170251387
    0xc0906060f05030f100302040c0806030f1b01110a0506131104050105090403030b0a1a0a02010506100813050c03030a05070b0a140105040b06040504090c030308091504110102011d0601050411 83
    0x40590140c103922000d07000c0c0300d04c401010001031110840b822080b000b15409002000054102d00b80209010000d032529446409640030032061a880041d440040e207040408540d40690b1020044d6034070707200d055804007030b4010f01005034003040081c04a1b0380b1030200d602250480b04031514144032610454020725200da46400018005511845c3c2035580c00350781403c00261107109040018010300da241d01100503207124400e60024081d6150103401150b001c0d4001381300c503841e032500300101c049c16919a6000901c61600055034042c14004420645000e0000e85029025004c0803a003107520003c8108041080054903c0030000015021540208003d1080107076109403000c0744414041841074a10542c0c03580703045072040d07807460115402480014400c004204071843c003010a08200e20090700461210070000b00107403004a00440d9403032203194146020340d0340b5030b6100303006181500300904540d680c40104445002c0320500502c14100ca00c000c005c19890601000103a440c443c200c0d4401110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170253884 1250 170252634 170252657
    0x8070f020a0308073f060503010e0a030503060111060103051c08070206010504020a0315032d05030a030f060e04060e0f01020a021506043e09030a0b060a080a0c090606 73
    0x5002c11110b8110509280c101c180944850f581e0352110780c6114031505200d140580206413203698171004003d5034902106001042d5641300309801c03a8452160000f1503004041d4041c000b910810045502003070504107070111541b102039103441c2c11802d810031102940038a8080c000840c0841741c8451a43d03641c41c1070728280c40c2012000351524010f125981c091900402c0c251a0039010340c10144007003080c1c88100740310a0b520b00304800ca0f80d2603554131201d042c1104c05040580e0f003000250a03a80c54000c0700a61602503040c404900030061111082040340d5508800705210703241e030207841d00070b41c020788001c50b0038030300d5464840c10f00e8501c21445406da2703c1041350003403076600812404807010803400711404c0d41c1e807080f02240151041d040c2c1c2084c0ba02c0202c1510444881e03035009440ca0902a003000b400c0041500d140d1b289900c04d080c1c086516500440c00760000943c3c03201402d501050140250865079901c0040b2071610541d0741c1c0c2112500004d99041c84149628403c82008250a00e48141c5580 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170255134 1250 170253884 170253887
    0x703120605180a1d01150b0903030f09130507030207030210060537120308070503070c020418080c0a03030e031e130503030406081501170a0b011e08070f020a03 70
    0x1030b01504402807500184000070f1141502d68880d04413218202032126000d010700c04018002d042c521000c403102c000b80180810980301039030a41d5000c04e400785c000c0d480c00d0b40700f5412020503082031201c5607101103504003103080706020f030056900a41141d200580c940400745406800c0031811000f0a402516081b0b082015a503030640c41e80c441c1c0802e82c2078003040d506d02c40c2e520350210804c40131005800c0e04014002a8006500c8004490030b000e036507000b54035214003900311010b00c0103403105000200041101001b51030541d01510f948041c3d14080700640c40c041da03545409400500c82d01d000c2c1d4001800d06003d068241c0200358800107644040c40c54505410701d0340b8618610f8002e03140000c2004510b401005001c40740c480054200101180d858550b20a00145608011140002d44203c94100400d4039401107642100003c80d2000040241c1c0d6490310a0b001803118201031410031001c50040500742c100c803200c2ca00380490540d00c0304c000303240043c8054440c640c0c07801504110340c010700440c030200c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170256384 1250 170255134 170255149
    0x60405060307140103020409090c0501020d080115030e0f062406030903030a020a0912050d0e0609030d030b010c0c081e03030906040b10090e06010810090213090c1a0703120605 77
    0x503000207400e41d1280d00240c3c01200240220381152080307a25200c1c025082c030a580a2405c2150001da00b11001901624001c603201842072103920040780c420162005d119010f900070303c00b400140412900c001d6242080d4903d8064262046050307503002100760505800c4500700c3c501740396015500149103081100c48156a480010181c40c101540400d0710580e0358400d0400e0002040c4c000b00450b10400a824010f4840010380d85200200b450072a012040b41011415165960401005000780300a00b00c03043d005040e80c005001d04001030458810005600d41d0800710180c0320b10401085019140e81c0e2822003d100300f10040d645503c01e0040103020140014921349c070070f0303004c10401a141c03101c0302c1c1a1840d8415800140c0300c0c0b07080007085427800c980010701d00e04940d0504200e030702099814800000311240041c010350000b03012480e4200c50841030300b1a2031201d10406241d01c0d00703030340d0342c0c1c0000f4100034011074035241440000303010b4145540300d0801003881c10041c40420610340b4250001d03000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170257634 1250 170256384 170256389
    0xf020a0209091f0c120c08040201121b0215060102070f1401090905070206100f0b180a031e0b060402040b090f1306080d18030b010e090c030d080a05060405060307 71
    0x2620020005031010206212542d01103010b00340c808a420b03c001e2500c0b000c0d1104504840001e0480404000c205909005408001d41d0301d482d110721544843d0011074400c1118803076900c0751611006c49041e03609504d0041c00381d65020368060502c28410754042070124102401260456200400c18080f0342248000c1204a4100355006d2081001c00310050b41d0303070a82d0b0b521076616980b419003044500c4e40c0101e8002c1c0314940105c075003035440ba11000000f00303524490207a16801c40060280500c1d41c14869144103c55000916070b5400c242c1e659527100c15200c2021010200c81010100c520410484d8168240c0103641100c0035810141010888040e5000d00c04140348070b079482c190f05a42c01d40710030030a4074120010000511046464203405540d41c01030011060000e03180c40d15104115000029803010303a98002051400703a4079169058052000c080e100d080303140502c003510030f165a001c00081e03403841a16150345503140341110403581160030040c4001c0c081c9041508002c01d070303500812010705 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170258884 1250 170257634 170257639
    0x702071802130524160204050612190201021c020d0f0206160302070317100602070504020f09010804020102070803030906071b02030a0201031a04020d02030604270206070f0614010302040b010f020a02 87
    0x201e20b60b05400c80d500d41964070100702024001100c8010b004403245c4800507a0094a0a01040e140d9a090290044202c0841c0c0c444d40c001415074002d1030b0003d0680c030040d500500c129442203911580e19491703c894081c1c080096408004c1d038010681c0c02001c0044041c6040c000f4041d6864040502420089040060740c2007550004641d020940910340600f400b121300003a00c003181c6000e60402101c4040c6000ba00090f00ca0300900040310315160080320b164a49946007a03051003404001901c2e4807001820483c198081d81501051404042011310f1240c260300008180c0c0e804c00c0b8001401070b250401000c65418455a0f080340035840000c1d85038521982880c0000b140c103204505034400b480c85855050784580005800d041c2615640c010718005c00084804001c2032241240f004c0f41414458640e07061101000d14030005460300c0300c040c00c0114082c0300f4074503c0015942d00c00040301c411341c1412000c1d40b0070200500660916100c2c254400c0300030b080c06070750103820070303c0a90b039110183d40080c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170260134 1250 170258884 170258899
    0x1050a0f0e160605130b03070e0102060a09020a090906021606020a030b0609100f09050a0b070203160302100e13050a1a04060803041703040812030f0609070f0c0f050607020718021305 80
    0x5012101100c1e02c0001010821011b545a06220000038403c05e4048851801485203001044490345144241d00b2100d50040150441e0383c50041d90402406108405658060f428040020300c1018440c0c03041c0c0451040300016614507030540054200c6403013074211805040d041c45990441c0e210303020803207807400042c0bd1080501604520881d200746242d04000e070881500e0307100146c00c0488101030215148218261402d40492080c032039070002c42840040e6100038031600401c1014000c4000907000680603055052002005e104241070b070f00d00b130754800c0c29540e5880b00000f030703040d4070090288404800ca600b48038a519150300781b5528010740c01511079201c00315810b410b40c07803020030803a0010101001541c1c070f0302c4c11480012026410440e80b1041c9800c260001580603e00448154407480b01d58a4001c0303101411a4111036692110208440e0300300c00b058840046a0100705881c4035045031f50003404002e0403c02c2000c0c4030204011004522401801031064081e140442101030b0b850a440c0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170261384 1250 170260134 170260147
    0x601060c020f190602030a020f2d070504050f16030c08060f180403090609060e0105031501230a0f0305100b0304021906020106050a0e040510180501050a0f0e160605 72
    0x341c01031107072040c10f2640d442144800604076030003101509082c51540c00b65545041808050350315040301c4240351045205031848401d01d00c1052804c0300e000c14890080314079264444001c1421100c040e52440d100351180010007040541c091a000c2d400603c80c9400d00400d104d41d040641004800b81583d031058142d00210140394588041c80f0404052101c150fa62500746414050404031070390041d44c0000d45018000b24110303001e001c225010185c10b95401e45942d641e9015941050380c0d03082500c1c10807001803d40d0404141200d840e2004600440e80c7c1e41e80d512200c000646038030491800e620916083c1401c100a8000d0b80120000712520001019960340d03951001408060407041480c0880050040109905605520403010b403401514480d5089849141901028408580050460b0312030f486244540f400e68010880d2100115014150030003962358450130340d002100d01090709507039802ca4110780303029402911048070020000d0000120010783c80041e1070000d0107490188400024003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170262634 1250 170261384 170261389
    0x70c140102151302090106020604170a050f0d0b01271206090b100e07141912020703180905040507030311070e0f090625110f0a030903140601060c020f 66
    0x26440350038092102c1c01d800e407900d0420701081441c02d0900b030b4040c00c2c2040000ca40c0c00e000294550065800c0327401b803041414240010503e82d84156801e0080001c18490582d80e088a86c014001004c81c002c07002c103506c01020001003100c0d152521089440c0c4401d00c011070b1900d00c819880b41a24140d42500d80e030305865042c510058000358800400f0104400708114442c0700c070014802c1914481c8443c030320903454400007180e00000001328602100d60802100c190030f402028203550181444c2072140c0b08014000400d4104c0e00560400e80100380b00c45009490000c0c80801e450140a41040420190805d62505c560307510613800014140034002d040714183c02800c0005100500c60100001c40c20301c1c00c01d0f02c6a0702280c00352048800d40c441c24001c1201102011540840e1082c903c40722036500c041900c04031354a60400b41500051700908602e01074000301032244801281c007948450070303007030302d1480c082908200002c10226160010001885410341c400411400075404855549405150100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170263884 1250 170262634 170262643
    0xa0507081210170105040309050906010c0c060f030f020c0309101b080d0b0a0501020c060a0504092409090314090609122d120c0f01020408070e010b070c140102 70
    0x1034041c81c03a100c4810003034044074080aa03410b0352503001c40300c1c0705250140f4a450907100c0a440003404249160018010740c10500700c1154412130514100004003402d80f900c0d0501d4010707420031000941c242550280701a00744c05100c5031000091821071400d00c030402282d8a0f0f024031100f0a100b90b1035208110b01d098801c2d0382040300400c03181028034482d103503450300c03007800d60050080c0110242001e54039201da2402d118480100d80e01a000f90842001d00d0007003100c668031800801060040502c40070810341e00c14420100100340111a90340d041f805800011f1070b2038226032020074174030700b40030015000070b40c4031101c24115500001c00b10b849000c0b00380003900601600c0c011700c1d0085008004002c140030009080980340b002081c1036410f9001000d04807500607003950010002d40e000602419406280c10300600001407000103442000c1000c4496600307a038443e61180509500c858001d01c003503038042d050310740180520101689400310744e40e101110b41525126102000d540d000d02c850103a4000d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170265134 1250 170263884 170263897
    0x703051203090f2a0f0a0e0601021e0a0b0c040614070c03060c0e01080612030304140304050a1403010f0b091501020111040b1902070503060a0207020109050604061d060406050a050708 80
    0x40c1a210035440d4585440c469061380da04040441c1c012007031240060400c0744c15188000400390041e0101401d1039449103c81c2e101074502e504506c103140d012140e0b4800543c07040d46018061002e4200c080c29400c20048854010302843c1021070708000401103a90090000d91180410011003500c0b8041030404000c0180e850b840641104d090441070507200360302c15845a04100262907074000ca481f8007040c02902540214014500c2c0c1c010408070303000c554103400400c11005160101c0749070a441e400415002c80c00f03a48007070b000a204401c030b80400c2c6420301810030002c3d210541086442d6251002a40f03070035010b071803500c802100300c181c22440d034030030f400100303095490070310003540d8541e90301e585aa1075015080b00b294050401190082584c800300f520011500014001d044548599038408002c0d031181104078140b02c1c00c0315000505846480181c8020b00064032400d8928181d00c01038210410300c3c0c040c10307200e230f02e042100380000b5420030142c4161900901c1d1968a8400e94540f82403d0300c60034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170266384 1250 170265134 170265163
    0x1807170a0804060302030f0901020c0c0d15140108100911010806040908040612060503060c0715020405030d110606030a050d03021c050411030f0c010c08030403050d09061508070305120309 82
    0x40104440303400d0b1700218044c030515010031040780e0f54484586c2c200e0103017241d0010307107070803018503240e040c6840907840d01540c1c0111442d0080180d44c440c0039084500344c001c0385060b4440c1d08010054440d00b4403501c0740403100d9220502040d03100d65640050b09400b600828103020840007c0f0f01c0c10780b0b07250b0104c0002d0758410002075039180c880d000501a09030700d0176040e0740c0c2401c0080100e024200411568026244241541c0c1002c886949030480b205203276003100038259091100081035a42000300910000107030303d85142140702c006559080c0840105414000c1c1e0060440700d0000d00300041e0103088138110f1034010b807210400d0329217042d060075001c2c1000215082c1400d010501241030010b04101c00c084084400520413900e44a44070189021203902180500c1e0b014404101c0c07403c020750b8814400e141c02da151418070315244086420003041a1420355541c00200c02030285500c5e6000a44603820007810000e1031b41d81c0351652000c11780b008103a40d41d80800401c42c0b12004112405020188 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170267634 1250 170266384 170266387
    0x905040f08072316090207050601090507021203040c05010801080c01091401030b1e2d0d0c0806040311210d0e0a05031603090504020a17041112070302091807170a08 72
    0x4842099135612288050748014200e80180040d0150061003111810341c0d00c4030103800242c0ca07000880009001c010840ba00b980140c0d00b88d09510514800103602c030300d104641005d43c1c1c2e82000d0004040c01d2050300309400550000d84c0c800116a00220b10404503108039128540c0841080700480140030981807a940000c1d101c2000d2480c0b52900f030b4250f95504090720307414600c90501c00401c1c5c0350b0304186107400c4d1070b140d8201100c1d80350030401e00d205c540c0c80c00340c4441d050041e960320b40a854483c00310380503400940154518030400032305210340789803903c0da050a5204801d103000050f05502c00c60510040247c0d4409040d12054401d200d5403226039082010361f81c4800002c624100780340744c0003500b203000800804012556103814400e60742107820075559680c0783c91520340102e440344406041581c200745020780142059455003025400566028080c00072203185206000038000d02a190411580c04011040e0300c41c00005803103005c4810f8900c040600c05200c1c502d940c00c100c0c06c020043e251040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170268884 1250 170267634 170267693
    0x402070302031e04061b0303022703150601050d0b0a05031f0507030c090e070e10050c0c0d17070f06020f03181501170f070f0f0905040f0807 62
    0x402101521000d9500200941403d074480340380b080358401e0f030040c40d000c203034802c2a4100149256148114241c403a007801840d00b5803140c04220720714140c40800c15480c00001e09070a050406208414183c9041142c0e100130f41072010000e4060300030314030b490950700c0c0e03100c5104041d5602d0034400d00061070301505940b102d24019046040349010f01000c1a4282e00b8407010a015034401e1243c1c00c41c0d28010364401000c0c030b080680000350131402522540400440113155810b03036590080c0d010203960f5940780d80796204100704c0128108001084103c0c4541399100c02540072810302039144280c910401a81c40c0d031900b481c0340c560885a610306010704407920104514080942ca600210b000382d8001410780e407102e00e0301c443e6596460304441d91014010035000100600054102d0401e03030760001c1070588950509140402d817a18025500c000f07178079148030000300b00107a0207400310005000942c000340090701d459142c040d0708014007600101035100c0001c00c7c6046c41040396044a074003062254407480003a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170270134 1250 170268884 170268887
    0x10e09010b04030219050f0d0302240a2412050f06040804030204050627100305060901060303030b060a02070608061503040b07020c01020c0306060d0212060a0c031d0c0405100504020703 81
    0x41043c003040b4017800d12164000344c10385000c4500e000710307003004060880440e549800d01582150b0f01c0030031415481001c00000107a80000c1418040c42c0e04c050102c2414070300400f11805072458800810903210448403070071821203101081c1c0b03040d10303050903081601084502e40b075454030701e824581105901400050004119111000b08101c1e80211000d11090b1900130411072880100b030b03100400801200080c00c2030a41c0c0061490340000d69800e0580d8540d0741743c0381c007400c0c04011510420165900c40c0c0500c20190103100780348110b09e01740e50320340c14020121000b9585005500502c1c00b4446030000088a41c0da801600d00031a1480400030754503410a4a88a064103905444803409030040c558486480e520001d195040c0c0c3d01c0040041403140c85000a1003100c114081099821100208413902d0101c0c042100c0340c040c251804001901d548505001422503150041e101c144494110381c000e0050f07400103c000c034842d8121000901c0c0e4480400030342d4540116442680c000380040740030000d16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170271384 1250 170270134 170270137
    0x10080f0c0109150e210a050a02030d0306180e101a01020f01020306010509060d0b0904030f030b0102071d0a0f0e0c0f0d050607050f07080313020f030723010e09010b 72
    0x503400703032210010107850b00c404110a031031214402d40010040790045116160484110b1801d402081e000440c0d6014100302608115010500340e6a079400a20b0150440c2402c00500504407400d1408010190408902ea07080c40700d915440e600641d11003020f0100420144420780030203680c00d0041040d01c1c04040f941c01c60910385403296000d40205030210b4411001070085034442c0c00140d5680f45803002100c1000641d81200001e15807003070b5903204200454a810280b64000c80c025142c041507517181c42070040907a011089424115004510204002860052000050300420002c1e54440c0d4601d0002d800802f01240c040940070f05000c07460031540700102d0b100c4c03120b01c01502d141090000301c0c800d0200116640e00024100e5004d8400101d45070710520103000c0c1103540d164124039010040e25282c0381900242d80311050300152004480c02c51814010200c0000d01c1a401307403000030302e00440425200d04a000b401ca00c0d00003021440b1090381b29071400e040c0500014144042545c4400120285 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170272634 1250 170271384 170271403
    0x706080105030d020705130f020d02040603021e040e0403082a0c1b0d06050619080d030f0c1e11010504050d020c15030712020405120105091e0a0b10080f 67
    0x3070b00500d92900015440860303164150f41018100100b04080b04447c2d07402091500d5801510760342c02e00003810908054002807004050580e00546c0360303900b4281c080ea42c0c032103102d00c4140e181020030003045044006802a540190181007a024507515480d802c2c0403151442e881007500d5950301d09082c10865442c01600541003100704035000c80c0784590118450303c140c0400b26510104041c554000a011500110341c4240d01800c080da030340c1801a100e00d00c40000780c000d2100c907004182c00c040a690706103e1100307644c003801d4050000d036008040c060569210f03110304180d580100c089490324a800703039001d440a203d00800800941c42e040c20300685990041d840d20005006804000b0b441e171400f05080c089042c0b80c540c0d5149162900c41081c1c451245061728407080603000d101c001656a58052007003c0c0d0f4180c000013103136918140070f441d410700d88a24a01c0103030405c0200b070003079400f80010304105031941c4158406c4480d150f81c0c0c0300b18491100d0b644940d00c90301c2035000404000c400400d21560 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170273884 1250 170272634 170272639
    0xa0206090c0a12080a030e0a0503041a09010507060c021f05160203030708160c061407021513080f0c03040303180b1c090c03211d010c020910080706080105 68
    0x3a1841c000e04110341c0103460310460340d100c40d40c4884200854201402007030f85070210300317000580102c1484100d081c581d03c1c0200391419040403e0411098000210300c61501001442c4c05140208450028060380256034010701242d60390040300d030a40b4000c110b00e0440c500b00c0d403496200078040c208914054902111240d10b480c0010441d99446030000050300d020b949603072503401c2607941d0304554000c000c804840c24002c0001e04894000070844a00c140d080c520f10b00a5558080d01e42070101038500340b1000d0410140010340380c2080b51012019210900c17581e8001a1141d844400c000065014054401e02e00740d18000020004101500300300c4001c410043c807041c100034140d990610000900034907024a0700500350f42d5180398881003581c40300c15060300c12501c912019403203480f0760a800360166401120900095100103040c2d401070f0001c2c0c0d1451200300d80490110036080001c040850303442c0b00900034002e12010650108140c15400c025014000031500e00b0b81d60740100604494003880351a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170275134 1250 170273884 170273893
    0xb0a23040b0a030317100b04030b01030b07020604230703020406091e051009180b01030602030a0608030702030c330a2007031101050d0f0f06050102060702060c0f0409020a020609 78
    0x1c107070034203040d91821a50103480d1843d050016075540400d034440241401d407205c40250700400c0002840015002842c0150b41c20461581035240c0103449100144c00da4003550310480401001440e01c010480c0400b21149524486880e080801450000349400003076001b41440360100340340c03142ea80600c0c0b0580810702940c02071b0300414800011210309031507c5255030794444050208426940010381003480f98042801d4084468840500d400320a8108498007500003092050040c4940610000350807150044d41c50541580c0c002a6140d034544802b500800c0f00e00c3d12031402c02c0801440c040d40c0e114000312034010003030040301c9a00030340c404402d0398003060260f080410540d0300c50454440c3c0000c05c40080032090f0954489500d02803160f4001c5d81000010028060190401c0c080e50030070040e200404039026500c842c030f68040e074070aa0007060442d44160104455640e000640d80d4001d8681580715503a00c144001580b160300c1250440601740b40005400480c190f40062054814864001650b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170276384 1250 170275134 170275151
    0xb07050d091e0506030601120c090e0115020307060b030c1504060306120f0f0203030c0a03031d010507050d050402042a111605060306030304050904080304030809070501050d0b0a2304 80
    0x60603240400810b00108048110a02c5982402c100454100e6414102298051100311030107054030081d4030130200041d018401008070110b0081464054241001c800e101c40004002c02540d80c020300c3c1005e058680c48000890081d2014000c42030150f034040d0203d201f40c501106603101d01d90080c0b0840000900d86440001c2d03508620400b0310340e165204002004520a0b07490f45c40203144101c9099a15010401c2480411142000301c054003d1098401062340c1150540c02c03200d903402c941c4184942c4e4101002c00c40103690181c02c03500109074918000405846a0000c82c0044c40a03428840258032408403040d0940c10030031601c1840c2d44155542c0014500200f5200d072550380c50303041e134088a00c600209005a01e000d07009547d000d1009000c80707003099682d0002910211003950203850701d54000007888203140d408203a66a001e41e00310020080c591908000034582d108550304840500d5456240c101a0398949100300f0003449054082130035a885462111400114000003d01c07035031910144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170277634 1250 170276384 170276399
    0x80408070e0103080f130504020c071403011116030905060d020d0c09050604060309021512040512040501080609060103140f0910110a1b05030705150a0b03070b0a0302040b07050d09 79
    0x1c840c1039a44c03000c059402e021101901c007400d5042004640d034078078030010300418152982d01c0948888865100244030b101c2c03608036440a4228000505070103a41024520f1800224500c11240412100301ca040700702000d50504440c0007030945c018039401040000c0c02c3d8803a000c41d070058904c05491010812202d9000d03c001c0d035034010a4416113030000002d00c01001514002d5000184442c005412007906214200841100e540b103440c8002600000400384002d00c4400c101940070504011001d61416007003a001a10003c030040916124442c241d00003807090f40b00780c12034420044001108692810040d030100e01c9814110b40b0030805200b4299070408a419a000b2111141c0302c194200d0303c1c2c0010100c003118888160310040000b455200b2440b80081d1081005052040c01031002c1d1032480ca008003600030310b40018140a140c2400c003400742106079130203c0c03118200d0340c0c0d8103101642c40816410a801a01440c0d0150f00d607082c1c04122001480b9020480d45039690040c0d03030b0f407010951203504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170278884 1250 170277634 170277659
    0x204062007090e010b0d1209170703060c050d140f06010c0b06120102040510030207110f21160f0f060801060507080a0e0915030105060303032415040308040807 70
    0x1000d003003540508420848080194003d019010741c4100100c0d144000001080082040f03032001ca40486160700109081e80e03011009501134020000d0311059202d00944190380d698082c08007915141d600e4442e42e0915009104640c1e0800c20104203100c0392080641c0d100600b079040302d10607400c0303000200041031984111058508242e001844c6002d941b6a0b4007484a00f075084644001c541d0350070000442c6603030b01c82c03610250315659541c01503a036484615008904000700b0004502892005260981a5481d003242c219618511a1701c0c000c0c0998280700d11b440d200180c040d0100114852001080c02041034040c0c206450020740f035424025620b4100311100c810034880e01d00080d000340001c0001035002801003050342d5181c40c06c402000c03124400100e4941068904103850b1b00b003264100740904081c0100d40d405401140514254580388082005034042019a21141388030181d030b80742147e483c2101e2460050b0b10400c0c554803544c507454420a41d60107809951103500c140e01e40011004c55102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170280134 1250 170278884 170278937
    0x1207020105070903060b0a030c030c0602010608011e0f1104090902010e1e010804081207090302011106070f0309050a060608030702030613030f050a120c200303010e0f0402060c010906020406 83
    0x19501c00509296444650051844184c041d17401f000f181d10000100300c47c4507040e0040d500a02c21020440d00e86400642121301640c482132042e4140404080100c80d54140540d21700080600891341000d08501d83c40107180c0303d41d4101340e042003c1404035482003298000326013075100b80c0307568030302800b514100152200d203c0ba480300446800c10340d001055108402481c0c000d44500c01d1075081c0009060050000384088450f0300000c1c03800502003065690050b040f031051941c100180c54942400071006284014154a40c0141605da80c150f4040183c1081203041c03c2d504000108400c5071500b09060b101c0d4041001684240300b28408070325100107840258800075415185c80200c08026142603d81c0e1b0400042d01c0301b4007540505518000105002d28040c0061941e40e00030200c41c1c3d4504000143c2d00c0c55030001385030f80140018018414685841a045443d040c40040e02d90342c1c91001a50350f214541c503144241d42010900c3e41005200d40150003907881c141c0b06c000355030345081808010f456a42c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 170281384 1250 170280134 170280137
    0x20d0801080601140105070506040318170d030e030d05090d09080f030a0810051207090507140906070212150f06090f040219120309080c010504050d0809010207030215120702010507 79
    0xb180100400b000300c0e0801c681180041c1000b80c1000f01d1a1151820050b04450517000b08410f440c802052600e040d060101818941c51401d00c071502a8450a07581c0120802507800c0c50765030000710a41c800d0030010b40d030502c0041213050009240c4040c5480d00e50740d600b00d4201c0868150f0740081403041000c01e01d00880488040218105040e0348001c5842e5880030f455004a18089000031400e600c8001d294040c80c10130000408041d45401c1100e4202c820080c49801000401c500c1d401c035000e0281e04940743e07850101d5110b80c50f03107064000280f011010121480d081d109100301030507072006221006100b42c81824040c45503640f6801030100c0d95004864540140b00d4000010700146090542141500d0b5035080300e0741115224075420403030305e000201c282d0202e41d419034204141c28040111400c03641c000e03c3c180341081d01d07000100d095003134117400040242e1404030341b05490742d1082000f4001180c004002d60540400d5040c80c0c02e46a0102c81d42c18a4031100e180003641d402e005000701030048803035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 170282634 1250 170281384 170281393
    0x7030915090e0420040e01020a0e010504120305031e070804030f090e070503100b041211150313051501030606030209101410020312090102032505040b090d0c0e0601020d080108 77
    0x656540c070b45400d24061300a50b4200448030790809945407481502003006910000580d1813004d101d001c0c15000f100d800c03c0d410881d0401c020311500780c096161000301603050030130540b280c48040c40410701062441c3d81c0e0001c20701400401034036039401500140114004e07251f62000041050080b0f03040a0b0ba0700600302c0d41030b01c0d500880c2001d403040303000310f43c000c101c03401c0c1014880d10341a140300c45500940c407858170141100b594005000b4045242003800350215040c1d0701d50f40900d66000f1403404003c042c0d4004c500c503241d4820074010140520000d0420903403c5008640e180e2a12400501040c0800d900030b490070360002d50480040316075502901e0030f400543e01c0da13a500b04204040a0340703008860003180800d000b0b40056401d114181b5000381140300005d0303124a4002403500744d004070405151075402d401c1c0006c091030307a0801c04840a40d140303003803103c0d540c3d21451b021032088420071134000c0041100c0c103800125106407008103400b51134260300784e40c001c08000c502106c1c1001e082c000c09210350403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 170283884 1250 170282634 170282641
    0x905010311060d02090d0302030a1d090c070816030807030615080a020f070213020702031908090d060b0904050a030f05072001020c1201020304150219031d010207030915090e 76
    0x500e0701c0580841c1c400f01c840589000354800c01314807100c0e08007004402585c0041500402150483c4142c4d0030045100c2280310102032800002da0a000060894901044006043c10601091000301da00c0100010a41381003a907443c0f800800315041160703040c00080c505500803500004c804c076806c1400982e03030f58a0f6295107030b14000300025845400841c842d07101c20810100141c83d6006049034050400c4070050712100c01e8014907080c4190051402c0440d0032208000c00000c01c09815140030902c29104564250102d1501e6401403120900c0294416501c001f000108040069180321081c8079546101c04c0a00b2b48106651901407040014501c1d14517241d00803054034004001810000c0520450701421015004540001b81404081c0b03442d940000c1044140070300842d40d05980c1d1500641185054400400e8003540d07100810480100b603150100031070004904850000200382e000c00846d510101464043c181c13216511804040c14617215140424900606c918011925030070011151540d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 170285134 1250 170283884 170283889
    0xa030c1d0105030a110310061707050103020a020303010b03132f0111070605031e010605070c080a0305030408070f0602130e010f05150c16180b04060b04090c020c040e06010f0905010311 81
    0x30154000c8607010310809245401040848c01004000c15120000131402e010a60100341003854503000141403500404c030151945500000300c0381102d9201c05026180c0c0c4945007016501444514054000b40c0c068415910341042d264242804294400c90952500240801541c0a88510900000c250030004040100b58050360056a1180d501040c00103041c0840751302000550080e00140005080400d2500400014104000c05030802d007004102003107495a00070b01034803001f000106100f10100303040d07080090708811342c0c1406610410640d222240035040e02c802da0001c1c07003034112030a0303050000105592184440010b84101a21800503c10b030018210b00d258003e103000c400f640b040701742e441021881c0ca0120000f03403540d412040c0c1000038982002066811004040b48035506c3d24070108494549141144c0448208150115401170b800c20246d04200003100c05079003180c180f9101c81c7e0f4105002c105203040c7d40c01c5048811503c0e859140182c1140d000340401820604102c0710b0030701d6403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 170286384 1250 170285134 170285153
    0x30503073213050d0f0302060702010626030702031218010305060d0f0c0312090e01150905010e0d080c0105040b070c0c0918050136020d06020a0306050a030c1d0105030a 74
    0x880181440400807a964000b02d51320118200041c1d03240c103107182c0064201030f4184a4250014820320090084a00303004440191000300c1409607803005d0901c03141c560031101032044e100d030f80ea002000d0341c400b130460a80a4015900000d00c690160075000b08107a00e960207441402c2c06010302419508102c0e1455594004a9800314004d552906d60000004001640c503145400c841d021035594460b07031031609031220251001a0041e015120303161190282300b0b41d00c90a04d104842c3c00740703488814007001c100400d0007144142d0b07018000e5500000d015038544415002280114400d020941d6141c3d1410030403584034040402c000c04070032103200c0c10460040711750000b071250701d04043c038903412042d181c1c0d4440c03c480500d418070080084042d0701883d030700b025403240d02280880341084002c2000541c0046c506c0f0100000051840f40d0216000c5202407203540500054480580126485030301c900b01082d0500340f81c81400005c43d40700c0f103001400540d0300c000700d04940c1e02900a05081c603182d5038a0783d0b80b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 170287634 1250 170286384 170286397
    0x6180f0b0a09050a05010b0102070e01030b0604050a0605131b05040501090b07050102210a0c0806060423040c1713020d020f03100606090302030c090108061b090406030305030732 78
    0x100c2d4440c610390020400920101203c60b10074400003400d403500200190500700345500c0f42041c20310800041002c2540762941991011049400042681c0d03951162001424150411780d04944010080300418205a200500c03404010f0141c10000c00301d01001c803803c2c42503002e264001004200b0801110303150788007038400b2600c103800260902003401628140b210b402441c040451000405020398401d071482500c01210203803030305100d545001d4000c49c030144120300c154003a0080d24143c287e07062488038140c08881400400034420f00344198001020207204801007001c04030400c011601003403071030046a40307596010346200741c0e00c0d03050b07001c0040c9103000c4181d25806000e02c14034101c3d824618030070b4a015002a13254000b0352030a40c01031519094283d10054040d80c4c402c0c1c014010101d0000d00507900c480c6004c3c521080d11842c2c8a50300050151140d441e0f0040d08020022003050b0700315010790720402d0107641d90041030310800413542042c201d01c160094044c80c001e8522148440003070043c0072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 170288884 1250 170287634 170287651
    0x210903070312020f0a060f0c030c050912070305030c15130c030803070c020a03050708010605010513090c02030d020f1209010b014109040b2e110102120406180f0b 71
    0x311000003505541001750108088030455035406182020b8441885424032204280c82c0421111004040c060424801d4034a514800c400e81221901910020403661024540c0541641d07100c03c2c4030311895503220048031a407110403003943c00085a1041c8551100d82e0315403c50003078011035240d510b485c45540d01c0505424100102002880f0140c0c03961400702c0000c51040008044484c944140303039084403403c0d0019410040e0130010a01c190300c0881600c41030b12454000010311065041080e40745218150b482c1d00520f0020406100070913090300540079161001e2040e420664551107040d00300d0f440c543d151808030b407080300720b4418610b040203002c1406070740b500b41c80c007100d4580707001c00000c080d440380c05164407030000341070030741800c0c0b07406686205c483c265803400321015500140515000342205881103007010300c8240c42c1c510310440c0320510b100c6c59603008656415032074805601c452800c40e010781c0c00600384021080030513245441710b864035030000c0e01070b2000e508954a0f8100c2c0000640b0115 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 170290134 1250 170288884 170288893
    0xc170105060319150302030f0c06030c0d1e1a06030112200301090c05040c0c0c06030b0f060703020d0e01020d02030d022a0a0b0f070503060909071721090307031202 72
    0x4078141c0340f0748910703050760003840b0028500340d2451040518140500361408403a811100107100030307031200019a81c20050000e449622454090380c02001403541740203041034074070718594501d5504005d60040000558506240d642080d0480a000c3d16110030f115107080442c0709009071010420411aaa0034158070401c40c9071700300c80743c0001900b911442042502e0031080c1e01001c0006103001e00c6408090000703414105e00d00d03489901c030407061100c0b503c2807a0a140e00d40c0b205100c01d540f10b1050441b40c0000038843c030f13215008c60400969803694207c401d00811340c45801d280096000146261403000c4680c010340c0b03003228000e4490041e4100040c0d04514a0b1502c600c0c90316a401d144200001d407903210700070300541d0b03880d00300340d0050b4901510700f190a0b00784600b404011a40700c8116640040180c1d1400c0940d114a031754a440c00c1c000354000030031130390410007852158401280c040306c4041200e00040766000c2020380e804042c810031490b560f055004450800018482464100f101341036801a01c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 170291384 1250 170290134 170290171
    0x1a09010905060409290117040503040513140f1909030908030304060e06100605040608130c08100b01022b0519030605120105070c0b15060403050a02040c1701050603 72
    0x4000b500290000c0010580b1022008051117140400b040c0c81c4c102122290041c400c2480007804614111510780084090800000c0c280142041100c0c01058007400343d507804052030344440000c0c4440c2d840700b82c0040c071a00209100705d2110019238043d0400358042c1c1582c00391a4085002840b42603401c038188006000000f509040c00c1c00514452809032801160403d2681c0b03105081210051840f5000d0310000d00a200d080e50204c203440944071a03040270320003034840501ca040906500c120013804562104d40104003207101040807206141002d0b414440b0403181801641c58400d152650303646010510100124640d83c0800500c149070b00313080c0585070520500d1006604100700b0202c0001c02e49480e0100407038107204804411001e403000080045050120300140141c130b901002400540210b004200900c5070100c003041800c0004004555440d07076481c050b5140c10403001c0903071007980303810318200d2805c1c00780035054408c0e2500c95044140b607082c0740c1040140e80014002800c210007003c2032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 170292634 1250 170291384 170291389
    0xe070e0423040803060405060a0f0b0315041d120c0c10031407030510171b011407030914030102040e01120312090803060901081b010509060c0105011d010f1a09010905 73
    0x1601450041d03500f5903a9140000a110940f20040d007218050800c4130820866803e1400440050b107030080103641d92500c441d00c01080042c500d880c681c1d4810702d8280501c08000b107600088005140c4681a500c1c994081410303c0014014041c01103995004020318842c0c602d890183c40c070074030850b400c0009407131251841c022300d180022904800404d903a642400b40d00c4003681400310007046a8802000920082d0009940381d810540da03520400d4429048024143e000f420440d81d0440050084c40d01d620351402d005041807110701c10703040c4079214007410f101c0a05042c007c4a0640e059016002c043d64130300039501d000c984141505a04120300c3d00b02c09500700505009903041203000b43e11103500c07824803004000d0701140603844a011a0300c01d804007492003e5112001d52120800d0904070313201d60000d000305c1d442d4801c000180f0000e520700400030070310440004110000000c54030720440560b80350310441c41d0700c0105000e002d5180c0107008000880c169100001d00c80b508040c5001c10415680e50302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 170293884 1250 170292634 170292701
    0x6090318030111030c0403060e06150f12030a17060d0c0b030a0b030304030c03120305010609050d0516090c20210d090303020a030c020c0d03031d0f160e070e04 70
    0x2017188120b00000740400a2040c24011500c00501205c00b070320443c10035a115140480c0f50044044c0598019108001b055899459121a55600f9029282c0e146100c00008065107e0041aa500701c01c0a9010440f68100140d17091040341d0321181030800d035802c080f54041e43c3c0d040240020036250f120741100b96a518244003030401180300700f82c401034060551601c040c401c00007020080415103404010880c07036502c090030204803402659110013030b015034108903042c4880b1600301401d030344504100284490b4164441440c200340e583e1010114484680809100701c4103c60506040e0301600d002d00d07841e8200c425504c03510a03019000b51801d00880b14520580703650900030f9000c6540810303806199901740c058010700700030910107410204c0c0e1000000c1c0041e5030450001d001c042d52144405852034603581403a003c246100119103500c2140f01882e41d5a01c2110301d8111800c400c100009044000f8500040c0902c1854030307544200ea0380003080c80b0041c5040281c000c00a0703895500b901e00c440b40181d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 170295134 1250 170293884 170293891
    0x3209030d0f0903080606031005100507050601080d09050d030206060f0604030b042301060b160303020909151302091c0c0b04120b0f060d0f05160902070506010501020609031803011103 80
    0x105075240c240c1070184c60060000d0859005107800c00820410001e800818000e031401211b01b0020343c40440c00844440c01078000080441c400c0c0b0001156000b0002102c900d11800d980e6103060301d948844c01e000e000072031100d00074056440800031914a15003c103503a80c00310f0024024500b4181e980d10b580e40200001c0e1404d0300c0400c41110740003001d0f050781c0394890365044140024450640b4040140c0498820740c40b42c840712484156100f01054403c0c3c0407150306100040801606040c500301810210000070344152080c0b100344c12700c4090300310600036181c0400005290400508078200540c898109080040b502400441c3d4007092410f049800b40002d040400d90207942c070041c0346040e140314030b0041c0c6034290428000c000c00078150f40303040132100107a42c064200e00c0050302c00d00c1c040745001c1c4d10301240f940400c0322900100d01d031440c56015040d80d902400480d80790380d9a80e001a82c03a20016600006140c008000841a4030919902d4803080c48010300000b8246040f181c0c040501d03002603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 170296384 1250 170295134 170295161
    0xb09010e070c0c090212010501020d020a0f060612082203030f0f1106150111010509030a05070606050d08030702190c0b1b010c02010204240504170a0204050f09013209030d 75
    0x1286100d42e0f09406d0358442d0140c20280020040c50140a00195540991034030081491080f10084420003529030070000040c00800940c000b081000c0c5024120f9401c109281d0002009401240401074982035014080b81d801d91941c4c00ca100c4511011105601c0200000b014042020202a0014420080746104103114a00800341c02d90b10000107019240031004001c1d00d80c104010310810700c2c00441202c500d00e40710b0602c0343d03035884180ba200018200325400070b9480040c103060310040c4810400154480e07420740e0b0a444c0300b001100380d4031580703140500001e0058214904103124043c028002030403100200a404d14000c44080d001d5802c2d1100d6000040040c0d4012030b04000070045c580c1e6804c0b00b102c0c840204519078120b18070080c881d000d00c1c03013024446003200000100021040c1b2504003000c0e000b80c014031407454003016400c11400191200041c640c68031008207550b801c5070f40021401201c0c420340c1d20b65454103907000e158205000d00202c40c1c80c0030030401c1c041c400e0f44a10406209003401d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 170297634 1250 170296384 170296387
    0xf1806180f0703051209010908060f07030506030a0f1202030904110c01141302040902120312060f06120604090201021c0918110a0315091401030b01090b09010e070c0c0902 75
    0x40c69060801c0807001568609500c00e24041c4000ba40202c0c6100107a040d90464a48401c5103d00403982e06c0345592100b851801a07405019100002100e503c1c0300b200766440c00e020ba0f40700c807814159102410f00000d80400e6006c500c100000340c602200021050091049031704208402d800a4110b540f1065628115100005e200b00c95810a01400c51400030403203145541c0c0c070f882200500943d1060071b0081c0b05543d541035400841d5900078403d0307101003540f421252254012025a010248141e40151080040c040414928508601140c0328010089180c25880d262807080c80060002c400f0204e0650103001d1403400000c004c1145045048003941c0d030103062070318240c0d4a084001e0f1416112007094204a019154441c0150450b0300704800c0d4a40020702d02e00b0000e4480c0481c100340c20003020b89081c28440c0a8007940303001c010b8141d80c002e9a0026143c1d982d010980100d441c4e60186680148010004000e85041c0c00324140d17100d0b48500b0004004c5c0304a5139500c172071400702c3d00300368000ea50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 170298884 1250 170297634 170297671
    0xd02070305190203151b0c0d03060506040602030405040f020904020307020618010902330d02070c0e042105090405070c03020114270102090a060201090203061b030f1806 74
    0x401c0040500c5000740c00c500442c40d005907000300c2d031590817010010300d44020300300101d041c030001c8500d4101070030313050495a911441c03900d40b03054407a504501e2040009080c01303070200b40352070800220780880711143c00451030f00389044c1c24000941044814400700950078490103415031110700046110762207940c09814036250800349144a0352a0181c17400d6982e24025000300182c4480703040a40004500103101801600d41000f01c907440c840099038519001d01140358000c81049402078404144280701c0d801c003551f02d80ea00541d015000300c8015040001030002030f101c840d005240b9034400511131800c070b4074241d201c20210301a17480544801e0000784a100c002400d0680c2841350a40e00048282403500074200b81048480800250030440b89900c01c102c509086164254111840100e01803d6501f9040c0d585401a0007440d10581c140d0280c000ea00003d48072285c0c0040100380440d00d00c8c0600e04689800410440c40040140707100300c4100044154031482004018031841510010883c620160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 170300134 1250 170298884 170298893
    0x1090506120312010911271e0a0510020709021204061a030c0108150904050102030f100b0a050d0f050a0f0c052805070c030605220209061905030d020703 67
    0x7500d50400390107904180304400903680f1440e465411601d1007000400c072100d5511045216200c0c80440401e00001524060380f117800508403c1c490410441d00710f03030390f502c0300e03040300401c8200450f2031030340507180200902c210b203010015880107000c40d1045840554681041030103e0f488025845081c4100c00c0801c000c21919000d081b0004110754581079100405e140400da072022942141814810910001209000c08210540c41200b005100b03440318102401d00038000d500c142c0d00d4a5518003d5000544a550004814002c0b9105080d0542c0360428820301218160085c00140d2101c80d1148191742c1701c8a101d001381030140184003400258000d66649400480304980141d405104080c0310407100c040c0c01e20381107040d054226224152441a1100c01c480c1d5109014000b416901a84408414406554046031040446c1014505000c00040d800c0c0c03008070151400070342c060b50010005102c1d0404c5401e04440700c00407000c0b90301c1c0e292180c0c0000c0c00c24030380018407401a40035560403c00c0c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 170301384 1250 170300134 170300149
    0x201050108010b100e0f040219050d150807060309080f07030e01030606020c011b0204110c0604060b060405062a12120604090503041511160501020607080106023301090506 75
    0x40204640301c10b840c500341302020b025045448045846040b0081200041c6c2e1255011200c45200180700440040c240203406400c0740c00000b99000610b14011900050071000b0041e501600d5602c8020b0807440e01e0111700701c000d04030584c0129005013003804444084d0501c100500320280c441e403039040ca081613000004040310351b42e600000841d4440700c0440314998100e002400409450b0000c01c940700c0391030000c540582141c1c414480b44200c0012412440003001ca091406140718001c1801000401070400c26180140d01841e94861b60401483d0b001d0018034680d410281c014090321040403100303c054a04000016004551805000070004809460131a1041d44608200d800700461801c2d03441d16641e83c0500d00420070290300c60880590342c1c5004010603040a5800340032584c028503041c600e1128400c480c0b1805025129050105045a0127400d85c030341694035590043c006051840800704081c002120500e0364200c4680035405640038000d0700c1406810548408036039400d0402c10710140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 170302634 1250 170301384 170301401
    0x105070c021906050409090609021519110c010807021f020406030606050f040b07022124060d12090915050a051206010e1005100c02120d14160c06020105010801 70
    0x30215502c01801034a400800383c43c25901c60010003d003071202c1e494194008c10074444081c1d84841c0780900b401000da00072000304500280001c0001441c1b20000d0103987d07400c1141c1c40700c41c59804c0b0340044485540714043e03540d40f01400707104a1314150009200003589030101044c600405800190921201c1d0301805a580200200c1c07400a00c0c6c0a00c022800c0040c0c0070350f000d00108120300160180a542d00c0d4a02440c1e07101d6002e82000081c41a0740100d50345001e1280b28100c0040a880d01c40d80c5402c0a0700750034400c000203451310504080750307502c0220002090610b0340070301a00344804560b441c02e80c4503801c90040b1000088404034148810411000d078664001d902c074000c49003d0429036031000c02c2840c11a0000c00040d00c0545030381400030240c02440d000300c0c0e0004058102100480d603c042c10080650003039804070311000300c3c542016140c1110b00c3c030201c080364500c40260401c41e201402800c1d1020420300c01200686c455607501d410000a0740303c000142e4460005020014003032141040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 170303884 1250 170302634 170302669
    0x5090c030c0a0b03010b131a040f060e0105030a0507030f0f0e210706050606091305040c090b0a05060706090506041a0f010e01050d03030f0e01091a090a0b180105070c02 74
    0x40c1e4982103010380a44414015071601180101c4c00000d240302e281281d4001d050804401c1c070a0403d200c0c05060549c01520a1300c1c542804520001400f60003604042914941039545ca480c1da034500c050700740035050240c0440100740c1c1d41d0030b941410002c00c2c0b0a840301c0c6c1c1d0b9102800304500500e950014a80300b024000d4091918101045c8509410301c8000c8441c001c0e0f200c440032070b195840c900012810301440f00001c0e00039400c0801a00403550035400244102d22130744820307039901c0d251100c502c100c840368000c4d00c0c0c010710408400d02140c81c0c528054400c040c1310b654041a8403006a9440b42840d60584049401e81032101d51880201c540300105136000001c016500882d40c540b2260224020041c803d16016181e940b0000040c140303c1e8000001240750207005211980c42c030820725000f8015035500b540c61100c48060b01c14a15408802c550040c1003c00080084034040c3d100d402d0644406415180d481c0340d00a10804050341c2070040714480c4040e5151a0005c05150041c003140469420700c081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 170305134 1250 170303884 170303899
    0xd1101060806061f1103040e0711011a040b0312130e0f06030304050d02180f010609060905030703061107050703060c0e030102030708070807020a0c0b07170304080706180605090c030c 80
    0xc5603201d030b105810070100c2100c1d03801984105240f045d14680030090308840036001c0000e01060303061000c414030340a011940d80b08140300c0355200c0712074204d4103002401d40c250b4020b280820880d2615401c101d00c01c02c0c008080d9038110300202c0c41405240c0c018507410390380340014042007001c0c40e660b00c1c1482c0d2001280948040a10f40980003c0c1c99205074003510384103c2508110790255100c1e82402c0c0315801d1301d44004451410f01c1c0c41c01a24880d024469280002c0c0b0702180821414841d55170a0100d903000340003401110306603560380003e00a0150400001c06080c09820040303241049640002c5004d50030001d030303135080340304020002c5041d0822203000382e00400c24085450360100300107070b103c110342c6030000c2d0944503030004904007103c035500505501050500412511640310003002594816080c0566104001290100b14082194003070700d0500241f000c1780111b1a981c10090b10303d00c0390581003444280c65943c4c18100d400569103201c0940c0140548002c5050803c1214501501100d010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 170306384 1250 170305134 170305141
    0xf1205190c080c03040b0c192309030709050c190503150a050d03120b1810091103010612090206040e04060b0301020405030706030b04091a0a051f0b1b0d1101060806 72
    0x289894440580000c2c10f03540301600140a13540741c20251016040b0382300d09204a103c0d4a40001e01c07003060508009032005411140c0e132070006510003160714041c405006842d00c940f13000361900040c04000c040c805d0241080043c000210f04c00c10105d2001d4500b03448813920317420400d0300394858031143c0c2d0b5114000c00910304184956a200c070000410a41d01d0f1800900d007100c9010010050700c02c12101e243c1008201408550801c1c001c44c030796101d1441115212210340d030714000c000036945d9000d05000c0c180d10420042c8000c40c4140c5c40d911646541150115840034142c2c0880d00d01d0340039900c904078200000b8184010040c0c180290070034500c04070001e40c107090030400060744400c100d20400041c5542c276132034180a034940350042100750342c001046055001c4030700520300c401641102da21001c2460900011002c0500902540b4501d00e003001c0b0000c514204202c2000742d0b8040903201143c00c01209031641c08030000c20410009002aa44000701208040d014900391080e40d0888000c641140040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 170307634 1250 170306384 170306401
    0xc01030203130f1a09070302031b0105160c1d060103050601230a0309060e030a110a0b0103030f050d050c190c110405040c150509090f06030c010f1205190c08 69
    0x80030107107904004001c0303034994180340c80261420203081e00b40d54200c204c42040000c58001c03500100322030098003510110106010245071406655030200d02080007072264031415807018120713102c002d22681d80315907115103920300c900760729080b0740040c441015000d04002c01540d150180a40044003030070305079180080c40001c3c6886001c542401031100e200400e030002e600c2c0c07080d003000c0c0301a07400c000304204030100758000d1512640048002400b1038094201401c104c00300152103e1116000180181341f81d080d0380e021914008501600002c05c04180300040841c0a9442841c0c0200c1c0e1711440b540e501c3d125110041c10089580312001c040c010201c0e070100c00701e00c02c449040c0c05038030111000145a907a41c9805101c0031100e0308000f01280c4401c0500c041304ac0c02400901c220175084030344007800e5450030741048400a08485503070b0184c214000c8251154001c0160b070010001c242480203140580c09100e000325001107400b03251969078000d4038100d49040d0b200d10785040e04186005003062415103003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 170308884 1250 170307634 170307661
    0xa06090c21080a140c0a0c1a0f1b03031003020a05010f02060f040303020715050109060e16030c03020915090a0803090a150e0d1109090606010c030509031c020604050c01030203 77
    0x400b80c424070340095079440e05446140c84400700900e0801041e11101091015543c070032000d0390445100c0c810540218801c0c0c0294140001110808041c5281034050b00301c050554004030b028603000201d800c02d41385a0b00f0240050752042241021101186140d8010419124a903510560501c4a40d00300c0c010340f5580488c6941d8051000000b82007070782c40714079003100240b00740200a40145584121205030041a40050741241d8400c202031002544440d00f00301580300964900d4088402404001000c0d0302035007001e09180c025080041c10076180d10701080040c0c600a018600008000800f4201e40c60312507800b01c086c10761a402142001e95040100d02015070502402c1d400040c1001c0045520b4803640400183c03c4020b408851400007510301250003112401c500c52040076004002040c0e03120004050f442410165105042101c0a45040da001e60080d08502c7d0907006101000c00158100001c0c1410503400c1c0c0c1c000c200c0c03413510f800d00754204001100094100740c01041444015103c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 170310134 1250 170308884 170308949
    0xc1d030316050a06021b16060c0209070306090203090c1f080c07060f0216060f050712020d0908120402010f0e0108010303050a020c03010c110f060402060712020f0a06090c 75
    0x18003003003148016003003031850719030803d200400351400001c0b400e2082944a084814510701d0300116850495400e00c1c01e90416418000c1000055407011090b003d480c00c1010a60441d8203410002521516142c43d0403c0ea841120302a81c0d6074881080342c81035080c50082c44042008036030b00e0403d10030f24018001c0c03c201c400303460b403042040701141030320501503654409500761f40840300c215680c91407400200f064265075601500c1103450000c120a030740d4268040d0b98410079a903521013080b1150300107074000940100b011080c485542d000400002540c04009160480304580d500c80140380c10300c00141914a401d0a4030300700401f11041100c01d9070004807042c1565030508000e0344890b8250341c200d1a101c01048459030540c200b0750001e10003a004034101c545040703c9001d80798840803c24040782c0d5007505440c02074101c0030410802000c0b40910600481545861041c0c48003c0c1e05070100da0b01e000744c0d8440c02d592a41c1d403a0230030401c018030046900c1c000c02200440c40f078114000e1505910040c40784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 170311384 1250 170310134 170310157
    0x912091e03030d02041212020a03020d031a1201020306090c040e040803060d0b040b040302070b090303031914180c090c0d0507020f070303120506010905151303020904060c1d0303 78
    0x40c08054041d079810300586040d0001d5960854403250748000c040c2c2e0345600c20748140d5168000701461044280f01003070b0324810390b0701134000301003804143c070040300200190230b00244100c8600c034000b49595110001103a01990a200160b103d0606030100809800050086400400208000c1102482d03980c04c069126030030200c070304d40300d40c0c548000c0b071103433140c244000300a8514402084104400400e0841c020350096003112199900c88403c211075114100c0080d506d540305000051010654620792429201c2e0107501041600c0c0f2450380c1030b11010240c1c0d24515a6046c4214a140350388100003044039201d00701c403134848070300700f4164400240c4540f07181e031046503840f05c0005a681c0d00170400c50341c203414000221005259030b81001002101c40c282404042820000800d407076602c145010320640d20300805140d15208a40c54810b0350345d10029102580c248120000000340e95201030103440f0f503010741000700b00000401030050080c032185c030b042c15801c049100c0300c2c4c4076074800206441090011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 170312634 1250 170311384 170311429
    0xa0603031b170304080c120c0a02060706020403061e0b010503101404110d0b0f030a020a060c1103060408040602060a060315020d14090102040e070c0308240307030803091209 76
    0x794100051100b52150b00445507150000c00c0c4420000690300401400c0d01d81e0f0f066684424203050024107910a0005030110380d0310515048016203040c038000c080c5644240c60051a041e0360360358440a89010001032405098098814511a4124007130403100360001d03c5c1007441d40c6010259440c00101c03d010b020750424060004844c3c80d1a680d114001080c0680c914a0304e640d00140c8140c041e0035004851070060f41d0020001c0d10504000402c0341c01c113980200106082818860221a90404a02d041e03c00003032222050025071002e02450b4080c3c0c0c00381503143d0742d5508100e07010345803d41c013512100141385809000c20100300b0380c0c45030b00304903050031202503554660040307808089c01d180c2d2180d00c0c002c040c00b8203204081205600810032140d0445054199645040d0181c030400c1608402501142581002a80341d603c40108501c1e0040c590450782c07940c034203100101e03140010b1504100d490b401f0000034000b9880c000c00c40e81c5105071400444a107049162000325280c1040d60b00720400d00c014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170313884 1250 170312634 170312687
    0x10905040b0f06010e1315091a0607030210091b060807021f0204050405010905061908151e040b011724040c030f050604020a14100e031e0708060a060303 67
    0x2017048010185200104000a040d04101c003a00081c080e0460b13040801c00c4010b4005500c2450713008401424105511b441c684900324401e01100da413049100328118000d0a859080c941c0c034070b00c200c9041d10701900c09819030522106850000441c01d8120a050002e11400c1245290b400181c1015406882d0030780c03642070300d04800304400f038019031308074507841800d160020a4000300d607030020b40f00d080304a50700c104c02502c0c650540c0b5202d07070310300420456030440c01074011403400340030b0a039411464004030a00304641c103400c4040e2079007091f60f0468151482c0c0004011a0120307920b5810a508a40b02800031100460144841c5c0c10005405000300114580001c00388900d00d0710801c001c603081101d0526078502417400907260981210308903c500003050000c50004104040100401005030805403180b10800041d650400c0192686905104011864a100200358170a8200d80d468000409c100c906100070507042000c02009880748130f180030070400129604c941c841a0098608206d00c0c41100b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 170315134 1250 170313884 170313887
    0x30601080601050c0c0d05031b01050405010b040615110309040c0c030f0206130204091506030804080d050906040e04050c042c0a050604080a091505070515040b0a020a0c05060f0609010905040b0f0601 87
    0x980848525418001d50101d441c1040640bc45031217540720ba0000c010035000030007004203c5010f80140640e1101f00c01049607140c6c0100a890040e880d180d04490905924500040640c1e224000b04800500f46ca84e9440805400000f41e01d110489400a00141e1800c0c0381da01c101c0f8101c1d11400707842942c5581601081c4140070400041c1040066820301110341c82742031805807030b48076100380b1b590b500c101c0603001c4050b44108255012680000c1005142c07a01d40000607000b9000980161080d01038a08011015a03c030f01c80e01024135924201664910401c015083c1184003e034403030201500420b0b00e05000400c013040700d9a0003507200c10a5030721404c0584044401c2a000d400009229001d069400f00302c5070406c01520300c05102c0c50840c2e809100e4a1030414000a0a9800804046000c404140d01101c40d802401d43c9250350b140507900120140c0b03949240110607517021800000b0390041c030015042003c0e03918050b0410200511060900c1c0e9650040c0d800c0040013080783d04500b00108007a603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 170316384 1250 170315134 170315137
    0x40f20090109050a060f12020a020c130b18150a030f140703080705150a020a022a06030f070801060f090603090206040815060405010f210c0b04080102030601080601050c0c0d0503 78
    0x1000c024042c004013540313079040078129940081740c0e440450040c100a500c3c6403654002c43d502100e02d9406002004111001e005042d01104039102d400d54a40c0c0c3d10200b03640703075101c10030f000c400c04920080560502d0049040008016080c0c80e00a80e40d036001400400c2d6508007208070154000d254144001000c00c10504103900d640000740542000103030030040c043c000038118030302c42000e03200c11519119032400d07100324494000f407800075801c1100089492440a41c240d112100401c1c0000a20703001540014080d6004a408240320318214003400000e642c884410b6014000c641015402d503c80d006014041c5802d6200704c10030103848046080442d110381e42594020034200e0b04650400381500d401101010084452a014624142c000184161030502400895140642000013001c84100200405c10002c0040c3e4001c1442d1030006018000080100000d003500720005841c0e040810004200020140c940c0741041400d1000b20000c940c040b60802e48007001f01d03010101c402d42c80c5002400d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 170317634 1250 170316384 170316389
    0xf0f030c140d020306090307052a010807031b030e0d02370206030f18060601120209060403021c0326070503041a1008060a050403050a080703150311040f20090109 71
    0x5005d85803e00c604c550000003d444c0103840b40040e17a00c4142c83d207000e0f200d04181c404011081009400d10345c1c1940d4090180346400050514000c201c01c5180101c280030607128100c0c0c4000030b9a03502c2c841e07414903014030038428011030394406055007d4019003c844110400704d180320307101c50429485100c03da07070448914a846c0e4003400c40760303c0b03181c81440c1e81c04204c801c464050340504540c1d001c1204440c00300c0c42602c2000141c45001a001c18400c0d05802508441c4800713421180400011015903518441c00702c0c0c0c4030000310380c01c008a41a281c020320b014960540704c01000100709144c0010810120307016402072a61402c162260341d13904000c42640000950118481a5030040c070595101c40291002075400306e6084410540395004450229001150007400040c0c040c400803d29901c68011a5004041c034580400d000c200c030360300302d02c041120380c0c02103805401c0070792103400c24201030183c080c12000c1443c040007040c070b085a1200b8200e41500504040d1140028000c00c9603000d401031001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 170318884 1250 170317634 170317639
    0x5010f0504180203180d0f0c1a0109060f0902030126011d010b040e0f0303010e0903070b01060f0e041b030b040f02030a06031e0f08130e07090f0f030c140d02 69
    0x1440d01422510b00258030a90700d0740105941000245510344000414040b030040c00d0769101d0100701d06a0040325a652022402c690b02c1e03055468401141e00f101403140c0c0a080d501c04d002504914001030030009140302d0f88030281590043c001082006407402104514105214800c40d2450b20828030500525903809011043c00c402c03d000e000341201540319050b00308058801300140000d03176101507039651400956400b00d500410040c080725100c0030702c0c0b40d0891464001c490802c2c0d00ca5603040841c0c00240c00c1000062074100b003500b213041d445402d00920084c00d482c100000810401206143c0e01c0d69613500081c151210340380e031740541303440c0e21002480b99021000c40d120f003014903480e400f4102d0303032009440d56100340b02c034004074251003401181c10b5035122260b800c4606044d9600845a00f0035502140031781a2444c0008401d40c2041c00300e0b10503001d990714a0750300c0c0d0800410005c59081e540168000100301401800010940711118040d03560510f0500c8041c54003000003030b00c48801620094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 170320134 1250 170318884 170318909
    0x20702030f0609011b1b1e061e06050a0314030702130905011104261e0a060507050309060f06040b04050109140f010b1204051204260c01050d0506030a0c06050a08090304060905010f0504 81
    0xa0030320000ba4414000c9c038040c82d4014880080052100d41680d25502941d0f40c01103c032102040081c031043e00d41c0810900b001c06403070821086800040c0c2840c0500038000f1030b262240d14010420900703100341200c0303451001180b41060704000c0c00c0c0c5e94401000c4081041c40c0145a0800c0340c0e00c004101402542160310b4104e035101d004415a292a07060f4400102d800710304010200ea0b80c00d00a03011b80c0d100b1800f0344004c4c880b9650b18580050303050400303408245c00c50b55900245c9544e4a80b4010355018105055011032201c002d002c09501e2144001e00c10404041d401005120300c0e0842c10485100101c030302c030040c6158540b0b040c060308085d091650302c0800d650005000412080c0103030050005c07281d40c0c42483c0f4030700c3c40780d503895120005000c001e40001c90400c40390030704406503030040d0f4000300702a0444180340c4140d0349280a610039600042d001c250041070035140f02d5400384400d5844243c0e100950306151400300c024020007000d0080030306003c5000e540c440e19a200d5004c2e1001890314180c07c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 170321384 1250 170320134 170320193
    0xb04030c06090b181801090c080f06100804060204030c030c03230c0f060c060901060510110606091305062404020423120105070903060b040506180a020702030f0609011b1b 75
    0xa0003010728048c0c120100301054002500c80c18401d0f81c0c14400c9001070302111240c000ba4004880407403004104507030940d801c5c0000300204c1e41c2c0700c0410019511601081002c6800c60071b04000d0704803000c0216054050007100c83c4641000882d91402460301920b818600080e030700700041185c0114800c00e035a520a5a0802c5140c8105404c20422502c064070680d54072000024100d46503654191044400e90041c00032803084e08114603107a6100301c0c032a1084100c2400c0b0742e80e490034120207130b80728201d62986040a810000a8210040540300200c07411840d080c500303049803940240c3c0044c0a81e400b205280c14949585821070136030380d294505c8ac0200413a03c1c10310320162030f4a83d14003090343d215140183c8a10642414031a5500498000700050784030041a00c1003001910003c04501c0e1464091013180b005071410401030b695821948050002860b000c0c46480c00c441100400c200d88200d03669102d0701c0035801c030592203444980c01030070341c0c606c1016080ca9000c00d1010407405d03400c1094050704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 170322634 1250 170321384 170321399
    0x309030c10150503030708071203390e0307090e01090804080708060a0504080d09060e150a0e070b0d0902031612060509030c03160606030c0b04030c06090b181801 71
    0x5800c0e081c0d044080202c481d01e403018940e40e80201c003401440c0200811000020a02032116207142c42c00074038011070000c10131181c50001481640340c581041412940b00052081d03c48044040e4940c5032812074040300c80d0400203070b81d415162241e80382e100d0f82c03038414420b504803e4010300c52040e004010765a4807036880119503070301c1c0564411141940078040101d100c900383c0c0d000b010b0140d0b410081c0d00b8141015071070200014440010102c940e140c0d0740000f525004c805100d20f0070182e030307800d0329040319240c4641104180c60710105000c80300c0c0c0080d001400006411020b03a00034508031480060070310f1070341c07011905e00003032038190a01c035014104002a0210003000d10071080b40c450700c401d003e0758079403c406550f20302495140031800d030400d1090051480ea242d0800740c00301d008000105406a4a440d840e14000c01c54002c40034013071000078180b06100000c401e420043c5940d19100c03886601d451040501800344003803d001415600300032030059551100c52400201e006c030081e242c1d070350b965840c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 170323741 1107 170322634 170322641
    0x5011a070615050a0803040501091205030a0516020a0b0703031404201528020705030d110f120a020c01090b03040303020a0513062c13020309030c10 65
    0xb03000903d9921214684c2c01407941101955550741000c000402c080300540180048581039102c401c0010030002c1201c420760400c0c81d08a80320442070381564842070790702c00c0c0a0343c40103d9907000318490310a0402494540d100fa2410040e0081102407510040011600606001134000880d441c0d00c188400c40c40d00d221300100012208821402d60022581103018081c004c01c0d8440c180d280f4400c0c003150b214200c0403450009040b403514010000f40c1c0c40a26100c0c8408000b0428070280180004103c942e02007901c00040d60745800c03414205111316004013140e500140306980b01120554058039140003a600c15841491456aa580301500a5070240c051b40b42080740c2007144011031404098100b0292005507908250341d4030780b0030b4000300035800054552030010b80050307240e00d50f602d40100c0d03240c01c400e100c000b58490760340c0f0305041d0440c01820b0241015000e064100043c51540e5032 = true := by decide +kernel

theorem cover : BRFrame.Cov 170143884 170323741 := by
  have h0 := BRFrame.cov_init 170143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 170143884 ≤ n) (h2 : n < 170323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
