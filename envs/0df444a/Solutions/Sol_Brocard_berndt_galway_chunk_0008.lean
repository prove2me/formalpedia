-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:20:05.853064+00:00
-- url     : https://prove2.me/submissions/9b638460-9c9d-4ca4-8ce3-e4aaffb4eba6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1259000 ≤ n < 1438856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1260250 1250 1259000 1259017
    0x10c05030417100b010203070605041704060806040e030c07060c020d0b0f090d05040503031206060403020307060c050c030604020105091018080a020915060906130306090b06040e07030503040603020a02010204030206 94
    0x40c450030b50501c420141c1403a822051944590b0b19040710643e01780d0f800015610319940c80040016903450b82d080c100440c40d81c1608641701c60400140210b801c680c040358460042c04251404e0001d40910030b2091785030f0084164031038842d48400004c2020f180304410b5003000d45d00240403d10107100548460000040072204000f0144000040c00383c02e21013005581c42100044c0707480e504180c20303c40003a48a2040c071400c8502214030502280389580da800c200c500a5a0090450b50007907030b0f40c0006004031b0f0034281d00703503054025075505210500b03004c10443e200c0c80e81603507541e142c10090303801c00c008089500740410030400085989480d2440002c180b00c003030041e9100404900b2121720401c0a6040c0050031500c00c000208010209034907040e060320028013040f42d9158440d41e13104c0c050340e02d9008139071015102c075040c4401d0005000c5008032817802440181c60910600e500088661b50b0354101d031100810560080204029051295014061250080c80058503083d48c84d0005030290b00803410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1261500 1250 1260250 1260269
    0x209090411010e10080c0705030c03030406060509011203090b03070c06060e010512150105041e0501030303020d0506010e010e010503090106030b09060901060f080304090203100b0304060b010909090b01090902010c050304 96
    0x1206107543c3c104408806510007220070311030007100d03040000c04801d00541000c000f140d000c980710082000900070760303a0b900c55110460b5200e00e41800c222300584254072130140503602c80400850340424100e50303a441b4035010380f01c4a400701d2508000c0703845584000c082400f00805540c82100083c41030041000620304030b505e01440394101020800005004604820750303501c4104420200c0f00c1c00c400380c0f41111030407600040c107110003010396004000c0490070b0303d00780c2d442c14001108050b056030140c8010200082d0400641e940d01e40195811184840390710301003103203461005c0305588a0001164800030060010526a42e02d60b034040f68460242d800400541002040001002d000d04c070783c0d0006c3c883e5000300307003800f440c0800b016120700c518041d110815800100080c01c0031000700d1702030010052410706541d83c1c50700e401c1c194014084c56101e180001c074140ca000400d482640103418203030b50042940045640b07801103520090901d0b12040b4144040e001114020440030300107400240309410f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1262750 1250 1261500 1261523
    0x60a1206090605070201090b0112020301020f030903070c050904020904060b0411071505060301050610030507021c020c0901060201050714031302030a050a0605010e0c0301030b060a0302060409020901180302061c02090904 96
    0x14003070003030303078001090f134011a850200c0700310100c1c3ca0211034a046403000e200341012140c40f400860b000e40316409044502030000014050300000000050407164010f9060b10003190f2034400304140241c00341c80c081d5020b15a0004140854602d51055046401c003e00000b482007008c058409150445107055440c400c01d054403065a0750140282070388050700f00c0003080035240000000301c251001c0c62200080607a0b500004039801d008011003880d0b103520000e08910b41c028014004c2d42d41024901c40c038000d468902c0005041c0d8014040c0600800480c0ca07413549084200d25198055003001b0200c110415014a0980c0541c500740300400540d4007480181c403040388581031001c1907031070683c01103a0040d002010840c00c62140c1c4180da06480d0701c451410b2190f03c0c0c40c00014200b0400b46c1003c0c0d0b000c20002800140510143c3c0180305060080e250b00c00c0c1003242c108410b41511180c400070790031600c10071105286424041002440440633240107003441c0c00140400c544841c01c0320200d901c000c0e102c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1264000 1250 1262750 1262753
    0x6060203090f0306040201020601060f0c05120702030d030519020a05040e010b0408070b03010e0402060705011d0607020d03020304020604120206040f0801020301031406040201020c01030c1419080105010507030203030609060a120609 101
    0x105245102902d0640040c041c03414581d0000303640740014450502000441940e95100c94803460719441d0007600b14085a0031b0580b003011400007640b000404030300c03034443c4410105c040c0b406401801d10030981c0343c100f201071611082212020398411a859003c2100420000c5024101450f07542c0c040c00d090300c40b142d00c5da814281c1c05031500100ba00a00c2400c501400100503803a4000c42c9103910640c19290291107181c149030590240410440c801002005541500d9140a0024031203200311810350807255007000c2102c080d8200e10060300d0107074000720104014080606901c543e8159584050301c030f580340a80c1c480d56452407400701d40000caa0360350000010418040440106103101c42c0b1040036080c60304103940042c0d502d4254a0000c0c2c14580c4038415070803443d0040c0c072840c50079160740307425690750310f0314031314441d02c003e04c0081250200e0081c50020503154407a00a0b54040c50340340e002946503455800400c031001c18001d120341c3c0d104c144c503070000c40c1442000c0014803c03184160700114180c8410f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1265250 1250 1264000 1264009
    0x50f01030c0812090105130503010504030201090501050610080105120c0303040303020304030c050603070c0b0411060a020303010312050a0206010902131802120c0c0d030e010f0203010e090705061821010606020309 93
    0x19940042c4459001d0607150728080009030460302c5a65003400e1569484244548801420300a6409503915518010401090607010b4105a40d10b0384100000c10a030755542c1c2c100090b1004080759072001444c20300c010b01c840e09180c0e4450040000c440210703510403160500003459548150400c41c016003001c02c0410070441c140c0820005401c4c2100c1023411407500c2c10004000c60381182025010208400214050003002d10b10840c92130001b40055550f4100715001035a2a8403c0c030041720b81a50903581044180d12030030681d40010001d90161050780d19020707484001e500101d40c8031203009441c0c1000903100c840c0d1100300000d1003480c0005130b120108503001900c01d0038014168080c0c10401c003c03805050b01d012441006020352801d00103181610529170307600403c07000c045491114030000000c02d18030040004c141c80740071aa822102c00a40303603c1840303400d0080002c03046480030003c402c0100ea1070003540700004d95612081620100c10140202403c0d9501b5601030009600001380c01c8840341071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1266500 1250 1265250 1265273
    0x609010209090a09020a050301060902070b0a020301030206030610030e0304120303050601020706020c0d03030204050909010501030210020102070807060b011206180c02070803030403080408040b0301080c0103050603061303050c030706050f0103 106
    0x404000031420522810040352603604002e09659441d40d41c0c031450011959108018005024098000c2000c0ca449a0810000703500c01c14060f29960104800200c00110b14000c0301c0c162a4060086821a1240e0091040c8201070a1000080c55129140e00c0091803081010340010000900405100015810081c08484014203210304540010000348510b540008128100b02c105507462403100c8210301b8228001e019a400c01540f080200040c8140704005400c80c0e410381f4005c60b02e010088512080982c201d22611038000c5c140343d003e01104006c20a20f920500c515001070516800c08201c95080d01b003202d0307072500701c8103c44580d41109826094140315071100120b1600080c10280d05100c01d160f035a000003880181046101c1000900300321101d01a14000c1424645464995031501c03400d6031034407008402c0320b0000b443c000000d40b4034607001421034007485682d10080c00840c81500c04a5280e803055941000500c8200203110018a403407144038070607030043c0c2c50400326504501c1c4c107090328071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1267750 1250 1266500 1266511
    0x304110108070f0206010e0907080a0c05010e090106080a090204020909040b10150203031b070c03050c01030c03020403120804111c02030601050307030507090203150901060201020304060615170a0902030a0309060206 94
    0x8043c1041031038181c0001d50a4103540c00d00416582d03c1c0d54903d911440c110060708041ca890040b50150350401025488030401c1e16000d03241c05590304150011300007140c03824460b800026070440003040e85040164001e0340c0b454005000940b4000c22440030803a124002c0c1c0e011a0100303480c1040181000b030f500c3c54040905221082910705143e001002540c07400b01414005850740f0a92051003083c4052007240c18080d8002d0b0f150041e513a49041581d242c03030b055034045010a04098001c414035200c0c0c4210303030940b6444030705081c4045c001441242c080ca00180304480a580e442c2c4801c29aa0720030f9580c0d00da800c14030340c142c0c001003c28414107007803000c10b07800240a5400303c441400001c0002c940d82080d200702c01c00040c0c4907918800b110b43d458008441c1280c001032084000304803d0b0b410740040d40706600481e020b2100c250340305c81081100c0100e100c810001000c0c0c2c40000081030341000000d4000d461000041603c08a0741c0000703080602d044000c4012031499042003007050340503c1090383c0301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1269000 1250 1267750 1267757
    0x10c020303130809040b09070903120203030103030903030305091006120302010b030d0207061d0603040309050316050108070e040204090e0604030f02030a020c0d080c01060b03061302030402030d05030405070b030411010807 97
    0x42c1440348040c1900e41100e2801085240f000c80c03014440d4035280d20600300d049004040c2405800d01781c0d0080c200210500058409035654031404605a00000440381242d5046d0303101d6010b80d01e1502c00b100201005081e149150003284c0c0010145402c40c01404050032040c1018550607085140103821030b402c140d0298000c0d004004070349070a64010902c88100c034468140a442c1343c4410ba0300e091004481629250b000601200f403105040d0300481031405e5a505804551320345180801409800034680b04890010b604240040c081610400a82d5441d800c06000076003002d0700e4000c40d4040d544038003140c26041c1d116074204418544e110140f04540c0c070441c0003841c07805c00b044800075207420a00c216580202c0240311000100480350040b20744019014000700045520b81022030101c0c1d0041e41c0c02846401d102c245d00c900e469032842101e0007154000d0003090300d003082c608103650680004100351420b0107800000603986a902c0003c40c4101e12600ca13510314500301c0000034208480141011040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1270250 1250 1269000 1269007
    0x40b040b06030f04051002030906040309060206090a060f090804030602030f01050619140705010e060414011406090402060910020d0311070b04020111030d0606020a05060108010c02030403031206030b07080603010c0203 95
    0x280e200c807012690031500440b4484043d42d51400d0003450001c0b4100d01e50740e55403000040100d07045001c100e981c003031031080e41c5845106a45481c226aa15001e551458158004184000006446600800f800e040025000c186030020791583d034241c0d0000d0348240d4019400008102e802d448415060740504000c440450030708128114590404141c0d50840051244000609041385c01500a49400d0390f8860000e002041e4848540364903242c05540403540c0c080e50301c44140321000d0600074500003030040d0850090956401041020800c8040c0c01a60485801c220a101a0303c903600c001d403030301341e10360018821080340750001821150500c46080d400c000602c000e800007158001e845070400d0b024079060541c000144000c42c114400c40c06a502010310307142c0c00140e0540c000c941c01810a004000782d9200da0f0b039440d400c82c01d13a250041d00c01d005810402060001a009048068107144604400200300e6100d81c2ca209400e1010744000740814841c3e8108109480e0074091020072140c6840a1401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1271500 1250 1270250 1270271
    0xa050403020a060b0a05090103050c030106090209031506060705010207050303070906030b0109050402070201170a09050c0402090901050d031707052205010503010506090f030102030106030203090708060f040204020d0f090302030405040b04 104
    0x40756481201c004000c0c5131100140310590fa62580058041c0000402d03c4107103503942d142c0070341c0d03a5000000c100e000307500748540015112802d10035184000e0018000e4407000905550690000a001b051254402d20501c0440d020403002d102408034140304800850b40c034200010b024141490a45c0450105411302200d8003290342d00248040031039000ba1030150b1140040d1005070340d5104100501c52001b5001000c000140d03500c0d400c04514980220309a9440407a440140002d84c451525001d401610387e000400c0f9500309035801c155140e0203440d2012001080c00b00241007007609407500000a080480d0b490030664501039181c10700d05642500704021841c000001c0c1040c0030501c1690710a41e008202c0801c0c030340715a0458004090300a000b156250f85404c40580250010385101115100b440004290203400280b080c2c040c0480040c1d0711200d54640d0b082001035403281081c14101c0380c8035036407541404042d0043c00c00152098000e5902da900b0076086c4070031500a5014141304600b0840e01e03c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1272750 1250 1271500 1271503
    0x303020703081f23030a03030501060e060906042705040b060f0105030702071401020106080307050604060b030303090a0209060402090315010608090705010c1b030203030703050315010807080708060118030312050a05040302 97
    0x445140058000d034000e034903101c100c50b01e0644d90401d0380502a40100d90100355044d40042c1c140c45a81e02c0da03c032581002000d128090080311895500030804000c00c0c44282d03180655501c19505880c810000426440d148200740c0b1010385040f240242d41a0500007141f61078501c915000c0c5081c43d01e14210326041708025541c084900c076100320001150302c0c1040a134801e400c03600c00340881e02d0850b41e44d14002d00d4504c0d0707503583c101c41c1a15003514080350180700e45000f2040360300440c2460020282800355400300203010340090449540594200b11034007981d1028054401c1c0350802ca0342444041d80340c02000341108200410805d511307000750030140103503a0400d1040401070740050460120306844e114446540201c1c2d00041c0d4984804100041099030040c01180302d491041c10f08140c0034120001554020790035074410300805c00d1900000e50b2140b00306400c070740c80f11052404c0280000c1020010b2412400c0740c000b580011142c00810015040a006958100c81d204008000c40c0c80c0a4400a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1274000 1250 1272750 1272811
    0x80a050c030f0c0903070602060105120a12030507090302040e030304050c010e15030603011104080604031101020301030b070c050109020405010b0d05090714010f0302040506180102060a0501030b0a020901020703050109030302070308 101
    0x80031001d05201090300310300c580f000da4508501c00740444c4c1080c0d07191440a90303070715001d2151030b2260240701c004100e00400030031841d01560b4010b4509280c880c030b0329426005410020411003c1143c00b1000001507a204e002c0c5080c4000040c0155541e07050504116040642c0691000d0500a42c1146402c040c0c9032800480b0000e01c100540984a803180c0001901602d00e40e02c4281071840c0100307000c20052800b041d0306e4000c5100784c4940f06002c0042c5022400e0b80400d1101508551301900040d51b094050311781c130014644107a0002401001590008044503800e0f008054064008540c030014040a44101d41d040415800100851071618404080c02c0003296102030400c800e803401000d00a00a40565001d0900248000e4503081c141507000340034400028210300620070840403442d00d008503c00c050580303800216429a699800401074023a51000303410700c0c1107108228001010440078815010305074400c1c1d4004d030707582003036003002065094040c01919020701c103140020709480154217003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1275250 1250 1274000 1274011
    0xb0d050304150c02030703140607140d0b040b180105040b0a030803180f01060b0702090f130204020913020414180c070605060409050a05070602010c090b090d11060408010b01080a050c03 81
    0x116466a07246401c00c4400f0020114000e4052045403004020071548401881a001d01c035400c41e07883c0d583d403e40880d01041c4401504001031010810485c00b41c81a4000d062107100203080820820308070408222103161b09010140c10441020052100b40307010300440714007030011100c000d405800e5171520505480040c00c80b0b0342200c0b000d040c40490a40c10300c20380007401a400000c2003010b40d5400310700c095504c1114100d104400220020b41408000c80700f4074003800a00c00b5103d0010126070910000b5030100c812581e00038041c030701d80201c42c04140002c0020b4020301c0180c0564014100511076550510f181207444003062400700001e261680b4103591449070090404102c6407035034004030300201038443d00a4001c2c065604a2414803100080e208102e62a503030003003101001014003221980703d24040e102e05031004000b0080343e80b0b0a001000d80990050103a4656401c1c00c50024810358416842611309075180e0324050740320768004001c2030b802000d1200c00d010342c2c80c010303c0c40d00861000400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1276500 1250 1275250 1275269
    0x5040e0709050a1103040c0612020313030e040e030c0a0507060507020303071106040504020703030b01020d081003020607060204050303070c0e01060905010804080309100509070302030601080a0210050a12140105040b0d050304 98
    0x4503081030b0382d041441e0301d190348000d1030b90ba802d11f4202020150424000d550100d0600d640900351038a2901c01c40c0d10034000d00702500c122151540e41110054407a00d402075006441d0441d0302c202410610041003e28880c200620a0328040d00d4681c1c20220340350f0001042c040140000c1015880120441d8240d40e401400c10b40301803405400200e881c040d075044a60440d2011540342e0805400d507000c0021020260200c0d2684840008110741d1408101d48a00403480340755420070060401d440079114841c82408050b081680f100e0110340741d07400610054449140a05080085145a4151901609251524440413414400082c00800c80600f000341107500000015400d50001d102c4030303801901e9181c1c14001070810703000840d520945408164403901480c1c00001d0044000140303e00c4003a0f02a043c400a440041410b40b035a405c070400c580f007404609540d5500b4805c042c4203c0408840740d40001d0f80e654103141c01d00c000c50b000540e80300d018400150b202d8010810020a89040350515030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1277750 1250 1276500 1276511
    0x60f04050106030c0b0a030b040c020c06071505040308060a1509050111010b100504080c010519050c0703050601030b0109050606070201090b0c0304090203100614030408040306050c040b0a030501080705040e0709 92
    0xe005401404140e00140c18200d1013840410404d20000c001c100014050303034140f10044400c000c02c0200c0b090180c4100150303100c00980211400d012018105060041c069003112841800420041d200c08480440000e44c503401040610b280824a603009010010b1a00c04080200c9501904040560041da4140207007002201243e00094225000e0040041d1400c2d04c2100307014000303822070b08103024080d094000c9907400040c5512031020b46851a4030702c02c07980340c0200306c5a030507541c540c4000c0721341d041e600403040013001080b001c02105000754400c40c207003455503140c40c50751011200d01901c0d95200d14800c0025070007503030780244510240c1d5483d124071a591340700c40c2ca40e103103584103580c425203c01c2d001204004400b001414081c1c1154400c0e100e5007108407064072030f01c59612017110b0042111005100c05e002181159115650000007141c04503d00f40e104e032218215034000350340a10000362101d005110080d41480902d0003031000742c805219005602e8403103034417400c40b0300982102c9690303079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1279000 1250 1277750 1277753
    0x20603040602072406090c090b03040206040512060402040f060b03040201030509100c11060106020c01090902030603010f02071101110d050403030305090c040903051908010b070b071701060906020708070305060f04 93
    0x140d045610702d9038091828050070001c4c41d001c03407283c0e2004800080389460102c0004803400e09024100c00300000c0e5541054040c10032284001e103070009401a42c108074244400304140c3c4503080d0080c1c00d032400c1c000402e141d15042c410041500c41d034480c400074071400c044040105400e00300c03d50350050382c24240480c080e602d46503180c2c42c01d0804000002c030b00342010fa0150207241c2201c0100070201c20101030b00c04c40d0781ca80c0310a0342d070b81e02c907003c401f400030705007010400400318940d000d142c014070000e00205106c0c64002d5140c0c00d0ba08500e80903260f09044c008040c0886da040a552950300842101411240f907140c54050036500440c840507013459140d40c00915440c00a204001c540d050040c000c00081e426400c0007070803500105400d808031031542c010280524040d25800d07040750a8081c00c10b00d080c1d8540d03a40c003100342c4098070000500024000c03440720881c00e0302006011302001d6444c006241e1405100034075001d525407146115810240c4c0034000b00380046075181e03010f480a000204903481d02e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1280250 1250 1279000 1279013
    0x5071205130203060109050105030303270d0e040c030501060f030903020a02030303070f020d0c0503040303030207080904090b0601030b040207050c010f051c020a0801050102190213090203010203040b0405060903031302060304 98
    0x1100004049510301410030010900c41900007200034003da0860304103a0301c8400b40c20455600380661a0b15074018000030b008410780c4e800c602c010400c01c943c0d5066080c00010740d1898000704a50087c04191401c90700c811500b41441501e100e09068a0180030951511002505180c000301c1400304158590f60204280350080022541d06907000e402c5941c1c0303191441005040c202c00690b0100180240b4580003407181c411a40041d529400001852900c1d1459034140c1c0203502c0014100c812020610900c140707581c95110f404640c034044c0f00d43c00344501d04071000408840c041410180304500c14072903440428400620080c07403500c00e0030310428000c8034680550300b601440303e00341044038040d0f64400300d444064000d0422a12251100f10b15641c943c0010fa80300c0250004520081c5800c039030040140c030341101c20029510341c0d90000503070701c6400d8010900f680c2c401c450a944403006101480200181004001da020071709030040d50440c03c01000c10120b04044441c040d12841010020400340001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 1281500 1250 1280250 1280267
    0x602030901091403030603010c09030809090711010903020c040509030a0504090f020403120201061401090b0d110903030a02060906010b030108030f0708090409050a030f03060609170a0b070503010e13080406030507 93
    0x30400c0c408104285803d49403643c81e4411540d4038000c2d4286800010884c8c0610f07480f50a40350700c81c500e41d007001108400d200f801e4800910000030003039001c90200c0c2d4030000f0f208480c429806940a442d00d141050306000035103030003812800c240c2d4401c20078a150594007005840036a00d00c80008100c03081c07100700d40d074040c0c022030700050804e50400b0741075000181c0560011089448410504050140240065500c060944113089580130b00b0082850a8941c59122404200201036020f0a2803010004240703540c20041c2ca14003d40d02480c00d003c0780300320401003180140440502c0a20f107606110910741c490142d00d002c1700340c0880c0494904104401c600a82c0c40001024104000c030419034103100c0d6540d0300090341580804c1403410400b05d040d200c0e006280030b83e01e0507103484072030b145031299190180d0013400141c01607001b1110b58000003245c13011000d0249500d1755071281c0781c0d41441403024038007a000d1b000c01d0540f00603c001c1000540e5003800d80d421916a4140045c4980c2e030914281d540c0340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 1282750 1250 1281500 1281503
    0xc010906060b0705060a02040501050703050a030e070602010204030b01090c020309060309070317040501080a050906070c050a060204080601050909010b010c0204050a02130806090d02010603020901030b06060c030307020307021f0c060203090109 106
    0x41c00c0c0701021501038010405056540d000e00700300d481c01c2c2c40f40c0b080320040b440b80d80a01800550104540e00c0441d0151004141d0800319140000d103280e48040b205040c00c4058010383c0051750002000c00034800311800203409091890010401c420000c40080c1d40c0788aa506018000c0c10040001211010103001d00001503412904503200755150080c8e01c441c503406400343d0f90100740101d0104034290528819a80302d801213200410030758903400403d81c0c00c1241200e0840c0d8038445c800d8010f000070740b030380040c00c020030355140102070950610003001a0300c50000c02051141e85001c248440ca40e1b031042c0e42e80040380d01600d0010b240d407101c40c031280292103140c00f09100080b8514002814401c0080c00507c00c020101c203680040b50b081001301d00b81ca101d4400650f005010320300500105210480d02908940000c22842c505020240500d04541040700ca040241c0c001051280540c24501413240500124601ca0a88019011409019241343c2c8501519880d030220011301005425403040c15040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 1284000 1250 1282750 1282763
    0xf0302030f0c010606080112030801031104110d0204030b060105030903250609050703020108060f0310020a0e030f0703050d1e0f0e030102040b0405040608070312030203090c040504050a0201020d0519050c0109 91
    0x6508a40e0b02501918851282c10000b4404400025a01d403940482c440e0880d45035407500b01c56440c640340c1440c190544500981e100d0354a1400285820403040100381030360031040007603121071550402003004c080080c88141801400c0080080d400c0700402240c013015034007030300168601d003222000d9100841444000f001907140c1002d17007080c420001385000c1200d100740d03140261913446005000ca00b404000d0100c0d01a8000c101c41c011580c1a500035204085542c5000b0001c548040002450072000c0c050410361504040303005d0040c00740900c00c6180411050078054200800c001c0e00d04082c0386121040e00030024107410031004030f841400207424988000f8020741d100e0345c60b800006100d5016210340c0d8891f40c80c203140024088004140842140d4101521041b42c1010700c000754084c1d400200108114003130708000d881559514410315002d1401980240200f084e103200184c6024101d010040c18045c2c18002500d140030035038190420f0722603074174045460b008a2102c10307024001e4820003c020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 1285250 1250 1284000 1284007
    0x206040605030405070906050604050603060f040203010e0f0703020f030708060d060203090f010b030c010c0209100905040308090c03010509060c07030c0503031302031006060206040308041406010b0913180f0302030f 94
    0x3040d034010003031401940038030191500d00d641c0e00c0001e401c0328110f01c00d03550811000d01c820402450980095980303c0c1c00544102e403c481800000f5007280d00c00d0b0170582c00701140e4400d1015003901042035036441012810114070b042c42c40c410131071150000400040800075040c00207085e07610755130401c2c02e00592141c0c0540d128104500380b0394440400211411f01d96291405e500f41c1442c00003001c03040316506031940340042c50140c090181164005210002501849900080e90051485483c1c071450280d5078840050800d00d41d99410200f844c44403612913030500c4140000904e0224181c0c0d000400e00d2203055468046203000d80e00805c1000000d45180408410050018034140040c2c1080c2d01c210195946041801c802208851060146c80c00503441030380042c00180c020f04450390060f00a04400d0040311404ca00c00d841c1802c241c04c010b58101000c2070411407410b10364401d240740d0b090100305102c120800d10380c1c48402c000c0340d18068840c40302907009000b80350090044170410200f82c0c405503039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 1286500 1250 1285250 1285259
    0x604020c0604050601150e0a06030506120a08070201030b06090901060e010e0604030605100b030906060d030c05060703060303030e0106030206070206030c07020a0f0807061b02010e010201020d06090506090702060f190603020604 99
    0x1c03160130910801c09030812000781d1090443c8514000c201c0c0c21402088140a40d04140d8103c0c01421300401c0150888030824603100b10704401c1202c000a203102d01e5595580750440c0c40010207480302c140001d03002e8803080c056030049542e405461030654510f490001f145800010040f100103422800e0141c001400150110500645401540c400ca100d00c00020300b0a582d040340201d148070461305207105411030008200c0b540b0703180100c0f1602c14001c5c0781c00c000c802d01d42d46030035003400c2003541c1d181c010035030f0754000704201901402001040481c0c10001c11a6a14503000319006100c1c8200082c414100080041c00c50510002601d2006d50042c0c01140039688507004498200c440b40104111032052400011325144a0140c4049500c020b10180000341340560046d01d40c600300392481030555400380010792a1800a100317240040843c1d22011072107051240078442c204a024004030110740040c4200070b0340000c1400056006070002c0450316030010001c3c03401c8000d02031a0002540b007000001e0004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 1287750 1250 1286500 1286503
    0x60d0203010302040c0503040b13050307020a0801050f060402040501050d0f0e01050403020703111903080901090305030c010b040f02030106140c0106050306011d13020102060106050703021f02070507060203030402060f030604020c060405 103
    0x40c1a68403d1310200042c00c5d400700d0540d6180800c4034000d22a000c40070000d0b102c010b006c89030816080c441c2085a040000a90000fa8903940316002106541e544400708401c1d40164240e10760058001e4408514103414400028100d100b45481060740503141c10141c0503400941e44050540c04045000f001203041c10314009403034a0140c030090b201a10040030200162500580410381c2501030240c0c2c1c100d047c5555590b80b026040608030a05001a5610000106409000030001030043d0070000581150074410001140c02c03c0c810040b000c1c0c03050005010068101c005084001103140310107444880b500000c1d405004e868110310f80500900d000000d03003000f1589030000400c40d4601c2501e0030f9560207079440310f02441d80000b900527440f400c01040443c3c001c1008000c01e41c024819180c000081e040c501c6010000e4a6106444a60000d01c44c0e0901c5000d11070708019200510145145040c80e80024900c0e0050400600715240004045556a41c4550450b0740440d600416103043c0c0c07401d801c149 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 1289000 1250 1287750 1287757
    0x609030302060708060306010e07020109020306010303090807120b010501031104030f0302030d0608010506030d180503010e0d020106060f08150111060403080103170403021302030403020a0203030403050303070f0906020d0806040209060d02 104
    0x4038054807880e80410072550042035018841d520280051110760300c1d0000ca18080c001c082c00d91401d41d513986119502503181800000d02840c00780c2c58400090713103048849807401ca8a54400050445c000801c1d80014070324058040c1150030034038000c104007680c003c00e40200d02c140d500007460044014400c01c10903802101400b807107090007a0400c5055600c141d4507003681c0d000c40f805e82e0b26402904441b600740d40900600b900e0031140fa41088440d41e140c00100e401c4910407440340d4029406030400c100031580c2402440090b1040340390a010100c8249400f900c040f401800c0884400010100c94206904c504202400ca03180304044421505082c1006082443c0c01e00055602d500c1942e00c48490318100e80480d0100c0317034044c08003041d003c0c202c07201000a4201502c101c0440c05043c40f07410141e80c3c208080d1000c0d50055000e19a02d00b400030300506040c0f0f40c000c481007403001c0b500c0304200003174020540d00d881c0142e5080141d00c682d038100010780244a0b01c22019404140841d01a12900d0107a018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 1290250 1250 1289000 1289003
    0x50a03030e011803020d0201030504060b0d030e0906031501030f030314070806040e0106050d0201080901110a020d02010b01020d05030703091b06090306050a05040b04020d0807060c0309110a03020a090e030c07060903 94
    0x43c1c41036003901000508040c11036001c041e41003100d8040c850019486a804154458050400010b41d200e030003000402c00d1107252415000101101c41d0311166241c1204055000b020490003445401c1412580c0707407540405204c050840c4441c5020b003030501d8000e8211842981d04202c07843d03101c5c0b800b150042d10f03000055680310300661070410741d0201140c05110b03405c20360794010329090104c8200d600440d0100001405041300c0d54030780c1c45100084140002611015410f60007404602e4003174030009086600601d009030443d0721409210402682050880342c0003c400e103000304003403c1a00f40200c100c980c40400100910750200000f0307a0302d52200c5000240c034460344040c00207490381000c020641e001581d015128070084da01141c0140340c45150302c4210792045c42c1710b50901e00107443d044200c074440d4058402081d101d6966008228000440204441c0e048460460481c15a00410402c02c11400b4001a0a65610048110311030400a6809240d0420111003405864a40003010445203220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 1291500 1250 1290250 1290257
    0x110c060a0c0b0603010509030d0f020405060403080304150b0a030201030908070203070b03100815010501030917070803100602030c060a2412050705030303010b070605040606030f060b01020c030102180415050a03030e01 95
    0x40f42e510f24040c000c082c000c0941d44019410004502c02100c010076017101ca91032560b0b401c120020303158a0ba640584001e5008451403520783c6040e01b01801022402c40c076002e000c0345002d0040a1598031124064282e076021b00c1e00140c0034007240f81100e002d110381c480280d07062040ca0000610342003842c0003107100302910100790351030f15640c0c908a07545050040c030040f180c00c03540e401032107594420350040400c1409401c1e41c9a01b0801c03407001d101b00340d0002e030054036541d40020805c00746260450400707000301980d100862a203508002190b844242c05020215020f4481b12881040d844030300b01808c42007000303110b4220080e581c608025128100e101c04503203e0180301e100080703a14010094034100d0b055106400d1906585036908001000020012150280d5420010000c54014a4200d40652154400081c680c40080003e03190132904060316100c1e03070041050034103542d41031040d0a5040d0307060b500032070504480b801103100c4802c00c2d04104e8011072888400004e1542c440c115072140032080c0c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 1292750 1250 1291500 1291523
    0x60906060317040602060411010207030c0602010204060207050f0306071206051002060907050a08060a02030403091505090301050907050a0311030705040c02030d0b010c03080f06010903052e090210110c060a0c 91
    0x4818071290b010f80d100d0403000d0703044800000c000c01c54802c1c104030580c20520649401070340720350b02c0d5080b10b03090380c100000507036000c1820f100351501041100b000d40302c11143c43c1002d0999000090fa03d0030001c10480070003811149401020340c054000c00044c0200070320358001c01030600402591000c04580880c4030f8070550a0006180c100407480c5010744912901400560fa06c050f2800007035800034000300e04100c0510800540c22003101740321141801070380da8980d9a1401c0c002010300b90f43c000340c040d400036001b1340c8003000a607461a013101e040740c0d0710000f002540703032000700001d0401c01d00d54889a001400e0424183d4005e40c0400104080d100c952030400c0000a40801190516100040100481c3c08440428001182205140d038007039014035110030b070343d0749956607d41003108800340a000070500c2a0034060b080e4041ca010985503c031079a04008520303060700000c89801d01c629110041c480101130248003c0c03400d2204503070009004d440a030341d03411582c1004000c495104810303142c804c0801e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 1294000 1250 1292750 1292783
    0x103050112020105030601080403090f06080105040c030e03091315060e030d020c030604020f030109140601090e030310030201050a02030d0204030f020a05060a020715170a05010503060702030a140f070609060603 92
    0x1074201104a6406946650540eaa040b0040d104808060416002e02c220800c000824486400c0f00d000905a03c4d03590302150352503d010b01c001e0310941e051761403d1600700022035500940000960310080f20407035603084010f400d00302d140010892500002c81c41e01c0b64500224034550401407042840009038100d40b148800c40b9402c9888107129100264190040001302d4054031b0f040450b0304c0c080c2002000002c0c503070026641d038141c0300c40001c40c8407143e420200041100a896105030014640e018001e58554500750307548250034886404000c2c180100414444400f41c420405e403102411202c8085644a459041c00d07030240d400c00404030300c20341c028200462682014030035540f04000640060900a0502d07003c106c40b0307800041e0a2040204594400215000c420040c0d0b02860b45054001540d5042c8800d01d4105030000300310342d0556004105140845a005001084d0080c000d9011915885050303d0300c69180714002c00030b0f000c00c1c2404c0701c840a111107948450100e1340b25001c05002030410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 1295250 1250 1294000 1294019
    0x207080a0b01060305040c0b03090c040501060309030c0206070305092d0409031d01020c03010f140105030303060607060527030306031b030c010305060f03010c020a0b0f010b041403010908030a0b01030501 89
    0x11294000d0180714807400400000b070207600403641107442407403d04c40c800d440b07100d854400d420881d0400350b69031180e9030150f0030f82000c0c0f1480d80944814903040c840e11309503490140c698003204500a004040c00200103050511840941d000b8170002000f042c43d0f01740c0c045030f502400e521080e0710b68400074074103d070100914043c42600c41c03290741601c40258616450a41480402501d1181419030141c014070b401c0d0740e642845181c402c040c0700280026040c850700084c2424100c141c01442c081d034010814006165121070540710100d5000c0004a111340e5010301e91070300d141040c01c0311201c0455207645da0341000400702c0a10f11801c42074040f20890311200081e40103040308d004030250503401c5200c4004003940301c0c0c0c008550003880a48041c02460466000c00e0031203040400040040e01f1600c1e002c01081212010b81e90009184100c8d1840c2e0b50603d11080000d00c1944103184040e4402c00c2000c1c8103807401e4114000060b0800e40c0c2544a251018401011f805402c00e01070003c0e1a0000200e050b040c0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 1296500 1250 1295250 1295263
    0x403030e010506090403180302090a0e0105060d03020319090b03070c030e04060609090207020402070212032104020109050d02030a0b0703020a030f0e03040b03041401050103050a0605090d1d0105040b04080102040501020708 97
    0x4005144041a45441e101500c1f0710b25800060198402d07450804005603d9145110b40600801880014a12900801e0508488020745421f10400031100040c0110340d00005546003005091042d03c00028004420b4841402e1640140400d24011041010a90b0070410b80105d4500948545002180b03a508000c103c5006014000100e40c0061003485202178690140c9081d40c806170005140004a4001070200103107031080300d505500014551031440d60000c000018820180c520b000f503800d0a0f070010300010328034060303a40900ca0103042d03270003559010080d486640390410203104150408d41d00003006917120310089d00110b8240f186000c07411000740704081500c00c0c544051030506d0300f019074131451544042d01c1910700c80c100031000001110300784074050095100c7d000521220246140c14000c1e208005e0003a0046d4020703040d40c81355a44c001446a105a010418070340540c1100c1c00160303120701030303070b0824140604040b501050452055000303105035a42602200c01542c1e0310b085c0d1554860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 1297750 1250 1296500 1296511
    0x3150905100611030906030108010606030e060c0702060307050904020d05040201020c01050406020a080903010b0307060305040b0106050405030a060e01020f0403050109050c0a0b040b13030206070803100b030907050f0a030506040302060403030e0105 108
    0x10228070421015125a00c68008021840144c902c5c240d101c900050040d002138103c203d69942d1403808005842d0548541030941f80d0042c042d10091801c148940c9680c01003c030041c2c0207500000000740c029100e1000c48040c1c2d42c0040c011511107203040411001040d0895003240540305038044100d0319070003001a05d00310386407540101030442e000d6a03500d0180d0414068582c045d900c0718440303003140c4c0c2c0910080c400b42032256400121840d00703013000340c0f1540040e0304c42c0c001d000701000140290344000c242c005030150401c0020480a203400c5290b402441003100408902d080070402004220064004200d020300640483e41190042c1c070400c01410120b10a0042c2c0c002e040104120780806900504105001d0040c0d5043c1640e40344c0103e0500d0744000412107070040b00008005d100c4407462085d0029011440d49076080d40b80c1051389030b0342c84411b4040c4621468403511011400c0d910150040b0185600400f615000c2c02d043c50083d540d9501902d085000c01e0034000351000903a0148207083c80340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 1299000 1250 1297750 1297771
    0x303090409060e06010b0c07090605060405040c0c020a1701050c030f040b0717010b2808070309020604090609140c0309060609060102011b0203040611070305121b0a0303150905 77
    0x11408604000c001c002259003110b11a0302c800614060340e03824040d150080400700440c2e40d640e004080701500704012031b0058140207140010601558541205403810f85005590000b000044044141c40a07062100f000b0f5206040e083c4c04140d0351140100c408003180c12400038000b50302c4000c0854800d000854240e603140218070002004105564040d580005541c2800d00858000c00300a12403210241c00400c031640002424100c14072250640130110200e000c42003689050815009052902c0500302008041c0c40c0e250b403d0a654501c2c0488005003005401001020307504ca80e200050161840090ba10740446800100002e003507000706c0e8440d16030700018080ca6070780c0b101085418100a01103c0c110f640c0c0d6064500d04801c015140c40740c3d0a4250015030710746d40b40040040c00840000ca00086a803c142c90420000c3c00018200d0320001d54600120b48030052110104da5603c05e5440c40c2c0c1035482030500c2c40e8281078140c2d0082d4060101980c808032520b4440019105440055400f00e041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 1300250 1250 1299000 1299007
    0x705010504030f081303060e03030103020108070c0b0a020310050d060b0109060504080604030302030a0e0a0b060a080a0305030f090f0604110411030105011d010504050301090309050307060f020601030807020d15020909010906050303 101
    0xd001030f1300901482d118002072005140e03da4803207004846012801d44425840040107009568110b409268070104a140450b9041000d03600c04a903100040e1100c07441540110104181007a003200c4500540800b420301104c0e0000c604124003d841054101804582040c20105803948144101e60940340e600008000c0d0b6200c5617000c80013940f0041000034030a03a11281141c041109002d401407180c001c959100840c14030760100050f0320003980c00b000c1194440d201404c00240c0000560780c0c07000e43c0009004031562007406041c103200d08103000481034001c0c40d00300800c0007000420b406055001b076a00b08410f020710100980707148021301490340451203804074103c0c2081035103400701e540388040c0b401c2c604169481c004603096604410040303010070302c40032040c07200d41030420520380103241510708850000340c0014041d44481040c00003070022080040d031003040d174440780c2da61216240e012086040104240ca1000d0080d0020100d40344100540c0c00000f65414044c0284015542c005010b18034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 1301500 1250 1300250 1300253
    0x50a05040203030a050d0204030807050a020111030c0d08040804030203060117010b010c020a09020a0c0501020307090602100203072001020408100501090c08010e060f030a02060705010915050705030403030905010f0c0e030705010504030f 103
    0x1546d8004c001d0911102d502001f002c0700041d0824080d10984d84240024085191244005000c81c14102d40e810113541c418400f1049180380058160620360842c181f03c00140c54500f80742045104681019415109000c0001014036a140018031701504000080140c2b44040004440c0c4e21010400070b0340c0020303624003d00911b002c07940102036070726441c144036814441c26238506007680c00c03ca445e81d010500c038840c10815280c050000c2845199945400c5155150110001c1c0c40340d001d102c501010707400380601ca070900324001d50440340030708070346422602040e0f030303401d100805000c09018190b0540d003003842d002e641e18007496969050311500f424044007540d8030414001e264404240c15641340c812805070502603104e640045c0003660180c0c0000c65180c100d405d001011100070401c0740c82c841c1c43d0104210000354410b0580703401ca9070610340401d42103c2420076078050240c080940780b01c1460700114400040e04444180d004c81415400d945865a8030001500c0602640c40041d0071003105246000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 1302750 1250 1301500 1301507
    0x60c080f090112060305030a0f050f030423010f060317030403020c0108090a0602040807030303060509010305060708070e09090705011d010801050409050304080303010b031509150405040c18020706050a05040203030a 94
    0x5940e65040c58200904a54600f80c5030035948194400d440d10f4100140d448a016404440c0407070b0301c0800c0c144140780c80441d60700081c45100091015240b14400114580204070300d4000001d41241c0c0c0b002400140e07526487c1c8802001c00d840102c1c2c900f6500181c21404a0341c03407050302e110b1900342d002340c000c0800d65001134030361070130042407814280600c1e12243e001800603c040c0010f88108002000c40c1401c510300036049400782d400c528411030320038004000003800007407000d5001e4000c0c500300d50305403034142040e105400210340d1298072102c65010040310030000a64039040324800da8554071403400c010385c0c2c9a004d0f820000c0301c81c0003c0d485d0005002c242040e030851000988203004680c9000d5403a5030f0a03007590800c1c4c0041d041c0f03807400401e01140200000741d2502450341100c07240960b00b0403070f00741211542d42d00e00d00d5010302d072100c0020341842502c1c2401c0e4018940601d605803510500c0007008000d40c0040c030109c480d140303490007207100e0510034030425214a0307001c0c00079481e0200140c0c095 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 1304000 1250 1302750 1302757
    0x13020d080408010e0106080c030102040e04080702011205010e04050c01110a080309030706020a05040306060807060503011710020307050702090901090203070509040606050402040603090204050703090209130804050405100e01060c080f 102
    0x3500c40305410040020305900034030607840100301c841d00004043d410100114104440d00503114400ea00610050012005e01051315420507404203049640e15001e01c01a0b5401c0600c480c2a0940c9140c00000120400140001031103584a0340035503240144000040d0382c80611240314014542c82030b00e5890020b080100210f0301b224200084a00781081940c440d01039a10115010b00080e10104042042040c0c5002d0034024041c1400501407103070a001004040f804144903d4000800d0310803c160700c0c200c14420000d03001d12104003903503a49080720014210390f11118040380103038103070720029141d0b40042c031034005d21550040103840481d1900e001c03c00c400341e02810686803140e840400050660f100d1004100604580c0c50205050030140108030807104014071110a0504044818005035030700050302c1e034050004401d105560401781042c800d14040d603002540c025140900b0300024488840c0c1007011150301000f114056070703da1000300c4038140f0146000301781c2c15040c80020b18140707240c8040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 1305250 1250 1304000 1304003
    0x111010207021e03060106080c120711010c020106060e030f030a050a020f0a0f060e030a09051009030204050f04020406080d1d040b09071206050d0309030204020306010c080f030108010b040513020d 86
    0xd810262640c002924003503c00b4039043c0800085158140030b400c09014940c01008241401e4100e46000c00200c0c0c56442150094070540460200080d10103020b0942003c880f410030001700a26004010080e0082401d402000040303280001c1145941c40c000800004580c002005141010b040781d0040d14150456a02c000a40c002c0883d28035003800c0c20003003041e0140c0501b10414403c941810300c0301c11100d1a106a907015002003082e48006900012010700700d480c150b5400205012101c0e0440d0850440e03080254000d04100900c962414804000ca000d540200c408100c5190b4440318556144044103001c4003062040500c0c40402202d0080f25031000005032004c150303200041c0000340c141c030084428401051691950400070745007841030704080c003802d030355062810031030361006400700390329103c020b201d5900000000c02d240d200b03200d640b101c50740c0002d40540b60302c01c1c0030040d0780c0d0360001d000b030400c950b19040c00b49419141600800303010381092540317640861116006c0c4950508100350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 1306500 1250 1305250 1305253
    0x204180b01090503030d020405090a020304030804020d0c080304080102070510060501090306090206090909030a030f0501060e06070606170a031803020d020405060a0305030f040302010305060d0305031f09020d050405012003060111 100
    0x140040c10f034400313100400c01b80710110300050f0743c0c1e401c0030204116454082c3c603440d819407041c010040041d401a0406402c2a01241c1081c044003a6141440203100c41d03030414890b40c04007040000302090150064885948201c0030382e555048821020002c850491180c0750004800b021304002250300d0360b0109180c9070002d840345141103184404101da2060594949441342d00c005008039070664140700311650a4900c950500c40355241c418028540040604460f2240070b0014000003000303410340c4140001c0180c0401c1c41100c0c50301d0f1000a4840c0d40d0718070140c01003060401180c44c14240d48183c01c00350307035004001d40d0500c0039540030b101c01010001d002c5600300b1407108021020803001c0001c1c000c0483d440380960b556030705610004051703071030180a16010303100183d11040002d40081c1030303035400026000c1860007201018008144020140c1c814540540b0004180b0310889032500305070f20481c0200000e12406141040c11040f01d0b02c07142007419401014000b0035160740c450030805000d90540750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 1307750 1250 1306500 1306517
    0xf0f06061302070605010e0402090a0504031211090a0605070203060a0203070c14031201030b0a140606070b040f08030403020102040303031b0903060e0a060501080a02090105011409010309080c010c02010e100204180b01 95
    0x1135600d012240282c204661a0100300c040000712b250060442d68002d81002c814806814113a4014111600d43c42c000011640c0341c030020041d020345207064800c07060000f021900c11998583c000381003548403d01c2640030303005880c0000c001c0031a600840b4012001550341242042040d06e994100308814141030900340002c0260344031005480d034040e170195000346e0340191a1308244c42d0707107412240050b400d042c612021000300030060740c82c98165400c240d0046401c40885da00d500c0e201c641c0801c148001412802c020041c842499815400390080c1c1e8461b0720200700024031100c40d0354581c03000040420024410580a10002d01c498001400d40d60301c501c110f5039a00c1c01c50f0380300700c203887c000d801040050380986d10400c11744c900258a1401400213081c482442511440324000b507109400801c0d050640b40d104040400400300c1c1100c00d42d2401700020424072102520080c003800c0d9043d451041441800312059040d00d00b8401c031011902c4110048000e00030204108002c0e051b0b0035a854144082c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 1309000 1250 1307750 1307753
    0x5090d12110c010306060207030b060d0f080a0306050108150111010204050301090303020903010b01030c051204050a080705060405060106140d0e0109080a080f070e0604050409060f0c0207080f0f0606130207 90
    0xc512004031440e1294803940011004040c0b40ca118401c0356410981010b00410400d5004201501543e400c041040b80e281d0360113000ca14110100d500040030701d1101060942485007900c003401c03280d18913907814003500382c0c0e50b0011109035005880100d600c9650500000207513004403800c08074901ca00002500340756a4200203421a124254207501094002440c042286400e02c2102140c0d0001d007410010700d414820010031900480003c100e24580d0080440c041c44010020360000c00c3e0700c000c41030b555240d1032a00513291201580c0c00c88661007040c00101d9011300032210030354407003c3c1d2210715041400c01d100c05c80291202419652880d540e404561004c144440002c044e080e1882d10b80304d50b00d00340500000000c2c40014680410082e08028511403a42c840c011a0100d0304110303004103038920681840070090040c01c81c11382c6098902a550b126840e00450190102c1d6092002d45030711410491300581c5414103005c0321100d80e0410070004800d8901440009a0044031540060500305a07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 1310250 1250 1309000 1309013
    0x7050405090c0a090c02030702010c030203070506010311120106050603070c030e090106030203040c06020304080304050409060b040f0501090605090906131505070e09010501020a0b0411060904020d020711010203070507030305090d 100
    0x35076104007503810040c8100e0440c14403100c004010600b00c0c100304002c00342004000d40340d0181150080c108801244d0103004c1c103108100b0303100324582090a485030b030750b500e00e001406d8200303030740e4014020030a600020484401c10300c964011a0405000c003451039542d0001210b2400100d075044080c003442d98491001a120104024080c180a40b00142e480c10642407203014050303d60300800031036000f00300503c5101c001000341c800700c0303005403070100707401e4013601d0039001500b0342c10b000740d070032614011100c0390700701d41900720354102c2d840c0035010030030079072118188041410b0803100d20b10700d0790003a40030840c01510003071045232090003504d0b0224002c1350740901e001541c1080e00d1000009040c400d09546516001c241180140800d0005041880055441c40251600240090075042c00c03510300c45c03460340f100400c80c0d8400d04014021580c0e001881540c0009410030304060f54014010202960b0a500000c100d49030303140c006006110880c0345a50484440c0e02c26000603404c8404d012000e40000e10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 1311500 1250 1310250 1310261
    0x30c07030506040c080706020a030507060f0203070c0204050105030312040f06020903030f07030206010e0103030c12020c04141501030204050a0909020d0606060c0201080604060f0605090a0803120709050301050103020f010809070504 101
    0x10603006002c03142800d091521518013550044200d6400041d010070a0680001c0c1c010303a200d6160810645940c40c5050850041ca03410024210650000040120042d40aa09a81e0507882200c02b001544d0f00d5000b41950b0b8012143d44400c880004000310b00480c0f84c40509069141c407038640903140c00045c201190658010081031000303c1004180d00007095014001d90303014200031706070180d6561540e10001d1a1407420800980f401c00d11200c0d070845030b4804e214131040300030003810034803034400c600050500e246c1040307842c80540d0300b1480c030b02c4081d907220b4000c8804680b07004065903171560900d401c81d8010b0601101c1241c1c030901c1007604500059450050b034000344059207684040145070b000144c045100182185d200318500a0140080504081e00c1d005503082440d010303403107000050203e200c044550700084824400030400000b110b204175003240c070654040d6901009140c1c1d4106044c02d07038000780070096204d03465a4400c0030a501c41da0b2500d40c00110320040303030460359886000c1000c695 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 1312750 1250 1311500 1311503
    0x30309050c06040f031a040201050a1101090206030106020a030215061807020106030b04060608010c1404090b0102030408070314071a0409050a0216030801150203090f010c02010908060a0501170a0201090b0903030c0703 95
    0x1c507031300410824040039003005008081a01c0c8100c00768035156000800520410441009105181c44043d044070030960110205c6540a49055a03075612120060350f00e90582d507089006105556003a03000c151040b1589000f040040c0c1500303050741e8000848403004c10700400c2c0408566881c03900101140c40c548505020b5800b44400007400c5003011195802e6400003803003901031065241044028440e00e10446003161b1070490001429100800100e0547c812503005901c0d034170a540c8044107111b0008001c50a50889408441c4040c0c2c0d07540c900310030401041c50345546040203000c03c1085645a400666001c1850803005140019844100ea800750840b03000380c000400b880014003e22503c1c0e80180c01150050004505103035121001404000c0b81501940c10811311419000459000d51101406809048185c400074902a0442f500130300003481018036107812640c0c104c40707181d0046030030b40c00320b50180d586001d80e5060407108181035001e640200c0c1c05101c1081614001d0406009120185 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 1314000 1250 1312750 1312769
    0x702041d0a030306060e01020c09060405090307020607080d050708040b010b0a03090203010c09050132070201020a14060402010905060307021b0109180504061b0207060825020607030507080106020307030309050c0604 94
    0x41e00b4000006d0140341c03550211410b40d4409582d9402030b648024405901800c00ca90100c1c2c10f0352010101800e40c000c540000350003180103d80807013000006000360102c0390b09004208115a54002c04841d03001c0c0940340a000c1480500052154021a60003004001eaa074240031074003c145501103400c5800000d0100700141ca800380502280da03215850000c504086405d000701546444080c0c11002000c400301e100a41d800501d01003103900074400441a1600f14a1307121075441500445601d50004541c104d0000e113151070040b03070601e401415640a00711507070060444176003d401d8442e03041c40104400b418010b1207040000d2100301030b440d80552003800320010560b13042a18020082c2c03000000d0b8041d040300070542d80c1c43d40b541e00241810480d5018502085103407a098411040400545968103c40980007000105982c000602a01400682d40d040266030360703a24003180e100d48280103a0005030030070008140400d110303070817403400140601e06903000085c61000003a40d5903c640e010750b400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 1315250 1250 1314000 1314011
    0x1d060301030f05060108010c020309042003040c060906020316060c0c050609010e01060f0501210e01061706070801030c0605070309080607020c100305011508090c0a0308090406050301060305030702041d0a0303 91
    0x41003c140f140300d004200c0d6a0090084e0221114043d44900a00c2c100500072135440c404410502150100500c02c8a2102051a543e00341424000c00041d0035009100220748001c40016416100008650640c100d9028003035510070340e590303868040e100540f480800c006c2d400070840c02041d410700002e4050381400e070002844540909203103080d52a00c1d40021004150007204001e1a40c112058070803007543c0c006000140740130000c50100400110070501c00f10b40c0303003003000703d41c01100ea4100c03c0402080801c0700c01c25a20340c242100e140101340001084000000c40c10455a40540b014101d55403017410700e201090384500d1000c0c45c0807411649071005910030112480b071410040303405980e4440c2441c00780450741c100148940242e42241c122020485203900082c5400010302003442c0c0b691004050f00700d0309503642001c01060300100c82e80e510840c9004030000360707880c051207400112030340103001d141810b4003502040010b21240c2c949a840c00c90b803454030910382c503060002c00b0341c903403007918000746 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 1316500 1250 1315250 1315253
    0x30405010e1503070503060d080c010504020a090203060d021011160e0f01030804140103060306020a03050109050606070b0a050c090306070c0605070503070203031302030309060703030905010515010c031d060301030f 94
    0xe5129804a01c07400340e00c1160a902c14a501d020481c1d40c03201050a100760b59442d2000801e5001c501900007406161012940004c3e102042d00000d00945c006c46400000549640d02d1100700c0c8810b07280c481d84510326022507801410641c404944030b20300c84c24544000e88940c10b68171305100d000c42400c03912840c0d81c2c106100384404655002d400c1041149036420660640c2d45100c150b02c6540102903034000b50310503001050b8401d41205010319401082036449107054140540604401c0c022000d00b50306000000e00b20f410440c00782d800b0a41c0081310394040c3d4540d001018002c080c0a00744e6418810104a039100c5501c8c2003000e0703170284d08541d0702c4429a44031400c10384119040a0415000c0107001c1090010b404e50000649400210305400c002d1409000d10000e4914801d02c0200d54000074081040000d01d50141c1c003d840c81750141000b808955174551a0341da00034192481140450800c210001c0417074070500d0b10000b456072500c60758400d01d02d111b0008404d03402c01d0340116524440c42c1c50450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 1317750 1250 1316500 1316507
    0x3070501050c07050303040303150f060206090609010e030d05040804030204020a080114010503010e0601050901020f010f020d060e040206040e090705030604060e010b0904021309060b060309010606090b0301060504090905011b0203040501 103
    0x26801100b0206543c1000d9143c1c4c3d031350340c880c4000340c805000c00d610b8040556003203030403408020040143c0c88201d89851340d04d040180d1030f18807c841020079809031703800140744034106004a40782c0c0c3e0f80c81c50180d80342c5807150780ba240040c94060020740b103100c3c0500000c001a200d520081250802c19202c080007907140070f8100d0b40003400316405604218050004003c142c0e501c107c5103400500034200707241c42e0501c9200403413602032186c1c1484555800c007e0900100c04166008141d092120300c0c0c140035140d22542640b0b030071401030b034000350000c90030401040040209054190810070000642c0c6031541c0d5040040d240040c20b490a0300c1e41ca50392580c2c0304100f0b100b40310310b41052074250344599481c603250b00011040c0c03070481000d105141e02e032141c01040045681c88412400d4008140503100e04041e40c02070f0003803419001e0000480c4040c171000c00c1d110f0094065a0417941c03195103161400d0304204500d0090181042e040f1065900d4a040a078455200e500003001754055074000e544580c60200010b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 1319000 1250 1317750 1317761
    0x20a050d030207050a03030207050102070209010905011403010e070501030504020111010e0c0f0d02100e0105070204050f010f0f12060902060405040f09050706050412020d03020c03070305070905070306060f030e070b0c03070501 99
    0x81070500c10061000040d602151440034246c05040c010b850344140e05055000e489145c000940c8840b20200110725000075511860590700540c00e58400c80301c2030010b040c00c80e00d00000c5001c080e406a4000c0280c0d6220b41c104581c001e00c103240c0b0303002104440190034256840e20314590b0960700702183c40d00c22030030002440c030380f0384104072680e0740d50809075008502081e20304102030040051400d450402c40c2d025008542d984c65000d80104071919040b92002c5001c0e10a019441a80e10342e802c0004002448880240c140e40c2021407a0100c12441d96070a0700500d1105022600700e20180800212031ba220320500c880001c01c0d100c003103000319444c5811828040721382c03c01d40600c40c0902091107000fa6401c2501c3c1100da0541d4041d003025006d003401d030b1815010124040d81072141031400f204101020a02e6011500c04000a11032621280002d0b41503070418041e8100103251440442c01880c800e400c030201455a000c1603a03140703038450390001c001d071b801152100c0c2d03582d0000500c0381c1000001d200f90b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 1320250 1250 1319000 1319023
    0x30c0307120212060405040602040b040303080f0c0304021c06090804080c04060509090c0111010204030204020a120e07150309111009080705040203010506031305010e0604061a01080c0a050f0c030a020a05 89
    0xb1481d0610700c500c0c80024100151006014550b00d400081c1082180d078110f40c081e1030780800aa88499807441c00810010040314584a0340482c40086007a4103403a00a49006a038018441d0f0150b60f4211030030541c004030560305849040c0c40701007a0021401c140d005002420020001d0300a2540d81c101b80700a55120750300c001d014880c9030040102c0b01a001c00c84802c2da420902c2c04c10441c0c1c005100b201e029000700d800c040d600a20004070724042d541c000d0180d680e601096a418405401d0b0301244c41e44990961240460241030341c000900040d10940c030000051348111242e8030000c110f08049050144e079484c10034041501e410b0207201510042100078001d108c101c600b5859076050a0125044d0300018200c906221290a401d03003c10600b0341103011000c00090031a1030a240504204000d00344070402540702c03240446003510194407a070b5405120f8800c0d204900d250005c41181190294000900c0b1001e1110903c032600d42c1103418801421800a6503009204109443c00c1c05414010b1f01443e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 1321500 1250 1320250 1320287
    0xd0606030b10020d02030901030209040204050406080303010f0801060305030405010e030a0b01030308010f080708100c0c05060708010306050601030506180604090b010902031b16030521043002030304020906010c0503030c0307 98
    0x618051300e40c00000c40d80e028030280307400350f118003460001c01c020780501c0d00550b41c060700b02100412655800405181240e20741501c0042030342d95400003500f00c1c0d0704c902010780701d5041003100344160350281c1d40c5221050300103006c64a00c1360b41500c800b9400030084e00300300d00048004004015001001e60088050803200c0c014100b80742ca0701e080f96a80e48a140404009262179079032807a4602c4c002c0310358203101d44c0c200d020f03624240382070080284011024081241c90342c0c60100840c85030b511a01c03880703101d001c0141074101c1c070014a40a20074401c1000700499840b07500e076035010340013502d8107000318020210b44401603141e05000d06191150a44c0301c50702651203000380300002c191200016144201038050500a9440103003401c02c050b0300c1b401c044801500500c3e1310a120411800d440e100c80070040000e282c5400005401c0d040e4107440e00a4245030060b88188003090140c603000300c0484e04100f0504200e40580d05c00d175030f0309003907400840d0b030302c0128003000c0204594aa0030442c0107420000011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 1322750 1250 1321500 1321513
    0x1709010206130204060e0a0506010201060b070803070309060209030307110a05010804020102030708030a020f0301080c01020105010501020304060e1c06050403080a050606040b030c0a03090516030201020c090906010506030702030d0606030b1002 106
    0x400003981c814000300142c0d0a03550007032600c000c0d500d40b80c1c01413020f07200e54103c400280c0380c81d206002c00b4190a4501d01e00640c03800c3e0000076030545c48010380d02c055038401e40080c0345480d551001c80180c03201510650f04030340d0030440f6410542d400c00041014522600300d0769894180b1508207c00204a94403050502416004210060780d01008507000e0a0f4401042502c9841c0c4004400c001c2c020705e000064a6940000042450f0714005644042003409170b009110aa813148012038803405588145400700d0f0b4411041151803509071442d09101d501c80001c41d6036002e403601c1e05070aa0b10261025400311b0ba0400030f0000d0f0503458001d29a104005039805407a003440c204842207103100040c85804404404105c00c200b041c80394015000d05a00038086449094010711b20503068443e0388000c0303026203e40b090808260411048151041010801526403686800180324040e40001d10302811800204440c040c0f52100d8801c070000b4151640e03000452102c0322092081604030852540150352060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 1324000 1250 1322750 1322767
    0x506030d050f0d09020a03080301091a01091203020312010f050a09060308030a0504020d020a09020a030b0a080309060702060d0e0307060b0105090a030201030b010e030a05010c080c070506010603020703050702060304060917 97
    0x141c2164030800003840da003543e90742c0080c02c6400408107040020f60100d2106000030034020f520001c1d60589140090420a1284030706245503a4120a110a404105048030802000360000c0d842d0308018080d0040d280340c965100f851551030202608165550300d110315051015003000b000d800050a01d50004010250554403080c956000040c40c00035015150000a030454886c012280c2c1d58590180c903103004e954a40b00e0110180d00711011000000c5d1620315018454074001c40010222201c50001e14600600701c0e091003543d602503181603070401010088400c208406101e6800a000c0000146840705c40a01d0a1810364001010701d50400c1401c0c03144c880c441e940e540c1144100c0e0380c24200051010300c0800180d911141c2e020501d07526000f40c50a010a00070706400c0381c80c082e5503e40c0d820403140c0e107404514005015038140a13110703900c50f40040c8100d80c007960081500a000e4181141440c0199000030405d0344103c40c2201c0e000c0d01c490303508081103a1880c00c015a41000070440f81414901c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 1325250 1250 1324000 1324007
    0x3070302060c0f0702030f0a02040b030a080d020310050603011203120209060306120f0a06021201060206010b030103030806010201021b010f0c0305060d060203060411071a13030801060806040e030a020c040506030d 93
    0x603222240822000646203202003c0f0811100c807139a02800340c8030701c0711402c07000981340c1048000581c0203906004894015140214001d85031315406400507003045010304001009403c02007c03040d100c440d0031001305440d51070380090341c0202000791100000d140726180041082c1d01100d855444140140035980d0241c2da203005503a4000800d03940760b02018861945545061039101200c1c4803406526840b000b40700881e001840f8400711402c0d00303552030341e84a000f01d076107440910070b4503c0c0c40ca040c00140b001a12175001e040c2c1180051001606140807091144202d259404960030340d40c0d0b45112100000381355000d401c0b01c1c40540e08003081103140040103e446122000e030003d08444d40040041e41d01d5480341c0c089540c0314202d8441680f50046c40c070f01940070010600500c80016600c40000300684d04582480d0349080c3d0607582c1d1000c1c1c0c1d01c4c000d0142c03001180580340c140d0103612059000080e560810190524001a90003445a8200c5a080c4012030f030000d0001402500800c12205600f40c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 1326500 1250 1325250 1325263
    0x120b090402040c0201060308040f030c05030c030303070503090106150f030507020c06040909020103021204080909010806040f03031d060901051b070c0302010c030512010605070b06040504110906010918090c0803070302 95
    0x1c06907008911100405412030042c0540c1d0801007400e1008100400c1ca8a0f0280420048d28481c0c03400441c038540b13a0f010140d0b40c0c2c5440114a51580c81000040e42c0c551242001d107070090401000170034041c0d12480082c00051410743c8220000303020f50b03898189107a140c00f5554000d2000c2c0080d01c0710100c004046074441c0b0803030244113070b01602d807101e000c11644694115081d203915000c2e680600d0401b031501c41026480452920f101d0301c210b400209401d0000724580307005a40c0108006d05d105401d80e026405401503194109200f8103403580c105516405106441c4907040c81c00002481d03103006c0c103001d422854503035550540e5000c01d1142c400010350300211841902d0702420600010580740c60b044415204405000d0341d04d0080344000a400ca4120010341001441525481d440d50707228414481290800c480103400310407880550506410300403416600303c001031404d968007689512180503466140c01038a0f4816503191207100a001c103245040001d0b103451009945081000d8800070364500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 1327750 1250 1326500 1326503
    0x402030705190f031506080d08160e041b090b0403020306011703040b0f03070801090b06070b06040e0a0c03020a09020a0207060e010306050a0801020a03050c09060d05040507030204050405030a120b0904 88
    0x90600c1400b0084405140e4400146600031000003429101c0c80c0c10b4101030442644030650505061000c0341d0701c0804140c681100301c055543e242165100c81c110a500c1008107061801c2c004004150b01d401d445500595404030f10100c155407260003810402020f802069100611444042c4418001030390041040c50441d480352514420584822082d141544500d51020445940000b40c00940c1b0b003032400654411011502c500d112030303a98010401c02d8540b205400b40e40003908116a42c00205801c1d070142d084070b8042c1c000a204821040d00500c0c010b980807041d82d6025004d04100218641003007600068406010103505092481d000a90345085501401007800208005440c150340310750b1159004050050461000c1981c1d078650b24001d5100b8414071000904143c0090f02d0102540c046407503502c009451103282500300030b00c00d4001c140240c02240c59008004000007d40c0d214000c85001c0d60041340030b142ea0382c20000c00a40019040b006880203582425001200c40ea284811030380e009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 1329000 1250 1327750 1327759
    0x90602090306090303190f06080d0206010602010e0109080a0507030e0405010906080609030f03040f050c0405070302030601020c010f050a0f030e03030709051003060303020a0206030910050106050d1107020607140f010606030b04050f0402030705 106
    0x2072014032401f4003d000c040d0070400d181e05c148283e0406039a40090740c0e038101c4101d50001c10100352002c09142c00e036012601c01400c0000100101d000c61740c400d00050a00b2402441c00c6030038101e40d040060180d4000b1303800241d5480e160b90042c42040e4003400316a03000049200113610302084440030001c0b9000041000d820310350780070890410b00806015828000000803c10880c40c074180b01d019000350000c2c1c5010b801403060f4201a180c07540620120482c014003500d030581059842001120b411248801c6c0a04040e150074000d0f03d0070500b000134502500058070740e900c00c103050005002c7d850000d81076580c01c0509019040000c650049603c020080d016100541d91350341d00c0300014075218800d00b0300109603107041d00010703c0c5036001c4050100c011071010203000c03080c1443d24517641c40c011500c0107940180304006041c0003400c00c1d140e00d040c085824099510a40f07541c4401821504160301880c0841d8940003404403d2801d03102d4a584000242a00070590410384c0220f2794903881402030f031303010703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 1330250 1250 1329000 1329011
    0x21c020604030501020f0a0e0904050a060f0b03010f09020411040e040818060a02010e0601050102010e060c0304020a030c0e04020a050a0b09010f0509040603080c0d0203040e04080a1209060209030609030319 90
    0x25500c602080328003441d00407009568a62010301c809905078046551003000684102031440d5500e009005107001d00d42110082008010644411000385103681402c0c090340c1d0388168150298501780222003603080c00c880001451540da0040c8001c3d00e1014140d15103016080009028041c2c2d920051030f042038102c86840d4544078207035041240c0d510030910150b8072003404100682f143e43c1c15000300c0301c051100b80640300d50366038610059003661000c040b448541d400000006091031201d038086c59000303000520744240c0d10707038030780300c1d1644216990084034000c10450b08001c198244400c11f640144000d40e0541c000f645081060300131070081c0080c49040143d1000841d250520500540b4626039000f4400c111a540d44e2502c1d407801e40c01a4454441c1e80510402c207641a80040240c500321200c1810b82841a03541d940c40048651003003c01400b44542c0e101d0161003210b42c4e1060707482c8284180700060b9030390414820076141c06002000c0c2c0b8895401002000800c40d4020b003100ea0301c1c01101c801142 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 1331500 1250 1330250 1330253
    0xb03040804090e03030a060801020f040302010e03070504050103080a1b0f0206070f02040501080d11010207050c12030408061501021009030e0415080609010903090603060509010303110f0607021c0804021c 89
    0x219071160303601c9514110305080f204202800080000c0d4010030440d44e08200140c1d944e001d040c00c2c0c4c041c21086251031a4180010409540102850368090300000d0598039010389400c0058102c0c0c03000e170001da5800344042030006440ba00300b20036180004004000a880200d2a07a80e500c2c0c481c40030b0360007402190003045c15820081e03102d60b5190100c0e03005105014540e1501e00b01c5603260681e845060004140c40000803072540b0610840e10000d401c0005040011102c80070b2010500740c00c0c1d01c1210790f00c000c0200142078070090050900a00d00c111255143e5142c0e100028a0300d410b82034000d04151074030b01c40000007908480d003507140719025107020900301e010321b0085130640c0703455102c00d10754041c4904014603680c0661015103a01e220344c40354a40c10780ca07140f04504a8225010780c40d08084201c0041c40030900034040341c0040c0c10001d08540d03191000e0201c2905101064440b01c0269020450b4101da0382d550f4004482c07600c41c103280004040c40c064000411022607074040362050f9400d41c40010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 1332750 1250 1331500 1331513
    0xe01020309030703060509010b091501080702030f040306060609050301020310050405090705030f01020d110c03030601080c041509060f0e010905040b030120030f0a0603020306060f0406080a030503040b06010302040303090b0304 99
    0xc0d603550700201a5000140e4a0820b84060001218000c1c030391751802c00010079600e01800c08600480c804d05d444074a2401010055440d07810190a01e01948800e1044454405005000b00082c511070000499100d1601070094003800044c0c000b548a40d00500c00c024081103500448000c441c07003200e0200b8651500000e250a1400d42e40003d9010b0041305001404003505400911580c80054010031403400d043c0d0140700316000d411043c80b100c1c1c00030008150301c0d43c03040500f80d42140000340c00d5480c1580d140010040d040c6d0b50182c103008242c08800410420b83c009261858405190900c00d94a10300c51000030040c1e80c10f80106441b2315910002c5d0805603c00b548404003910200d441880a8641000451601e810403100c10b40456444c1000032010304840c01103500301c0707602400414440d21240c0c20020407800c4401c14541055a807000024401f804000041006000e42c40d074560740d01300390404485400300140700d1818140100410030000e540000c88900711200500c003e5201d0b155441d1070b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 1334000 1250 1332750 1332757
    0x40803071d03010c02070f05040603080d050a02040b0d050405010c0302040503070e0406020706020a02030d0b030d140309120d090b01080105040b060d0606080105010306020d20040b09030705040c020a14030304050a030e010203 98
    0x41da003561034400041856900001d6030707403d07107a1151451010942d144100000e0b40c01c14007004112703090500c0315040045c080e802c19504000140300c05800d02d500c51181c0c141da5005052045007aa444000780010300c5428801d00101c0c00072454290318245c00c04012a603904014030030503404104082c0010180440b9606680c01c2c43e5004105640d5600102d500030342c0d0ba08041099250903250890b880e420345000940c0030f10000b00340d1541401140e450b00f003030441d900024404103a6006480401480310f60b14802060f500c001d07007600050035400c5003440791040005801c0f100c081d030b02d040c041c0008100f900b150558031000c01ca4180803110554500f100140c80141d0103140a5801c1a00100400166401410507004000303410001c1d0141200070080503c0b440d00c00607800e447c104001d20448035031500a141a43c4007804487c54182d441c0301140403640000f800e0801604680c00b4078003008030a4421151400607003000f1810340c1003a440382e9441720f00302c0a0080c28055070a0741d2559690003401074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 1335250 1250 1334000 1334057
    0x5090901030b010510050a1d0607050a08130b070f0b180703080d0c02030901120f09020d11030106060f08070503040609050303040b01030302060105010f050711032e06050103020304080307 82
    0x80050550703407442c00d404410401c1c080c0c1c41c804c03000121482c2d1910302c2041986c150703040d04e58540400140c525800810b100c0407012181d00311030100040e80c00716404000c004ca22038411902030b039a4108a1840500c07136480da402601001504006000c0441c0711203a0b000034494000001d01748a44444d00c451400b4006018402ca041c00b030030200100b44503c072406015146034400003440034a503100002c070303264801e6801150204034039a0480040e1380d002e07403142c0041107904900040703541980e0002040030000000449582c2c83e60000304c1d50342e05083c0240c10003040702d414500502c5810640107040c0c541d00416100401030b0110004043c058a6042240340702c0e044070a89982e400c060030a003001203001d000c15400b40c441c4100018181d4400d08003000c00003026940c4070f00b00318003035668001d400c99048190b40c9c58403e6010381c00c1400250004640c0c451180030f00c03c1c45881141c1480019205940e1109050510620030040400d012100712640644603207040380800342228603120290340b42a45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 1336500 1250 1335250 1335259
    0x503040506030709050a030303060303020c060903190201021e0102030406060905060105030109050406090611090103050105030601060c02041104050a08031903050f01031b03080307030209010318030c030f12020d09020108060405060306060f010509 107
    0x40003048c5609540541c040e41e0185e802d0341c03840000c9a060001c1403081d800c0280e09940159030a10a1041d00510002e03458414410340d0106562400c1c091202c03a42150502e03001e07507000081c001000254807a100003005080000d004600d00741c40060000c0c00305205030402d01c0e446800041c208403240d07010400503070380010100212031056078054403036001503c00c180400e280c5800410149400180720f1304a8003555110340d448a42503007804068410389620103c0207600380700c040f49941d2541c401001a100d0344009540344e1403a000b070340c800c0020380c18400d07080c50f10346030a01400f0704400c400513044daa0414091a80500d2100350018200040c0e440a40043c90210070301842540c0f680041401140076038003400f007007120000c04e20398200001c900401003440850b901e00000d00401c038803290813810b428101c105841a20710802a40e020b200070501c016500c1801c4000c40d82c04c0490540c000700152410400707850103d021903503450000c3c0450b4460040c0400d40ca03c2a03110340c085613540301c0d0190 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 1337750 1250 1336500 1336519
    0x109020d0b01030b06090408090103020705010e060c0a090f06020606040b030307020409030509030c01020111091207031e0b070f020a031101020403020604090504030206160801030611092107060903050304050603070905 95
    0xc0451065000303010132185102e05002141c0c2604d002258140146c2d00b002c0c03410301c1c100d8000f0043d0029404040e00716240e54940c4007501da10b01040c0034a07441002c0304040715035600c29a41d0000d1405916030806246128448412701c51542d0000da40c81d03001c0c9055900144082103031002911314022000004d61003030900d1102d0082507801006040603038404d404403287c1502c09001a82030b40c1c00140395510540003402102e00e1450700e4860900d01c410303448141e500c2c1035241e07150318445c008441903000d0102c26441140040141e40c20f900c070740c000d0071440e0140042c90796007402034445510340760190070440322a001c0d00e60038000703504440c01141e00504850f51280d45012100c090300c0c084600f40c01500076440040d1580000d003030042c5101c440c9a840b42c40680c01e40c0d9031080203281d121041507500d00140f290600d6620383d4247d008c400790401001c10003030076240000919140b0036420210800260b80703002c100203600001541c050b120110303140c1d0348a5485043c22250404564401a401180038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 1339000 1250 1337750 1337753
    0x20d020c010b1309080d020304060e060103050102030f0106030e0c04050403030219030b0406090209090103080304050a080307030203060306060a0b040b030606191d01031a040e0c03010203011d010504090b13050109020d 95
    0x15030040319046010303550790b003440f002d07104a43c00715005808080d007541002c008039002c0141c03941c02541c0c0148200000a0041c111a00080c13500c80240c02c11940c90394000305210304180d002141d03500400c0b20f071400b800029040c04400c1e444402c1014040c2c0200d03181c0e0041810540030b601514000300041c00e421b4404082c0c400700401074000784c44c1d40c50040b464070a002c10004418000c84d81c5140c8081c1c00000103174070310742da050701c140d10040040da054000c10440780002081880214010b2889a5015889040c03110815082207400b0b480141300b00e81501d0100008900e803415641203072060f820468407650744801050b91803148400c0b01c0407a80c3e03815410604d1542050444100d071000b20061041040001b0043d0708035094030f000113900320700c4800a100a483c21341c0104002c07001c088103441810511401007803c0e600207030001d03207441e0b03990b24141c40d031a15038081417401004115000d01c15090b154a40f60340d0004094101d141d450381000d4060140903094100c841050350141c0440d441023110b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 1340250 1250 1339000 1339003
    0x10f05130308150a030212030c06010b0301030605090a02090a0b0102010e0703050d021002090f090901020702040906020406030c03021303120c0f0308010504050c0702010212130f03060204060f02030a080106050904020d020c 97
    0x9408101c1c04205110080781c220000200f03c03100151000c1c1c04107407050b08640800c021054010091009840b041040f090051014480c2d28001c0284102e02c40d101c3d4158a8001d050310070003014001c1c164044009203016a0750020b0094020050b88000201482400c0c0100d02404403205a08014480c0200000400c240003c1c0c82c42142e40a90a40d142031750000307030045c00c1e48140c52125a11140307000c8880840d1078664070741074002c081800018074156280d400f007010344494240c1611004d501103000c0120640602598941c2c0401c1c3c6011464a0041d00700c0c50301c2d0656602010386402c7d0024402c5203003032f008441560880da0454010b61702040755242c005c0030b451090140030b01950400c0f0108a05640c04016a980c0030783c142c01400003032608186904454100030310303004891150703080004042c0c046e03546030006540107102c0540e440e410301201404084a03002070303c04541c001c000c51074860760b016032414150703081880e2043c0da540151000034068016400c01d01c2d101071001491401440c0b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 1341500 1250 1340250 1340281
    0x10204080f01050601090303020c130612050a11011404030807030c0b090102040801180201050d0b06090d030306090c050c0304060503040201020a080307030e0706050f0d020f0f0301060906030b04020307090302010c020102010f05 99
    0x240ea00240f11a9696800440300c00001d0700c402005a40030f44c0d40800c030751030100c0314000300c1d00e8080000640035a0b602d081d03c200c54003608098400da0004903581e824404500c440b40348100d000e0905400d0110441c1b810750382d91103180f1000d007101d64045002000c1500c0fa00b06014000d4115000c012a824070f041e405000f07601030f104060442d8070349085143c441d0561416000c0701a016182c580c2400c40032040b941c0a0800c01682c903a00250820018103166140241072107810b0017580c00040c818244841030080700c440c503140c40d003031010501081d055954004122801d036001443c01b60b440342c4452005138a020301c007070002845a0404410002c4445c0d050b44550040146074007201c004559850b000d56030351060700c40c1b40049180070041301740c0c2003e20782c000b458064030a10b101c919113451a00081a190000e8101c4800182d02c0c1c2c208000555050140081c4d4000488003140b542c2490310340500340c0c601510000381031011814455055a0003988205c440c02c9552070103000c14a030035403180001d0381 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 1342750 1250 1341500 1341523
    0xe011701050106020c010e0103020309150901020a0806090103021c0507030c090902031504020105030106030902030709020705070e010803040501020601150309120806040e01020301030b011a040b0a020a030306061d01030f02090301020408 103
    0x601c1c000000a0300d510020b03201984904c11384035000f102512000440c0a90310050a030142442045070440c1c40034441030400303200c1d02c100740006071100280314005008920140c0210301c03590001c4010300150790354803900c0b19002000c804c9000740840d01e1400f6424403806901c080d000711904100010780d80b0303d540240490324421029544081d413210f800d51862081600c01074006242440140280c5009912a22201c0d000404035206107030b9600301442641d01c4403001b00c03040d40100c0010810000c1344024070b40503040703420107503041c5170074500000c1d600d0b20144180907808030452a41940680254007003081c0741d401031901c0c269400314040240c0810f0007511001d0103107141101200c0341140610903030341604d0784800000b245900e050108100c3c4220030240c0d1010043c10040001d4103640000100003c0c000764004c0d2004480500700a0100c9005130300c51810310480a1003c0e04041c00075041180c85002404d0000740d4405000c42c03d0000c1c010700349826015031000801040f40c03100040d0402407a03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 1344000 1250 1342750 1342753
    0x706030c02060403080c0306030307051f05010b0406020a030e04020408010c0f02070501090f09050601051204050c0102070905040305030612030c070803070b18100506010507020a03080702031b01050703030b0a0e0117 94
    0x264031a510899031107004880140000e4200ea0100d1a4000c0c00001590081401821a03003000d0050722114244214002c4403003030404000101018940103008981c014a41000d409050615040e0080d459500300c8034000d04000e00018905115520356050702c000e8074101f0000c02c030005c0324450140c03a0b5200c0d6546a0050310400710700186961040e2144020b41e411a44650142c51170a00000050040a801c00c0e047c44801c4c40041f008070740345003210744120701403402000305104200c0060704000c459048400b07403030304260810002c00c0d006400c49420002c10b595403200c10f00382c204014114092420b030805540a5410005036043c0c00102424105024445c41a1107880309003240c09070402040c01000540c01a421003000220940c0c80a64407942c1818000d20300715041d40018160111500215a440b04c00f0139444d055050412141c41c20402841882c1060070100b40041c045010f000001010103884081d4000030743c84040c0000020442074035a28115610f0324443e80b500400f41035850303942d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 1345250 1250 1344000 1344011
    0x10e0105010b0f0c070506130e07020307020f0f01021203010f05010e03010b01020601060c080913020a0314010302030705190306020c0102190201060f060509040e06160e09060303030c07140a05070603 87
    0x410103108450480718500506407414210303807001041500b0100c81c0d48458051454001125122a401000c0100b841030210046178208890700101c1e840240105085500c00d000013030060b01c5030401030315451400c50b80c0b6100d0709820340040345890341540d003100b0b5070301c2d0100c00003842081c1c0344402010303600240c1365a440301c40024181070803104c05482c13070f13401a0300402c01005003500407210b01c1651030046028034038158804001c1000c1500f020001e9004d140e0015141480c075515201e0b0001100700c1c02507007200c03035141d600042d984483e2030240c1441240d071310707410b0681040368140e91401103a000f80290745609a00711900d000b0b40210b100008111080090116028810303c030b08026505102c04000322030f8200352080702c20350040c9281c6508203a44005050140344100318261241306c0b68801d442000c2c064180052880d4001c00d0b034603001e50310250a2026994020040c2d951209406582a40320348c01410100c0c2034044006e40728070140a00003644050210115011b07040d12900d4805010707 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 1346500 1250 1345250 1345271
    0xc0e010215040209070509150403030206040b01120c031e0506010807030201110a0c09090305070803090105040c050a180c020102090d0b0603010c08010803031303090504020f0d0507020105091f06031401020a0201 92
    0x76981c02c9600030361004080c1e00040c000c90050b8040c0c4000c4070060805010b08521500c4a5010741c410b410540250340f0850804c020809600590383c050025420011080b05a0f642c2356810344209002c000c1044240301c0f11200d00344465228685030036000f50881d41c095075201c0b0b0ba592545aa800280c0c0001e80000c01d41865038000204030106a13406900545400d140c448a54001c00c0ca500c411400c01200700012804248020301460042840400001e040c2c01d047c6005482c0180580c801401501c001c1c504000c0511401ca1140092a840001082d058000380c0224024851444d0003a84001c41c44c100c501401a600d2311759102c1c1e4230580003007049031615042a614100240300e10b8103250f00030400644100ca424100b0100544070741804041d090700c6500240a0760064951a0302d0201c020425101c0f82a040c096281c00071620b0008119900b4484011503d45d40036041c3d41540c0c6503000382c1140c1482244c0d105100940d00038103d40042c20034030180c1c0b8003071350004006400543c01c1c1000040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 1347750 1250 1346500 1346533
    0x21e0d050601020309030a030e060f0703030c0906020d14030402060c0a080301061202030112020105071401050109150b070506070c11030601030305030702011505090a0906021b0a03020709090c0b0306030a05010c0e0102 95
    0x302c9030b031710080051083e003e05903812152410705004058000d60103100d104007801c1c5c10405421010300c81e440104d110400e0940c000d054142c2984900215030111038100e03002604141c5800b014030501108580d680d030396001264441c86801c01e41c0c1c40c0c0b4070800d20f181090254000141d81a64020380e5030b04200c5440d1050542640028040c0ca00801c00026200c00190b014070010403483d4803070910000035000c0c510311103003114401da00c42006192255150b001a62201c03981001030103504001e01d0030040540c035210b035070300801800b0b10140054181d4410074010100100300c05060000c00700c412941e102d143c024165001959030708095802d01c114040c0d0b6800085041040d69006807020944d0b41c1c0741d04141c4c2c040d1000801c1554116805c22030101180011040e407981190500000e00c3e54034450b1034020700d490910351110515600c1c00d5000740004040c004c085080700c02921400c2d4403516a2000213080001402c0f00411561038816a041007680020301d1081030b1109801341c44a038884540e06030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 1349000 1250 1347750 1347757
    0x2031207080d02030601030906050108010b0102190c060507031b1208010b0703020604020103020a03020702031507090803030108030d0902130c080406110a0c020913050609030706060902070809090406021e0d0506010203 95
    0x20100e0320140072459010510f03070b014507800f1005240100b01d01c04a503e610702120301c2a0850066651286804111035804000c100c5e07640c41062007020540c00d00351100d480310300d281e004801c1040b0002a401c01858802e04280c3d07444841420003880c5035900e89001041d00a042030590082031200e0000540000d0b03c50030b0702c0195070140c000d08219500c030340c01103000b0b501601c000d409040d0700340b102c8800368030b0070025449202c8040840341e0403801c201002500078909580503900399482000188141c000100036140c050340c0740c005c0030504005500c0019800b0600c0c2c1f0109040615000c030390b00c0c10541c40300c0440d000e640600410030031003006190b000c1d22842061303044800b040070401804014180710004030703407103100d80d001480100002c1ea92241009415500324072107900209614040c44401e10900d4014045003100714507001e0b20745e8070341c0d10500a18010034480d10494000500f807104540450703051000c5000d0000e2128003564944105070000c1d00c0c80c0503101d1070b104c0007a082d54000001c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 1350250 1250 1349000 1349003
    0x601020d050a05090d081b0304090e06010302010903030804080f0307050703030c140901110a080c030307020601093b011d01180803040b0403090b0f030f09070609060e0102070510050702031207 84
    0x2c45140440390424461604065242290f80c1d01c03003040b0303584500044e80c0b40b20341005007d001a551f00c51030300b4480c3c010746001d40380c46c611030b8100000400050703806c00301c584100c80e81410541c46039a250309051120b07000d90b12030526030500c00410070000d143d00c40020074103244240c40030803001110b00310071215503a0500001c884100308000111956014506800c034150000c1d0031151002c5803555040c0c0c664010b00440380d003950000c41801a03582d0188000d40c05060009401c02c42c8040c1c05409407015600a50a03041c0c00b5007800c08401030748100c103030340b010211441000784410003200c10354403a2509102e0920b02c07036528115042c1c0b800403e0704241035410707070002d00b0380707003151141d40f204041c200025200301c0520140540025241c20a00c014007400c40c070310a01d440d282d207804420040100c0c001800c40c801500551002d004d0a508141003405807030203843c144000a00314401030345001141d4000c00d40c0b00002285405a80f0351200050003d13501c03e0741500d9102c862151400c001c0d0164040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 1351500 1250 1350250 1350257
    0xc09101502010603200a0801020703050717090901030807020102010e07080601090c020102030603030405040b010504150801180902030d03020c07050a0306050103060b03030a0f030908070f050105040605010b0702010504170a0203030c01050601020d050a 109
    0xe03400445c62200b08441913801d0080c41e031070105a50300700050884e80111800c4011410208135a01800108401703c002c044161034003501e0f005c0340400090410301c050100810381200400d604055900c01d600c034440001c144000c42da50703283c50300b00150b40c0d42000d00c030b8411035a0400d08030011542c4107003341c902030500a002942003a041201300005428a16801d904024003880001062504a00b41c0c0c800d07103000d51a0015107506000643c0d40002620510758991428000e048006840008220201009501c1c0c0183c0b40e00c4610082814007034140d00095028400140110501a582d030120341224803421041090801c040149a128008d1200020201e080641c000000d00d00079001100071520810b05a032920b401941c0300034040347c4188055172039030740d03480800c0104070480c400e0074090304078240003d0810a1310740c0000e00c1881a070252050742d1121420503160014200f1500d2402c40d802425207031240701e4142128001c0ca001c4803410300502c2550100340049000d04210788030031020b607a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 1352750 1250 1351500 1351523
    0x20a020102060402280608070e0114070b100f0602010b0f03060105060f0309010605060f09010201050a02090d020402070c240305010605040e010306021605010204080708010f021204030f020c09101502010603 90
    0x808101350207920080b04110317040140b44003121360107040244c201810700d903180c5140a04115000802900c1450b0400c1c0c1484841440c0c10004000d000680f03c1695204c00710020030f544005c82d01a107035540780d200c0c00c460302c2c2d00c0e040404c81c40e406420a460140013952803e105220f140708040d0f0310b100070710070650070000410003291742e460400001d546c0300e0640382c0040358483c2d950022030800d521161113040001d0002c43c00204541c0e0a0140e0398102d050710b407040d418660850002844403051040081c0700d42e80c00280a8100842c0f04140d400800d0b10015501d00790381c0352500c01c2d15140c070f40e500d44c00000b860b010000c21039500410030745c3c003603c00350b6000740da441e829590ba40000794044400c2c2e40c403221400e8200c0300042c0702400200b000c1c004d004c01030640c00b031a00d070010742943c00665400002d5030043c4080700c0c5580101686503441909841c0401301420705440070380c1410105452190804c3e81d980421280e010303013440b40750803034518030290300c101ca40c407840480c22680d080c00000d02001c1c025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 1354000 1250 1352750 1352753
    0x10302010c0302030910080403030c090609090c020a050a030306051306080307060f200408070812070303150905040602040501080108010c090312021005010f08070506040303050403031202070506040501060510020a0201020604 98
    0xc9641103040c1c0d10034011245450541e400180741d51a02403441c000003468201007104059141c0944261a201c5040c1442c9940c00c010001c5c29a603881e0141c860749640c0c40c103641821038420810000b2140d0404190b4080480d1420001d0241c4060b0260600030300842d44401075a00c0188150b80840b040440514200348250b6221005010041010f917683e903155076046075220303010250740e0155010b049103180d8403880c01c08003038140070966008580b0b6030800b14909a42c1060001280c0840da85840d00141d07500c240400003a50b10850780120b10381c1d9261100f0001008501ea00070b005030b84090300e4910b0030740c1e03882144a086e80d403220060344c001040040100002051150f6103c84c80c0304c03d005035480c0e11120b5426100305e9800364070020700445d03d54010042041c051110740080d010640701d0700d01c1c147c210340b0082d2542c880c03480010100101950070940f078481039410340e005650700c101a01e85500b02400c00074041c1c00540149032045a510a1140036a400054041c4a4607410b802130840782c0e865 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 1355250 1250 1354000 1354007
    0x50103090c0e130b0105030c0904080d11030c04030201030f06060c060902030111120f0c0c06010611010603060c0c0b0106030527010f0603030206070206010b0a08010b07060b030d170603030304030801030201 90
    0x2210211210a521807000c50706020a0b03400501c0f0300c00c000340c40c01d1035010798284141400d0042c2d0046010303402900c054a050744542c01e40c0e562103070300940d1856a800c04884850000c00031402c01c2c8103054404070500010800102c01002100d000340da052148030b0120a10000b2a0000e1140d4408201032400007000103443d030300f004000740d00050002a04a0b080710340b08903180d0086a0800076400b680c010480d5070254a00c056400c001085201414040c01500180da00d0704180141424841c0a03001101c8440c0250850809154012014030520b0b1a203c2c006c0c007580004ac2d0b049850000020000c01c13480d121348506446000300300354201d02d4203000c2e00191103040700b40111040554894030328040c000c0710381c040c04000750702c203500905452a01142c006d00300710042c2c10031441d10703904101042d06103501c00980f905403000e000d180795444442d49407040c010824030507015050f015402203842410341044482c000c0c0c07440d00301204620b54416081540b44e1004440007808180c0950061004d07511 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 1356500 1250 1355250 1355261
    0x412020103090501050a0209040609110306190503030a030c0806010804050c04090201050403080f040501020d05030405030d0507020307060606020d03060503010e0a06020901050c07090603140a03020a11010207030b010e0403020c0306010303020601050103 110
    0x181070009412815441d05425500201e48034084190001904a140c0c185031169000030030070b1500402c45824800c9000c170041c4805446980b288440180d07481c0744480c0d540f1400e00070003000b004ca80d51030401403c06005131020300302c0742d808121910009949035004210704e0b0300c200c1c0e000010340f101052020030840200741d4813906030b0400c8000e01010001509180081141007015868103440768a1700300020701e4442100200c404010040c000d00000550000030303964035807184400415590394800d400c929501a0041c0a082d030750a0110000f030781c0c2c1d00031603d144280801c1d9402c2c0702c45034445081c0741c01c0e01e405080780d94003544208003002c00b09000e40d002d0203040c0300c1494440c0c584021352204174074244441c2c11150400e6070fa03190030070807c0720f440800c01c1e043d9034000c094000040340d038501a4458483c0704016260300303040c295182040e8424072005001d154032110508007940c4500ba02c130101c0c10103c030110301511500341c0c10800380ca40050140c1c100c17681035000300216030a29004402410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 1357750 1250 1356500 1356503
    0x308070305090c06070c03020405100f09050601050c0316050c01021f0507024204050a11130608010902090603010e0d0e030102040b0301060e091803070305030402060409060602070306060b030c0412 86
    0x22002e5500d0f41d07a56040080141038012960450402c1c1035004000866102600401a07418444810080c12100710b02c0d01c000c50703440f20380025460f07840d8001603621f4415034a00031500e010014405800616094801c0905802501120090b42a0384010790f6200c00b1807144200c06411201920060b910940020303038444100d1050f00c43c1204030384510300c0b4507001d980100e0f9148030529890101c1014800000300b603503510217001c56141c02d0a80f44c41c0d445006020024146000c038265401007074483c107146002e09524a05c003000110390f01c0c2c458500800329060120301c5048007202041c810301e0305016a11140040c0400392141302c01600094800c0b035510281550195020700001610030101c0b400b440c000d00441c0c0300e80d42c9005844040001c4100300800144c0d2505240190441102c40081520f110544c11700b07280e030362034071103000151150240e0f50051980d02c2c10000c0c007080603030f40880c200b000c8a205141c1130002503115450f221403400110b07089615110f0502041003d0500303080302042e4213 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 1359000 1250 1357750 1357753
    0x3070c0f0f05030a020703031202030c0a0305040201020109021201060602060615040e190c0e0108060103060b0a03090305040302030a0507030201080903030f040206070204020705100c020c01050403020a141504060309060e0a030807030509 103
    0x1446107680b11400c58106500480240c0c100800c20001d00d03401182c09100000d1208085141d450240550030700e500849200100f010380d103000203000c59000f544210700141c0c0080001050006080c0481d01030482402014014000e0b200030440c9414410010100c5251342e03000c09080038108940ca2510340001000c000300c03a6161560100c00f28070512a0780c16044440c1c0d6101810100100050210030f00900080c0c10946043c904101d0394113800107035004482281b4002c9400b41d42d40c28200d0301c90045400195043c028200c1210810400042041c2107074400c6c0c0b910484c5035648189143c0764041102d41402c0f00d640c91001a006103030001c000c00358036200500040c10080d0030340300e003450603070078407220b00e0f8a6a0b039070550b00b0255010003c0b02d01307115091030032a281500315400300f84280401d201381c245000c070b44800d0300381c0381e80c03400f5844141100c946116520307a551441c0040c042c01095100340c3c4c2c400d1074101e400b01c03460404201e000050350913403a01e07441c03a21600c0f8111300521005240414a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1360250 1250 1359000 1359023
    0x20109030602070503030402090609130305030601090b0f030601030606050c060f06010c050307110f030102040f050907030b1305041104060503030a140d0c020303060a0801020c060c0705070e0103062003070c0f 91
    0x7652480680020342c000c600660710303803801d4414841054070190501d486006114100b182031544a000c80c03041d10781c14500241c4176254040145c60042860304542407114003c12200c0305080c41c01c0140d0b1080e48266014440503941e40300c141c82912419a4018840d040640000c0c0414030580d02590000010700d800b98038050a503d49508603041400203d40c1051030191140851500441c1d2514513502180218075191416000085003070f010f118490081907000000740e072042c0070b03520a04e407030170016164602a24034003015078010141154101d0346411070100e40c00890419205800036108054000c44c984017400d0400c0e03c0381c207400c0e4500124118208107103c1c0e000850b0240d030048100d03d800954a83c140482000034900751600030300d55581c410b200c1890b4a540c0050126001013000c00720301e07901d40081c02c1250404542c1e40000c1c0c110310030303000004100041a801215a00081e10020203100b0300103080458510007074a403400011207910782da0000c60034031000700d003c041c0303d101810035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1361500 1250 1360250 1360253
    0x71412030a0905010507080601020a0314090402040326070f020603040c050406080102090301050f04030c0b09070806070905040b0102010603020303090f06071203090308011a03010603021c050108030415090b0403020d02010903 98
    0xa1a403045550000c12038550051808201c0c00340621038002d45642024071152902d01d00013035440c0d40303c9402508014059144000803444082200c0724110060015541ca03510b900300411032041100c4440c042a0303a1a81500c412828502030b2003006500c90f0a016150341c0c15000c00220381c002810650b00402c01c00000101c0f03a449110350b0b0b0043c9240c50000d80c840e8121410942140c00003450b1102c44040f0f00b0411000a60058088082ea41c0c0900d01c101701e0345907580000e1038080d06030400050b91082109020603150032094150807920f00702c1c2c0c11f01c1009407000c01242a54250300c0002e40540c010b000150710b610301880d04202c1c2c407078040c0410b824002c6a449100216420310041004269140c0306501031591207410b4601502c201d11643c800064020303200131007840144945410180d0204042192007254001c500d804007007100c041c001035845201c1c6603240da116200d01103a2621141d55910110300078030200c0c0858000310703405400c0038503503001d0003801c5020040407410004d103805d0100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1362750 1250 1361500 1361533
    0x170c010f0605010306120503030105061c0e0105100801020703080601030f02070203010212010303080c0c0601030b0a0f0e070906090b0109120201020c09040c0f050402070203060711010e03040b180a030203030714 92
    0x20030840004010409600d010005012545250002a03407482c4035081280400d1000040b80c0c1140d400ba542959103100d240c00340c040400100032040716171414110015031000054110500609000c41101e6105955061043c200e100d4040c0c0100802c0c0c42c140024911360007a0f005846540c0c24000151130304180b40d00003801c83c2c1c8100ca16039414100c1c0c10043c0305044e403040415071b00c109001400792038402e08000b220303a90881407000401c10403c84000840390b401581101c06082c69260052000c04030300c004e1039880e0f190500036030300e80c14645800000c04000b60300800d00381c0d440685a00e030701d13503003031541c1c200d40b200d00f13064107070306610588544181940b12540c59520541c0503038540100c039810801c280145c5030716544454461401401120096074000c20749035000b0101e400e0410301d102c04910300c2809000710003804000c03070001140001d15400ba00c0c0041000088061051562a801c04104103c800c2c0c00d0001075050380c000d10108000880304a842c030b2022251900300e0b0400240769070b240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1364000 1250 1362750 1362761
    0x606040b040807080706020a02060304080a050d020703030509010c05130315020c0d0906030e010b06040b07020a03050607030e010506040c02030412030509030607030603060b030606090a020f0408030f0301051207030f170c01 97
    0x318210b41c000f4800f000200014404d210180ca05032000d0308000321203400281280c000507102030000000007a54941c0940203504481031204030a0040d501d40c0700c203050180040904031081a015424409041c850034800d00466594440f620200090b03142107860f13420302d500c1050300d030082a0768201324014030082c082201410a05072035541a44c1142458802400d03030b8582e00040215a0511007130600710b5485c4003d4070141c0d400d000c06583c4460140c000188444000c0d0300c00b40a40c01050140410244d054101d40e4080c0d0504001307000648456080c0030407114000c1000c001a00240014042ca29641050400041c02890b20609090f02140000d0a041c000e403554000300307075109000c000304842402940041903085003d003800d0310344080420131001c1d0040402030203550024103d40c4a003480000e5402500340d0208403911940103880081d502ea0003801894460b0983e0603201c419a00d002624605980e4003041c0c0c503000501c15503815840fa0f0280a206003001c0d4240080c1003445024480c0c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1365250 1250 1364000 1364009
    0x20904060906080d02060702070501050901020309040c020304050414010305120307121406090901050708060114070f0602040e06121504030c0b04030801090b0406050102070302060c0a020904050105040201080a02120f0606040b04 99
    0x82e205140104140c03620000013009030954008100700014030341c001c9101d8044500a003802580c4c0c50002c40100d02b54410112251351007841e1410340c400c000e500001030016540709076010440399400c0401c041c03201c1d000344002016a442221202880c402480140d41c0020b4a03040c204498100ca1030300c0c0058400c85101c3c0800b0729143c200300080f81c54507503051034108010000030840f0341003a02c00108024001070986c2e042c800684a041d00142c036034004c46000541040086100e00f10034580300d4041e41c814131584010080c4007010030b19034a0400c0880c51080301c0c01c4001c01507401c1005120301e10381d40080040c0d046c890035a0b2410080b03820300301d032144200d1203550b82016560602c4081d104485076280014011450300805120590300020040123a98040354690f84410649602e0342c80d003160118021b4025100b02c090100300a4150040782c0120b1003600c03011043c0ea2401c100e41e04034052902c000541c0b04596000c2003d03022100d412640194002c4c25082ca45900ca07101404c160340207500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1366500 1250 1365250 1365269
    0x103030507050105060d030f0f0908030c03030105130e0d0c0213020408031c0501050d02011d0301020f04180506060d0e0106050312042603030403051602100306091805030307110102090406 82
    0xe00200b0440e0038400c0a620039001c641c516491b160721b8800414990b00c040300c5500388100300340c1c0007851500815407040149510821070740d90b00d0000c0e05280d140c1d0828440e080c043c1c5140600e80103802e40c1030040c900c0010110000302444501680110b80101c8240c505a0300036a8202420810000c00c0c0028006440700c1c400655490050080c2c8025802c001f09030b80031650b24150040c4080d17500d0520180502c0d07024a05038118982410b002e59030a042c4d03400030fa9140d81300240350140903440714050400c41c1c0c6200000300c141c005210b01c00b001e8500031a180366001c00b0420244201007003540c00b000c1000041000002c242e501c0302e01003880c20115004a258401c804207081110802c200018003800c6108004207070016904080241c1e24000035200605202003ca1710f080113441c0d507401c80310903603001003c603800c0310b0b5104006001072105000300354600d420204101c40850b4014003013041300e0b5100300250318558401c1c104a03544181001d00d096555000c0000901c07690b5540207401c0600324422 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1367750 1250 1366500 1366507
    0x30606030a02040f0303080612010c140f0c0601030b040203060106030b0901060c030c051501080c04060b0d0e1203010306020a08070509010f050a03060b0705060702070608090303010e040c0305030d06080d020102040302060904020a0e030601030305 107
    0x1010409c10701c1403030805a280c5d0307050074462042164450602c0c00071941c0c1c584803948410509015040d0b90285640300e03a801d11445000109000390500386a000341d00039002e960890b6210017084081e2141c40700d4081c0c100c94000c0040000c00d01c103545600340c5c203003c0d1500a0000815507500e60810003440c0b85054030111000040c0203908080c850007a81e088212070401407949070075580101ca0280304603d0303c0860b85c036501c60404030310511200b8003006030380303203103a03540d40c0c50f8504074009410003203080d00001c03c00400208520f00920031948000016181c200c401c04c80090704903405d601c01501001050b4540c100001c0400303220000d4410244600040c2c4041c2c50034080007442d0084544c80b20040084940030321050750f00100c1101d056980502010049a45a06101651060030740c00106144000105800705001650050050342c1080003582c2d5100748d2000c04038241c1c00f541c040070303520401c1001065001d02d040e0b401425010018123282401e402104002400d002c0300340e000f60003149000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1369000 1250 1367750 1367761
    0x9060103020a0504020c1002130b03010608040302010f0b0105160507080d091a09010909020702010201090213020a020c030303010510030506030109020d0803040302011103011202010309140d0c050c04090503030606030a02040f030308 101
    0x542e400c040c2c002130310110b04152108512540c1d400250740480005c560000d103a162403054141307401e0140a00849040c1d59595403000101068011142070340154a4800e0602c43c40348a400b600d151600142d4907541002a4003002c41846244084102c0795481800c0c400038000d5004c0c06000030b0303019141c13102085240741c5400384105100403407500308400020070446605a801c058107400b503803403506005072156500c1c80144e004101d1000080c1d80800514607407446000250010441d040c0030354240c4022865110906a0328002030244e0b90340003d1107405100d03000e2280d0320269002e40010000f14065441d5008244001710034502603d404000000f003100703141c1c090046040307038010710480c24611743c074081401c4111888950005d04141c0c5a9032480280844001c00d01c00d1600c61505907000280d603d07a000c0c00141c4010002c445600509460300181d19152091100d001e4018029514580e6641e04100c0b469100078848002142d0030b120104a650382e048250b03020314480c0c4c50720800ea0808 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1370250 1250 1369000 1369009
    0x705090312040b0406110f010501030804030203010c1706040917070605040b0906040201020a02060703022103100605120109050709080d030b0108090109020f010806061b070302010809070807030f020114030906010302 94
    0x6489602078614080104100e0501040c00b01c1c2e003110356610702400c1940c03c460703e103030a01c81b241080c07600c5582000000320910825a000b00b00300c1c2c1c400c800805c121109190207580d907150b60346810f140c038813070781d00001e00c0ea040c9500080b5015120b03032400400b483d8420708840d00c5800c102c030180c034a40c1d6510708210030444440100c80c0c01c0840e400040141c1d242540c0000d51f202c1d00608003d000703ea02145a004241c003c104042d1381040b1805030728000034407842c03647d8080e00111240c03030079024011070000f5418061411507034085020080f6810582c20001a02c0c09420050950700400103d035000240d1160f0074840700199195994000c65003010803c0014003410014203030f50100c0e490000804016911003010900502080c20100e0981d502e41c00050080c0c010004c00d024003001100c90510404c102007042000e591007600c40b400691a01e00182c1c0e0b881c4803034028030102c0c0e405007005001240c241082d59000a01c14900f01080250b40801c000854000707840d4030003203511076001071085282 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1371500 1250 1370250 1370263
    0x1060306050f06031609110412051513020f060c03040b03070801030302070509070807080703020c0a060605040f020903060114030c04090b070207061103090105071401050108060406050105090c0906090f03010507050903 95
    0x302c004180d40c0c036000c0c800e034170900514415002069a00e59188590710104025239006110b8803890608403640b41c00e080d40c0f600d0300381c1da10150680040002528240306071502040b61a00600300c0b0a103103035140c051210690210101d80309500c0184000a0340c5004540114802d02c1c10f50b89440c4a5450b504e8040d18114280d0805403140c540d80e01004005984520051f601202c145031440c401d407900c0314141d000380328980016440f030141900f0107052103075641000044032400d87d0100709083c216800c4408a00400c210668560070a00040104500002c90f1014100f4014166808a005000020b0840b42c0c02c0744119000200d500800101e10303010b0040b1001040d0074109800c20791310b111211900c2c1d2007141c4080d4140800410064184500001d107214100c40c010005c020700d503101c440e01661640225021210b007030901001041078140501d0b0280614050705489080a000c00c003004a503401c80203100d038001a610700045280c0d03500b401001e020f1262038507415640c41c513840a0508000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1372750 1250 1371500 1371511
    0x70f0e06010504061b03030e0303070c0c05030303130b0a0f0203040606030203100c0210090510020a0206100609030308010e040812011401020f0106030f0b0705070c060207090e0a0b0403030b060403020301060306050f 94
    0x380020044c144d04404c4002c01e40300b8650b01042c0d0a440c030725003a8000e200180c0c290002c0e10001c4100710220703405c5039040f19403130b001c0c4140c01c0c0007550360001c2680d2880120b0741803074101c14403882e01d00065050f21007aa04021a00004520303d19105c00703800032600116410b882e6951a8001041542818022042810601c000611404042050103955030145442c00071180d0782d42c2d1207200c03d010707007441043c0c0c0ea42d40c5110259901c031102c200007581d0344416a00140c1c0c4001d12030002801c00e0081d10b20b981165419110510140c0c60001d8049102e0780c024004d0341c041c1003c104e0041c0030358213000b40902074140f14000c007070b107410004002460318200000303400d501d130b142001c28404a8281d0140211842e80802940e006607914001103c0303502a80c640100b1040302e00e0340104a00b0303004600c800a88024141c00c1208407604450281e460440c07481c0504412481c4001c140402e22036000303003400c14000b80075545010756950109003161100d80c02510356036910428010404800101140c00a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1374000 1250 1372750 1372757
    0x60506090f2202030406050103020a08070608160e03031306080a0e03070204050a02070510050601120501030305030a2c0304090501080303010303050415030b0405070e04050108010203090a11060903070f0e0601 91
    0x3058403010904400e18965628854085101040807400c900394604400c409002400d640f00e04091400310090030081c00101d20071182c60b8408108410002507080c101e642c00d40d68500d86032260602200c501500811490400504043d00e0030180c0701000249080303103401c00102c41036403504400400c54540038042602c01801c1c161003503c403103000411740e02e44503011100010700d900c0700c7c0c1c15800207102d00140102a03005a10010040d00e40c00d500c2071f84a6842030303c0d012600d00510308418121749003400000c01151040c00401c10000d4650321000b560a24840e58072030310b22085801d040c244568a42c1e0b030000c1c0d80002000d00411030b80d40603590040c0125070040d400c0d541190fa010381140207a014039001c910004000c54485842a0080c6581c8880500b00300100e08000c034004281c06a44e8560703034004d6007080700001c0d183c201407086921403079200000e00710001040d59030201001030301c1510303984443d061000001c03982c3c0901880300200110750503403085034070303040030403440c41d2000304000d060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1375250 1250 1374000 1374007
    0xc03021509030702040b0f090408030103060e06040201080103030c0f060204150909020703140d06030605010308030403021b010206060f01030204030b070804120309030e01050d0e0105010b0307090e010b07080c10090302030706060506 101
    0x201c0d0380003080d940c000da411240498108540e4011880e50391803c181c0e103034810745100603c400e0108080045068902a017420f001100308034041580e2403606440c000c3c0020007410042001c640f10350701a500ca00c0c03051007402c00003002900c0781c20690300903030001000304028500e400ca44a4000f10528020240c0b8a0300791b08207202a20080c000300c010b00e02128100c000080c14511813000740e40004050b503488201000596180c4c14004a15041150100c000d40300740d00501013004000c0e0490851110164010812035507508180702c0b08a0070020102c4c1815000d020110024480c4913456104e184c043d41c82c65454135107800c00480c4005064880c9060520704003420002c65405200101c82040c2824110b81c0c81c1c10051400c03006060000035212254178050010586559000096000c1c0d81e0a07914090300585030f0703034956040c2c80d0070300c65119065020040000080c0e000ca020f00042100c0005413880541000b03d84400c0e156404000c81c0182c00020310581007024070301c0f43c9400b078603042e18080d08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1376500 1250 1375250 1375261
    0x103140f0109060c0e030a020303030a0203060102070308070503090a09021e0a03090503030901050403081308031308040308030f0106080a0b010c0f02010203040807060504050102070e01050f010e04020d020a0809100c0c0602031003080a0c030215 106
    0x100ca20010b0513341d0490340000029107075900801c10300c001540e100a50355030f42d4607141015a180d4029130382c10743c0708d5410610b0010b0740861500039241e05130340c680c0301c500d001510342010310080d6002803400014903403145900004a0010301c0510720580a880c004150392407d4940180106401807225450030480c21064001c201d84405803507003d04002039990845605003000c188901403a03200400c0c4070340010800000e0104005454121002038841140c5a101e0f1603004d41503840c0d220040380096509190346010981000b120020f113401801601c0c50301e52a14000c5050681c1500032402042001504107d15641001600010206501c0030201541041c2c00500c015080707207991130403c80e4584501e10346540d183e040315140104c103038045580c0d1642d07240291800a04844031101d0740a55a11814480d410b4001c81440d5101644c0b0508000110ba503800000d42015000e0052900b8000700070002034000f500600c00c2e41043d0f211711768503002c0c40c41c00074504040080c0c09801009100306004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1377750 1250 1376500 1376503
    0x304080301060c1106040305031206060c0a08090402040506030c0307020c0103060302010f0c06061710060506030702030307120e010203041505070905030c011d06040f06020d05040302090103140f0109060c0e030a0203 94
    0xe055880c0d42c43d26204100c0241888016416811285680030320000b5001040100020050140d0504400e6406c481d5840ca02000071034041d4545030080782c2c002004650004004900070300f6540d900500040c02c254a80d0702049140d003080700c03010b00082c00001406030799901040311400034103092900380155030a40d40000c0060701e25511a4090104400f4030381c082040c20b0300204054010038801c038031100c02010020340c2da0408400c00b030410902c0d142002c02c3d1030402400300da11034121034004610355154120300300d0ba081b100001c90380c002552480301d0400d625081c001940076074010400c030f10003117101782400c0d001c5520140c0580309000c01d888003000140c801040c05a02d43d03000f42000018104501940c40940848042031a40100b000501041580c128030032141522500ea0032648921601c141c01d43c3e183c403440c0000395200060100410003d504084105c01c000101000e580c500c0c070400519030b0070741d65540f8003140ca00351900b003003484850b80b180c5041c0030142c084000700f0003014183c0200c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1379000 1250 1377750 1377757
    0x60702010e0402071202160602010504050303010b07020d060906050103020f0d0506010506030a06050405011d01060f0507110109090c0309020906010905010c060203060d0209040303020c010605010309030203120405010f0e0102090405090102030408 107
    0x2414800e681c040c110381a550780e0305071580340b50400084015080e900d00000d498440c01c0c2d0081d002e990040401140d554814803400c0d01c034a500c4070007145544d00f03007145083e0300c2e0012042240d100c0c07201c00d082c80003d441d42c0181c1c56000d1007107501242c154107520400614004082c05507016140891021010480002e0901d04444083d2400c0340c4e079803290540c082c003400294104640043c184000040e420040c440c0e51009186802d183e0f0580d40d0700c642c011682d5404602000c3c2c0014014440d800c0410b0050400509210050411030000c59940d40360005a892944699010a50341e04c0105c0541c102614241c0e4041801d00e04954410b090100285c48000c107034002424441d40440014843d8030313615200c1c01c081c0d030028542c800c0da1420f0f19004001e9400003946003001c2d400c10100080139406409180c03003540e0303d0340107541400c10380c00c002c0030f4005000f40180c6466498441110040071030340b2030f8040f9076407840c00140e42d443d00442407000360751000e4640440c0303030310400c03c2001051031501135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1380250 1250 1379000 1379003
    0x604050403030b120304210f0308090307060606020309030d0504050105120402030102161b090902010801030204090c0f0f030203060108030306010c1202070503100f0e0606010f030e030d02040902040509010b090607 93
    0x165910345080403002081c3d112401034100300b110f200c02242010000150088403009058805140da103030300e2200f01904c4da0300c0700400076103003155a80006401004543e0340072a015044030304000c15511030302c2c107071003003030f4403103005600005011031881c00d0a200020200b003030390518030700e03051403c400208144180072070407132504070110100d400c555081d01204d2440354001075003446070071182406030030315010551744107884000f0303070001400d2074850040c0480180c0503142c81000f40e1964082c070000d00040c101c01c9400c1580030602141c03551010503804060b08181007803407101780c00d5106052038914117810880869100307000700419607901c010100030140d802a048503002c418071009918100795500040e50500918050000426850740b084000d041849400d01000030f01290340c43e11682d00342c071304600055020604100143c000d03004074007649105011a4540800c0c1aa000200d0308240c114000150300090108503920b01074440f41d01601400c0001803a01d02d0706800240103200da042e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1381500 1250 1380250 1380259
    0x50105070201020c040501060305010608100605070305030601020114010602030a1103030f010311060705030f070606050108090c01030e1203090601081203070e0103090804030204021204030311090f0d0206040b040612060501050903030306 103
    0x1145001c5920a005250241d000034005000a50311103201402902c800d003c3c1030005036040002410500d400e10001d01140c504e62561031908086850072501d9074002800303141550b4803071301842050550b03600740344d00a241582c040c41e181c20581c0300c01000b45d4409070f00c2c0281540103005000d40d19500701880b6044990000d2441c200070004d2340030038100d009a5a0240480c08045850705482c000c51004000c100e00c110010000030791035800540b020107041d1580043e5500000d2142483d5000f5403101c080c1440b603200303c0b600c0992070800b040e425482114084050b030801c900411400b00c003041440000c0c1c22000e4241c0c1103203400b00006140d140072260060401d03445154003410f00c1039400c115001395030040e00542d9109402e2000c1d005001041d2811030010b4644424010380030300c031200761205408018400c42070042d4840402c00302e42261031040c2d1b40040c1c100f0001440740100c8009000400c440c0c0c40c2c80314501e140004120807038200e0b90242e814410100300086023642c004c411687d10040849 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1382750 1250 1381500 1381507
    0x9010917010f110414060724020304060b0406060f080405030408010c0e0f0d2109090612030807030501050105041205030405100908010b0102070302011707030906060b0919050604060f0216030308040219030804050105 94
    0x101048c9003202ca246000000c881d15401c0101d002058008511a9000d43c105018984441c0140003c44100b48240400545201c4a0000d450b00c10303200b0540150260781145d0030b06468040f00c038219295601e400f40440d02d92400a07482e42030201001014541c1201c80f104950001d4a400f449490481141192402c092404080700742c0206402c1c000391030280d60802500703840744180b5501910080d016170102d0302d50300006200c036210340510760507202c2c1032751802e0a091810080c031480d85003074441214035000610001c1180e44850301007100043c3c00e5a03a0034242c070b140071012400c641c104a4600e0442d00208814000f42c0d0300704010842d54050481c0407074041c1d540e060308070300a000501c8000c20070f90810600150b00d0390b03641c0192240041c11102c01c41408103031602420290003030700c1440d8000794213100400586008050003043c001c3c0e02d0041e138510030000d450100e002da401c0d420403404510140f0601c001c0d0b0400a004400c00030310075580303211041c210348403108075000b2403052070304108000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1384000 1250 1382750 1382753
    0x10c08070f0b010605070302060a0c020c0d02010e0402070303140c0403170702030f1002040602070e01081005060105040e040b07270302040b0f09040c060f02031305010509010917010f1104140607 85
    0xc881e8104415080001d200880d61940d10080036640841b01c2540148a62804158000490b2103008824a401d40042c04144200d2041c0318200810210582c14014000301015281d140c2c1d00007000c0f583c0c42551300050b03008940e00e013503051101c003a050805218040c1310a10014844903806100060100744080d1110418030000b0726000c001605401980074580c114400300d00c090300540151107440e0261400c00d51507080e9001480780034850604075a115125400c0380714665031100707400030b0043c1f410924003912240e0200c480c840c00d41d01160800c0006003042100b80d4490800c0c11441036440450f07d103001c50440c003103030008990001030700c2141c0d202c030891500e90b1013410601c00a00301034413000b81d0740360509041c1107099643c07181c0d0002c07510a244d910103191000c0b08032604603c04c15000e40800d8100001141c82da04410510b5043c00503a40b80800c41e411000c00400c0100d12400c004520004018041e105541303078000c0000300e0803818002030008452180c0e1741c40e4000d109580858544105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1385250 1250 1384000 1384013
    0x4030c020402071e05060402040b010f02060103080307030608030403050708010507080103020f0906010207080d031407050306010903060f060306141b03010b160f0602120103030e031b01030203060d02091009060504020405010c0807 100
    0x218421000012042910812801080c21b40c41103000304e904000d500701c800015180b2503410b00c038403030058100c10014000505908081c41d005561441c0000b0f525440b0040a803840d1300c240c0003a40c0651008800300400d1109001d80e551111345807074005050351459020231144000481c0032445203103800d0004a2591003081494010b0400c04225080f0130303210000900200381c105182600c0040e0840007951441c051b03402c4074054081a511008800c1c0785443c0c1000904500c4140061036894180000c0440c6003405021b04030b2010080700d0b002c40c18510f42e045d012402039080c01c2203401040c0700420150001009a0708140600d0503040c4a9000c035290400315000070b4840100304a1022807030038195411807036a41d060368401d4981182c000a000209a52400f2050381c0002008006008d00050f5200390003454000801410a400201c21a40000c9c61000c0448200c4141e42004004002250382402154020603003610114070340783c01c280000b0402c03204403c020701078110004041c01045403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1386500 1250 1385250 1385273
    0xa0906031a04060b070c120201080c0a0201090506040c080606030601060905150403020d05030c0d0507050309040b0303070203010903020309040b010507020319170d060311030114070e01030609020409050103020102070e04030c02040207 102
    0x4010b1040190a07143c01560903d50007144059442084210b40070174607000c1d084a0300007841c2c050711408540da4441c44a4002036020000d00821952503260407800200c003009024000e5114030844002c2908258800e4505400113001602c00d03403081e00100011500a6110300c2615020b030740461085841060b81c4c040d0388030700c0e03200075000180560301e0b0040c000003001030301c08030b1503050588500c0b004021044810340200000503260340c2007040080518686036000344161072f03000d07003070780d051030415000282103464013242500940c00006150340d203403510340318009400d03209082c00c07410100a50040b0b642c901c1080104c0d03c03215190710381142804507980094401142c401740040c3c1d104020f0800c1c0d4054001342c031049a1506840840704076919040c003804035840344000c112101036503682da040300c3d4441a49001e50501d03980d480c0203e1503152900080000d0135486002055035451407000900e040b405c1d42c040c1602420703000c2444000b80d800000c1814442d0110340140e00c8140030f05041e901803070b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1387750 1250 1386500 1386551
    0x2060309011806020d0506010918020702041407080121030507120203040b070c0905010e0903090d06020903010204140f01080708070c0201090e09010903090801050c040303050c010e060c0408060703020a090603 91
    0x2500142c0c400100126074000741606010442c041c0803540310403005450810080c01903141c003080140007049040703000ea018000e0f290005002048400350300102007114681628a00001400c10005004640c001d00034015118901e0891a50031081074130020054043d034400140302c14210361415081a1082050310003804c40c042056a842802d0302c0c2072807400ca12846521030346402c1000010700c0e00b02d1421007510401a803c00355142c42c000b00304004184c00d0b00300c01101d24944c04c0c401c80c0f4254400744041c2014210360a4008210300d120007c204011040304501410031811000304804039601c10001600403420b420800626540d034801614045200e41090741e101e8400c40400542036070540100381d240780680c444603100354a468a0a090310030896200352030200420080000070711174001000020525000000c02045400f12242080c030151340140200c0030200d014012940184009134100000341811407a1a500e002d0140035031038148201c1e8141a0b070b038480c04080c000001c1d880b00341217 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1389000 1250 1387750 1387781
    0xd050726031003050607140712090b0301080f0c0904030905090403020a0503340201020303060f040906060303020d020d020304050d081606050a0c021002040302030606040504080d090803041101030b010c0206030901 93
    0x2c0c5020550004021440e01c810345091203880e002c16084c0c1d0003020075940ca1080440c40925000c0c40b40c4490950180700d080010030021071400001c0c8881d0010043c0d8003074403520000d05404802440c9aa29004031108001c0c8686115018840081e81003101d0324225001a21755a8440c0c1e904d017000c2e428030782c00d142c02520031701000a0f54401d1070303080d0741514103801d040e84010706101d40c801c43c20504030b00c841c40d0007405a401040451158a40000c0021440100400c085611810340d5105801c2d03d45541c011000f6900c400e001c4415150188814910303c19988015030030315241100040100c0074058000d8a003141c00103010408030004803a070b0700610740242050109040c5032000780e00410440b43c02d00014001d2122540254001d8021901200d0b0010014130058403210704000082c403015000b1038810104110950310000b0f21b0040503101c5001d918495164506400c0041e140c00f0050b0000e41094586012880c1030382c2c100c2c99681c111601901c91903181d54454404034014280416600c409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1390250 1250 1389000 1389007
    0x40b06070f03030b0a0b09011202030c090d08040806010e090c01030903050c0105040b01060e0a0b0f0a02030c070311010905040204030b0a0504020f03010e0a060c0905090a020904090204020301090902030705030d050726 95
    0xd15803d43c01a01410780240c075001045a070301c0c030840c0ca1600444c40410f00180402682c200000038580103150815a04440e5504e4060b0340c10015526186e05c440843d6a8900490100084001402100d005000001002d4117500d00b40380302030345411000d48424181a40c50003400145403147e000d0f102c400c641c15000300160705160070454000342003407046c0c01c00544500003d45103801c0030441e00d0103c07100200101e04100c41c44a801125070481303410387d021032005000405031002d0030400c0038029805a01020800f8640400040540845410142c02240100420800941c400501650200403400c0024441c0ca0b1840050b180045181c131050b419800c001f8402d44074400451001d4040340300b8030040000b07801d07000c0140c40388903051003240d6000b4000710005081c000b00b0380007041500c000810001e00651b285c2c2c0050120b0b0400c2e0010305949a4038035543c000c50070300700113010140004800800c406071664100030014421000000c002100c10b07c1419400c0c003a61040e0601650750841d031585 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1391500 1250 1390250 1390253
    0x102040e0112020907030b0303070609050f030f0307030b030d09031b05030d02010c0305060306090705010f0306030501051006030e0606030606010c020a03020306130203060106030e0d030c050903060106120605040209060702040b06070f 102
    0x202030340390030b605034403c5407460040342203603000c0e10400b01c40c0b030030150185040022544842000b0f1035605020341e600c1c0500d00030342da403e4034284010620202c045c140b003a22070502c01c0000b811120b1018550340a03501c92440080c0c900e402045440c1140d43c8800800030411a4400c09211600e20390b201035018030030314010b01d01468064112514440e19544e0412580e40c640c010196102c1c0251040c130041d070066481400203510490449885128a04000c40d10f01c1d0740faa1050700b1140200e8120300d00c60030240b8144a2140c0c1400341042c90360400c0000d10060400030000b0b87c80343c40181145040c0100140014115290485200003d40e0014103491082c40d15081c40d0420002c9000200d10a0090f9000031030503a000c0d2040c403003105441f1004004181046a09a0040404240d503a00380b040500018100b0780d407c001c0309000e40090358421001da00f4003041441501c00c9900220b1240c0e00520900019445140555400640440303010960303c0e4544007144030f41c0318848001e05a000709550000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1392750 1250 1391500 1391519
    0x6070c03050f010c0302090f09060619020601060f0804050601090c0e030303040f06110301080a02040c110a050f0106290904060e0403050903100623190806100801020306010f050703020102040e01 85
    0x508541500c0004d0244400d20303202181248a604d03505644035806d02400c40f0706d030800d1580c5540c401c0000d4020b03417400c5602124441051072075220000140c1c400c00c014000c61344d01c10203118040a650601e90490b00300303951a90b0701c0303d005028032a00b0580e1070341c0d40469a44101e0705c05640c1c6030083d06803a41c0b401c0c00d003851452006050004c0e0790060074000c000072803410b0310b81101d040b121020003074903003000c45500b04000b40201c0d0714a00b0820400a19a0020034800d0006481c034134801c0c401000b030000803115442c2580c41c694400d40400c14104c1d56407810f0f09214010825212543e14003650714600c00e000500200000d40060681da83d4074800c00c01015040001082034a2003101252014041d001c602010f83e40b890050728213100800741c0c3c40210040d041900020950300805030304961a80d0b8900b02031910f02584038091550082c8280401c064282c6041c0010f0403c4e0300c002e42c95490031100213459164170749901010040001420000e00d8401c2d03042d900030302804080d00c0c1d0300d07581d90b038083c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1394000 1250 1392750 1392763
    0x1060504050105010203090102030301030b0406110307050d050a06080d05030901020408030406090609120f0209060301110a050703030e010908070b040606050d03030b090901090309050d020604080a03090305150603030d020906070c0305 102
    0x1a00541c6032100120b002d60001044c1c40c15240140d00940c610b80c01d42c2e45010341d00c6400b6104a60464a40e48403843d030700824805148034003c1031f42d0b140d807125030201580c0c3c192140a80b4158100d8039040c0240030f103c0010801032a50012400d16503074030b444d4040750b40d00921a03a0700c22000c900010030045502030380b105801c4110341701030341c840781c500e9101c80c2120351025031102e004080c802e41c000100010b04120040c03d501040080000038041c2034805c2c01e460700e40c4183c90690018000080040800d0b801d48101c501e5501c6440003040366461558408945103e039800250901e64a48006010814070740c000d0405800041e001c10540e000c5840c026000c3c007150b0310703203071300c0750204100055090505220b0900b00d140c00d643c2c0d984841e0f1525080c4680d0403088881070360018002c05c008514039204201c01901148642e443d100e1725861401c00d182070121800d0711041041e40071040c00b032159400420703201e8555103640c00599a611000010b001b41c440c0a000038100080880000f09011012405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1395250 1250 1394000 1394009
    0x904050a14070b0301060f05090d0302030406090e0402030312040804080111040905160c0201050c0102040801050112110a0308090f0406050d06050403020606030c130b01020a0209151005090105031503120a020106 92
    0x101c00c0780003040049151900358a0040e28110f5030207000421000784101458486032415042051814009100ac0f4003003032103d044c20b0300075a200050410610360322112583c02400046002076860805070300082e124800d8004801b200400d150119051000000c01c039402441c47c1d20003001101019118500390790418032070516014035080c00142080c0c0c03000110711842d82199a0341e1840c0c0e6050340152210f0300407828000c00c0f076609100100b10420244945800b0308030301d1001100d0304200746072036824401d00500b9180174a0007a1342c100b0005184900383c9080070300480e042c51030a04d031000420002e2400d030748065800f815052040c01800140d40c80780f801079000b9800e03510f95070707512070516542d101ca0b07c91880d080b142101e0f4020500501e07610040714440148142c1e20304008580024002400c150ba50850607003080803003100303500d0500b040809024890410310b041c45005000a41a8040144500403001404d034001403555014000c036155603204940054650625000007070080025026 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1396500 1250 1395250 1395263
    0xf07030e0901060305010303020d09080a02010809031c020c010e07060507030302090315070c02030c040501060203070303020304140a080c0601050a0506040905040c0302150903010501080703050a080a020109051002030601020c0a03170a0507020904050a 109
    0x40d9a40300c940315440182c141c81c10000101400dc10540c0111952280108070311a0b9020900001c19550140b651005c440910743c0800b40e16010840740550071a6017040c1c08200d186d10a0070204442500701c8295026250103044c01030300c5100c01004641440d100e2140c24502d003000c42d041005440d0844d001e0040700d8002d800b21a03951047d0820300c801c54034203000340402b42c0c0c001c1c843d08000a206c2d800855005200343d00c02c1c1c40d0b401c036200c0752504d48440150700301c44e1103201041a54551400b0048a401070400b00c801c0f281d544c0c9014080703861849180120803a142d1a24001404d1101c01c005a0340115400b4000740000d0a4182a01707005402600305144294203000c00020350b480b0010301a03060b40e400401a061030602039450210b00c0d0300c603401440a5540307900c40107000c19021300036070900050070b060250396443c200000908003c07451102c0d51141144041c02c0c03001c0f03080e400c8800f0100e2000c92202d69561071005003078680780504000250320154450800c42008008100207500912444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1397750 1250 1396500 1396513
    0x6020903190b09070501120c0c0c030b010503060a0506060304030f020102270a050904080a03020309070f06050301030b060105030709030201080603010b0402040807050f030d050901030b010e1002010e0607030204030302030f07030e090106030501030302 109
    0x180d10a460b42d25902c12240018078010b80310490200d623604c00320001290f41003800d0301d10669542c020f4a00400d0f40305540f00168100100074504080c072003076520101c01c0c41c0401291034807a000666600020703002030100300c4036051440c4028006d5040b03e41d4440100030b058829480c1403070407103500c8641a2600d001d0365440c6070018840c02d185a600c0d004a038005c240700d0a040e00b03a50300320300a400041032180b9a2003210400603401a018907031502810f0541c0d1113039981c0d81036090070382c91004050304060400204204200990358401680d005990b82443c021003980c44e010006800b501fa44412154807a10000300010032080004404089070b00940c1c030000a0f82403001019203840c5100d001d240450003c00500030340798460392100d110500141400b89010200001141d900c480700703075031140581e549200c51440080c080008607406102440d0a610341401c1d5900251280522808004803610104400f8201405401c0301404480050103d000540e900c200060240c030082c1b005038050701911 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1399000 1250 1397750 1397761
    0x7050303090102031c140408031e010302030d030507031104120204060902040501080a020a020a0b0c0304030311090109030809030106030204020a05030106120506060304030804020d0203030307030605030c030106030c0e0406020903190b 102
    0x1100703596403407a050300030318107003070a505044004000075841400c080d640d5074240c100502da0071a07184d0040b4016503c1c180c5a140884500c104c03204215201003030100c00000400040e900000c200c444c07410b1a01d03021032940c80700704c030550107003a4000c007070940424041400310304244000350f017503107a40c0200d45c18090300c0c0e03442e02600c01300c1c4290b0080500117050140010311142480c1c0040212071101c0c812900b900c00b4948850355075110554044682c20030000038407041c507a0500562441c20300e46440c42e454185040000b8101d00da4502c0001d01407100410000101d540030740c011744c0115000ba2003955201180b000050180e0300034050140801c501e4240040f070a041482035a20034040070b050145580c4940c0c405842c80d40000340100d80c04000403076101d0058170280090343c014503240d100031441a040200705810500e1501c07402d4081d81c58030b541000452010a0030004403403409860300d820b5291030400401a10a00c44134076018031034074580c050324000840b418280e042c001c64000c2c04540741c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1400250 1250 1399000 1399003
    0x1090905011a0c070801050c07060f0605030309120a0c030f0b0702030901020a02060d090606090204080c03060603070302010c0201020304080304030803010e0106050702030604030302031009090501050f09060103030219020406170c0102070503 105
    0xa0060155108007041e040b04040181d000918112a00070221030800d9690f05005080d60310464012100840215088003001000e002f2050910542c402c03e2000c2070610020030390384c3c010a0800c8c3e11821221380c20300174007101803104c2c04880381c200c03c048000035102d0030a59903829004c0000c40f02a0003d800041e002e034408000d80e009080140e02034440c13845580c08000050f0401000060140d54070050240058504e2144400030b00034404c015031114507005200e824000010000c41c02508600c08111080e80c0c0030840e01e0560342c3c242007504d460190741c00102c2c514000c6030004d007254400003070080203201e03140f0080c0d412510010b42814a40e030b00d030791080303680c0d00648200940641c400b10100380046d000303030040c5502103410304ca840695a82c0350945425103004030010348040c0d65031800d00c88544011582164424072110041189500d10390340203507600140320f0102c20981410001404554440c2c121000800201c0104a01c0c0c030b4110017910744641c03000800d5800340c8114100050b00b400d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1401500 1250 1400250 1400261
    0x60f090c030a09030e03010c030b0f010f0c0807080702060a080604061208070b070509150301080c04020301030515060102011803080f060109080d0e060f07080a09050d020d03030c0207080d0c02010909 87
    0x403000915801d503150b00d03a6034000b070702041c5401c5080c07201081120b030b2107031424072078240c182c400c983e030100300c000307610040c0700d40c140245407943d0410413018a00700c96542c05c003403510300705070b4440c217200d0f80c450b114207202c0428006c2c0c83e0f000354001800115510401c0d44082c119014200c100c3e42044003d90302c4044074040304094000400d441020312648010030b0041807803030b921940d182000c61401380580c0c0051010790006005c181c1500f0040014400444200302c0880c0c0d50105a604500e154150f40700c01d951200840c1c0c00501e40c0041030f0010701264400e4101c1e02402e20400c45810b0300c0d070100d150140c1182000c54021400c4141d62000890a43c40741411004480c407190250034280b10f40c240880d4407995605481303070408010003580070448000402011150b0250a82507150a6601d000816148580c3e02c01c07441400d0710714003540540e85003e600382c2416418140018104038140050b400e064190340180b12a002d051000c09a0b030360400f8182c54142d200b640c0e440c0e07505850380e0a4404454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1402750 1250 1401500 1401511
    0x5010e0412080601020a230709020a020705090408090a09020901030b0102011a0409030509090f1006020309010212030a0f0608070501030b030328110102030108010c030b010804050a021306030503030f060f09 90
    0x620104018015004101060b00b1083c1813064400058460325a00c1c840308085420121083c00c603108662061400d0001c403000e00819030341545810740d452002503894580f801024459440c02e8085410013044008455400304040d018102d00c13a610025403000350051840380d40884d00f03102c0100082d43c4103100c0d03246100340291a8001d01d80191b801d10000300400701084081c0a0108600006580c40307a0f40700d442200106034240087c542846601d940d00c0c81d13540040103543c024000032450b40e0f00810a0b100507164417084a480e580e0750840304010b000c04a40752940540f030104089104a400715681068030803e8805021425445080c5540c901ca88040d24800e42042005142c110442114505096601b85014401c0c000812011030032a802a402814160f654164040142d60103000f400d41103030003403c241c1f140340350544485403940049131000340b0030b00c07803c41800c4580035940c0c4001c01942c0c0140c120394807464098490030f1000800c0c0c55640c8500311118030039805240040031280b00700e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1404000 1250 1402750 1402763
    0x10c12050127050702010603050109050304050a08030403030801151b05010c020105070504030c05060c0114010e01030507060302040305030307030c02070b0d02030105190b0406050c10050712061a0703120905010606090905010e04 99
    0x140d0b50748403403030042102a113410210f549800c3c000011a07024040c0c0042e8a0160740030316a10341c41c0004012102206911640c0290414801000420303004006581100d2190000520540034141d086942c40550740401aa0744080140c020600c40b056008a10041e4070360001c0000e511040400d03103c40c041ea104c01003003039500315414084c50900d03202504404c4050b5001140b440e0030b2500d050410380d0243c104480000700000100b0604c201004900010440d0381002c51401d821611220384038031000344802e060645800c100484548204502c4006000440001c0c0d01e4051039900840654000e1149c14850224a1080d60007000719910307400864034140d50140c9003502d088003d90f0b041d04000300e05441d6000d000c070100304d00746142c080c4510401f0320346d4842010225400c001c10461702150442c00542c1054807170380488030301c5581140c1003d9054100024120620318a141c0078003101c1000800c04d5003811800108a90840d08e40d03415079000c0c92013800580e8071601911661801220040c061 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1405250 1250 1404000 1404059
    0x7050a0b0901030f020d0504050303040309050105180f0109050306010b090406080106050d0b07030e0703030806130902030d110102040b04060c0309060e0105040b030a02161101020d0e090a05090f010c120501 90
    0x81d9030180c0d101d0110b0010070b290141c14a44c4000c03950044503001c40302521940c0000040004165009040300b000d40ba09007442810090301030f443c103c4c5110042d06050080c1044941800144e0280d00080010300000b402c07550b556854441000341a040b509403580a107090171800719150307906000b03410a83c0c0f00034004030070080c801d0b203486c42201d1020300604107060303035424009103400381400003002440c002d8070351300000c2c1807213000e015089071000a215005440c080310400180d0700415010799000083c03030310328140c00701c0e11042c500a109540c401807074403500040000310b4075003118080200c1030283d102c400e1180d580d120169140d01241c504c96001520800003403280c2081c117005542c01c5600d0b00070043c02d0844403904c0030740ca00c410344026500034a03000b0300030255603410001400e01141618040c0030394241c0c40c02060035400d001d00f568081c40d464100040e0415030800c90b4048443c0790200a0040c00c41c40707003024110343e521212000300c2504100c0080b0341c81a904008040001c0c400781d001a9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1406500 1250 1405250 1405267
    0x30203060c090a03050106060e010f03140f071205041406011d060402030a06030b07091406041413090506070905040f06050306060d030311070b0f01080109080d0f09080a020105040507050a0b 83
    0x815500c40040b85034461480c00022000c5a002d105040107409580c1f91052041d40100000d025403d45601000415091689200e25885442d10168010b513100000c0c800c581c803030b01000c0e036400700c941000c850990b203040300b007109100310240068800c004440644c0c080385d1701c55050920b08100f007850301c44040000d4020031740d0717814503900441e07101454685c0024611380340c1d95454006241522500009604001c00340104080e02c07110b0030080108842c0d0903d0145003841c070030001a82c01c800760744110010a0001d0030340c0c1f41908041c001035402002d88500c0d281c084000f41555005016403400b40d450b080035240580700510403c810384c1e0b0010004c188035aa60401c01c007045e0101c3e00d0480801d910345298001d0054020301900303030f03207100b8036075009245000034100d81c0244059005980b280e0404c1d480e5004200c1e08030031030f90021940c000104207403d042000320040c1048103c000c12070340700003070703c1e2504a90662000380075601c00c0c829070350315a0390b130381c100842c45040b409407102ca001c0800603000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1407750 1250 1406500 1406521
    0x50601020609150c0913020307090503010204060905010302070f02040207030914060301030b0c0702010c06050702010209030f03030f040f061404030302070201030e0c030304060f0909020406050a0207080120030603030d0908040801110403020306 106
    0x1c0c3c4c01550218100c1c038165500c00802d9546004144c0c80303060307a401009201145070081c03450005410b069001318100740c40d19500600d85000d43c460b8a0600da40090000107001a0302111044650044c0041d036482d50140307002450f44681d4452000344e40d540d03495400d12031074410210b03030403250400001159602c4885900302e0b194070024003203050141103418800014800d00460b4460781c05600016100c0d014607090505010b1202a43c8485810401c10490a9022405180d401c40d400c004101e800b4a664070b040b0b0000e00c1c0344500c0100c030b0f0144204120425605800030051540b0030ba80903c000c420031182c0323942c4c8000803456507034540c100b44000d1190074825003814030f0401540c035055045942c0c80c1010304c126403040e004080015800102003501c903404004500041664038020070540d000040d2101440e4030b0704100418000002010800556040040d903150602c80f0408205510280c42c1c418400d6025129030780540d4200000c040d007410141c0240d0b811603030042c01408550f0384412050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1409000 1250 1407750 1407793
    0x40305090301020c012405030102040807060e0109030b100302010e0301050906010306020a020313030c0314120301060c030905130605130b01080a020d0e060c04061202030601050d111605030409050601020609 90
    0x3582542d42400f4103090341100b40103407180d03143c482c8480d00c0c14820600d51180d4174410343d0042400b903070040104010403034000031618100c510614140f02c850380c0200048440d500c4c00c0d403001d07210034000710600151041d17600b200310441f4402d13280e18000b029070a0516090f5134040702c4800054000c000100040f45035600144400ca40c00c1c0f040e203180071800d258401840f2010f810640d07003104c0300c0701d0070b008100c481d0055200312214a0f004000000102c000325405100c1401080100704411204404141c0640040409450028650340c204d0703202010010003801d031841040e210b1045600f1028400c9494400c2c1c8185840c10307074540206070b448020004c040e60050003071036601950b03030708040c15445080c440c0c43d0041004004082c0d4031803070007000030070740c0c00c0300c03480c0380c10306881042030105030307a00074044421545100c0408102800408280046801034650b0f000020040801c17070000c0107000300c001c03c1601c5416008000c00e460306401207a5402003118600800da215105c03000e60111104001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1410250 1250 1409000 1409017
    0x40210050408030703050405030c0f030d0c0203030708040b0a14090a050904050f03030103050a06050702120904091703010f03030201060806010b041a0403060c080601080612060703020901021006150810030506040305 94
    0x41454030b50b490310300514591140c201070740095000305080c409032034140045685000112801d40d00009e000300043d40340c040102c0c4080038045018600c80031924180306450040da041584291956a281d465114503402104c034080003410b000441d40103444050306503101c2201c06072090b0340300c1d42844140015000040d00c00e454038450500d400c142a1800c000543c0a075118001502810160f441d0240039a64044c240f00b06640101c0e800d002e202c2d82031025103c28030001c50300403e40901d181460300080c0521401c0c5440300b03c00000100b1064070300c3c1401012070380b00768020419140e40f9941c1c6a01d620080c00303040d03c10318003040304100ca03054100b101c61100141c0404103203402c0e6a56506012101c0d0341e1803500205218104020785981c1084510b030303100c10280c0341440030a80c50890070341c843c84018242828035a01080040e4540d1080040b00000400301501700000d60f00d96018030728012a115410000500c05c10015411740314202c1340b030f811a603002e0024925a19a0340d01540c0c56000b1015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1411500 1250 1410250 1410257
    0xa0507090b0a0905130201080c091309030507060c020c0a080105060907050913060303080411010201050702060406020a0e0d050601030b070507050309010507020d0f0c0608090d0905100203040e0406020a0206150603040210 96
    0x301280f0400c0512607603009200b810480d01d00b1150074400035204030401001d12075240000d0020036160b440300e5520f0402d4031544580011a81628907003500d1601803820080c0c40386140c2020ba10310550000740341070051108452403e042c581d140050390917110200d9074280c004602d40003040c3c0e114001c1b80030740200da10050180c2c2d40d11402000d503504840296006800141c03c800510040c03202903007a283d0524400c0c8003d01444c07030b00782001395031a8409000140300741c0e40010441000c4d44520f860051101d80101110101c40b031504000361b588800303000a9840c2c40b42c08022544180c010021030b003078154828095400c6c150514019030700707500b08800a07030f0010502d0381d440001980100722424100c0c85000b41684045c10148000c220076001070004c14a41d200300d50200e062a000300100044940031103e1a80210304000102d040d03005a511944c2e106200505001c100102e030f401a007201e244640c00c9491603a21a01d4501c0b05080959419400100030401f0502504258040c1c006902c01c504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1412750 1250 1411500 1411519
    0x20a0803060105040314010902040b0402030402060703110c060f0705010507090503070306090303020409020a050711040203010b04030609061107030f0201050c0301060504090c030e0304080d08011202030304051003090c060906080601020a0507090b 107
    0x88421000000401c8001b40d03d9654005c2c1c503045143c9407180c580005410b480450940c681035020604030710501c240074043c0400e100f010031442c18104815024202c0144c209529010b1041002425400c125011a410f500740710008010a11882c90802120001401801d00b607185444040040a802c04d06404054003004007284c503242900081c070001d001503890036510005400c2c00e6210300c640301c1d2800c2c8900c0c01040100004801101910103032500100000341213101490160005c0c1610100032400d0071010912405060b00803c281d034005041ea0000e1013143e0315a07070002c285100900900c008290184030611941e03d1f01d502201d401e00c000d007000680701540f651640c2c50b6401940c01140340da4881030036220a154880812801030a8503c40c4080200f4580c0c00030391203000d18040c01d402070380d00b4005000300794400d4220091850300103c0c48281c40ba19028000d040300300703e0203031001041c010000b240c800c1d4400917100106a800c0f80150942e03500301480340c0064810746607030072742c0098a036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1414000 1250 1412750 1412753
    0x1a030d08040312020d05100509150609040b011106040b011d01050102060703090f0b0a05070201060b03010f0302060715050a140906090a0605100302040e010c020705011106010605030a060b070b04050f01020406020a08030601050403 100
    0x107124590040187d207030704003845450071040264021004000180d21a20020004419210701c003e8400000003210040703110260080100d03185001c60001000c7c51144c1002e200501c01000c1c2024185e44460034019500d007a0b00c95803800310f610a128403030040e403040e0009a0400c2c840ea00c140c1000344100c006502058461b02ca4081c005000c6c1d805015482c3e40c2e10900a0641e02449590000c140d4203c4c81410742d0302d426984c402c800403910002c0d004210024444040100d51880ca20842c11000002c20260911b28045801804441c142c4440001c0c5140030464400c0000b40b52840391507000b00811b05c1030b185554100c060600a030180701500d0340c0500c0440140d60300d010388003142e0320000000881c00225003009181000c141e0140e0f050100400c1200d00708440450752505481c183c2c10002e0f6283c6440e1083c0000b0641507018052a401c04a1a001009003000a00f40918001c2e0200c48518002260300ca00703e21030b0b40b00d6040540d11860030000000d070f0143c09160300800c141800c50920766203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1415250 1250 1414000 1414027
    0x70f050d030507080612031605010204050a080c03070b070b042006121e040c0303080910020403080a020c12030d09050f07060206041505010605030c030a0f020d1a030d0804031202 78
    0x1401440042078a0700c0030080440c1e40400c406622002c2101c0010817a0061034500387c0f640704202c900d404c8404100c10031803d02c41e00750100da00806002c4c0c0059055581c4d00000b40d00da205105a8600c2401060400580c50144406a0320304640144491005461350394444d0b0b08032152682c12201d1446100d81d4041036039480020b03009111414448414a01c0c010b080d082e4401b411036001040c400c6280240b0002c50740006815050b00d9050030714024a8481c0003c00b850700e14607107000c01455000250110070820300c40090881c003599a001c40314a0400d1034200614186101902801a401480305900c80d4000e074211001041c014010740756460a20314101e8144440358002d803015901038401d22040000c0440040c650440c1280e08004075414408010030920001c1c00ba040b100c030010006c100a1283c030750251546401c1d40030110b60b518400c07440a030142c00081407c82c2c1e9016107901d14000c074100800c000b40c18260994a4090b1942c5030795041c0c413000360383e10400040340d40c24456200e07007401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1416500 1250 1415250 1415263
    0x60807050d14070504030606082e060f03081b06010501050a0309030c02060c01020304030206010902090603070c02180f07020106080a02030a06110d0f020405090a0b011e050c0304090b040c050a08010902070f05 91
    0x10f007076a40030364035030450070f0400640d6510350200e03c03140d00440803026003c41d010513280d44005900351040303000004018070400703444643c21003803071010040000000c1100050007044201007000c004102080084491034540303d0912410340426000c001c0700580c18829482041a0f602c42d043c82600c0340348540109505403c07948500007280c2d4000140300515404112039801000e184009519088566001c100030b80405001402880704032802c041c115500c1030912407184c0039208040c0c400307142010101d90307201c0d026100c00c2e02551819201040141000c04c1c0142e030f0903005801050ba001e0381e9900c1100a2014100b860b52411044c0880d080c900e0712801090417642c1a46c0000d1384a5040c803042080e5a04080e001c040824030b40092244103036001444503811501c040c4140241401c0c02406030781c0362240c0c000c99039403400001030224a240e8154003540c0100000d0310108481c0c03401c2c400a0701d891182401c03100c01304d0f0916004109010071500100f20340d41c0b1440700300000c00d0302a52124a0140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1417750 1250 1416500 1416511
    0x109020a0e03070f0504110705060901090c050109030203070b09030c0307060306030203010b0405040f02010e030c120f0d050309070b0a0c02040203091506040b0a03020f0604050d05060a0f0501060807050d14 90
    0x1500010310039005603100340c201080e1401107025051451601580700146500e80c440c02d8011600c07080d10740e00b450785040503200550341100907610546031100e941d900030308100c202240c51441054020807254456240481a40c0d4003030014000d4a003090802c0701d26030403c88400f0b60503c1600b43c2c10225072000e10801c0010301d620307140800d086055104142c00d44612082070b0b40101c2c5042c00308004107004440e214400390b02070a11400541c140400310f4204a200b07240c1c140c0140012045d00200b0070001203201c900c0c54048140d8004a5000d02c0403074252005642900751a8480301007440950b213920000c00e6844440d01301180303030300312a50100b0166002200c2c43c0c1c085d40c100302807d860002e40b403170040b0780c0640e0071034042010075402000244c0041d042e01000c0c0c080c00741c9511851042c0c90300d00880d40901002000c41143e215986041d980e56801100c072901c0e058201050300d01c070714920b80950b034182c608a803152055035440180880f410340124042140c80c84d1140001c2a00c4802c070a106402403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1419000 1250 1417750 1417769
    0x70b04030b090c030111120402010909110706060918020121050f0105010305130b1302010c0c12051b010f05030402030a06110301060e0105030408070204020c0708010606120c0305040510050c0f0301 86
    0xd00d0014401410180031510700f83c001d0341024451020405644102d0f100841d0000c04001140c5460004070303203c0103542c0180102618005070007400d8141c890140504034443c1c5800d2009a841e03116180c1a2280749004c0b400d030f00c06488035080103601940a0070415010a1960322110044588410603144183c8880d4084400c4e1001444203507414001c0c26031100030141d684440322040e07507511321301e03450040c03030b40c090f00403000e580c2030031603200310b02c0018202d8129a020070000d880364480c1088402200c0b0489032031140c01c043c0038465410034a0418590310585801122801151003a202940001e204030f901d40a9010000d00150061182116005181c41c01a44943c1441c0340a40341a9100602d241801014002c020000700c400b0304445102d81e0503180540c0301d0001c034840301d25081c0300d500070550550070308002040c1300d43d001401e84a03121902e01d0030300103c41010350a82c1100c00542e405420b83c0c0180500008240781ea4001d1504001c40c00e00ca2803401e103903c1c41c2015160802c0c4c20500c0ca4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1420250 1250 1419000 1419023
    0x3080103170310090e01060503010905030901030b120303070e040e03130302010905040e07050d0602040302030f010c030b0d030c030807020309150c070602010605060a03090c0306020403110a0801020a14070203070b0403 95
    0x103212501e0400030080da05a61042d140d800c0100384400c0c4440544a0080000c3d210b0060f80c54004080d00b0200050501400a01c20303122685000742c0c494000400440c0003c1c40c0502c1440c46141816000450520f10340181d8a141c450b803504449040c42e0140140c2c0041d00c8003501c00b9121070420062050071007110200c3d1982d03056100046c850074059025a00c07940c140513403116072034004580041143c030300311809116200185031410190050340d0001c0c1d03050003084040127071403106400075400054a81e030200801215041040501818020003500144c0d0079040100002d0081441d075800c03000d5401200e06001e60180003424058015114600c503200214440701c415400b00403840152015000a0020a05010208502c0c1c000d50039032400700b41c1c4600204007807000410b0040091a00700800755603da4480c10200041c201540500b40a115008000140040c062017580c240c0002559944070070190440112943d411440d003c1ea4980164080022100940002003004510516500a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1421500 1250 1420250 1420253
    0x80406030504110a0308030a0b03010506060a080613060b0408010c09030803040b1003060e0703051501060806090709080105010905040210030506010509060c0c04020a0f080901050403020a030815040504051b0d020d02061b01050403080103 103
    0x54800440c9ca040c0203a0420007809116078400307041d80d9100515140003030265840c00c000820703240c500c2040890b241d290520202d1906214130082013a03410040c024000c030881810211400300d554400981710070402c1c00070800241100110355000401e0b041c007060410707102c2c0c0b506404c640450790004130039841f4080410400c002445084551908582d0080f0650314003e806404084000d1031140320710380b4400004c1d0310074004c1280a01401030700008010700d43e11007100000400c0d01307440992090940a90380541c0300d1180c012907200b06010b0750f036182403c0c0740c0001d200039900700280d440c4060049005242103900c4520150036140081c2d6200d81f400389158202074a089000744c000003180c0d0500041001080e0000344a440844d4945031800c010307038510300c00e900c4d400103140c2c030103038814100414041070250000303450503e403158101d0011408039034020003403000c94524000303400030180c4002502514041020708903480351007070f800000b11000c0d07114900b1101c1c22641100420b46c140700600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1422750 1250 1421500 1421521
    0x8040b0a0c060c11070b0306090703050705120103050a0b09010e0c040b01020705152503050a080601030b03010e0f07060203040e13050102090604030f0b01150516060b0307060302030a0b060403080406030504110a030803 95
    0x1001440041b100c03500c1c41c1041c002040e16518014130074828551113502040f4514440c4080b10440034483c1300244695071a0320b001915602d4001c0103448031060000030400800040c464803480840c861300800321500b4520901000d0300078840e0071415805410b10019586c1c81d0404070607203035101c01c1a040d40d0b4022225902480002c50840001d074902404401000242c1000458140000900b003040407aaa00401240a070810f00345c40741c0c265080031220448400009254444100d6000980d51000d443c0c86d4101d0b640d00540c0f040d0035501c030000010400038612042800d046601031b00001d480c02c050a004551346074016803045848280e0400003006208810a0b00d9014000b43c094807403103000c103007900408a001c2c410144100c000002549402c0017656440922409000380c1034031070007a0345201c00740003500100d9640034201d08001481ca000c0c5804002c44060380e030311031180b508007414400c040700100303401002280e80c2003030404101200d603182c4a88000440c850761030301e80d5078540443e421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1424000 1250 1422750 1422763
    0x1209010c03060501050403060506040216050c0f040b0102120304060e0d050a0207050d0312020c010603050105010b070204050105040b03030301060507030207080303130302010b0f01080a0903030b1206060102060c0708040b0a0c060c11 101
    0x34101441d086092102c0d03a404012581102e07088800400c0303588800e00060300a1040d00d1000031100310740506102044000b040c0961009012074105800e4a809018071003510458000c3e6030058124a0600c11803000000140d80c0060140c400090302030b03402c1c1811403400400403c03040c04a44003248008803598100700c444003810b0240c07540c072030081ca0b40c3c1c2c01a2130014582400c07030301180c01040490000209510220003140c11500a100d05c1d60b59500004140e4030234a41a40120304040005c03905040c10f0041c3e045050000d40110b10310303803070a901140e090300301a030118110b006503840068190001c00107140500390314101e02c0c80340d42581c5400307421614000a041d000c1d0342000c1600e5200d1b80c101e83c1c1160f0058001c0004581c0800780d140c03ca0080c80f0100256130300c0403142850030030402d00010161300c01c250a03000c41b00c0585400d6560b0b0602e004812000b003100380104024401040e0080141c241840e1504020b001580c040c2d89110175292031040e21300000e540000004001c00081160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1425250 1250 1424000 1424021
    0x1030b09010c050906090f090408030601030b0a0b090d020604030b040b06090106030b030705040209030307080301090b1c0b040204020904060305030703030e01050705040f0504020309031b01020a0314070e0d0215120901 95
    0x1c00c0000501c0b0310140c2a40561300c109485500c001c00c00041e1510750032440c1c03410203001000c0d92014039051034a01440e800554207940040d01d0444c0e0140345041445507e405c0d00d15049509007401c225004100c030f90314207440700b280c00002c24040000080d04424100340038603c2001da250742c91400d4414094260340c142d009504050502c4e69401040d04c01184080982e103059601580e5040781001003480c5202d0080014001500000001940300c030b16030059200e00c0044804c1c9801384003000c1005542a00c554001d06a2005000840d00510b015401030941b40009000401c0003552a1280760440d0450030b015800b10383c680056054009080c81210b070b00c2034031400c0182c2040d0418070140d0303034090705020300b038001c41d130001c00b20341681810001d85000130080b10f03502d8003090a4003a0345020f500008984004281820400f404001e51685100d22401895950960400803038081180b0b0f0b00e10071b13405036004203c440c80c1184148810008000441072044000403904020300681d00310740c6502ca4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1426500 1250 1425250 1425253
    0x5010b04060509070e011107060309060e010501060f0503040501060e0103030201050601020601060807020307140f03070c060201060503010207150507030b060c0d140304020a0b0309120406030504030305060906061c020c030d0501030b09 102
    0x400d0000366220003003950844e01c14030789000012001e00c0180c2e104041e02d0305903500d900ca070040020b14684c0c5034000c2c20b8000c2c86444c060148014001c0708a080e14009e01078040030807400800c15030200e105a0285d90300500440000c1150780d603c08080c0030450003030b0401e40040c1d448900304021540c0400a80c0d0050015240811881c50810002922402013482c000c000c0c0503001c4003000c1b6104c04125920040c0d021100780c0390b07103100a183c5922840d4540c401c04015500380703880002d007031034184240c401480d0000e003541c8981000c4032403c0000c10009203903130241170303443d03100d50180e40301c1c14064103d08200704000c00c3e039800c000e24042c0091384d007036011413040a420402c000060321080c0019044426090601c1d441c0e0301c0e00c0b44624180b130140c03940348411f03180128000588070341c1600064000d50084d01e0400090312280d00380300510500325003c681205080111804034949a064484001c0403640c0060919824680d81421a13020812060a03541c4450040c001e204090480b55040400b680 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1427750 1250 1426500 1426511
    0x6120a0201050f0a0309050d050910020105060904020409020d0b0a02030105030c060306030d03051803030f18010c0c02150409020d02030609010503030703080103030f1202030a0e010509030702030a020d0804030f08040305010b04 99
    0x103000030141e204100c85643d9503803010038040c152502030780003610069031100c15070301114002c00b4010b0407a04911011481040000e4020003001d006205003402020050a006110794031794091102411113080e049030400c440d070902c0c00220751203000860003183c058002581d039500d800c04142c41d2078601e212045c81036004005216480d0340018043e8081c403260706011815076201d00d11203c019580e444083d00f280000420810505498074113244600550548400c5080c602421642201c0c00801018080b0750507002c004050700d002c1c1e0807d11114008071285103007640720b611007020303a0003481146501c03a40100c1030101300e00c2e0900e0b4650160006030000c6041540d1514020315600041c070018040c480311040400c602440b413070b000080521440c006560340e06100c3c1d80d2200070084105501159440e080100d201200e02100b00c0e185540c000b0010700c2c440790941c0801501254180c011a0810010000040000c4410704c0b42d864142c0502c66081d00c4030b1440c1841e40c25a1094034986102e2803808 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1429000 1250 1427750 1427753
    0x201110f03060d020604030c03030c0501060e09030901081503070602010b0909060403080f06040f091506050a0f270c0203070c05010905060304030507020f130608070f03030f0503070203040e040b06120a 88
    0x14401e9960065084901804003022030001c508988559000541940f510450100c2819007112015060922400c002c20000307a86004560000105130b80340c008030b0b001000700540d25803003510400e40146800e000411000040c00000e803a140840d8032920150351200454900d901c1c107440340303c4c0e010240340058061490280d07801840908001c200c80d02c1c5404074404220240c889512010340e01c40303100d400308880e042d1410f1114450401c142102e2501c0e0a1440124850409140d494100da9000f8608580c4905040540c00800300f01114401e8556101c04c0441c0c81039414000c503561090190081d44c0d45000740d06140031400015000641030200c005c0e4100000d48070703042142e5016405d40307001c80e11400746e0300c00035100386c0c5407000c01c3da4002220710714019070014581c480412210a4811a07200310b07525050109200d500348400350100d1490a4900700307050046004541c040c0c442d105407131130301d030322000618175000c81941c050314003590b270104004107410074003051004200315000410b004e0f6800e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1430250 1250 1429000 1429027
    0x1020301120201120207020612060f0d0b071d0904080703090902030105030304060305090307020904060c0e040509070504050405030705060103080d06090e07030201050901090f080a02090601080f070c0f080a020607020111 96
    0x55803000f410811207560b42021850103505644405500514440c5e842c02c11f01202e00c1003020648125100740240a03540300e4500d00100d400540607800004250560b41300c850903101200405503501503400041c0001c000d5a844181d854499841007103001c1d1500b6031410002d140c10256040002e42910400040c44641d80000039102161031a190100e042da46081015065004401000390481540b200b8041001001c0d0011417003080d041e510300011040440801042da20251045900c0750045c080500c814105034001c40d501c01d001e031046034036105969031550300d0031100344e00a42c2c00c002c001c60f05440c0148940202070041800c80018403041000da150aa21903880d444001c1c14002d0002d85000c40740d0007403160200034141e509180c2c0190b076440807003586620410000320b124151540c00160300358002c0c0001ca0080885182880c050703580c46c030098a0480c00d0940030f8841400c0d880a0100041d6a200208011882540982038a0a1140700030342510000c04505a1242040c880030140468 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1431500 1250 1430250 1430279
    0x9080604060c03060509040c0501020607050703050f0703020f03030405010906060506040303050d0c0908030703080105030709090803010902031306020403110a060201020a02030906030c070503160b090c090a0b03100c120e01020301 100
    0x40008000540000c0b55100340c000340107036400385401c40c451034200424801d20843d08000c4440070780030364003940d4540404481d1486a4400100814410701070074040c030f80c0050252410a1207801201d1955010126191650300304480444150303460740e10450400080703010740b0700103180a56546023400e0440e44e02070868040d603070342410000e80e20352144900d2442540114000c240b088162075031010b913801c000b403a80347d090007054001d110710300c000030b20205a8499a08081e801c1102c640c1140d0038858580c010b5803029128096050400c055640400d40a20043c00210301c240c0c4499625040c081c20300045000c83d0f4000015a441030100d02031b09074004c0b0846200b09800c0f0350450740c0755103142da90039590044480242c01c5110125000c900405182c010454190181d21002443d640b8a4071a50350b40c9603075103481e03411040d800d0101c3c07804d00d0283c01ca80031a0000509a0703240070304141d000400c58920103414070000d85103030452004e4818500c260074520b540d445c0203501c3d640c10304c0e066115500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1432750 1250 1431500 1431503
    0xe030301150806030a020901060906080f01030309050108070309020406090203010602061803031305030c010e0d12020f040509040609150501090c05040f03020105130902030709050a050306070206041b05060c03030a05010609080604 100
    0x49900083e0155402c3c081e19501c0c2e0ba00401586e41c0c2d585404000b001c482c4540a018003080201c00480e400e840c1f2507113028100c950540d500350780b40f42080300440302500080c0030001456110171070000160b56500582001c1c04440c4001600ca40c5003000c000d140c00c501829449415800c2c0bc10002c00007000700071030380c1c0400038019031000340e6941d140031803441c030035007640a019510340080109540408150007250300416a51081c2c1c003000120721004a106203076403040c65840410040009041c0726041680c400d0040100083c0d803c3c407504e500480c0c241084071000c046603600c0050040c9000c611401d44800124074041e800c02d400d00c0140d1420300d00c0c50201905125000c5240031551410115420181580c44e800750b4403418000e4026083d629140a0700c2d02c00e4440d807001003450705001034541d20441150740142030300d8956890351500d8049a02c41d90540c08080200810035450f41c2008115403001d80c00110790307916051818104a40c011f0b08803100300140241c00b0000800c4c00201641c105 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1434000 1250 1432750 1432757
    0x5010b01090605120402040b1203031003061508060103060c050c0102070303060504061202030a060203041106040305070602120c15040302010b0a080a0b060d03020d0e06040302090f060102060a02030705040b0706020c030310090e03030115 103
    0x582c8c194000030400d01d2403120b081d116220000c200002600800011400c4900c555024441c60161580d1440d8544240c0a41020b650020004202145003900181603528542c1007003442e00c4090300150742664408a81980400e488050070021414148124401071041014000002540e40d001030384444c092800600f110380c01101003811302c000f02000800b00301e40284402e0390f9a23964a0072640f245014890500503000324144104003010b8a01140c0420b009907025000030501e0038500d13030700a0400b91040c1c085660310160394200f03842e0200f909000e040600020943c2c04c64900d8084004030009201038064030601d140400003075000030324070318000380178102034103801040d10118040d406540d1000c0e511010721b0003401132945c031403261140105020b1f82566010b90740e426112041c1e01c0103607400c00000b4001c101c100000790084015203080343c0304200142c5003204510340c247c0345070030548070b1700c910542080342041110101c0c810b100854004034051400c561501030303800450340c821461070f01807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1435250 1250 1434000 1434011
    0x603050603030405090906040605010504020304030905040c0e04020318010608010c020d0503070c0501060b0703030c080601080c07030504030b090601150201090206030604050c07050703081803010b0603060607080d060305010b0109060512040204 106
    0x125036042c026200607203000741c444a413914111504070340da03034001c2c0d5082e07581620305000419142464000c07039210301e4050715260407462070b100134030000f0000c6921030400c1000340d0000e107100742c1c1c1d140011402031041e0080d0384980c62200d0b02650848299500a1299a240030800c0580540100304001d01c5d84480c20200e440b80c0d2044000d0b0340034881d00c04002c041e54a45400030500707446510140c04500e000c4e82d010040c6920408090b03881c00b01c20756156012a840f200056600200c0340003c040603403007458120b00f01603903070350388410010040e02c40c030800c1d40208005201608545000101b068071032300c002c0c0300003540e60b0085005440082d0220307019a481b040017032401154101203440043e071110456554035a00d091075012600240f41c0999101900034104da0300d440c0500600c2243d0000030407035899516440200720180d4003414080360607120601c001c00d00441c070b5106850045020b60004600990080700041200045400c84000d020081c0044414644c1c4248410780c416419200002c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1436500 1250 1435250 1435261
    0xd03020a12020c0102030106030c0c0c030b07030b03030301090507020f0706080a05040201090312020109031e08010504180b010e0403021005012303030d0207030504080105010803070209040809011404030f050c1009060305 96
    0x104003200072115030031180000380340144214150f005504a952a40d820407031048408401c8a0401400c240940000d164200c20300106081170b51180d005410f60800041017444c4c080400d00b9074100768810390140c0e50b5142044100c9405205035282440324801610b9658103005c8050402207010f0500d14025a0f5a030009045901034245400556000400c1a8a948080038000d0203001240310490010300c0781c5031211102042d1201c1601084451340f6852001e030b0030b11090000603e104102c454051060500f104003080b10f005540380078182e0818844a46d1030203090203403818401c2400003000d04e140031700400c40319560030b0500b0721248190368100f004a4580000074a18080c81841c9500144002049010150060010000c03500303040000e0046030b80c0c03101207035100c0c0241d61019400c00c07508000500041c0d10340d4001d00d80881c0504100541d8400010590610f030002e400443d140140c2450403828000304000c20030303881c0c01c00c584000c503400c800e140040c61030540344202c2c800d241d1100080340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1437750 1250 1436500 1436507
    0x4080a0c0807020a0308031006030608030d020d110309060703050c03060901050f01030603050607020a03030605030a0203031b1002160201030506030106150c05030405100917010209060906030a09150606020f0f0d03020a 95
    0xb100240c00070700d001c078801e459007040107040e802507914941d8003809400000b000c0c1e010b4040c0104030752021002d1424200281c1020001c0e6000c0e01003540c04950300d03010f0403003035041c51010f140035414080081c841031602c02005402c0364005451150f0f48082801042150350307035082070070306581098407441c00d26054000140c010b8001c0b6040140301c3e0003014204400b903a400601044107a0080d40c0c06d00c01c00f55518141a100c1000004c0650150020804444440c43ca03c10032680521100121b402c5505400074240891300500651190583d500c41d101087d5a41401020707040f02048008104541c40c00740c01000b01c040c1d92103008144803200e0304c003c092000c28030964000f020040d282a426403104000242010190300071100f5050140b0b01404d407814052080c0d801400c405000180340071202c10402c01d032078000400070140c40c1d40f1606000c0011350804150340c80403c0ca180049041ca0906a000e81440000440301c1e03801c1d80102405041c60000251040a03818903081c0103940713915041046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1438856 1106 1437750 1437757
    0x5040809010503070c0b040501020904060b0307020a110d170a0809030a050f090a26060604020708030406020d0603021203040303020c0103020c0c04050c0405120708070801020304080a0c08 82
    0x40352940900021900044107040140d6610005e0b0744844800703804840444190750080b07800c01040c2864042e40c0c0180003c0b000490861030f107400005d40d1140401c0d800b038504c2855504058031510b95030460300c402508806045115040f001c00b070382c4280d20401004000629820003e4900b41c40030003950011240c1c5d50720f50303140c0901c01565604d0307500f01e242d04030b40c400091107000514289064481000e05200034020741c50b442c2c950085420900c0007814580143e0040100c240002c12540131640d00c580e0122005031190103401d02c00005181a0304001e401c61302100c070741c4046c3c6500002030001c892203982121401c2503114011000c0e8083c41410300ea941d407000424504034075060304019403003042e59400f5403d0954505c005506100080440c00b02900b04503001d00810300180800b8000d801c0c1e5030000c4d8903506065541b0202c03071249160210030480444401010441d890007207 = true := by decide +kernel

theorem cover : BRFrame.Cov 1259000 1438856 := by
  have h0 := BRFrame.cov_init 1259000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1259000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1259000 ≤ n) (h2 : n < 1438856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
