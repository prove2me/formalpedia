-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:00:34.531839+00:00
-- url     : https://prove2.me/submissions/80d4c6ab-536d-47b5-a892-871ec0fa4dec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 456294964 ≤ n < 456474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 456296214 1250 456294964 456294997
    0x509010203101e06050306040b09040807020918030a0c081902160617060904020a0b0a080702060609010e0a05070e0406061d06040f0603050c0909010e09060a111b0c06 73
    0x111110038050480010030070104244290f0042894507158024240580000c100c0c0010100c0e81564864014001040000340b028005090a29111446a000201c1240140c000c032000440c1c942c510403d001d4a8049000614901501404c0880f0340707181000b0111541d0302d05000c242034400c4607480fa1986c0c4003136071300140720406803040c0d46480e2100c03030b50000c0700300803004030380b0050540720078049500a0b03410784444001d5200c91001940131000781c1c1150017805d101141d070f00d140c59072005035a8000d0b06241c0a542e4207031501000d1110b0a4000d000f0303603003960f8031400450414200740d030110b6402441442c2c641a502d50007000501038a009038055000900f0059030350020b914186010009500d003150028030302132900d180251200c0b841d2143c001499503400000c1c00c05040c8a040310b617044001843c0c00960340e101c00020044100644201d612440b403107000548915030f0307114280d03441c8117040005040115480300414500e100140d604528010305948044a88803000139001d001680c60201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 456297464 1250 456296214 456296221
    0x4030c0e06040e03041202040b03120307080a06120f0b0603160b04030303180f02060f130906081c0519051c1d03190c020622140105040e06090907090509010203 70
    0x1d0740e00800f070040040e00100003c2161200c00003400301c3e0746506840200f203d11a29000904112a884071070203044000010440d109078001c0d14144034400ba08820451136031540d039091040b50314280014424a2003110040100304082e246540c05903000301120103500c0300d00034007603504495600241410401080a100b01600f600580700382e090364209003003410302e9070303114a811150b918038080e026140005048d03100048103800c44030781205405d800b54400d55590030000017410315110341240d80c010740d1400d24002d04034848000b411084c41c4d5410303091615141d0308181d0495405803090a110f0108002c00c82c0310022140320101456650001498198507080d00300440b130b4440e01503006400400280300e56403401d07022408014100c5c505646241c00030b10101e041c5100f8900c0280c002c0c00b28525282540c8800c1043c60103441c8001c0c0381035a0483c02c1303c0103517035500560040401c500c859000003032042c10410041a40034418800700d0350a10b64a040640841e1000d41d45042c65035000001c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 456298714 1250 456297464 456297469
    0x207060201230426030a0c110d0305040c1e05040506010302090a09180b0906040506100b04060806061c06050a060e030304030618080c0a02010906111005090c12060f0109020c120a030204030c0e06 85
    0x1a0031080d4070034181480000c038400c2415489e43c48000d03404051555a0000c50140079008544101a1090050810b40904600c1024581d003207140700700c40c4030314102000036850394441c0c02600d00d4140050000e0302464103000405000c1c00c14582c0d03092001454003c0180030510000e882801500e0078009400181070900704141400e00007029000c1d035081c940000c00003441810200e80840e0060710700300c151522803a000070f445100d04c0031022061402c0000d842c08415896022400300d94044448080c9a5910082a512640600101c950580050004102041741c5030040d0b03000e050f040d0512240a20681c0d0303426813503000701d0790022069200e407202008550b0041d0000024007014102000f0106200c10f07810350320f0b40c0c940b0403d60036540f20800b1961800c0704020500311070300d00614150510003240741c5655100811078080395904a88000044c0d0390f070b0350744201c034003540e00100a002000004481103c69901075000d030fa040560800c00000800c84801e21500507180c05004141c0c1070612408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 456299964 1250 456298714 456298721
    0x60b0f0d1b14060304110102071505120907120f0503161a0609040c0326030106050a02060c0c030a0c0c030501021801030b040b0108161715010207060201230426030a 72
    0x219107020490020b038202140d6403a41039903801503108024060b803075181c000403410703c07855611103040c109804158520342034100028024101002600320380a40d50002015695582c0388901d0106024180b60351000c10304640c0c44944a42c001e9040740c0c41c013802e0742c08685010001c5802550780d9286000030300381140c8008190354000d0b030100e030382d101241080d889200031020a440010480e48203001164049000900046141c50840c030845840c4c0d0f9513010090042d0307111680380d00041c00b4075000292280684000d64030240d40d42e034001c50502c4003562064403400b40d1050191f03020ba40c00203000000800900082140460740d80f00f07441450025070015058501c5503450b1031040d400d000c038858450741d00c20f040300c0c2d1150320718401c03104c49100c2d000d00740c44402c100000355a00718036050400a01411200101491207001c0c2e00b10780c5500c2c0e807000100d00301d44500d041d2001c3c52070000c9900c004050035031803107078005008807440c014036442c011148803000c4424500241c3c481001c4200301c0001c61520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 456301214 1250 456299964 456299969
    0x306070201050420031906150806010f0b130f120c0506071104020d0f050405331303031b181d010902161a04021504060c060b0f0d1b 58
    0xc1c052401d203035599485031005614440e6100d0044c10f80240b060343d08019500500312580c1d814604011117080c000094600c0500e4800040006000003555040c0001c80d035040307500458010703c0036410725640340c0440d400b1400c41d0410f840503003004104141c4505289000b82180c8851209551080c035110400c000c141e4400c620580c0706215400200d0004089900104822180169180a05292030000344814070b00c11260914180030402000070005140007410002e2414454803a01910821620001c00d541c0000903c10100810b42c002c0740303403500151280c42420b000c01e1061803a6503510b5003105040000000070799401e248000e4500820303582000d4201c030604c46018244640b45810032a0040c403035008030940c009082031145e884500408156980803840d11a00349402c40780c05c40450003130720180e00c41c2c60f038a138000c4981440b0b0011202110710a0321013010080154030707a28024170080241340d0700421940e150310115030ba00c240290784a4460f011155495a221f40c0500c00243c8a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 456302464 1250 456301214 456301217
    0xb040b071506140111100e0f10051611070504091112070f030f08070c0f03050606010e0d0311100c0507031b05030306091513021228020d0e0f0a02030607 67
    0x203101400400c2040100e144503440a0900d80101d82c601741c4480e1400d0200c6400380310342483e141c00d401040c2004101c0d210b1405a180c01c48191902020482d4101d40341500e0071055145c46825414000b4043c022085190a040d41a500d007a541d0310003040613548080030482d0b201c51080990704692511088011807003200c1001800c1c41414000d8410031f5600d540405042d40400406800421408404490240f41e0010010798420b5a40c2c002d036000080900003143e00d802924005030680d40314020a2004040061014984c07411644080d15501c071041c100300100e000c0d80100c1c20703c0ca14280100c0700765110907a92a030769801c09040042c40010f482c505440c2c50b07000034001401045000040d6070300100121901c000d5910f46076028280c04180c00c14140e000000190129a441d400b68003801601c0b0b059407030582e540d40c65100c3e01d009003285071030549480c2d0480c031385c095250320309034041d0803400712038131001840000341100103107001d455960015a42d44650354000c21401c0c1841b0241c0c00034240e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 456303714 1250 456302464 456302471
    0x31b25120f09090b0301060906060207051512060603070c1a0105010210090b0a02210903040e0f040201090303050a0516050303010801110a0804110103060306020a08040204063003090b040b0715 84
    0x1400c0c001000d400b95031180c40403081d260712013038245540070350000000b0184c240d4204003d903900e40c07000c3d403142c250b03100305846041d01c0078122007000382040854284030a4520680c4032584c45400f080016007000d0440c0d000c1144420702c4000140307010610044118511250f0740440d071415000a00c0d065289194905403410030490000007062140358030307042582140b01581301c0c0d05d124030492030118440c40410702c9100311024001c19000100040050320000089201740f503845d001041962441a10000c0c00201c1584003080800c1c45600a02030940107850960301e0000b40c2600495140e48068081d11150070010040011070824400d00712180c1d082c411003401c042100c0070213841c2c040000d001401e00220780751444102d0b886030344042e01031341d4060021503c680b02c00c10020b084000444049010f240342c00c4002c9027004480c1145000c15800d00460000c0c14001002c04081340c160690072014000103290200780a842000648040c1601d8040316803906940c0c01d292a59070350091441204034038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 456304964 1250 456303714 456303737
    0xd1505090a020a231204110a050f030a03200304091a0102060105100e0301110a03020a0f020624030309030703080a1707050f070c18021c0203010b031b2512 68
    0x1c1058480c0710600780600e0340c00400803a404d40710428801c14030086034020b141020001080b40c1c00802941130329040d40e114140c141c40d40140049038203201049941039009100450004c3d1240416070702c9007220300081d88070802d400078400d00c0c5070801d0704614a0301d41ca84150300a10b240c182d6261010040c03d10091525500d4280403425001c1e206070950708000380641c4134412038500b500a1611180c2d01b4040a03a1340f85110301c020020341000f50302ca000034a0b10418404501d1001a08900988006c60140030314525030010b582c00c04c05c800300d040d403d40001e0002c0c03103080c2e40600c0b50a001b5402000c81903074a8092400007015640440c0030380907888107003420300070f180c5d41c444199011a0b2000d09015560f0102d82040d100b2111280d02210030707007110b8200380d20030700b160781c0145c24642500110b1802012030f4400d01c005900090081c0e045401c013b00000c0c0290100034800c3d000c555440c825145064001d0b0310b0428518000c201c800c81c80e40ea0b40180000b0001c0903034140b07018901c0703860114819803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 456306214 1250 456304964 456304967
    0x12030913050c120406021201060e180403020606121005070e130203130b070201020c0a0c1d0105130903170705070b0105010c02091527040c0e040f02090403050d1505090a020a 76
    0xc0c003e5100f210300039080001e400c000443d41150200384514520301c0003903941b40402400760603452240f1703003e6001030505028903030188829034001c03a8150050316055070b951091140304400c00311190301c148207180d94101406e045115103406418150754000365640d40c101440b60701c08410301c080c04010701c1001000000c103050074242c4072140d13014500500a880d500400c9000e8018465088010b0144030551400c0100810241041b21843d0720010f0090002c3c1c00c2141c1c00500922a551304160303400040300410f10254400000103209040030000003d4100041d0301c640001c8404a000c2207002031000c003404440d844183c0109001d10307101c4c0c2c01c1000c50f03010820488000c5d2200e881184410759200707481e91041c20340700e0454041030b4038000b03103110600c0000c013141d4242c6040d030f076030b00c81910040341028030fa47c5124461900f00c0700040301211036900348546480c2c0140141e0400c00240002032103030101d0700600ca10808a04001c0024504003030801160307000103041076461a104004402c41b03103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 456307464 1250 456306214 456306217
    0x7030302060601140702180405010c0509150717040b090114090d0201030b130903020c181308030406270219063e06090105010b07020121060512030913050c 68
    0x1c4403c0c40c04c40400050b11400980ca8058500c00035401250800b0180600700030100c4903206038080c40090020210594007568075204121a050300260443c054100036800c0a0090030024400c0c80d4103140c1001600344030701c258009030400200c1000c0010407604660380300d00c0380c4001d8890072010034640010030700000c681c0341c240c0100905158079403a003190a0350350b060b1403620229109205102c141c5803490002d49070500140d01b00d2040c81da48499900566140c0c1c41d0511036140700700b50720525042a200c94107250801082180c90366100c80c1d0900490300c0340d1141031245c282000155014003502c0c410030514a00c21030b8540c84081003041d0030002d16034000c07110500340c01c2586400c2c1c132a4107218007040040c0900c0902d810801d2026803903010709000040ea89100340c1460000700200d0f40ca401c26000303141315a0b480a0300056504450f14101261049a65100411003000041c003c0d40c1e40003148000840b00c4084c58a608003140e0b4103068200484110303010001302000300002e01d80b0081302c4005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 456308714 1250 456307464 456307471
    0x4090b041703160f020f011803081e0403050304140a0c0905070815010e030f060403080907080309060d0f0e0d030203090d2307022b020a080a110f0112060b09040507020703030206 78
    0x20080340c1d81350001401d0091002c4d0b4415800714000b40042645c0071034014807040320b803c0840008181c1400214200c040316081c00c60316200e541507000c140c0704c90f20202c40c1500040c0080c0e410026000b05034143c20780410080d501a0710903841c6003036140c5409904002c0707940080610090204403010824400281c40c20510b0740c0c002400c0c111042d42000b00800d14007003540b40c650344188a007030140014581c100d000c041c0b2038408841145c1322641c451210b030b5124091000d225170084810b000034040080d49400180c8032291481e0002040f500381131041e0b1400c08404014400b180d0300200f03000305001c1c180a5181070429608010202e1410001e0030281100205134906071250041080002c65895110b0100b10111486820301f440c00300300c0f0b162410102c9010304074851445488005541d190110b155942690445480c00d0000f900d901400a4a10210f0249040062500030130410310340521654000c2c107085040f80d40c4800300141804100d0b100604001d044d903006001c100000390b40052010b03030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 456309964 1250 456308714 456308717
    0x5160512180106090204080309120d0c0f080f22090b0901090903020c19140405010509160203040503011e1503210905100503040507170c0d0503070204090b04170316 72
    0x10301c404022012801440f443d0888101d0078000200010000b4002002d00341003402100c0b54140260454802c0f50f0300d8500a110301c0c0030510010010020901d81d4896117036450041d0011407070070707400c0c6052141c00d912039000840c049410300700d032078070303505800e07000390b0140000c05010422070000400040400c01d05100f035902c0d1030344030300407401050710a005020006d80098040750090420180140592040b806141e40d440b11050307007866140360a0044a040301e2014202e4012602d0345c08022845100421420b41944010000011103460911a51b001c0180c1e108441000c503050019440650b00503104004003084100c4007440801e1980c42c0107142c41c07001d03403014110303047d03044401d4529140f5030340440d03840f15403007980b00d81d12074000c4002c40c442e82c07046040d10949070710b40c0d110442030043c104403079119a01c0310b01301c103445042441c85e10b100c89010b01c0840341018825400101510b0703201008a440043d5413084c03004000e0103111041e0b0a9100c0c85203142545800546801a28840642d100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 456311214 1250 456309964 456309991
    0xc0307120902061603080a0e010c121d0709060306050a1a010503130206030106050a0315061d0411181c03020303240307080133030813090c0305160512 66
    0x801c5580d92801c48501c00c5109034100c1d01340215080c0a400040c040b5000740405c0d08115154654085c188103403900c0881e26200c1e51001d0b00f500843e030b4028030120421203000d81c102030021146400802c03c0750000c065503000400d806055191542c2036581c01b0341640c0c07400c1e00300780c00000455030304500d000c4801740c280303045030f142c2d07459100100919542c56006900b0500c00400443d5a562000c01002042d08585090102400b09041d4408688161141c48002607082c00310a400e240540c41a2507003000c01040454800200c4243d42183e50203a0b0000074558122001000d590526400000c0208207140401d00400b01940b006034036480018103070349000e0880145590342080201c01c418004901504445641e0b40303403140d00d4024231029440860f0306403d504820401c0e410103005040c103084001d441040d02d40f0f19561803410f80c000e411413181c044541c40c408215101e40740718140c23103144180d5000c00c0174203283d0502c512144044c3d0860041042c10040101c0320002c2c03091058000000140c0e64 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 456312464 1250 456311214 456311231
    0xe160608041703040f0c1d061002010b032d0303071722050d020c060906120c071b0302090601030603020612060411071a010f03030f030203060609090403170c030712 72
    0xc00d00e041400002c00740c804004424001070100010441c0e13003c501c10f10314400d0343ca0b00c8141eaa80c80f03040412920840c12416800503595061039010f01e0000c5400d0300001c103512502c4000a8184400500c001807000c44110510305200d9038030000310380003203400c40a5484c40c1071140d0028000703150240c60400c8541c0250200d420b40e0f0480ba4030b0412022103500030880203003945002a00c40c241204108014491180c00c10014a001d00880780064002030402e880c2501c1c024090134a000009c0c2582c03034540c82440802c000c00ca0280e40106a0000c14040b1484281180304025625901034001410903142800c1030005850394021100c90759004444240309980c0c0000042c0642400b09102c0c4100c440811510204511024500b0584541c4d072200c1c241607823150800119220103102c007070700150b0490484e2900d02c0c0254001c5400c00c070301421541c0381c2604074002c60741030721044d9000c400140d481c00705840401b03441d5886940050900d4481c81c41c42c1040400240302881c1c0450058142e40d559515 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 456313714 1250 456312464 456312473
    0x507020a0f080a200402031f0602012c161206060902070f0209131e050f12030f1003210e1f0e060409052809050703080c161502010e16060804 62
    0x8400c1000001780103650305e01d401981c509032a03254492284c1510201c1e1b9000c1b0f2020f006000300c401544a02040c94200321100100012250400440d4002c50003207050400c1440744081882010304000f04615001c14028900041101c009178030910317a462041c0314100010340c4106007003040a0b0100c440e820036446221490042005c0b010b00103004c80c0300540b0480d84409e80b4150441e00c24007a03408e80c3d011a4001424688429107803c0c8203410900c200002513906c2c22100116400200300100b03142c1d004c0d202e0343d0306903c1e4040345444a100d020b42c400c40d00c1300982c0c059602e895030746064500510b0304220701c010302001d82074061503605108100f031342c0030300c1a1240b4069034000c00c030024040c4194140342c40b0582c1c05420141c242d60340000e4101e903844030303100c4501403421556480002880780d1459510b074126190403020314078070540110000b07200310303604112528018000c0d80708002c017505ca4400c40a800c4031518150000a42c11000c5072000801c0400760040c100c50142c1042ea246945a181 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 456314964 1250 456313714 456313763
    0x30201080601110c0406030302011509051504090305041203020a211d01020f070e04032d260a0506010e1005040e070903080f09010e1203032707060507020a0f080a 71
    0x807645c1080c90543d0000074142e05400114a407200c1c04035508241d5121034205041d200101c450114800c04182c100c012030900ea44480e020ba8020b240840c102501c1d11048031400100003000d80050344006a5001401610124101c003c0c06064035049595100c00c00642465542202100c0740302c5000c5c00106070364002d018080360071890900b40c0740616212030300d4480341c03c41506c0540015109058021002049084500124001c0c0c0e4007025204c0e03010500b11a494101004004540c03281c2c440b08003101301814034180105910200403d540c03400f003000400d401c000710340091240000c41121160550010f044a00390750b2416541705183d9200c1005558801503a80300500403140010072058413a0084082c0040701c100b42e030341900500c000020080c1038211004500040d4000308080361069801d036a460615048982d40c11500414140110b13081002e1b50707004101150300003484104600d80000c903040030b00b007021441030480d03042c0070b6900e558010f000c0c0010b20030307800a980025030580d00709 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 456316214 1250 456314964 456314983
    0x1d01052b06150b0d0f020406210b09090c03100b0a03060b060708030702160602012706060b0c0f190302070506031003120f0e09060325050a060507021903020108060111 73
    0x16032502e81140d607551030340e0040c0e114542e605004d91522900305409801802102c00f22030341e6644003544100182c0900e0743d2442c03180302c05c2e202560790f0038220365251240c42d00c01d0300c1424420054081071000c542414100241c6600081d1052720b4280003008075590b9142910035030750040b07000a0b1520701e500104006109512001d8803605001c420070100c1d6600291080140c0030703410040c601c5a07a9003c060707003038403402900740c0031150341a100d017016000a041513a000902540010802d6542d5241c00811030f40150300514098104456a119005082103a42200400400c0e12020521b890301c0017501e81905005003071040d440000407800c0c00140b201c0a901454001c5075030f0040540308007000c0c14031162038101c00f01080c4485084601c034a4031601c118890038000c0d018000c0d4240714a03070682d00000c1225003080c42c100c803100109a6489044121025220903150650307a034410740104000f08581c0c00242c103207400c030b0950510040c0d80c40200b40b50015400c1c00c0c154080101c0c540218181407410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 456317464 1250 456316214 456316241
    0x3120911030a08130b0f0301060807050d330e0c07150204141503100b09060739031a07110a0c030201180503030306060708070c1d01052b06 61
    0x182d20700092114020050510082120311040903d030340f0300e402d02c03075030051043c0d83d0b6020805000420229024020705d9a0144075468000d103009106211802202c09661440076a40350000742c2100080340546428040814064101c01c103602d003024125009030f0040041c280340902140d01d1040002d90701c164030100780c000390250344031602c1e070b0f00b005c0560507414201e0781300303005403038400c51300d03c00c10705c01c0301d0003040b650510402c641c0c2420720522075540b119083c59000001009070300041802c071280d00c102c88050000031221000070b049190b2044101c1602d400816541000805c00280c20b005950000a8040101c40716999180415a0320041900c010a0b05000c1c0002c0042082400c0c203134101030381d100740c0310710090580d240328140380580c10f402000e40580c03041010a40c03174a8081d01600e0030f14030841c200c91030542641c1c2d540304034480340e40c8562038150804064007601186668030b1070140009480c0b18101520348210000041c2c0d9021040180f80002c402d00800d00090b0307040319807032490710f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 456318714 1250 456317464 456317473
    0x90105090d050105060103061d06010c02030c0d081c020a08190612060b0907020102031b070f0c0b0301080c06031b0d150b1206030f030a0f2d08130312091103 69
    0xc2d0500c180a01001c41c0d9081c002460440007250316203911111402a0b0b01d20b0604010998906006403080c02074882d080c1c0c2c0c035105d030040315003a0355268400914801c3c0b00e036a41c0b40d151562003035613000f0f001841c41c401e2650340c010f020b0480e0081d8407400341769008807052004100c0ca40c2c1c40d91303484010078071600624150015003800c9010312420b80c201e404102d00a94080c007103650b90540c124200d000c02e440c2c05082100b010500c05148424001034440e8900548503090081700c9035540604140040c3d0103038030440790100c01040522030511840c8403030340e03050360418650724141c152024220900e0b05600815000031a00740d00c03070b40e8250310aa003024580c41c4030742c00c01525002d03d0b5586420058100e1040310018000131b0032801e020aa141c0d8011030407005605044001d0750070380d81516a4041101040388020861040001c1001410301440d0440501d0703111041802d401041c480c1c000b01060400e5803a441c2d0200060380c403070240c841d5001c0b50300300020704049a1500151082d141e0103410740c036104c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 456319964 1250 456318714 456318739
    0xd08100305100614091009020703140c300415021c08150604050901050d080c0d05040603060b090a09020c070e04140105130308041b0506220902130b09010509 69
    0x4480d84140c09580310041c83d030704001c91241c20000c1d98201200d0b5802c4540905008120301c80d40c62300502061032103800d00034503144001c250546c0030f4000c003070703801407aa0001031801c40205000404d00300308860a0540c420131076500d68484a1807045124032240200300d042c44c0480c43e403080c440c0d42c1d111780f1515441d84401003d02001000804259801541c0b101e010b102c0d12110f182140c111011610094800c207017070781c0fa000c03c0059111540d40d068442503010000e1800c0d45006111200f66980d958999a4980d810100000c00305c98481e0030980c5105820000e2541a50740e401d1510200c561350030b40580e94001c0d0070626420710034140e0140d803112070303100148001c000300300f4502c02142c1c03a240300802165840003040c000742a19080060045a03020010070301040c1c8460080000c0c1d04501320007921903544074040f40065001d001e214155030007c9281d00105e54107441d400009280b0040d09500340140c03e0001c003100c082138070841e4040c0c4000104416164050429221188002800d0808590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 456321214 1250 456319964 456319993
    0x902030901050f060f130b0a15030501090b010c1a061f2d090e100308121e1b071103010504030203070614040b06041d1e1e0d08100305 59
    0x481694043c443c403546030b00060441c00c0504000111010080c40611502001d01c0341134004c0c00300241458201101140c003140d8050100d0a4082d81181a0313400980740d803500d005201250f00218071a41044081100ca60119404440c03c0c072800110109100007612001c000400300403050000040d00089a2500e9220341e0300040c4024400812085450030761002c49202d003800c0f1288035490f40407c0d9000e01c180315104022502a0b1711465190b41244001c1d1641c890113055003008901004d04001002008804134072240f82014241401845070f40b01e0601c0c0c0d4050900c00b030032386000200d0600200c2c0d4075040c0700c111158868421400b42c000c0241c0c0c145428029160740c4403403001d898a50500b05801c0d2807580d8549074074400d94100009003c5c6880b0b540c200302c043c002401d070700c001c807220780000c0010340d24052019091a00400580c0c84c9800d45401d6864200000c41c41c2600b000c203940306408442d0900422030751041c1901746000c802698403a0640352840c4003980000d0311921804844003040c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 456322464 1250 456321214 456321221
    0xc0c090b0108010506070c0e0a06050a030f030e0f091306140106052d030106200115090e0a110d030c0b19110a0c060509030915030f18030406180902030901 68
    0x401082c0d80d098066078881c0140b0410380710345400100321409005040001400c919030668020300c1941c40403504030380c0c2d440040e400500d5504155030b901c40b414405000c154002180c00d280c0001501e00c40e4040c80a00d00181016100a1206007111034201c2d5103800c00005031f0041d1030038010280031513069619071f04020030941081f48040b0415804c0b5052800c9001d01c40607000d4107002083e40c032460b581c20070008895441705145540c064003003508241e4041d9000380039003412185402c80c80e04109180184010507500484200c0e8455040b601304800401ca5100d0301182039402a10301907070031009440c0481d83e00710701c410003400354000c1409008014206048900d105404000c061004101110281055201d60314032003010910340c0c0c0c43c02000a001c4d0700690341c050300e0b040549003081401c0d404612015030340711881c5000d6000104210701d04a82e100b400f504407909404158032800d16405155aa104034058141030000e072020a0002103111009807010b40b000050564880c1082d114440c040e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 456323714 1250 456322464 456322481
    0x6101209140111180613090f050a0f02120a0b0a0308030a0903080f070c0b0c0c10020403290c0c031b0c010206061f05160c080a15090f060203070c0c09 66
    0x20b500300200344000780484000d40b05a040309070505089101460100134a1758410384071494100450301c00012030624621607074010b018282e001192902e4259280b50446074810606000c2c2441400072261039241c0da2a8594044105a80050502c41d038a00080090407640d00c014000c1c00e002040017a281c0341034208442152094440a1041e110ad04409070349060485480c80001c0c80505501c01148000c42503d400c19898034215180400c0b1040d030504140000400340340c40e9400050030030400c803d00b551100203c1031620b00c03c802c6958044080f01c1c140019080d80c0c2004004a25088281c1040c000c880c0b1500344200d07120b0841c10040c1380561038507110919079015002e081c000910b1410040b800c040400c00c100c51244c01001c07441d50665443d00503c2d070300c000140200c8500f50006942c071010700007038020740c00140007108044c584000903d00c40c4850b14480382c1058161800a005400d0a50310290301c070300050b0312950303140c0c3c08454080502c640901000382040c0c000407811085e6000744070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 456324964 1250 456323714 456323753
    0x150c070e06040912051308071d09010b0a0b0d0e0316050d09051c030903020a0e0108060c0c1902011b0b0603070e0c041521020301060e011706101209 65
    0x600755504020002107035540308010301490741c10080000003600c00c20041c848950500c00c0001501e46a100c514600203458005040f05412024140d060030b8540c0500343e03200c000c01e0b00a0242c40c0803a0003007080d51215201d50748807480003003030104159441b40c11000081c82c4034030880c3e0b16540300d48240f1410013842d40c4203640c98020402880320303062155106038140e54000e045c22003454641c1a00e200182001c003020380130001c03000070110041e80d4418102d0010858032000c845694109414241401c40241030107a02c002c08009480301c0500c0450148100540c40c99411410a00c40c00141c5080c820441d03d82e40c00c402d03c032001c008200c07142103494000c80040d0220391445407a036032882005201503c1000c0124810301c0100014412007403d810140101d151100c050454907406100d083d0007141c2c1c00b0a115000720040c448541d000c07802c0c00c00b441d8240381485e00800092500242560040c060b00d000d06028070290548038046e40f0240700703041803010100306280482c140000d4007000701e140c004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 456326214 1250 456324964 456324989
    0xc1205330a141f0816021c0516170a08010509090c01120612061410030c150203120705090f0904150518030703030b0301050c12010e090a0606080a020111071d06150c07 73
    0x103049100107040795403100c900c00c84011f141d01400003070303c040d08400a18010f0300105207410300001c60600140701c01c402d58100490300c5420042c2d000c1e010b4403058000320b025502160400041d9440041e941075044800c0c00c02d00030300154412a07501820442d00516030041c0400045010000c07940c0c000000041900d0001d512512140000d0050302800e00c80900b248400c007200380400d0030301a0f000c98900c20380c2e0040300c1c5000c072908040c4d003022604031001d81c0070a10101d443c410030f0901c9860010b101000b12030907407003450980d50306c00740a0100d50701c46090f1540e034800110b104c603030442e0300c04980518004580d02c50710302d0f1174014040c0c2482c9403c103001e9424000402c3d03419512505a80c01510307000340c035060a0303081030841e850559004017a1603417840b8400d801c82c0841c01520070440030380006000b0f4400004c00e40005411030700e01000358003840e0306ca65010441d030f40600030401c450340b1081102103800c9d1602c2000030516050300d40d0b2500c1c44400011070150440c4006141700c105e80042d038110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 456327464 1250 456326214 456326251
    0x6010e10150816033c0501061205010b0a0c08090102070308030a0f0605040902032109040219020d022b050d0e0c030d09050306040201030c1205330a141f08 68
    0x12015030340151503c1c240e414810314004c02c241e03007102c4a5079003000a920381425040140c5e84802c2034550a90020022a07a0210165210075950190901400f01c0c4101d481c81e00204440c018008203804a000e031031002d0106040e107290384240024001140c001802d50349a0803c6600074000788030204401d0603a03840c101c80000c2904060160074600b680007006003480803e543c865119444440b244e8881c00d260070010350f00d4641c0e491002e003d01141450714074200c03a00705600640742400c2a01d16400b9980211960f10b002d040103080d058500e001e8036071908400042e551305607002d001e0080814420742c180340800e00744020024803024660701c11012154075000061003503e81410601500d50903810000004c0d015500036000b86984458074602009203a2003081031a0464034190b41140507400114000102c100c407580b581d0003044c1e100d880001c001004000000d502e030071148103000140f07000c918100000d13607076004800c1002c1107003128540d026207800d1008000031000c84403c064a02e014050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 456328714 1250 456327464 456327467
    0x50c0a051e0115050a0e0c040e1003020126010b13080316030206060118091a0d0f06060b090603180c090403020607080106080915092802040b04050906010e10150816 72
    0x41400300d40000d0141c405c81400e0500d4041d00c01001030040140070700030003001850380006245030f8460003244492440880c03d40c40010b26001c948500010030450038050b8102d00900048103a04507006d60052ba55101e03409101d40704661002d50242449000c08285072003405404950509001d1181d03003591256034455005507410103a041070640549001070044c004411503a00500810b81282c80072030343d815204d4001a4035200300002186d103103801e03d0032002004850b0240e00c010340100541503080000d0500869001d01000300645549070150700d00b104020002d201016080c6006002040305180909002e90703100c1d0103580c2140000c0c041310000800034403d9503800e01440c0d01e44c025021146104030558580341c2e01414182d414005e07580001c0c1800301e00130325060405080503810148450741d0040008880580c558540118180003c112024034042407490540d54260b10801c02c03030300c0d201005041484d19800c11079415201c00007550115800201843c42407900600d0401d030a452204d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 456329964 1250 456328714 456328751
    0x312040528091119030606023004120b0a0b0609040b06072f040504030903030c1a180610080c130e070b07061a010f1202190c0318080a03050c0a051e01 66
    0x18880141c00c15000190040309d03030642c076180c030001d0380540040b5010703134859407800740d01c26440084800100700306402040700d6400080c0d445619208208400d1443c003002c42c80d544601692144603039611504440b10750b03524401d684816401898090180c80b0340c4d003152180700704031042c222480322480c5140da1140303403038001e941c45250700d03681d0103116a1440c0d03801c0c2d4080507030503021658650984040180750040310625442070545080c0760342001c0d030314a501420940d002e01074480400403070400b8440b20700c0010f0340140c200001d540c0c005011035003540003001031070402c02c00c4015000f00200094060110400303080000c6c007903401002100d8035070b2800216503240c020058082055010140201c50040800034088855044058505072080241d03c407144c5099030000302061122164000f4590700c0307a03142240f18204000c001605092000c0b46698148003d00103040010020301d08040034003e00221b4440303030b4440704458100350040b400c50103c00c1d1401400c0340a40c0b03040f0500079600d00e20300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 456331214 1250 456329964 456329969
    0xf01020a0518061c05060a0509100620010606020303010e06060712030506010507020415030c23060a030e030c01060303080604020a1e0c0210080603120405280911190306 74
    0x45480349012101c240b040e003000c0502280e07541c803035000c0c4103078450b0900c6240101411001803100241c00e02d0004100402a0000e03007000b402540180c00304511080c004900300c05480c410305110003035410001d120000c814032003440c5000d95081500000b0201c1c0c0000c095810b940c00c81c45654865500c1900303010850043c000302400348089020a29100d43c0281d11031600001c0602d032440c5410709940101d0141c45110011210391006020208284812991003001810f003914000c40c1640f025040d1b4035410980000c00e5100396800140f5400741030107a440405a1550301d0f050382c0e150151410641d00801440c4416004969100b0000307140707107418403c5a01c3c6d4400e54403440c40b80140784940380c4180f025204c0403410710207011081c20259403400d14040c07688120f030391000e50074944081414281080400f509841640501c014440e507a1030394500b02c0f0a05121a1074491800c10b0341c00006040c2c1d165000f41c4106251502d00c000792040500200011044158078034014071304644124112070462 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 456332464 1250 456331214 456331217
    0x30b06070f021e15040905061002060109051905040302010e070602071d061507050703051006030b070f1e02031305060301082a0a090b1008221a070507050f01020a 71
    0x1c54035006181c401051011815203540341d50000d00c1010204814800003550b9503401003020804000d580c3d45405142e0f4441d00a41e500240c01c8659130002e561200180140582c003903c440000e69150001e841c1048030001541b0284100e003480e0501a000b0203040301042c07490b018903a4080340c414000510401107409010000e10600f41c000488025184081c0071554403000d1080e40010101c18880540b014078003600c0540b82ca58030b903141a0340341c03022034520079850b141040c100b0804a0100c1354002d90200341414845841b0102900880301c060101080501680522401050995000028000c54000440d100c07008a4441d020000240000d100d05007041e44440001d070301e50020010071160141a00386000d940660070700021f040814550081c134540f5035140840700c4189080b0141c00040d00d0309080c040500e0134008103024081c038100da1032003622240340c00c445080000d90405400a441907100501c054100000020119888003009031410321a210b2540d00b11030703040c03003100e100d120726 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 456333714 1250 456332464 456332483
    0x102061302060d0c140c0102043006020c0a0b0709180e0606040c110106152c0108270f060907060c11011202030406050f1311060c010e1507030b0607 65
    0x1103e40c200003804520449a0402001300c1c1d10991a1a03000080c10031015a0000980c6071400c0209440b0400a1808214004000d00a0340c904090400603103003203150f048400541e603040b030684001d2038454141300c020002c984840c200103095030300007458030984600740c42d40010341c6202901c02003070b501c500c061f1204c10342140d800b043c242c4c5859803002c0180300e420300340b40b0f0b0400c005103245401c40b643c03503026170701802000000408e1194010007610108400c0138000990010084403142500d0580710b070713981840360300c0c4040381025802011546020301c443d03c06220700e10348003100366210510380e5024516840341002051051b80e0204e00c01c425151160365042c1040720039246c800940080c0d0032803506003c0c9040300d101c104513103400150300c128052400401e13107003001c54078800711010003407003d0403c0c05042c000e500080c0c07000101c0c50305a070040303a04a407110400f405240c01420307646100c038414415000001580781081002900c2450319450400c05503032502c0034465644106600200361000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 456334964 1250 456333714 456333727
    0x17210c270a0b070506090105010918061a0613051801060f120603061404030207060e010e01030b03030c010e100e010908070204020d060803030903040e0108013e070c05010206130206 79
    0x600c00a60316000001d1074050300d0707540d07080901980c0d40495070644180c3c00a208011440c10240a03840c01000e180f81c080202c1c51103140070070807889810800520702c0343c64107a003802661460318480f000d984000c10707190760b45552907141c0500300c509115140c040c120102240c0035241c035504603103040310620340b6081c60b1880e0300441120412007500b940d441322683c5190100201d40780d0701c076a0380600f5240c0508441c1d03042c5401c001c2e29280d42641300c0c030700700440740c83e4229160740c3c0320b200e081031441e0a086c0400c404030b041c1c00190841c02a02c904a515610701030340782c0000640044e01d1086407010300802c004856803c002d46091314070300038016060000c01c0009500508040c0c3c01445140320701c5000040c40c3e901c0e1b40100f81035600c180d80003025a0b2020074248102e440c0c0c1c1c500d036401804048000c005080d400390443e107840088403031102c410080502022000403004001209014664920503510205442c19204801080c020240144199000107000c01c10084402d40d03810303002012281444c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 456336214 1250 456334964 456335017
    0xf02150114120f100509100c050f07030207030203011122050f09091912030e2b050708120115171504060f030605010305330417210c 58
    0x80075040d00c0001842801071020480c0018001c0313880007100280d01107854140748580d0742c60300308150803854815140080300022280c01400301e03540007000e564003d03215206da0070180e0400311942e002039019400c000c0720a0350030480c4002442098000151248000c0d01c0454220320064a401f8264001d08944d21204091800707100071980301025204507009507020014500f03400058003003c503060780d5140282c005d1160540a18403110403100010481c0308612222401c10f16007506c0c0c01c68400500185040303c1e944200c04440b0440d400445441d62101190010800c410092040120010014400c040264420181001c05a680850300001600e8550b0071f1240500c5000d4084d41c807641d03403500040d030442500210790040d402040000707410b625505004e424212105c60340450217076071108659070001c02d80f0b910380709a04a541071a403e0359031860710b026002d4030944500019840440c404410014101001c5815a4404504075403a1507840d112104d07400740f24610000705114030030590049 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 456337464 1250 456336214 456336229
    0x60708040c03051b03010f090f12140a0507050c044505060f180601181e020712030204050f0402030603010204120f060b03030301031a06040b04020a0f02150114 70
    0x6008500507580d865807640d07070500d002d50050200b000d11051030881c1c5841c2c6003e100795101080e5510061000c0c010130340e20140c94640740d440c01031181e07640d45c4261940ca03104120303c1000d0a801e212640e642d0315030742030241958024281c2201e5901c60350300d0b940103d050a000b06e0150306980340e030a40c40b01c50b04550400002120300041e204100d4159612803846648403180a6503a01036030280c0440c0c204051410010301c2c00401c47e18045002c0300c103046284030000f444a0445010200b070803018030308000300b00c0142811012000a0080f2507050980300040b81e0b005124052040001ca0942c25030b8003c103030241c2c01284642e5a00265404031144a402c0030b8000315800b00008000525080d119803080e884120440c40c01c7d01c1c4281410211001c0211511950145034001c0740210308640c51a95142c2e803140d00e00500090009016022030610307100d54000c40800720000f041551604055540140f500d43c0d000c00e0500144542c5205111203100b111f04c15040c0d4842c01c2043d42e909401900348003c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 456338714 1250 456337464 456337471
    0x13080904021b060c1309020307080408031914190c08060d060e01060b0304050d0206150d061401080321091902130f0902040b030309010e011b05070f0e1602060708 71
    0x204030000100d9464120144243c91050300c10a0b01580c40f0768200100c0040284107030006101184100b0501001c140c106148a1f40503920100150340e80d40c0c0c610000000c0c40801c451880340c20b0408071142c410051601c071083c80f81e008010003400704120100310f0015a200c0111a0b004110240042019070406e4091350340070b540a40d2000c50030400400c4200c0c00c580040e40300303e20305003020003800100300c401e00808083e40c150f88000c241e43e08003407180e0840c54044070000d92084401941c03560030400c554001110b40d0386003507002d0708250ba46000305034907548100d0101e0800c50301e01507141030700c540c4003200c0c60044039280010000c42e513244500c00069a01c00034160b074040d40b92014051400424050034072030000032a404100c0592a10500080d101c004540603c6a0000e004108199a106902400380102441c200840c241000c0440f0300e1405500400b52580c060101d02240003101641d0000403a000503009001555500f80050004880c940c2c2e41401a041000800c3c00c492050b42420b81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 456339964 1250 456338714 456338737
    0x60e012f010e06150307050604060f0c02040e010e100501060215011a0912100f060612050a061503020c071a0415120204151713060e0c190e1308090402 66
    0x4924948030700c82c61404000700c80303030300c100c9588524080c11070400303000c840007c10068546a05150400070080c013045610482d280410424181e0344056503900c0e001400d03818980d00003040141581807074580c0b21101c0e00c0c00c0d03140444c00c01c40005034241c80010f5a010304401400d602030981d080c070b0708404100c0050f410850604105000050b41d41c0e6a01d280b003048104103030f004040d4501700c00b44110595544403950001d541ca44502005099008481070413a0700090f24002110b035106080c0c41c00603c1c180d0000d1038000030701c22150b968607030140d0062644240300411599a950b46a034003c02036081040205079040041c0f000300002c00b04c1d0410000030202e1400c00f4401d00b520400004c007203030829801090090307918004039640c681c00a108c0d8034000c0400c50000302601d0b0100e01c1090403240200d0091050381c0c0ea07940040101d20602600d02200d00007080c0803941410001707140045031b41c1340540e401c51802031010a02000084941680c82c50303000f4401030500d220501080020b4004080c9042e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 456341214 1250 456339964 456339971
    0x3030702011101020d1401090c021c0c05070905070908010501080105220f02060f120601030606020304060e0a03140f0d02060412030902030c0a0f0f0b0f070f08040906090501060e012f01 81
    0x5000b0405d405040b00e601080c40516070550301d8290060251541c400c501c00c1903401202a0030042d808505502d400410181403002070480070346007482c030381141070b40a800005e01c1c0c8070500c549554403103d00002c80e8542402400a0790303c0e02e4406003200c10540e1b49410740400d010301d031480900b080405a9943d4080c003210103070050150040750050f0700450030b00084200c0040d4000341401c031850510340081003841c08101060070010040d680748954041c6506103c1e02250480440d901c84400c10080c56203e208100c1c152035081145543c0d1888107428915070040050031801c0340d02c0014800c0c07080c1d80000900000c00000e10742a0014000540e05a17094050b451084070580c550f80001c5000304841412943c04614140449404c803045400c1130f0200003003005031440c0700c80100169150b403504181d10541207459071801c0070881c403c0e541300d2114581422400103901c011079102c0750481c6d9583c1c440d4500c0700005001101c000489500c12009401b60910303070804200300d4210410941003000000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 456342464 1250 456341214 456341227
    0x70b0402060f070501140a090b0609090f07031202010e1605060901110a110901080f0601030b06060c0f01020a030605010302040b0d1e1a130608031b0102070b012903060303070201110102 81
    0xb00c0703160b10400069031569105c10650003034440c8102d08940c04946042c0401003003070290340f0702c0c6845c82d01500c564418041e590210350540400e01038804550440c40031600c075035680e4981003000d545454108000355107004100b09114101003100c000b441c80c001e045000b8039003040100000c070381000780c455040020cc20035000040004104000f0118000c641d0619103100340c00030005000c105821441140c0c000758541c418824000500350b0550781d00c40c0121406940e09008144c65020712004503e0b01d12880d0810604000c0643c010100d00c05143e42c1440384c5603d0f00e005400341e12507440380b0b840c404000c0000d07a42e104c596038030040341400b04401030303080072007200700300344c103480103410b0b03080e050f00c0c0301c081d01d9078a0324105013400003030307403100d14240030207032409650607164080c00312410b4604040300610700c0c20301700c20760458140c00d0341300701d4141c802d503110110070340200744040314180111010481c0c18642c000c00002c0e640329800040084d441c103000703075004494000712808211502e43d000c1c400c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 456343714 1250 456342464 456342487
    0x7060c0314040b19091a03131a01090b030c0f041503021302040501031b02070e0c04030203060a0605010e030f120d0b0907020616030e0a0b190f1d01060803070b040206 73
    0x300010119002260348504c0f0031101d00000710040d018190620400c0d2900b042013508060700c1248503061181501c0e102d55541d082d6540c2069442c200400044482942d1340b15994030740c0e0418141d540e1080100035505050051598616800641c0c139481442c0e41c0c40398400b4642a0004004920100350440c01300e5a00e60100e6a203100d0300c404030790440c2c1c0204080c421035078503102d1101c445108031036180030150b1160020351900168024002c0c0c01c800e45001030000c00c05002106c000b954040c00f20383c42480d10f0901400240900e0081038001440521003070701e541350006d0000007811800c03010f001050182c074140f1805601000b441d50500ba1034a190318016503074403600c28820b041e1900a02003925003031020141c201600102c0400740f500d04480d40c4245280041d8102d00035500c03a400101c140c03100014041d000c68801600c8044604045960b251041c4941012051341324001000601401c2260305600b81c41243c02035544a0f4018454080840c6c0e15124075034000f800504100e1034041c40303186 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 456344964 1250 456343714 456343717
    0x7060b0a0902190302131202010207081f0605010509030d0f02070b0d060305060c070b01180b030109031805030718090204090c29030705030403030c030608011401030203060106030e07060c0314 84
    0x1144070310540c0820a440003800312060800b162000d4601140342c20290070421407060040d0080401400f4404201c1c800c59008010460183c4910802c4a0000c03051800c4202c506964414030b242a604020300015a540580b0075a03526100080150114070051001103400440380c013503a5007188100c1d20002814508000209414840204081740c0c250843c01c0c001d1600802403d9004034000800c003030343c04113075411003043c10350f8191b20348900c03044d26503e0050050000301521507450f502e0000c4000c10590821200410f10243c20240c001040c0e0300d20801d6121040c61041141110109543e40100020b40d41b0605805200820020320401f240d112402c40d09a1904813101d40c1c004407010400425000070032162034101c540126255180001d0020a540400350006051603220410310301150b000741c12510140c56400001c20a110518079180042c480038401030b4001e0083c0e00010a43c54824040e4980707903204100148007262610400b112060748a2100fa010000242078030b42c00404500c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 456346214 1250 456344964 456344969
    0xe0f0a1206090c05030c102303010b0c120306030307030804050a120203040e011410081905090109061811101e050901020f07050918031e03190501060c0807060b0a 71
    0x15000400e0b10301c2d40b03019494840c45420062081d8001c031a4480c0d15a10607050791250851450400510540c2041d5005440e11910a0b035640e0640400040386d10013240b4085c1c03240511110854280f180b81c44942c610038402a01c040707070160020003814011a001d090302c039800a00c200d0848035581d42c02c1d125998680c50306044d40d401038100080c1002840c03403c0c5480e5024092204904000c20505800a4511400e0040801c24405800009540e031f034046260004d9010480780300740054030b00248054020184003001b00d0704140741040c10800c500701074140c042c1165106801700d1130001400200002d2240c035049280c00c000d0007513040220320b8002c1c42200200250707521026110b241c100d0000e820020130041e0240306512070382041280e40d465502c0540c110b000380c6c2005c0d401a420070016802c5120302480c4514950070054049090b00391003000394495a45040042108961a80a139003612028452200010038040d1004045082c0e0340040c04854440e5100081d070041002c080b81800149030f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 456347464 1250 456346214 456346223
    0x409020c0f0a1a01060206010501170a0e0a111c05150c0d020409050601110607091707080307050a170f03040b150301090c0503100b060f0d06050a0b030108120a0e0f0a12 74
    0x85032681d00c45200e800c3e098050040342c006001c05604280001303250440c54030a141508a0344004141407019650100c4003825068082d00e01100302c0e401c01c9105c8042d0300310000e0042016142d01254400d0041e841500c466211000c0c045000402038a0303880801c02031b110f052144c07401c01030b586011050b4401000100200500030415140c140c0024041d101e0400604403182c20032010014000c4d44158600195803503130200840d03c005413510b991403c44a90401c8480c0c0c0700c0003a0003401d1190004221708101c0c81001c02c003054803200c070340c42c20032805400d4080040d9101480454002a41c202d20309921003a0341d82100e401c19000000a425190002d03025103090044403000e0019050501240450505240c010300149804a0100d0031920901c2c0b2000d04100d408a055010040580c015800a20004107101300d40c0e5118070309507040da482803054980030711a51030800f200c81503000070f48840308440c1d01d40802d0840800c083c4a44400034500c03c4e94420048880402c00c0507a48004a1419014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 456348714 1250 456347464 456347483
    0x51c03060b1c110304030e090c160b01150c0507030f030e061902010507020313030b0c07050f030a03150b0a1101090506070302070b060a0b041e0f030f0201030506010e01050409020c0f0a 81
    0x400302d588110392981c0035040f0320b20020001c1001081d00541c1b4021089400d54494003c0e9980a80e8030b0507d015499994000b0000d40040c10284520605007a0603129441c017060051401e005d803da842e03808540d002801504031030400c1003c5145102e60441e42070190420107206490000001d0040d0311455401007000601009128050750910441d0b6210026000852400c0c03442c034546001c201003031000800b601c05480008003500c0244090b10b60b006d80c41400c6440006c2800e01e010b859420002410f00041c0c6000400404061108500340c202d501d42060309113441c1c000b5400b1958489184541c12081d03403940070b80e0001032070401c04c242c82040c466800585401107450f1200341a000030706102d02c1681c5607a0140199044101151300301d0703140c0c0340c6e5100b40302c40468840b45041050740c4600a09181e211001003407003800703c86100a14801d07070b01048a651b4900040d43c2d04001c21807842e0008800348400d22540000e0741c000d0000c00040300448140751280c0001510b0319924603002c8562020b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 456349964 1250 456348714 456348757
    0xc140a020a1d101a1b01020403030e030d2109081207020102041a030402060301050d03271805130809010207080102270108040b0613110a2a051c03060b 66
    0x1030202d945034011140e5264010001c1c68502d00c0e070702c802e103603c83d581c19500001950000c50101011041c0c45240c044000390f45950362428080c12003041c104c0308901038000d611510910500c9410010214140021454481428901280014282d01c84125000340c410004140d04200100b6082d00c550202d0b0b00141c4d07203070300b05030805000d07941c40900c41c495603d00f0300034003006a54101c182c03419500709652280c80070905090403107e11045640f903a80c0d048001990700504200800740b0001c3d50048000d00055428200000080b0b603002c40e41700910112a24806000400200007072540d000148101c2d00042d446000079800c80c1c1c004a03507484482d110b0711491040d490f00054800c107542c070900340b200080c0750a803034820745118014400d81c407500942500d200d03202c10641c428401d0000c84240c031900c072400d081c2c0140c58520036130311900c50040c03070700303030100001c0707410070080d10140c2e401000f87c00310340ca556014044c4240b0072441902410788410b404070b0007160140143c1404413180114184c07110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 456351214 1250 456349964 456350009
    0x15010602070503010902011704021503040c03021c11011101020c010e070f0b0903060106051c0204031514010605090112180f0c080d05031302030f010e0127030c140a020a 74
    0x1030381c56001034000d904000903400540c0e000124210002001d907210006c0755200d03c0000c003c4d41300308940072f40d24100401844180942d00e210241600c2c425100c0300391148140c00a4030b4403503c44480140880100110403c1d1948139866201032899088005818038854140490a40305940c1441c0200e038800c00d002c008030300640c4c51010081204d107101c82c0c40c0c14040004207864040c14020035051000005040a0320151101510f03044a00341000b10341b250b4407440e0003417082100e094402c051500740502d080c5002402001a4102c540980b20946007481c9080195210030411000444a0380e45908942001c010040b1043d0030324800c580700380c0c0c0390b5030518010500c5d8000385c2050089501080c1c040740096005400c0729040f800000345481811010310000c5d160120032042440554280150a1148c01c0305421404506500c00c0140b40c10004000350500490f81e100b40c0030340001c1d0b81c0400a004181d000c0700e0314984ea40e8510a9682300c50f10b40d0045030240c02c40d98041400d03080703540313005080c22 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 456352464 1250 456351214 456351223
    0x603090109020f060c06130510050705031e0105030606100909090b19021801030e0f2b050702030307020906240409050f040f0803091f060e010501111504110315010602 73
    0x2a00c111a2281000c0c0d0b0310600c10740d2101c000340b182c480540c00342c0c7c0d40024800d0030803d40041805c0320b8000d000604d48010300070202d0b002983c0c03e16501c508001945207045500030064103071035010707004007002c3c3e81d107104108522507850400c000b0f0110300722000c85d4114090260030f040038092414401c40d81030030020006400c48032161a00c20034414051450340103500c0803400703911102460007040c55050203108600740801101c05030994071440d02030800d0300c2411003901c001c861003a1310034090b03a200c1743e00c02d5400e80b08410000754581c004001600c010704e032403c0007607000a80985a2600c809600038111440c0b010360707401520140e00490f042040f6034540c002c696010a2840600c6e2103410b00c1d907510a80805800801028900048000340c1c5c44401000350080c50707190740800500c4074000d10883c074000d0809000744030f11620b0800010030254010801c103100481124024a980030728940700750281c1401605c100d0701800d2024140c2d055940400802c10b88100031030103051305514002d006880c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 456353714 1250 456352464 456352489
    0x6120a060e0d091211130e250605040b0f04030b01080a0506070e1c0302032703010f0903170a02040b030f061009060c031206050a031406100f05040c0e060309010902 72
    0x10000c2d103000c1449141c131044900031003660301c0031040e0502d403092000601c03003425109a40000d5807030642406212440061300d100200f41c08626401601b00301b8602c3c0904001c180211804501c08003c01c120a170901e2005200780f442c441202c41c00d040c1c0b01c0d40c8070f000d03a00d020b0380101c4065204405280902c4814270445401001300c1c14040d81010804000c580ba20515a6184580f401e4007005002403600134000c4807070122401c0b034032000318607161209100d000c0141c80050300175032030170304100c0030390b1000e220725150f01c0d81503120740c6215200907030060b50503100204106e61580d001c1c04001803401c3d0a0001d14000c0d150f000c2044594980032051000040e1036850341e208101d2103660801c241c0303401440f0202e0494061a0451504003060004006440c1035401150091070020b0008103100d1500c1c400710740c280c45001030303c681d5201c401d507400ea41e00885c040c02d004c015016070304014a291070b138080080640c15040030400707a24200c0c00a943e540040f0b071415020394654140c10304518104800816 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 456354964 1250 456353714 456353717
    0xa11040c210e0706020a060f0c02030403200a0603050915061003200301030501050103030206090c100305130b010b1e120402100207030512090a0b16030806120a060e0d 73
    0x1880112a002010384030304080104020680c0392820340c1401d00d0360408441008000100ca0099680712402540d822407050280c40043c5070041442d0510803c1c05106603501441d1700450805081d500d804008441e21083c40d000741e00582a0800d10352200c10800005241903280040c07289054038100382800050545109404105010850316543d00c920490016145150000d01802c001c1d01c42c5608034005809602c83d160b01000001c10080f05400042c1681d100c2e03425200f050f00c0d00b42e41036070b0303601801071841d6200c0b04002c05071900901c170703900030703944030010910140e041c1c04261500c100d50002a000722441c540c001689002d00e4502d0b450042403040c020b40c0c40c601d0068500340e8806203690291000340304a0051030800181c81c820040e1102558010b4180d4100000c1c141016119030700a601550280c401504001542d400d11010741e0800d0f0032071160304c043c460142d502251415001414250301030a41c1000201024081102604081c8030300710000d450003268070300034605020051401c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 456356214 1250 456354964 456354971
    0x16080313170a1e0804090926030c0721121b0c0f0204022107080c0f1e040807080601180e0d110a020d060c080601020102042d080f0a1104 60
    0x1540d46900140b4404425044040380caa51150035207811000303c1e0242003c3c02d00c1300040b0b00407a280f5015889910013a204070521201c000c03204e41d4040d091080205e40314054002440099031001a50004100003031040141c50300940c00050488845c00600c484040040d02903500340d00c045100d486841c0741504640c210748000c1c500c16074028991140c022000304901c280b40b107003104540310341e010764002c3c0e91201105a15a0b060440c820000c10301281c412000a02c10400704030016851004c40d8072032001480407515200c800900703141e448100d806000c054110030440002c1c43c91003404282c01400c140e0000e001c1c11b501d0701c100103095068000c00c4810f864904140141403074030001c0c06594144450034030503140c070b5503182c065007021541e10019400494440c1e480082120a0f8032414030401c1c0745c2c0342c200490301c0d01e000481c01c0f4020de01903805440d10500803c84500c0759842400303800280801407400d181d440750300075401c150911000c947e0075402594100d0800c249401000070440c01a1800c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 456357464 1250 456356214 456356249
    0x50a0c08030c0c010c05190b19200304020a03171308010b01051909090204030b01060f020d020c1e0d030203120c071502090d02030601080f1603020d020906010216080313 74
    0x2030f485118501d02103040c0b0460742c0c40d803010400b0034000100300102041c00515149242d08244240090445201c20903043ca00c490044400030b0b03218503059035154590210b41d01031034217140350b10303035001400076640b002c88980000300180c0d0104000f600900302c9550315842d074003421040740b00508160020080c0d64100480648541d900006071505041e9400b68116040304136201611800401d8002007981800041d0200c10b0155024440741210800e80e54400c5061042e5812a29281d10071002030060b0080c9600035810724004c070401c17003041e0382c1c041110300c01800e20b40052840c1d0001c42d01200560408a60400c450075a5540683c0c0400c0b01608a850005c49955002c407042e8114a604000b5502003208841512400f08400c81c19034013804a400d50f503111105141c0d07a1045131030314035a0f071081d407150754030a4039044160350031268090603071074001e00305500704800e21038000c092034114031a040810b0b4202e154000210b00800200d806180d0320040c40e181c040240e00c00b80c009803d40d00c0300c1c8000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 456358714 1250 456357464 456357487
    0x110a0e150d05100807120c061b120905030313090b060a08070f050c010c08040606050411040b03040501140708010303140301030b06010e060d090c1e05090f04060216050a0c0803 77
    0x44500700e407a0707520005615030320384444640f200324642002107244904503000c60010100c0200c0d900150081d200c0b043e02c1c507500c074001c880060881100086810880e50010001aa07a0032851202d95003400c04000c840c1d1030b00080781c038503000343c030b08110400660001002150158440e0520721030040c0c66003440c0040146003c3d06114001d052101003000055465040c84d00c01d17410388003946040c000a000c02088800b0062800e8007e44080e10b040d8a40b52000030b4034078080c410011101d000040403070800349010f200b03c0c0d05402c000e00540381035488440b980b15030075000c80168801c4203e511414025411420001c05110300300c814040d080b00704000520118125400055002900746045182e1030b0b00c200102c3e800e030160b00140c20fa080e0900a801e010804103000301402e541d403000d4000f041071800c1c0108030800c0c3d034911610713400c40e4160011840909880010b69400381c010100586018085a12010310300603242055039103821806202e800c000940c20700d1801801d001d4019400c25074070802 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456359964 1250 456358714 456358717
    0xd0c050301330c0302070513050901060e01050d0813091503050d08070504172506030b03010b010c0f1403040b0405131413020316090203040c080604050613080d110a0e15 74
    0x2c0500501c10100e111500301413080102c04003604001d8100d0700401c010802d8140a0602551488074079404c106020503100d001601c214100c880080105002864030380b42c01026a2266800780510402d441000c1696a8a40602c05990004903544006645181459818010800b101c481003040d0b0a041c04081a800000e84050350f00c4c00400182001101c19414584030320b90800400c640243c001044480c0b62600301b200450f040e0b034500b170103c44c0820f000c0500300e0341c4c2c2800480c00b180706041100003090050002003540c910030070a8491345180300b40e0452454010703600080c05120009024801420b2035040b000c3d150700b4143c02489290741e1000703904101c4c0b1004240e009070f0882001280290b5804000d904034181000f0714100c1010f444500c050060350044805443c0300c0d42e807900c0014115000100ba900c0303243c10501030b051a0316000300b52900d800600b00c090f81c03407200900232040200e00c3c920a5082e040f4000054a564203000b600c09801000744014041c416a088034050300d40d011205c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456361214 1250 456359964 456360059
    0x6010b040e010b0903030d0f15080601150806010c1e061404110105030c0f03040b0f0606040b040605030a14070c0209090a02060409020d090b0403021515010f0e01050d0c050301 77
    0x3c2a140c01e05140801d20f13500803101c01103406814010392801c0c9440d154450b50714181039041022000380c980164542da0f42c020301c40c18a4084112021301c2d001803152200d1900098145804003411110b9111183e48105002480340081910410641084154401c4030705848103043c0345056441d06489802100c0e070418402418484e0010010b41e10100410071202c80c01004600f00303480c5c1c20507091100d1500070441d00c401c0b046660f24003151031480c2590135034003129600c810107450f1a08002080320301d50400381042d00b690713403541c45231040e110340860b05030f02c030350010303500c0c0e840c0c40200340104144824090080080798008000c9800580c940b030040f07d090320040a005a9280394111501005041c4c802c000b400d50303000d035000d100405a01055004418074002d441000d0340d2a00d104040d018a14075802078003044c2010b069100b2a401101301c103019260504000d420b004440700c1100903a10701d06041c070005031000005202c0341c1d140d5003d010054540081030440180c1c05484c1003480046407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456362464 1250 456361214 456361229
    0x609060e0409030311120a0507030e10090201020a200108060a06050d0203060d02030319080901021206011803050105010f091a012309060406031d0a05071a0f03040c0806010b040e01 79
    0x1c50300001410b00940041900c5c0384d94115440d82c425140150180c20f5000b60340c7d28004605080c081958507109004603940354901a0240c160700460000044c001c10030124100c1c1980036107480c80d004504041140c018120680024040b4100304030001070103220000d11146c801c42551005008166000f81914654410101c00613074075103074180050030404088000a51612001903050030403d82c14948048440c829151540b0544030814010300341e000b03c50380c070703c0340103412000582298841d09284485c1c0c42d4050b402507032540c47e0b840301c03800c0d00c2098000c0c0c9180045c441c4100505a503034402c101000070498100c005002d03009000034081805c2840000820f215100c004086400c940200c59580740d008114964541d6115000b501a00222911070301120b5025010504400042181203180340e0103000b91042c00c0c2466000030340c4000210070f41a10301e0082c4080083e4081c1c060003903009a000328000400a0b28100c003107480d0038416000b6680604050100b00004005250314a0544040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456363714 1250 456362464 456362471
    0x810020f04030f0c05130506030604021309120806030c04061d07050f03100f080102090123120c1209030a120b040b04090b01410409021906090609060e04 67
    0x10381000045015070781025011020108012007081009900081280c100360380f00c132012800400c0e14411038204403080e1390581c010100250040c03800c5140e91150b00200900040e420700f0703d07212000c401c0c09600d17201d00031551810900040b0704d0304004044030403004441c20b110b0b0305d05213590803c42480d44000684a0f000700c0c8082103004e80035000b030340c81c808040c3c01456101d01d448103d04000d40d403e446400c0030791032056000311b040041802101d105581c180c594891501341048a1000300c1d840d84844034401074140100707080b0350101803415000766180b00040c1d8489900250f49900721038050018076040d0303c2001106012904603100c06100540c0000010b40d07045c520b4089009014800c0203190f100f1701c1d040302c4e80c0411104032000c505941d00c401d200350f5003640400036102d03084d00074030025419801081440040c0740c1036166a0003440301c05400884d00d001c40358081900142c0f2106040c120f4141310303005105156101c5100701c020003d91030800105440c00d0400742641d0805003000340070759103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456364964 1250 456363714 456363727
    0x406150e040b031e01020418020f03150109080f0601050306060108090d050c1e06040302010b01081012060f09050312070c03050706020a0201060b030a0c09050306271207030804020306060901081002 86
    0xf0140030054003800d141c0209407011424200c0c5600035400341c0510f03110040222800c4000782914825903801c03500c110700161864031030200b07001da0450317481d1303440f410403120000200c0c800100b0b101d02850814a100100450350421041604000000300070034108400701c81084002c02000820f24680b49070390620035030359000c3d0460303641450303290b00034802c05429400442c5020000051031510444c0a98005c0004000d81401143c0d003020a452020020001380824415113030103490f4241800d1051b58002404003600c20b500007500c1d000502511150400300d04421085080c40c0390a034400d0705071900740804d03a000e941c0940907020726800500340c00e030301003020340d801030017584208083c04500402d04e84a203806a408800340040c4810100041e25210300014641000074400e1700942507071074901401c981c0750b00d1217400801520301c1100640b183c0c0c000c0015081c0f80754014480d10b80039a48041c15880c01e801890718084000e4084c0e40a64050b000400c1052400300e80c0c07400f120081c5074003607904c48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456366214 1250 456364964 456364969
    0xf0d0c1502030d060608070e2d0f0d12092111030114010f060f030e1009031404030c030605090a0f0605072d090f1802030604140a05060406150e040b 65
    0x70700800e0b504054a08080407800ca0f8010702520b107e4990f0303035210300028007418180058508858a0a11641c0c1c000300700000d1311545020302c141022024101d200c07070010003c00100c0d40c2c00e40c60408d03584120204804400b99510088040103400d401c0300c5149402c20054012090040e04500548044030140359041540d400f90018800d454006400000c15619000103020355a030364411b084c040b406c0072190030032541c02401034003151040d40d4003400c0170020b0100c28002400340c5140403010441d800c0320504100c13040002510286008040c100001030031881e10408455024250300c0055101046050000d130325445140240d5912101c0030a00b515085000d86410302070361006040e282000440704e110284000319540499100c0d99450b1029a58091800301c89849004061050020300300c080ea54100540065800c964003400c0040e1009005802d48404801910b00d50b04882e02c0e41d06105042ca0280100c86c0502410181240342001e4000c001d0040c040101c00320b4026611905041e03140c5c2e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456367464 1250 456366214 456366217
    0xa05060a0203280f0b0a08211210090c1b1b080109050f280f031202030a0c0905010810090929070f02061603050a1e0b0f0d0c150203 58
    0x41103d55010801880e1403a02000509502c0080ca0a441c0c5000d800c03a800d850180340c01e0045030300d1507003d04600c0045140050240c1d07401c00c50982c1c4100d00b0001d80c041c0c105a0711a541c81000c3d49100404082c2c01c0584181c1030307640c0070019808200041d0b1103405443c40d034800c1c200b40c85500c0074200641400c0d00c004502c03984813075400f01105500c4c2c9480b28050102c08981c00c0c180c80d81000c1960307102c206680e00c2d0b00b042015003a80401c1c4810301e6104c00000340580b50866000f50003414283c20704181e261800c400d0341d00880e20407484a0300e4440c0c0007038041c2c100d408400a000309013000390721031804c0b06442c40024800e10901c000c40f61074548900521450340c417603503000c010b4000710459010000d034072559203410a449000004803036607030810001c0c1c400724450b4080c0034100058221803105120403030103820058042c4207a299540360050500341c00200c26814082d4061003c505880140d0820420544802d1100d00840e0112030381d10000d5410512182507401c03100061100f83d9a441080307145 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456368714 1250 456367464 456367501
    0x9100c1b030305040510030b1512090a030e091f03031101140f0a110408031209060709080a0308061c030201231303050705150a1401120c06030b120601140a05030a05060a0203 76
    0x6001c411400f84011940010304452b4000c0c181d0740f40684502c88401d0351201e590f00043e0000c1d550306204070b4280b40248034030303810000e00c03160111003580080320300c5007500c120340c0114007107500d0845c03080342d0413000c1c0910115080c0084060f14107180181020050200007041d030408107980c1d00c122603076034400c07000b901c015058420031070352034000c0c0c0719130401408000c0d00c03100058441c4100241003103100310801d40030b94881802178140c8085980e0700351201540504074a03070108071a103e00d80030f40301e81039121500c5d6000340e001183c1e6081044110340d40d6031181401080006860040108000080d22494021645840c0190750b0303101c9030a14904002c850351400c0101300c0240203101030400d05411400c0c145c080e1007003203102ca9a9a580c1100d1322060600001e06890001c4000c0204601a41c0000c901000c06400d030314940612001041c2000004d03003150450100c4400c80d0303034a5003030094011000d0081035000300b03076510103615076544e2010020424060640c0001c0050000500d90159038030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456369964 1250 456368714 456368719
    0x150f1c05071412070303050a0e060f0c0a120212120711060403170703023619170303090a0803060f130b010f03050c07030c060209100c1b030305040510030b 68
    0x6080d19241226005465044514032a1900d480c401e191000f000c91458200d9606803074040c607110400c407054981142d50000680d0104050204006000c00c0b04020183c1b45c028801500701050170380340000c070419140c0c1d0144e04540c029205e030041c0c00708007402c070340c0503107400c80344018130769074104088ac0c1002ca5100c400e5164015802408205900070060700041e46020060034802e0f55083e40440c101c1c010310080c8100c155001d5048460051400c0340302c4405c1d2141000140e29041403804100b0004184442a61b8003440a03002c0080d00030341c81c101802200c40d01e0246286040a0f106140d44008111000d80a15000004981c0c90381e14800710b03410304007003c0d050412240d81800084000c00c0b80d4101640410740e48862080410721910840780f1a01c0c1c0700c040f041c00e002254404651101c0e2108045664076420408501c10360360b00100000094865690b12000007407518012001d403c000001b08416003042c1002d00c002a0000c05031402e0311010355440880c4144454101c0290210584154 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456371214 1250 456369964 456369973
    0xc030324030b040b0106082205070308040f0305070f05090c0c0c0306040b190b03030f070c0905091e030913051e0c0a03150308090418060c17150f1c05 66
    0x104010004070710368400c50088180d1302c0d460f0f0341c508099a1045e02100d0788400c0d4203980d20b00041514140242c0803016000f4422100c2c160f44a540b04800c80d40160003000707182c030507000c003042000030810503000a0a49000e201e49480d18100103d0030444024100380407206000c01c522010040400182a00b214001c0403180c95003810b08009400010645202008800d000821010a0101d004440c40d60300702400540c900821607001403c10b4006440807240e085100200080b004507a02409001d0810031018040c0010406071101801280d40c0d62109940c0080c000c1003829030741c0c61780e541b0f0580c0d40441c01041c50380e615040001215001a0a01c00e900f42003014040402201ca0240515031083c0e10100130502c0c40301144801c141092000400c60102040f060030141807541008071090140e05145541106550b101000e5603522003103480010201da114101900040e180300d500310f00030b000c400b80000d4001022075041106000c21501907a65050101403441022054610340c070b40000644 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456372464 1250 456371214 456371219
    0x60e030703030e19180c0e0f060a03020d020408010e0c01022406180403120b06040506031501020106120b040b010b030c03040201082205070311060a05160c0510030518010c0c030324 79
    0x291828045011340d00401b480e0100703000e01503000301da4003001c3c20002840c440d0030350900401c0001e01d501000d149020181c00703001440e0007040500152002e00110000401c45443c01d03400c15190181e41c2c11514119401608444e54110f462a40c2c40c0c5681c11000000d032155440401140304054134078005400d141c0144108001d0680c000860b240740e400c1524140008100d903420421a40618010258041c00c00c002003410125440c030300c101030002c180008190390756140c1000042410a040a8592800314400c10080164650020380175200c0c4000d141d00714100102c0034031141c00003c0c002414040120080340f01c82000380e0300030140d80580000100c1e8010941b51980e224071040c0310480d418400160745806e035203000b50a41d480d8000c0b660350789003040c00ca05610701b088005e444041d030b50a441d07550089001d0700c81d15040c6032544407a44003c211401e081d04490324041e83c440c49452640d24003036410b96202d03448000b6420f05905403401242000c50307007544081b103070b010b5850a0032003010034200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456373714 1250 456372464 456372479
    0x1202160f050705060901120e01141f05040207031407030201090b160e09040f0f03110d110c030a081801090509090f0f061e04080c0d030510060e030703030e19 69
    0xc0000c1907100d4820b442802d942c40c002d20586005480b40c15000c12021458080152055030080040710400d800103c6d5031807140c4001c01e140c030700c10307280004d1141c0c07413020500e40c0c1e1042c24141402080151011890300b50365440041c40d0b0004080342c50080b1000241000926100b50888900f41c0d070000300d601c40d03505044200c0810032104400c00004284007401e94211440e28a2815110329081f201e0391491070441e58890303c1d180c4c0e40220032010b000c01440d03a07284a000411001042500300d8440c041240c1c481c032000c0340740c9031920020900c29800507096500203601d6209551103200210850701c9010341c1d0000588015540d50003580d080300e990402c0040c460703c002920300c1e40703580d140f06640383e60070b51044540e160b0004655200e23030241d102c440303201f04007401d5080030340c014080c0d004141000c1001c07100d03d0070446001c40003130010f6101c1c1c050060180e08100e5800003400542001000c0800d82000b00c0c1c2c0310405444050240180961042c04644507052401019100c02c54100c4109461b10710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456374964 1250 456373714 456373733
    0x218100306051509060702060c07080604081308061303032d02070611071e020d1a0f0903042105160603140109020406050306190801060f080d05030105060a120216 71
    0xd614407420400801c9003a03c40e6200840342a100c000d0040392500c20b0a800f070007a15402071211101d140301e144000151303241d013840050700851040912a45c0d030301811802c042c07101c6017a00072200a4000106101051520040c844207055050030041a04800c0402c0c03003081a07082c22128900b6405c2c0034504200340019801130000b1440b451081200c010000e2860b0154012458014803000491200e909901400c84040390a0362004060f909062102c0d554070040d001c98404102e40c041d2101d050141203000340c0903996012010000450600c0c1c603061403c001c0035080b100315040c9202140302d190621a09120000c3d014091502500d1542e81c3c5030303001401041c4e5085020035184049001240029090084030300300e40c4141d8030141107459080c100b0101d1500070900b9070b04580f40d03e5001800c00000c1c002d0f000103010780040403a0300b9140c00415410164481503003c20800f0810050000e07542d40c400b40ca454080606c1e240151040c0002d10b00001e10854107080d41c40c43d060903107002048015030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456376214 1250 456374964 456374969
    0xc09010b2d04030c0f0e100e0a021c05070207060e030a110a090c0915050a1e18080714090105091603020409061401020d0c050601060e2d1806090a0218100306 69
    0x801780701465907140c0c0806040402980c1c18104040e5820080060000b00f01040d600142014001841c00342d030603035131a0402d004130103210b010039100ca00b080381240d014441c8500810007420422004140c610009032501e0548200600041c0c81000d101450740b2401120742c054002103c08111580c44520081d0501d40349214854156003155007080c0091b2188040d11109a2140c40e0207001b01e0b1621411101012180c80c544204500120422104103900e131001008107d0782e0094400c0c14100560308103808800d0700140d00686060004210584440310010341c4045960340111208a000108601030f01c1907074000e0349a2410301801190b102400504040b05d0b690903000c4030060040705000b030750a0018818003400942014004105043c041c0c0498601140c0003040703400000d10010f401110500380b5101905501c0344800c08514900b090380600030b01c40303851000e90003249013100000f46000c9006050307500080d00030451010103070500c040c0403842d41c401000040740240700c03c4018000c01c01403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456377464 1250 456376214 456376229
    0x6051c1d0a1e0210050a05162603011d040f06020309070501080105120c04020c1e060f060d0b010614040312020a05160f03060b010903120c050c09010b2d04030c 70
    0x1400202d904000c4441c2e0751040e5003d010740c61000c0c0881020745240c0c02510f0407005006081044100a0340c074983c004180600c43c01c1060344604000c029890340502c920700c1060824402c100520003407078400e20074103501e5000024882e240e81c5030300d090551138511003801410503001000340480d21402140080980d0001c1c0d0b2118070170307030f603400400201407030700b102e0509150032030b0bc00d00340340c0d040603001461402528021200c59a041c6c0c0c81640248000c01c511481035040b035800e00540d20000300000303801034400c03581c85500c0415074507002110070b4184644402c6c010241d140c1595035024030241e600a6400c2160700781610300e00b92002c1e485030802081207400d406541c10078485c84204c0d4500c403059509210420007024150ba4610004140401e0801c0c10700c08402400000204801d140b04a81800356880c030003117846901d0300e0352522000b4041c251003031050000503c2030222441c29100310349911001503080c0840c41c400103d095015842c2000512030000d000702c00d00480c1089070040b44d810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456378714 1250 456377464 456377483
    0x1b01050f060609090a090c050604140a14010504090f0f0501080105070e0a1d04152a05030106140d0e1b0108150a0303050d0b060403030c03030c080106051c1d0a 70
    0x81000300100d0780708100030a540300713201d00c02042803801d85511454410748141c0c845078a0b03a4030340700040c0440d001a03010200141010410f03a140307080a030004001007070020100c030152015480044c1103401203026129003aa0394200c0d81c2949050303500400070303140c1d0300c80c2d0401080d6194039009020b460216040741c0030401e01c440343c14960405034400070840d08441c0e0b00e501c4541e020025030411010113003041d150b1840e81040540c42e00007610640130050300c00318500e0195900c5c03484005001120680020034071009200400c04160007134001507400060046582da960645c2440400612101503202003e200c3c030712000c2003c015a10504138164008d80b6000c40313980d46c0c0004542d5190004600d0b40e0009400c400420000b401000542500c90340c02c0d0000c6403c00004001c1403031a08558000c2d80081c0000c55584245601403051040c80c41c041c6c50321840e150304001000c1c04038450a00f814100c10020444488030525a501100040402081c002e0b0f2802c03012035116960304003200e003a2100c401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456379964 1250 456378714 456378721
    0x20a0f090b010e09070c02150307030e2b0806060705070609050a0807080a080a09090e0601090e2a0312071a0f1311011412010801060b1e07081b01050f 66
    0x81110340c040f04002028107010341d80394603044620501034107049822809448003800c02c2c1c080c64014600c1070300c0d207960019010407881c220500e003800e188603844203001c402e113a00251200d002c09d0b010f80c585007814080426107400010402512824001030300d5801140c0010840b142e00400358021510122a50610507448926054130fa440070701c034031403140e4041a041030020780c0d0304019005543d107a0400e141d8483d603a400c520f059031035606031051580c10480c01400110058400d000810f071582d40104030b83c45c02e5900800c403602d00495241e00e02c5c2ca0107102c4840c20303501085000400e140b2540354946a00240c40d01142c403074080f105841c5800501000601107242a6416034030a00b9000f00c1d441c41c0030265110801d403208807407141d5041203080019620114026802403051468085810700300b5032400c05401d085071f9180c2c1040c070507207008210170031004442000c0080f0141481c40c03110354032441890040c6080c441d54111401c43d0000c0140701c902c084041d40201d100d5003410b00740014580c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456381214 1250 456379964 456379967
    0x4060c0e0316090c030605060409020910030c0e131508060406060602031215030304030206070807060b0405011a0c030c1606021207082505030f0c01060b030606030412020703020a0f090b01 82
    0x5072440142c2500c01e001c607000c001d0012583c03c40e0000e8906400c1c001031051f01c075000b00f01c065105401002c0304940005100c000c0d4149000e100c81105a00e14040001c0c59500000030590075140302c20a00c542d5040002240b00480755001c900b00c082907048100310307a907031941c186480d02c80c1220305032a02880e01d000041c469002104441c129a031024401c28141d440e1143c02001e1100c060381d590705440184000700068980744010b1510301c0c000d00b07107186c0320200c610308a0140c51046906c03500450406004000031342014442d1201c084c003030003402e5140d00f00003124034030f1401a160448043d00c01c1d044150341d60340b03682810390191000d0740d094404c124280c604074682c0344207209004020400801c5680b0b84002e0341c0c90229050765080c0412400e0030410344030b59145030000d00b0b0002900000248081c843d80b001d104803401080c209461038110b2030082d0024a1030b01004101070300307880041c400000c0c450701c00e21900005c0c581c01081006003a480b10414003400c0068000d6861451500703070082c2407517 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456382464 1250 456381214 456381223
    0x180904060b04020c07181b0f0504050306040b0406050901150b0c100603030512090106050114160c1e08010513110d08044110030f0203090114010b0a080103020120030304060c0e03 78
    0x140703101016104002c47c1c4045c1210342c2983d41d0000010804284030100740d5903000e1040074001c60040c1c1401c1d00e141401d050000031a207001c6d0200541e68513200403000c140c1c0f00301c107014040310b070180f1030b1644070782500c502d45041000182c0802643c41c42c00350302008160700b00e00a407007520710030500d280465440e00b948608035200e0f4000e46010559900340040c50032300a100918900d032004110040e040c01603514042511215003140408081b54940d1184902c0c00c03a8061006005020080c055410700800c091a44624480094881c001c00e08a06900d511404101d6051f50b40c001c039400d44e55a0348020300d00018503000c0d4101000150960440c000441180c1c407902c4110349101d085000781e0320001040720b0031600c1e410180515880d180303031580b618681c4c80618882c813480c50002c10f51030448454800045c03016005201c4d085070032320206401580c01200c05055a5082c00c0207201c03805c10030040d240400e074510840c1e40c10b01c0000100420485150001103a5009548660740d503503500e8010907448 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456383714 1250 456382464 456382481
    0x1512010218060c2d030319270f02040e0318010e090405060f1819121809050411060304260c1f0f110703021002180904060b04020c0718 59
    0x466000c03841503154282c881c0740340020070a00c2d0050800703910038201d0080c21904121400e040043da02c0540764004060b07800360300c40c1c1d0190004841a1440880040302d002101c1c100041d052854a40b544811500c60b54410100901d41d83e01303c078ec03102d11100203c08241d8403107000318000b804249228902e030520a805a0240f5840300203002c4e603239150080c06540b01001415001c11201c081c5506200040134003044800c82100e5409070400c00d01c034101041c3c1d8100000b5181308010391a03004900d18a1201d050106407500b02e800464036844500f801d40300d01d042c905c103055000c01c0c0007041c00100f00c05900301980c1180f4903c40390308019000c4003808018050300d00e02d621707103070040b01080242520846030220070012800c0e00050b09140c00c84607404481200c112151003040c009050008e03d82c04008044190000782425480c2a901e4480020000002070403103000d203030300c00003080c01c112403030b04040c03003050029000710344135200d002e0f42d20f0b0b90b4021481b0f01401c00d0301c15644044840202d0103800107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456384964 1250 456383714 456383737
    0x110703021503091011090108090708120d09021305060f01090324091407170d050901031a13020d06061805270132030c09151201021806 59
    0x28405030211040d04940c00100009100c2c000c802d80102c10901c1807103001c80400003101046c0d12007a1020001d40b551314050101100d41c0d00c010410082d0307a200155100070755200a070181d03150307003540d9082e1003c1c0621000013580030b401d0000103052a8415805140b0903001107522002d84c054603401964841e080d03000140c900003210903180710018006180c4015528061030018011056881e201250b41d920580b400054214160400c88a411100d542c0002405407014040b40004824094218402c6a07030450515403140c808101c0b05a900d21036103d02e4901405070b404122010140c3c20095000300100b4668520300000425154801d0180c0c2040100c2174403600c1c0002d01342410081003808084000345103500d20305003c0c0c0c20140f41e140450007441421015145101d001d80488425900f95103900030444900c6a40542039600252480058800752000400c0303445a42d0345640c19125801d10750703001f4125005402d03901c0015401418100390f10356594462202c50b80c200900c52145809044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456386214 1250 456384964 456384979
    0xc0a1b110f030309031903080615030a051e0403020c190308070809220c09360219180905061f031e05150901081b0f04050c040611070302 60
    0x141400c1c200240031610030020110b03030070484102d0020b17140c403125114200070310401031944010141c110804907040882211085820210341503000113a0000400c8800001d4640d40031039400f001c152501954140c07842200c005600d003e06019541c0c03c0d0302c0c031010340030f200517817540c18068410030340300d005403503100546a01d000c08548031241290420044a44c0c40741701455021500000104100d102e8800380101003107002c080d80300078000a441d94059880c2c01440741c0c0100e80c01801e404020801d81c0030411440810a14503c0c0c0c0009024000a440d003402c01c0841c15070f840c0b40c000350403011001d06d4904c10080315440300da8000c251042541c0d0590080203074200c58456031034211003091224130518000072132100c0344d440d601106c0700080341172101c60790315020b02201903003e00a5a83d0581c0503614024694500740280d6581c4800080010283c1a5000b032031055076101c900c0903d41c80d00c000e20a008600301110b4103200c5e58001e04c500400f00f4000c00050150076008500074044070380041544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456387464 1250 456386214 456386243
    0x9120306011b06020c0d1809021908040303061a0c01110f161b030b01090b030f0d030e1908030f011e0308070206090a09061703030603070b09010c0503030c0a1b 70
    0x1800c0703004950812528503070240700c504403c41d400c0260010b046020b5507004030441109150103224807d54000713004607801000122182e03026411000690300062612600c1c50f911801c0c02c8000309070b10381003540070540c8201081051010480507103e040302e890001c0060f41544c0203018441e1181c1d80503841070640511070340c402c0988000c8000706450084840e080400c0f54240e81c20003a0505410484800b0188801031002da003552042d101140000c1d0028006494000385a41da617000c510b588904054959182d45c540c588280100f6000000051034226130345c0070f91814a480f50021a13001d81640081c000028844c1108810901994447da042541c01030660700c4150696001d0707101603070020000c1014008a0301e0b0b1044601c0180038810000600074289000c804051402040350100741d8000d02c24040d550354042400b4044507000840c0759610b00e41e040043c0c0e01c107040c03658080c180b8000481081801c690f1b6000805002c42e15a0b9030b1241802d03280440c510f404000000607090b81140c075441d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456388714 1250 456387464 456387497
    0x406081c1b020d050f06041514071d030703050316050d02030a090902090a05100c05012d022a0601081c080609040309051c0c0e04020d0609030c0b09060912030601 71
    0x144007094083c105840b50480318a0300ba1b4a006407c1d02d041361407a40d20b5004a4250510f4410018840303000040030810703041c04440200303411030354030790080c40078140c102121546d82e04000100c01980d011042c0d030f8a0301c00042d080c46c400b01c0665002c4c2d4042c00340034501c40a06202000700d80b482840354882445646c18001200f0082d04850086608000ea44402283c19a1121040da007107101d565140c1e02040c020f4985242514048244586001400f0340c0c0d00700045840e45581501c6411041e0040c1c4568003448496015200b14500c0e00030440820710142e50f9550110f0418103031981c0f442100c14412800d2a1807040b54480368061002a0986020518501d4414601e40d0014000d2400c5680d564032a00003901400020070a5099180842c0c0c1030010011070603210b1000f0600145102c00c1403415802140058007044801040c1c0c80e940e5003903c0400d4081c04541c804107400c204004200e1030040d23017460b519101560304c140a4450f000c441c41c02e0140030740c204d0384200d8040e03491044e03103242c2121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456389964 1250 456388714 456388729
    0x315052208160b042303030c0d1808130306050702062203180b0a031a010203070b130c030303090302010506191406070b0f010f0e040308150f0406081c1b02 68
    0x2088502d8184224804000c503000100c403a0149024030418580003400c1c0804410101581034202c02c5a041482040024814241580c100d005101d00c0440d4040da20300424400f20741420b00109001c00c08140c1d00940740180071904150380c4100e8040019848644007681d80d8101203070500070b2445d0b42c000807011082d600d11141075843c0709040c25103103010384148445c000c4465030004041c1c11804901900050b03414080c06500c0044480000c5141e0001c1c00002d440784178401c2c0103403102c02c4502c0840c5036501e61000c2c5800313141e0002120583c0e21b840b80f80050280c540c2540c203030015800d002c0815100d250074034800301c0c8042d29446500c0104d20b40003c403d440300c803540e006c9078014130a01a02002c1101c41802c0391088032344051007070456040c07904080f04c8a510703070000a00340b13418804000c0026080300c0312a800c031a81c2c0901c1e9910003074180001d1221001e149415030400d040410004554000080403403105d0041c0b4204003903100b148004442d4540300600300c0315003411403204000581003020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456391214 1250 456389964 456389977
    0x3040e1501030f050a0e120408030307140c0d020102090a140d030e011b050a030f0f02120313021009050108010b09010905060a0215010b07060f11190302130315052208 73
    0x10b020071091102c10399001201c4048843c5034105480704040029024244005005407a80440d038904141c02e201800703030f5a01004000b02e060081c04130003400c85005000031343ea130801484d01182c0310100e14005c004c1c041d4100d090428090740134602c0c0490000801c0b00250805040600711125100254504403002000b01d440741e41801100e589502540d20740f600701a001301c0c01480100074142ea1842d00401907440714a2071800c1000e00b0322004042c070740c0840c04201d908103000c4150340369212107007a60400303208008003c2d84002c0382041c0c151860703007180e5480215030003604c45641a03a41c0b001da0a0740c6106569080c0d00242801e2003d100d2498444044e100c280c6043c4104c03a100c40c03420340b01868801081e0062030f500a00482e0380400c0089500452328076442c1e1820601c8400307000c100508880c01040c00181c7c0131120391071035200581c800c0e415a181000d410055001080c0d487c00c158a42ca185504402545420030f00010012600107851200c2d5922062842c03010b007481d074a60044030340080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456392464 1250 456391214 456391217
    0x806010302090406120210030c09030605040203150405010c020601080f030403031d040c021e010b09040b06010c0818030111042114062701052703271203040e1501 71
    0x748601845520f55110b1000a4203d0301e011111150b010300420400044a41000041500304003010711140d6001c030110b001c5a138042310118468a49100103800c16505181e10395003000140204400d2041c1504040701402482d025190380d1b036240e8a155859640035440c543e89039008000800000f40b1400c10010502d003001c0000181125400004099a018405400041e8400801c4068004e01486150103100c1c50310b000700054440100811006040140003518140f103070000901140d020701c1030034001681c013030109a601c0d100d10058100310249000c45501039031828043c0766200030001c0440d070684105100d691440032203450000c1c02c80440c0e00081b240384030a40a41c10102000300529805403030345007043e035a4007a410212410a0b8038000f41268207070305003801d22465041c203c4000303084280034900c5560801d050400d81e45188201c408004000140040881c10b11103000b0714640c1e41082261010240f0100d8802242d8a0048d4010050112516030211300032030048074001d04c40f220107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456393714 1250 456392464 456392467
    0x1903030f14041806060f080907050904030203090a0801061701050415020309160b0d180c051908070b0d0507090b031f12060902120a03050304080a1e211b0806010302 72
    0x11016007010904003c0707103c80d0400d40310201402003a03040592150710052925004015140420040c0e540700680c0c0308483c01580301c8004541410302c244215100550041c3c03203916400d645000c440d0091040b0b100e040558166040164450071040c050300340247e41015130100c01d00e07940c010850081d403000d03140c10003e00c0303010006160500e1003076080c030042000d82449a2103000d1135a1002c1550300390700100001040303000e62200000c01c110504000e0b01c0090791880c101d070880e0070400340094144d40051005200340540081c0600a510040c075000241ba08148280d8035100b400756490711075130113001070015017480098041802242c1c4000d4540b0b90182440c817481c0c1d54420341148582c1c00009586480c0c440051a06504007890b88019014800000b0890701d449030314020801d001c0a4801450450001001d4404600c18030302c100d050350544510762141190104c1c041e1940f10910400880c910420b8031703420700d1041621802031a0071104411518002d14000e048528043c001c0c800c0c0e050590 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456394964 1250 456393714 456393719
    0xa060e0307021305010e1302010c0f03051b030301180903170406021b2d030a03110432030c060313050f1009020102060901090309030b04030201020d050a0207021903030f1404 76
    0x29080d103041d031042500b5200013031175410315045d032140c0d910040802c0300e5030b100c8040160050b41c0c81821210029007040804188400d286000c031071138401c0034a61189803c6034140fa9026182c040b00450495541000c5000121401d00c1c2c0074055072810700f03001c3c010900081c150410006a46041390344144100c0006180080030300b81d00c40071260700d01307441c10740d82d2002030340c1031211414a640c074191211030030104001d00701c208901030381c0f80702d0380030004209030303c0e02d0140740458080b5007540c01822241c00e034184001c1c0703010889070f0080441202034128240c0400c20319128100030a1419005d0340244c007413444c69507078401c03501211980c000111458407465885c0c0761030300740c24442102e800400d0440031a90300598000207261000283c00105540d145c1002c03040002e03008500b0400b1680c1c032540d0400503580d41e04040e4021300a00c1c10242e00c2c030317080ca420014103015503802880414400c45654060540442118600d003c0501000300403a051182480440c1e00070906a0700c0c1c0340714581c00c1850141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456396214 1250 456394964 456394969
    0x916300b1b0c07030b040506060a0b0a030902040605030111091503060f0d050c0414060a0905090309010c0317010e0615120406050604180803100605030912070309030206070b010302120c030a060e030702 88
    0x25060762055503145c508030180020850b0621020340c0006040f00e403080703014100706c194005c500c1001c65990a05a440d08101c04545464100400801005000f042561003440100040717601c5025501d00c1089603d00c1c0216000c40c010540c0d001e400042c18200003814641c2c1400b4074a100300e5001c0d100341c03080000200c19551280145440ca030300b03424007c1d0840c102401032181c0508a90804010070b03040c8070030003050144c00400e80341e0213030091074100724032941e90800742d41c03000c1c1900b404800c000d010000410043d900d00c0d8030b40d01801d020f40e0302c2d0b998403c40f55150310041c02076420700e14a84006402140104902e60441070304002c00400020720944401902c04101c61140d900702c030351400210412011011820f080e4008042c00d0401614614000c00e138191030b01c01d4291020b00c0c10300089000c1c2c0500d48a881c040d00550b6000c0d00103503448815017801c18500c1803d00c000ca200b603070400002c0e080e5060129110700010390181c003c1c0200105a07030755201400d4550100c510031700c8188003150260307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456397464 1250 456396214 456396223
    0xc030e01020d090b07020703020d0b0c040b0c06062b030c1407090504062703050319020a030b0f011b02120a05010c0c05010b03240916300b1b0c 63
    0x42c078041030000b0842c1040c9030555094800610790310a5420400040000da2296108445643e502959a4125541c1c03800d6684050066400c450040b1802040521400400264882c061002100c41d01180310024101c1c0d03030201268420480d00d0004c44d0051030009000c0c11b01200d6172403040c03e86039080e08070151140e01d07080710742c2e1040d0312140c0c4410500082c0002c620556166000b2a9803c41d841c4082a0041041c2c40a001d17009040240000018055503a12034440845405400f4191340c0d8112040004024080c4049824410248501c0413140f540c083c60300000c1d0385d4460619903a60601075020000c00c0d20303002007035200034040c0c0c58864000540a100f1741078811015260f0103019081d40c2000740c01c5502a4401d54081d5000a1607140c2d00c00b55064000119520009846500c0c0d40700840700703052500c011240584002c19800c08120390000c2e02041c10302c0c00e8a41c00a2011007041065020b22146032100640740c1400c0b81c010507208842c503d0007403808814051168a005580d42c03074070307241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456398714 1250 456397464 456397477
    0x10f120317190605031203061309020901031101111b06070203010e0105010902030f15031b310b0303071502130f08150a0b1e0307121202071d0a0c030e0102 68
    0x100b118044140b03000401d01c0740601800c001e42c001c062200c04000219114840944507a11405010b10f1310b1f05440440d13005040d050358094001c101c0d9507581d01d000c1d04000b038095412408030f1464081d9602c5c0d000001600f0400e08407181e12080c00010840600501d5401000d081e6015525a042804c005100f4010b20b802888032500041e503d00d00034242c00b10942c40501103100840440c0e42001d010380d000143d00b4645134030981d00207000c540354400940010740c040c482ca82044440e03a80124901008003100902c400485420b002c642d03e404201030305c074494036800800c5010360494403103802c4c3e207a42c00f401651544814022110b41c5450121502c00300541c86004c05038050280710740d800440086841d04070303140010034020a010080014a080110b07603080c0c88461416200d5469640e0401c5940000c3c0420860803043c241c8a00f0150140460300701c404000d03209002001070240e1500003c40180d503108040c280c200d44034819004081c150170805801056160707604141e00a1081c80201074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456399964 1250 456398714 456398731
    0x1060e18012928090b18040906050a0b010f0c170309150c04030c060807050940050705070302070605090a030215070c0506090a210c060c110603010f120317 68
    0x10f24084104038202106031800e800702003080b52501081900410700c05d07616040c0402c52501c91240d0071030042001403190f04005041d142c28402440010801c41d40000034004082c2e80300c168800d60301805482400d0440c000801031a00e038542c0b89040c10000b4040c40d0000c0001094030002c0e00504403500d1601c1060380c0c8101ca900000074104200a51404080c00410300f500b090b4a261070401405055801100701d035034042d00c903e0102402000c4110500c07080400858003030b0700100d8484038800d0f040310070032030900c403000d01c1c110110340950300400c1520211941036000742091070074a0412105500701e043c140380c00600d000340120040e0748031440c80040b4030407800d04070b03190311941c00e00f000303142455404180200c408116030140e070780300e01030035506661580c510f02c524141c410344800c0d04040c0303007480036101104059010641c00ea01c0316403203010328003c0b241c490f02880000c040051030705c802e20603002c44a02e10941000407040016a00c002f4900a00b0201c03800800b1004451030601e0858220380c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456401214 1250 456399964 456399997
    0x20c030403290702150c13030204020a0306090b040b0f010f09050901170c09090d0507021804060509100203100e072007060320161b0602030301060e180129 68
    0x203810003241c1081d41d00c180f03284010041a485030210f451520b002400007049042c00241001e040c2e0311145110001396400703402155105070704078005000f8111402a0300905003000354844240ca464000c0400000d0002c1600310a642e1510065900d11998000c03081440754140001070207640c0c5007a81402841c801403440710040448030010b091031103d4603030710b111340060424070071301c4400050303014400221410a07682c0d0703440900001d1407070140e8101650745000b44008000410019402c07141c02070031110b040320a8901442101030683c081111004100e1268001c10000b42500c8011660014000d0070008414040800504103c04140c5407912545c0c0c400a42008101c0e4540b164000071840da144283d048541c1c070802172120700c038840f44070400803000e0500b0801d1143d0405c1a520000442c20400440c1e03075686000f03500c0340c00910074800482d02003582c10a5030300f804801d9048803141034000502e940c1c2071200c5c01640c0c4030403007032203107200209402d9800040080300c0105074040c0000000d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456402464 1250 456401214 456401273
    0x20f0a09080610051203131202121f020306010e030625090f03110a051206040b0a0b0d0212030f16020906010908030d0b03010f0c0c06110301050310020c030403 70
    0x1409080d86a44080c0150b8040400c110555280e5890441601d1044176001903a04141206034914090905001a540d010320800100c0152000c91803a003207100340c550444601c5141e0880b0b40b00c0031400c10b03188140340903140c41e101000d03499000f140c0c0503805041011080745000042031030440e0803501602210541d50100e004040c80042440e0b07446074174503107009460b050281088204c02ca92100425031820420011403590729002d01e44054003001c2c00110000c20a80c00d020740c1c074401900c00795090500c100104168a145000c0e4040b140c001504059075506c5960a2209400240429150034023060114802442a034070041002d50b03601b1100070540d420714010804004005042c0c0d90502002103420400c0100c0401910041c3c0c41e403050014800405001180c00b41c00043c1d0f8200d1551f1070007442c200705903080300c0d08006280c000d04080040c60746d09210411702e84003c0c010554580c4c8155208501d40d85143c0003040c80c024030b101030300d04050b0340b07030390b8045618039050b400388000c03030300d242034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456403714 1250 456402464 456402467
    0x50402150a020316170c0703030801050a0605121009111803060421140a0306090b010e060409090f02130b010206130308070f031b020c030d050c030405041806020f0a 72
    0x44121400d9040c040e280000d0404065600c3c4190103003542c001c0c103003034510414805410b6800e140c2c501028134950f83c60308400074068071242c0350700003140803461007000400c690410301c0702b000c150303002501c89915000307004c510803048400c010240e4449074010100031800b0111802007261030329103185030984460881550001d02c010010590303000754041010800030880100e06a0b41030501c0309070b40900c400090400310348102c04a00f80056000c00022100c040c6581a400301c0221007000c0b400f002560400c00045400b010030380620340d03201106100902c119401a401070f032110b03200b224801c900424590120f034031a07000b44e08cc684440e549000c100c1c150350b01417145581c410705012206011907100e43e800341c00c0900140021041200240d136400800307000e980001c4c1418000d081142154048140c02586c0f0303490781c0d404070302a004000307503145014000c00650341800c1020000d14102410601840003e10303500c040743c8440a651500840810a940700619002d124880c4c0340e035079a0303900d100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456404964 1250 456403714 456403729
    0x1020d0b180c090d14060105040b010f090e060301150b090316030c1401200a2f0409110901060201020301090b090c07060903200c040e010c021903120c03050402 70
    0x94040c01503604500d1909000290707080c4580c0040b01500e070580350340381c040100c0c21207000b218006041c00714100510950000001d1980e04070782084400740600001030300110b4991111030340e840003040c00300c1c00c140095891101c02070b81c0007402034000502c2d48003640f00024601260b44c04807102d1a4006450740040c203040c0041d200918080080a11146c80e59589030207100c614816550a080c09001080c1c240e84200d071a00c6104108a400c103403003002e2403a1090311603600010407201c50b4a04001582d80d071883d5000c1440c81492108840e041080000a21020340300c001d000f1140883c41103d1082d95030b81780d48415000c1c2c03010b94001612981840c103002e080301c0c4142c1856204800110801440250b480c00b1a0036082c0d020002056000c010316007595074085194036000001f41501314419074807030005006802c1a0100e40610043c910046c0060803520005055401600a021482c0208188280f0700a40903c240340205008031100d030f0001c100c440c0e58200d000066210001d0000758a440704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456406214 1250 456404964 456404981
    0x60f030f0304031a01080706020714040204030204060b03090c030c10031107050a081b0106140409060f0f1a04020307021e03370201060b0301051c02060a02030309060708010305070314030c0d0201020d 87
    0x104000da08020000c0d5840c54948110601c5492f681d00901013616650152002954050300611082c1d4483c0d080e40c03519001107503d45002e10580e180f4965a1500040e201401b843c0940040e0002008a03400c5014044c540c8090b100d2160802c5200009901045003409071800341d45460b442d00d2010042d40412a021071120015a040c0581400704580e41c180c108500310085500161240991401d84060107110b16040125460020401403551294120034105000414070041400b51602004100d0000f0b850704030050307104d014545130040041035401c2138031f030740b03c0c04890504c1d0441d5184480319010542e80200300d1481400c1f60031099140100350100b6225000038001103080000149050105102d05880750483c60a6103803900c281700d6411201030740103000b2581d181580031001e55a5030080d280d17409140300e024005030f0950301c541d164905a070b41c0b107800303498000d00e580c44509000340b00300707001052404200601c02d4040c1040162a00340c5104d50005612040994045421180d986 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456407464 1250 456406214 456406229
    0x108060117030324031605030c04020711010509180112170a0815010c060204030c05190812070c080a0c0f0b09090c0d020c060106030609051b03060f030f0304031a01 72
    0x10108007044001000b6203610100c0c05903208100c41d460b080e000c55100032800b103680c1501681e91664500c110141c0028199503007641120304014101c41030100b00e10511070043c203241c019a06d0604190300c21002011024001030029243c021200790801c102c0000fa4454055030640c1c91502c010019070032408000210100c3c4a18103107086002c01402d04030004003404401000c0881d61401680510505c0010315008541151580c4d164074107804440d106e4000c09100702038a90a88400d00008451a03040d0381c1140042e16540c00784e00f0041c1030796005100c080703a03103405000003c90301550803c000d0040d1401000001c40d0107281024542c400801c9402c45101c455041000107140c1e2241c044082c1c0012240c501c1554480000c1141d40c000d0140f180c17012170038001c41d400082d100e035040d0080426100d0425003004692105801114401590110b6400e032103428000620740d49000c1002502c0703440060f0640346c002c0604401c90b41181e020303800455010340102c444800300004005c00b03d0151540c3c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456408714 1250 456407464 456407489
    0xd05011d04050a030f05220906050a060504141813060c080618042d120813030e0307150c03090f0806040b1b0a0f120b090112050f030f0301080601 64
    0x25848842e1103d0b0406005000c3c030035040507040480e44518211124441c00c820300800341101c15821070303481035031845908030380c030308006010801b40307041d900c11000c88401e915254501b92604000007a50083d54010f25402071140e07031014041c03003880754624881e11480c500c01007800d01d05e1920104559550440400f004140c404015660f1600d40a4421403a084198072880d90303524a821503c4002c00304000c6107420001038200716203540008840743d01ca105d080b112401c0308150408850429046504807000010f4a0803400401e0040c40381100c3c0420140079030b4013007619183c0824502e030900044c540003c1601508509166001c4411006444c0001240c10f145152860b0070740c1d525005040078104241450204840a82c40107410070300459500880b6220b5132114030240c1035040c0c0008400104e80301c0402d20506010510854540c05402042a071850f420130009201e038050540c0104d4a51094820020f440c0c41c0070800780410b1428008603980c4c0b50305080d509070800b40183e00413a0342490 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456409964 1250 456408714 456408721
    0x30f0305090301180c0b0706110c0c0102150702060c0706150303120e010b06041a0d15050406080f0a060c0201140a06150903082203080c1507020c030c0405060103060b0d05011d 77
    0x501181100860f094001c1007600c0b8025400c100004202d5943c039024809e10000f1102403064000c50b00c040800426001d0b10349501b0030000300886108202c03111b4005030480c4002500c00c5c80144080c044080c0528400034480d21004a1450902120b810650114111400c113924180369400b50310b00340f5150030002d10001040b200400c00368022801407051074601c0054408101c10013400b85c503c1c80d186c40c002844035560b803e0f4100680d6803a4054030f0300560a08d000032402c13840005034a030729004500000d107030750302580e110007000b4580b44e88a10215500c40c81c0c00b00d840c4040c1d00c4114040d020105000840d1450050901c00200c3d00d45048014024400c0c41000800d4508068510701d00c03980d02402d0044804140322125806940c00c01013123544040b1300340d942524006690740a9400c01e140d5403000d030300c400c141642d07600d80030b410035549030740318241c00c1d501170910750080da80080060502144041e2101c82c0200356820005620103445c0c1c0d0380303004010751047d0040d00c40305100e184400d02e45604 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456411214 1250 456409964 456409973
    0x4021305091014240708070b06040c08130219060e1305071b06110403030f0f02010e0304050118090507020d12060506070809012102040302030705060a022104030f030509030118 77
    0x314254600c10f10b030780212168148413070071080d030200c0a1042007640d20086468400c00c5a007110f4000e03a80a414000090018281071055000e0390390182c03a080c109540c0c00005490060100f1012070f0800304042039082503004c07844001001d04401d403141c240b80c4107064140300100041044651106081105104050390803548401c140c504580450707860140b5410160301504032030034968040c4000003400403d03d5405a0318440501c40780d0744030110410080c1040742079072000d102440240e04200004c204944c000c02c0d2044020300b9070040c1b650001e5461241504441e001c60310400544c01219100c90b5183d8810b0340d02240040341c840400c0407906040c0810068020350780e008101a02c0082c50700000d80c040e107441002c0d031182002045c00d080c1c64041000181d000752008038002e220300340011405180900584005200d964014414001d528002400b00ca6041074a5400f14170208008008241350b08807020b42c40d40a82c4400360380d9181c000526086442c01303030b80d9420030040c45101c1c40005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456412464 1250 456411214 456411239
    0x6180c030109121b02060a0e121209011d09070906090b12010b0a025823070614060409020a0605030720061e040f20040213050910 57
    0x70f22481c12010140140c1444001002140406540070b1004181c0c0914590300c4203210b0200c04003501d404400c042d46000c00b40e85d0b40070400c10704142c2c00e400d0080981170f5104135140040111960305001c2d03107401c82d40201d8403802c0d06a625100294080c1d070144170079500b001840780184110b48485281ca426039a000048107018050f209112200140da40c07100d0303100304400c0217522054006403110300800c84500308c070080c1c403051441121024aa0280e501c419541c502000b9002000809424039040002101c00d1044189550b40240194100c01c582007009009480b245118039030014103c0c4c5c0c00d4203843c900c600700502e518031841c180103101c0c0068550b5902d6208031a01814144c0d16500c40c02c800781e40e41f00c3d104e00c03000da554130028004041c14200260850040c10745054800803e0103941080c0c90594084401504010300c01034104002017015109d6810808100e0b040d403000c0c06500c00081c140d90003004084030300c80c1c0100702031050740740c01d5034090740009041802681302e0b45002d03400e1294 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456413714 1250 456412464 456412493
    0x501300204051302041401081e041a0a2702030601140301090503070515060d050a020d140a03031a0108041a0c0d020c0f010507110a1b0308040e0f01050a030803010b09030c0306180c030109 82
    0x80c04001c0e0042410405c4283c4a4192030303882d0310b040c14252033300074500801056200d030340c02404640e628052070314401451520218a0700500a041c95038241544140c101c1e44002c0e00030341540d62400c450b40412418005407075030500c180050440d440c14240b4802d020f010140516220f50041480c0b000000c000207103605803680e040e1421b03444a1821b0030318044500150390726070a1409104080c00c10594144e004a8042d140a01c0403101d0200e0f4400440f07144030125802016400d141d8103014031117140c0d006099001aa5494691400c200e681058060340c2000001050583c407440030101c0c40c850070302540707a0090315454202d2014265401003580e803030100c00c2c05401c107062400304456444000d03071604003540e0002c0e04650380b96524a11440c200d1000c50b05400c0503400c04002091520700714002d00100c1e500440030030704590805032541503d510002e0800ea03d40b098542c49001524103201c12480341908900009141c502e1035030103410810480e800c94402c6c4d01d404c0ca10340004580c2000030f0300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456414964 1250 456413714 456413761
    0x803100f0e07030b010c12023f07080c0a0b06091605090d140a050d1101020406020307030806060706110c21120702030c01050405010213050130020405130204140108 72
    0x3d01055140051b24240d00f4503002411209204001d1095603800080c40010f800e60400e002402c10703e90f00c06d00c44c1c1c02a0751f42148043c450681c07245154212440c01400045002d507440914100c0c1116070310345000511042207981d042c0780350802c42980f4114070300036807000d41e08010401607110b22a00518500c01e001390340d03108018a2000da400d111100e040010704030b001a080390794044240c10328941c0e070092010707000e0006880c8503034088040018020781d0106d4060f80c004604042055800380c035001c60042000c1d80209050003540081400c42c021812164450744000395103406600900d8201081580c103110814498045110042d106104440c040c03094100e40c1da0094a40b4807003241544100b040304409582000300740400d101307040d4010480d41000d1401d01c903d141c1d441c03005540d0561964522a0703a14140328400810a901113a40041000590401454180c4500001d005d0020103038072296000d502082c00d2020003c0c6c0c030a10b640510382400c1006c4285000400c0085000c001200c012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456416214 1250 456414964 456414971
    0x3030b040b030d1d0301061e1d0a09031e031e02090d02090601170a060504140f1504060b07030801031502030f011a07060c0e1807021207080f03040803100f0e0703 71
    0x92403100704130014229080c010024094656900216009041d640240300034040c12604002030625801b141d1040d207007000e01c140142035860106010090244507020741c01d0140c03404901002006085c0402c18801541c3c40010b05c1040c040811260120f0301d14402800f1403040240c412959520b07405000b103260b04030b0f0307680410f0351124012030f0791a01d900450391a46403801e040c41100c84181e04010b080c0d800c25581008543d42260b80c88603211000c0e15001c0320074035040007003682010b000190180085019001107402a504c0c000c20480754030000301540091300100c014030800290403c8003083c6100c0f07000c1541182014010244112010303c109180ca240c0c1c8810000c40c3c5c0004000d940c565034001d04204086258984041d00c100b41075180c6a1250000b1080c1c02c4c0d0000d01134000c00d025140c2da600811000700340c0340c402c03c4a81d01540701507506103818880301640ba05100000c0d44154881d012442c0c40f410211100c03850718606400c2a40c01c00d01e0380790706001c41114100310700d620001070718010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456417464 1250 456416214 456416237
    0x317150409060b06030103031d09070f05030406060b0307030f0509010e1906061a030402010f084005031306030603050d080a0f0911030c0a05030a0206030c040e0a050403030b040b030d 80
    0xc00100a407030f6496800c144044000810700d078201a040108900004040701d0b08400001001030030365040313840f2400310340071203118600c40d44903c02450707106100c0c040000e095510703008691803036001201e55100098440100c07e008020a0007516045184440203000040400001a481d0383c03803c0c03240d50003c8040c050403800e000b501d41120004084009080d13000c14410120318000764012034099000ca259002110340ba1407051001c144185d822510302c0107a484007c8520415401302401d6500d00744001c801100004101401d80e60080d10420043d0741d03803043c900030f00c08840003651280003894030f849800c1020600109200c05040310f60b01e0039680958401d00d200c0c000b410400d223290074462620001c2002c000d94803c41d00c6001000302c04450f1800f00c94010003e4080c051300940d90160810410b60b0018202070780616007100a200c0c245041c240c031a40503201520003160740565081d02d400a02c000e040d003600c12141c0a900c103a9090011074161008281c0d50800e0313610820400003182c0c0c05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456418714 1250 456417464 456417473
    0x103150e15070201020a08010501020604170f0d0e0c12120403060c1407050a0b100b090603060d0218040312020f0306091504090b040c08030c0d0e0a0906080a0317150409 74
    0x104801c0c6072000008004508042c68004c0c000d401401480c2c000c030b03825100104a0750700000c1c115201d19880901056600c1c100b111200d05038100c0207028490190500c000d480002c818001c000d40c1c0380c40c0d10f0003032041020810820000e404c0302500208503030449503034040c08100341e10442c0c2c250394009001064002d4841400c0743c007661f84101580355103401146d00001c0042c0410300010710b9015041d010b0300c1d07864422018010b89c0491081c411008170402644c140c0781020009150f0100c1c00520503400002240c021031a0f00804070102c1107901482000c100c10980c00190116100f40ba441045041c030729250304170f12542c070002d044107124030300d070394006000a0001001204440000350040c0320a1a05180c44089031800303407400c031049201c010010070604400000c0e40d540d483e04400030606007da80205890300041e02c400c0795002020500003040340005c034003501c0014015840100402d11040c14010024001c120258000c41c6002050001c2111080014482c0300d00448000846101600c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456419964 1250 456418714 456418723
    0x12080901090314060703150609030303090614090f01060911040e060a080313140612010308072f010f11070b0a09080712050712020901032301060314010f050103150e 72
    0x100020f1044015000c105000305050b070040e2034584080c0702e840c82c03800c1c0c42c00d410001d40c0581c03000294103250400c00700e4480c1e0402000a4080c0c80001070340c0c0d00c00004220403c400700d0703800d200b592001d80621588442403049500400a0030020410028011620f01c424850381c80390141c0c809400d000700342d665a8850140009105100c1220b964400c044500000c6000301e106101058000d111061310505210f000c6401180529500031a160709560304d10b8125000220180e071004200c00da1061031002450040e40c0954007800003080d9440f203140011b180b946241c2c902002c208034002c4891680b14000350800c2a1014907403805d45482001c40225508051640a141c0c10f1042c5140000c69600039038a1001d198007900685543d0740c1c94000d80c2d80c40c40030700d00000b50011010001040444c460341d08084009200c041d0f42c003451883c1140076425540b183e04240ca8801181010b2520040244a44030729140502d8040c811585582c6400384401d800c0c9021440058460109000c0d0504c01d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456421214 1250 456419964 456419969
    0x90b07080403021512041b0501021203010308030714040807030b07030b0f01050a0c020604030605010501110d1e0309050d02150604060602070b030c130f06030c110c12211809011208090109 82
    0x80c02041c17240b5180c00d12454902c4001952480407403400d4021a0340e502c04078194041e04441641245140d20356a207070200c50303000902e02c100304103101c0d0040903040c0c50480180300403c0c0c0c10000346590ba007907003003d8458000c050240070074540307880d18005d8a81c440452a0051000900b03245494640e01081500c2c0d07495803241c0254032082c0020040208000c40c0c1c402c0f41600d000380e03203050342086042d202d260359601c401c000d88081950f1064003405401041c205043d5140750380b81c04100c0241586c0c4091810004140741800360300001980d1031440551680c2d43e500180403241401803d107420406501c904042c0228100c50b2400000100c0011020080b581c542414002d10b00407140c5da401415003040b014095200000d003004400c0c0e0b4640d114548030909901d10801805540b24247c0030081d000c0c5450030040c882e405080010400300c00c0180020102c030403010301081d0348203842c0854031075021416013124800e40c0c0341c00051002d10004466500003130b611101c0b085e5500c48620042c1d030f48250b160b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456422464 1250 456421214 456421237
    0x40506040e040b0a050601050d0b010504090207051b031609020304111507030e0901061b030903050715020c0d0c30060e06060103090b0a2307050406090b070804030215 73
    0x14000074000c45198000340300301d0244070b0006071501d80242c804180c4105407513890010710144145804101194000d02e051603050418602d0140d403010020280d070000e0106075400d412206141c132040c4c0b941d8111407124182100a03142081101050107000b000c40d0141070805a07000c0000b800700803005180028190b8002c05216002c0d0040034400c400d40d004c59401c500003180e112840e040c50070700640d00e9050350b2280d01c0300701c0090144134441080d0b882041c01a02084200040040400e4003407080c00041c004d04004140050b040070f0f80070f8a840b2240389018054001842c65a0110b550891800c041e1503002d59180e02080c00020340c0128191601040d50304040031075040c0c4200607880d484121803482c28010b0f160180e503044015000c403510440702501000c042400103100201c03551042803801090324980d62003449030b2003112500001100e070310b0007181d4009414030600303801c109520000d05040300401c1c600803180d038611605021b20702c002800307074050608440d00751a035501520b80c0b00110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456423714 1250 456422464 456422467
    0x9020c0a081b0706030b0d020d02031509061803040f3605010e09030a080a0f0e0105430e0d02040504031205010f0501020a0f0c1212030605060304150f02040506 70
    0x103601c1d120b0769a001014440728144650303400016054068005c00d41c02c10002480240101c0e40354081c442446600c040c12a40350080640e003c220b1880b54031800c0c0509410030040c4500c1c0b40c20207840240340031361310800e0bc0030780c0f052108000e84031728440542c040d600c0f8280c0900d20301c81041550300303210302c81001255021030403607a402c0c01c2c191642d218a0403030707140e40c082d0641504c0b81000503490780300d003240d40c1d000520068000b030307000103068000c0040407d07404400a0740000914207207084400a84074481007025a00d0041c440030320328000a0b4641d680c100c20320320021403c2e4081140c5c44000ca100e034092007545845060203075181c001000c00d050b005002800645840d2900130900d420014221481034507010020420310011407244083d0f60044c0c0042102c0702d9192603801040d180c0b05012294104030800108480409840404025114135a0000c0c0003501040141c1650741c50740201d80640c2043c8100302c080b82c0b0741c095040d4900ea591500262010031068141c1c041d02c101e030000c80c0c00000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456424964 1250 456423714 456423727
    0x3140c12030d0506010c200a09090c0311030d200304090f0f150b09041802040c0215090c06091017130b010e01050609090705160f050f070605030109020c0a08 69
    0x4000c80104a0807030900b00030840f959a0200540d10b610303455501170904038400000000f0500d4445001980c46801094031511554404580b01511020712080310b0036500e0900c1003041281f20f06210845290881c0900008405e0110003000c403d144101c88a010484c1c05409607129018022100a014044004e101c0c00c014180c440c0003a101615021410300c0c40c203060812012954032002041d101e150b86c9051414101000b008060200100d160344209031241300103006036038501c14192500d40c55009000d0341540804d2070b240d8440000d2801d40c003a0403400c59030b0b100341d44841c01c60b29010011035440e024612003034411505d91600002d50003442003150700b80b01352a07110613416181103210340c030000180c0e03884840f20700c20010b0a01c02e02e070b00b203842404106094a845800203a00100c03e2800a061858503064070091601d00c0b0030554104540800c02028402e0620501d502c0301c4010000300013681ca000305c01000c3d4403051103032180e1603601040003000c601e000c1c40f180b0a0503402030710040d140d01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456426214 1250 456424964 456424999
    0x503120f0c06010e04110d050601090c1b030c0318030f061a030a03082707060c021206010b07200d0624030b150306010609152a060f0e030403140c 64
    0xc02500c054a00c00f4107140803030341c140341007d084103020743e000c0c010340b065910301068040580044501402445817658284400c02d20008031000218020380d80c481341e0a0f91070901a1055925405c542060b080820b021710100d03161595074107205910260000320390b1042c69480949100030314140e5414041c0740d1060040c584e21030840b6004a00100b40d5007e8107944900f40d500400301c1c140040040e801c12036003004024020418000446d001403d5149550030080c2c0319801c0100903009a6604080810684203001c00080304121010501c906201910401c40000780b40f010131400003000c0d5a00c0b414074003c01c04200d0180e035900d05032003101011b603944919141540c1413044800102402143c8852516032800040c40c038100d405c540c940d014110704042c1c010303001510801440c010710144203500d112236018510b408405150034140310f101d50b140c0740b0f1303c0c209440c0d40080740440242410030007090340d03002100b141c00716a4012940541605420410360408451091940d03120000003156809031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456427464 1250 456426214 456426239
    0x1403031015030c08060907140c0624030a0605090c0402181008010b0403030c0c0f090906060e10180e0303130611130905060a0503030d240503120f0c0601 67
    0x5030a826001c400c4081146802c808480c00b020180c030024059101046850412568003908440342c7d160100c41140881c0381c050b120780c8905150410750b4007510401c507450f0b12802c1856124124070380c46000036029040001d0740c5420200c4e001e801c09a50744041384c00080100683c0b01c445502030803d64540c2510b000134011207a50600d91402400f40c40508008103200381e1251b4161340001401500303190840d10200c540480701d0320200c880b808501c4020031108200201c000040002c05008107600e5082d14114007580c405134803040d00e03410b1400c00d02c00481480d000b103005480381400070f41c00d10101c00c094440030f40080921495540400414030140c8102c920410405a02600b400d00400d031100d041c2c0c00c1e03d446424010070014a030020f0620807410386030031039a04000001d00103100280c03a80300103811a400080c4150759643e56210700550940003a044c0107a8034500c80b80c0c00c214500e000040790321407101c0c1c00a282c50b80800075403250349461100a9885004020701110f21541e105c031066640c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456428714 1250 456427464 456427469
    0xf044106210c09040510030c0608040609060510090e07050102030a11012306090f01051c0201110d18050d0c0b03090a140705010306170c0f030c130c14070b010b0714030310 75
    0xc4c2e810a8009152003015800c240c00f2030b503100030750000d1580307000c4044403840c4019100b00c40c000c2d00c0e0115980414058001d80c0e014002c0c0050800b0481d00c0d0968100480d0f01d0800092030035000740f003003003000381e8010003550b41c20482410010b240c118103e0f4694010a008500e80e01f40c41d002400c051550b03010540c415204840680d03000711076482d40c510940d8048403d1244540c405500001403181c0301c1c2c440e020902c0c803481810456085004100d1b00c2c0c1c140040003e2480000d41480f151352604000c0c1c0c0003280080070180d4221400700c1c41038881d2000012030b40a6040c00b0003000011400d090740030000a00c2d41071300201c00d50740ca822101c801c3d6898606910685000900b04200881c80c000f24031060307004041e80000030f00c05034052105211400b0010031005a160150b00101c01140d10345010310460b1028101c0c000034080b00c0c1102c050803080010400c040880001c2c0301c5280060419540c00d41076070a070f4400c00d170b1201803c1c81c1c98404040315200302c00c0d650001100384058a02038008000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456429964 1250 456428714 456428719
    0x18020c0d050310030f020a080a060515040e0309061b030403080c01060b160b0402060f07060b10020a0b0414010209130b01030f11070b0603030f044106210c09 69
    0x10180e202540031280340c081501c90300d56040e45000100f0004151590100009101409000015617601469030030480007413000e0700c5c020380b59010404007030f0014000c0c003010303001120100004020005410364030f00540c8a45401b0f42c000103941700c01c404450940800000d0880c041320703540d64891401c10025001500d50008941c2404000310740044080305030b51000d10080f50b90343c1c16407081d807140c50304000c0103841a030700710100300520465150030390300400d00310b40555800302d2080107080500c0000090f1059140454100000c2c51002801e0703c091180c0054010701000303500e60507119000d0080c8280d000341c60b40004d548412100c0c940107508100103010098804100f0034150700c5144058400c030074000e030078001e01002284000780c041c030040c54100c100a42264289081c16001c030b240e40d806a00005036a03540e04c0c00305100c5c500100c2c42c1c026002c0713950010105c070000f031411200001602e071801c00e210781d40124016004040e542408249941c4e20075201c49a0b00f02041400900c1c1d1200c49400d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456431214 1250 456429964 456429973
    0x50d1202011a0d0818040c03060f1202090f101d04060b03010b010f0f1205040803040b1305062e090203160306030c05010c0c1e0e070e030601150918020c 67
    0x481c0e44000c0800d00b00e507200c0686500c0c0001983c1c0c1c1d0700103244c1e02084100c0c0365460710400202d5580c44502c100310b02101c141e24001815400e20100b00b80b00355581e800b0b5250031124a4807107006858911410380c00c1800c15200e03030042c1d103602984220400710303900508103282042e000101c41c40c2c80041c2c1c07070780524012081042083c0e074050900d402e81e00a0307115180030a10601d20300014a1203a4500010900b0903e000e0805180704030f242d10a0710010b4400380c3d0b41c04004400e100c00e20100510441e040186440c240a0301e10041c0c0c1c07502c0d21101c0040c407241c2041c520700040b1703a900c04900b0090801320203280300e064243ea2500440002504143c032081d41d00d0b1349061103aa00d09001b4411401540e07041030141c1105480c0000449140304001000c03030f918642881e00154168034041031620070141e58802c0d40d000c0b03082c41c420115011008001104208400c1c66040712510003280e52815071f451081e02d4400c070383c017441081d1007104155000014005812071541268a01075010300192484a41600e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456432464 1250 456431214 456431231
    0x80a0b0d0c05090903040f0909030809150a020906041205070e09210f0f0a0203030402180f0f04021f0c050c0d0b07030906090c0303020606010809060714070c050d120201 74
    0xc034a461440c8002048211420000d000034905400c50340d501070308520860745400e0300c400350744000385400c3d4048103150b2384400752002090f0704a009550b2141c6880c00510019003415001940340e01c0c0070300084521940000e004259840b28411074001d00702c2021010010030781440c01c107903136448604c514010b0342545d5001c104030400101d1810115081c0300b0026207444c4d01c00c81c2d03a01d00b0364482c3c0c0c0590480c400c00c10684e111404000301401030311603560080c61b101d2415005004c0302105402604d4043c0c1c40003010407103c03110126000e80c020002020865a40da1284081082108403941402501103c4070b215101140d02100b803134809031181f025030780009940c0040c8144341d42440c1004100c8161640051780852007030340701c80780fa203024041c00f2602d05104e031a03c02981d03036940c0044d07005030443c008101d12540c10482007500301e800640200254035003600b0080c444141040e42c0030010070006032403000c0c4520856103074042c080003840074020005614040500c0d2845009050165081c44000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456433714 1250 456432464 456432469
    0x30f03270b0d0e0c030d0504090608030a050d0c030b0a120c120c0608040c030813080c0109081b060d1406030615010e060304020d0c060201050a11190507080c030a080a0b 74
    0x50303080300c5404002904002d010030105003d0000a900a4498400c10b24031318503e541c1040318240301c00b041d40350749070b80e54185140b03107081d44c000f0380103601207a004101d5403021903031010448590a0740c400c00000c500c84000000c5028001001e4115440803c4d800701080340004c0046101d0654820040f00c0b403115581d14000b400c0800303c84000e0032640c0c01c0501000100d000d0700305103a00c6032054441d109210380780d0b070b10110309801201010468203907081080c08980320030010843d04075024207000c00340a20300500c0c01c0d82c0700c40c0340c05041c58100320008410201e498a8007a00d051010b0074209110980500b4028401480b00301c13030991191043c203003c2640041140c0c080010500181d580c800c0b000c01c03900903c05d40c0c0d0300281003240c110300d8102d00300b4045082c4551080c083d00d090b50010402d400c01142030300035104040915404044100100314035813030500c02c019003803a00c90030b00c280c40e9161400d001004ac002c00c1e940030014080003901105482d4000141031080f0a018003c00000510005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456434964 1250 456433714 456433787
    0x18080a110c0901032d050105070e0f031002090103020c100b0a17030f03070516030206060108090f0c0913080c1f09030819020c010608060405060a02030c0417010204030f03 75
    0x450b00442d40d840180082844001100384d503038140300d41d220151208009a10103007103907010036189a59640706001c612070340004500344012040320031320545861040002c0c0c031003a0303024113410481e5001070109883d0b4029010f403420661110290340d40e0480f2444082c0c00f41101d66103261090010500c081240c00c0c40151a000c5100c0c024011030800c0c19080b00a0503d5201500000900c40d081c8454000a031540d1038099425110b0390160503182405000540654000340c0210302c950007044418008510020b110802400c04540c81c000030b0300c40916040c0e90410054001e0005c0400041c94031580d200080c4954400000b810208101040d41060a003204c6c00494010b0020b05c072038011076100490031105890020303900d24010b1034000503040d414211812135102c0007050300b020702080140704051266030b40c403252001040d80303503107890b10046c40d00307104e180116103e000d120080c98081a0302503055501550303102e090601100c51a00f0040d050800d400c040108c4105005e61000c0c1c0d14034400d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456436214 1250 456434964 456434983
    0x108180f07032a0e0408160807110616020d020f041506021c0e01081510020109020306060d0c05060313080a0509030c0307030b18120a08060310050105030c1318080a11 73
    0xc4580402404e00c03084e501d060a010784180da0b814014802e81c81400c00e03d05281c9034080c824045c03142d50f05400c0c9803441002102410203480b50400740708105a000d0103041e204841c583c111744000300d034201e0b8400200d10700c4200c050580c0042c0b405440c4c82a07205842240c03410b07540541c0886140c0205098000d0828880d65840000110703061404646540035440194100c0315130021001c1d0603004501007516644410100c40040c0e440700000360940c06c0502c0100c1d0401c006480940143c01c0580700e015101d0000c3c071406000d0140040000c09400382c480c0c0040d01e080c0d120304190368a2000031401090741c1c00510b002417090180c9005030009280c0015801f0449601c00c4208090b0f50303910340700d00b88807585000d42c0441c9004035003039000c03850210001003517012096160917070542014018180b42c0a8050018900c00749420018415507030009941581c880c1c0c2290301fa03c110042030914400790000d8021b2159401101e5040402c0100c9400a4083e0091326900e01c00610b8220742801c0c0e9030070a00b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456437464 1250 456436214 456436283
    0xf02070645170c0a05030915090901030308130803070306061103031603020a090f230904050a02040506040f050403120c05040b0711030f030a0305010e0601080103020f0108180f0703 79
    0x1460001c0000b040500919002021854142d050444102c00d2500701110110104c03015040010014160326100c0717a10621040003c8000d410001c18801003510a00b0600010b82480140c000255400030300200041c0e10580c01501c498a9042a84c1c01070040c000602a402c046901029210320117500041620312400e55882803540601c0381031401e6000390300c1103800c0010807005401c0480c0d00c521fa2a03217140242040d8030301d1b002d840c08440c40b0140c004403940030b01b40b0035080c0b501403002089000400c000e51a80440300020607449860004d402408400041d5140a04040401041c1a003101940454141114081c00160110801100d5034451750150010b01d480901181022683c00e1144444848000d0102c80030348089081982c995003003150f19200107601d480050005940310b00180d030308407100307080c0003103d54115400a07000916045070a410042d21400092013040351503a220703801908070082ea1142c01c2008200da4a070061400191600340800804141488004050b00381001b140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456438714 1250 456437464 456437591
    0xa0203090415080d020309210a1104150806040302161208030a09050601080d030609090206031801090b0712050907030b0601080414240610120f020706 66
    0x100030401c001841900c103001850380d02180b01041c0c9100030804919641e91903002551900000c004002c115441010b01001c8a0348401c6284070b013040004403412520790040001d0000c0483e04089001854a14420030421552450002c2c110202107126805207001c1c0d404e9594013140c54004220300c40080c40b440c5481c007184102c100102c0c00c90406150803a5590b000401c0c00110340d210145440da00fa044001c0607041031080150713881d01031050340e005114003d82449001030a40002c0d940307000080075220907410729651130052041c01c1d4000200903074000241c07140c504040100030300d0b000130200e140070318034500004121200400076803802101d910444200f01da664880046404a2003d40112500303880d030711104d10030040c10301603c520030054607641c6021520a10b00616010409811107001d2400320031070248281d03010019900c40642d1600100f100d0b000401d40d04000d1150702e1000d41081d140040d4032403030346030480800d94507000c0358070082540707902c015003207000251050208081a07007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456439964 1250 456438714 456438727
    0x4060609091409120f0f12010501020709140a0e1f061809050a0303020702060c0604030807120b090a0e03090d0c05030106051e1c05060703090c08071206180f150b060a0203 75
    0x13a094003c004030602c00c00014102004601c2e4010785801002040041c4140d210040c4603179641081204002c00c0c049800b4460011001c03d148010000074100030307025901c8852034903e03802c041040140400c0c110f081d0400c0103000051001c01451075000300520000064208010301c100c074001c60003166000005420350410680d010360003075010300b60813a0444410310004c410b082003400014401c2e03010341c6403080c2500d0070324001032110303100c80900141d281c41c1181c072408035100d1688040c5e1081c86828001807200c20016000e181d4010029601d50000420002508020041d84811708555080e802030050984030800c12003800c0c411042100c030106105440101454200b030090000342411050b400b003c441511042e04008003142c422001c25168406541080458030700035000705480c0c2d0140410b54207142c130b00a1a048080c4001e0406500c0300c41425003600742c210300d940d01c1076001d000c075101041c5510f04022120070854a13400014a4400700306040d08201c41298003080039540a145083d6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456441214 1250 456439964 456439993
    0xc1505010905090a03023409140a0204030f02130222031208010513020906040b0d1508010606051605032b0606030902011403070306030206161e020d0b0702030904060609091409 77
    0x114050b05880c2d114804484840f0b80540d0b001c1f650014020921000c100c40c1c101c0440c00e6810000030784020000c43c0304101c100f003c036060959280001c0d038112000e41d0800013110821001c0d000f00d5a04442c0e8141080306d44564820301980041103900c9030424103445c030420581900c03550801d03c6095008071060700100002904d65006081c015002020355003000e0305d4500a0174160040c2540710300c1c1c5552151900c00000182e03140c0402801c3c100e009208190410384001e0150003000c141c8d805240b2a081c40508100d4180141d50040c41003140306500e00700300d0525440ca04141030f1f02107210a14100c030105015100707014810036642c068581c11708001c108018810035910007031240c02050342c0c82030044010303070380c40c0e005101d06a41c056964007060502d0401820240c20201003000b1210080070700300040e00e40e10954290719810110543c41c1d9a00c20358280e0075441041c4080d0ba00500d002c201180064008120000b56840c050082060361100c076159040d4800c20f40390143c06030321146040c110320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456442464 1250 456441214 456441253
    0x70201060f090903140d0e0303040c0e1506040b0a0509151215090106050703120c0518030321060a0305060109020415020c031f02040e2d13020d02010c1505010905090a0302 75
    0x8006d42400106e8840c240c1c0c4072420750f0016281115194a1840104018202d13850b440383c012152040c1c1507034070054840024507030302c42c034810480804000b03d403601015001c1d03420340310703d0000030b00000380c126034400f015601c1d1b6004554031281c405158001ca40201881c010b8100f11000107001d55449908118050340c40c0e402481003201082160204c10308042654000e8100c455071586641c0d03200c2055a05652a003118205030900a50050108031100d81d4480c80c01031240241624a10321764481c2c0c8041004070300c0ca500040c0440c814840001407443c1c407030380103100703c0380980c911140f5041d610404a80b282d03024822141c0c551301c008401c514400d050600c0b203219200044005242540d5955004420082241d404280e40c250b08098440075014558031200110b68554002d01407504810540701d441640b600607004401c06071103602164054020301502d15002030489440d0324180a180300a4078090080328400c5051501098451400048240c0100d915030003801c3e11618800e180d0400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456443714 1250 456442464 456442477
    0xa1109030c102703050d050a0e01050d1b0804031e020606060d110c0a0302060105040504030c060f06050d0507080d030903080406020f0412060207021002030c0a060b0f100909051b180315070201060f09090314 90
    0x1c92351440380c0d5480c1044580301003c0d441ba65100c01d0ed0714a01400c002d04a0105807066008840d080500304420541c08502e00b40d002d84100c551548a111154402c001070401100c0e4200c55140094104250311001800c403030756500c071740d0031121b4903031700c1d44240016214107a5000300030036040210400061000e40125842c01681000000c20035668000500380c40c0d0b1650301036849070440fa85c24400410300348000c1140c941541400c0c009610030342e900510507000104007420069001c2940a0a10b044100300d800414801c54020848105401c00c0c00003503120180403440342c0c0030300300c10304040c5002000361a9004007200c05000300e50210f854a401400380d00c050194070082d02d0701410410783c3c41d220b091012804c10750750414000c0c1014030900445202811320300c1070340304008284070300c0100901100c800041c006a09002c44e01c480011a142060a90403900055103410800401603415400713881101c500b480c1c90804107a84e0f000800454503210006030000e00f80d00300400c81141d985006082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456444964 1250 456443714 456443737
    0xb04050f0603060d0606181d03030601051e1b0105092b030e0f01150f03150c020307021f0f08160c2103050a1109030c102703050d050a0e0105 62
    0x10b1301c00d1540d45650499105802c494901d41c102114850950814859920b1503088c0451449682c441c000809942340001030401c1d04100c0300050a0000c0944004014800480c0e0590366848281a003000c050038422420103034610340c641400500840c00020f4192071031807143c03180600d29008a515100b040700c21900d030383e052503210000d40072030101c00c106031103400d54490000203031002c2c10704000720052010391001108002940050000c07980d61100407489071082100002c50901070241a41940a04a000395000c0c00010664562003414020440d81402c1e594400c003000354502c0040e100c82c84140c071200840b0072880a200101800b0303414051901d80200b40309a11a1000c076103a070068459451003e00003a258424003001031780d54000d244540c2c0540348150300f03245041000c40c2e62041e202103041d1149000d0003100240030300841c1d035003500b04e00c10348480800c00881d00200350340740301d1071104684a00c907904100020b82c0c8204c0c156400082180e860314942e440c9840111480e4000942842 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456446214 1250 456444964 456444979
    0xc21030f2c15030915070f30091103060a11030609040507150e090c0403080a120e0a140601090b0d0f02010315030308040c0b0c0d1421100b04050f060306 67
    0x2a03542100b032001e540718142180080c80210900050032009000240c544070500c00d01e0504941525003103251071110710785030311034108000e5420400340c0d0009410420020300c186415096800d05c0202c001804031180241c041ba40c03903440311a00d40081301e220201440900f001400821800d02d854010180c005000c1c00c100c80701103881e4a5484285220b000071000820700580305943d8505160030074030b038010342c0c0f003244c181003626588036a443e030300c507101c0101c0800c2001002c108441401d64040c600920745030044504214036880e00d880101c1d9081c0008400b442688000654200b40d400307201c0e0590400760140e020210035a403a1024100e401d0030803414541c0300d414440e40ca03411111090001d501907a03031a509401c00c1c0c1401014582d05400c0030300180b0040141c8d007441d0400044c0c114034000d4614041030600c0100c500314455004500e00b0328030355849201c402c0c510078a404d583c58050010521030394062540c0e688110054802d40c45680c2e00499909014bd60514240340038660000c005000c41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456447464 1250 456446214 456446239
    0x209040e0304061707090303050d021e0c030d15050a03020d05010f05040f021206060109150e1806031920060c0601030503030106030b0301020304050601120c21030f2c 73
    0x181c15500a0340103503001544203528140c0302136281c404550440e0071400c20300e101c2400d540b8011f00d188200350395901c2094000440440c10646140101052600c2c0060247c07a4440c3d01d44980d2203034420800013039064200441d40c080c151058075070030200d03100285040716103480c603400d20041c15421081a00c0f20755a0f4041c0394086107030360140c103104620402401c0d01c0d6890710720410040e210841c00c0b00740261302040030415240d030840f0081c410f072244051a84da08440c10b400071203d642403143d946401c809150300b8625142080308000340036207021415541c2c541c14540c00115688024003005c3c0006000300008207490f03102c44541080c0003000b0304001c0c90451100c1195141490a070320031100c0b903100100401585034107119244001600710002d502e03505040d12520380e104018041c002d07081c5002c03007001d0104a818103106006010b40c1340108500104004100038880c100d0409802140103200b441d4101d51140c6d4a2450100c031181c10580d5861041e0154003034040840000740c0c00c019443c0a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456448714 1250 456447464 456447491
    0x90302070e01030f120f140913020d0902040c051309110408010c0207030b0c040320011115041109010e150102010b030703060902041410030b070c120e0a0e070210020904 74
    0x10714041c1d800b500d4084d80460051401d002000300d0201c0c9281084901405c81003210f901244452001d0860500c00b43c54038002000070300691795a603c0b40c0314142c400200880040c1c40c45e003042c00132600840d01000800250807003603490744038401e005080b0b0744d4184000d000002440d8401d03202d0500c241001402c0540742c03900f482c2154a80240c000240e44508010810080c141400030750200d13440a2a13810940380d6502c104841c20103182040308620600030a00031648a005420454000310084800703080c0c071503800d1410600d013503d040c0e900a6159400c1c95440c28580c08040c103e904642c0404a0341e91403c480f515000b60145035541195221140000f065030108503c2c07000d1030142c0000207200c082841003108651000007407080d0222203008201000c0101e030842c508403900034080d0803442d0f984080880780e2409034440200f400060355007030000039a00104000050405072010082075441308000c440054003241c0e49001644032000d011305111260300a0108068040c0001c034012030403500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456449964 1250 456448714 456448739
    0xc130509070804150c0f030b152106040b01090512070509071106010504060501020307170f0d0617070806060120030408030a1205010b0708090d1401020c0c0306010e0a09030207 77
    0x207050300040c241c00284010300c050700c0b000000307445022404000207410381c2d0024100d507403925000004e0664907440c0d0040c035200e070b004841c0e850103e4210301380e43d0034500c00340e4850609140494110406003200080c0d0b217040c180308011680c2d00c16120700390384601d890b003004113030110810f19540c0e50248a1000610ba11940603050044001d030300c40c00380401c4010642490208140d10283c4590b003411000c21650b40c020003202c005c160400f154580074207510041c80460b220b1032103265a4200d0006403030300c540e403082c0d00c1002601d07400c8101d07188003400c401406a0700c1c28540074650807604924013007135235507001e2444040500442c1390041d0882e0700d0041c105045410035400340341c1d01d4200150442002e680305424000d0011020001c015a504102c144051030192403c003e145410001e241c91181e0754026205502c5c0754041c0322440562010b000481c040e400030405090544100301c0403085518021403041d058030340b13008500c9010b42d5102c2c2031101a050f03040b4103a0941c0514507010074038801c0c141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456451214 1250 456449964 456449971
    0xc12020711100f170f15011b15061e090c021f0e0f0604031d01030209060307020c01110a03140304141501060906030501060804020d082a060901020a05030c130509 71
    0x8541c46811401008003804611000d1012807007100130354100040700940d003a540b07800620342d15040c0c1002080100686440080c42540c01a980f64140385504000025000a07080e03018202e0510009940308090181e2108114041b030150012000601c511811903000c4a071030440c41c4112012020894000c1c5001d058284000801d00d4849202d030909120420003052042498802001070340386c0b039140180318000144034030380303450015808507107135a100303806a03000c2000041c1940c0d41c0341001a00a036481000c50541d5000c03620143c00252120b0010480c003407229055294400007440e60034041140340e10007081100c08000d044132a01d251901040901444031140c840802d095040c0380c0d024154141643c00031003007500304401400070580c0814811340007036050b9a45141500c56181010160046c4400c1008122507024160750524002c143c80344028103103c282d0b401911102032003803d03481070813100c034041282007002c12031404c0250014100b0714082003c201035241c45a00281c0a0007040c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456452464 1250 456451214 456451217
    0x6090e010605030d02030702100810050a0e070e15120a02040f0308030a0e030310050111070305031603091401020d0c05010f09060e16080c04020d0e1e0601090c1202071110 75
    0x1001e003480b5505081042c100c000740140021030601e00c3c80e42c0015505c54805c04000d04020050000c60058901e100c850406401c1c02000c6804840d200c1c3c1e140031651b00d0440e03039180010000395201070b0504000080c4c80c0c0c01188a481e02e07140c0b02c40003000c103103035502c00741042e451154200400582c60360001c1086000d1032080c2d20b42c66890900e08403100a0701c3d070844802c55140c1040040c13280c0d0615081050048520a0a02c2410090b8140d000d40c00c20b855584060028080000c000c00503681c158007407001c0034401c0c0c9965004948400781122102d1b90342e60341e0703405070340300c0611108080e00403450b0b2040303213120740004180f15903100d01031402e03980d039940116001a181c403844590f0205c1400b041034808071040d00a004241740c84840c5581c0c0020090460003133a00040c10003200300030360030041d01c1103900d9040391100d013448006c80c0d000343d002150320764444c080c140c008210340c400c5009942c0701440c00d40d58894400b500314110002940101812515400501441a4591110300d980b48030b0b00202d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456453714 1250 456452464 456452471
    0xc051b060402180c0304030804150606201204051210020a03290108010501050309010e0609060105040c080112031d180123091909020604031b050d03170a06090e01 71
    0x20701c103000030194281401d8891143c52000c00407119805400e5030752082c1c0510300311a060f1180e0038040003085003403d100c00c0083c20f000012480c1c03500100e08600001110055000d07688010301e90541303071000c0408001c980d02c0200010002c1e41380c0000c026076918042c0b010b030f4086030a0050564105d900a0064401017a10b48048101c01130403110042c01940c1002140c244501c03180000a101c4401409030328140240880828983c0c1000d5110b090402c0c5040125005c5003010100340742c1d1000b09201c1e4070b204600746080c509585110340d04150485185550741e10714400181c6e411358512100f000040d03890300c40c0c0000078040b81c1c0c3e01c010640c01d0304200d281c442030b1541482d00e1a1206141c1118540301602400d00381ea0f05500c90948181d845044a5040c520903401d00d410000540b004103000307507204501140110501024620031044440039003890040300f5500d109110320780d0702040c000b6020170140022000040f03c020201c82d0301000302000094100c0d2074400c040c086640c5020b1041007a0f64 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456454964 1250 456453714 456453721
    0xc0602010501050a15032703020609100209100e1302190908010c090e1e090303090f060126160801020403050f12032205120721080a0c051b06 62
    0x40a10038030b4003620056416003411801d0030320301c24802a01402d018105a568140ca03840c180803180b12075249150800b0503101039041b13041c025521101694408450301405a01c0ca003451000e10807214917641c054841c01207918044816100700b0507440142d40c110070407031101042c0c030031107100404158001c44081901400140e100522440142c1c00000b03880c1e02d40340151601c26004110030045905500c41150385a69418829007c000c801143d1080c0001e44001c1c4601400b000c000345124903801c1003201d64208203001034a079071302c03c00c0c0300e034135681da10002e5607032040032192051079403007070780201107070200f0006610b80c24499000f03600411a03a50301144c10710800100340102440c44a1420041c005a101c07d5040e42542c48050111030514895102c041540040215441c0000b03401c9002e480145d080c0c1c0740c80403030b240c2c020b46080b100e0096400ca29010060035250840151555a072554113a83c1c449444d08002c11802000405003c1d040c4908450000106002001080780350b010703140030306 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456456214 1250 456454964 456454967
    0x33130e090f01140f10030c0b07080705060703060303140325030213030305030601020d0201020c06280212061309030e010e3007050a121b0306090c0e07030b0f040917070c06 75
    0x10f401170074a0610700d0000780100702003160300803008190b81d14031405035543e04542c5001d102902c5502401000340c0101d0301004040e540542c007980480e4065211a08030701c51504584c040b0340b104482030344007541a581301248002400d201d000c1d15114501b00103140c68000b03442c1621181d503aa02c1200012800003c000302540d05100460400400340000d5080605990810742c68207001403c1e00000031742869000744040e103142d50502003241c144402c43d920381f404926421090012205280a11400b640f04145000b4034400c0494054040d03039520640c9107001d00451311089480c211950088800e82080c413001200c0d0325401c031804440118110840201c0802400d00340140e001d6403050380b814a00b04030080c40364030309400b0150b20070600c0c00c8400c40706070301c027514a0300c40d04040c0c0500c2c98580704008121820701803400380c4d02c040101404569503090110203076403242d5107046d000180e9080c1c014490a046d00044c40e1184500150001005180c095082c1500007001c195409c100300e00c0d0801c000e6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456457464 1250 456456214 456456241
    0xd11010210090f11061201090203041a060603040b091e030304050c12060412200f151909050a0204050c03010f0e04030503070509030c33130e090f0114 66
    0x65400300d07400d11110460b41c0301c16060542204010703180c9030281218640907500c090403a900d5500d03030020b800303e550f1100c051000a40086504880030340c107091210614400041c101c0780b040350001c0c1054a19030700c95a507003001d200c010b00390040c180700702c02c603003d03224829501c0d00700391401d03202c01161245401c0c100b540c9000d408003c0c1502840c08110401005203010414950094000b060000c4010400c9400c44940340c00403a003450249003200e903407440035800f1810180c1a2911011202e90542d1000c40d14803088084d515004c0d554003d1032102c4100065800001c00140540b080d103910413000e401060a9540445076050500300c004014810580e0011019024201040c424030182c502a80c0284c0144405007030710702805000710383c40e8155030b4200680d54540c54058030300c4109810032410f4070a0307092000a50035400030306180c024101c5000030152a0308401482d034030040c842c80d0002d807003101e003070151924105024141c031518103480240120f03c003800d0076118503d9145803110704901036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456458714 1250 456457464 456457483
    0xd0e100c0f08010537080a08040801360c050a1205060708090a020603060f0d06020a030617070b1317060604050903090d0201031e1113050a0e01060804110d110102 71
    0x1c0c2c401840c0d85041c10103802d05010424070742141107401c13082001c1c0c44041c100340e0386d485020f8501c1640001010420800c010380102c4540b02c000b404050300c2c0d600c20020081e4807017002e00181d240c041d82c1520455a24020510580c090040c6034541e0382c41d00c0115074594141d41191074041d10a4401031b080203c208003207a40301e90a4504010349062240800b80c44403242c00c4060701c28400400070400c1c03035442d400a072055000c001c048014000441c80d00764043d42180030000082480c000700068011010100b074003001a180b4041e0149031f042c04c0c8266180d400044440c00b881407852004a48803c10030600001c050003c40105442c0c580704042005655000341101c24a0b0024089900607480343c5602ca10380e0f0350709003404580d071401003180401c0c0900084d51100d402d424012040d11000800d4020051104401c032020a40b6071203c05003d848060303440341c00c40400e41d01c03004121180c892004a0b40141c442c200300445d007410840000c42c2400c3d10381c019902d820740440030b044a5a01003045000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456459964 1250 456458714 456458719
    0x6020601030302150411040c0e040b030f030d1505060a02070504110702010816050d02180406121502030a0617030a09062a02062208070b040b0d0e100c0f080105 70
    0x8440d030459030020344401404451845850041010404003ca0003246e41c40c1c81d680680101305403038415000a0201c40070506a034043c0785006100c8656080108856080c014101d00a40c68200550441da0040400e00b9840032a40104100451a59200c170002e00103081035500506e440da00744000c00086928080c40e08500301c00401c0400c0050b600218980c1d80300c100c0b000d0350181d42e60340d0320b000d030366900c10858a40d2806200140142452901c0d1148401c0c00302c00b601c0400119440349050301e40d040c20210054040e0700b0540b50703038038202800c0e0001c2d5480b2062450110740f6607500c01a130000401c44004030480d507000410303143c40301ca074060a071400904192401c1c15076032000b0744c00f440c01611003010780c10304108000411390554a0f1070040381d5980b5030710401c0b5103032307006015020b664103400b5008040a90169080c0010400811425030b000c0e501c0b0911000e240011803c56a80141540a4862180e004901e03004591070203d10407060041256114500d440c0e040c62001024040c05800440c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 456461214 1250 456459964 456459973
    0x80c01080c0a09080d1d090f24210d0c110f0409020603010e04030f0507030504060806011107170d020f150c0c0a1104050c030912030a110318070602 65
    0x541680c0e0110311150410038108500b41d0755408040b04403082c43c45600301c0d10241c8a21030fa0b92113115030103217040c0341c00200c0200d009070011060080004019040e580d030b000182c2035402182045264403e407007040710302c20003001800f1010401044a00e581460b020891840c13203100843e01010511a03038000020b43c0c608a0300c540d1196454aa003c148040710034010b84100c6030300380d541d403100c0e40070310b4400b50001c10007900c942c5d407000c0d03030350f41170b80c040301e0450018400f80318200219010b0401c0c0c0c0c9109606480d0740d818213043c541c08a50b079400041c64981000342170078840040c10f6040c4400400741c0440444420b1040c9000c00d40c80c40e2080110620b0110360203600c07122810320000c1102c400c6030b54001407038030f01500e036001c017041c00380545203181c1340c0b601480f84810200a0084a580d4000205507802e00a0f6950810100a40c1c00112003001040d0841008030300c940005900842e44803203080000200100c040c0c4102d140f81d00102c415407903115161540507140c180420420008220700c0c401003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 456462464 1250 456461214 456461233
    0x605010c03020a03081b190201060b12131104050a0b09070509011e02011b17010603020702130b1201060f03020913080d110405122103010807030237030c08 68
    0x943d9050b03805005070410000780041062446002284000742209801d01ca0b216040c3c84001440b240542c04240301661810b10001240001c10041c2c2d15a0640c410b40c001e0300b07503903042208187e150150000c0307900040d00440c2c2c60030366403248500c40c00703140b02e0100042c10a500303030240100014003801ca4810b002050140d003015a030700c00a00c045003200c4c504c43c158520041d84090740503240d04c4d94119041c4181e6100e0b0854254080c0c0300f040221181c11b2205403690342c51000794102e101d0004040e402900400f003100078204150000701c00081d02400300b0b028641070031140c908560342c41d00028901c582a0404106610b81020700c1c0340c10030207078403030b0140c5003010f4ad40300a1144503241d80c0c1760140d03482d80700c01180d086007401520000c01c8040c00381000d000304000c1003070301c1d0178038481980b1407000404038800040c0308010569050710101401000e01038150380801851071440d030f045c80020159000300507080a00e03180c900008108a8003d11546810344c80d10500100d0107411105c141e500442c0603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 456463714 1250 456462464 456462467
    0x203270307020d05010626010612030c0f020a03060501151409010c0b040c0b0a0e12010605220b06040e041401020a0f0c1a0c03061201060308030403030b03032104060605010c03 77
    0x1101c201a904460b45000c9010900e0801d001d0300d40c69100300009500c0c88615460341252401c1e00c80e400d010070000f0403221f526039280e1090b5030008100900099501000d0b400040c46140913000e080b80000d00f0b01c06e40c241d07640d0324841620400d030030201c42c0c18401281040c0341a080743ca0401260a482e403840e081031001070000f84201950000034101544450204060040300b0205802411440464030350391500048050260401e100c1c0840c000c10850b0300c0c246c180c00c018400c01e41612030061001000b10000c42005040c01c0b6024200240c0340c1e655110903d4503903503900180001e00c0007008540c0c140c507003070034104401143e041c40d0b281c20703034010850801c0840e80004000d451548509120707180e00103a0800e103504c8001000e0f001c0d41d00c01620103001506603a00040d5104e44002c0303a0a1442858116406013a42c14070301c030060445405101040010b40690050520000081d0460342001d400c80030450007a05040400c4a0910340c2000380414000d041c085c49000d40401e0030b00c24043d1005540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 456464964 1250 456463714 456463717
    0x70e0609151834082404090f03020c0a03170703120c031b02010e070b03280c080a020910080702030c070602031201150504030807020d1502032703 64
    0x1e40004000c0302009040e440e9101c248655a40d502026100e50600d8801611040c50f80d4000f002000102d009400d4807011505542002400c0c403203507104081e9407248140381c0c2400b042d4800d0800c003200701e104600344548070791042c0400a4041e003c0718002d001c40d4100030341400b140724030030750050300203010600c04a2086144000407588a980ca01e07035602c03040c2070442d03821211980010b041c1d401c0c12003200711568550000704071102040800000100012000d908882103145d0718017003a00004004c10a00f20725001031640b0146040c002c900780d00d9141c001c5900d800e4410b008003042139444d50740b2003440f584042441e500c081c0740c020441c6070001c40d5000643c0c000301c02e8859020001c0000024030f45500c02d0069801610950307084619450711000c0180d01c0340c204021200c10b1841c49000090010200c4a010340000d420784c503014a0a811902c0c1e490843e07101c4841643c1088001810400054641d060207090325201c0070010b8586c01d002c10408400d5919440d8148241d15420f41211080340100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 456466214 1250 456464964 456464971
    0xb0105071b0e09030d0b06180d050a170c0c0612060d0c17030912010204050a030b09031c06030201020f011b030902030a060f1e0501060203040e07180801020c070e0609 73
    0x2080c86010050507a10440140a07410011444403240c0c140300b1030300d0000003d0a0b4515814100784580c81d007450600415008040081004e65a200c23030f8000719003003d4504400d01d130700030410b4030306141007921104a400350308401080710030030005007294400c0061217030240010040b140c481c9080c0790000454001200540002d00c1100001c0c20841044007618a0078010540d050742c017080c1c0142410840d4803070b08841c240314020301c0d02d9400f2a2203440c040c400c44003520001011001218110b89480c540c0b800020a150340c1c0d80f2081216141e000356100052425a0b10304102060490851000904211300341038805070680c100368190b014125184003249180d0349500c0d000a80300e020f800082e24000490030050041031800c050342409079078a410140304100c8010302c4003100c0961000503c101d5000b40302c0c100041e0814401402000851046140c10910924024110061041401000c4400e90348010b07840d80d4005044c0303c2016041c000c0800812503050185902c2c40c0400c0801e0010f01c004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 456467464 1250 456466214 456466223
    0xe03030d0507030216210e1e010c050102070b220b0f0a06090612020a080312130804080f0604020111150109090c0f1409010e060f09100b13090e010b010507 68
    0xc200180c942c52090381569203085041c12141920585402c0030401c074940c03002004451000d01543d515a580a030510b40c02c544030141040300c52103a04010404070040751135034103040012061592002c55001d0000d05640c5011303040c1d050b01c1d42415055200740801500c444140700c5042d00c01e200108003641c49566116043c040501d01e166101c22001340201a9504402c1d0501c1c035080e00411020300c0200d5007044d592091f98618022034448900f40e279a402074080c141c01e200052800a01c1c025030003106100e04600c038608240c00c1c1612401d44604181c47c0c450803481550000d4204015503038060148901c1060001c0a0040290080c20800028005000700020207850340209010000c03800d2207000200800b0540c0d070502c41c1c44a611198030a210300400f440341090000200f02029103800341405101c008001141442d08002031009408008194040f60302800d100003802c815801c000340b044090150805140d20b040040343c1c0212510984040d080ba0325042e00182180d0300541182c0d480c0380c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 456468714 1250 456467464 456467471
    0x706050c090a08010212010609080a1502091206040b060619230406110f0102030c0304031b02040608011d0a020d08070602040b3c09060d09060203130b070e03030d 71
    0x10200c05010511500188036004410220001499941036020700002e003800c402c020350590ba01c0300116020040c9010301052030700620790603000944095401160b010712400301600b0035212000088105082007007500d0150000410801040780b05504070340c1c8064201c9105003032036500000c4020400c1d6981c48401805040c913070302e4000101103000071a44610506503540d076542ca400e0000c0464884010402451181000d9084040018002c1d20700c1422245503540c1940d80e0b1791801c84a0013712458400c014a1700320401002d40c45500405001e05070517000456003c8401c4040304002c1d61000c1c0c80030300c60b004a5840e400607a00c94a2a090403034018010315120265030a000000340304d1684000100003000604135480b840604a504c04144003442d103044050140b80c444c1e0003585c550780e007447d04950812807070a291600402414034407200c01000115608503950301022030b03005903650041c2d21110485441044003100c2d07502d52098407444c1958804080318046644c9008105002c1c40c0c40b40c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 456469964 1250 456468714 456468721
    0xb0a15030c021501080a151b121401090c1701030b0a11122a0309101805070b130f06050f0d09051005010e0601140d020306061e0c1011070605 62
    0x308100b00680c0c2400b80c40441641d585d2003008580d1001201021200141068201492140c0f14440c4080c40c810381c403101007640d80100012146000061141c40017a81d4a2034841014010315440c50701030301c0a4400007074519500d0502502411101c0c800e0070086060b4030041c07000907006008a90849070030300c008603140fa644401038483e80500b00d003c442c0e6101d040208100030705400b880c1c44c03020840780f0a07040c92083c003c12190440c4800c45d11160654004000109400f07250350104400e6403802e800b40d45a00060b036615400c00b41c1a030300401041e030740850800b06007a1014401401001c40f80d80c04000c2500e0302c0d00c060510301a01c00c040f491051301007124820441690016110a940001a40d018078190111080201000e0003160f00034420080003501035402802441d400304580080310342000080744020700a5070004003541d4200c18140b240800c040c5141041a00810001500d03d03114002441d1040c03074688034040324903020707003000102c40f00751081c0c9007220b201b00c1d00280302140c0c664 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 456471214 1250 456469964 456469967
    0x1a06040b0322080301210302061513020a050c0c010908060a0b0d0204020c030a0207090b0d0f050c0604030312050601030506010e0603130803090102070201090f080715030603050111030a0b0a15030c 86
    0x100c01e502d80da074140d042c1503104020020504000d42c1a60a00c6056008141000441040d5004042d6004002da440f00d8085003880350384040e8811106070082081d0458400340510350280d0b005846040d004c42c80105900000100c2803008900242c428030344004007a01c0d01d40520b0b984e07600500300044260341c9040700034503600c40c1c0784001c0b00990090f00640d0340e07562020801b07170741c1d034071045034030005002e500c1c0040f035564190b005640c09260000c11442d8140c1040e00c0303801e0b8040c1c0c20482214148111482d000283c3c4a0601410003580a0349840705000c41d440040c0c000d89400502640c101340c50101000201c1c2c1e0005140c1020520907507007240c903030f981c2070766540c2e400301c2902c0003801521010003040103508054004003805817003a0f81d010b5809580f60703501c1c0d1000d5200d0003026010b0300300180900c10b070146550282d03010f032446e150100d001a80e076110b050031550b0604103010702402c00070400c01203103554064039268480c10b4400302c01c4145002c020543d04102d5003002c1d01010f0301c0ba42580c03a8203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 456472464 1250 456471214 456471241
    0x1203020106030204090f140604030509042a0f11060702070612090b040b091216020105091f020a0311160501210f06090b01050304120804331a06040b03 66
    0x440d800b8204110304691814092860f1b80c0740101110004280c80c00c24030620004212035018030383c103450b80b6003420204000c01c005801000070411090781c0700041d18480d160050041a0300580d1500d41d04424010840000c058103140514846d09601c0031090050f803a90008a88040f11000c0c60500e60140d84038a99201a20654902406070f03254801440b05101c511400940105044011144400d440c04441d400d0380c040c1003149810900c1225000001d54001c00090248903802400d91181490b03007141c524030b0030b842c0b46a030f00042c0c1c012042602011340003030416620420100003011822451100001c00f01460300510341008852403c0b00240d201a243d50742c07804046403001c2c002d030b450f81d442c1c5400400d202d109d03111100381002a40d070303081d50003481140d00840d0000030800c40240210340035143c0040242088585e0b04950352100c1e40214040001850807446e120464240d4092a48000a40f8107170310b20000307108645a828640356851108a4084a9180014584039501e18800c1d1158 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 456473714 1250 456472464 456472469
    0x4150804060e0102130807090c0c110312042421090311030c0a110415120f0f050114063304080f0715030506150d0b060a0f021e071203020106 62
    0x2c642c0086000c0681c107804032022815110740404803541d0903580c0d00101c0c103603071810f40c1d62800325492051040109a0f000e05000000e4005030840b190081007500b24545640580e10000040c45240340d1110b00140c030503042c05140b822840e01c0d54482020f0741d030790498a4403010110365510b903a011541c041600580480006001c51003e8944501300c20307200e2a160804c04508032255031600701042c01c03a152a20504e14100d424603030b140889410100740c5043c07000340c000160782030918500c0e05400100007003081c03046148100008202e05002c600c40421410f4090301c401c1c4101c24011042d1078075000b080003100c80e612800485030030006041103406c00742c030403600700d0619402100618a003150740000d0000494001420442a8081044048048036816142a80c2c4a980107810030003206e6010041c003428001d00078006000228400040c0d16548441d21480118510200900034640c0500c09030813600607581c9028000100200c0e02c0761070350168007912130f10181c980c1c41041410701c01d6100300007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 456474820 1106 456473714 456473741
    0x1090c3b0711030423120a0201020c010c020406050310051006050a0203040504020306060d05150a0e0f270102030103110f010f02150705160f060c050415080406 70
    0x110a802c004055103140f03c1404041004a18101c008115251440789030629511242c00d011406940716582011074114030f600700c0c00b40c0d802042d1000d440303900340380049040010f880060002e200301d8106d81d0f0980300300b042c40464084c0950001d801941090405005203135505811030386407103294003941c01600140310400203801d0540182d60440c20007400581028140601c42c0c044980071612280560201640000d00742086145080908180c05c60205e45107405047d00780c0d00d05000e8010b0f00c020282d6a40540d54901c1e404074898040c101100070b5549580d242070407204844030240d270a2040320342d413004821540c0901c150703146944032034002d040210a8600c50f1038101c0b2000b80a5410300804112040d04c00107e800c070007060301c0c45003c4400400c0154101403086034a801a8402401030420080c829100550741c104540e0540e45049621550b491a085015100301c000303518 = true := by decide +kernel

theorem cover : BRFrame.Cov 456294964 456474820 := by
  have h0 := BRFrame.cov_init 456294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 456294964 ≤ n) (h2 : n < 456474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
