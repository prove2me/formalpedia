-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2739
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:53.173432+00:00
-- url     : https://prove2.me/submissions/1530a3de-242c-4fcc-97f2-0c2a55fb7e6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492446043 ≤ n < 492625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492447293 1250 492446043 492446063
    0x30a14010b010c2006090612070305070503010509040b07020f030c010f1401050901090905100f020a110d0c020103050903130b0403030f17010b0711061305041505010903030f0306080109 81
    0x1009280a02411429400900e003100da00480741d00d408084019541c11603c1c0c215407840340325242e1300c07180c0c1960510b4a008107495141d500740c44c100c120201d0700b183c0f0303000028130780400940f15900034002e5a050360b0300502400025a220342d1840014900680035406600c6504100c050710b079020002003440760301000020400799a04581402965a10100c1030000003500006000c2e5840f01403e40741110041c00e40031031074100c6420100c1c1440c0d041e6058285a03410800c40000c0940c0c40e4000317201101301d940d101c104035455014880e8880e11000065400911490001e1001d98420f03044242c100445109980c600320021003110a02c40035640041c843e207030045020824560000c4e50f9a0041400b8204141c3e048120400c40f880c2d40414000c460008001003140000d100d024480061480e0018140540d5101c419041c8800c0880c28440c0d03e01c110f0610f11480c51103007240410004890041c0c64a05003107046a8081e1159140c1c21030000425503107000c00549030100740601051180501242e003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492448543 1250 492447293 492447323
    0x110304080705180705031306060515030708060d0c05010c02121c08010902040609050d1104090c080c01020c060a050a020a0c0306020706050702160b03070504170601050126011a0405030a 81
    0x40f00f15a4100f0b100810341c1c0005080028094114040341da002c00d07440c8080d00c0d60a010b00e001c1c80142869000b203a00b2102c1a140300c101d01c2c40d41c000031030207601652a074044070350701c0f44100030340b030300a518005041e469042400c00141d40101a0700650311f00c014000d01c0822103241445190822144503616401c0c1c40594002c14182c00044850141183d9030301036180c24203111020340350703140710302c01c1078021407031071160f103041c85240c030392184403110000c0061103070740e1985c00d103162125914081d08400e0700440301d2844141d8000141703140195000b0348030500382060314606a4036600144030031410360080781e1584001504007082031018502c150801600c805880c00d0810446500030915400e56010300080b400144800c10400300311036950003100d0381c913554400211844c3c0100c0d484550a50304480131a0070441000c104141071b01c0007aa02c000c0c01c0942c0103543e2030100d8140e6100c0804040650060041801c83e8002800080350010024a4181c1c1c6401080c40d040c014081134410322400400c403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492449793 1250 492448543 492448549
    0x90901050a0e0a030806150408060901092f1c0b13060f141314070b040515030708040f03031d0c01030c02030c0718090206070305071e120c03110304080705 68
    0x400c51000c0d2000040c0f44485041e40c02400352880604014400c000c1e030810600e0611038041107402504600e02990002d040c081c0040340030740000b070001c6a034484814000ca680e0a42046100c40c1c16070180b60201c03104910b04140603200101d02c10780501c10032402c0f07554000c520310104081c0504078240b8038040078002810814101c0e0442d841c1060400d04041c0a51038203088603c4080e0412200284407108144c24945035151401c00d0752950700704d0161003800101420303214084d00845505a071100c035110402a211234440c0720849003c0040381064000c0f42c0030482004100040340e100e0b00b07002542c00c250a02c0700c0b841d00d01c0031040390503e91000c0c2c0c0000b05035a041c01180b041d450680001c6003402c024041440d210502030149142116204400d900403184d207400c0280b40300d802401444c1d440300c16041c010819807005078256450b041c801b08068010700c04030300b0145c0d201c4d000707680899040c100e0102200c0750180130a0903010004801c0b00c88401c01c10900041004019060083c10502e240c2014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492451043 1250 492449793 492449801
    0x31908010306050a180b10030c171e1f2c01140601020c01030e0a1502040602160312120b13050613020c1e24012607051e090901050a 58
    0x100700c00b41c18809030303400112244042c0e0708201d0707005600a90a039101c2d850151136691239400944204149600002c03000180300d0020f2501c92924199041070080c0c01c980203c1d440c4400d0f081c51a548060304600135228400d4000040e104005404200546400e008610036800603100088015002c044940504024450021a1420040c1481c0f85240c5000040d4a909002c0304241c10b1680b00c17040169188401e02068008550100788002c901c80403d180c800250064021100548074180141e40440c050704030042c103c82c1d21010102c004c643d4854203c61032110dc032651501552100d800c3e0003240c1d01d100c2d81c0800c86188580000e82482c101080081c0c103201c1c1c029454075a441009010b105a40c08a00703d020322105084800748034010401c03203840c0480e000009000c160340d9592010f8840303070400a40d41200c03620480400b00d84035400c18141c0180e40c004041f40c0c69404898108007500b080810040c6400503c0300d080c3e00201e0b02800b00c0c040b104101c0b49943e00749d64a40800c0151669841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492452293 1250 492451043 492451051
    0x6050a110a05070509130f080d050906010b0702010f2129060f130e0c070605011d07030c270302031908030406020c010f020703031428090503190801030605 68
    0x100401d9141002c0d140d40e6203480040c06054003403054480012845a816440d00c06202d80c80003100e170503001942400c030415003112824160040c00d01000c500a542e0000f0068140c0b90302e510840d1410505034015200b100d800d8800307400784041e43c40b100290524001800e0130a408070b800c04120010850585115100443c032002605030310091903ea00d901e599081e614942c0d22510b1342540c44150310b1400401c15a42d40c0012620401e00d420400201c8126018200d01e40c070620051050b42d80380d40003640542c003005a80245c4800780b80005100c140b080c0c00c120720001503804d00d4580f40c6102d41403000d90042da6034500b401070134a82010021401d08000c482850100b0100d004d101d624a40c2d9161071501c030191000c0c01b01e070b401282c0f070044884290300280d4280d800b41d100319a185964a4054090802e090014401e5414800095080c4258844c13090072100030001c5085107111042000004040840c01500c0b030f4401808849100004000507200c0002c298a030801650324528241c015920020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492453543 1250 492452293 492452327
    0x22020a0824070c020409020319150506010e0105070204020a03110310060809010905031605030405180105090a05040c1511030703030e0607050f0a0c02180a02031909170f040f06050a 79
    0x20204400301d544000300d0f201c82e07581124042200c036083d0000034600407001d104901c140b007884484004100880351261a030b000e944005102c150340e03481c01941d80c442d014040d60f000c05c004000c080010714081d8020403442c02c0a040014034201424040b80c400d8100b214420442400084140420740c1c01c00c184a41c400d01e400001d00c4142020b949141d101d00558000f0000980c5011706a801c1140601c152400f808000c0d10840001000a8140c10244000e00c40c2600907020500400c0b5140c01d0790041c54400e580040000214a182124407640c0d540c1d2002d0190801100b00b001c81001001030004080c410b01a035800305000340c2041c901824101d0262680050050820a5900c60749000c1c050303980318003260805014008a074000302d0090280c0c00d081c1315a621032075040103071030384899000e0360056081c280c0d5008080240900141154403540004d405018000720114400384141c0040c6940c0c0305d8240704908150b41d030b068500780100d582d00071102185020400c240c0ba10350141444d10401000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492454793 1250 492453543 492453613
    0xf011a0d060e030c0607210c140906160b01060f0801032a0b07030309051614060a02010b0306010801090213020a23040503160e01080601030b22020a08 66
    0x6400080d104a490355002002203845000c21030a000050054900c40c4180038280d4200d4500f150009010804090442500c000d000107000d04154080c820200c0b90343e09038981d410000e503401c00019458002c500d20944c007880c10800c290034052840c10705010248030f51610307807982d410004090429500b0b440c045040010038001003001c1101c108161f00301984090121120150700b0117900d403000303425009440c401e14005a0b9001305603166011406030350169040c3d0707001d6403112241e0342c04868203105a100010740311803404075625052004240e690100c0c0000111520044c02003403c044091340500d0f0f05035542c00d4980c042d41403c140395542481640411840c1140604021348004165400302c8100106400d01000c140003000c12900506402801c641c080c0700070380e18616800011780a500141c01001d000001d01041c0010040d050b65803008844016071343d50114089000c00401c114062800248140e40143e1100d4072007102400480d8060041245002d003151100984080581450802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492456043 1250 492454793 492454841
    0x8061206040b04080304060612050303071d2107030c12030e01020d0c1410022a010b06030c160204020f0408010b030c030c102a0c060806030304030204020304080c0f0f01 74
    0x80100b40e942c02640705011075202e0b00d075414254000c1074035030410070343e07200700d1401d07031060040010142d84141004d40c1d0b0104074507d80b00d1a040c1851081004c2e5400c4460340c0e001208281c1c4410b0301310585103000b003c44541942c0c1c0c5d19a01c0302100a503114640b40020b4108403410f040e07100400905549080c0000d042090660100800d071081408000d40350381071840488982c00010f108540e25500d2110041d500c075081807074200914418289020422041e4103000001b8241c1030181c4007207884000c2886095660b0004d0a8010350b00000b0241d54101c02d000403000144d5a620107441c0a8000a102c251118100200b40f4212803940c04442d229034031207000409556030005070620603034010750350b0401c04548140c09136505041d0b01d0400d100240d400310144200300e80b215102c80414000c181108030310360780720302c242c46c4648140e4540790944c004000c03c0c009804c10307030025600b080c032a00d034080c5400490f040080c00c0010b009807201482e0070502d00100c604070240242e070f803448000b200f00118050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492457293 1250 492456043 492456053
    0x50406120504020d0515060102011d1209130207030806010e1207140103020f041401020d170f040213050f2e050f0301240501030f271104020a0806120604 67
    0x5000100c11003026150800941191900403e030319500c0d03400021110b40c0030010b12045d458540840d41c850040d03107020b0080801054064490462804c1c4902800402c9840d241003c030715800031003078a821440850030044000100d20040044501035510f18200c3d0504c0c400050803019040c1c045403240203902604243ca100c00301e0035030120381141c019280c540d002040160041c1c000c03004298008035001c1303400202c0b5a80c240c085030011900340d00f95400d000c6584000d45074011294050034010503410001041144400011a0840c0c0010510704a49081a400005840040310aa80222029000d00c150320700500306810300e9102500b006040c3c1610160a20100003d6204aa2082040110200d115103081d8000b0116070ac529202403041e05ca0030000c0c3d101c06405100355030000e0300e4542c012604081c02d1050f4602c00d00d9031941d01c01e0182c06a100d4000c0c00e07240c5042500c000074044145252551144001d2003029155190604249080e0040000400031300d030110100341c000c4400c00002503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492458543 1250 492457293 492457307
    0x103080909071b1407050315040b04050304030c140a1406090405060a08061608060a03020a0303050901021c031a060a0801030f050307060204060e0310060b0301060507060f02070602070210050406 85
    0x2010707a010001c50761101c8007120284025003102d000900c14880000c01d103c48240d0f0144d40000d031408481c110341d500c030141561081d420000c400e100e441036000c1800034501c82c03441c640090140b402c030f0f400c2540705d03210a0b8021640340c0c4403c01d51901800708890320b0501881000042a00105800d01e0b800f00001080c2d8a220320400d46100d140d48070001005a0365010044018120b401c0844045141c001400150080c40754005d9001c200c0340000900a440c0c02c0408500703807540680103500040c80c3d660250b400740c01c81d200b95819400f8810b82c84112045030421512584955980030480344d603003440822070010000d04060061104004040415401901160440ba4040101ca54001950a000d8150700580e40300500d11800043c0c0007801ca0360016081c542078904038261040201106110404c541c0144940c4445103010b20041200e2030154000c8c3c5051400b6813004942400d0800c411000c0341c0c404c96045911581c041030301010740c1001c400766001d80c5860b00300f152500e0b04000c0003601e42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492459793 1250 492458543 492458557
    0x51503060115032007200a0302060306061c1508030c07171603030e2106043207090608150604090303060b0d050103170913050403020f12120f010308 65
    0x9050580070241c2030740b10340e00c0340000140712528007030f1505a04019030110b600801c01a00c01b00028604490020114007840400d050014101c1c04898a160309004080e04010481e90348808207000c401c8ca21541c940061400d04850140018900f03140020341d083d218068100b00101da0007805010342c00030340016040280c40d4071084c40e040c0300b01c12401c42442c0001200e10301140c801740d030500104068016401151881c421a0321103003500712640080c107054113440c1c0040300c0360720100110b00490482e25110500c001c200c2881d031003070071412050b0b103610011088003040d03590108200b0881415540b040c213016020120240c400e98074084902c40c00b40e00050704044c456541e4035100700405010b03034490300080100072890b907229080c0e1850a80207140911058615000b240d003c2d290f000801c00403940d1010004160031007103040c641814004000c010f20480a5108002450891100400c01c440545040708504c80d640d125421040340256005003c50070200355410041c800151040300396001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 492461043 1250 492459793 492459809
    0x180f2d01081506090d022e0f030e0a1212150302100201050f2e0e040303110c07091d03030906090d020a0206030c1822051f03080a090302130506040515030601 69
    0x880002170002517180e80c00c201148801f012031103002c0704100803506207002503000fa42c46004d8202520041034050725074a507403404032031300004010400a24003010021090040c1e00c8c00607501908582d605084441404a00800c0c402c41d80c4101300714540048614903a4100e8070003803210703041c0302041000110000e000203400304100c03603500c24032000b510041c45001c01525001c140b0140e481d072003440d6141050328141e0019041415000f40c0c0b00104044038aa40361990050010710f1410500340000e20700c45c83c0c00c08400f1141d000da076645840410145010f400d9000140400742041d4510b146409030317100f445000c0d50402d40210016036107540980390300c5400b6030003466031030302114802c0803da40c0080c00241c1c0002d199802111071812456540030301d00001004015580360400880201c5001d9000c00350303240c1c007284090002400b00e00c060168cc52a600f40700c1000c0e92642d0000c3c2e4502c0c052030100780703590358480400982d40b51501a040d0000602800d4101605251012a441c2e1005004020f8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 492462293 1250 492461043 492461059
    0x518060106080c07080703091409161206090f0b1f0c140102090a031203240501030914060f0a140610080601141b12180f2d0108150609 59
    0x9071090403d03049400c2940e000f180c5c20b55400320b03440d0151121055010344103501c80750f0100c0c0106400d21052007409010305c21a02011040748001c202c9080c6149004c0000068444600149c416014000c20046900d141e4000c1511615031041c80407122844040e2035002c0c08401c100c0e440c050b00145000007032034000420300c40302c0000c0c8000705e01910074542c0654015002c80c20000912a8413501c0340040e00503a90117000070000485084080380380200381501d1118440e000b006558000d50080181c10312810b04032005142c010005414202e00f29000041c408241d403c2040c420814071402c0c0c1c80612080ca81056403c201012640403400c5060504c1803100690106401e40c0c0a42c8004600c07072883d841c4996541e01c049856021207002c4005541f4900c5141d140b408080a00030030344101805540079094111018070801412426071900345421404590f070401029030400c0c8502d600d910010325005030034481000050141d10000c100003194212060450181d41c0d0b0304080328900c500c2150440303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 492463543 1250 492462293 492462301
    0x40204020906070206070c230906131508010b13090f06200d090c0801060302060f0f0f0a0e010216360509060a0b0102120f0c0c0604060306030501051806010608 70
    0x20b020341c4207501c0003940c821400705007a002c000900d105d42c8151000a01282013841440940e10000a1181c1c9126409490036002813418141f13010710404d00f40d410180440d42908031010b0800780d030b0b0300750005800f994454090191b01d04200d16a404c03107404071320007003000380050f407074030002c440554400920460715444c10100303c4902c4c4040d00c07d054054042d160f5110001030b00310b030080c10700007000c0324422800c020004001d981032141008032a0083e21440c980200c2d40a81903865100d12904190040140165620700582c84040c0a0440b00b07501d03141c100910b91000645410b040c40c1d0303542030301c0c00c00b20000d01c0084865001d003d612602000d646100107508a05404005114065407459502e0b002c1003100200002130b44034000d81000d06d040040d448240300482c3c90780032038a18040c40e41d90402000c0d09501040c3c1c010005854a0400e641e850f40d0011f0010303680390700ca03500003000280c4070b003018010300c0000c1c800ca68100c03000c400083d01255400348000d403070710414031900040c842e80304005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 492464793 1250 492463543 492463549
    0x80a020c161401090e27070f060c14070b0d0b0109050d08030f07140a052a0601061b020f04111b0303011401021f0506030a02030f010509240402040209 66
    0x40e120a4540464480741c080c0ca803030500c0144000000c189002443d01c0400046000500c0c4616004042545010001254071082203015500e0725580d0034042c42070340000030350010011040b00140040b0b031340345044c811150405108003d101849031040b500180f00070809601da860444040c00480e110101e507034107072a070050b1441c0c11164801c0780c00c940c0c4c1c3c400980c100541003004501c19540502c0410300c640329003408403001e000203040d91038043c41c20082548054080c0300030b89488214500d82c0325071503030642e031811000301544201d01010340c000401800305a40024500d10340c01c0d220410040c1821498002075402110038201d00e000702e50700e26081d0b03524900707442100c090080e2040c0c000301e1110a1420300343d0300d603c24802c1c11200500303103040034065803010443c40e240d00f80b400010718810701586c03200401800c01030310080d4581b007480601c20051300c0070b00c4280c0300c1100840c0009001d01d0001800c504041d48035442000d005842020700065018084540d13411a405a40050b00ca01400000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 492466043 1250 492464793 492464803
    0x301090b090f0f03040807060c08071e030806011107030b04061104080f0d03060e0f060406050315040c0506091003180f080703090b03280b0a060215090d080a020c 71
    0x50480280d60080003511100000e000d115103800740c04076a04140b020300e00c1500d038001d6002d04480350304130780c0d0304100c0c2c140701e43c00005001e8001d1407400d05c0c00c000f0b591003255002c8600303045112107080c0072406050507080565141d001000b0708140003c5502c10041070744030081400300a0030004483c003c01d09204290b442424240356030384004d42e445884103d060303901c0c0322200f00e0300070501c42d08005410070340c8240200011a40d8410751407040380c841054420030071000400282d0001e0b5240c0c0001640d039401c1200501c8401007200c48034103420242405c0f03c800d0580e400081c05034108101c2a00c0548175420004080e510078500014200c01c5003910240c48015610003800d01d40b00d04035068184a02c0c0030060040c64841d4039600300f229594400001d450000b19041c0f41c0f1040c080da41c4034655620035074408801030101400140c551003070000141c46070075a0f005000103902240c00c0c1c2d2600f61704601500c4c0c000d205800140840201307a54000c20030100100f20028054010032500400b0100f001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 492467293 1250 492466043 492466061
    0x604180e01060303020703060c05040e0a0c03090c141804030509060a0306081f0b0904020303090f010c020a240c0b0a090f0b0103150c0302180d030c05010504080301091d0c0f0301 78
    0xe00031543e403424002d40d150001c0c0070030781d401407a010b000280280101b0403101244c074030034a24074480c1e42c4c00c55003500420000d05c1800505490728500d8001a001202071700285c10b0300c0c0315504862018030309015900c1c1102c158003000403a0b410a000c08a80c120094600d41c0d03d044586643ea40c1c001d14007107015000c550300c903074043d01c40c58050180c0c4d0000003001000a16400008103c1d210b6a0b10130030801810599002e5016081005149220b080240d4184c08180043c14144c150f50039640c003141c030300492544054003220000d1340301c9880c0fa0262201c2002419a86800740c11402207464103a41800060300030300b4026500d2250f4810071148594110600ea001310800366250307900e0414a0031481400c800c5124145040c51003100385010780701340c406028034a5480039400244505000b410310704468181e0034043c510314000d0004100340126880340b481a140145c483d403400b0088815184107a4220b181210302143c00b14070341d8030016401380d410f4000c681038010805078401081c018803002d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 492468543 1250 492467293 492467321
    0xe160b13081b011b03090312020114090d09050915040504030309060c0816050a02030d0203070504230f010c0b06090a0b0409060902030628020c15040609110906060418 73
    0x11503240c403582103145a1440504080e22102481c074181c0040c810701340e0a40c5402004a001e8050138800700b541c042000700c04190030300001400f80700300c8400c13800c1c648045604401e40c0d0701a8208503400c3e43d02509400007441c0c1a594a0f9907820084483c4a1002100c1c0740a4000e9550303800003401d062085e000580c4030785d00048100104c00341032000038440b200c01c54140c07514810182c1c4a004017449042201c0c1071004607405903040c519050120030107944041d061608001d400e2101181c0d00c0720024400150a80340c0058103010a24003051120312a450b00c049030500c1000c098000205d07403203011540d8007010840d1050816a01c0b44c1c1000d000b8040d140300309401c43c1c40d0900303960400006500c41c0d01101c2c0210100c6030560380b004018000791126480048407000803d6181072590b600e03801921103003c0e2a170958401c007884125009807621304403020344905840e50603980034400b4240818a0540041e1050216482c003407002c034005206c0c41c4100000d107904c4101101820200d42e000d050841001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 492469793 1250 492468543 492468553
    0x102030706141608070c0807020d08040605070302010606080c0d0c02100f09020310110901200d0f080612210702060703030b03060703090b0c0c031e0a030e160b1308 72
    0x2010b414031500a0440e40012442800140781070301d00d000c0c03c4124401c054640c1d030703a00d0302d1810740e41e01e25068000c0b50003241c10040c0d1403030308000500240c2c0a08083e010301c2d95099150005818000d0035144994001000d209100041c46803000c035540c1240d175566107900c0081b5048003450800c0b85043d2488a0042800e0b192414841001c0c00b00c2c2c100100d5940224101d4401d9600c42c0d00134021542c5070b00d140208100c041291031015406500032059641c101440040000c403044a010704006d201e1508500142e010b03108000c00c15008801a5089101540c3c0300159040b000310407a40c0b070b80308030620401003281c001d12540754034096088440c9580d0280c022038540d0401c0c58040c02600c0b100f0080c84c4030f4001c1f00001260709200e4820740005540007050605151502000c8441a51006002c04100d0204100c8645c80d07040180c9420181c06480304000e9450000143c0202200d19110000d8031035085805444202c0c0e2004428000f5942c2105295076100540340f030091818900b079011040a00807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 492471043 1250 492469793 492469811
    0x6030206041518080d0f02160314030f0d09060522030315050411040602070e0f0c03070e0d1209050312180a05030703150b06091305070201020903070806010518010e150102030706 78
    0xb020a0314045a01c0d26107618a0400c6c102405a0300e0f18a40d8811010f42031902d0410008901c01c1080340c5600d0450000750b9292040d80e04962075079601001c40c148280f40c0b60004102008220322900d41d20a181020700704035144100700f00c969404185002808041d1152356151600c1101e800100007090010700821040341c40a410480e190003602c90500035004d04c480000c1c200060300f00b003901c6003021b070003d0b0080c0d603112206100c00390000340c041d030b0070420003030410300302520303100a100c008034040d601d42e03150119a540020021642074102e81e020360001c0702424512001c007403d55010ba04802c004103485c2c0344040c0851504441540300c103600d0300c5a04000424801c01e000700c40c0e90036240807010f0108144c86c01c180004c0c0d1044e046110f8006481d2500f01070103030b030309500c405c0d003025040c400540b0f0500e10700d0029190074141e17004040650080001041549001400490081005048442c0320361414440a000210062802d50b1200d080a807008003a8401c0c0308907850694804000c00010352 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 492472293 1250 492471043 492471059
    0x5090c12131110031d010b0102100f02090d08030f010b0c1b12010908030a0501090917070c2c09160302011b050709051801050615071b0308190306030206041518 70
    0x2c660619401e0070001d101840c1e000817060040e41006c01045c0c0040c00c1e584840514480240b1581d624044510303400c0c000c0c03000968854a161051602070780d48181c0341e0404e03000c100d0b0014010303407240300b0b01340b4104141420320001061079030825044d22110a02810a0b001050045c80f00c0b00049a09504c0d0168140402c1800d1000d5406010804010031682ea01c0d00c7c0d05e00111242148046d200d030310a041c142c1203462070000180051441403010324802c9903103081a1000001d4001000c2141c07494421510800381540403043d03002c951040100319940000d850118000554040a1304004041005803403092910480b40100703503102c03040387c40c1280d85500d6500240b6085d150350b6440009110b140300a2101405958001c1b000140100c09810800c2c11002081d40400000c50f038500780600303951300080c11961003074000e41c041c58100366201c0200d04040482d44007081d55005040ca020b0003031025850703282c107803400e6482050440000d003040c10015034060f11130392400c840300d80150f000826460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 492473543 1250 492472293 492472301
    0x4030506040f0c0803090619030f0e010507031a0906040b0d050304081b040e1b040e0a051005060a08060a0c050c1c140a020a080f09060a0905090c1213111003 69
    0x2d800754039144915030f1901c00040d103d12541c21035550204051011440d00301e00b00c44039030209440350a00041940040102e0300980d400142c54081e640d669804008009030580185058181043e13407100603080440300080c821000500140c0c0656503e02d0608803c1d10b030030001804135a0400e0441c3d45407591081200d0f6200d03d0b10050604184014016150714101401405c404000e40000341c911400403050080801600a0340399034007030f44608841034440340c24440b00742402d028502401b0380701403405880c003e85070040c02d506e005000e204002c0158107000708442d03402541601d0302040c1c8a111041c01c5a05010341030100c0514004d00b4805a012510804d0140318a00f140c0c41380d12500042051105990090038801000b50300a0300540e800070b00c03804020412444c1020007a400c1104102c0800c4181d0420903c400c0071612005082c4180d103003440f0b59070340c0319548440051174480c0f100c0001000e01c03809800114488002440602040701c5a0300c100c1480c203001d0b00041c80500c40d050028054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 492474793 1250 492473543 492473573
    0x3120a0204121121060406110d0623030d021c09030605010e06030c0603130b04050f011e150f0b09030a080c010c0810030f200d060606030c020c150f0403050604 70
    0x9501a03082402158280000c50100e40c0c84c0001502042e5225110718000d0801c01e84080e00e10b54041041c038038000141d210b4200500342900740030900480541460025110f0200c6461103a0310000b070b41001103900241d0030100301d22440b00c0a204500e10081603944500c1740e04020661820320b00040b40c0080034200807442000110101c0d120b50080304148200752005a90712401c4468041401c40840c2c0c42c11800c40e0414425000c0700c20f54401d00307862a0846841c0000c10407845400070003101100024041c0405001c0080000128240f50540d2540441418803558004020200e03540343c1e50b46e030910150031101c0e0400c01d20f554404d00c40317426900130101040c004000c904540c0c0441c0005d40c2c0c94055505803a44001d0f0b10204410390740750841901c00c46150102c078640010700b8031005446941d14074650510440020924a003003c402800356030035070048904641c0003d00d0004076550760a04105000650803d41d5500c90700700f03005c458580b2980d0400fa0141c402c03c0b007840104075800044c0040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 492476043 1250 492474793 492474799
    0x180f191214210a110412080702031006030c0603060803120403050904060b130f0e0f0c160308040201080a0b0108010b0906040803130305010510060525210e0d0503120a02041211 77
    0x45030b41c3c0c2c1591038040b5081118185024682804188103042200c00196010b50140c1c0e43c00f803c0c88465070010303260941070300c4404000750301c8150030070420044c20107041c06868a400c0070301c0740c01d0a0890640c0d80707000e01801c10403121182000706007454018011503a50210103003060004a80b200f1090103241e10850010700070481d445800508482c940329034009450000e0941001a01c4031400f40d00401000741c68086602801c101c3c4490802c1142e00f8a00300354840d80b03c2010741e207001e000140007030100030440e07450142421a10241c981e840084075044d07440504500361104c0039100441c00e00d00590300255900e2100160701031171a044d8520010840b40b04000a2080d80d5501605140102051280e4030102d04144148501d9022441042d89805158540340c810100305407520414008500c0341f10038076500100d20074640c10360103466400208015289942160415502c190b924455401c51010308030002020505402e40d90f0103e5004240a001c1c144d001d0500d41400c3c2c00740a80406c0c440c1c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 492477293 1250 492476043 492476107
    0x604050705100e01080112140307030206070e0906012003041701050604060f030213020913050a0507020607142a2a0901030807110301060e180f191214 66
    0x8a480c810503d180280c5010794070b980d1640d2074030241c3c0c84400c00182085442610078009010707000410405481c055010340c0c01040745040840001c0d01006041800381c1c000c011032020401b65917000101d1050600f80d981c00300410340e0000c13420364194020340e000340100855070207007500e03006815046240210401c441c2007200c0f03030783c3d80c60304c002c400c6041c440250808060408100c100300c1030390180c0361002c806015000c81566401c0c001045a00807031720022440e40d914103000034540e040200e01c0e4841c5090034210400d240c2000f1582c418018120703094105000e1b011030799070791800a00d0f010088000c07502207446104c2488082e8880f802c5103103d9441820700d0828144107803400b41c66044c102c07504005503d14006490f1540a00c40034400c031425011b40d01c403140051001414003001c0d01c14403d0400621248150021041c1040782c0b1640c07940c45a801000401d03c0b10595402604149600c0150822380c03200c041c0054500d242d0380036805004035004603200742c0140303d180c0d100303e0030320f4841c1c9000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 492478543 1250 492477293 492477319
    0x608060f04031709011107030306030b061504140105040f0f0503150105370609081005010e0601050306210607080106050720030127050c0102030a021903110604050705 73
    0x4500d451048030007600080101490000e02c0744102d481c82c0d00001c0010010400002510484100e50302c050000c0b40003994074103003002070014090540350000c03c01c49080c03d07280b900700c1c03000e076103801035004044c0110f2007144523101c3d6a004004840c001d002080c8200303901c907601e5071100b40301d6005204880c0240101941ca09108502c0701d1300505031a001800c40064a001c006c403418002c03183c40c0701c16a0800000c68000d898034a60480900601c6145c0e91003813154103280c1214107140c0d00e103d001c540780b41410018418130300c0359081c1c564000c1003880c00ca81c40342e46040001e0318060803164401256140d1605000100c1008601e8611076003860b12104000d90b42c4020803142403140c5800600b403111840f00b09902110040c00c842c02013680100049070031403c1da040c051840303e030440020040c0030044500c2040280c00c6c815590044000d001450801034030100c007948503e080f180c4020b541c1b240040d0881010b0146501040240303030202110810b181c903151a030b030b03030700000e000703081c0301c0c5903c40034007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 492479793 1250 492478543 492478561
    0x1c05040e070c020604031e020102010c020c150f0708040603150e0108030909090f030f0d0c08060d0f030201090b040305120108190b15121513170702030c0a0603060806 73
    0x45003151400803001280341e0720034104a030640140401207a124138200030010104041c5e600c1e0728160071060040401c0070803144006800c4030107400c2e404065400140c1120030075520740011101420a89241954981c41450800c034544119100107219010208011a489500d50f21005440e94010200740c04141c03640c060041e214402d10510b200c50340f00300218881403e00c005010340083e0480111034800000e0743c01e09046400c4616588280c10012600118190241c003660130791607003030b0034006d03081d05201020901c1001303000303400380081080d191034134100b503c01d52000050300d801c40e0144c401400c040c40c0041c196801806851000306480d0b0000c01c0c0d04101040c0300035100d4140034400340c3d42c0102d541d280d0880703400400f8504040462051212191030f0140c0203400c25003128050000803552541548141c1c40252441c03c4010400e58030a00207640c001140710510003540406480703c0da248000391520182166594218921040000314507405421a4090319603c50a403000ca50710000d80c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 492481043 1250 492479793 492479797
    0x210060905060d020609010903050d051c140105012a0b0a0b090c0a0c2603070809010b1012021b010203091b0f1005120f06010305010801090b07050306120109051c05 72
    0x10f540300034441c00b540d005103840d40050103562810704000000c1e96076500c4050901c0020300c4208040f0300c0000f41c6080d00c0c0d036a01001d102501407200100052000b80000510302081406034a05011484140305100140510400c49a01e51560301c020108691300e000045c00f802918014105410518041903a1401804681c441c0c444000c00508110040a0807142051803c07c01c0d42c0907110301060100b00c800003c401920f04250356441c95032410582001006031030700600c0318203140d1401c00d002c0250baa4a0007070003a82c00ca43d1501d0f0040d00c8401d4aa03030001d120f107460034224400460300504100c0010b40280d840780b0410015140d101803030681800c1081081040d4651010350600c0050107464048604900c00500e40b40c850300b041e40d0700d10346030f0700807006a440030940112042000740715030b070600540d030261107103030000d002095469032140100540580030405115010000440c0c9455049282c460307058040000d008031052410a1038031030311210b1807840c1c00780c00c42c4104600a03000b081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 492482293 1250 492481043 492481051
    0x70915170f0d1d0306011410020d020a061a060d0902100e06030c1b0a05010603050d0e0102150901020d0924020c0d26040b1e012312030a0210060905 65
    0x1828024002c1041120120803162208020b038916000102481d10704102050203400703c13500108444481d801009100600c9210b00400c56011112001001c4d034007040380300f03296610420204104140018048c05040740305819a00302c178001c507400796140103541044041a009890714030912180304001ca0304c0119811401d50040e03c2000411005407141c401011402d0301124510407034410900c0c02814450319a00c192140e83d15520244140003041c002c2e4030101c00703241015081084c420740041d4441380d0186840004c80b10a100044c015031003901103e0b81040d06c00c1003000018014a821007403a405142a42d1129082c0c52001c00d000316584222401c511240000703151025100004031444800090901040d00e000b506103c0c0c5105541080d50040f481000e481d08586004020b51303030211850000079007442100300040100360ba28200e0300f941181c0e1782d030180c0c9600c0005400b0441402c015a00305102d4480010603c81c019804200207800c0b4240c11010301c407103581e844450050742d005903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 492483543 1250 492482293 492482323
    0x170d090801061406180402031003050c0a061d0406030506070c03090503030a05070b0a090f0b04020414060f042c061b0403120305060d0501361e0507091517 68
    0xb03101400b29107000005070a4080c030700c21006240804000106d000c0c1d800a4415007400017a00d2401c0c810024280b002c1003030001d068903200541d0340b030320200a00107009030080760306550320303465525096212900840b0103035401c00b04582150500305001005d41c0f4540d80c0a50000e0b00f4020045400e213004800c0300c0b0703255a43c2c1d07501828071501d921000c901207006030017443e96036990950480050303031090065408074083d100c00155450580140001e54110020303904200ca030300c20401c00c4594800309000d8040b201660000350340c1400090081c0c952a401c0741d00e10382a45022003a034250f100000340d0b14860400f034503407070f800076145d2162165240a00d0100524a01d0b803a0700e1091400d210b68401c0358004002018807083d0303003044e141c1c5400c44a9415000e1416070740018010341c00a600514149103942c81d4844603c042115124000403483d040982020420300c2c103509400c0c40f5003080702802030070a446c81088442040d145c0d10001404600c501f02c17180c905845100c244200c0440c0c1300464148039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 492484793 1250 492483543 492483569
    0xb030f2d0a0209311208070503060a0e061809010e071d0c0d0b1e2b020d110a080c0a171e10020412062d0510170d09080106 54
    0x4401d111188034045012220f90540204403500e51100b1488181c3c1901510981c1711003140b51200801250005100000b40070301001405a582c42d043d441108550000408640c642c480c000001d50703000100c03444c60307844003101d000d00c0001c030300640c01000c840e031140e4112400c0c6c0ba584c05d07083c0242c038070050303804940c201c06000140c00280302c10001c000910000400003140324040002070b0090b403180c0040d054480328100c01c0f00d400c0c10f100215011000415017441c0821000c50301812080c000940000e02518800c40d110080240040f4005100c0b640200503040d100d4a580d0315030340d291800200c05d4403c03141204009103802c01340040350883c13594000600b804a05070003098074950b105510300800c0d4401d082d0740480c04e940910241c40504502014200e00e80000d080c05003d42d10105000c000081c0b05090000340070103600d00c0812030155030b1502081ca65101c0c2d0040400c0090780d844039178815002c1c4040f00c00141c011440c0c04d55201e080d129400001d403500c04890032038916008a41c84400741c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 492486043 1250 492484793 492484801
    0xc240406110105160c1e02181522180b0f07020d0f090302090421030b01122a1205161d01020705060903120a08060a06030e03030a0b030f2d0a0209 64
    0x90641d90422243c0356400d404801481d40e03000c600c41111088d056069900301c078046c80320b1030141811400308102d0444a4440b40304101e6590542d1004641c502136880307076200324412001c103282850300c68268000e410903080745400140d610059000301c0b102e0005006079041450280c1c0541c1c05070300a0812aa940700080f0f04607400d100301c030306c4060401c0e18100c131089900c02d00d540d84441003501e0111140d40108041605d640050005144170b00041e610074144501d1040740d0f00040030303000c025400000e0b495050303080f00c1b0b400e13a085400d2040c07004a16081000300960862082501443d800340b0780e40e003540c0748100c0c4035001c1c3c041030480700480c016041890208540d241000c080e140c0e81030002c0581c0d144466030b900c0d60704158810194200410441410080186003800c207900c02004182400c0c080d21448410305501ca100c0100044407255031000d074526036442c100599890303020004200d619004c00080058240503a0800500032000d0503056110703964008105101096400760941410b80c0b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 492487293 1250 492486043 492486053
    0x315111606091b090b0906030d1b060e1b0603100306111c05040201021509060f15100309111203070206180a061815020c240406110105160c 61
    0x84603090355220b4448442c140401d2030460043c010154041c0f48924003840c15000307070103540003140401c0c0f04007010300030440c80c1d03100400c0780c030824203481c980046418440e25003602d00c200560405401d807450402445101c040000b20401100e06402851102e44940010040c0e00c1c070045071720407450700706100c0400c001a4140c010030550380740340303100f01e04010142459007d00709030b484d000d4160a4641c01031200790350f014081500c2406915401c1031172807904510641e03403040e0213001c44e41d44c24000c0e07000881e6910f1440319480400c100410104004240d4000200074100b803080039a18900212568680341c58400b0201d084100110061400c000550302000242c4e004001c50304100e021004880004ea641d203031030103016200700e480f54640c60f0001100d4101401090b0013a1003500f480350740d035072016900003d10000c0081c0c1107a8104030104c0c00803194082884524140300c1100001ca80450045d4102c0fa01c1e4510322a20802000307145d03a494050707201070036000580307008980d0303100c030b03500100d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 492488543 1250 492487293 492487327
    0xb04032307050409051518061305070510030e0d1b2a06092301080f04030c05060c0403050c03070506030711030c1b04051b040501050d1d07031511 64
    0x345a84099a40099440012406960300b070381e02101d054210140c005c8213000900390481d046500f1005091131900a81803036940c030203029100c481c1c0e11020307221120030030a04004402c0079041c0a8001c0c8403201500b04060040c2c40c198019a04d18011100320341c079494490640d00042c07c030a002e042c583c4c00119141c50070308514142111074001e42c0340d40c907020604001c409080c000c0c184d550320705464034a010209904e00411400307a204003000404150100d80e4030001058000c620100350080c9030702d4034a402d0300d03075101d020f0000300075001310000c105c0542c0c01900075004680c090020744510010240400d5107400361405910781c068000c0c004510100d00c6081b82410b1039041000312860304503c428028500001c00c030450781000203c880c106524145800707a250484200d0b4004022002119035a00d030074016802110704005001c54100c807840d2450b046a40700c180d00c902c0d001070f0020a09051038540000740030551700103010540b0314100d030f4030030300c00c04807440c1c200448503080400445441c1105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 492489793 1250 492488543 492488603
    0x30e010c022e0209060a0207082107121b050601081510060c0515090a0218070e0603060301060e1f06111c03020409140603060604060e18011506030608070b0403 70
    0x50b9080c01381c81c10b142c80c2c60000f4000b10b010340d0020001031385808811460b181e14001e01c4000a040a11a441c15034a1082610300c440d51000c4544650059140c00311586c107034800b402c50721000350442600030700c000410108d043e2101c440c240c0301000041001e250300d60a007952042254058030700d08205242c03090003039443e014810001e0f03d285a9101c0400003849109a4603801281c121403110f50451800b0b00342440a248414003046882ca8104809400781d01d040b2450307030060706e0000000e000d0369000c0d44402c014204110f400d40481c21700050710403c0c003143c5108035007401801400030521602602e0351519003201c40005102d50105001340c10618010300180d8001e0503002e000210380341d0503c0c0102151420704041c406c0f00d0f03241c02010585002c401070a1580601c2c50400705000c0040f24a0705941d201001852254184d02c45c024101e00415108040144c81030b107084010030550341c0758000c1c9080300c90b080204c0b03d85a840300440d00452247e031000074481240c0c08a0503035840c6042c003400500d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 492491043 1250 492489793 492489883
    0x80a03050412020f0901150306050f1309060e0a060504050f03030405190804180c030c0305130609020a03020d213e0610050301150501170a020405040c030e010c02 71
    0x600c4d21083c0100391090020381024542200e1039005104151b807502c103007001048215142c03032030100d00c44c0200b00303400c081045402d090344e216111841480296000103003403e007031001b00c408402d03013800c1c444028030081d1006c030f4180c051042000480341d00041924003403908803020b4140010300c5201d88441040f504001c86500c602030000003885010b00b04a5600080c0c118404903415040e16002011241c40d40007060601d4501014414034200b0145014a102c0d800440080c80c0c01050000071000c104560009511007951400802040000700c4000e09401413400d00c18421411144256141000030383d46809005d05812403503000c229a0300e010358410403107003014001c884030b030340c0190a10504858403500c006440e0004c2040b401d00348100c00059100755a0a40c48c1401c003000281031902c204070030303000008040b011442c0c00000b541203c008280c0104100321245000c07074098060001c07010b80040d15440c8c0002042c01c98000318106183d0a103140582c910140c1c0c0c0001080312100801110305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 492492293 1250 492491043 492491059
    0x6090112110d110f040903140702010e0303070515010807060c08370f020f03030c0702061309051608190c090503191101020f100b041113050a080a0305041202 69
    0x6800e0301c031a4010b00c1058010001281241000024000c10804c0e106816010f01c0c50710b0a0200030a40c401080e00c0003001ca4103441e0b0380e5011030f00040312070f9804440d025034140000a065010002d000a82c2900780c2480c8007011100c0c0e03130b00c4004644510091203083d01103000e1600800001d0300134401414071101800c1700803654041007181c000c45c9103480541c48844691072002500b016004401c810005060344010400e0700700c81d030a815124000075045110908011a1001c1150780d944260b4403140c018582c64001143c0c1c1b1000354010345000c3d1030f6040385809001000040601c03071491240300d2214000d0701d0400640014480c4020032034901a4001c200c400d00340400c25980030f00090302002d02c2d41508600607041c500300714000c060f060311201d0655001208460310800c012441382011030b1285400200074100d0700209024101103440081c4441d8000381c0790b444150f910340f0580c00d031001a04ca69500f152245220756480400070000340214400380070401c00d120305801e600c55030f00e101900b160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 492493543 1250 492492293 492492323
    0xa15060f0c0213021605010b040e0304050a03080904110c01050717041e060608030a18060810031704091b0807051e0306030319080108010e0703080409020a022a010207090506090112 79
    0x805d00290380822589039440f05110481803615000300485524050095450245080d00082c203031021440001c1105d06d0220b078400d0a991260b2142c002040c2c68400300c0d81c2c6070403210240340249000c464020200300040498508184141d054030301c110781c821106818141991500e400110000300115400d549405010880b02c04c2440034044001140e15408200301d00d0091014515000d03030485020048d05d90b00704900c59190030800790880343c01080716414804104d888044034400d54000701c3c03829080440001c803c4407164000300c24040309a56002050325035850450b480e228030b82c8031850034080c00340c2c01c444481030900251b40041c00101180d2521108903d11700b4005c05000710038002c25407200c0100b204c01000e00900b00080080c0d000f1349041c5095594042080c001c0e406106c0c2441d9000c90750601c3d40703008100d1046918048980041003103901c04032641d25000050140e801801110130000389422503004250103054018485183c9a08000101e00401c1c14510196040442a1034103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 492494793 1250 492493543 492493567
    0x103170741030d050109020c03040506180306131211060615070b0408040302030f0106080a030f2106090f050c0a0813081611030a020904060b03150a15060f0c021302 72
    0x241c607108014801440d15903544070507440441d90160b101c00d505a004210f00c10009101008035001d551040364651349685200300d101102c44c0100c03280d26010310601d8248501d01e10507205028199106008224421b076001384100c40c00d0141141400d515800540451218903100c1d4011440e942010326060400341c03581c45a803003401307090b00c06558900340001d046c415030134144102100032031035000920880b40380800e107903034a04000e2000303010030074102c0110341100d00c582d40d25205050a4501f0103283c1c81014039440c0108940d1050910040ca0440100009080380c041c05100d0345280c00d150b4141200c110f02510040002040c0e01e803440c214000440c00283d6120140c216040c07800721142303183d0404e01d42800340c40348228005210f54061f480d40401039850b108500d0b405540503070085401a8003801007407030801c040c44003000c405141c0041040c1d080303056000d400d81d0310749080e11015403076072584c0546a003010300d1800c10024421502c448054200584a1500103900c14070041c68a5801030170 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 492496043 1250 492494793 492494903
    0x31203140c040f0e010e01060509180f0f36010608060405010f0f05060d12030b03120306030d050301050105030103110609060c0a030201060902040b0a030906021207020601031707 78
    0xd0066007080400d050206415202c480c10142a00101c010000e504085e12500b1440c0148100010440009055599a01d401404070001110001564502d080840c102c004c9050100c070400040405040010311000180c500d01541041d11010391a80c04041c6609010f40310049464015640d202c0f480001c49c0c0d00e0412104d07202c1c50241000007182a006031002098504404040358200c1c103180c10b2003450754a406240e4901a4000c1402c0b41110b0040c90a4000d009090380080e458010007040307400c840203403800ac41c40381508a0a60740700c030740460b4054803140420701480f40065003e000610000e918800d0403424004010403543c00e1211000c0040d0035070307100044006140d00440b4940d41019024082c074170191004c048254181414000307c52458041d00555000b010703111401c800c140100c50341203c1c51940820114241d80ca00044044d54640c820b10080f10301101280490301c05110744d80540f014240e200502403401c0711000859050881c921325042e203041c08601c0242e80d5541074401e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 492497293 1250 492496043 492496051
    0x42007060902030a080d200a0c0203120a12060e270a0f060c0206060d12140f0409020702180c04060c1e0b0105190509040305070c090203010b09150c0703120314 70
    0x4072586c0c50036581c800c00240e401000b1800d80058071207001e201c40401443c240d03508601680750208035a449400041d150140344540620802e400080c441070b00c81d40b10000d80900c6182c40c070103000c1035a44a503000501c403c1140d03550910290030500040350854540d01d00100300ca0401100c00e40b00c1203895140c4806010081140c0786035440075803841084d01400801d0340804c04945021000746d00d510f032071411a20400c5034004018503100c4246002039802c01351840b01c580748216644690312168044025400002c040c0d20441c1913200790144040d003501120301c6101d80000356400c0c01d1410b80c0030340e44a4070104040b07a00649080c00790202c54100425069100d00030209407885500d0b0400340500e00410001d900e03103032000c00c0000c0c070081e2a054051600942d2503d0140d50f81d901904080d42d611030300f134100c1c2401e5400000001a07640d215805010341030011981c6443c85562914445102c1c03013130340c10140d46a00400c8081000c141d151503c5804810b49045c0401c400d48000128151078404031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 492498543 1250 492497293 492497303
    0x100905030c071e06020a0b06060a03020d020301031101180303050403020618090a05040c0b04030c0e07050405190306050609010e15300c01050307021e2811042007060902030a 76
    0xd114001d428000107034010004d5001070101c2540e591115035003c5070040c03051380179010000f10000621310036412248100030440085480b0358582c90028000000000d0450004040c0441096404201d0902c070003181d5054540ca85080c0c95542401210740240c1107071300c10411026004405600c8081c080e611421071035000191601d42494804480d00d46600040e003200410310080c00004c50803540c40007a20100c460003151980d4405003241e080c4aaa082039412180071007580c44503000a42030030b01600e108036014002c42e40c3d40d4080c8040003109125003404054807901003807442d20811500001c1600103052401100c8400342c10300b00314542000c59600c40e41c002000c40816400c207020f00702100c042440e005287d41007a0b031000f5600c034055598040c0c200d81d441007294038241c04011494016885189010580c2c000d00d0340e040d1130390490340c010f8401e06031814440940345001c2c8500004c10341031504003000b00500e00018400c0d0b4201c40c9046541e16034070844d803c05a5010411405c203a4414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 492499793 1250 492498543 492498569
    0xc180d1a162610080f0d09051f0507230f0714010c0308091f0b03010c0c1e060f0203040b1f06020606090403030914031911100905030c07 60
    0x10020881c40c441940c0107201045207204900c003102128440d440b020b600c02501070216602c0e038612000640555a00446061007001d00160013030101040180e1070394856141c0c1e0b090565101c040c4821494022560603691040303107100ba4080b800340d80034201d41800750691b031418541894400340440135401054801d0b501403080b002421404201100203409c0e00640640e0000c4075500103415144204401001d10901100017800000300704040d400e40d100301c281100e007449080100307400401c034035a000340c000d5090800410300c4501611407000c03150761214140148103221100782d00e401030300420440c0c0c034945a442d107414600030745c0041c0d80035902440446041d801d1002c241c12800d614003040021011070410104031a94000c80e880b50b02c02d0b030581e45100940d41d80c3c60214000c0101170401007001300da82c4042c49540e400003014109401c00c0007101d95100c611031000356428468416021402c3e4020715007040301d000340340c001218107485001100d0503c4c0d0741088850900c40142c020921181c1d031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 492501043 1250 492499793 492499801
    0xc06040510060501021209040507021903030b01030b011b1b0b0708220312030504030e030105100e090115090c0203090a09020a08010b03090a02211b030d03050c180d1a 73
    0xd02d2080a0040900340000e03d0820800400507607680601d2041503c200c0d61840040c0309130b0b000740020010418081031104410790b8510b0040c00608104a4140c0020b2405240d03130140d5005e0950b41a01582d803152400d0015159546d002c0814009200390b400140326010002d24081c641029244451007241a1501e8011203514540303103401ca4183d2011a034186c01040010542e0b55034000092440f038a40402c060b941c0d0306040c0c8003003451000c00340d0103601c1c0c50104030511250084000603200c020002c3c0c0c1007615007083d0395080c0d60740c80564501000a280041040c516250312040d87c034003044c0140c038102040c07080001e5003405194400150680c0020b40c2000e0303a031340162034601612005070f01c01e00f14244808079a82d40d52501900a02403030403118100c100c08400d140420300c0040f00000c40e0a03101994941c0c074510140001032034000d115501101d00401d00030f02a4500c2101d07500e00d19428040f0034210188108410340350719400482d41221400865505840341d148800c01d0300f045581c500b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 492502293 1250 492501043 492501073
    0x1804050c0108041a070216080a050c0f030309040b0307080f060114150a122706151203140403081201031a270f010e0d02070e0910020309030c060405 65
    0x60300c81606810032560000b0400011415501003406024540c000e0a00d40c0c1c414905915000307841205a0020380c600000003100903002880801aa219800b600c0c055074421b030900810b0250400b210364180c205000c0c804003810180c0c801840d02c02d00804859071a075498041314140504020400303800c4e0400001070104170700010741702000c3c40060b141c154080020040100150240403e04001c10807100310440111003d908058152021a101304d100362855142c414068428242d003100c0f0317076041080d81c0310540200f281850850f1b80e110b82c601403190266504036050040b00d01c0745940d0342410f200c0800807034078041c01b030303310307403003142c020035110f5045051100807401c00040100d1000000b0080140540b4030340e244070a03841c01c0c100804086170344031038224180b401d401a80240c640c0391a40c09100354500090070b00f40600c45400382c450498079822508047e1400701c0d40303641603074005005c0424150050b40107590080c00c810070360b414000006011400c105050340d00b1748944d070052401e0300e0b1110b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 492503543 1250 492502293 492502303
    0xc1509060f070e0625170415030908030c0906070f0f11091611190f1712061c0f030807020706051e090d02060a170109060311130605180405 61
    0x141c114189035040c040c82c2c0b400900c4d1071058107005000ca881e50803001c4999000c00c3c4201802036407003840703e10050383d00007454086070018071448030140d04181140043d5070080c400d020f9015040303860f103403442c0d50304506203805502034000c040d041282041420003145100102003502d40c440c000d0041d2591072801e00ca403c481221441501c40c184440c00c1c8680000444072480f801162404c110140545101000d41061005115076902040c0303604014100070201011841d804d01c9801044103400c42c2035a00100c6005004880c00e004000d00049041460701544051030500c0d01304030703401ca50b0815074950101d6078019804030003184920044c0050242c0500203040580924580f0b2400c1851400802004295404000080f17000006070700450341c440c03c071100c00454000d0089a501d441180c3c00904814003502c103800c10702048e20000c19122400e004210881e81c200100c10200300d031000030041002c0c0e1080882400d1552028001416140d906840241856a841e00c1d0b21619040c24118140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 492504793 1250 492503543 492503551
    0x120102090102010c11190c180e01050a020702030325080f0c060c0c0a0201050c01020c010c050d11090901090216020a18050a050126010f1a01320c1509060f 68
    0x8403980c0d907010315010800151b41140b1001c01140d204c841702c0d141c1044d20084001d50000c2052801c4808102030010082e00042007140c0303440000c00c425901c0702d010b0412030054150007980b40c3c000b00700024106a44c0c03812031041810300d603001c009ca038015a984081550002c102c240c44601c000c18000e1028134180503056208200c825024906524400c02540758441400020f05101000c1034100d001c04095040d202e01a40c02c40003009900ac5c255005421a0080e00c0c5050015081c400408a000c5d0406e065941031540a0043d0900b6400e1100e814082c0d040100c420b030150428004030405030f61001c0d212001000c0b032004401200b844d001c4104113440009010120325406c00f0010041520501d038228512061790308440000285c2c040024007400c004004149c2450901180b032400b07884a80c03208540b180240c0321100e00da0b040c03407080c1d14a4040c000c4181107941a13800b40c85e6181100c440100207240c1c1c00c4056464528204001000200c0c040d580b840c126407050040144015800c82c21a0b08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 492506043 1250 492504793 492504797
    0xf07140414010302030c1c060507031e020f04090c0e15030106030b1203030705030c0409050c0406030c08070909020a0201110f070c050d0809010c0311030a0c0c0909050a0803070c02120102090102010c 87
    0x7a981940c01081d03651240b40d540c1c034007400c0105080d0403daa07180300c0c901c201070f42c483c00c14031a42c1000c07032000700685240302085000140104081844940a108a420035601d00c5100c0741000e25100ba400000c0c007070449044280204402c10946c0c80d911480030a041d06400700c6519125410004020708584a90744041d02500b81d40750b000c0e14a040000981c1d92044062805035640d95070700e0040c103460301841e40030074445400c140c240f01e545038400000c0c03c1550315550342004030b0740680c0320031140c030f100640e040000300e04c00044c14401c0c900760f500203010201141c00007050007103580c9c00225143e80042002e813000400480c4070300c20031404030005001410300310344401001c00980c03100d21244c4103801076141440740a100366005c250007401908800b0030b201c801d981c0c031207070714a2028200041100c82100e10121110011031100e0443c0f091030a00c541003401004d0781f007006d0f03980e00304a074000b904031804e000704204c007140140e0f283e548141c0e01c50a104000340c0c072031031b00744006401d4803195006074017 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 492507293 1250 492506043 492506081
    0x50f0106050a141b060c09040f0c1b02041506090306060b09012a080a02030705070e010b0702060f0f1b070f060507020f0f04111e03040506180f071404 66
    0xb115a03101c09034a07900b003001c0d0812079541000f441d018030f0301e140800c20f04920b40940d104204a28034800054061410f05031001c0c081d86250106c08402c41c2d080800e04401b15032550107580302d0002c046040e03c1501d01c041e000155000503141d140c02442129800200001d11007041801000b615020340c10041070880b09050606178101d001030502203030042d4128000300800c1c000942c180d408421900c00c80d410001c42c983d02d186003c8000e4403580308007401d5481d0301c0755030000a054a1040c880038121072070400210f0070068182d0802c02d40b6402205c648a09800038000020720b2403a020003052008480c81c006603100c0f00344140203007001c0d0603501c01c562030303c2d62001c1004030642103400c132500d841d81207580e03021411107280014a194030302d14440303411610340080501e0729900d0340700804118500d11407204880101010a013a244000c5900900c60780040000c240d10081d003070180030b04480c418054504480c407124840380f6080e03041d40400e04150b40841110040c1c105440b07801e45040c01184410703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 492508543 1250 492507293 492507307
    0x5130212070e1605070f08040501030510080607110f190507080609030f09060c062805010503151b03040f0c0b190e131803110313060305060d050f01050f010605 70
    0x8440aa001007250342d03011075030081035940c91300c140100c0d43e00c180d2100700031850008509044000d5049030041d203020924000109030007030003a940780710032181450014102c554801404442200c0c0005141c00c09101d4421011290f00c010302c0100c1501c040c0d1031440b00000a9418500c1c0360840c030341e0004070079400400c2481400b00010003150084020700b4030385a50f8548034004030360a40315206880805014090a1015802c0031a207400c4800c00c040003031154078000c00ea43e480840700d0a108032a8598061382030080260341d110b801c250702101c5228000b18002c0701c0560100c0039401201c04860206c14003100ca010030a02e080300c00041c01c1807082060810185442c4403280f030400002c942d082c000420f034100001d40c1d41c00035003110403910900c00d003c5094a08030741080d040d041101140460f031a41500540d0010001c10b58202c482c0340c81c1504030052030305005800906028120301c3d0081c20b146010804900204100203807070060740000180c80c5450b600c01d184106e0181c0200080000809c101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 492509793 1250 492508543 492508559
    0x1030f0e101515051e0a121506021f02040302030f060a0c0e0609040e0705031b09060405071d03010207060203040f0606080d0203040b0c0c0a0f0e0a05040f030309060b03010513021207 80
    0x503000f03070507590815580c0c0390700e040008140e421020a00000f040000154521043d500015000d800c074800e8400b40540040c941e0085041c06180c043c0b4001a48070383c100d00c40030080c1060348a95000785c0800146490303180c1d00803a040030110000d5a00642c0140d050102005042c401c80102411902d041c3c1124031400f40000d2070b604c600005144200d813261030740d600c9410184501001840c000b8112a0b1020070341984580100411a03c01d120340004000181179080034050303140300302500d80d01c90302c403401c0c4490301c480822a101901501990309204600020308244002c501641c0241c48040042c0c805140140070b032480350704080c1094003d4030050b030b42d06400206860560b03020030034168803500f610503c14580784202101c5980100c1c030320300000d2031440c07056280c001e0750544600500c0540d1018203040c190384094a0050000180100d45008039109910004a00384540c0b00422091003000010f402d441003614100452000c4840e100c0851902c840100e14850344a406880142c4c502168 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 492511043 1250 492509793 492509819
    0x100b0d02280503010605010e220c0f181217071a0103050d020c060d0f090b0106050a02060a061d0703091709030706080f01060e0114040603021201141e01030f0e1015 72
    0x1406820300c0d009c020b00c1000c0d12142c8100d031419000301003000d00c0b45c19000038900d1031000741c00b402180c400445412422042642c44e0180e421031110201030002c4e5580b43c542a400162090000b02000e000b4200018541070024030407040b6810340c408254154100745040020005c00d80d4259031040350090b0f51a115142990428582c030100051034004558010001c2c0007014030041c00e05600400100c1d4558211001e0b1506880a41c01c444203550350780d01e0101103c169000e0062460155040e04020004103a041940710043d49404a105030003660380100c10b02e4003600e110264103010540780070608040108900900c03191400c80074a0500664055000d40b042c0030354020810041c21400041e400303802d5407640003917070480369695640c0d0344600a0094019031181c0010784440c100002d042c40c80420100001d1000401880445080c0040c080c00d401c1c2e058069418035850b80c1d211000e03000203101e6050b01c0c0441901a050003214405164210740d00010005000c8500c4007052041c8400030321 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 492512293 1250 492511043 492511067
    0x60106142d0c030c0a0302010c170604020d0605090405071802160b0411180601091205150a0b0a0e0a060e100311030316060b010908030c100b0d0228050301060501 71
    0x850700a8265110000001c5101e070b02e04042d034a00c80050031402c0c0d540002034000070940a40e00030403011340c038076004880f03e07603990540d640c003c4021000325000749001c0c0d004007046010500c0000f03100360385901240040c0f008139000d4a0390380180380c003041420130a0342038003449507584108503c0d0200800504c0040c840c11075001d05155600c0b0002800c002c0d41080d00a41400000d21402e5100a164060150640c0440700140040c0308102c0c001005c14405c4421026a82d1110242611340308440c0307806104013005242000751a1180c03c084241d40718903603d00080c003208444855945445640103060f02c0c40c40c1c0c07190710415074060400c01100b806a0260003582d500c509140132034680640068507500840401030b1241d0f8070622424104200d0358403042c4920001c0e02c510241c00c0c2d407021402d46034090715046080a4001c07007005c0b40c2d205010b600c081403030b100051104141070007a4000c1110b00308401403903d8038400e920004030801c0c0c3c03001d03240300041500310000c0c0407060a00b0300003000c45c00002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 492513543 1250 492512293 492512347
    0xb07110616140d0f0519110405010f0806010306180e12090105041215060b0414031b1014040e090f0304030218060111010504080405040e0f07061b0605010806010614 72
    0x4100708501c480d681d080152404503100040c0172030700708041c10026030200d00351342181181c50003454664a41c1401e050700c6c120366050310781d94070b810120442564080001001c2070b042681c0c45001103640b800640c00e8003980913071000c0002d105044100035034034090004480210200d03040c003050000c0d80e845000c55041d02c1b0300c95903c44104c0f803149001107001401d0990302c0640c0303080c880082171090001001d8001c680b0032050320441101a101816181c1014541c40719140c2c4d40d191203080345003000038802c07803141d4051030140701210b001c03082140550000c0c1c10100b520b91101c0c2c00e04c010100c0400011980c03003da00c000d5445d0a01d0760340058071581c050362640048070005000503080da801602c03039030804102200244102d03d890b2500104c41d600c039004a40c0315900d881084001e0900004004c1d0a0940c4940103120343c1d41415000e441b6007101100562490f00071721080800a419406000c0c0248282001040c240d41400006422005400040d00607050107008070303080e80354a0030054001d02c940c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 492514793 1250 492513543 492513547
    0x11803060c11030a0e15070c050f0303040b130509011a03150f040c0f1b0b010506030901150609031203090809010807030e07080c090603070e041101020a0b0711061614 73
    0x1c0a07a00382031450855480c50001040e11040a600420100446001201d0100d44808001000b403030601600c1d00250405030040010f02a0342002c0000fa950300100404907801c260342d07040c0207006030340010f0000c125016070a10030880b80c180b2400c050702401801200700041510384401080c203010041a42c40d4156840100003401d44500141c030b85103a0000d00240107021310501d0103802000c800d8034600029205c0071940e80c4680c0550340c201595640110600302c1c0f0313441c1504200300f0303030409005110135540e5035480020500c084000540280030039110300407598034500b0b1080c401b060782c403184004d1509010000740000d80e171404458110409007007502103034450f19000c1700240204141c2818510540c030000c40d00400010303049503015401c5606030144e907a61418191941e0307051084940001c3c0c00300c0401c00050000d84100480881841190200c0c1d03450b44130191a68400d544140100d0140441c54200080910000e503100d460f001d840344c0c010140aa00038030421349039201c400c0070500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 492516043 1250 492514793 492514811
    0x609180b0a090c0e010801090c0801050c071104020906030f010e0c0906040504051e01090f0b0418030c0809060403030314160e0105070c080d0e240a0c02060912010b0f01180306 77
    0x9103d0380e40c0c0a0300d040207520030f1035a11030000307900070812400281d1f002d0000704000900c04105005040c820380031442121305003c082d941d4a1803107403480c100582d02035020312a201440d15481c02451054400307140400f81949004c03280130103580090404265072004000b800e1240d1210030894084035800e60300021160784503120f04442c40e5500340c40b0303051540460000910714502e034100c45440e5807220001c002a4a08000b008101c0e00010a0800840da00380c0c8180082805440d4222040c2e004480580c40c2101c010000f039070550040d001280840c1e07480c2107079029180c1d982d002d541c1c048000b140c048a1003060401c060182c485040c0c1c01410800d0000d010800c00c0907941c2901b0050482c6012038a100c0000030001d0f101400303001c401d9002e11a0003008160b881b00c41c000c800c00100180406a10300103518001300c0d01d502501c201682c01c0700040081c0101511503c0d900c1011032000302c00000c40319001010005c2c4803075001e4015040210002c2c0c81418265040030650441c1d038003400c0080c007030034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 492517293 1250 492516043 492516053
    0xa03181d040210030f09060b03070b041a0a021c08010e0a05060906061818090f0d0e040203040c0503030a0e01030e030c10020325020703051c08060f1201020403060609180b0a09 77
    0x884107010001700341424084005c020003900319503040300040f01030300d100d10340b11228100280280d219142c0c1d00c449002007907500c008500e0060400b042075205958420005010400c010002ea080d187c00240e6980d004010124a08c80010b402c001001c1c0d0038851820208001642003c026180f40d00c00d00300002c42a0403a805403014810140019040800d0b40c02003d01c0c0792040c0004803040c950034081c2c400180c10290011a8031000d406098035000d10001c0340764140002900002c0045800010850011070f999500b00040c0c10301f624595551013a554030707940010709440a802d40800c46a200780644a6001808102c889011141c007800680303994800081c111340001d0175000d03041d0031007801c00d0b0a0315154041801d0040d01e0261080742d000703400c0c0852449140940c4c02c03000001032254008100c003490503141000c928880105110103854800c400142242d000d584115245a0345144c2042030500a000b00002096020f0104c01d0140d440d40b41c150200100400c0741d140c242d9501e5000341001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 492518543 1250 492517293 492517301
    0x105040305032b062301020d020d0f1404090f0f020a0c0b062103190804030e010f0c0b130201140403050303011a041203080901151503020c030c0a03181d04021003 71
    0x30b40c2ca6909110351681c800b02c00a50807120030070300170a0900d041104074a075000207032043c04065654000e00c0640340c13400d01200d1082003c02003000300401e90b405d014074810354101800141c1100301d00001c085c41d00b103002c20200c0328240c1c051b4003040c1c0140700c80000b05400c10120100340390004805400c1da0b40314400a00819808a1000c0c0d07045e884203110494194000050700b0040307058002c03c4854852600281d4150301c088500400007951246541c49035489030070007030300c00070541c2081d04006465548110625030201c420780001842a01c4c2001550f9020580c60400d08522056034641401c5481d26500c07032005000b062255a408903440e09076115400448000302203191001d012101140350080034400b095580c007032250700780a000a031307079810f00d00c020b81296641059512802c00080080d0301030b42000400b102140414407400180f681c0910000c4e00052090b07440300400207a0400501210440d50404000760142a0011080c0d445141500fa04035404860508204240d00001c034041c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 492519793 1250 492518543 492518617
    0xd0f0204030213061a2506020c1c02071208030a05101d0601090803120a0b040f09051e0f07061b0516170d02060a0207031112030f06010504030503 64
    0x100300391030880c0d950050b044d44000e0682d0380d507071100c95055200f4003c5084030301841c0c02c86603441440352176140603d42c050403490109889a10f0160505d641038010302e040002c2c0c0c0c42c800b00142543c2d1080340000b0b505101c3d4001500440515181c20841919420b01c11b0100070822070302540d0703d501180c0d040b000b8030750800051401001c41c00c102110180e0040c100c480959003030b030104003c200c0c0460b0021020050786c40795029003c40d500196510010f002c06045a00e01854001e90b81f0f0802201e000c443d0301a5502e08c0e80a8401030140c07202c8000007110308610b035a02c54070150440410740c036910002181d103904540c000e24011101103602115004003403201c6000400c00c0c0700d010b4180c2000b6000f104420202c6104900340341c882c00c040c2c81c1858407220311010910050700b01c47c0010306601060b502900250b8001e00e0410302d00740745002c01c54039210301008404032000c00031080016039954101860740c405001c0c41c220b8242031940e55516568040c0104860300f607002c032080300e240008902c400c4440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 492521043 1250 492519793 492519799
    0x606071a1b030c1c0b1e120706030204051005040f03110619360308071104050f240a0504020a110712020a0902070206120c040306051e16050d0f02040302 67
    0x15030f040c020302c5411180c0c0300c0c1c10b04a40403c60000034640c0f00c515440b428586100c05003084510184518a1304050192080440e034410050000181c002d8010070400d00506165200143e403a4288020848462000c0ca0b808040000c01c0109201d00044410b94200300eaa0050202042080c8d141c00140140240703480b116684036114941e542e0701c1d40c00011080d1101030310b03420903c0110704074407569165030310050621000810410410002e0300c0d800003002c21a00864800d01e0591544000900380c501c1620019454401c1d4030070700c04000b90030100c03603100d2a1000d840b074903c0300e07003940400c1544000b40720380b500c40c80c0c0c086007080b03010b800b030351404020042180a0320b1a050300c8031075102c0360f0181c80e181a8001c0d8501c2c1c0002c50801030500c00c481d01302e9001130000742403d1809180130307038858000704000c143c1002404008000b039500c2c0199400b54040300c1080c01118174104d04a410300c080101001c12142840040f82c040903003110494a6440030300801203a10480c2e501d00c4000383c07299900081d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 492522293 1250 492521043 492521047
    0x60a0f141207080601090b0415090b0a08061908120901020118050f0f010b060d0902150706021809070e014a010504080c01080618130303050606071a1b 66
    0x441c5598041c541403050b0700315158803466444000045810350502e0040c0c0307080010030041805a202512030080711010289016041c040d100d12158001c0e4105c150408086140c60042c80030f58907041c00746500503202040c40d0641949400301043d80d800120405840c011400111000982d10031742200080210310300315005050070503e80f40d60b0b40c0c100c03403000d85400e0080c07070164600d41106004582d0746890051180d0706102e2403101c540028400c1c0c0030100e0340001080748a261801801010702070050140d540141c468682261504c44945820001c130b10584e020310400807804d0304081070921164080c81d0140c0e20344d6020f160141e0841d000106940c2d0540f80c0c50001203020003400401100c5044100c2d40d0b405440c90f01c0040d1401c1c0158081d181ca243c03c0140c4c0408039500c00e03040298403d00041280c1543c07010280c184000c45420303242c2d022989000c0c2003079030a05400d4000c29401c0841501d169140c01c0664445480e0105403541e06130b6107010f1003010400c20291444070100c81d00340700b40c84d55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 492523543 1250 492522293 492522307
    0x8130f0b09010e070302090610020a1a060a0501082701020904020408010e10111204060b2d06041208160b09030a0f02121c090c08101406060a0f14 64
    0x40038030181110380316410341c20710078852800c0c500428500304a90307015141c00e080d0348400c003c200d0354000b24a41e00c030451060038100800304003480c04160041078290068034042c2840810700c800c1d02181d80119051001c501c090105885c0300f5504001b952944c0d5200501111040c081c070383c003903c640d600441d402400400d01250441c010340c020484030f40c4130400c940301d00c1c04280d051b1003601c0c0c0c9104440000403040c88000c007500360f01c40034103910038403a00c80010401640c0c030016a407010f8400001c5085c1003d201141000500036020a2510b40200e131054202850300154403059412000000e00b1102c0c0804e01803181c9003a0421215802d50040e82250b152031301404103503881d000308044038006010b07002040781e02d6002181c10043d00203925189850801c3c07082c10404040a030250041c102a42c440ea8903020510480c810000703003e55501a20503002404129801e40f407016111f60035034a544814000159100d1045800000c0c441c1000e414228007000261040d000010782d24442a00025004c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 492524793 1250 492523543 492523553
    0x30e190b0c100b1801051512100608090705130209010e0d08070b0a0c0203030a0911090109020406020d0206370603060c081302030a0b13020303120601092408130f 71
    0xd00740d0600d07480003040100d0f85030040108160403504804810b83c000350040c8020300f0003201c200d08511000a03460b00d4124a903c00c5003004030105da09440e880c14500090003025400048240c101103d0002003200c10706150010340529221041442c8150380060714008a0740980320959142c10010042c0d40c441c091800c2c4502c080d0300865040350b101070a1030004049080741e20039404200002d600a504556503c0c4602006204150003610b01c5140441101d025a03036190700640a80a01c9038003503121032410f50064540800003d0070300c1950455403c04c1003043e904544212403000b6401804060040311040401c3d00c91501d41255030141040c4003c001d100164202c45d5a1040c40e648041e000d0b40e0f15809071101e00210017009515800601409010032403141c0b909030024100302400b104102240d00007460740c0d004011480100e061002007000641c1c0008012005190410130148802d0358107a00019002101c1c0515003804095000708500d0a2125500c03540140d001d400ca0060400c00d0a103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 492526043 1250 492524793 492524803
    0x2f0c0f03030112120203030c0a030513060203151e130207030e03070306060f060f0804060b130218120d0c030f0e060a0201020d050a063506070f08070c030e190b0c 71
    0xb52005002c420041040d130b403000040f42c1c81000c46008081c00e1040b6010100e020703140c0640032080d00210b440158010030514070007940501854103185c2c82e46140e4000f4000320001101d03403212407500244403d0380c182c840343c5800505801b10000180d8900c01e40c54203403a03044c0013004242d01840380d5880071040100640c010f00a8072009480024010380c0d92104945045a070440040020001c074003040005e03030070f40c00c50708240100401e000a81450b400000003240c0204241c0490042680c1c0c0858550a0450800d07102c807074400054101079601100240c80c00c00c505000a00700b050a401d6a404507100703680204010a000f459190b540d44110340c009d010790050980c1e908500d281401041c0c40714020b00c20030007190410311410380300c4c400c0300c0c0355001502a80501c11480140c1ca8070240d2450780140300035845042d09440e92228040f05c1c507801401c5140040601003408205600d40b00400d8200d03001e03075200d190440c1c08a07a070b0a04070a00880d100400d074050800344401103590b401107000429 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 492527293 1250 492526043 492526079
    0x91305060424060b0f07050c041109040b04050601020a030f0e061908130c05100201020f03010e040506010e040203070909020d0b07020f0f0114070e01090e04060b01032f0c0f030301 79
    0x2042c0d524240254807004100c941c20301c529481d0341d00420040e01d00d6241d00010389151030080342a82e105060010100701540c01c05884400800c100007001d07034035407030302e845240040c4009803402c003d2440c0110003c1d6031078094660150610002000007032500380308903003909010201170a45a00c9401e50401c0400481d8007820090104405c007000400b005482a5941d00d0160001c2001c0e200700d14080c01d0000d0402d602080701c0c21550204024a403909400d00154002c0148241c2507809250604145007001c4040e0403006036070b4140d00a11000da070b400240c28040c0c60503c0c40004d080e41c40e0348000f6a5a42c0e590704000c1030076005a08000d071103500070070344182c2001010b00340c480b420503500e0703110301300c60956444101080f854000300d02c945100b030191006420041c18080c81264540c3c2c803488039040704480480d0120340300c4078100c8281d40e0600411030400013a003618000c551082d0510441100c107370b40032a00060740882c600039011000c110031045501b2200551742d80c0d58413a0311a11105582d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 492528543 1250 492527293 492527333
    0x1509090f171804050609180c1c0309050d080702061308010f0504050c100519031e02041d04081209030904090c0f120b07110a15150f0b090913050604 65
    0x20782c081841e4140390059034881d20b0300078402200c99440c212540b4049940b00215112481810707802602a200d40c4900c1456450100407601d00a0242c4ac00504000d225004140120304c00318001d40022440304c2a601e480340e044131510340740d20152031092003000c800c0d070203040c0030341c2014042c40c448842039010341d00581c001c0041e2800742a03000c044c0701c04420741d90403c100013142081172610001480c0c1d40002d0592152401191400f0721040010420742c0381e0101d242056400130b0700708942c80e61060244102850030070001d059103040e403108035480c0129005c45e0800c40e0a000001c00d1040c091049801043e0024410000e06c105418064020f5855018010418000c4074000c925648001c00c01f00d12a42d000d2078400781669405401c0301c50841c112041c004501c01c2c10000c400080341e13030300505941c0c00500710010b00d40c1c0f04a021484440c84a60000c8440440080d05024954a0740c04031840d03136100343c40d0f10240b901c8040b40d880c01080389132005071150003824180b20400c20301c103002c150820904 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 492529793 1250 492528543 492528577
    0x209071101050f07020d0305130b0906090714060703080a0f020d0b031015121a1e1003110402071a01030c0302270f09010f0606030f06091509090f17 65
    0x700500700f01c420401e407041005680030003641c8078864800d03001254000c3e900c62158250440d07039a00c030750040e2000ea03802006134010f2030401c00c0c0c80d4070030000030303009054148801130300d241c0010200d00355100d299805000c005c0e00000103400407a554000500c0e00c02d00900c210f41c0c4000308410f6400414141130190712034011014113910280ca0b5011300900100c5401201040a15040c0148031a10b6008400c41d40200a82c0400080850401800303110b15010b080112b68141c842d400380c9071900c001445482d400545c2c50091020501c0d5008070801880165801071f0b89054604042c211030000150000ca0300345c041c0000700c2048026490f60b81200c3c82075401e03080303240c98640d41500800061500300c030412040c90002d039542c48024559a00104100000561056110051020ba034400c0d08040c000c1780d1182000410091280b191500425100710200040903244201c01400500341c440c19005a031107850060511217482d10010080d036101700300420807010b0380800c9029400c401e003900c54540f81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 492531043 1250 492529793 492529801
    0x703110109080615041806020304060911010f0f2318010905060415080c070b131104090b0627130b06150901080c1905090306010b04050a140607020907110105 69
    0x2c0068103074003444411030f0018448105406000060840e00b0940802d4260401280302243d09440258003c0340140740210310811a828020340d03000c1100c01e45d0b8108002c203481002541d07440301e064009002146040082103405010031041c1c22003241e03a4040324100000d10214689101089801001c000e03200c00c01410307910300030020180214030403420761003860310340040e9803803141c0011a40201c0c0b4888480c1401c44075145c20b4001d5008455640300c3c8040c0389240310501102c481d9072004500101c400303002026499482c40112100036080da40191260000084056810b44461070312905295042e400780c50300d4004207100c5805074505503005402c1c1c5002c03030401d08102641111014501d03d81c5460850f089004507a501c40040403900300b2031051180d10806250ba509003c0000f0060355640d8883c0c10200c101030070300c801a4020300c194141000304102c10740f10704880d2011203801d0880189036211100c0494070364820880e000f507008011000700f040440e001140c134441046000000c214542d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 492532293 1250 492531043 492531059
    0x105010f081f0b121b180a0906032906031009020a0519170a0b0105060a09030507080106050120150a0e0139140c070801020c1c02120304230703110109 66
    0x21044145520100100900417600000c1c5902048034000a407c40c070890740d85200c4081100c01c2600102c4840310f046141c1850215040101030b4040da80d104078910314204480001d550302c140f01e0000c49020380707409482c0c0540d607980003c0d000921015060031426401d104a81c140203000b405030b0070071102034a80da0b2441040001301d4411540c0c1c400b1911015034200010000d9580000308424100101018040001401880000010880d01e000407031030504002c00500381050046c40142c140203c0d101c0e0041d0400001802ca82c403c3c030032640103103075403601c1080780c0c06055094400d946a60070849440e600d51404074258103013103103024000e04d011152204044000801202046c0085c0100d050030a408542500034064101600c044030409961041c40b642a6007003503121401981141700280c19030400d00321490024012072014014045400d07008021034040a803003d08000071f1001481c40c0355010103200d12001d6240403c84001e81c2d583d280034000c00c01c0308100280026082c40c00029016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 492533543 1250 492532293 492532321
    0x21b0604080d020d0209040e0f0c0f060a0c02151201050f090f0105010f1812020103050c032a09120601050118140d030c0b01030c0311090105010f081f0b12 68
    0x5907020001c03518007410040c015010307401102d019140680e017001b00303054075600e620503d05000340f441d01501c2003006065103541040150280c0d82c0c000c0030015a45d8481b03a689004580189607103003420022244140007140f607003078010392502c0300345000241c180300600d102d841c054120740c42160301242120280c014410300d65030070340340080d04182d10702c018001e541c05421280c003404030038a4290707203400b1049040710118540f98010f580364103601911070103659050003216440f017141d5211500e1400c00c02c0c900342d00441d07003640c2805d0022200c190410301c804010201c81040c10000d0078010514100d001041d22103000384160307400705451030b000d1026580704205080c01c0360044407500607000008401c0c41084103a03241c040f010441002c1c100c900290400c1c44242c080d500880b40401464298075040e0801d00d0109a00d030310a030306a00040003e40c0c0d022018203410b0344c0c5458141c0e400d850300e03014018a400c1c03401d1441046243d000c40842c180c114000035184c8040b500b142c1c00c01e1a06d8100e02c0032178071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 492534793 1250 492533543 492533551
    0xa1d04260319020a081626090606010c050a12090509070305070e030615060d1d06070201060b030c03040809040f06120204050f010f0303200d090806070906050301290d021b06 76
    0x1c1070304840020404886d030401d0840c0f140131400c165034001d80d50052a40ea0100d024403148107110f000c000d22082c001e040141c0741d440380081c02c1c481c82d504603035110103907110201180284481c40402500070f1051040700c0600007400082d00b004010f04200c9030150142c1f07411a14040011001c18000030b661030001800350044070a404455a8031200d5801e0046650144038407103083c1d03844400aa202140480c0c1c07505200d100030b40544070b41e040c03c3c8402400c0d00c00f82c2c4d10403243c2d0081070090000917113a020440e03401641c088140d0740e1b9207520b81c02280140115082920280740341510018005401101e0541c495101301c0301000655111681001200d00a004065009505490900019001300e4030074048407070f1050540c140b044070881030b5280c800b041604200241c0035030020000c00360308000e829045106400c103004090b08140008010b40414480e5140420761004900c80001261800c0d4075182d41c1c00c0c010301d0b070340c16840d00c440d03020794000c00110a203685440d1a0a00c05400464030383d000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 492536043 1250 492534793 492534797
    0x602010506041116020d02030d030c02100911040507020a022d0301141b070605070c12030b0d020f01031103040602090a0807080c01051803031b0c0a1d04260319020a 72
    0x40c4240b032074003100701c41302c9010100d0700003d800c520400941d5041240300500903569501041e0324460420081c141802c0705580884a400c04107082d000403010780402c4070401090354005034554803075200b24541155140040e400104050450303488184101a80f0000c1c1d03020420328000c40038580c24142242c0720485450a0882d2410100e14010103014140503100012040303d410f2803900c1d240c503070486030155525800302c0c008614401c20000514448030245605040400c076218243d00420210710041d10000d1182c01c10441d0584545e009a01401060081e110020b480e0301e803518104000b9440130762014800c08581030000344080c0d002400009442e2200d003c3c20603013221000545898000850408400c0c0c0d03403900e4006a40c07002c00142c040c003074000a141c403108024003681410305030031410081c06102d00d40814405da00d00d482c204014503120240181c1c1039580c508080d00c0100f08610800c4802507002d05100f20511b0b01c0002d14040d1000485c5a485001000b1005049120f01d14603000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 492537293 1250 492536043 492536047
    0x20414090d020f3a02060405121908040606080708070305070b0c0a15021c1b020f0c12030903062502210306010e040c1d030f060c0f0c100606020105060411 68
    0x994604084020613120702e101410101c80c0005807070b130b1054000741060050f44003e04001c03e101080010b550500c410301040c1d450044403100950040119031050400d0140708400b140030802e080e801b20004280800c182c40c101c6807951819901d485a0384002d0300c45100d40d406c08550011007000f15070090750001d00414826403d5036990559940c81007a001400e42e00780301340c01c440255007484040d804502a00040e4010382070514120500c018590700045501c100c07040c091107040051808010403081b0341655450341c00360692480c512464404a03018055002070000740040b03901040290240c42481486080003410700300d0b030f034100c4c204c55080f0040814403590320030010071b80210340141d4189003441c043d01d450700c0401c06442c50301da845c6000070400981d120660170300c07454445218000700c01a10230304030000c00307140d50b9290142548850410008115400c1114a005ca034040080714055401110041081d603000b032a191091101650805002407082d203000d1040340911603040f01c00d18 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 492538543 1250 492537293 492537313
    0xf1a130608130203030a030f150b310305030304150c080103020f0105070c1e050f0f04020a0225031a1306020904020909010e041101021f110403020414090d020f 70
    0xc51a0380702500040021400072154400342e103040c0000d0000c044a5140410b02d11404039500c001c80c0c0041024284010360403006112500e0719004039003052401d00441c081424044d01d2030504a802d500c0b00707184107001031400100b00000400030754452802100302041c5c410f0614510020f4540d00c2030112700082200b00148014580945000304d8810185403007410403000c1e94400400c40c200341c005900800d194441090a2a00700c7e401300c1c054041659000d1000d00300f030b0041100114030402c114421070700469000700c2180b003000384042d05940f56402c22140f01b0040303503d42600c400345c00706580741d0a940002c1c00e160501c0071401c5014242c12950b00c180d140f1162600c40082d0800c03010341c0d074000c2c1c0030448032100756611841640071309030051484030f280c00c0c5442d013000c1c00240d03194024150b402c00222907a00c00d90b0f95402032040f070003d40000c0f5103803440b6411841c031f600c29608001d600900c0d2258103000ca03051100000e200d203520300100c03042c1000803602a03030b58458400b0b000c14a940400030070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492539793 1250 492538543 492538547
    0x6101d0907031e06140a0513050a020702030d05030604060f030305090108070207090e030c060702010504020d17090402031905090f070303030b0d0c030305070308130b0103020402031e010f1a1306 85
    0x21035205401d49000201d0507240108820740725039103142401010386909041c0074602480c041c546070307803008a805414032440d08001c54154010105051009541c6070000b650701c501075011209100d500070161404c000d41c0310b401500607082500e05501070361402d040403c4c10b49550801c4400da07609515003504201d00c00004490a00b0001c0c0304004502400000180c0301c01c083c002d04803040c200b10080c54945c003c0d45120347ca0418002c3c1110110380c1000d00f8000940c5a606210510507000103514102c14014115210303140324445034207402a200000b0414500b6035515146046900054140600d840b114182555140d1500219006802c0001c080001901941c441b018210025106403141e039020344a510000d102e680c4150f010910000c0d01d031040561115100350b010010224240d0440410f8036403907409401404028000da40c00400305d00c004d82c84520036101d04014884420711580c503001078060100c010b01c2110110b0451455132491039120307105544004003155640d01c400e81c540981 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492541043 1250 492539793 492539809
    0xf02101707020d18050f10030204050d0303050603011514010c0f05030301090c08100f03082215111902010311041203050a0809190219050301050f06101d 67
    0x111505100c0c4441022411524030a0068800d11081d0040c1c00d036000384110181c15219503080c80c8800711180f1109001d280d545984010b58550207640c400740303010074160264024401c0390041342c1c3c010101c8824408159040e0031040c42614290700a0000510489200c4980e41450045405100c001c100c8903c141d4892131980e5400b500450307500d004148280c89042c01e550083c1c0014501a4a440c0d2201c80700b03410803442d85d0400005d04031102854035109141d00392034280e00000304200000107440d18441e9060102440000d0740c00300c40008103503540c00c41c02c8241800a540c1003c40e410150000a82d00046520880c490542e03100402000d003c1c5c0c0114014540503c3d13603002c000c0117000204500414005c0f101425119495082d9640001031011b0101100207044d40c0f003640c045106d50000014140c24000c01642c1a29401c0d00e684511f0040c0301804c07010780000d9055860b0004014101702c12030401ca0042c041500e206107480380f020001c858103c2440700103190182c241030303201c070f850a03d208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492542293 1250 492541043 492541069
    0x91106031003020603010b030a15060906231b0d0c0206220e1501030b06160b0c0906070303091e0503160302010b09011401110715081e040b040308010e040f02 69
    0x46207000070303125800034083c0e030400e811401c20114084108555101d85104000007030038283d0070940039a00c0d009008150310309c6070190504020b48181d880074081e14040396048600c1090000ca51649030110f040409441060f0b60803074523100f0030340c0114445028030031666040d900500010b142c001079602800440002d01e03103c0c3e9036900781c02c40004441400c10001c4c4d001e40c0710040d030041da101c05280010141c40390a0801d0b441200100b10320414418001e80500300f580d84140c003945c46984c1c00403071007028024040c00307070f0300032170300140000405078994000040f60f807003120300c9000e0f0800c1243c100a4080c060100800355071080003044848420740c01c00340380c481d10900c00030030405a2080410050329007a0b10003820f18420204000c01580c0208541003000c0d1a10000d00b00b2074034040082001c100161204028031100d003000c40d00d44045000c00807012503166501d1045400e280c50604060380046400f81c4c00280030b0030021911740880140d040c021500200d104a2040c41d0b0340801c0901d980a00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492543543 1250 492542293 492542311
    0xc010c0203071a030a0623010c030c02060d020c06010b07080901180f0909020f011713050307060e0303180a03020709180b0c040501110c0d110a0819020a060309110603 73
    0x2100028506003010000440124112070f440d00c90405a40e074406503509a0000340726204070541c80703c40300440d00a240c01403102440c00c0a81490141000c1d114411a10401794100320002011101c0d610301d50001c01c138040307602d02107520aa80e03130002c0074860302540100520251040080d0801d5600c48c210081d11300d20040c48801a45903140e0440054854540c4800b0b9030710344510080c0154070703020041c5e8501c80d5080c2440d1700c22038058400004000d40060103040550100130944061100030000d6428541d41b00b0420860100300300642581e0780c0084406101b0007140d107010b00080742d004a80200c0306903154008003042030400d211003001d0814081c5090801c407040e1002004968091388150244581e146010340e43c074202000184208103070168144168410b10010b50541c03181c00c000401c0680060003c030701c0c0f09187d00092500d031034a0348050600e1061016401240f50114010413149100b29404100366594120986c290b40741c6c0c607006000050003903071030101d03030a01ea0004c0d50f00034011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492544793 1250 492543543 492543553
    0x603150203071b060c08060f0d080f0408010f1506110627010911090a0e071a0903030705010b030601240c0602040b0409050a06080f071205190f02010906050a020c010c0203 75
    0x83d040350103400203002e105440640c1c0352004040100c2e041a00950080010743e145890231040744081000703154000d000400c80350001400401110382032041e20050040000280301103001d0101c40c00180c0700d02c9440945001d10400001005800b950041c41a010600e015007455952900c140c0c4030100309604190300221030401c1540e04440a10407501010321456018032945010020301c4811140104001405858800706040c00300700010300cac1c2c04445540c2c2128802034103040c5440a170303018442c40c581d0940320201784e444c1000419080b085440e40e0640031144140c0c0c0c0d071424070b030408000801700700da88030001c902500e0040c4150f1031400030342d00902015181550782c01509905501a5200880680e6100b06021010009019840c000c01020004040d40842029096190900c42c4528114840c5045012040190601c41e019841258002d808070352100340c00c2001d2500c4031100100e00240e410100401d0f0a03005509484800c2516802031640022510045d47c040003c04402c3ea414400e07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492546043 1250 492544793 492544817
    0xf0102210a0c0c0b12010e070e0909010b06130905060904020a0509090a050d0909060f03020f0603100906120302010c08072a060e0a0c090e190614180c04060315020307 73
    0x100102c601c0003803082e0f9810b107585d108102c081c0000c2c040c068100900003200705091000466200d401008025002c0381c0c000102d448164295004001e070100c42030b0450760100ba030700b04c54444424100308803004100207001700d5032200d040052010b8100c3d00290702400f9504103000d40e041c0181c00e00e6019440c5411200d039012103885252030046600900d9001610980c424841c0c0600390203540000d02ca0800141052070440d07001034464590701141f5402107602000241c802c0c104030038100000c1036000b07010820141c0380d0300c03c0240051754a0080d00590300340315008000a200f810103520498650740e0b580c0300403010b94486c1a0600c0c031403101107200f8520002c01008100c032807140c200e1010031100181042c003643c0c54159040390742c03a807000600c0d51500c0c140744100f00c0d02160418244179804821010b00c42c851400c400200001d040000f10f05000d8010005911402c07841c6d020ba000b50391040300e032802500350400013540c680b070000806110ba07400f003000071011140c000d03681150701c41c1011242010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492547293 1250 492546043 492546053
    0x90903020f06041101021207170f040902040b0a09050f0307030308060d06020c010902013c0c0516030201080a090c030204020901020a05060c0301180b030d120f0204060302090f0102210a0c 82
    0x4401c1d6030070384203001c0603c0b40c220151b80400120164840c1c5480c280d080800d51b032a0400000712903030a03a041c1c4040025542004440c51003110f0117800305402c21520341c2d445400c000c040b60030940c9240041240440c001c651f17440e00740c0b240440303800c0c010020b005c0d4030b0440d9021911000301400c000d8004400100640005003540082c00c0c500742d006000140c00b000f9400014410721a80c00b090102c08201a44c408400d610603840d8080365292044c5c3c00110403026200312201107803120013800034029034202c26800c5950040b8981102d00036600e0071055104d00c4c100d00c00316500940018801c42d0303045010001800c154014082010301401a00d03403019454a405007480c00c2160020b224a40000043c0310740741246d841c104520b181104100240c4039500080390b134545c042d041c03107424058003201c081d4416145810412044481c0c0c0c105544556641a0107400394001d080032521605a40c00202440e500c00100741d144400c00e00504403071581208405102c5900000700c201c200100041ca490200d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492548543 1250 492547293 492547303
    0x9080c011d150309010f0902130b06071416090e0d030b04020903010c02100e060f040f020406181e05060d0206071401090f0b0a1b0f200a121701090903020f 68
    0x10004018a60780e0745800c001131070840e00404502c842c821b140408140c0561901400c0d83e003460300e582c07000504620020b001500c0c3e0f01a0010041c00303006a105907100411021412203041d4a1505010540985a040100640d203840100e0002070380311013001e4070641c0c070a03001080c004401401c01898180b6a601280c01d4400322050b000143c3d01005c1c489420300020b115000e01181a80041d0015007070502800c6680b01d8003900240c0310045101c01403065680300e80c0071a0042044100c4420080c00036907a8201038002507041002c054200b050f02c1c002c15480d40074035803207500000c210088005859013080110740000ea02910503c3c01c100d80d0f00c80088091140110f010b0260745c9800f6444840d150a07100140020801d52503541072100d8400d070255000e03880031604041c1e040140c0c115606900441d0f1901c2d900c4c4220041501811400c01800c07000b00d091903c090184a020f1042e9140c80b0095402c032400e0551a40503440070801000103407007943c03200706614401d1054070003d00811b0441c0b0700d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492549793 1250 492548543 492548569
    0x60412031104120f0308070504030b0403050a021905010e07050a0b030a090510020a021023220215131703040b0a030e030a0806090702010b0603040816140304060f09080c011d 76
    0x5020484c1040506400980d01507101c61507203010341c901800d6541c1e09100308400780c001011f204000c038800c12258028011520319040c442001c070340218150401a0180912079595100742c081d500d00400d190070000b000009498040c0e15192850300c4258030b140046c644002d0903500342c000e2200460385940280002c026514507903000b0a0b0b0140d5802d1100c0031940301d0b061251b02d42213080b81080305032800082055220101100300319001c0d400d000e1128a40381c0c6881c00075400361403c0c040c0c0c0a00e800c1c440140031003c00e0145103681d0b854842d20104640c1c104c0221100380c1d680148403c11030010007000801000c40c035841c0215604010079251071864100c1190b040224000b4401c00c0401d04140034900d40c007420a1000b40000001c1c1000709039144009040503081c4440014400042101c1d08070602616900840c80351210058545107502c0783c12600403130740011109514810100d1155011500b92a0703c107010381403038041172006407a80014a080764010350404c0070074802554504507031050f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492551043 1250 492549793 492549803
    0x110a03020607150507050c06040303050403300b010c020d0b0a110d02030a14190b04140f04060531110402040b07030e0d21020c0d060e060906041203110412 68
    0x80c1080c0c40f003071006407880100504c00b084800c0c400202c2e000000a4002e4015030142800112a11903060850ba044801420f44020302802c18030b5400042c506440a0401c100b15001000501c07980d1004440741c008548000e584800403601d13460220302d03100303156a0000303000c9000107550f4500c42200c141d9a0070610405010030341c00b0042040f40761a5020366201d004040c100100f0a1824a01c0440c40904416032401e9807551044a50520740301c90b40300d01003d070311854a40c0e03c2480e00400c6483d4100080f1421140769003041d0114202d80b20307020442800d0819401d02601003000d0b550304d005014500305d01603903854038030034880046442c3c0344000c0014000d03980f00360b41e0710305540c20058a406812030340907029412035031284012a070007080c0390618460403481c2e5412441d0550080b890001c3c4411481e0b88828410500e508020b82548485841d1200c4426101d003640c030144074a1302c13800201c2e00540650010900000101c1c442d0780201320b0046490001810984c03074281d0320840d030600c903400b224 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492552293 1250 492551043 492551063
    0x711150117060103031b0812150a0806070e060a230a170603120705070306050112060509010209100e1c060906110f09060d02040b070c051f020604110a03020607 70
    0x14038040300801d504015518010701e65945503960080c000c0240c4480d175941365400f020074804029075001124083c020801540d18a030526103e010740f260b440710b40c00e5106d24526040020f00709000300e0503a20a4186845508200000a051003080e5100701001c1c41005140005280e042c1225074000c413199907100c54460f00c809001c00b0241040704615030180026061108000d00b5a0340000e140002004003030800b40ca40d4000d00e003441c540b1001e904024142820640003060114a640741108414000c0d8002d01c4181c8802417058200d118845480750412000c500a504042c052a101c1c01e11000c05815140e440d94208080c061044041800311003d5031103600500501c019405454080d10798003490701d00c0c0c00e241c48010182c41c4214001b20f0701981001c5900c940500c001c0d815100104030b07403412940d0310802450401003801e818000c1c01e10900381c4203859601400c070300c0d44174036210044e500240841e441d0368450b45071810207480e2241e40a10b203040040010703120070340540036152140036070b01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492553543 1250 492552293 492552299
    0x909070819020a0302040c09210f0813170607031d030711120a03020307020901060f0c0b0703060e04051c0305060d0204200a200d0c12030923061b070b07111501 70
    0x45912480340c0b00d002560128848a00c0219070822038050030310f44e01010039640c60380f0381018209031841c542d101c076400cdc00e6800102440c8070b002142c8684100100d950400180000c0b002220f02055001034090007680148001c00014078260600b8001402c002c111040d00c4140c0c40000e80340690021089005800c049510740c21401c042590901500c61030a10324060700751048020494511200050500050100031819107802070f0f00c20b9018025254902020340b40c1410020b55650341700842440a5010b0601804400e220b80b041602440d0001d1504010451640800c000b500e089650f0700b6282e07184c240c035880d81801d40001031100c03841645803090502200c92144e09003102d01508a005a0071082080080c240d100803011400742e4008c4008a503004801c0048000300050b03034000381504110003c0c001c0d4007140b42c10304181c2c5e8990400b200c0307569503825200003107522540024106010284000e90008030003511099001a076403400c03460458400c043c2c0713031404e14020508608034004038014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492554793 1250 492553543 492553559
    0xd0c0e030c090712020403020a0303080f090c0f010c080d02030f0f010e0c16060b0909070801060609030c0302010f14031003141c14040807140909070819020a0302040c09 74
    0x14000400c4015282040910010641e0340314010206820460707294010101d40400390305903405075401600c09500d0315240c0c903001c1c002c3e2000b41d6034141552500c5001491104001480c10012403000d03100813031005030130005551000b081d00f021224a80c00380a081400903c0f440994801c0f422060603079264208140c075941548010b0704045000501c84041080d001c2c22481114510b081c44c001e840d4202900d410041d00509000b420154045811030a005030803400103041c0040e070303059000070800e0581c1c84d142651401d065200080000150b058100050740c060f8201c0204801c1c1403e100c9450f0325400d82d5045c643d0b008895a86e03000c103c1180034070601001a40112030b80358102e00400701c000402c070032500407600850064007081000c003c154641440c55090b40d0084c0390b94000c0b58032403070720f80024400c04059140309c1c0f07005100c0e180000c0c0d40c043c0002081e200302c68506014203041686526191010f022041d02641c03c50001600000140c8851080413611000c0340e550003240c078100302c85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492556043 1250 492554793 492554807
    0x3100602030307020316020a0e130c08010b0f130e031605120f18030c040e01050a0507050424052109210d0b040f0e1608070e06040b01020f030d0c 64
    0x25404550003402004111600041100e80b02608805140740d80000c51001900d9241950094010044c030030381440b54a000a888161409105011250305141c940100a08858040f152540d001420010303081c81420400104100d258055101240c4d15400c0c4045da4a10340c041049105001103c1c1006001d00200b484810b20000c0901c1c84c20749405002014000d003409403c0c020070444074440c0d43c1034002d64003041005000c1d54054014000120084c01190003000c5c122201d1041c40d007004002940c03e44207200316025903148199422107255111a441030031078089064100b4800100941c081032281c1001c0c14024008ea13500c85881e9103851054a81448800c1056401d02452940c1041e5103011407001d9880c50300f690800000c0001c509000100600255042c03405030500d09020207518003030100d480d20040e20700300344080d080e03a034900c400e035a200418402e00c0f00d25998000401d0652170302d50010080840144121140c51603130350540d82c00c6a00040d00f001103139952f103520a460b6900511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492557293 1250 492556043 492556049
    0x30108120313291503010b06030106020d0c06140f190c02030f0d091a0f13031e2f0d11070918120302040608130201091401091a0310 58
    0x12803401e500300100b0707006010020000082c40c08070031105020900c4000441d03502e0120440300c0000441c1041c0000c48421922100c00a000e5400d00000c10380030301b0a082124101d5401d83d004000d0f008185030129240c0440c0d400c21200542c403505074901c204a1b03000e41d14001c0c0210601050030f820100402195040c00507030400d101030420304180c4c0b0329a004002e0310540100c1c0f03007940e0390340c420301c0c1c0c0094010249880d000f480d002003c941c20f000e240f4100e101034403d50510500300300c9034807a40010502d04034442d200400254240d04052a03008101000700c5070421a400e0030070310318950401c1f10b45411207400400c0e20440c2c0c00d00002840407010466040c9205550920010700741100c1d402c1074489115004454845461b2960f402180710807501990170a90404035601700b03e2540c1e040240658440d108510004102c00042210b030050303907513030342c2c6080e50503100c1940c15890203903403111741044401c03003034180102420300040300c0d05114104c400740c01c02c0d5000d2a580c0d241c003500381000040d10390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492558543 1250 492557293 492557323
    0x40e19030e09150d0b190608011410120602070c0b030a0515240306150a0c02100302090d020f150a080402120706020607030b03030f0f030703050c090f1207030501060b030108 76
    0x1800e0582d250350b913181c00c40faa044040c150f420341d20b514000c418001384810740d415203468001d000034900c0e419031158001c8208200c4025580c1c0b14001e03540c2d0048007034050604c01d2415049181c002440702d50080024601c00c0d46442c0c40e00e40d9907010110250400c942541c882a2030b0310400801500c3d420202c0000b0904030350084458203145c2071004000d10300810308118407000400729805681340c002d50b1a41f96401d141050380d950140500500e988542c003001c03400350b4211100e10035001d010b0300a807084240c0281c8100c000d02126020481c41e866090030054000310450b629840d2a40620002d0240d03110b03503140c40c022070030988180211007680d00e00207844e03504000b20038032209134003040550700a9524038002c0b680712107104c0082e00314424900b600c00351102c005017465446195101942c030604240d10104129952090406141d01c03a1120550b0301400388016288245800600c500c1102e00c140c041303514168403503a500342125075940100340c419502000401041d08100120203000500da = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492559793 1250 492558543 492558571
    0x162315070c02060309070e0408070309082b0905040f150503150609041407032003070b1e0c070b280206011202031c08160914040e19030e09 61
    0x10802441d400c6a424001c1c0300310800400319030000b504103c0f14010b080d0071101048182442c0c54044165403003a40c0450209111f04c8001a070b9003801719421800404400c40e408960000711406550402e0282c040018452003030303404205601c1d01d22800c020003e4900c5d0000b000b10648484455005d0117034041d5109510803140d05d100d81c00407000b016041003050b20709088a440742d2400801030015002d12031054803070b4032030000920800c21620400c0c049020807800035008d05000341902c2d00c1c1c440c0a0120750034000c201100c40a420266681001d5400038046400c010b000d28000c0d0400000b81c0c069519410042b514489a0303211800c00f090010301c440c40c01d01e0844d02101c000c0d4a4910512410f2a64441c80b0309060642d1414808030080804581c0500003402a0348005084038405540036030b285240c01e0f0000396810b000c0c07801181581e001b0046007080350906020080a420f0080030b00c18140640d20a07043c0012446100d400042d109403905d924000314502070242d520b2005004a4a480e00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492561043 1250 492559793 492559801
    0xc060405060412150216020901050d0308150d02040908030603010524040207060f09060e061602100203070216030606060e0901030b0604151208030405010c0f090605162315 75
    0x40008841c125050300b03201c00c3c2c10385060f04102c0c01c0c0003229100c3c100c1480c0000343e55506415880c4070103411304d2085441003c00e0740c075581401884402900300902040c015000b041c61902540b000d0009100d0041a481d44865164089820f0f41d04ea074000300c9801e0303408001d001c168542805000d038021445400c001c5420150301c03544181b410000201e6000b01d47c000340e49030600c02c43e0b400112255020700014055100c05180100003000120440f01d454003030000802d002c5480394400e000700540560040102c10b9100c0c102d94000e600140031881948102c02d0018a074500203400000250b0140e41c002400d40c1c40d108014110341c26440d0910b124084c06001880058111030700d45030000b00075900050042a86002c085008603650014060b4158200c5020100012040110311a510580003800261000325044c0c80744446544890045080d401c4c05021007071192024021002ca071095102a000f540c0e11b4844034440101c0c0e1040240342201000d000c1d40381c040081e0008054040540e00c400e00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492562293 1250 492561043 492561049
    0x506060a0c020a09050916060203360d03020f060a0204050604060f0c020604150e09090a080c0a0605070908010c0806010e01120f050109020c1509070302040c031d07080c060405 77
    0x100350035604062200040118003551a00100307000500f035078580c10811400c1a2a8040e41d80c00c44c02c15401040541d18001300c1c00d5440401a28003c0002012030b01000e41303030340c2d11650350001c84002890f01e980c580f0902e4245030365862f403030710910f4003075005442c4a0194144003414420003c0640c001705004000800c00d54880b80c040b90101c40c89403410140c440c100754000c0b140c440907034201135800040454085040248561003548544468031103c0700f19140d081406400181210000c01d41d810544110307010550640080c40304022003019a0441e4503180e481000719081504e440340005c0440ca824450070b0801d02c20020010320b982002c0441e8075003400000c0c2166240c0c403a03203041007512621488554000e07009400b0000c0801014411903071104d080100a401180c04000c5d10300c900342d9101600c04003800c046000d04240409828034606580a0001420046a0500405548424100e080300403068600c41001945001d081424500481c0c0c0d464107000042c018824601000b041007155 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492563543 1250 492562293 492562297
    0x90c0c070b090d051b19030f0807050f070816170606040b0d020a030f1703010308030609071e082401020307120504050a030804180603020325180212060301050606 71
    0x807071100d04a5550010300e07001c50701c00c0b085030b00c00514520944034082c810340e5507030712881e014240c250b502c442200003c0b489040710003040c2c44046c0209242c02160408144c0f07c80080510710f01a0044803030b4422100049443d00e00154083c00c005e80101400340c000810f030910300d00051030b00ba40e80c05c1003010076004007600c402026204511640c0e0b40e52940e841501c581d035000319800d40003014500160307501d09084001c071441800c00c0740c0021010710200380401c421000e50303040c2c80e080780c1e90a040d5520035043c0b150140e0701400f000140324003a1400d0407507c14203421640c0060040d61002070342d04143c48a0b8160b10f11800300c5400c0c01407500000c00c12664000141c0b200c0e40e4209640d088034681034074091b101481160400b5030004ca1100c40441442842402441141c162000303425811814070a038004640f050701000350305400940d0080001030000b20213606054501f04640c0403030b66038803420350080030501c0b41d50428a030046900d5010807164030b0443c4d84428180c000380201c5c40d082000030498 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492564793 1250 492563543 492563549
    0xa120e1512101a2502010215060111070303020c040510060c030807140a0f020c120d0507080d06060c0311010510060c1110020c040b030a030212031f09021b07030b0a0218090406050105090c0c07 84
    0x302c04480002152750707120313840c01c403981e4000301d0645012a44a00b03000b900c550380003a42a025904020224100f40d00007a0641c0469480307a880407442c41060713904440e00d400242c0000200b00300c00400101d403d40303e000804529041c0d0700c4906550000400203400c11942024042c070030214040b030a200700c640810101001e0072289401942c40030545040109809560075a42a40340391031070116496401813200c0000c1c50007074560301030601d204d2440d130b03080c1c9000301c0d1210701800d400e950410629004000d030001c41072045201d16000b40102c0c1c049086800e04101d044c00580c0501010301c80b5081612036405e065206501414800c092900e0203503640301c01a0143d0b00c0e0000000000e81c0c004040030000c12020919400c1156080d681c000c000007941004810782d1104807240c620501200001072203030201c80d48040090202d5944aa200000b500300010b0f40c1c5a08958800b01d0501d6a100810700e0320961250000290320350508043c001100c03001821118601010041ca0240c95030000e650012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492566043 1250 492564793 492564823
    0x40c11070611030f031008060c0c0d08060418050106090b04060b0304030c080c240903030709090b03070308031807151d01110a120e1512101a25020102 66
    0xe02c28411822440c500c5104094203500d070010080c4518091040e80000403101180c00b2038105444403042a83c0720300c28050300c0d01141c0e01203401c16070003074040d030b4440d035000314000c000040221006143c02c1014642c20000c0794280d41d41d010a20030000c4512400001510507502005001d003840c8d59041c4e107110140002e02407002c88440b02d410010340c041160008003000d01a100100310110003002d5494201c03a401500450007000120420302c0002a24450540c40c1c5e0760021181c54101c5010060102c00101c0d41c15000312203020003c554200000c5004030303003007003200c0314601000c070340345042038400e0b040300350a228201e8040015642c0144166610320784295800b030203074030724001a90084040312005105001d40200402801030240f0351a0210545848070f42440c01c040080005294000c41c51204d0403805100d14005150503140303540d841031402442d1480756485540f1001d200c00d12410030b810a90001401d81740c0380203007581b17041d00707101c1c28100c840e403c00b4240d00103900c41203990350500c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492567293 1250 492566043 492566057
    0x527011d01110d0203040c1806320f1201020a0504090c02030307051c0b090103150609060f0e100e0903070615050a0e0403091e0503011802060304170d0f020405040c110706 75
    0xc00d02080c1f201c0c4000600003035000801010403500544080e00191141e4560b101400780e2000400f008640c0766524408054004903281510030100601c020140660680010f64105406000074091000f80f4403045a901c42a4807245828031500540780c4845504d02150028024003400da50000c003629600102c015088184407030f84032490005100c020040c80d403084480b0000401d0211f10104c0c0c5c030702c0140003402400095160105801034861a100301c106000ca6050704002d0704039100b1110f0707000a540d880d5110103590300d102008290909807042c60301604001080410030656128684101208a0920701c000d0316240008900700301700e20402d5424141da6001804241c8204290005000c0400c0340381030f40014100b540c21a8003047c0030b010b00a601e0490710550a11014040d03042d5654020407192440e40c2e0f9030344540c0d081008000702a0305410501080024001c1070081040c0303080038401c0162a1490f0000704010b84041071441018480030a8000442d0341d400305a480680e00c0b9820040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492568543 1250 492567293 492567301
    0xb130e09150a0209120601050907030e031e040617100302060a020c10110d0c0b070f0c12030203040b240103051b1306020715020304090527011d01110d0203 68
    0x941007500075411049101480d004100051003943e0150000d080c0984180445950a10406a1340c0500780603442d480a100e00c0095040392003900711803c0130000d103050341d0a1038840000b500d041004080d1510001c8000310301441020703400136103808801614064009282041500b2841040d40c0d40000703030051305c0004507191128001c0003041c40d043c8003e45034050f80c42d2103640050850811040c1440701d402142d84201c56540716203d55444903401c072035034648584604030705803003100804018400b44902d460840002c110110246000c1c48004e40b0017582c0d81c50705203484401c21030001c0902d890284049686210164401403100070600c003820002115190b42c80c060074410800c1c0e55800300c81d20005443c13490f041c4146900000c440f07c030b8084500d000d448248141241e00010351f03102c0161310a10040005440680000d50000381c0700030810842c90740c004800c45900d0a0800034041c40c2c4d15100382c0e102c041111880400807034461802081401608244d07041c8921400d581411300c650040082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492569793 1250 492568543 492568561
    0x304060f0509180f07110c01020712050a0804081506010903050a2015070c0501080618151f090605031006030e0f0d0215060603040803220606090b09010b130e 69
    0x108039030403075007481082074139080000c286541d10888440700090104055413640000c009030aa210103416000741001e40d00b40401940c00091800003560b151040c10300142c041102c0d203006101034002d50001d480d11b01c9091807000d6441201800f868108542d002003040450307408520040c1003039110741c0300065800c10038800e0001c50764510354554054a515218a0070141da24000c16800d8840c41000c04000d540708015104108100c03001340d0170034400f00343c1d05800014001c44a500c042401d9541c8d068190000103e10603203c20741c2003581c0c1c042000200c0828a0308003007010b00610243c5859440e5240c018400740c2500160b02c5000c06046c0c0340d41d401e41d0054001d0002c00001d40089044800c03207104410b0003541e40f64140d1201840d4801400418020700381075088038421904000301518580302c0e4101a45550525190440c100742c000d00020005440c60248100416900101146004400701009403400060303211611004040003d140800c44552045003110449000c3d035a6554030310100f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492571043 1250 492569793 492569809
    0x80619030605011d010801060506160602070f080414121903030912021f061410030f14090c030f0a020906061b07060905030114220605090703140304060f0509 69
    0x300400481c100400450b0000480707141011200c0070380040d41031640d8a5480508a032400c0c041d140d04078804001030092062078010f045030040c403403c401483d2030415180c1162a0003001402c450501000904000d407501c45010011014000c560031181c02d0801022643d403042c24031644005a00b204548000b0705000341d001c004241d4110300e03984026207401c0300003900c03204140002807464000080c0741c0c8000400744214000d403207030383c0b038154400500001001a10850343c000c0030101902c0e070780c4a0690755000d0007203110701d18100b40c0404483c03c210000a04014100f00003038002e5100f0305500074403c2d00010300d8512103030159001d0318103071285400725440344140d10000e002c0e00348040900a11082c0014410112040c6a56502c2d250340c66104142c01d030340d20010740700460f1307207280d0100f034401002c013080e882d005502c0e40342146002c2d01c0f65520000d4810490301180b25800048080081c0007030b16040304030342c05800380a145841e05152000c0c10144440d00070340300b08000803450580d59115110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492572293 1250 492571043 492571049
    0xc011205100b030c0306032503020114280f02030703090510050f0a02070812040b070303050721021c020f18010c0c03050604171e030405030405090106020303040c08030703080619 78
    0x1c41a0f580c1d1500b40c0c803d5442d5803082c0c6003940684201408201c61500c4068418100351140c007144450a240d60011100300601105c000341c8800200a42c48180c18041e609044213180d6220003800c42000030f901920071100c503030410065400400c50a80043e520003186802d40e5800c80e517201c90705019013002c440302c1c024400c14441f01c100000300f09460341e80010b0740748100e8100a04071850180590f02111841c0614411154240e000f404040c00090003134000661000c1c40f864100c5603041d03500d03d00624110344141071000c40b5400201e41c0058a40d20049200b1111030030000d520b0142c501010070021301c00c0380c10041c9038000c40c02640701968490381300c0300c00c2d03d9000941600025141c1c20900e440344400e58086071900103c201684d001c40d121403d07a401040f00e02d4841c2182003030301c011a50a644003c10440350f6000402c008109556130404a40c041d09081d4002d5840c4c1c5080e01c1c03c00f241d005244c212600343d5105102107400070b0340c441445903020030182e40c01c480706c0d14040a14503182c0c4c000c4d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492573543 1250 492572293 492572309
    0x20304080301090e120a03020c0f060112060f020f07080d09170a02150c030115090305011b080106020307051207030c122c10081008060f0105120c01120510 68
    0x18402400000800341d4180c0d421030030100003c1881d50080c95590324182c4240703161140500400c1040c0d40a64040d20800300c0250542e02c001301e0303501e195401d00901340c2100e071031030b40f460f60b400c820f000d4540b2410004a6405c5011441d011075840c50b28100c0c010751600410800000810080b41e421680100c26455070220383c10002c55084000a0300d60340100380d80000611a518040c0b203170300d0843c001710307010328003904029103141d091040860790000580000400e00044910010000380248038800c4820030381d0001da40b50340d01d801c0e40200f074041d06901843c11584240484404184003103100005050741041e010790322070700c82c6030555030415008000f502c10b600c2268441c0015810030600320089521411030014002c0d10400240c100591103482d80c0c00c244c00d2000981c000340144c994680014504140d00c0d04691b55903100c51510004980760320040481c1c100400c228103103190b107128074000144c09449242050400207206400c0320255902160b15400440c0b94042002c200c100500306803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492574793 1250 492573543 492573547
    0x20d14100216020906030a0c09110408060c0a020c0d080307050313080c010b10031404020d030314070f08010911091e060d0b0a09050405030f0a1e11150615070c080102 73
    0x4a030b0303100e400400c000180d000e02d00c5280081c165103400304045803110703032001c50940800d0400c00030000030958a629001c151101300804071f80a101000458030035544c0c6000385542e241007071002424101c0f000040740c0144019242000002c0940c2c0030399030b1003240c2d46040d503140da44022a8000c01c00c03131703200050480da200054241c507800040d0414a0b03494004c0d55880b41c407a11601048003142c3c2000052029a042d0b07802084c01440c20407c0c03040920300030300c0c010811496080345061980380555910700855920004e069080b90410309260050070340400421103201c000464000c42d103e068259842210f00c8100c900790019607060102e1500005000c5640352400fa00c1d003140144100204c06224032042d8800280100590107a0740c071030f540c404043e50400300c403d45e05482c50b401820400041c00544242c1d42d40c505081c24007100501d500380d0301d2802059101c10300c1da0510b0044000300e08203034941c03020030002d601c1f107084441010741c3d02c1185960314a1281040c0d01d010280d50088550343d400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492576043 1250 492574793 492574807
    0x60a0f1b0f02060601020f030d050c070c120b0f0c0a030b1206010f090506030c031c0302070605160806240d0f020406050a090608040b041106130306020c100504020d141002 75
    0x1200203072201c00c40c855001c4502c2d41d1030341e5005983e03881040400a03800c1d84100142d00d101c240341d420807038001040648003402d2058075550030001189681180d04070b008150012410f1045660000d504018003446080f02d90408400303038019440742503000018161207103440300d540e8544489080440ca404000c1e2506540c481401d5001504140b00f500c0c941e47c2084046041c901d0080740c001580341e0000d0040a50303241c0b1070968007031101082d40c0c910505600380900804510306002da00c1c4160b100d040030307040640c072400c1d0140244502610041c0038030181e80b40138180f441d02c0890705d44460b007004185e81e01d900300320580342c014141d009034144106002080000c0e8294000000c2c0002640e0354803045c81c0191190022204064211005042c240010300414007064006074014400e0402070503581c03501da03d560841c03011803c030b81d10864040d540043c0c440140801400719000c0300b040f41c50203104500b441e0300080c0184101701005400070045101100307500f20208001c59545100600a64540316 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492577293 1250 492576043 492576047
    0xc03050105030111031006031806090308070906030b0906120307080c06010e0c03091009061d070e0a15141215060301150b16140a08090a1403060a0f1b 66
    0x4081c440c96010750308181d5000844500001a2481001e541c08203284591905001310080c0100600c0a61856102000240840d8141c001d1002190080c0c44610260410400040083c400c039400317038040620b8001b622009075641802580c2024080300c0d00d00015090100441c1148100c200042824200040001d003400303012075061704076103608200c6001a955402d0150716440122440780c401c0c1c002c2c060401e00e60348582e100b04030b900e000760b1001803907901d5600740c5800320122001c540c0240e40100000c00c500d880102e45150b1040343c2d180306009001042c8680145c03d4200e010362080b882003000e1001c45500c901e010482051022130403155100a0038117030918409080c0c13000c03402942450f40e80312031445038400d0901192000107000f440e2002050b0b0980d091040c0c1c84045405007039241001c1e00300c840800c9124125406410020303521040f02080002c1d05200364058088440403440040550b175001c80d80030750046840001003412a1500b60440040000d080526002180c859031000441e0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492578543 1250 492577293 492577301
    0x3122f07051203030402090417040302040509030c071433130e070201050f070f020109080408030d0f09020d0209090a080703030f0507020c061c18030309030206010605040b040b0304080d0c03 83
    0x6207081e940050002200b1506035101d200071603000e90450300280110300020450740115102449080d07555003459165400502a10401e50781d84000b5400482c0c180aa08014041440188103040c0300520040d018404221032800d2841c000784124990807441e030006441111043c64044403010540da04c3c4000c03503104141030074030701031031402d541034030000b8518074014402c0d0350043d034101c0402c0301d02c0d50f506042200c0d107040c4001180115501d0305c600200082081d4040d102070030180000d5a10b80d44856810750450700e811200d46000340c20300c1c8005015850707181040244070f40654480020b5580d050380b461030452500801402030000045030014140d140d07219100141060805110719194030600303d81d01d01c1c4180d02503a10150803c0100d14102001401c6101200491030106400c00b00d090740c20000710011030207802298030781000c0030816505012031805080642445420b203400c141e0304040702d0090780128000540c0000224003489420b00c141d880704c81c4805401d02c20170310301120080c090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492579793 1250 492578543 492578549
    0x9150c030403030f08190b030c0a0314101a01050307021507030914031c02031905040f030f110706050702120a0c172a0103090c08150105040603122f07 66
    0x70032180b1441d41d02c0348103005c3c00e40a14550240c21200040013440d26004003100c4164940c075115030b0003c0991622481400c0004500455075098040511920142800f04100544414600e0076440d5000300c0016440188004420b05e0200c2c0c60b60713034441d42030740743c031000010703502c9015000340401004030761580050350111b11400303101a00000388e2100c82d980f0301492130220b600140d02c5848104603140381e4040d50303000da610071b50842c0802d55410170408440081e5402c2d02c03104440c0d0804001d050300840e21701642c080529122503c1c1c2c0b50720341c03601d45895050240782c0401c080010324100755540d8108c5545a061a1016a010ba120924107a9007039642c601c03036040201c2d660040d1050411001c034164103800c600c2c2078a5480e6120840c4d2400d500403c4114003414141d80e1821000800c0c2c90341c44000191140e00300405580e40841045400488168805481282400350500000e00964403603d80781d031030b500f41031001c40305480202e00d161240503050450352082407500080311000060005c01c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492581043 1250 492579793 492579797
    0x1e030717030c011a0603040609062c0c060310120f08180a0b0a0c03030f0204030602031f08010b130e070506030a0204090605060f041a0f120402030d08040210030209150c03040303 78
    0x2440c5001280d00300136480110100d40d01c10010b20005011072007540000700480d11504001440b100c06002110302d03582d84240320405504032442043d000c0300100065014400211212030561134180306010b0208013500400000454201e180c1042000d0f10b0b10b080d2025a1116000b5112134150b80c000800100600b881e1344203031707031102c0c0002d900c44030700b01110019511a910540c5541c42c68409902a05d0041090380349142e01b0840000070507258800b1310300030140000c0300509000d040e00c0724541d04105401450789a40f404100d1f149903038440a4401034260201c0004c55401d44031521541018002d5000642080d8000100100204141d0080c4103850341001c0402a2503201d405015850290038986000740d58204420710a14103c244d54a209185110905152078400740c0c240c2015081040b00d1010750002c0d100740702c00c40c50203116041842c20a8a4400050f240540000300260000d000310020700d54001540e0300e0b80c0c1c0710611030801c500000000555a2541c0058041e9030794010300c02540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492582293 1250 492581043 492581051
    0x1c031e0f1e02120705030d151a0f090906030a0b0f0a060801020921071509030b070f0807080a06050d080315060301180507120e060a0c0e1e030717030c01 67
    0x420107090403068007032604940c010301900d26030078541900d43d4013116090782c140c4001c2c44a0880e408042c00b0741030301d80050903108240c030380c5000480f05075030007441d001e80d5443d002840440c0705803a51805940c3d84420442c0d00014580302c03800486c0c281007040001a0081200108204c0e020442c280d00c035014040d01882000080c0c0c1e100d590380d08074090103074503070341c8070440804410340c2200b51440c40b40000c01071001e131551596500c806960f41d001260500c030115020340405c1042c409603d512a0f0301c1015070074100d03c219212600102000c5005054400344549140481c0d29426541d1014001d2705001e000d5228600701e509010540e6003080710000500e5000d80001002420040c00381c9049404030303d0101601440c00764050041c020082c050303002c01070f00f0f810324104801d00b802224069a8048060082420200c9441099030340ea01c89034024420f2003d00202c5545070320011001402e07103803502c1105106264000b904100d12688644856400d040080d250150040000c103904103409001700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492583543 1250 492582293 492582317
    0x41a09090f0c0d0615080c0a0b0327030c1014182e0f020903010e190b06060f13140d0201121a10020304080118021c031e0f 54
    0x665100e500460307090694000c914255120708140c1d80c40e45019106182c08643c0c0a0b10004c09183d28510f035116500b030f944400c4d190005428100d40f454050680185028914039040c00081d4500201561000d44c01c40b0783e030301d82c00d03101d0070a0058551a48804d02a1198490048580006003e54002c0001400240d8012803030903540c01c1a170100905507070014203c0b464088444624850031170411075030021040351420300c0540d413440748155040946000607201d444900c18035084034000d00c241812944080000380640d03030b40b041c0034100302e54480b01000749a0f40781c0c40842c01030302440d0032010400c1404141141e5904056050400750350030500c040307040c008800c00b00040740051340c801034041100c9a50005070080c654000030a07210384003c40b200c54075245404035008500b440c1000b00180c0000c01c050002c01d00130b00400102e092101c0a9001441c2c1d02c0c1c00080c91000d15040d040d0700d0303040c07007942c0b0303020180900402c0303105c24400701e400d02580710a080e0151004024540c8880000c250030214 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492584793 1250 492583543 492583561
    0x4050a0b0c0a0b07030905010c050a1206060e04180f081905030f0a0911090405250305190512070b0a11031303140403060e01140c071101030504030509041a09 69
    0x1445501c072110004040140b0341c0e489604011802a010400309a1a440d003080841d10174000c080c2044807035602c81d07030340b0800010001c10710001d9008000036030b41001000c00505901c018940c10301c1004172030006259400765604c80b1810b510071001000054218020024031000c40c002e01603c081d0704440d580800602002191039110490f0b92021100f0004003240c0260042d0303004000c4507216a40d0020900843c100240342040c0885040311554001454401e4054407a00c0d290b8216110426203900d99007180e0343c142d102c0090850748281c00d007041d4030000600c0740c208140711b188050b2001d80e41e520001030400004031042160140f580b90300305060310130b410100030100c81c42141c1d1704003181034255040e60704807189420b45e018620700071028400400410002d2013a80700d40c410803000021a106110801100008020b0070000c9280c402d020700c034003007a4103204119100400340380003c2c1540d180e16003995580500000190000d10b0511001680140c80d0003070b1402000445031070440380e40e1030f140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492586043 1250 492584793 492584797
    0x3010914010f18110706050412090b09040527100b010f23040b1216140a08070201090606061d190b030a09060c021b04090b0f04020103090503030c04050a0b 68
    0xa114070540d41400c0c1040040d91001019241407940140807130b54200c0300d418008640c1108034141d520340d03683c0044c00100310402e060140c04103128103120780014900022070403a07002d2261340780d001c0c0351030350001a01600e4407980e030381000c0d8100745401034030302c011100c1907a680c5141c201c8202e13440c60001030281d50360213848400c00318102c0d65240d0524101c65600c02c0700d104602c4140381c1d078101c01030201280b000a200080d1420060281e0703004034614049442060300c6003059a50303414403400400350100c840d0540102da00752401c904121009403600b510880c0101440300001e4112450314a0100e1075075030207030000c091982401940100c000c1540b041001d500303066440b1001d40c002c2d0400c00c102517a5618050b552001003480c0010b407070b50150f1141d9040c5c59280e22100c0c0140c1048010002d601e070300c0a00600303144002c0d42c041000328181e6452280003900503011087e95600720000604681c800c1e00409015503220013500d803079082084020742540c1040c01000d20602e51000301195108940741 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492587293 1250 492586043 492586049
    0xb0a0b1210050f0f0a05280902121f0308030112050c0102010e102004080a030f0305131e0510050a06090b0303160305040806010b030403031b020606090603160b0301091401 75
    0x12483c600e10300841d0400548030455031115402071211480007440d90707900d4104042c80080b40300b41c10010740a164509030100c50765000840d01c1841408090740308204c004525512182400520b040100940191400300c00c066000610810002002180b4101422041101140304074100e0b09942078407401a800e90b180400c840c5255803002d046c0540c1200ca6800400503a407003030034042c158080c2044c40c1110750b4040d4201061591201d80c200d1b0803d03910907001144010300d450b00300700a060030240c81190604200c005000389940b000c1c2125180050300000800c59400021100300d0785000001c0e1010b480d084421002c2c4601c0c0c03290015489002e4040d02c459988014090751420000543e13130440d100c0c0381d0a056013008403c0c8004501481c04100e030502a18003a0b500039202d15151600174207640e00743e85007070700750303203c9802007107040341c00140050300180100c0d0402d100e80e0340e14021074507191480450710030302c140c85000090f03030408900040d41070321030740401440041800139202c4218030080c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492588543 1250 492587293 492587299
    0xb0f01080906070f18031115071e111c170403020102060a0f0b06040902030907050d0233070c050a081507030f02040302040207080904200901030f0b0a0b121005 70
    0x2d002800d0244034080b4a40d8144050903d10b60741c0034850b080840410a5030402c036841c00740d00c82031b10042e2810171100030b044066403a081d4641043e5580f000c14540303520414550403101c0d100400e04120516466001c1440f001cac2210034012a006084e2b004402d0075101510041c05102060903840244411641070303d4060b0020032164442d03204080062401646042cbe0305942c400e8076070002e5440b400200020140703c400541c49040c4040500c1c14140f10384d11461182001c01c6d40c036001078a403000903d011482c00c1d240e03284004c000202c4116100e1280c002591031000000c4c08038100b000c504803620035100161103a8400c1521012499a5040b0b00341ea10a0b040349445c00040c070303a510a4200d07c4e0005a0502d0150a0a03900c0d40480c060ba003050008807590702010684814508091013448042c031000103802c400c1c00003009038a0814440d414042c0d04050b160340c5400341102254109400325180645601940341d5151420015038218003015091386e003001000c43d0600c0011602e104c1912001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492589793 1250 492588543 492588553
    0x70b0f21041a1b1e1204030201050a0207020114130306180b060d03020327190501020c0109051c06060b030f090d03020c0601060e01031530110d020607060905010b0f010809 75
    0xc0350845595000aa0740d010050711481c0d07000d094110404c041e01c829181d58030044210300f13203440d01a00f540e20091211a00c14414001c16003d80c2e405621554081d0386010300e5651040b85c8540d12088a0741904043c007203e0410142c5041906c660528441090180c00340d1042502e440042100510280074040c0044c2d00902a100200c1d50000784007841c030b0001402103514284040211380040d50f0001c0140c03690410003010802540c05100040c1215024600300c0700d02414580000c1c05811484100f02d00c44104150000c104241035200d90b019144800240340c0307034913003001c0071606003c085a0706007542c0070320880c48060300d009000b03603041c07501c00c08003601c2e103a0b003424000c0340d581c490740710098105611000030080681a20000714054071034646e8183c107168002d4503401e01c0d043c4420f1a600b040d05035080b2080415507e501c56500300030103c070305910007102c0c0d00000710a8052841e000e080b0380d2400004804000056002d0306014400741c8442110783c1c01c03440150791a12085030000b24982007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492591043 1250 492589793 492589831
    0x8180108191805010f0c270905090109060e01020a0e0a271107030306060e01090f0b0a0903051c03050609060f010c02010302040f03080405130509070b0f21041a 70
    0x10076080001d40d610b040511240c00d002d5911042c1c20766926001604100c0d50303481400c424203a03ca41804403520841e0b040c04442904d9810008124946104c0c40990070b0380c80000c03a01da41821340100c81a15044142071180fa000a0300460007580480d201e0b10100341c07905100b28060030195411412a480c8001e51141505442e40107441424415076814205946084101d020005000034081290195070002141410820064004400caa000c14107100c07c48000300305402c0c50105040135035010181450310b9103901401503d000c011500001c2c040d0040740200000301c21031004441403021203680034002c40d1109420b0154a800598400e41c06c504414108a07c80d401018108005032061400600e030650756903260b403819050b600200c40d40400082c013001117140100c618152694030080421070750400100c0b40743d440341c040c8140c0c08140c901140150940c018082928044800c00b180404100002c840c3e81c1c00b0080c0c11601180c0d286821030040f5000010402c07540e1264205e04c0715146d00443d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492592293 1250 492591043 492591091
    0x7061407020607140307060605040b1309110612160c080a0c02130203090c13050f040b070311040b040302030f0c0102060613020c07260105150409050c040908180108 72
    0x201a01050b81c1110302044102e00052814100c01803095140700a141c581103180f4040080d80c00c40d91100d40708a05080350900c1517666083c13200d07080c0b0300360040051a94260318204024502d100c948a901c4140420826075220001d03100d030f48156070b01c26605010340103852081c0d480ea1142140500106810700030324400390701507992560724500007070100d1060500c600c5440240d80c4129410050381e0444100240b040c01d14414003480205011400d00052501d02007640d0308034001480034046030011804070b01490b000e41e102030590041020f0f9942d03150b407504030b03407103050b030117440100d01034403c2c0c0c0045d80408070040340d01e103d034120507809000c03e0b486020400046070f188850400c0b0043d82004610f0032540c041180d000280255070350140c48104c1c5404a4806842d20001c150a9034103107070402c0f031b103400350011107042070804403400100d421080c1031107403501c1c1c0c0505584d40c02c1460850f212081c0110b00014144a2048620004504a407080112010341c81038641082c030680500744843ca1301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492593543 1250 492592293 492592297
    0x4030c0201081003030c032709150f050d0204050711030c211206040e010b191a03010609050103050c04090c110f0d05040306020702151206030115080d0806241209070614 74
    0x88160300f050700e00d0140c1c44610350381c0c48c591003d0200c0d40c1c0c402d241e10110800303040220087c03041207400b0b4687d600d094040342000b42e4420300240b00d299074400007034020740034050507202481c2034000c40e81c881407504402542c034249100001320029604950f002c141e01214116800b00b4181c1c0400c07800d503101c035020300010b072941c40e480441c00d540ba80100882c907240c0c00c0802c1e10034200c8440c1032450b24a4690001d51104144107556038191040005202c5560442404c000b114030038030340010746a4820070f0180c25030046401520308982400c0001d5501c6610080c0a07000414407400d981c112210b0302a0940d48805a03180c1da00411401e00080001c00d00c1940500b4036240041d00e0500e85a080c101110215405103024611610321301041c0402c0e41403d120340000c400d0b50b0000e00c0240360070321303507102e0390b401c100300044c41007055a100007002a101d003401501c0540a03100e00140164014180c030106401078034403145100601800070381a40000100d000441c1c0c2e55454426108001c0c02482600d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492594793 1250 492593543 492593567
    0x1c1104030c120203061b2b2406020705061909170a17040f030b0408070605100f140906090a09020907020a0302010e0d140d11040303090312030c0914030a0b04030c0201081003030c03 79
    0x300c803017139851f0b52008a260096031125400c3c4d00c210720161000d51080a141394860b0000c0c021540801428400d540300c0c40121001132820403417240d040305035000c003101c0303685840d004200f40a60002140c0c140c135900150401141e0b21802130580708520101c9030100c18000c0d44206411000650002c1000c2844c580129421502482502d440c0c5980e5803143c005440080d00c401d000f203151418100104009031007043c01400c0c0c0028180c211182ca4000196a600c003d00240d02c90140b030b401148520445500805070550b024009501510f85204041d454603032841098001d0350800b00e0a450661000c980e007a421200740d00c0b0940040c000d8505400c1a0708000d00d480100c1d55140b541d04510407a58001d00000c502c20303500c902c0300702d082d440e00454542090100320240b5092603041099640c00050000c05d680c80991035001d91034203103002030b03d4040c101201401c0c4804031005d01061560103051003003603034004c1e01e07400c6050310340c84140c0800320441c6c40080e00090340b502c2060b0003c1c0c071415034003442c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492596043 1250 492594793 492594847
    0x30b180703020a0215010608010807121101030b010c0203010f021c092a120c0611010b0a14010c02090c03091c05030c072108010611031c1104030c120203061b 69
    0x207009240c4107005c1d400f0405c0c1c01c41c60101d5203907801000a00020032000024140340c040d0a501303514159640041100454421030515844292401d9241d03c1000d1101d4680c0d00280280149100401c101000703500242c11020b00d4101c2c03120070038025055000b41c000559101001c040e5540310b41400b401c602110702c00e114035080d000c12000926036100300c4e0f800d4071240181000c0c50b81034a0084060803807503150211101d01d13410084024080e58840080ca000c4510740450702c000e00c031290300126480801a40000d5010360000240581070b10780201461140340d819086503805207101d14407000300c03014100751000085003000055088245100500546032085110410844030f0203a01910581d001c1031038000203404000411031180e00075052800c1c01c0d40180a50718001c2983c15001742c8500b005d0a1600c06504c03411001058074044085400035034120a08150031521001c084000050b20002a4464401c24002c112a0309580511030b0550071083c107514900343c0394184800c48200b01440600c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492597293 1250 492596043 492596053
    0x4050409020604120b01090c110c0d03090b0a08040215040305060106050f0d06031202100618050405071707080f0325050703051e0105090607020303220206040e0403030b180703020a02 80
    0x180030708000302a42c04c080c0300f400c112a9a42c1003c10050845440e104020204502ca80c01d54540080208030405203200a40d09004c518010f070070144c902c1003040e80514051400000d2003004a030340306100c54000c500c200c1e1305455079142c520542c402800b0fa4040600036811960041040900a000921042003200c1189091081498000c0c1c1210415030041c0e41091080d1154220305a05000d461082e49145000f0400c0f5130400300368111800d000080c3c1002d0307680c1c850201c0c2c24031404010308001440d1000c0d1036040c03011500780d0143c40328014440c9204512540045004140c004001d4601c4074144895003480119001e00e81140441c2c40c0c041075403c0c1c0100c00011003c10414800030141102c00f04c4902c01c154902101e83d821107d00828102882e044902070107042035010084a400909990010409599040d00d01800e85203030903009520500004001501207210580380d84518000d49040103c00002d42c18007550841e139240040c050040c100006d0b0809000f94090456074115104840e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492598543 1250 492597293 492597299
    0xa0e0c03190e07030c05040506030f1c18120b160e04020a030902102a0b0f2d040c0506160305030a090204150305010b010f08070f0e0910060f1404050409020604 70
    0x2c1d0404000c2d41054602c4088040144034600700740c001c49420640a0f8010100c484040d100e440c5c81348910707450b40e0700b02c1428614011000340b0a0a4200d1180c05011043d583d45a44800c102035150f504641100c1840005c0000f810003d21104408c100b80c500fa203800e10f020f04c004081100030340c40003141c41c0c14103665004180150315100064501d4001503101e10100c032010010075242c9140a4042c0200701440b582c600740080e01d081201f5400c90503901100c400c988401c82c01000142d03213006444000002841c0c0e0458686150100034011801005007508091710380341031005521400020311060718100b0b0002c03001030300c01d0000f141d100303011100024020b007403540040c0036941c110f0001c490465034540180300348a0300707110722410120242004041c402d0598405042d4030001040f103400d10041000030324103035014003003608005100174078082181c5403a01a803103d44890f4020000054184070390181800d0142012483d8801d4004149051610380001c00000d450000e070100d8200c0c200380000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492599793 1250 492598543 492598571
    0x30d21110a020c0102100e0318120a0602030f01050409051f0e07030f020a05092a0706050c0309060f1e0a110703021b0a1404090f0804090b0a0e0c0319 66
    0x780c0a4035840d5400b4024a84003c0c000a10f400c04d44080083c03200d180102d6944503c4d0004111044104038000c0030b181c204035640040c0c040d003140b6003080c0c034034090f400071542001220341c01144200d115407d20b88081e600d800900089840011006242d0342c004c0b25042c4462145501d04290b00c04043c00c0815010750344000d081c10f261299008960540340020034804515148d02c802c80a410240d4502d00a0300d05101d506103000c0c411100c00b007600c091070b007170a0490031880c01112040d80d040030040c0082e003040030510001c3e40c0112078001d054064400452621240540850302803800c01d00e60040000d231011407620700c0c42001c0d26122201e50b85980505400000c40064803445000b50040c103c0b020490680030030f001c00b40c94110703103d144285020300000c00b000340c1c04c9040d4002501c0010f0705010b545000c05080f0038005000c0c10f80a000700d0006554001c0da0444404400191503220189581e8460404840c4081d070b24103010200500010340c0c602c052850705144203e0a800c08122a1110086 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492601043 1250 492599793 492599797
    0x31505071713051b04110a0f05070312021308100c200705120102211e090109061b0e0402090a14030a06060902180d0c050f060d060f03030e030d2111 65
    0x1103103004011803a1100641783c43c1c41100405101078240c00c0c64084042401020940c0580b160020311402040c10300a040c4036801004e00180c201d0b000315a2090207160f50460040280f107249898815181401603140d042c0c05102443d070015141c0c4903046116074071030800300364000c1c056159441500744c00101f9a4070803001c5001400d854000590711484010905440c00c420115002d00a00d0f110500a014980d039105144d01050343c1004251a1200c2e0700042c05001c0251002d014941421407101c2030f0103a10f5059281000c0b1074849610303010403031051100b80c0c0a64075056600c26000d40c1c0070024043d45a1946480d950014103841a82c0c2403503860303c0442e88590445002698003060200b141592545450100e1a0841e000d010030360466580702d110f500c1d18002c0602408151648101c05d4071401c058901061030003e0a0014540b95004425056550301c01940041c00707000140496041c08a0701c0a068981503a801d040103a43c0450404c1441c4640c003071518169842094555007444040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492602293 1250 492601043 492601063
    0x8150c090f210d020f0607030507201507031808030603030c12180a0b0d0b01050405030d0309120309050304030b04050c0603070c050c0a140f0307090606050403150507171305 76
    0xc0a40c980402014240303083d108410401c150750204e4142d00454400003a0f150303001ea02458046141ea0394040704540030a20324030071071860790107517018552034500031400c1c01c070581c0a070505401d10707a030f10382c0e08a0035100280c4400e500901c00025541c085601d0500542c0d01c01c03009402c4070b1030403000c4c0c100c40d4500468901c580520040101c1c64043c510000c01d6a0080c007007003280e0100800341850780706031491250120343c407541c1d60786c0c0a941c50a6405041034500404c001030a8500905050501070060104580c04540314002d00c1c20040ca031700d000b0301ca202c44054020740218101400c6588560000501600070b40c0e0170f22486000f09919540c150066200704c025549404034900340e0f113440391801ca4104511803240782500c100703208194190031000341094080700d4040081850030003280c101f120503080f122140c0d080c0400450a00d4228000300b00b181d210310180c2038003801c00d150b05030032684140c454400059404444002107641c1c004000c0e0030507002030f000c08081d0460b82d104c40ca0080070b44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492603543 1250 492602293 492602329
    0xa02300919020402090d23012009060c072408100308120c0706090c06020c040506100309230f12040807030f0602091206010627050d030216060c060608150c090f 70
    0x401081c0700380c03c00303015403900c1c85501a842d040c5c0c89c004100f504c0e050300480d00c100e4010440130404000c02881082844003c10703004461910b40d01c4010442840d03080d2240c404400300c1c1c04940031541c2000f558a103001200e0700000c0250902d2020311155041e03490150031445250802d00402010808a1182d10444d038420040404050b10708117000e0f08100c45035012a2080f46820100301c00c40d00e802203014142282c41c40c0c0012030104c9440e000403a071448010300015100c01181400c000c0c0c0b07000642c2c0d254001c8071021105030105100004e40e10703202e0b03070044010b10b401c04101040080c0441c1c070300420b02c81c85044050300b440d5004000c59804107520354502003d0380319030010007216801204520902c0604400d4080711400c180110b4107006061184074000c2040340c0e176030b4051600c20b0014049034000c40b542d40a8060b51240000c0419299103030580d8404c0c40c00c0c00000d401000040c0b01070134031003413456800555803800049004c42d004a12142c1d0005003080c4400e9241c0c0d00d50310031074194000f0b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492604793 1250 492603543 492603593
    0x80c040e1e0106020d140901032301060305090f100b0409080a1d0f0312091804050a02031504150c0e12150f0708040b0a02300919020402090d 62
    0x1400d07240320006a10400541d0803442ca81510a036002400907403200e031000710742c0d0359003000c2c1e00120000c1100107040c2c0300b12a5400011110b4103142c4d00198100d809503503081c00301c1d4560480941c0c8034600d102c3c444020394807203014043ca01d100c5420010320100c00900c00294440d0644401d101036010b10084000110031066130b0020000c80824040040c4054034014110a00348001c2a41d802e490014600000e0002c54840c001d0750b81c01c002c00303241c0804204003040c50b05040c45c02d40d650f214440800c0307100b8040c1041907001303080e606e45024403564203c9a04442c0c00c40140d1100014039400c0c40080030000c802e1101d03507031603c4212401c00b81404a0005080504840154007030154019181e5124180c03c03005200c0c60fa58400e0650b600590080800e10040d00c0301c031b000200030b1241c81d6100301d101010f105108140084030b9154030440c481803ca000c225030320000b000343c03240c030b6070751210001455443c55036015080640c003070076941c540504040401500c54844ea038400d00c00f40e4000e226101d031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492606043 1250 492604793 492604831
    0x307030206030a020a0306170703020d08220f120827040608101b0e13090605010f23030613050703080c0102070c080c090109180b070e0f0117010303080c040e 69
    0x1140c441c81c4000d103032601a00c089188d0600c62a62504418440079102e0304c1024070302c90900416008880190081010301d820300701100e039031117410a4640c81090491040e0841c00103c4800109240800d42d5104003000d03d02885400e9640c0d030030403601505e00c50074112528003800c0341c4451107070501600c4504000c2804601d440a48803d0358400f0112890b00034610040128140e0011070203c0d0180044441070b9083c00c03148408401000325400c00b400300343c1040000034a1504c590810f000781c0e41e400601c400c0070300c1920040404003403210050b540581c40140001c00340c111540d5002c030330351700c035a05482d226696908e0f03101058004488944860f507000940c0000c00003c054040c0080045d81d010f018241140310002d21090414410403400c580c451903149610703000c050014464603808894480c2d01c4c00e1a5400828030f516901c09035006900c24408008998022900e21071100c901461407541682503940c01c503140302000d02a000184024007000c075100041c0452184188581c040760259408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492607293 1250 492606043 492606047
    0x110306030c0102120f0906071208160806030a03030b0303130f2d1a1209060103021c022b020a120203060c2a0c1005040510020f06070c020307030206030a020a 69
    0x40d001003541075500103500d51358103403404410369103602403c04d21141c0354140a004100544103014008080c201c040d511400c04640180185010f4803c0d42e1417442c2c0c4440c494419a080d24003982c6a0b80d0550043e90444c000030320a0700680d031503c10140130b503801c01000500d404a0811160080c011405606000380409101c100c1c0c8022551428010144980c1885800c0050a10a07026140c020359050001c45080505032003110308054030729581071451300d000100541c41d600c0a0008a2007210016485401c07400400131031804990003c1c0390321010b5030380c2e5030000c1d241c203034190201e078540742034007208005a580c03544c0010091050240040c804a8a80f04140c00c1c00b000a0140c0141a0709002c2c1051210b0342c08803601c3c6850403002c8529114441d03010f1140350488641c82c40c2c1e8001c0e0303409150500390358080041e0003150380c1681d4801e5000382c1e410302a1384410f4a0b034410b42c10740c2d1010001038410751180240e154030a00103816940c0e026200d0700480c4241d881150100c41441e00050b42c000307065 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492608543 1250 492607293 492607303
    0xf02070605150301091a100e0c0d0b121504140607120506040513020d0204060f060f1b0305070206071401060e0f090a0302070911250c140f09070c050111030603 70
    0x80811402004410615a0b1b0130014400030f81e150300481281600050010250b414008040d00c104483c10005180c020030017015544003002c0e0055050130508840031074103004184038460142c06002e0b041c01e4000f607424815180c00104181c8142c448006030f8001900c0c01d10209020f156169a08861120200700391001e40d0800b5245034003852030803007085100c40c500d80c0d0f01c003841507045500d6070784d0100314000100542080d0300003a00401a240c000030707050b600f0030107401e0100310300c1d216000b10151102240c0c100c88490040030b00410020840c050040c50f003c0010b007000c512034503403c07042c00303e902d00050031590309e0b411407240d0300d03000c106000b01d034951120b8095100b0680310050a040c03405550003520390101d4807407150105d45465417081100711074400d4030728249001130a41d0f039404800c07d000020102e081c50541d40700c502d400b00855240400505041d03e5240501080c401c0341d070117000d02c810301d90700418110030802c0e000501c000140007801006854101310000310b40f0780c28500c0c00c150800e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492609793 1250 492608543 492608581
    0x40204080309100e0f1c0606080c0114040e0109020703090801050103050d140316030f060e0906040204140f15012615010e1f0c080c07080c010e21010f02070605 70
    0x1100122910250713540d91000c0c00b0398072a1040d80c07085ca800c3c41c400790154030740b6204500201103500300301012502d02d4002400c0160123809a0f104544e46c100b000d02c107d141d02c564028048081e4030030005001c5c28906400500d10940b0a16044817440d50b06c00d1030b2400c40b07101307820489040d0040640b003a400c076030000905150403060316103e40303107041004010300b40350420070842040c15200e401c501441c500c180d000130014040950384030345031720341070680c0c5840726001c0341d04a10451824030844560014504807500c105a1031a21504030786901082003224984080c0300d504100300c60039a684035413441c403907000c0e54540c203001000d107500340a5550103165a00c495060704202c0e568075031650b00d903182c9600306070318180555910078188400c2c20480d40310b155440094001c05000601c0b0010400c009204c06c11150500295034001c10b041c001159074140c11200686e01501014002c00b04803031052290703400c04624000000c0d01e02c5e0061020341a80c0003d10152620f130ba07100304220f201c110350072080d00c2c0c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492611043 1250 492609793 492609797
    0xa02060c040605090121020c03090907030e07142106060112050601050406030e1603030507120c020a05120f0706020703030e03070608040f03050904090c08010b0d0c0b1804020408030910 81
    0x9050400000904a0003100d0f00c4c0d5040010305809100301a03401c00c000380903543d00304010f650b64140c0701e80442d070701d0740451a880d0003080007030000b50b41e003442840741e103035850711000113090007e05c0d240e210242c0c0c9400d0040c1703991000f9441c0c0590640142220b14030220340c2240c025103031fa845e1074030000d400a003e009000e03c185041034200404e0b0b03a4040110b85c2a0340c0c1c02c0c1400a0480c80d04c0140628000340500c0040380030080200200c14150000003904140384078141c0c0703842d001c07a040000c40305051070349030007500412000c000344414541480744180044950b030813a0710310aa6154220703c0c00f1695400440981c11101c0b06005240d844440c0094138141034000300704192070b2600040c06804010005003101004030123601c20184103508841030f1840040090040d80c0e52030504401051a41c070840d8070940c64000c40b500c0c9800c00f102d10740502134100002403890381c41c3c0301c0311440d143d01900c0c1c2407180b483c40c070b401003036244e94034070250014100090045803104030810611400e040d07903620701e0302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492612293 1250 492611043 492611047
    0x100e1303050d0e0c100c020a090b0d02060a111209030d030b03061501052b180b04061d060c07030305070908031c0612050f010c180527010303050a02060c 67
    0x101181d0407004a03000c0c920700300c4000812590228030b075401c10990b2050035a2011043e22030500540d401406108130303900845191f41042d0f51074424004580d000ba141e42d8000107040c0800f00036142190190030300c48068280b21401c4a04100c0484c10704100d175075052604400810f00c2c0d0103e00341084140c0085625042c204411522440002c1d65044009d09250402d00d003100ea050705644a0800c0c0c583c02e4480169070240051700d032440a151480304040c49200700c1c03a10314042582280729106044c101d070807031814015515240c070f404004d00003c0216074000000050b10400781c0c00c3c204646131144070750301d181a4686200b40b400405540d00500300c20b0800c02041c2003800100c0c80030088801c601074018031032403120300010210001c1e180540c05a03006502507030002c0c06204d000f161044003029002c00030000301e4010744003540c421802c41480041c00c01310a07000d0106003040c0c607a00c0300141ca2901c0d0402c4074003a00c203500b42401d209030011800203501146256189404001043d00150080c00a40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492613543 1250 492612293 492612331
    0xa0f020423040603050f01050106030c08070818190503030a14010515250602130501090b12041406070504090c0c0b0c090a03080c030a1404030b07050705010f0203100e 73
    0x128a806030868035102000300e0600c20780e0380d100c2d03100c0c000541c0e000042c0d0303000c40c10884989000b49000d12480002c00d05100640907010b120b120769900c1800b881d2a0141c0700e407101d00e2828071103e1001050807084c403c040980c01d00840700b00c5014030035481040190354a03c0c0480c0a04142e509002300c098040080c41d00520440d920300d201d104115110701d01c0c02d070f03c07204400c000c100e2500111422108440208001030148005a002400340608007511040300c1c658680046843d50030034840c10301900424002820f040d5a400d50b0160000e00681c5a1b02c410f0039084171240c1031000540300700c0081100090104003410150180c0a20100e0b1410131002c00e00c40ba8442c090755103401070040c0503840000501590541d1584180d80c0519007044141d521030840380345180d0b5907030050303c1a0300032071035462400c65101c08c1d03001200e095a46c0418403030502d45071168203403220380100500700d41d00d548503021226001e9480c03024510440b00150076401c400d01d000e2a54004503c094514003400000b51a10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492614793 1250 492613543 492613559
    0x902131e03050c2b030f230306060a050f120603160e0f25030203010602011a0303070809030304090e0c090c071101080c04030605010e0108060105031908030c040902070b0a0f0204 78
    0x3c0c00b804034166402d104030700c0c0034a80401c2020300f004010380c12000d0b21080d0824580e1000180c441c0300465120103202000b4840d905202c0440201100008081000020b686040900241c03041c0034541c1060307802d060301d030344078028540c103d00f42400d508090341701000b001745400c011412100203600540007000341080b08071201c0d11401015680c1100240340401c401c074028640700d4084034550b80704204440d01c2410300602a600030b11402005608140b000150400f1340304800ac4080001002913103405001e6441d4489900a003d40307641c0b600040c0702c00140040c01d4050486a40e400c2005801540f60020410840d11030103441011080e005110440c0091460041c0f4881520242000001565684a4101d00380b149400007080681800000984511404402d1713041c2d0345200140c40781681c8500a0603a50314590302064294110b04030200040344100e002180c000c034110310781600c2c09480c1c0d58040b007660300c41032041713609210364010420f01404502c980782402c80003503410342c5450314002c62 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492616043 1250 492614793 492614803
    0x10902030618040302031e0d020313060c0e03151b030c070c0605030f24150c0c0102030a0906030209010905100c060b060306130e031917101a130902131e0305 69
    0xd4042407d41010343e1800304130b00d0a0b81c40d5039400ca0030a550301e00c1c00c00419841004007a03011a500d13030030311421030140782c041c4094018a85c000b038002d1110f0711002005c0003810328050810450f0040001640440018a01c000e620440c482c0d048c183e45c074901c034a0b140d090040154880c06c00c218003031003480880e40341c141c0d0040d040b80e40065142441147c1c41021011040d1b40c0c4c1901c1da0140c41d8100d44110100c40d0700140040844c29010b5402441d14030b401603827640329165001c8001039240348140f0950b03009501600680c01e0603d480e10710b031500c49000c1202007089210700c00c08541c03400000400c00c84540100304002205a5070142181440d80225003144190348030807040c00d4407203690340c10b00241003041d01c1a20055804046002da02c1d0540035101c519004144000c0c1c0d140880040c9404442c1c00f600c0003100c0620b440d4000075131019107200da540d00020444005907504540020300c401c1070b0f0000d8029001181003004102e1f2615441c110000c404403005166003090030001c00c00710b200892 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492617293 1250 492616043 492616057
    0x807150216031202010b04021303022b030807030e0a060e0610050f0f130908090114030c040509180114061e131e091505070e0d080901120501090203061804030203 71
    0x12450105183c4070802ea016002100c0103c0d0030034408206032010700c0810700c43c0000c0764001d8071002007001c08074014035091074031800102101e5024821400c0007901c600b244a910152038500000c8440403c0e0340780e820005140c009540e4030380c1307407440000d01c62800d020301c81c0c01c0783d21104200c05e11450000400e8083e1440c998092003803008040701e07561621036103860240d8024000c4100081070070b9250400d40350f04040340ca5800144500f8100d9200000c1000701c900170381c0440c2000741041e00d0242003005082c001816400c0c0101c06002441401c402400f414a04802c05551020146812014082c0d885500581d1080c0c031400c440400d051ba8440d070720700480300e0311146808206140b00c5070240300c1c00c2c030039014a502e509140102403c00c0c85510082e503402c100325030303000780b10342d031141282111402110358886501c140c5c0050313410006030744900100045001170606450070007064000d641268026030041c1e4040da000010440c092811007000c18000700c690802151a0810340c4009503a4003e900d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492618543 1250 492617293 492617303
    0xb13030905190506040803071a100504020d1b030f0513150f0b0604030c060210050c090f01110d020703050c061306031a120a11040204062a0606080715021603 69
    0x204202d058885105140006018090718050762180d4a444035940c1c1c1e4041d035000e440c1080161a800c0d0504110100140500e03120032080c1200d0b802c0c10100002540800402c00e4010366900044080403540f4220f80391040d01c607103000031034400c40c100c0042900c10081c80050072619907409800064580070f518620310300324000001d40078410f940050010003a074084143d120300040b600008000c4150007260944106034261140c1840e80001001501c5069941c4129440e092081c1c207554107000b404400c50b0101490003092011201c4451400c009100000030016000000f05000f0f20604008181c0d007010152401480c144059058400c0d0b120341780139580c01c00d038841905458005d107150034841c82c03500081459600640c0d43c20081e82d50907464070112150030040e0b609003406d2409200740e400f01d861689400da107400b0602842078000205c1440014801c7c5a001000040b601d244600da01904044c00100565810b0030303c0d06001c00210300d00141154803441c41d0158021145020008a035802 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492619793 1250 492618543 492618559
    0x6080603030d151e0611070b0f07050a080d020a0e0f06040e04030207090f0b130b0a05010e040608100e0f01060518042a0614180909160605070b13030905 67
    0x43e0941801c10102984100865091316040d1444000400c2d407820071518191901e05050045850060300c030007040c42940c516460612113640194400801800f00e5403052040e40c82c80380c1150b4900c103080c0c00c902d04030040c45500ac03400100c041d400c65440014134104503035490300210104006905441030b801800700741c45508001c50101802041200003810b9050401c2c40085100c49402008082032882c1c24401c501c0048980c4950086100310500f050015200e901c513b414900195510380c0d20740401c60704141e0303605c0000760005042c170208214104520010503078a403400324035460402c40c25510f0000da49414010070040ea82c00d08400124001c090560980b40d03206e05091030100d411005526440030824032403403c030703412060248140d03140b03500c61724601c80d54040f5660301341c0201300c01410101d894000c1402e1070b2070030982030340e84545032004943c10303024055032010484400b540400301103100418000100010803041c1a07200c0b003103040c0840032815a0328010001c083c903104040c061002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492621043 1250 492619793 492619811
    0xf060b030423030a1d0d15050612011505041d0712060f0f050603121224030703030c1505070c060b1c05030d1a060a3e0706080603030d 59
    0xe06501680d00001e00540f13440b440c450401a0480c1c1080c40f52001e0a00e04024100540c03134070428030301503240c202218111014002d102c1100600025012030b038031030b50709896189418800d000c2c0b80307101203400c50340030310851a010510080d651554080c03a40114210701d1801c10020004410040310106609482e0300c54440c14402c0042840c42042d18206042119445144209401c04d9008910640499103442841b13142e0150b02d028821080303072079184c0d40d07000c284110300c5248502041e2580c41c180c0008541441d001a28288480c0e00450229440f100140140f1000003080c0004d04a007010034005e910300064018075141940d040201050758828440c4940d07101c81c1e04c001510450700040c030300c01002505195640c1d40013003800001c0e003070412402c11117001c140e1b040c80b94100c9010b45103d0401003091070a45a002100c40c000ca00484280a10321070b0446250001c010404400081e030001c4140c03a4017a424100140c00c03e0050000c05418007a554400104aa42c441c8061100142c4071607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492622293 1250 492621043 492621083
    0xa0b06010e090a0203040506061e0f0a0b030708010806090a0b04030c1505010906170714100302130f150306033c0305031f0602100e030904050106050c010f060b0304 72
    0x4500a140c2c0000b646010801c07800b50b203900542c021401102140c19640d54001040340a40f0a24100a0300030031601d0000018101143c0000056500601c08880c00d230b06d4016406980d003049071854002402800104000c80c0c080c010795421079018000f410240085840f61320b1151400743c0004c0412141c002d400040c01400240c0a1969010b8403080c809940d407a49880c0280019014000f00710300300c1207503500e5802c0c3c0094000111124008026032100b0914100826003010804d01410715400300031004589842c1a0340340080c4c00e0118511030800e0404c0320341d45001c6d8411001c0028140b50960038404201644c0c28800e010010005c80e07000041101d0a42d14620540f070118103c200e0503000301d008064011002c2e6215407840c509a03e0304000703400803224000114410f90f009600105031100912040d40c00c65401011b03408101c03072900c03601001080840360264043c000052010a500000d4003003030203100f882040c101410300c0020b041c46201949807201a000a1214210044404140e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492623543 1250 492622293 492622307
    0x1d090307050f0c1309020315041e0b070f0201020a080c0f1209010518031201180e0d02071509080c0f0301110d0b0405010b041d0411120f0705030604050a0b0601 70
    0x1560107800d9035102c1012004241e690389060b50f040388a5802011406000300340b6109030841150018000d104400320001a0035490b040500140c03185961400398450711902c4412041010b03110300b40c22452403070521030080144140310103100840e401080100400e9901070396040e040072880d040d66558403607080b07001c01c030341c483c50385035407224056502008a22001035000e140700c0d8441c01c6110560000c581940f075224070940c4c0303000ea00c0580d03020051161002041a008044081e20030004001044c40e09403850501e050840d03c005a10240090001c40c84240d4440848006070030050506800c100740070f5180d10f40c41c82c115002d1141242075034901d43e02500711002c2c10007c00d544641d200180007020020300700c100c141d540a40d04020000030880e4100c0125002c403402040201950341d0180348000c00741e00d018009030b4503c115069802032a903101c0482c103c0c5003210400600d1800c2d40369503114109041540402d11a8124a04210104a000c504038003026030200203400155102d07030050301c5003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492624793 1250 492623543 492623557
    0x40b06031006080705031e1f0609060905150102210903150c0310060903022d0604060e0913020f010c15020307030e010b19150c0501090302251d0903 65
    0x203905010700010030190100b183d40c180e44058081d07513a040c2c4070b00000c002c1b880700020740c0070488e884400365080d20f821400c40300c2c0940d50042400700340556100d0904003940c2080d003242042c155150144840d00383c00403c0581a1076080c005030800c00c0d0001e1464002031201c8010013004040011100f2443c2d506001009140314842000c3c22941007246482c030507500100c0d05d03540040303166036000c500240140880401c42c2d50060030514659032041198500300405603000408409210409040e030755648043c00c080d00103959844000c00c031580411911540c060500c030440c012503562400541c5940a0b4118899828202420354074151701c0e10300404c05d901200072848078400320a218215034150004580d6107542c10007440f5241c0440d042014076011201042e4440c484010200168802d0b503c3d2442d0010032400c017500d1501c6a600e81500392680c071881100160086400850300d5014111010f04250800d020401c495003011841e51400a20720103001402181c000040c80e040320800403943e41d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492625899 1106 492624793 492624823
    0x140f0d05090d0507030312110412020609031504050a0b070206060a0311180f0f0c0a1d0d02030d020604151127091501080a0504020306040b0603 63
    0x1090384650440ea0704000c00e50b0260780403035018840c0700002d5009484101c885c01307401441d01d003201c1070b5092150000e8030034481402030629002c80080c4035681075400560310006400042d18245100031a40d0f1050030010400003044804074000d0301e600c0c851804413805407500d00d002da03100d03c0d00300d8030160003902d840c41c1003010560400c0c59403d03c41010f01f02c86841079a07001c00310b51014046400a503801840f6040c809140c400c00002030348a90001059400d00e481100c00900f404203180883c090702407215003c0c805541c0e50001808599801412151008450100a0744807e800c940c16500e10509030b00d007401c4003c0c58000c5440c07804010010500d40048200d1400710103192401c801c2d094920b001c642640c43d194024114041c507114003451118405e850001001103030006c2a042c81c240c240000e01c40140c80008105070000e5001515040c80d64440b40440c0c5400070120700300807 = true := by decide +kernel

theorem cover : BRFrame.Cov 492446043 492625899 := by
  have h0 := BRFrame.cov_init 492446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492446043 ≤ n) (h2 : n < 492625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
