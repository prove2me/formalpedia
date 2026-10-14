-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:54.638548+00:00
-- url     : https://prove2.me/submissions/0a20761c-0712-4e36-ba8a-c022ce18c5e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 374280575 ≤ n < 374460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 374281825 1250 374280575 374280581
    0x1303150f090c0302030f1c050703140a091412030d05040f0f08071a090a063c05010f1d04030c02060d0b0109080303010807140d020409050d021005010e0403050904 71
    0x2100c00004002028042c03506031a0703800c4070b0100780e004e48914045485000400034038109200c10701c07568139000724081c841c11520740d070107480d04030f0030040166508510711942001070b2000312030b00d807280243c260614640030001d4005800a600c210350103140310415480110450b02c68038601c810100785552a403c1c400191842181c000b0049071940900701c1c01d1107005809040c0161040c5075440c4040e2488489440000041d80e02c04125048030a4610000d801c69100c011621000441c4401031000881142c10002c029a030b12558924010004207052040384240c82c090010700c001840218105004280c41c20b926810044461440c03501007400c0c58000d209880486500400030b503542c0001c00c04441c007804030540311034081501f407080404c11010110542e8181c81411004254641c940031388405003c0c20540701d190804942d5403014003584581c002c04800c0c0d809580100b0380c1c01e007841300080c41c05800010f40300a02349400f005200280c50706601c160001e426160a81c0c0b1351000c44002401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 374283075 1250 374281825 374281841
    0x3100e04030503010303031a0603060405150a15080109060b03070f1b0c030506071d01120e060103081c060f050907051209011b02120301270c03050a060605130315 71
    0x10640040400080603802001141641d02c2550188240c07107806556014000f2035450180e13101c40140001950781c186584071640c40400c0d0420118480005804207513240407603046019039000c6102c000c05195041220b080c014a0040c0701046100d16200454105010282010041140300c0e54030041107803003251107200c101c0d10442c01140c03100f030600d8018218102e070310044942e801400c00040c6c0703044c0034098224084010303a40d1103038143c00203801158945007044015910700e03030768850000860802c100321400b841c030580e0384a59803054082e0070020851240c0000d100203040c5941408600c2c0d14a0505084410649841e0070f00c0e10742e603034151003c0c0290080007405104440030403c216005400c8240400911421600c04490b00c6c1012a10b802d0b1640c41e00641c45400c1004228002c0d152802110410341d041c864500da01c20311003210140c1d5044803a080029486105100018096228050084c070700e13410841e15000e4810302c0d80312010b900b0310025040326500300660560025640003080313 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 374284325 1250 374283075 374283089
    0x6090a052e02011b0215070e0d08040806040605090a1a040606081c0801050d0309120507080a05030301081c0807140f07030309062d0b030102130e0609060a0f05060310 73
    0x1c1030814510000740204040b0400032540c4100044801c00e09002054901505d0400c0092800c0741e512036900b610704281d81408590003610145038400440e504501410150245901800007400d0a06240c02079400c00b52011546410444103000050f1508680c00c0d01c041d0746051b140c0d501d5843e4144940105016030020b800380c02454240d04a006126040c80d43c040f1890311408056621442402032030040380d00014086004040107000e560100c40c90f81c800e6621910032207809035214600c050030400c5514007192643e1002c0011b001c011400c0c0160044540750032404084000040030003049207001074802c40510210311050b000d110804c1c0103e8200783d11144503181e5440403454014000c0140401c140d81c0301e45003d00a41540c0318524444c000d6640c019445440003220b101c0b00070041140c0303924941c0c0342d942002640c00418800503c0d600400449418200500d000028000001401840702e4842c01a1a40c144210b020700d80c0f1070803e8a505481407601c9541e80c0313000d0003511f1070b0358029203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 374285575 1250 374284325 374284399
    0x3060e0606030105010e130602070819051b12090405040c0b0a050c0f030301060f08070c1b06030c0c05100b0a090e010c090801020c030d111c0203011406090a05 70
    0x5601440020380e14000c0c0000e9001300580d03a81c03203079008034889040c1e03506250807106c181018040307041a0082c0880f180241c100c1880d04a0300c0040b51303600d0400b082c6150200307001080750005058408016209076210340050071084600303510210b800d21030968014461a0f03200e010506001c01c81c09a4405403c00ea40f02c25507802c45000068155080408101c2c4580b2030080807000100f008001d0301e04880558450301259103010400751800d400c010101e038200102c0c54100c00100d605403c0c24000c580202100035040c90825000406a80c244c81268040c0503411005200081c000200340300c4042c02c2c80c0d4002502d040716000124440c64a0703004400d00f40c106584a1181e03841940f0440403018241ca403040866540c6420900380e0298a45150700f5800920451041c100517800a119060b02651681d1a00c490103001000b4495030000040304d250b408001481030549a07090f4484034401280e4880c04c1284641c00651054801e016007401030b01140f1840c11070301c500c9052940c1440042043e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 374286825 1250 374285575 374285591
    0x60c050a1502090307050114030a0c120c050403110303031e0907031b30170c010903020a11010309020906040c031803020f06130308060123070615170d0f090306 70
    0x100702a410081e0401d22070700456030300184039802510400402c090341c40d031040c2140d030313900d02950082065140503024441c040480d0714034201d075445050351100c1640c8a05032507904505006440545049519000364400c1040c0038a14007452100300340848409003489041d900c12030405e0405107a607200501440f501c1c08501054040c11903c00c3c151181c0c07900c0740010342c07088c4002c4000722401480d290754004c1503000d444c0104034001d03c0402c2030600350018034545441182c0803400c440d0300c5e100a8005820040701e220420a04105200d5000001d00e4107103c0c3c99441c2e00014010400030b440c25214076620341c80c10204038040c0d0480505e01d007020050312045151414040d4855400700e03820911801150b0000b10410381c09584840d8068041d40c1d10b10a5a03184001582c40304289500381d111080c00095500b00ca0660200400c003a510400c1e021803802552546a4514081038014003078010b020810b802000d50000f9541038210f40620307010007031512626080d40e10504541010349070030308191030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 374288075 1250 374286825 374286863
    0x7060501050f030a021806031c020a06110a17100b040e07020601060215060910050901090605150f070b1b1207080907030201090b2118100213060c050a 66
    0x860403204181e411901c0385a290741010340791200a600254018412011700d20202111000680e1100c000740c00c86416004032842c02d88000c1503070361f6140060780504080007c00196014950728421001c809a00708100710101810300851581c180700820700c443c0000304102001d4040400074807502c0815580c1e140c490307050340a25030044501c0000341c85030900014050b071000482040c0c103551080d2000050321090708000c1e0700301001e0004444440c9001d004540c0340c5d80d08078481d00900c0028800603103545801e090044489005111907202c5400344422090116040c003110b0090742d12130803ca185540d40c089d480b00d68115989042e80c0300e400420300058400d83d480032103000744a41d44404081e03a4562904554480a60000a0008000800c00c0000302801d4003d0410034020100d8a41c50116180c150001e0010441c1c00c1d0028254101d002d07074000c84148840c3e00380d04044002980b916041d034210000750030329803050313030208404031036502e091000a10030701250a07402001e1070030121500b45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 374289325 1250 374288075 374288081
    0x3052e0e0106170c03040b160e040c030f0e06060a03061815050709050603091005090a350a1b060e0f070609080c0a1806170a030f0e1f050c01020706 65
    0x142ca0400c01c0e1242000c103c00400e07110a17244101d40c000d00b030446035640c01c01c0c0b401d200204285140f041c07040c0801400e00540d52030262044048031a030300002d01c040749500e03542c2501d800742152130442d0045000d009694403840100b8080d48d41061003c45e242c005510154064015001c0103048002010f0450f9100e2100b508540c0c050455940d1701d45015491b00700700020340c0f0040d03070b58209650008040c80000b41c959000158030620041c180d034800c0305030f40c0310700d6401e0401c1c1c00000c68504142c88118480906d1b82442d5420b180e52421841c1000410007000d00681040700401405e143c0c0d610302d4804001680d08080c11002c8428107035813411610840c0599078440c20f0040e10040748249134085107500f0b000819000c2d0020040041d20f906282140d14000d030b181039900d02400701c0c1c441d2001b0685280d07080715010001000001003000070111304000308400c003150f5001c0d0400c84004201421355032214035400910030491056004148010400d8507144290326890380300d0350011800209001c1d035a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 374290575 1250 374289325 374289347
    0xd03020a0302060f27010f0e01050603060f070504231215060f0a0501050f040e090322051503060301140c0c240103030513030b04080c0c0103052e0e0106 67
    0x3800321403003a284c0030740091500c002184c030705005454802e5a901181729450f402d88950382c090000280e11390107003032460161400358051110503034480c8140512800c040094550210f880402040daa09040d20002c085114a1080c001d00483d6010140c200c0d034402c80c50483c0a00c80104400000084030b0011600c40d00e020f1303001e4880b286090009211030810001040a50f18001d0100c28010b040500545198000310840d401f80d842c03c0c000400c8103096a03402c18003500700d010041d500d54807114082100c3c8040035220a640c0c01c1c21110401c10b03503d40180e0028580c0c80f00f40074a4882d500c841c0030078010a41b03440714032107100011b018000113100400080801c0c59201081d180007003500501e55032040300d8040c075200a24011401000440c0c4103030050518800c45218000034203a4070707111500f85060a90382940c110a00003201e0f88801020400d503031610b20203003030605c01d034a03042200d081d080d40000c07021080c3c12950700801007405c0840b5501009044080040a040d5840750001072210381c0f02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 374291825 1250 374290575 374290577
    0x15091005251e21020309060f041809050705041d0105240303121812030106030f0f05130206030903040305120706051807050f040608100902040b010908120c0a020d03020a03 75
    0x1d030000425020100c0070000303580d4200c614081c1001c1c008820f100400610b450381e000310b01040c09850501d80d150b600074001100b94807209a10b80f4180030301d160319000b0076002c4640040c90010000d00003200803400c241194000c0368002022105000300c4000071010709d010704210b52030281002403040d503084c0404240a41081d801a4242c4110107165032480f9040020340900030150009030703410800c070007112080780041c081e00c030a842104103880480d00281c1040f00072a8035003081f10011076a901c80c0601600d01c002d4240801c0c00c1441050b084140c039010064042e600010000340c1c01d034000c00440d0015544042214941c0200c241807403101e4000102c04c6030150300f8100440c02d0719400d91103c9038042c01f44400b808965103010108034080c020700465641113070f1540c0000540000c184122030001e201d074400031501c0d6000e40f04102c00c076850500c1c001d0502036222401e01c02e6200002e2484140001305a50359521014401d01034500802c4990096020102401c088101940460140001442 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 374293075 1250 374291825 374291843
    0x7030e130e010c0f09050d020609150c06100b0703080411060d0506091305190204110a030b010306091b03090c090c05071209030b1303090806010801060e061509100525 73
    0x403482c2191544d00700400200000c40f0a5020320007441c0001240b166a88003c14141c0740c01c290300007203940c0348103402400c0680c0e07a001c1640c40d2180000d12450f07520020035003121010030b05242c0b51005600500b000501000708420024081240ba101800c0702184024a0151920800d0024030083c02b0f0442d0031601400005020030020558414500300d01940500645086520705c40d14041086c04080141ea200c0e843e070345c0240044544600a10340380c2d01b65540424040314903c00903003610f0250380a580241d03c0c00f64110b403c1c80800400484091051401080c1c620302c0341089400c03480c0740d4000d403103414500311048010720303048001012600c1c4101490b012500500e84140d40e111300d20311001c0d0a1004200001308404007070481220290311a040440d00e00703440c3c0303414a25050090b00001d445a64800090007480c1c800000346610540071100c0307120500241c2803564503800340824003070103940703201440c3c010b1034001c10070781d9400d82840c404010a2420a0a5925040d00c62041600d400f09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 374294325 1250 374293075 374293091
    0x803090c1909180210081504060609030203060906010e0a020c0304050414040c0f0303050a08040f06111b030405030a03110a0b0c04031514060f030703050f0d0206090f0c040207030e130e01 82
    0x500f404906002038000b092036450032000381064900110041242209050400d20181150307554810140076002a5036070b170018608510500d440c01c01c1c054a5905a540301100403c45821020801607001282c40c4001d03895641c0c100030346107180100d40010b0b07440f604100c0b180c640c804503d40ca4a2046000d2140100a56590038400f440c0c024a800b0140004100300240c00296010f1802280c000d40f00307030b03031014504500c0e403034403012100c44406990704d880000500c0b100400080321440d0154240703c000d0742c034080c940310011f591202c16540040510402d080784410881080c000350480540114a1035103500e0505617844081c1d00a010407a000700103241002800741749485800c4001d00384410b1000c0c0d03078079200308102030710000c0d0b0196680340c8070303070000400060005d0104115005d019001050034540954001e410590010042006e985c0007500c1001c690100040313081e52380d0400e69006070b90b0300e8a41412074a80001c4100660090318844441268038016480000c1441004008102c5a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374295575 1250 374294325 374294351
    0x301050f1f0303020606010c02131e0c0908061603020f03070c030906110a061104170109020f03060c161b0602100b09070e09340e010801030f0803090c1909 68
    0x710050001034010380c84040069a154087e039540c0b184540001d02404081284507030000a468204003010300c0540510350324102d41c641801641d840481a0800501d098100300d0b00c02d5503680b0081144211854803035003a90110f0003981261101140c1e0007455030359161407100945104c01103c01200010944000003850078422003c9140803035061000d050000324940b103000c0908451040a5203403030080200003040521740020600b03028182c0004110003060b03004100451200b15031381402a0040130410104103d40f40444020b1141000484084d11403410040e406100c13a1509042c0042480c03804105030b5000140d42c464042e20300e9041c041c00580e1014031065007410f451a4020415940285000f03240001d03842c3d0f440b254001c108004068200d441100a103403012070304807549481c2c0102e043c82070740a40c0314100301030b017030a001c0f10a52465a41c15003035800f210015141000110201d80100c209000514181c3c1005003e80e562a020038800d007079102c01e0b4455540494503003d2000450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 374296825 1250 374295575 374295631
    0x2090d0813240f08040c080f010605181611070e010f172b0c050601060302030613060e04020405150a0807140d12181d041502030402091506090301050f 66
    0x1115482c0e0343d0a510742007185042e9004100a402115810315101e004aa403c50400c83d0104800505001013841c030324200c1070040441504c0f5021201da2000c0d41007025607000b20f03032145010211131a10740400e000e03415a05051007242e401801d80c1002c01320001850303610356502d04050b61202d2080f480386100e001600d035a62002101c5072030494207041c040c01c103000c185084560310344041d8101070050703060035038a80341803504c240c011001103580071042c0031041c01c0107480c0c40360381080c000c0204000c0d410080800c98040e40107100030301c2592a1000105810041450301c4000c040c00b03000611400d841d0300400362030b200180240e079889100f8189410391880d2152a8100c00382c0c00c01c0070a04a07040ca10000c0300c2010590744114226102100d0000300783c04883c8054410001c96071a07854603086c149401343c091050303410368000450050060101580d5011041d5800200c4900b0001c50300034407501041c0240030300401c2552551078001000018510034011034801d907218403d031014100c184400c6210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 374298075 1250 374296825 374296889
    0x90b1501020309010c080a180e010306060506030f010b030c0c03030a090312061212140c010b15040303120510091406180903030a0b0f040f1e06051302090d0813 70
    0x1001d5007040390101e41040000c00c1c03514000d103031800e0010b4802d114050051800d43c00090b009c0760120040080c8141c911807007000d0001120620300e50308140524480000042c01080d540000c0000414401006c10044510300102c02c0143d039182c0c80c101c28001d005240961040e00401d182105034502000c4031302c01c5038242c51001c203d03038010f1140764840ea400781610105100034010030f009808940850380c03019004c1c98204a0000c40d80f01407910900c901c0102c640006000d03403a043c0300c00c3c800240c10500e580e18041e40300e4230005541d6124500d820f441c8826502090b00180340011585c0211b01c1c010b411446154140c660450000010300c01c001074400403a220600c5820600104190420f00d8100540c1e402009140340d00c000b00e410001030440e505083c142c0050baa844d081e421000200e00d15400d50005003940401440c0e00d8036011079149028041402c0800c1da00280b000300d00d558940704006800d42020106d62111805803075003a10b40c865014611540030107082284480740c00c0141462 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 374299325 1250 374298075 374298077
    0x71b06020a030c050309040501030c0303030c02070510050c0a02090c0705010b0913030f03060b0a260103230102130803091503070219231006080f0c09100306090b150102030901 77
    0x1007001c141c0c0c034125505a81e0708000c882c03030b000070420000241d03924082e660185d8024402182e409155240290071940092044025904465010041980ca0108000c00c060490520b150341300d14035070301d160900491150080d4050040b20034008104226006448084d00c030344020458041d110041141c0d419088808072120851307094642d000900c2185c00c9036902c3c02c03500340031500c507480e0005c40e911030304100c1c407690004502c921103002000d03210303031056040303823204002503519411a190f82e80380d4900383e4514165881e00000d0320111790401d60440d0300c00101e148234140441e4a904030503842e60b109406c06446a00c3c000c01c5c140035446584e088a0184030a50004c00400102c45e6060501d40300006c002e41f6200d00d00380c41000003ca10069004002d03002002800250030341800c64400c803141904103031003903031107071500caa400140000c0a0440b2a4121529581c035a21051492281d00701500001d0125040881000400820910450040e8500b180c02d41c0c10380f1b590001245e6034064556040c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 374300575 1250 374299325 374299333
    0x1202061b040b03070302091203030103060b180402031015050a0801151a03040618050102070c0602190b010b0d0605100e040b06210408090301020c0a021302040f060503100302040e03071b0602 83
    0x2842c1c00340207500901c2c00c0f04000d000235003034031110f10440d41142c01c02d03030056030042d0300c1d510f1404491821340004100020000c40e1140503042603004280e841c107000288a8205686690300384a0075003250825005110080800444a4a501e01540a043c180a80d030b4282c028090010440501e14900011402030903030308182180d44548842000e40840325480e80300001025003000031403003e00041203030074080d051041c4000e140c80343c0246080b02043d9030010484049140f14009a000c0e00383c64111184040c0d610340354186825440c0082c41c0c2540850307400200c0d0440c0000f0281c010100e05203802d42110100080600d55060002510a5503410701c18104904001c1d0f403003c0c00c817581140c01c540540e10306401c280c1e2000c0403e013203074000c40e41058a940f0a0040c0011031902003a6250800161502903052030f14006d07540b11100c04a00620091002c04000a460480390800000086030028401c0c000049549503603030322640861015a48040c880107010800c5d1039890454088808543c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 374301825 1250 374300575 374300581
    0x203190f091a0309100c021002030a110c06040b060901030c0608042d06050c0901090e130c0603020a0315030b070f050c070b030105030d03090f03110a1202061b040b03 73
    0x2112156050410841480401400840c0300c03035a400744400d071030060200c0b081d501c1c01c0007041240303028600c64540150b1070500c4480101d01b54085010003c0310400800542c030303501c41c00c9540e0301802c0421485420100c000c00d02c2a00c0c1030300041d03081c1c000d0703016004006054a542d070910010203400d00024108601d5080104a402e101b0003800782d11902070200c0b00100c1e811000c03552000b00c1c544038103110510400760f03003c00b4024070b486075070341125500c07c0310b0780380181c0280060450342d0a88280d40146800c2d000140c0000c628403018420745900242c070089040c5c8441c4003800a40141c20b10300b00107854898800c03851002082c50301c080d02d4020b02e60200581d2071500c00c5a403d2030403226901040f20a2083c00503140e42000400301a003c0044002d8482d8144400e0519240010340410201420044918007161040000909140c1c15142030810200c54500140c54400c15200040c000c40d8003d43e09411641d0204041d802100d5588100d007400850325070081d914011401034252500c420004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 374303075 1250 374301825 374301827
    0x2070b040b1b0f0304050102012702040504030507150c08060d0f1101022104060206100b180103020903030703080117073203070f05040506120d08060102010b1903050706020319 77
    0x140103000141480b100c0002c011050950070034001e03078004021a8404103080c8034540c0c081c05070031907108113210340440000168860700c00c4117030142c2010b0b000700c3c5ea82000c01c1c281413180088a0301d07160000f10500d400c401802003400144a54085500007402440200340c0b03d2a10f80134034054150840403801c7c0781c1b03072581c8405a240c02c003018454158070400b6a001400c0038941d0710482c68042c2e025005840c0c514005000c1d00342140140084103c5412079428480344d05854155903c03020201126224400030302d0051717009104601045525120115690080650000b0600d050341c007102d00c08684100401d00069039400b03103010368862110310444491103400c000302410307081c02d40c400040a011b0141c502090600030700c1e4200580c003840e030392814800341c1005c1c0265030f00184242d4445280c074050040480d00e400c0c012400004101c101c0b400700381c96a01c01d40194000000041c4072000e50b140d003555003c51210b051000700c88a018540000078500d0011041e00e450f0a0526224190103036081c0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 374304325 1250 374303075 374303077
    0x20c0103050a06050d03020a05011a0105041401021005010905040309050102010b030d030e0321100506070b071803050706020c011202160f0f0b01090c021005063604061b02070b040b 79
    0x16218030b2a41c1d03140c0001d8550307201c0c01c3ca07142c014000e4000d41070740c07030060503d6400e4800724607501452400030b0500207400e0743c3c410304071007c8034042500b000350b011400c1c00403420508220315444a15040a00128601d030150740613500640c03098840d070240507a500c0042e03003603904110481e43e040e08084082ea01b2540203402100100d161202603038504452511206032426140782100e070080f85c000100040c0c0e08100408101034501204c001d410003c02d0307541d079010010002c000c4000c003c00c0c81c1e0813610410300310820310080c55005090301c1c0f40b6512031b48025038464460110500141c142600007184601390300c00c6694400700104004000c0540c0d8580c100010b44080c400c4130004200040e0398041034038002001d020b0240c3d460085624100000000d24000010a210154510341020f00104c1d82c1c8040c0100c0070080c0a8141c2d10620047e000c078042000701920f01c030484030203400100000c00825500601451780400a0512200c3c070148040782c0d02d0f41d650090a9645c00100424450032162070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 374305575 1250 374304325 374304331
    0x50118020c0705090a09020114091509030109060908091806130504031107060e10020f0c0121090c0e1b070609020d0f14010501090c0e0607030203190c02040b060703020c010305 77
    0x10040b0303100300390703103102180110000302c0da080c80700c07665240000110342c0e20800003c0e10080800c1000c1c144400b140018a0b5246100641c00e820b20000a01d40380d251000e400c03032610b050b00100100315225107410510b15540c80100c02034810703020035a03540f02c0031b03c0703000380c203401407501418250860030300000c180c0043c180500b00703505104013111074540d10a000c00001c1c001d400145d80301785489621070244401a2142e4000c001550005058040c07114030020790112207440c246000344204e076051a00806480a80700f45200d114240803a4001b444a569502e600700c0340111b001d0b444c0b6964007a103001042094409000311400c1c104403400c08580143c00064100d80000c112041000321941c0d207003281c4022600458241101c120081a042030a2080c02d00408819100340030911a0340310007401c3d04484410203218443c0030403000103041c8200250380c50a0100000e00c3e000c1207400c1c60241c1181600c03a0100d00c600e060010f18072071420040251060306605800800010207841c0055014103001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 374306825 1250 374305575 374305597
    0x809090a0207020a090204060f1d0108070e040e03041e0819060b1c12030507020c120304211707120e0d02041d0115050312070615090f0f05011802 64
    0x20b00803000036030788180c0c000b0014224803c00680d0b82d4600318000c4c081443c05010101801201d070a06d099403c1007a481034044d1809203010122540c1e40e100540d404250514410740080c9021550014024004028400e5984200c010911299890450342c02c000b580e0103a040250850b00011240340b10a2400e40901889040085040004000801c40750070010103810f03014024035600c0018084040100c0c1c800710803616041c00340b4948010065a1406400d002501550a89d25043c54085092003038401034030462108424103035003403616209109017050151951340c0f4a4404028904d00c02c01103500c1b083d480140c46000c011048002d41c1c0070030f100d000c010b0300900b85189880059582d4400c100e40c240c800a022000c01c50a980c0d11401c50740d842d240c1b41003031100f44005002c542d400154600c0950001c0b03a50300d41c1c411262400230080c100841410415584203100170440e11782d01c1c1c0005070104000d01003045102c024001040030360b482840794440c0280a03c244980d401540d80080003040303c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 374308075 1250 374306825 374306827
    0xc0c380403022d04110313051504050a0c0b1905030c1b1b0a0305030301050607020a0e011814060108190209030a060203010f060504151805090915010504090809090a02 73
    0x14a401040b01c40480407000305210004288031881584a259a0311810f60182ca08000044d00600001030030b12010301f02410201034040b143c0108002084a41084041390303688072042e0a05181260342c6d500c0b06a4100c030f6400d1b001c00049100140701d400e17603142c1c400741c06018652030700c0003d040c0c440398800740040c040d00c0c00404c03101440d200100c0c00c0c0c41c50701c00e0130001441e1402c454a02a4604c001c522034151050b04c0103502000814000803e503419150304031403450750742c1c80710310000318a00700542c40310710030b1040040001054062110702034543c0c0c001c0ea6080c4801a007800c00c1c402108004c4410902141d031600c04101c4210494040b07001700340c0101401841c04620800003842e00b05003013411621741e0740000050281a200388c40f51001810603051450409040c0841c4500800249814070304125100e07086814070960a4014001481f000d007080100c0d0500b0082c240d11000c0500d036442e000e6201000000e02d03814540b01e00c09646400461441c14400c0f20010004032040240078901700e150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 374309325 1250 374308075 374308079
    0x70807090b03180c0f01020604060b060705070303020c10081e101a0d0b010507080403030e06040914040c0e090c04241d010b0306010503040206030a1b0c0c3804 70
    0x40207030021030240b40c0921103c0c1ca0302400800b114036084600c0800e84c09145641c0901d60341e641c000a400d0381140e8005c0012416100313840219501d802000f5000c0c04038440d85800105144e0041016a843c0d101a103409000402c80503040e1590482a0b034081c01241e00d803800c6150030741c80948a80d400481e1a64138882032640c0d118807643c81408402d90344030215001442030701c03410300c522030865009001e00306681401c1d0303541c5408402d402188400340030311042c545641c005680780002c0350041d0001a4040210788100d064400c04808116022207110003c03c4d008a0089007400300d0034840e940030001040c02040600911014100f0b00b00b8030680384d17410001b2020b940d5891454140130384242050f410700588240d1050044400684c170101000b5810000d12803540d0f4440100c0e40d0203134060f9000c5699071142a401d00c01800445450110346120240000c0ea0680c00600110824060001b129401e0789841e801003400003240707009541d140012920030f40c0c03e90f400c0a98940d0748000c50304a420a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 374310575 1250 374309325 374309339
    0x210b070e120124060e090a0e10050402040e06010b09060d020412050607120209030d0302071e062003010506090d051e0303101e0504050a061a040303080c070b07080709 73
    0x91a1a104070740c81d9450340c449070342140c814411400c903041c0740d00c9150000c07403030000045c1000d034004105502680c1d80344001000e0384c002e50040c4440103128000c8a241e128410f0440009100607601203110b41d0038404407096034140040c245050714807000700c45203043d03248400c0042c3c66211400b904a295028407000030b4400301011b858072442d01501c050700580c41c0861009084200c0111107001142c07051011030002e0710b00280c00711566619041c0141e680e0b5150800e08500316003201107805500725000c011041044d160420720800d4445500b5444403000520b44400a001c00d000b1a6000442400080134a15091025030142e030701130b0060303890301d1029100751f00902c00711402c1500c07550f1001090041740501009030000410701010381c0c1c24004181014003544541d148070b21845252140046812041240d000307100030480761242003118500400102c2c00d0380c205200681c00b0850482c001002d443c035140c11513102030343c80804100749036168407056444507006000c40c01042420803000c1146 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 374311825 1250 374310575 374310589
    0xf01050313051e06060a1401050a090806070914010201140a090809060304030f1b050a02040507050c01060305070f0f030312090807020d0503070c050a05150f0706060605040906210b070e 81
    0x18801030b48042e181c801c1c24030128134000000d41224081c80d116a010050072200365100700d040202480d0250380c41c0c460410880341016281c2105456018100c140030755160048140c9040b03400004009107101d1010006a080301c1c280d516041c00002000001001d6070304c5940b01c05030b902d04c0b034500241001324540100c1c10a42045400303d001c50070541400d5580c07504582880383c142100e10f20b0216000f144c1da649a16840c46400c024041c0b0744480210345000d0241060fa0700c0940c034003000b00304a42c1d403810000d40c0c440d810312848051300302140003c0b504228013a21641036030327050b84034294941c0900710024000c00060f0b4080d82c4c581401c2c044040140c2d1007540804610b40581d006688815903428440001ca59a62145e0300c074064001c020480c40c1c43e8041c4c00b4180759941581c0a46880f01c1034a403c0072445407040044c891880d140c80415010b4004008e0b006465002a04002843d00d4041c20052110f82d0584c421040c0c00300c200e40c400103440001801e03840380d640c1c035200c20002d081d82c002c9154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 374313075 1250 374311825 374311843
    0x50f01020a02060a0e012901031410061101050708010317040b181804051e0f0304030f0b0117030724060f05030f190f0f1b06080c090f0105031305 64
    0x1a0450f00c1070040f001418054091041c000200030411400b0020340d201c1c0c0f04494070400700070070240240540380c40e8025441011101074644400c0d50a01c0c0802c00141041c0f160300550011400d132410102841005106891040c113150329803000c26400c40e1101500741d40f414814901c211001c12000c14251500360181850103003115890300080600001c014024508803c00c40341c0e00100410000420740020705621041640740058213680c2c42c410742d2a081c000315030401c0d0304500c000540042005407120901c14039a0042803071403590f9072201500c0754620f4003105c244080364000c0c003036800070421040c1d02d003a02807500100410001c81494811302926025880142190b0030f04404000c00d060a00c2881ca020030040302400c03400007a00d0702000340c014092001361800750170451400410100120312188190042e03194002244001000d106121941c0648400038a05034003160156841e070b0150b07058400c006180d0344200b4044001166103800c02040380100002010008000c18424404080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 374314325 1250 374313075 374313077
    0x3090d050306060f0a091d040314130906080604051e030d15120f0c05010507030813050102121302030706301d03070605010b0c0604030f02032a0f010507020316050f01020a 75
    0x1c802c0d15180b4882110385540c843d9616105440c001c0100096012440ac00081348114040d170326014003124849600314a6004203821910b4a0b4002ca40803900281c0c40b80300368490300407031b02107607080600e6903100c180f4806121055803040c00b03c0000b10205401c00d030540c0700ca00416001c4982d582c4e0402c00880103031001540e50100c6c011400781030080c6c000b1001c0c080c1c5020300f00a0301d400c2c41554000e140280c0107200c200d03410504001c1008020080d012204080001640c0d5080d90401e00c020a013032a0780900200c4c4244108900058040d018429040d02440d860721103095110110907040b00e414002c00d41e00d0b000742da945031010460b45601141c2d0002c015450300958071445180351441c00c462043c0c00050782e0010601800030f18440000d1070a52103941031920440d154080c4000f40d1443c02481403160b281d08a0004009901d4156003005d8a074040b000103c4030b01c00350750621182201d105490900068204001c0f0301410210003c03424086803180048908460038070069508a8000316140b00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 374315575 1250 374314325 374314337
    0x807120f020d0b0727181a27061e0405090a0c0603020403060b0303131802040f090507023903030f030703020309100e030a08060f0a0906090f0203090d050306060f0a 72
    0x21118900300c038031404941710240d5220580b5400d0400c441c00341650003080c0d444261300e40d02403600b01c40700740b40c0485200002038601034500002c0340200308071031070b01c0c40c040c200041040001002c900d032000031401c484c64841c3c6100903603000f45e014440502401080301d5440e21402400382d00144050480030000c01c107030341d001038843c0c3c29460701206481007280c400c0e200ba03000f4030485443c60002548031049584102c0c01c0007903034688144800103030255074850200b030642c0400024020139a500b02c01e00c1030210350300780d40f4110f40715800400382c208503040b44181c2078881d41542001008800000032410001021a810311903a2240120540d0040340e09600082c0c000c0180300c201d0b40104460401062600c4060040d0ba129806c41c84d074a0241502c50700800540f080800c00301d464452b061428850301500341c824440d220070f202c00c01380656110b034000d243d15000150141011501c01d43c2c0c010980080600318459002208550715003001c1c117600d6214604111078004580020b00400046031070340c40704 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 374316825 1250 374315575 374315597
    0x21615050a0b01090e01060f02120a0e180f060f03030c01091101030b012d09050d050601150c08120403031e090c05120d0c0303020c0a0510060807120f020d0b07 70
    0x150082d201600c000c0c2d8140400d00304d080c0b180482036001d040c107442007447d1030f10005070501030403841d100b800c5120104141c40041c4010590794801c450710a040020f48103d4104400c0c9130403000c140c481140c20030001800380c4046803c0d894010500ca403110001421203042c00c0c180c0070503a00311b070503107107046804110b4000341c00c0e110358041c0203002c10044242440c0d010b1041c02e5a0103d0368000b201308803094845c00810003496a4040c0300e04001a26010f400388980c00664507007607648032030a0080d9140900307440c80405070b143c4a100942d801c603034060b520505001008603d48100741d00608101c09043c0c070303901102c07818a0000d01d601c60340c0d40c941e00040385940c0c950403e0007125030941c000d01c6c010014901003010080d0000340b15040324040c0d00d001001074100b41800c07002030141c0400c00300d150250342810000e03c0000100c070b1401018080041042540d10302e140b0760707911902c0c46082c00740c80038500c240b800711320709120000b0150300240962288401d50fa507140038946046038040086145071100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 374318075 1250 374316825 374316841
    0x20412020411030c0a0e04090b2707260a0803090d030c0302030c180d02040e010213170d1407050a0803041407050916030e010609020918010e040602161505 68
    0x182c0031812011070400c0f4a14104204000c40d244a415030140500401410700c24550b19294801190103812030099a1a801e00d54490342d516011a200003101005441e5800c81c00c03107001c01c0d80741c111641d4408041800700071000082404104111040d03c90150b03800b0345c40800c0c000c8004603c036039070b00400b401c1c291283e0b42d0041c0c122000e102c080b000309032050040203840c41c1caa004036007001a0761311a50701d0010000c4006029001c00142c0250040d00f44406480040015000703062000c12440c118115103031901c1350a02d04901a22803480349074006102e0010182c002c0d0051010480d11000351840d08115455007450f00d0345008003114940c034000100010710061000f010f83c01e0410001400130300d450b00001428240d00940441e0000b80e54251401206009901094640b55100002e120f40c5a403020200e00940002d100340e4040c10041c942d290b0501c1c0540340c0c0340d058600c103054600180c0c03240d80f101e000940200ea52441c201311034600b0400071607000d4800c04241116110041410714110701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 374319325 1250 374318075 374318081
    0x70501020901261513090501022d0417160803040312081501110c090f0601170c0307030b061b0a03030f020c0304050625050a02090f0105010509041e0204120204 70
    0x43d4200c0092240c0c0c2003415800703600c5281c41d0051000340c00042040024000140504c044840e0000e081d86454040c004000064006d003150f00e0300c43d5000525056105d07051003205980f5914040c1e0b840e001c0206205010340383c0a064190400c4608641c28101088106031090900f81c114041c030303600200f0300308100031010342402041309080c5402d901a0400c1400ca140b904142100b450521980c05030180b0005d00400031310161000082031081c2d81e0030034001d00b100090083c0c0c1c0c40741c005810700d4005900d000503101001c1c000c28003000c0309441c642e1030610450041c03007510704440c2c1c0020f00300480e0301c8a501401c0002e840d83c914001400041c040c40c6009000c991014000d0a20030f8014404008501c41c04000e4808035001a02e103241d403211b0050010403c1013496450b602e1590f041c0810b0b800303105c000910414440d1081e01c2100e00d82e101c1304c41030445818240300c0c0740d000600c1001088400e090503004204d0b130603200a451509031100010f400d041e81c1103500419084c0640000b480306528041c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 374320575 1250 374319325 374319347
    0x309030203070b071b0803091e041404140d05030a0c20150121030507020d0506010803040e0603070e07050c1501150915090308070510060608160801060e04110906070501020901 77
    0x2910302052141b07020812070310b0b4040e11800c0c1d48110044513aa44000b8401c40c2c0b05210102e00078810462142907081c49281520280d4055580c51460581d491412400082c508440f207c40d07120181165030b607107103c030082d081c8490a1802c001903204124124180d850340342c00c400100c84041c012a00b0400303040d0b107180760168000c084080e441c5104101100148000c07400c0b894140c50302a551710340034004200b90502c0010020f265208080001807513060100252050721150809980b10b41c540d4401c241d0f58075001e000e080180d2941c20046078000340918002d1642d54070328401d83d00a0580894170300e0606009038032040c0c0060400fa445568194000c100c1400382000106160642004900003080a405400014003a400006000051000802c0001c00c102402c0c41e00b800810380701c8000400c5510242d1300c000001d806509040c2000d4020b6261030f060750304c1e6940e200d520101c3c003000c12000c2c141c400101d030000300b03042181d00300e0b0351504002801020301400015980d078840750001020120a2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 374321825 1250 374320575 374320613
    0x9020a03021b07030b010b090f0339030d080403020f060f012606060f030703050106120204061401020a0b0703020405040e3a0c03030608011514180c03040309030203070b07 75
    0x20f03000303100181d1078012941c1545c0f222001c8544544002c4c0201da00714000c00b04d1541d0603c034100c0713083c0c04898a0540220b014020001c503c65000c02091a001c00003007501c180b66140c1c11012054040da4401e050581e482070092040790321038400705190600b45141a111780c11742c036403681d005108500f0454840d01c214020aa03040f207a80012400c100c0e11818081c142e103100d0701400700c0c1c0409507a000c1003051b0107960014002c08c19141e5507101d1400034880c1020032030149040030000240f05201e00107110038031030182c015003a500c42c9544c42064501c00100002c0a05a0038070012071203444501c9402e14850500005080c540c1c620654155203040020451240d0a42803025000e0145610b070f80003100340701400d1804610314a0f02e02540504a05d4000c40d02c25840c0121240000c065031243d001100d0106180c00c6003140d580c0b0a00c0304000b50700b0801104140b411010804896141c0001c3d6807240c06441e04498154495000904144295021011261000c1207010a0214113001001c0c10606 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 374323075 1250 374321825 374321833
    0x30c08070605042303161103060106020705040b0f030a030f050c1006140a2306210417190503060a0f080307050d02071a18100909050901060f1503020409020a03021b 72
    0x6a01260307952889602100c040e01e40307668608004100c20b42200047c80b01000301903501c4c96842e01d80c000d55640083c45140d10860410011584a0420b40c540044100300030380505044182500c0556480705142c600c0c40412030200504040b9a4003440141030341c0d5110a0082a442e1502100c1003901a01580c6107200c0c034519481045840c00621151100300b81007540c00221502080006040d0300480c40c906108209215000350300f2000d082e2414810ba1040c101b440c14010070000017441806406446013403020640c65918086019101642c6e0000f8000c0c1807600003034454804404400e45030b44011010b50002c0b501c1e1040000c03d1001c0c170f00c980c550344014803000d403402000f402c0c01c0420840c2000b441c940007424604012040021110004010b0041c000c1c02c50178001c0200662014412544c03881e10301404155445418000e0f00c04480310400400c034850b00f4405010014001d90b03804000303041c3e003040b000134410000d001401681d0415180180c4450f4420310b40403608441e80092061500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 374324325 1250 374323075 374323133
    0x200f07020108010e0630060f250207050f0d02330c0304050405060f04050712060902090f060a050c06010306150e061008090a0b010305010e2a0d030c0807060504 70
    0x110b400034040720300701003186d44401c00150074021b029501102910401c2d802490100541c140ba0102200e01800744100c041c000c507180305a102c0110f030703000000c034030041c0c020000800c0141740588180048007402880003040420640c00a9000c852040d180c09541c1003e00150203269525514440b20400f103801151801d0720100013a600c0e032040c0c0c01010720560351840802d03042c0d1607005a0b80a81036001c0c0081040307003020b280c050041410b1032487c091480c00c055002c00d0020803402660100c40d03020b030052110340010020000700d604010000d004001061040800168080284038029801840005608414a18940a8501b4541161000c905c041c0d0034000d854944800b502101005854900304c20303229288218104407260001038111141c0100110030b21806502c40c5402c640c80c02c0c110f44141e00c2403040c2a402c218480f6044861100944201c5620700f00f14121004075882450b142003142c0350340c0d4541c041600195403c0e078031107540e402000100f0203100e0350040f000d81801400e4080c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 374325575 1250 374324325 374324329
    0x110d09050106061812080d09061811041811011707050306100903050309041d0106031407060305060a0605070309210308010609050a0b07150e16050d02060a03200f07020108010e06 78
    0x160040b6401040d180b800503091f00880403940c002c40009900000500c07070312504541b60300b400b0800131405d5800040c048605070f02864039200b02503010702155111443c01d5265150032200a01c481184d5041c040402d154804c8090803200c410320070000e6403203181d10390500805120b200c0319444001020300c00301940c1400412000003d4404124044030042808100707001c0c0982496800c031071040d155800c00001104208411040b21003010303940b8110350165a42d5030080301070311010369086801141d501d5052140c40c2c880c9005280c2103000e4109800d8031a41d80b24500340d814100204d001c00c01c952054604105544240618010b102c0b91401300c8129007170000060483c4100e100f00c01440d400001c0c56070401542d9006c0c507207506201c49080101c0b1200307660340741e01e8010300d01c4030440000c901c49001c034191512500030001c498001d482d0600b44100d00106800405007001d150ba20080265000d02400307840f0070084c4903c1c02c0d450354558541d4241e200150400c8010303045a0b47d49540039080001903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 374326825 1250 374325575 374325599
    0x70c030b04140a0b0a05281d01111b01060f0b07021807020d0e15030403050306030f06190209010c0507030302010e0c0102190206160f120f0e0112110d090501060618 72
    0xf442c03140008080e250029007001e000c0124071000031041303c0015044924607645d204040718020020030300708230a4000a01c074201e45001082c00f129203018442021041001e500080c01d030140790000007102d6446140445107021994400004c15400182d0f5900b1030802c038000e1090034644021510b06803c0a40c400394a03410041900d404000d03200001c07405a130b480c0d1035840018110182e034596a41405c2c1401061940215990341c020312840c980480c510f00001403040c400e07580d8007526540c2107800c01400b00030794050f00c2c0b13203810052080b6036000417400612010f40114403030740000031296211140725081c1a8051340c880c1c155000348101544502102c107900112503412680c2070355540381110520405081c00070003822008030b0102c110100200c080d600401c02106450341043c0400c00c80088446041441100e80041e07901300c550482000c07da0452820f000000e09044d09003043c010042e02150300002d0160b800fa911900b0801c03881c3d0704203070240c0070a180300c040a60803d007030001e08080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 374328075 1250 374326825 374326831
    0x1e0e0411120a031e02100e0606011e1d04090b150f0315011509150c05060a020f070b0402030712030201020d0b090606070308070507020d061b030506030a0305030c070c030b04140a0b 79
    0x850140180131001d0920071b0200c2409428059020003042c1c44040342a5500c140407500180803c0329481c0b42103003000080d04181880d602c0340d5511046c55441003034203242010110714190070907110003c100010311b0241c2050310074201203103d003070202007c208102c550424980200d0003904100c03e030009032000d41d09998150b41e5100b0303000508410105044401030441d900c1030180c03411f440d448074030702c40d408840202c02601541c1210b0868484c101104100c1c0b00f03908006131000c008101500002d031444036441d43c0b1a000a00761088c10307030340b460045940100407008a0041c0d50006007980b428000e0302c94050480c00507103080c3c000c1c0ca80680412494420601c5c0a07003886000c90002d003d01e03101c0e008036014550f0103451b5240401c3c161138a00b01500304502158568500080840c1e6014440c3c401c0e00d1240500400400c1e081500d0b03203054800f0340c00500110070000041044c00080f0342021001030095101e6a041c210a16060a00102c1c6036190000d41146401140155000c11103504542c0e030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 374329325 1250 374328075 374328107
    0xa02090d0233070c14370b120f040201080609101e090b0f0a0b160204020415020f06070530041212020c06011e0e0411120a03 55
    0x8410000342d2103141003070314548000c1c001203101d80070404003072a0001403c405031140400d10166500c94801c4083c142c903072580c1681046030340817440070304107030a03100c680030042070740e17030f040450f00380c1c010f48509030150790008508450b0000300344801e0b031080c100c0c441d40300050106040e55424150300080036060040d2040d0310075601c3c44040303008150683c05100040882d01d41a55003181321220f80e5003005c0c005c1c818100c88900c0c0114103852424443d50a001a020003003143c039026080540c1680c45400c000a0b888008260310071140c01070701c80340300820240000120003c2d541c1700180d0001c0c54500036840c1d0101641080e0103115615404c84151402d5a6019441d070300d03061030140000b0500e01e6841e103801045541b62061006211152888415000c0603030f582c402000d000e40c4411050f4070401d55044110b80c4003000402100e92b20190601c0442e18408003001801d54505200c5c030b00f003c00b41c0742a20403903a015012401458110081d4103e450100d018003228503031502d018200d0281c0f00c076800303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 374330575 1250 374329325 374329339
    0x213150e040e0a03230a020a02012007030308090c0306011410050403030c061d03130312050c0601030b06060c0304080d02010b180711010b0409200603190c0c15020904050a02090d02 79
    0xb004442c2c05020303890107003910101e1500d0386c501032070081d0748140c020410303800318820364018a29080d085d46200f48c1000305c90028004030b4a1554110350400008145030464020210202c6030f903030701400303214000c00c03800800340c80e80b41990301040030700408001c202051000c2000301b000065040a60303c568513400460000d500b010303262400452628401c1c560350903000c000b032400c4101e071020b006007050700d0003190350b0715054603200d109039040c0c41080c4075403005034040001000042c413180c205540c000340241c0b59a040914400120b451600507402c4021180c01071450b00c100d00d0f0b030901c20401d240c901211412508100e00b441c1c01d1047c0f101902c180d013005060b40740810700c41401d40240701541405002007201507200d04280b1070032543e01661401c0741400d001d4030391007494201c050320300074001040141c000ca41520104130087c0704961480d0203211144401c8000304901a0400a030703c0400c480241c0d98404030780410048030001015a084540705103d050855200c0d005000c02003981a6441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 374331825 1250 374330575 374330597
    0x3090d11060c1c11031005030c0f1c021c0b0604050c07060b040605060c0706030501050d020f010c050a06020a21150519051203040501020f150f04060213150e040e0a03 73
    0xe5041c11880f0b4074003d280c1820030b95101e207190161001148500c81c12403000000755111810561123a000b89000d560060180a00d0461171900110007000d5420400c1403098542c00d59020400c44100809940652000b042c5840b081c002c000300050703841030040310100560310341159088041c2c00b4111010b801e040d0b4486111829844e5940303c2070140c4401040c440e00d588450303007120b80d00c034980c0c02039000080c00c00c000000c041c03c00c10010040b45030700500e84680c2042d28001124848800001951248600c0d10702d500420740503c0145802c000c07580e28a8800350780d003901064001d249405031040c940c58a40290b4a40c50081403030425a1750844400790032801081340028044e0081d0400c980c44180442408444000000100100d94080c1c094800e03581c40b8a0456407a0403030360000d4241076a4003000034038181030441c201940944103800060a244a42d400d04400034580c0d000f4101c00e1414122210040d07400840035543c1701d0048500b8440d03000684c103456181c801d610401028070099001c9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 374333075 1250 374331825 374331847
    0x905030a02060a053d260105010509040b040206070f030503040311190b060a030c1508100f051011060f01082505060f04080d12050a06140d020310060b03090d11060c 72
    0x1750346200040c405d40c030360081c1d1541c1c0d44030140d40030007205101c05052181c00d00740382001030080070304071540103001c10b50a40e22038460030082c24000300203d0740b01504001d19070000d0700340140c00e041c4600035503d0580b01d00e06468007415510005031545c540d5407050000c5412001401841482d42d0751210741403880e03417140740100c1da00003031070b40005100f010500c10210314002c2d501141c0d50070200c243d442030860340f03482c0a041031019190084018a88034031f001800942004c441111203200986001008100091032080c1003d00c1512084807484440c0010002031a04100089442041e00f4155059054151028086030f49900c2424001c0001149444014035050250b6000341102800d45a0800780c0b020010492861114010021480d100215500309110300c16102907504481039184d12002800c1002141d0002e50310403641803041c031a030104000e415000300402031524841e03850f141c4c01c24014090505042415000422441c160b908105460000d190794000140c1005c5965600301611 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 374334325 1250 374333075 374333161
    0xb0304030c03020708070902070501140c0a0e01090b030f04111009060309050a020a0f1e030312090212100c0e120c120a0501050f0105042307050f04090905030a02060a05 74
    0x210419140c0244040004c47d444150000c003009031050001300911010222204400c0e1801d4a00a42d0b000b828419810070074020421580512030504142c100d0703646e80c68145041e43c2c030843d101043c030000ba40c00d200c1000700d480d1020710080003c555103151076290032801801400e0500c0748008143c1c81d40094414043c003841081082c54002c3c240d40c5009031034456038140284140714003110005a6903008000100500c60a0190381d41070b82d51134004000a42030744c0281c105c0300720907680121319041001c10013100f000b04803401041c5034000305009140c071712301820180ca28190113010f0440d040c43c1407031880003c04c032000c004000300d5540c0c0f50301c00542100c40c07070a9003d1400401d950700e0201444101651701016904841c0c00320340900824010482d24054542011444c54400401802042005005030080d0642d948207030300717260910380c1d01d0401100352200782c0301c240e8031030b0000600c894400b40d040c04850740c8544150018400381c213002c41e80c045985da81005290b04652903100b02861150b07100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 374335575 1250 374334325 374334329
    0xe120c1b0f0d060b100e10020304030f200307060e040f02090310110705060f060f04020c0d050307030b180417070b0c070227010611280c03020904030c05060f010b0304030c030207 78
    0x141005d444100d0500b4064044001c070f14100d4070847c05002140300c41c520000840741900e42c88019800c4002c2246e80e100c101032104658164042c0030f401100c585070f141080468014603a640c0c6015180c6040004e12086592281000f1402d03401040781d6050b5450000d0582800c515004000654803900360300c0d04014020200000d103980111400c9c071504100e410741043c05208c0c1250900011006c0703508000c00c85c0300d601941d01c6250082503410a544e4000d4015540c001105d06000c900010080000b07080b0307102c042007503038030082e0000500040c1b03c801d090060071940c405811038502a040d0310344e18120007004181c908490700010f902000c42d1612943c003d0809000e00400c6040c100b415a10b140d40b800074090b180010719080d0420403400000204011080808640b0412900b0842421042234140c1d000695240c1ca45541c008016164a08903920460090755020211380b201c0c80c12504040019102100380c0e150200103100e01050711080702e0300990306062240340d81019107016400c102c038070303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 374336825 1250 374335575 374335579
    0x1107241803080d0c050c0a0b07090906060221130b09150d0b12031306050d0603050f06010810060e071803170d150303090501050307030e120c1b0f0d060b 67
    0xc0240041000080c10140400c0d115850f002c1c028800c040300c1c01c582c140030300301242d01e5503804130380208041811004290b402c60004c2c03520a060548540e048000e07a000340d0b0240005900030030941070b0a1545180082c0e020766146e401c58a840d050200500b2203000c140602c800d2403400044081c4143d8844140d1000c00001e0103120780c0f0f50f031031311491000503e5010000790182c074500c08402440500402143c468a824844400c10382d410181c04446907000200ca0b481c4442d40e40002001068040001401e0b18290384014901c80d814402e12500304032410307040301c41940c1440414090151a41000d81c0e020015103021800140300440803624100d01d03520141510394807002803080201d00800401144003409070911890701050f00000140f44544000340c00240303842c005000942c80745000b507401c15010316004c40d11a2030301c0d0641d41042c3c1030b4000b05901c154005000551070070284541000300d4803500f0500350007075902020a01e02c5075500c0c1c0c3c06200300c00c40e02144e801c0100a03400340c0055600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 374338075 1250 374336825 374336867
    0xa09030b0c160f02011209050712110301020403061b090b0d050c07150b04060b09130507121a011205060d11012f07050a2301110a12110724 61
    0xb00d420900c0410f012042c0c103a00103070846c60a407507021724a008007413400d0790110003441d81a18140c5e4009260070304100c1212071190380c00c4441000c2d41d00340068030281d4010381d030000301c1035400081c06003414811390150003485650403041004180f11016207982d10301620010601e0395075400e289100c0c2c402d0100081402c2c444102c0d040500d0400e500201040001750380400c11191150107024490048a080301d0388010502000c54000010350080c41c3c020b5400d040c5a10003400c8010b0b00400da072918a00c42059403440d80c6482c0044da801038000014685890f000c000c1d508140c00442ea21200700c51003c0d020b8840c48038908040e9224102d45412044042e1003666120011030858014039203100e65900948074456001c07805240c080c402c0c2044030840c600701000a00c1200300c00c1c5505420050160500040c2c440c0348c01407020a0003c0944540b04003100c20006c1c504450281c107110b840c103c807040350b920441c030500102e14070300021002480c030340c030301e948250b40c000c001140d5116110404850401c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 374339325 1250 374338075 374338117
    0x70803070f020d05070203030423091608060d02033d060f0e0c030a09050c0a0e0402100206011a030a0b1c1109040b0606070201030605100c170a09030b0c 67
    0x25100c000c501007a82154240d8907102143c1c4011203c45c010320902a42c1504200010802c41c101c00c20380000880b52500420b021403903110016405c0c801c202d810020392040c3c5008410865806007546138401000c80c0c948250000c0303500425604c2030685007000d12800144010716511524480b07540014180400404500d100200b884018103017a04c0307a8120610040e401040302120385220911414915900e94115500c248100000d491158416240750044510079009515442c1c3d5040140402010340606400c0c82c0c814802411b9030b0281200454019000600c1103c4440707139601c46520071546200e841fa140c89594200400b0b440f00d5a9511549100c0c00c0ba00460089000c07500b100d00601314401d001001e501030040c0402c08581c001e05030000603002600c03a1500030045c051071401850000396480d16500030403030040c420314120300400e00c100100c00801944401d402d000c1d04403a41c84500300301c903002020700f040310f490100514241c0c80d500001c4139000f5090503600e0210b07400101040d019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 374340575 1250 374339325 374339327
    0x16080307020a020f03010204032f04020a03050609090105070912030e0306090c030610050105030105040e150a06050310020906030c0a020f0a03030510061d09060a09111222031407080307 81
    0x200b9000c0303040703028142d900c109545614040c800d41d0200c0f070b04560010002800b250310500c40406003e11107029200609080c80b9139242d600c040d106050060710002a1420600304100500000506100c1268104010080510790250409040702c10b850a21401d6080c0c1d860700b92040700b0052141d6030180b1819041010040c030015048131036000030342c195450b684a0f900c090020a0301d9015040c00714000300010021401c00303034410007495240304141e401c400c402d42c00456441105980d1501410f0b141c0006010520b814840d583c40c03500c0c070440451400703140c48040380751400003c0c050702c02c031200802e0f0701104500170b104410080c0c0100064034800e204a10f0050010b240c1a140b95807000007154004c80c2c4076000700941c0420b00d1001030000340b0914484100400583c0040c0145d07003206000038000b0380a00381c0c0c0505896220507003560303070300c40c0d1150310150583c6034000c1610001e2001b45a041c1103010a22260b100440c0d010326068842e080404a2890b4901c900000200580300c0007040121003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 374341825 1250 374340575 374340583
    0x4020d0213170304060c1e061503060c02070518041109090d0e040605180406020f0a1128080d0618020903010b0609010f081008011b020d0912081608030702 68
    0x500c038400000745480980c110b030a41c0c1e078080e5009510114180196010105242c6417114080f4071319407018040402641d6144e4090b651100b0040c030780c40c50036407014002c01543c1d01541681c9001c6100608660f494800001c01003a9400d03005250083d00c0b40c045014418400103107001c448028007411910306040c18403c2c1d8070082203e92034002560545803000601e8503018840c01c8071002410082880d40560020a0b29040a042122110f608010f00081d1700401c1016000c00a041d031107000211501d446070604061100144030018a5480301c02525019500803110381c03160810403007900c0e00e08200f01c0c2801400340c2c0d00548400f4040709034400400d46150000c045400b4260001c0c80310020a1007480224011480201e011031404240100000d200d51151340d48600312902c005552980c3e1500942102c0d60740040d07002560640700c000b06102d80400440b00405414074200c8499440e02e804010000b13020a002081030100240d0304906c4440041e1075030052b07801031522075a034280150080e5807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 374343075 1250 374341825 374341829
    0x9041a060310030c150f0503070905030f0f06150303030c0703090929010306061d1903050f0f07062010050f01090c020f100506030a05070e150409020f060904020d0213 73
    0x3500301142e000b00d11141703100e001a01690b040d88034000500950342c3c00b6112500300601c140200603a5141c00281c40ea010055042041203c8000d001c22030300c99040582440801801c04034039a41d8014031085030b8400104032984580c021407525180c511910b41200c45004551018440900b8114a5501541d1284540c400c05c0c01000e001180c65009400650907110701c5e10540700410100c0c000c2e505030b801407600301511050700800e8281d03112500e425602440d401c07900265400d600050341c1301d0382090b00304541c1681c507a07010010420b00d407a02d0001410b10081503202d5200c480016041080480b0400c100f10303050b440048240320514200c801d21480070000d11600380751904101d84002e0302400455403864440203000640142c0da00c200c0c2000151001a00047d0144198a004400724034107010150103003000400364042414003181c00807928942c11015032046161000603070059403069040599a03806940d51611051800000750090262038400c041ea10300000701c45851480103501041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 374344325 1250 374343075 374343083
    0xc030d2007061815080a1d1e150f0613020405041805061303050301050405060105041205060403080601050f070b150d0b04020307170a1e061b0f1409041a06031003 71
    0x4140c555035180a9420200440300341c0204032000045002200180c01c003a009014841030f510060340741c001322902d0300c02110300888d0282c003600d660305982401400921018214000c0601040c02e01c0c1c1501c4850000c0a0207180c8920544110781402e05807070380548005001c0100304000742c880410000040d4480f900c0216074134090702d400110809456400f29074a1900340e5902421030307003013030107120003000c002d000103041c080103210000701400325150700c5c2c40d07035882500505403a043c94030b070241007042c0c0035084905204040c4440c00c42c00822005036805260408004000b41c0c540b049103c1301050080c01803a0800a1034010754284400108540d000d24400c1d030807180349079034802c04d40550241c0170b0580000c40c0c0089041c500402ca9011148048141c4c1e88988002001303580e0310b88046914007080c0041c81c00391040c519400e1500851580004549810700b0b40c007503c1840c0c0301180901c1a00e603d24804da54544150740508100c400c00c4500400c060400d540d81c1c1014289004403c04a1004807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 374345575 1250 374344325 374344367
    0x414040b04150c0509060915031018020304200406081e0601050d0c031506120c0501030b0906030d11030705240901020702100e0f03010f0209030f0c030d200706 70
    0x1e0401e07049100b2680c14442a13940c55040c40c92860400689500c980b9800d50300c081000c2020030b0342c0500c00700850240703041840125050b03203005404828030320303400c00f601c00c914814010071010690070300e211444251000c02e0158024029000240100516041030762140700f84000109946950381415800c804554102c0e40b0350ba907200c0401c072594100000c0100b407074503000020000a146010300341c1c02d10200b0140804c81c81e03111400c202c20740300e012006980d1581071100c104801d50f014821039000715001d03102c180a929100d001300c3da4454a087c060410000300c4c00c5440501c44003401601c48056000007074078034091098440510036001d40201c8000c0300c00f10f80100700c19250520844403080c2e40600456001250346100381c40d00d5800800054101d80d5102d5040d4065a0a10400780700c04e00300000107807075400c4601894501603903000e00c18160f074000000800c00b5507001603a143d41c0b580b140341540c090050b5540303420202c441042094081e100c1e444001c01e445801072500484030340452003030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 374346825 1250 374345575 374345603
    0x2c011e0509010308070f03141c06060305060f0603070905090907060f02030403051c030f2a110c0f010c020a090c140a05120403090b04230a0303120203060414040b04 72
    0x45000a10008110400070071178840041d1000d2903030b24106001e8240800d0090000a081010307600c06000c2c2e060004004240c500401c420703201c2c1002800c404c2c0b900304054134080010a40b410700410250b44943e0340800001c4130030340300304043d00140502410010460030007480300c0b0341c0c0b81210f00072000820070300000300c24814400410b0741e0840750000020050448100c002801c414134910940781015213031a410200c054050081541d421715126001e141d6540b04010080c4003e9840c0c842c0c4100310382101030006000c00020321144d4020b04440c802540302804005035160358030b0030300007500070f101d01c00001400080c5d1750003114a0084c548036240c170b9200800040c0040d1040c0d420b080013041e804d100c203000c40101d200c200f0380d20030710034245442182d48400a06146400135400742d407944440b0040b000380e035500c02c02c41da0f000d000252141100c05085035005407050720641030f005881c550120005907941d80e1504000c401c0c7d9403426030038640d81414144007007030b20383c01c40b020380b1419000024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 374348075 1250 374346825 374346829
    0xb090106020606130e1603051c0207050a0b0d02071e03080615040e060d051605030c061201030b10091118010801030c1217030a050105011209020108012c011e05 70
    0x1068403e00005144140c5400d034202454020000d240001843e0310a03425682d11071084055040042c6000784004c051010000e0f007a403012026691840c800c6411200c010031540c1c41c1d500078031040e140340030412074076281215170b20b10090041000260483c81c0450b0241d11041d0307800c2c010381480303001f503507401220343e940801d000e14001200d081d1030384c1040810003003140065580da9190005001448007850320380e030380c0f145860881525030505148103261420051850100001e800c0400213942035030403c880300092218a0005100c041c0030320f600b0300000340c24040c082c02654041c0090b09000c000c0700c410b0b00312130b04894001ca020700741016400740102040e03600801a00c0d0403243c1c4520308003880e90922240200b00a03003a007044800c9040c400c508007204607101c001e18410010342d1400505e5624240c001041e12080024080d6600e20700440c0320054bd13804201c083c151140c01c0c0b900703101400010341a5401d442155007185600a9884c000f2070111403c143c80e038155002080d0b0090419110300c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 374349325 1250 374348075 374348083
    0x303080a0507050904090303091410150503122d040918050618030c100c02070e090d0c170307020703030908070e0114010e10090e0109020c0a1b080d030b09010602 71
    0x550b540422000d002845407882d00c0c0e00101d14081c424a808603c04210396503e8400c1781caa81d03080c01c80c58010303455551100100b4860880c1c40002c03c83d500e54800d18280100e6281d40031210f541090f5000042d642d01c1200005041c200c0a0a0191002c2d01e194044045551540c00501904011a080500d0100c800d08420100310714550000040c1103a0385500c00d0070010000e0340b0039031001031b0006200003140660248034860b82030000e510003085013950080000c0c00c041c1a90044d080c04c00c070440502190403800184c0c8104c10030f10341080458030000b403e14854060010b40086000e00001007080310f0b4550100f4868100d034400d8440c0c03800152184141515039000740642c001c00c0070014010003400040c980b00b004084818105114442c8200b004603030281710071188000400d0200b64200000c08030103c9090040c121880114200008041e0860711108001c2000d80401e850b502c1d00004105d030442e00000500510342221000ba421030800b0f40542104100d25208a4550000041d0180040303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 374350575 1250 374349325 374349331
    0xa180c08101b050a0e01140c07050f0301290607080307050d0b04020a050d020f090910150e0114030603100204060f090e040201170c0c01060b030402041b020613050c06070c0303080a05 80
    0x1480f0103042104d010400c0f60203894a0960b54108540b9402c00e500302d01429005101c40b80d00340d805061024181000c0c0306a400b00014014040e0f03144c004c20782c1642207034201c001d050701840801c80130004010320002e0414090598050041040002440082904103005040505441c80700384035030724580040000300d0103580c0300400402c00c00c202080c194030642d0300400001d02800d80b402d0904016802103071502d102141c1500f61200000c00901141640356120140c04105140c0500708a09080003b0402550405840200e28000c404207502c1e5905000c0c18240401b10b1008644482d510f1300010710f1005060200c502086a030100803411401410381180f04a8040e15020340b204491012903096520060400082150920031a48402028000e02006140100b4025141d0800740100011514a2102040c511784084402c50080c4d801103207503680080140007020001c69542000c60603c49114041030380010001611000c016850301e40f60180c81c0242d07903405441e5604100340003100d03000d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 374351825 1250 374350575 374350577
    0x10e0108010b0a05160305030702070e1012051005040b061018051c080403051b09040201120b030c1903032303060d240f0e150a180c08101b 61
    0x5000500154010b50003d104007240380ca0000c2c984001c1d081a0544040311200440c0061800021f04c1982750341004400047d20480c0c1600b11030f41880403842d91203010750700c90110a0356802d2140c80c141710061201d9158010b0704a0203002c00e203480d241c0316498840031148544a1014200ea00a1540c800d10080030745129844200d40424209030402c03048107184511a0303000b406811071440007034043e8024100951040c0f0003000fa82e0b589810505400c107481800b50b0049085504010241c0c2e405071103c08c4022b09014002481000013003c24200f8084e42c00c41d58000e540c0400316807412000e4104401168040e9850050402c0724003e41c15840204140c01c0d0340c58141480442c600d1700d405e019003940684101100e0020921840190700e2940862800030003043d681c81581600e880c203401080c40d010000b03400740000c8502c02c50041d0046034058080d01c042d50746c0b8141610460807411541402c40d40001d042008a03a4922280d56980844810071030911b04001034001c3c05440c4090b004075a41c85 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 374353075 1250 374351825 374351837
    0x20c01271d01050a12020f010e010e15030a1512031407120c05100c0c06091109040b07090617010504150e0703022106010504120f020619030b010e01 65
    0x46242010100e4140c45010354600940800980ca60015500035500880c07807100562640c90202080400b6409900c1407250700100003010006a136454440e048561090910014848440004031341110144600d030360084002070394107003080203d401441c0704d410300400a01036203146900700c1142c201c592080701da40c40e0018442000090040001220b200c0e0780340318942c10324115031150131504c00441112404141d4034031034401409000d04c0382514004002e00d00b0302842c400c0107001070070500355000261403d52307150899010040380c1000d0024017078000f801d00c40282428241410520344c2a5204070204030320800c0090024010035540c4844c2032402002c0b1f40036032030320741440702810300901c403107180444031540410007500d42c2030b41c40d024800c2582c0060700c4800941c91501c8c1001450340361607848032a102089026039000c001c85050303e0b24101800e900c1c000d1031500d40755841030300724001d500180128201481c400b0b15000c030f0a5420305640d0a014041001c401580c0143c0f0008040380080c503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 374354325 1250 374353075 374353097
    0x60403080411100e091f1802070501050405070e100806040201050c0309030604051c05090603041b15051e190809070810050708070f270b13080d020c01 66
    0x201404040e41e006000c0c00404201d0b42e140300024064980d40c202d0b0a02003504010a80e66504090090560040180c968220039a81c00050302c440480180b0a0740d112a91082d13140e0611442d1360152828541e2000003441142058581142c031020240241507012501c84d0010310400d10030134481003260702c0c51020300141e89443c0c00444a035440204000c88031300c010014200b060710304021080c41035015901a02c01001c11030440301c030341080c16821a003041801e019030a580e40c3c0c1d10040381e4005500243c010300e4440400aa001c05002c82c1c0e00c80300b0032060481c014014160080028465051428240b104a8102c8103203071140d0b006003c800c20318a40340001d5004003a00901a964100850b0811201d421750ba501c1c00ea41f0340702c0041003600c2265101d00c01d00c84102d4000c0d0200f60089880c0c14042075070100d404004066020341310006c040c4a072600484c000010305514050090200003480e02c1e5901c00d00b417a1700d82040704510071603e0070f1207455004261b503480441c055410f510f05030b5030a41594 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 374355575 1250 374354325 374354327
    0x4060f08060406031b060809030a081909150204150305010815220303090c060206010e0a090819051e09212b090503071503050709050a060201060e1008060403 69
    0x80c02059560010360760754000c00030420781e1030352002e0068002c1c0309007005800e00c44c005100c107401030420102c0703600905c090022160408002584131107000f04100d0803617408a80d00028200c4c8460181c042010005246841806a00204296142c2100c8980e420801e110101c0807a0b00901c1101c030311b50000d5011903259540c3e0000e0765007107000c6440b400c41c0895009403d000c030310000a0111f011035610070150041006500d4060000d103840d0010704040d601d401001d50389420014104a107880d9141c50090400c4403480070340b00c400c0001c88004900200c04540034080d81d0200304a0907000030600c00d160807800318202201c048090250903c0130056040b00c0d010304c00e5400c0a01101140940e01105038401c48206c2e090703001c1040b948020682d5546030714050320400c000d070001802a0448081030040b1540018007880d104003504d800a07003641c0d41c81080340c500341c880c0c2205501c0314961000150b05a41500300c034042d1442c0300002c8074130b0f8035401440241e95441e8880d10203140c2200001501003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 374356825 1250 374355575 374355587
    0x100e07090e060d0606120c0e0603030a0c08070f0b190605030c040c0504090515100f0e0d030309020a060206070f0203040f1a04090203090d0e01020c03060a0b0f0d050309030105090304060f 82
    0x102c4405000103044880d50703521041a41d0250304412480291090b524041c0142200460001d02400074000c070f036810800d010903103034071980c0246014461441464010481070f03008580e201e83d0454240c03d030143e180c4ca407020400e00265a0a412280d41031140c14001c10b01d481800f04503030004000703000c000010b030244400b81c21030140a0701481320034000022040107a00a1510a041030041d030032244120344204000c00c240b008003d410880c11606c943e011a0f00114040c2d80700c81c00721010180810f19290460291000d45002900642041d10003d0119000030b0610b010300820b850b80a10444000000c076a01e018a108040e000d60303c0d240204124482d40c3c60900454402001a81c50b058403240080c040e6402501c8400c2c09a111814103003140780d004141922551003440a0b055841c03c03000000d030b88243c05401703130980959805242c080c03176403040c0b01e180b0500000781000403201451304125480c4e400c21031805000b5400c1100003601d802c008401c032030030360300192524010404000811101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 374358075 1250 374356825 374356831
    0xc040e19031b061505150a05030c070204021b01150611030d202b0b010c02121e010203040501150501140c070b0c0303060a0902040f0509040f020414100e07090e 70
    0x102d403142070000c00109129001e0524001280940b00c4500e030310300300a100b40ba0000400300d0618000c03e200301a08164068100c942010300303c00c1c1e0341c2c5c440c0340d80d00020b402441014a000c900c1040080d903200154019001828008002c0c415454071030b035112019500e000409685096a07042004500c40d841401d0340581081320f16140d132044003284001d41e5400c00e601c150300050040518036200c040c030b181e0b035145d540c0500768000c5042c4101c408400000e80940e41981c4024030851080808407100c600410a100110010341a20344615074551004c078000d51041c3c1c0c0030b581a5003450300b01c0c0d4801c080c0c1d402d40402c498040e901e02081410000c0140203030703008910103c0d0310b80034000c0d00080380030b07124001e000300080d401e0241d5034030301381002040b040006e5984000c16280c014041048011704010f00401241c7c0240c800404540d19860221a4414402d1009500514084802400403c2d010a15120b002c419031303070212031911455a60082d0700e040303403588001044031605012441001e01c140760 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 374359325 1250 374358075 374358107
    0x5030c01140702090c07062316020c0a0621020702010f0c050106030206070308150901141003140a060303111504020d031209151514010c0312020c0c040e1903 69
    0x414142e16034000b070a4414280c0f025102010f01103907460504c50148240c0e600143d145201e050365940310701c0f0019400000801c9803000700e01411600380b4040c024010b1002031040200851502a12050060400402c2c0c80b100c40040c015041d0000421009100729003d4a8058690018402d2600c40881e808040501e04488554a6900c0000140c035600301900d803061294840012901e01207140010300c02403508030920840d40000100700c3c4083c071942070b4500c035a00303881c1100c200d142c066054026210b40714598108008000810283c400142d1190050b01e12a64611040ca1920303c84995074402504c91011206119030120740107103050f1034a01e00003032082c1018420620135040078030440e000c0203401c0d15500d060000b03003400a030452084140c282c1c0954181002e2900700702000100c01d13410300100d07060010100d10714044c503004558030044602c0d5084d06560b0384103080d900a84418803c20001c1c0198200b01400104240110301e114061010480c00b01091010340c17011203a10500d04200700f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374360575 1250 374359325 374359327
    0x80a02060f21040602030402040e01090c0504200d0207050f0a080d0207060e03160303050115050304060f06050307090903030612020f040b010e1002060f0105030a0305041802040b120601120605030c0114 88
    0x82c040650501c229403040e8010300e00107849107000d006110541d9a01686404582d15014010001454120301601558025600087c0f22000014808a403c40f800b081840c003003000b04220b00d05012a800800d031980c0309606031180c10450b1a25a40e4800b0b0550700100300413400d02402051030307035a601030180c00d800781d00c0c08648000101c2c0f2803811584040d07241e1500c1000d05000c1010b050705801903500528060180f401c4e41525200e0003801d81c0006800108a1b40c0c8402c204000d126894000e0320242000805844020350b80e5548980201a1003600328040780c1000f000186005c80c0701e044980040d00581004660206442003200600c40900c0960500c095008400c40700d031035140000d680c0b2034082e001040181464083d0290315030f0140d003d43e2203a400207000400003036008007500c0c1103036600c0f40103e013514680300080c0c0c041d02842e041151a50400314281d5019482148010b008200a0f2a041c184400d448820b000f6503585010302905a4070246940002d948109203940c0501c408020307413 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374361825 1250 374360575 374360617
    0xa1112060f0714070204060905040b01081920030d0804050d050306010e04090f060e0703020102250501200102030709150212090d030908010c031407030204050906010e0301140106050c07080a02060f 86
    0x7401c80e035041c8c0001012035500c408000420050f00c10190142450400420040c079245410300010740c0802c03030003131108a220700100b03800700f01d42c002d80807040e000505a030400013105400610a000444064500c0c1c407406002c0c004450050084034015081a5104480002c3e218103002c041c0c0400762040781d066920103403141c0454400d00c41c1050942180e4041c10b0801d103180002880e000202d54060580c12030385c4084500c552000c4014001c441d002c0c24802e45640500006903150300c404080410694000010004182e61044041094030f56014641c040d0000100d412a514a000e20341d01c01040010030111445281004108603058464a01241032586910b43e03d801d440313841d00701c040440c0e16500305206860550004c2e6600c1441342c0b030210b040924003000541260030103400c6034144510001040301503142900041c4042e01d80d036004859550b50b946005105511542101417107001d140e102150121002c40d84840854000b0912402c00450383c8014071140e0124103110140e00003c848 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374363075 1250 374361825 374361829
    0x4090e0c040504060b01030c0201153f020a06110a081e0d0504020906010c050d0e0105070605100810113103030c0611030403021c050c0a1112060f07140702 68
    0x1494800c510407800450305c584544009415104000000c10559040c1059000401045020b03941150311202285e01540c400d040c00d40d4034960f801590022a65901c0009064408a0f0781400705040c4243c40c15850640d40710011900700c2240d660242107a04181102408035001c50040e00b2200b800803503005042206e0a10303c02998045599101c2840d1220100025850b100240c5039210f0301c00e0828403154821a40c40944812048441009200c11444244c2d5035900c101c0540300a240d1001040085040012200c6a03080700c920554039248a5241c82c1d01031329a141c0500c0da00b403035000046030b040481110b0343ea10210f0802d4100390040c5000341da4804c08140d40b0060788000d60080d00e41807080a040d051440950342d03000310310281d0a004000380310000390f0008009401d0800c00004a40e8920000d0048800348940e030400f101030b00c6081806018065003492142c2d045000711802c0022a151802d503c1d03c401040340e40d920a178072050b000945440c0141a010a181852f440c0d0529240c03442d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374364325 1250 374363075 374363081
    0x1115040305070807080a0309062601090b0a06050c070e0613021902010b030304060509010f0306090507020c040e01061d0709030c24030504121206030510090c0f03050304090e0c04 78
    0x300507151036104590030050100c0074010b00d0041e2800201070021800c841e28042c0903107e0314421103003000840d404a1840700c0074001124a01e00e14400f0051080d41c2d140001006803c1901107184101130b44c1800260b098040c0e400c403098070f102040038005c00f0345007082d4064480c10080072180c01031a41c4643e102c44007140c1c0700030414030030f00c00321001e260031002d00000d0846081c41150340c06903108000074042e5940000658a440c0c0c02482c20204003010850220040d10b0b0b2548584212400c040030b00061940200d0f007400a0902620104807403404010441e003aa0817501c03603007004007600d101c1110a82d42d1491030a074408080e09200304c00703554032740e50006003800c00e500c4030800409c2c01c0b01c08180c0024514448011654602d018005401c01791184000c102100c10010b0070300984524062208086030040002150400140c40001424400a01c0a03060318a4125081066200086020402010460207aa070468021420503003030507500802040c1d401a010010320a1048241c210b540c4d0340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374365575 1250 374364325 374364329
    0x50c030a02010e0708070b04150e1201050601020c09040c0b0313050601032306070905060c071208031b18010f030e0115060807030e0a23070b032a07111504 68
    0x1e0300000c0c42411104905040030070503000081603070402281000100390800681e01aa02e42001400c00344c00c00070070540b03900e80d60340046034001016015845c090340065101510820007030f02502c1c20300c2030b03003000c001b0036500c101c90003006004a000f0900410700f50001442d8001810f00329503022502030784900307140c0072099004031078400c2c040c0100c40081d03814869100484150130000d24550404510203881c40000d80501402a803020940c0c2000303100c00c00c00b240c0102021311701032280607590f0500e030f140c2e640111100f00034403196042480741c8002402c21138084018a60040b5207520148004440b004141510700d802c060312003800350404002845604070303c050240447c45480e1802d10080c100c0c0f400180300d501071514140f0504032044002c44e80b039004c0d43d4080004e0380d1fa4054448010119032901e0400b691920a070310300404d41c0040c4100031401000304164107c201c07842005009640e42213000340020070a01840180001010603024100c8000014401c0c0c5006507070620010568000b9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374366825 1250 374365575 374365577
    0xa09030903061503020616060b0d1e030203040504020f0d06080f030708070201120e100e0105011d04050312071809050408040303050c150a0f15140d0804050901061d0a180b01050c030a 80
    0x38241440c08c0080500c1006001ca4042c0c4113042002696292100c50310f0003007940180c0351051040c0041054828001c4901034000188110344810003000e4488d0f080d00403201c40d0102e1490210302054004000403030310560030814008524101d8030783e0780c0310103070f40001c0000c034140428040c402025100e107014020300780038074000074000d07102504881415141c0c1d65111800d564541001400101d51030301c0c0700d40700800681046031036070301c4a161040c40c5206d0f5000d800444801c0c031092000b52a0f2207c44400000004c45a034009140c0b516560301c11128240c5004001540400c420400240280e015001c80710044007510541d1201d592507165074401101c1c0c0b5035880d6520600c844000b8414414181401c011000000e102800e2414281c4030401220325030b4405e42d40101040104040481118040c1c64042d1180f8055655004090048031500c450b2038070201041d00541e885080002032001107940d4400d04c6686280c403100080002e20a100c030f2241001810411040345e6442000248006c20781 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374368075 1250 374366825 374366857
    0x81602061204050607030e0c040b01170a14090123041113150b18040203041e0516090b03070504021308030f04030209010f0b03310501060e0a090309030615030206 71
    0x14942513007800c0005000000f03042c500b03501200b07190000500d0104410060364001009801240141c0c0c5156034140c4101d101c00300d07041006481c1030290054000c1ea0706010083c0c406440740c5044500f65041200344411038180b4100780b8048900d6600d905400c140a0f0341c0202e550420b580110300740001c088044007501da21840c410301048892601c010040c560810411b0030f1446c1e943e618a0110200c82e0030070721480d008408a004d01c89903599080000c54012051200142d1f13611386262a907000182840707110a0307003030740040e0f0141c01c0c0c0100501d10300c00a01401030541041c0410000390410103601e081e1304090107003c501d0b404108000c108601c1d510004d991aa0725502c1001034010301600010701c18500544100029042001a6a04a110b0703100220f19007034202c10f4203014174400003100c2c01000f601000c540a010040d0300450a41707030100900403291340c80c080010142c440301800103001690182017040843c0c450b81c0050008800c111881810990701e03000281503803c4004071311041c01d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374369325 1250 374368075 374368081
    0x20108061f27030b010b0904020c06090a021c03080609100801021209070602030705070306021c060b0702010305070e03070e09190312050a0911272d060a030816020612 73
    0xa640b180040740318000a031400045425a9134000d41000c06100b1035201400c0804c5425260f513a40d0162003035101e190084400910380391051503078030030590754142c5c00340c4480c0164511030301426030545c2c0c540d41c0648602c00152030302c105001844c1e01c0100340710840c42500f040820452028001020744e074449410200b0a402c0c420302003814080c6942c041c4040d5070041202000045022590382c040f03e07003004005071100074001620001240041c0c0d202516482d0046c040366504050700580440b038001c1e42c080041c0e07903076140240c0b40c0510500200b54984c0c0000c42c10010b140c05460070356030004040382500c02d00b591141c84d4440c0804903990440100d4008a100c42c602410362140c1d590181d55100240902d88031030312100d040201d0801c0050142c0240b1050140042100550725040e5205002d80b50351854008100e184807200401410555a24003080c042c00c107070446042401440000c1052000f14a075a82e0340348103901c4651584003172550304012901581d100310191030034507104941c12820380703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374370575 1250 374369325 374369357
    0x30f0c090105030d02210405041509050f101a0712170702010605150a03021201170c3016030302071403030705100b0d021504030303060501110307020108061f 69
    0xd4160449030181d0301003150500d186034002100c1105070300300d00000d00245100d082c1d9032864451904844d4004d418070300c3e2030705d480303240a8074102140c080b02420095a180c82200d070074581d00580e8030342c807044000e05040c440c0511254003142010092045107180540585e03450a00101c00640c143c0410100031042c4200421019101c0d40403c0c5031000b00322407410440001c1c100d8403400310b038421440000c941910811300943c12a240460f001828000560b03486900040141c610001d4056502803459104403500780078031210a4145011884a050280e01c48080d280c0705c850b101004d05441340440b120202004505607002540c0070354060f0442c4c604041c03090860501c0e801410307000794000c00450000c280041800c400c070014201002c2140620140001d540310120b00019500c00720005401000d141100010800c807442510107116031603649005540762043c449410031039410800c40400117601c00e01c032503584143d004022aa4490f201540000d031000c0440815000c1211240e41d0502c078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374371825 1250 374370575 374370589
    0x1f09110901182d080f0f0c011701290705030c070f08030909040606090f0b0f0303071a041a0403030c0e1906081012050303100905041e0201020c030f0c 66
    0x2004080186603442c9001200d110711080c10a40840f20010740400e101c840c129094110010989035013251500043c0c003603000e403540000349440c00c551260b945014078550044404d441c03401d81941d01061b0036880c1458412901e00c004c11489664171100346001078504c0d260f0007400002e4002c000950310390051006041c60104235410043d0b400c811114100101d02c40002103d1406505684c0c0500a8640d8500b20010740180c0c1c002d9101c05003030030020540c7d1207250f0b010558030309045540c0308141140c501859228400c006c1b0140000600b0800c5010380c84030281115003040c80b908040e00d0039005c46a0b02c19800c5002c1d50704500194460039400290755004007003820310242240d034050170340700d0740c0380c4041c080181c4d204142c10310608034005500c0744e801940e10002080c10f000782207141a40d52a100d1f0f141d51044440e00d1000c00d0340304021a10802c00d120b003e214642c0590b5150081c3c007000e4103c002e091843d4001c03030444c400c4035196240c41e01c00340000d011002c030080041c0510004402000702c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374373075 1250 374371825 374371847
    0x1270612110a200a02300708030904050c0307080714070501090b190c080703200a0302040602070e130305071e050f010b010e06070605100321080c121f09110901 70
    0x202d0750280d190000582d031044440b8401d00f007200403401c3c0f44d4035a180c4800d0070045500201251f03020715180082d04140100061050351800c44042000342e81d18150460f181c0420780300d0f5400581d4034000140b085004943c6031100b80c280c1c140803401d01d9039595500e402d40e440c1d0581150380700307680c030144880d5000411002c40e2158400c3d80520080c44c0100b402810141e00030500010561582441070611030248400707003084c0c0300d129440342d54403050580038001e50300c144107080052142000000d8050440d0103014054050202040c1e54203950751070803186030700081402e0358400004c00c0c4408a41c081400060303103091140d4040d000344400c0000590840e01c03d40200760502950981110207550340304101c61000b0f5000c080014162100d5001803081401c941001705079488440002c001a0000404840b9500e1180c0c1c40f08403680d640421100306025000d1038a040310345003404a1022a9038a203800d00c045561307401c0440081d5696000010f681d00250030050300d000000b2801c0507943d028600e085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374374325 1250 374373075 374373137
    0x6030f0c02060601120b0901090506180106020c010f031410060e0d0206070f030504150306030b010506071505060102010b0409110a090605030604060906140f0601270612110a 76
    0x4180061030103901c1c0c090003008941000034171741090b030308a4003a40c401c0c505d82802034510a041d40e19403414400030501503650500c10248100b007000508544084641a5915a800341006403484401901c2078000c86400009068840f12003040920710200803a218681c064440b0500a241840140078181c81c4141d0302c0c021046400d2190140c1c803203804072081300381d000300300305003a15850600311004c0c001c076004030030010711200d00c00b6501c0f5130680028081d030307000301044540c80c3d9981c020040b01c0e1240950042164417416900000010280d0003550f012906000100b1020a51400101120280442100c01c290082000e00150500c19a0b04002c1c013034011b41000300c982000c3c00255207401c000c10042c181c42e150007100d0208651174100b451a07007040303042c91659081040010941d01c2c0200d80450000300f0b0000c050060500c07201621424444a00f00d1030006c3e81040e804480c00340700c0e400d000d10b0796a11035904400c88504c1030001c022050030345c1c0d12000c152a100780d00034001c1e001039494507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374375575 1250 374374325 374374331
    0x109061b1d060703141228140703050a061e09050c030402010519050d0207060518010b01050928030b0f181002030a0e2a09040506070503090307080a02030406030f 71
    0x107075581c444608403000c058060600c3d40c088810b20004209502c514940c1c109000d0008007842104012041011940741045403003c2e00b51031411240803c4442d0090540807190582c004103a8581c001d6010a421101004021991603241c0c912140e488002c01400545519480c07020024200c2500ca159040a443c180f070303a286042c142c0008100b07008030310f0b03081d84070182009410f14241c0620304480349004a000e00355180c0500d401c00e02e00401007100d03020b4a5400501030604410418465050308583c16103405041803501da01f40803108451a007040120b43d0381c60140781d92690412039220085124002c200b4152410b044840d0094201a10076640071a00065074041c041c0041041c02c08541e40c40001030303d90b6601a0b00300c0251180c1c100902650203007966503180c50b10103800340d000b4405070b10300e00d848000c2d001c030900c1440c0404031805041a0013503c0481d00c007600c20b40c000d5070040401412207003010348548072901180e01244020340964070000c0c0411050b60140200d141c03c00c98042c0030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374376825 1250 374375575 374375627
    0x20f10090f081b010908090a0819110f040219030b030304080d0f0e060703080a0506060708040e0403031508150c04080309040b1c050c040f09170702030109061b 70
    0x200903078440307090020a0b800700400c6500d1201c451516681c40c2104820081c07041c55006e09110b0300d5680031681a50103a2038406010440140000380a43c00c4100041e640514003100e49074590103030039250a5941c032000c0c0e4140708500d5516800503003e6560740c410501e11164107140042c0407581c0340c501980c003940081c0720030001d51502240804180b149400e0107045040c405c0002c4403800d6098520a40c004c1020a80d2000d050344052140c0c85000c01041c10803e0b070721410308000396401812030080c5034810401080c0f203e040c0400815800c107200b0704000c01d4500300d80c074000070030380070b141c001302040ea1216000200003111409220b4010420640030342c030305030a04810310b49a105411159002d140c071191041d04a4455600103918100340707000390503c0c0000c52412079142c0e0040c0c008039100300d0603c02d02d041c412600b031003a04115540300c05051001015484024002d8110070000d03a0315540c0c0391a24004100f10340501c5088250800c0d110b80502c6d41d414010b0b15030222001d0251021101b0504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374378075 1250 374376825 374376833
    0x4061502100c0c0b070c06050a020c0a08090312040b0d050c0a121505090a020a12022503090e0f0603010507081b0c010f0204080a02012a0803091606020f1009 69
    0x101c441640203000303002c5450144400291940c0703070002d0005088003009010803212580c020b080c4800244102414429074961a07208401c2c0d0180c103541080640000070400c00040d1500c0040400680c00303400d50f41d035a41d8440c0b021800360070660044040c6000022034010300e40280c802c150303001c41102c0500381080718000000704550040c58144500c282c1c2c5000c45600c2c00381030103418008050003080d1540c2e5141c90801e84010b50054107400d4003180d00d0020300d0f9040710b9a1300030f4076084c5c1c03120142241885210450644510f400c00015014803028140102d2090205606c0301d2052442c002d01d02d00900b000003d2600b143c0005007214100810071007840026030342080d80d0101c114042d084a034580d00c07800701160042815245045540c0d2000400041203031001c540071903a00e0003600d80c1100c50840050620401015001c10020545200003003030015503140f014503005081241102c220f0051540c24064029094101d0009a8000e84d807070341c00e013030042110391b03a040c54074002481041c5099071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374379325 1250 374378075 374378083
    0xc110a1203110d080a09021c061a013e1603120e09190e1005010503070b03090607050d09020325090b0603060907030b0a1203020d08150f040e010c090504061502 70
    0x104e558145d64450180340c0940d030302c04014420352900301241c40020041458440010400392a00c031200d80c104075813400242d17001d40e019003018016100e40c0e90400c0b5101c20441e0108100c1d81c5c2c2000100c1089444185500e4100490038003184240d170008261030450030520726410903154500d00300709080300341142507180d52049a800c4401c0380e029102e8034040001400c00f8140e400c0500f44035109510b004403d440e019000103040381d4042e0180c4642070b85601c40f00a084c4403c071004013195200601103115284a000149403003101e1010000f8965141d40c00039040000d44500080c2c0c0300c2c0c8440349004000300120343e860082030090420858480000d002c41c074580401000288a0a0780e00002084140030340c00c440d14100d402410b203030b1003585500600e80400240c41e4141c0c0148540f0505466030b80c061034100d4050000a403800d83d000175800c0402c44420700d060860723038101d40ca4000002584e01d003401303080001c001c01d4030354101c1d060a2078180011200e0aa00c0820402c1d40c0c100c8400c1d241c5d4002c0b07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374380575 1250 374379325 374379331
    0x70b030903120615070f060e0c060a210c0f020d050c0a0b06060d06030302031908042103090c0b070302190c060c240b090f04120c110a1203110d08 64
    0xc0c2c244443d59401e030010f13544e515040b022225102001400100b044840000d181d0700b00c1c460481004013000d5500315503600e00c003a400480d081201000340c7c080c05d601071004a0154151140445c07010384503101450207545240c403950000c90300700707116044000c0d01800030800ca48510f24142e400c12100c40e075891758420040f0f802401510402d0b000c2500f60b00c41400301c40d10072400440c1481100c6e502e1030300030b540360300c00c044010170366101c402503840031849169a00d010365000450043c202c20075400006400c0c1c43e0640b90401e00d56110030340000038040c259420000c0500348078968440540e030801a0602c50b5205001c1018003407000e1180019401000342e40075200d40c0c1c60400080f0740a890045082e01504010b6448040000422603141140344c001400d01d160a480500c2d04c0d172142000c4644005054031b00501086000d1919000513210350700c080c68060203240613000100303050020501c02d1800350001083c0c10100c41e150011306401180c28825401c1449c0140315104507034000503d91503000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374381825 1250 374380575 374380597
    0x1080c041404020c03071202150606030a02030a091b14011119050708060405011a040504020306180307140a030f021b1306050301021209010506030f060a0509010603050d090305070b030903 82
    0x1008101c24682c99036415076113404441c504480e07aa86160400001601d0f032810100011f200c1c1034449045500000e0741a806000040e2203582917403500480840030350801001103414603030b10035034440407511820481400f00054003a01200d41c0c140b0a0000820410b4003040b41400080c84803030304104130014a6950010020248171001d04440ca040c0781400c4180c1c0c8808000c8c41032174140400e1000640c040d086451a64209058841d000c0040c4010b41d40c0445003e0341c1900658005401c402d414100b10302070351000c0742a20700d80145076072605c051107000c0341c1c4900154403151300101095000440700c0d0400c05540020f01b41026411079885240100301e00c805e001d4280f035210400c0c000d4264000e103000d0f02e0b00030000c0d51100c030303000b510340c56641d8102d4550140d5820800490690704000c01d5040101401c00080c0400c4da070b0300080300018000141c0104c020707641e030748000004100140604004101e03d40d40b902e43c9070749541041403030107d5603042910a24020810b0081500b00001161106491 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374383075 1250 374381825 374381849
    0x1b03050d050f071211070e06040b010f0c030c1b0806041205070203071503020d02030c07031d0f090c04030f03050729130302120a03140a0506060912120a080601080601080c04 76
    0x481201710303100d00c11812401040d00c1500000300d03600c0309058060f803140d002030b641001015080c178011900d42c83c9203800715010419100400740400d02c1460503511290003050701c00c00310449a20b0080e803100715980902259007002080c0304c10003055046903c001030b410b00d085801c12a40790006520342130548940700100c1350300d407000d10b0514000d8051f1103c181d2902011500e034a0701c02030072407940d8030603076044001811072440c4807403031200d110b203114000201404440150308003000340030700c0d080c01a02040f040f6009100010018040300e000001c0c01f1b102e951483e4480d0420328103118440c400c00c95140c4481003000202c5000b11862142070b91041c0007183c45617110001e414242d0500034150880440d120001a250000641603002203c146a5802c11042e09540d0140140d0032243c0554070194060400c02420249190a1108090040c0350200f528559168001844500da10981c11200440d0400381000615070700710340100e0303000c0d2080c204420f0b1403400c0707203815031103210718018190385400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374384325 1250 374383075 374383103
    0x14040603080f0a0e0a1d161b140d090e0109020a0203070b040807020a030c0f0609051c020102030c0a060f0605060a0807050a02150f0f09070f030f0f1b03050d050f07 72
    0x84115918080890090114040d0a072210300c0c1401031b801d0404080350825104000c291a111010304041c00d804e03465a0b0704828480e089052030203a08038000c00d82c2c00414650100b41000b80603c08106003180c0c3d5240e0035610713450200c4131018503c05a0202c40310620501812118640100481c0c04181d071168204900b50346501d00740e5014094900d01030b41094a00f803000c410800c103502c540c419600054110110b0554900003110561401d000325074100b01e102c2e00c0c94070503030070400150400c90301c1401503900305070f1700920380740c035084804100391341c01a04c6800d854500d0045206034409442e054519901c1c081850324041c00000d805415032003005400124421a140b0920030503a054042015555031070400745242d40981e5425202a1481d2541401142c2910000640780d012640c612000d40c0405180d0307101c17800307258044541541d04450901403040020003103265402c484050154070a0010308505001e490442600140d40034040f0405c042015942c0004c00ea0761020741c42244810307045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374385575 1250 374384325 374384327
    0x60306041d100b0307050d12140a0509040b0a0e060121140f060d02010221090d0615060318020d0203010f1404060c14030403030e120c0714040603080f0a 67
    0x209250102000301254030100001c100800304590407012042e010500c14001d28901309615001d40c0d10525520003d03d0510308002036000e18180c1070200a07041c40903a040c2d44101ca410756600c00390542002400000f180b10f4549020304c40c142c41d05100b41c0308603140c40d04005500300b004801400d80d50503c84901300c041c09555801d0401d00402603442c0061200500c2e850320840340e10000c0c1d0344680300d80040d1002035228140742100301005c0380c0590003441c8001d584c0752a900003825002da41000010104010443d41e150050320009484c8151030018040742e4440c4d1480b126003064115000305030804802c0c440700b022150300940c070540c0483e4245030f01445480001c1c01403480d82041c14095040c0500c0c11030740c0070320703c405500c11801103d041c4000401d08004880c201c00800c000da11844040c004507010a2280c0c0c010000c1c41010011101c074504030301c4400030b1541003060720002e43c0e400310406102c44000e100039030820301003c0d24203001c0c031401d540c0c0340505405204030880305a040803d5040b021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374386825 1250 374385575 374385581
    0x131415010e1320041103100501050f04090501154104030606060305040b010909050a030503070215090708070509131106130906030b0f0f041403040902030c0a020d0c05060606030604 79
    0x10581c0000b02c07001141243c45540481c5501d060303440c0c4140d25008142c2516400301701102d2007441d00d4540030003190b003408015035064000c000303194854203040c80081642a264812a8040d1007686481015440c24290080600c0b508010b68116181d08006c4005114000d1403c2403070300c030980e0345807400700a04418800e0703103009550010b4165402d10b200000c0c0c080d095480300d4020360213201c0790100c03030ba00c1d42e203840b083d582c0080d40240340b80c2c8444070200120f4401d10146421584510546281c40080c100d1403019810541e03507000b81d80c021000400c414641003100038014002a120000603150510141201c03a140c1880079101c6910604505183e5407028121200105645400902c181c0c80d100030500502d01404105c5100c5085404511002c3d955a00035225110030325204440341ea8666580c80c0d0980e01400300e4903d84000d000c0845c0403111030001e1231058031240c1300c00c0e858842e612402031030044410b610384144480904050f0105078080350303040e400f90003a18402d0780d0b500c1c1c601c082802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374388075 1250 374386825 374386861
    0xb0906090a09080f041e081009060204090207060e0c01020d05040905040809120d030b010e0d0609060b030d03140c0a0906050c0c04020703020a05070b03240d0b131415010e 75
    0xf41480050181302c2d621454000d0b00990789100100304891196820000416256004031841640017840c5400d08844a8000003592449004054141940c7c0c0340c2d40000d9800031801104e0654451410751207100c0c04200e101d01c40102403000741036903e102d180107006e074032450003410241a15003002030f0501c030341d480c1103e55008000d08020450070b0041c5106031039295403001003000904000720904690f100e50715801913990014050f6080b00c14982d2058002c052600381140c45a03203c60541c849035500340b01d03900550100b0340300403908644c078090007103241c50018040e60240c035007440f0400c03c0a03844440d9800351002c500341540d66480035180c003803415480c0040790f94410300000d8100b08141c0d0204a910a1502ca44110b4244545500713005109000880f0800d24800e410900c0440b182040c101e5003250792006403148260170b0103030710b0b07052100078201c649001c5006201d00324000c005d00f800503c40c104d01c00002501d003603209888209250324042c81090710001c104004907103000f0307c1c02c090400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374389325 1250 374388075 374388083
    0x117040c030210080106090b0306211005070c0c05040612080d060315020a02010e070317160b0412080106030c021c022e0e0f030712050c1002041502010b0906090a09 72
    0x104840f409200200305103024000c000008550480024a0b690309030144ca010307500081105a0a0488180910700484c80340d54010b00c511402080001c91980392042ca4010301595494000d03c3d943c07810068106107483e80658003440c40d1440c01c0001c1002c040c8644080e65202d078032603542e00240c2c0240c0700a000507030406800b8003100010780c3d400500f10740c014100c1c405650001d0221000c6541d04640b90000b85c40003410b40c100d1304000c142e24482c000d00a05245070480d209401c100c9541e15420740905046500315455200c0d01e02c01848107400401c0140144032070300e4148280e006044009480c0d103c800c1c03003441ca00c007450301c010074000d0007400100c0207560444810b1078802402082d04260080c2d00001c11042440c00e2180b106020000c9000300280303c00100851401800e40c2d1404065902103180d2000c1060130300844440032030501400c5006000400c001d40c90f18204086d00b1228a401000701055a01d000001c042035203030245802d52000c01101c0c100c1e882c4e80d0b203208840142041c200010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374390575 1250 374389325 374389339
    0x2010c050a060c0216050f0907050307020106090e01090203120310050616021917030a1d0a150e090a0209090403030b03011b1e0807080109020f04090216200117040c0302 74
    0x10040c144d00040c1d0071204400115119540b940d00c03004d0095003803510f05895004940440000c288501800013142c100d0a584000145035030b9904030001107607250b4145c541903035102d041c4441541b608012203903105068401c07081c81c60401d03058014051181e0701c00c0e1401040003003062152a18001c6c0c03a008419006884c0302034901c03814543c50b54400060040c0b95405030100d070b541071b660070008266a5024441e417544c22140c3c9180140031180040c0180040e448100f00340081500c1204282105414010f40c44019408140000b00031100360002c008010083c410b22400b110b076a503007040e140e002505801d00013001176090b408070f03000d8a0340d034241c01c001d0107283c0903440001c0e1380326100308108007800001000d65508144200c50b4100309035070100c00100d650005000e10491680140350082a00075442d1a140d070301d44014045ea04a85c41088041580365078107014020791000e0000e188800030b0404c0b00414514002038074144000c0c150214213482034000504000402c0500406140c00901c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374391825 1250 374390575 374390591
    0xe06120c10030f021c0f0c022806061505031504110409050703090204020f0405091807031e02190806071103030a0f0b090f011503090309050112140f060307050306011202010c050a06 79
    0x50b0b1702030880036100a004a150000010b2050302c0072817402020303414140040e40690390040102c1d9110600b4500741c83c82569214001002100c0380120031714010325440e0710b9100e16000c4c1707480110b02c0745981c07450300450a0070a05051882c240301107800f941c0c0840000609502c55407030440041c840d04000a42041c07000072315a41c0750300710b00080e00881d80103c1c3c522206684800d145600c850381001d14900070b60000409000050011802000b4502b0307100d00d40242c0c13107444e000a0407001c0070901400c0381c10102103043c07020344010b00c41564848540d040c000101140a129681d580c8070050096020303642d241c1c2c019220601540002e042a0001000031502c0e08100080d54151a0300b8405c840d0b84290085c00501c501e40070b801120f04044e00754560040c0c0c50700c6c1000641d007011b0210303d80f07030300107560360480a100764500c81068051100b14080002600d06213040c9807a200f0a83c0116103c3e0b03110381c0c0100103003014400c0d82a082075081c41c002c4403001c0d1038a8030b0751070061140402401e042c20b091131 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374393075 1250 374391825 374391877
    0xc17040503090f0109031106090607050d05091008040c060e0f0619020105060901230d02030604050a0215040e130c08070803030708010518060d080409060e06120c10030f02 75
    0xa070411402c1202c000800440800040d11030308001d04c40100601078108800c8124500b08000e0102c0da280981123900d81942e5070fa87c1c500f80741d03080c1101c1011a40100f00c8400c07504202000d0b01003098241458003c0303080507251300321100c00d10f201c1c1d002080303004a02c6115a403118540e45803480809040681c60300c0e800014100072040303900014006607c1e2800003000780c5030428100381201c185200d5046010b8054441100c098100c65000d904149020321050058604200151007113002d000a0800d8001c10710401c9a181441e040c03203813100400340414023118a170130440e15040010622021101026403601c4450380c0450340c8450200e004e1030000003905130022004522615081d91450313656078030b4400f08002401e0700201c404108a440000808900700380d01c1c3d10400311b01070702c00a81084c0d9282e01d00c00c103844040d0455109043c10320103102c41c41c00d01910354076003a240c05000d010005c4c106004514010600290fa01c101a1203c8080003109119030423200fa000803140408561168691 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374394325 1250 374393075 374393077
    0x81605011e0e01360305160b040b0609060a05010e030c06070b0108010c09030b040b18070605040e061002061308040312030204140307050310020c1c0f0f0f020c01030c17040503 77
    0x1440740c15508040010380040b036404e200403240c1a4844070070744903c650034402c000040c0d04150441c107024003001090030510544031600c00d041d128000016031494a4508015607034405000c1ca40038100140c1400307010350300c94403a1802d84400386040d003a0200c4410009161103060380941d038101d8000961038081c092000859410384d42901d00070300001c048003030304070740a0020744000340152000001103030008114915840c0c100501c030640d07020202d492803840d03003418500c1c0e210300081a00001c080211010500e40b8581c0a403040710444150a101e0001a482c3c0500070242c040c88024036140e80b00300b204100540b806950410301c02940d402c1c4007503000e0001e5101c2e0003010040c415103841d44100d8980000c030903007aa603001d806480305403e400c030030314040e420545441c8458040c0000c94502c040c1240c0b446541301d8055070f140d1185543c5114068010000f204c008010015021403903c41260001121902000280313030014842c0c4030381400716103038885044404401000c010a110501c80000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374395575 1250 374394325 374394341
    0x3020c04050a0c2a350c0706030b090f09030d020d060302120102130e06040906050910050c130b030c09031e1e0601120521030108060f0103081605011e 66
    0x284400b4201d03d88034010305580102c05049090420021409400103003984030701c914000b0411070445c1c0010b1101c8801800d19945e06090700d015000032030304041800c003c0000000422560500704880424040070910040d001482000c0c400c41c1640442c01003042001120703a4943c692508640b5219840c1e03000f400351886200a91141e0740b4401e410321002e07011310881e01e10845085040311880c1c5885600004a0340c0141036a611a43d02e0100401041290080f035200380d4440d40601a0b0009403d600e004070b4030054081e0b005910140702c4000046450040d07042569049a03002d5104d55441846252510401d80055054010391070101504540c2c0e144440031030032404242c0b140c0440300c0c0740d03c150580c41e00249503810340c01000100301d80c0058099010303005000300182d0b2030702d12a01c3d1605849508400c108455140000010000b00c40140042d94118100700030078155945503898184c203a00600030070596002c4442d090340708200d02540001401d0110110b01f04d18882c81d0380c80d0320001d00725031f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374396825 1250 374395575 374395577
    0x72304060f0f08040b0612010204091e09020a06081005040903030e0616020d200304121a1902130302120c130501030c06081b070807050c030106051c03020c04050a0c 72
    0x840000d074000b4068034500b58007070500c0c3d848500680d103036160a103107100c1c007412403508202040c04542c008042800104003910a130300001c68040c0f40c0d42c030368010070035030400c11013115441d045410740165100c142d50002c465851414101c4e0f0f4030f81c10442c614030718040e0702084c0e10600d403080c14400c058044e000f92691660752015038885d5605c40c2d616090f5a04028510001a000a4454403c41d4002c40e0350403e484803070300c0e14500c5203a0380181d0515560094209144201e0301204100422804000d6003095052168040800e8100613400000a65101444004840d00402c011584c0302a461031100290b8006241d680c41218024103c0d0b10703082010f01003409550482084490502d0a0003914122940310380000f044601d401e00840d030030800a40103029040704030008060300d500b084054a03016018551256403003405140061601d01404981c500a905250040100e0350341c0c00310f4013015181c0c601e180038510070315140881c14040c620000c650700614140500c0307440404e80e4405034503002c10f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374398075 1250 374396825 374396837
    0x7030f120c09140904150e03090a0f0509091b0f03010b03010906153807050a11040e1603200405040c0306050f0c0d15030812160908030f0307230406 65
    0x404001d1213a41002290050303c4049910071420200c5942c2e0b11040300015107a0503203003080c0c140e00000300300c280c055200d8a10108500010311403441c4c140549900442090024802d064030600c00e403403242d21001340700340b01d03c0c42400a12180e440139044020420340040081044a0443ca803841c0180017103110403149540c42040880d20400010b0012585524004070300039805001454540311b0071805400189450288000c00c0041c00420101c00e02e58401e95040c0c1c1d410103644140812a031110020500301d5002c200c2e01d03c003079043c148080301035a030071103100901c82c03812080061200d000401d04036027103403815040000b80400410f030803094904c546000d012131789514070358007038220301510360911394042082016806440c5620094128082d0300035240c01541d0780d140c48040c2c0c0c01c80e076050b0b800c843c912020406a9440c1c8a01404440e0071030030525200380c1880c440540d00d004040300101f0300780c00000400c0d280c42c0030b2680032000d071201026035410f0201005100038540c00c184150008685 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374399325 1250 374398075 374398109
    0x10c0305070f0308070806180c1b1903080a141602120f040f050402040b030106110c06030a1401050a0b09040e070801060602030a0e010318081e0c0109141207030f120c09 74
    0x250114030841007a51000c8c0211154542240d11041980b09001e041c050070040b90003460b00030b02c00d01110124900016031805082618100507264910080a030ba100750715200c1805890070b030407030140d034000d2004007810b042c40780364140c00c0e482d01c42a1580240d10b400046045c4c074180e0106c00c01001900d1840500842031039482c4107001c144d0003240544428010309200500c8013074031071115583c1001e4820100e649000c88c040c0440c0c0e5550094503180319140d10350724150b40119024110f00c1c014241500c01248031841c080041d50b442c090420400e20981d1140e82d004070425003004514080c0041d8002081415500d50b8041e60741d034800c058840100700481d6130551158003e1003035050b10606036120500b200c05565404090740d010217045200301c0401d07440901c20840076000f80c41040e803914000180e1031841d042002001d0420110810194440a00d0030061080041907503102036260070f03c00781c40d0301c0d0850280c1c4d020000d880141c4842d071a0846643c0708680c4120030070b04446404807040302c651 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374400575 1250 374399325 374399329
    0x501090504020a08010e0717040308060f0f03060105060901030f0608030403051e07090906090501060e01180603080708071e0807030905030309012c09010b09010905091005010c0305070f0308070806 86
    0x1c0200103c400108201d1001000714503c0051565842441072a2000c07403c6450903403019004815507064000a0350681000a141040c462420140740215500c0046014405c0041d0390f540701401628000c2c5004100901a070340690410b40e52000400001d00c081900e8240d981d54a403c1380c07100f0758041c03180e01380704001c1150751207440314003601c1c410140100d9414240c0007400740860102c111000d5a0700c10544020030401e20904010380009405481e00d545090000c6c010342d03500e0248041c500d864400300301f0006141d5011100201d41c00840b06807650b91030304081c2c050900044002c0c194800000d501b2003007144000040c0300c40d0781300751036140c04203481c1c100345542d9000e40c607100e03070200d2080130b40381401c41d0b40500750800c90305000038280903d4111001042c0e400702c0030b0380301ca5210440070454403000c1d82c011940801806042d03a4a607203038544140ca4480300609403066a05100a130303043c04092601c244100e44146802c034400c210b04200a00e80100030803002c4030705000284802000c22518 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374401825 1250 374400575 374400577
    0xc150c0f05071a070c120801090605030c03300d150e152b0c030620030a090507150f0801050a08070b030910060b03070f05040515070228050109050402 66
    0x42d80d04820748801c0c1d18081228401d409601400c01c0050140c1400030a0018002c0c00c807603056260aa41c0f015041d502d07080c41c2806842a40d00305920942100d88800d0103900d00040c80e1104c0d04814000703c1c400b1401130300540d0b41001d1841c1400300403500290790301c402511900301e0602a080440d081c110301d581e85410540d061416a0100d4600202c032a140310580382040c41d185d80301d2070000c000012000707180c04a400c0b44090300030441e00c2c1c180f4040c0c204180a02407150141840c8886203010902e18480b91049141c48005d00703145425a81c4e0b041c000038005d0410041001c0c00343e01c00403010042c02140b02404c08402600554002044d4200201d00c0c1c1c149095840308584840005200c40c41c10030560071a00d410080560040b480340c7c1c20781c1019075000340540301c01095041c501b50368904040364002c00c0c069132070380300030140041000200724603121101c909603225044203103603403150a02e100041549400180180d06480c000f020706141041d5140103008407003090f21030b040095541c60038002130b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374403075 1250 374401825 374401837
    0xc071805040819030b0307080c010306090b01080c0c0114100302040f060e070e01180e04051005190b2205060a051203070f0206070803010602010f2403060c0c150c0f05 73
    0x34400203203c810004076407044086004015401c0c00301740c11102c000400c4c680811544068482e500480070441156003502c84d550140c410303854140300b10760031080003801002003e445026460300008003045415800e41c0058a1034222244608050506805001c1d6207110390100382e10451500300213648180b000d10030032080303400c16100b81500f640c8500081e84c80f41041c4081e00d05229a8070000d80888036000b030080c01a1091070364440c61401c041c1480e601d000011003001d1440ca00e03200502480b03401840e460709c100702c0c80304000700c0c000b413a19010034490800c88038441d140a80d2008003c3e000c0c1010b0b000640b050300140c4007003800a60b50030402100f0348654842a00541040240b030000c43e07040c10f122025140050082482c04103103039074a0505910076403103080107035918107c0704a80c1c00180035942e00303c600d2000c407000384058034111180c07041083c0310003400ca80e42d6102070812140103244891110342c01c110748084043c04040301380040c0940d420f6120000d100c9104101e0028015016215 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374404325 1250 374403075 374403083
    0x41e020a030201030f0605090a0c020c0d03050702040f06120f0308070215060609010203090303120609070926211201060c0f1416031b05060307050f0702150c07180504 73
    0x302091031500154010b20180c03a05100c0b554440f003010079140c95280d00540162030b54503000074608100030f0000c0c1800060b0421902c01c1d40c80310050004a5030040c1134a001540440c0c0015184901d0150080205011342c401694941525440380900030405e20000b101e030b00940342c907ca50b0b40c1c2c03160200c0e210f00c0c8040d4100c00c6042c0c640d01040392814802e015110860040c01140e181c03205500000e0325641080c0b0100e40003108100030048181040c00559400c0703c024206403c031075050800381ca10014040d289441032844014628450050801c5450454003c8055400350f050040c1c0c034050b01980a21402d42180c88424000280ba034400e81005907801d0300502c0c020707018050383d030f03030451901048200f814080c4140b00c1e02020940c807481e01080154400c03800402142c3e020f070342c00e000c1ca101c280d00252154205004100081350014200d5030003918100e4070b42d0b521510761000a2112103072041c44400284041010b20707541c900099010103807401a010261003015552000044d00c104480040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374405575 1250 374404325 374404339
    0x12050105100501091802090303040f031101050f030601030209150d060602011b021504031412010501030c0807080a180606030302010213140f1c1203021e04030b150a0e01090203041e02 80
    0x2202000b001c2170985802c404d510098a05016000028a950013a0b0040c210300600003a04108001e00b41c451151107220a0030114100b403d66848201103000003002e15051540004030000343d82d450f1440100c4004200440720f4071080541003020003071256000d0380d07015610305209440c8441030452401c04144055006080c0e0b0201d4880740f44117604007030011130a1101d200d00d444c48074685240948506a030040009003191b142000040a1380c06440750070b0f003440880b0040c0f100035a40400581d6004012480104a0340c0d901c1110646401e99064042e1402e4605240801010b0741900106025100c15659595154450701035001c140340c401304a6522030200c40b4109000c0c00d010405011191401d42107600301d1f14591210050f80d03814000e15030000740e0008a4415464602c10b1205502e4010316501c0c0c24903007565640306031f959000d8036004016070206034100d003542d13032200c0741c40c05000c0000b011481541e441041501030b4205072011658414249002c0038140054031206040e030390001d0001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374406825 1250 374405575 374405579
    0x325020f190b040b09040b01170a0c0909140702010c080130080d06260c0d020d020a0801140106030c021c0e0d0b060906060c0307030806060d061205010510050109 71
    0x880001071203031624480c074a54800000c0d1941440c0050300c001e10f00700454994a404070000c21044500c83c0314064180300c5074905922007130301403041803030307002ca5482c80010300702244500030b5800c15025407060030b5450405a8560024440546131401804a80c009010804c1c1d880011386200a0034000c0c0c0072162400842c584120013000b6650b03400001d0304980c090103003034075201c1000a80c0003094214409440381010841c12002e100c661110158141c07400c0d884c0325800380b0940d25911a072034054820418408018103655400c00c07801580399006281d911126561002940a172140c0400050398110070000042c59600030b0281c44251501d83d8064058650f0441d5411381412200b5070107820800023300e50030182d1280d11244081c14010300d03280069213000402c106084000502c107a005120502207440320f014004191400a507060901c0e4a01e580c42002240c40c038012002d00080c0300c0d0400c41c0000d040d003d10240c900d21140030394000d000c280e41c3d0050a00360010107110341c6000407240c3c0d9003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374408075 1250 374406825 374406829
    0x305030a15030213050712150b03100b1303031407110108091e0102310e0403050c0106090203150a050a050d02030304030506010902091306150804050a12020325020f 72
    0x180d02880d00303206044003240c1d22500441c29030001e071901546099905d10500a40302d40000c10468809001d50040c0000c42030380341128502040b07031042010030400071006c100d03000b105180e40b80c05400540c09a0392a1407100fa034074400c00c502440180c0110301040c0900b643c8504500c02c075491150072641e903644a200d20801160581401081100325001e00c0340d000d03c0441403444c002601a002c0350016881e00d48068900c040d202e10368100842002003600143c50044407104a00205c90b0150b6a550345031f070301c40c10140c0e5280f06014100195510300400407550022946c090350040c54070030342411003101c04106000c07141030240151a804041030b682000145404109900c4451014081d00e003450340d690b403190315262080e0000035810341c0114000c0601d0401d429031189100340c0400c28040340b03281146a01c41d011005400f5820001001c00041c20b10404015481d1095072150342c032080e465026900940700e800c2801044079184c1c98140610850401300440e640f20f07500240651580140c0100b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374409325 1250 374408075 374408081
    0x602071202060901020a0609030302040f0b120a0c0c0503130306051f090b03011e060e10180b010509030a0c0302040509070302090a02090d050601140108010e0f131103010c050409180305030a 83
    0x10780c60442c41b0311718079500051301500522404620a4501689542c1070481c061001700c6583c101c070304002c10520150b0542200c1c1002c03150041c1000c64001264420410100c0e90601c5c102c41c054a1b41c1320005900c40007603800e1000404880c098001000240c0300e5202aa50100d0780510b0a41420340080040c880000203900049240100400020740c0785206640d07070703c1100181c0d8101c407040b42c0d10002000100300095041d23a001180c0b0344100c110508111040310011000a4044059a0342d04d20b10100303039018074116038002c08000c0c100e03540a0782c585000e0b014960640800c034080e0741048040b58031118005211001e599004220700c03d541d40e80b160980082d0026032040ba4090700d4a0408004030f50184421070180154500d00c8001d154010009024104181d0117984400301c400304020111400e1984d26401000004944040042c00d081c00212420740b0352043ea859403034250076941c1d050300701008204940c1154000e120450710318069141c42d58469030042d011075001c01c00101c846005034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374410575 1250 374409325 374409337
    0xf0a020c0d110717100c0c050a0b0403090e0c09010f03060609050904171308120a0f0e130204080a031211090d0c03060609020711220c020f1015060207120206 69
    0x1030100d4443c0c0c3d5549001c11509981d03042c8610141e004000f0f446010202c070b0140d12008030041c104482d1010056031340c0c40e90342150040260022000702c0c0404d007058461100403004200003c0480c0e003500b41030441c0701c5aa0321142200d8003040540e130004c0340441c024007070075040740d05680790400801e01e0001400b940e02401031046031031240e20480032400700f0b418805001824821602d00c07000301c0c10301e40580d00e07001001c40070450340b5506121845115a1100804024883e14034004c100c01c0c0c4001c2c0030030031090380b01501e80203642c0007180110b40050b00042840005009940345078846035914142000c544002d034500000329020000350301c06050600c0e898070018400c080310341400d42d807500c900f81280c1094001080c41900011000c0500c028443e190800e002c0c00c4964403440e0b5a000c0891107941514030319501c0e1151117585904001e4020b220141407118404243c810000090b0517071402414245d050780402c0340840030200d850340c80010510700b40c0742070601c0804810704039000c0103d0707038102c1d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374411825 1250 374410575 374410607
    0x703020c0a0203070801020c1011090d0201020a050106060206070f050319020c030f030c04140301021603140d06030507050108100b031308070f1b05120c0907030615080f0a020c0d 78
    0xc1001c0401601c1c00c014003c02800000001071311880400800d900f050308014190780300a040150140000808a0031280300380411510b903006200c10b440107074104014428003401d29440c2640c00565980c000c9280f92050340310781e0718043e0342c0c0d011610540d01800140c0309108248600801e904140086030700030480b04200c0c130200c030300b00007145411145030750040710075400303140c0046010801c03a20350488070202510228029803c064a0b91160141c1561142c005010803013209603407820034070350b0b000700d8984080710745c0b060141c00c6d107a041030350b40d400e018880c8038005010200000c40c40340c1f91046003402e07a15000012403464803a5010803900e10300741d0805860498040000c00c000407124915070700700d0b605ca0640100945035044491544001c503030300150040308014000884d80c413004c20302e140a0380040340c0703444107a00c4501c006c800409154101400c2c5540004034605101d8202c0c0300c441c0320301d80e80000d4141d1070750394404035010f07801000c2407511158405440c4404042c0204031100320030728a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374413075 1250 374411825 374411833
    0x1b020111030304030f0906260403050408012306120715031401091a01020c01021e0a02090414010b040605150703030f02040f03020a1d010b031b030408040603050906010e0703020c 78
    0x149030115811944242d80403004a64201d0118441c0e0343c000380c2e0140184800d0030b041c2c00850541071071190304101c80740c2c10601003a00078005000c25010b40c0584010340141030080101204012540b0640f28046405c140b03610640703000600b280ca002d00380d01600e90102b80280405625010f01c00240031030342d0002009064682540310266500109128000c041010f80440d091001e4002b15114003a0104076034110342189038001c00c241d800040303500340f2a068801140305a13020035000e600781810940025800100c4030140700c00e101341500c0c0014954000b50007001000c01c810100f02c202d603000c1c07040940100708464588004002200a0203059001e03040c04102c10b0f503c200010201d900c69044031091010082c400e01c00d500300706403c070024080d074000c40149102c80030b00030003080e036051150ba21500c80000c00950b040310054661914056444403117900c0e402c05107010150341c9c10900070748001920b0440040d16440300000c420341212031050340c180440d20b404200b107002e907114808007402c0c3d100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374414325 1250 374413075 374413097
    0x30201020f071109130b060f0102010605060706270201021203070e031c020d02030906040512071e03141504060f0e0a050105041403040605090d06111210060507031b0201 74
    0x15490380104402482880500d55403040f007010400c04100160a082440b5800d20000001500041c001d0b070708840c048840300c110f0145540100d015282a801c010b13082407011440c1002c100481e00b012950403541c907c4c04145207140707104a800300c0040080179005910000c00070050303000b080d009640043d2070780f81c81002c00441c000880c1c54031102c15030950b4008080d50920007076aa060000d10040300ba1031014503c2d001c01e1000007020b80c0102e0048902c104c201040e41a440c07001044410010b00b051481c0d01148500d5007000300c401a050300c4155402c0111001c4000c001501203007041003500c105c169000719460340c0c1c907120700400e41c0100c0c17041c185035104a00a5041d0040160010a40c420400810070340303480e140c010105280e20144012a030310a0105000aa4200003501c0702ca01003a02c003c0c02050b2181801e401614845400d079001c0413001031200141c101c51507030180305002a101180070156141d01c112590301ca544400fa0004009550986a58141c510140d00203801450b200020742 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374415575 1250 374414325 374414347
    0xb01121e0308060405131a061f03050103050706030e1509210c1c050703080c090901060f08220209131403030f0907030b27030c07030b060a150c03020102 67
    0x30036004241c0c00715030701c5020072285140901480350711140c5031000322140a141c0c0d681040110b01d600d83c160381d081a0a0006a0986a05100c0f41185020f200400380f0208120070150003400280000c0d205070003020703801708600e40603004506000d00110700418a40c1d817800c101008910019040c000c06000b40b010340c2c40003030a0481411269503145d05180d44e42c1c07074815082031600d221258028450041c0f140725083c0c05810406546107942c240c01c04040e0fa9642000c100100d00c50070a185610070f003200e002040c456401003400c4600001500c3d81c54942e01d40000c0d40110003210300c401100e100d4140210801402e2407421103402c030041640300c03207002d00320742c0d59004005110840300419500204c1040301c000d15103040141c0050351100545041803c5449800242c0710083c1106040840324140014100d16200356126240390901076036141c2c601c10034900d4071412640b0003603d104030310001144d100c0c0b07480c00355203044942d17001c1565a4245404002c2d11500403030582502075560034400599a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374416825 1250 374415575 374415623
    0xb1f17010b0310150f080c1302070605040b010e0a060e011401020709060909020a0f05090c070201021519060b030c07030c0c12080d140403020a0201030e0304080a1406010501020a0b0112 81
    0x40030401501051480301c13481d02d00304000195008000c080100d160070031500b500411070b40030f03080058402c0310800c03007482c43c120081d00c100a001064076107024200418801e03241c0c0018162400948400041d494080116081c0d680e140070b040c0c075555541004008091030181d40c511086018015a03000960f1100c514040b01c849a1001c83c2e01600d9044403421860950b60100107090002c00d00c0d01400d0030803003c10b0f01d81c2030040c2160880b000005561003503a00812010070031744040300705d4500c2c500c2e09003601c2c0d6481000d0250454014104040800c69460003020307030703101d24100c001c254241859504c045414400207001034030722000240010910081040c83d11031900e0041600c0341d641e109050150b022180c103843c0906005d18400c050100199001c01e1581d11a41c0901c2d010171814440c0a400d0700351700c1541e000716503074840e003000c6004000040d801c40708207810043c01d881160b84d8520040ea2640c0592500500201125006002010903441090326031801140310200c03003000c5012120071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374418075 1250 374416825 374416843
    0x114031302040606050705120d110319050a0c1b1e0f0314120a090206090414042a1806030f0803040506010609150e03030c15040b1f17010b03 62
    0x34560028042003541090700400d03000741420301d4902c0c980b5145445440d11010300c420601251540064804d18403151500031000700c10782d152000c1c1d568100306800a8070010a440c0482c4020306010003d4089030191188207001030b01500d491b29907040030b0305c003102c4d598140002262042e01200f42c0a080748140c08034021403610980381034a200d201c604000c2c04000c0c014840803800d4900300040c08060a0b1800d400b03410154504000c03441c44414800588540920644503422a00e02300c4030004c42d442d8045010b004500842d05441d0030b0a0340e0640318141c03d00c007490b0601c0d071a071340d0a041040441c141c440714840e06168a0000d0b03001d449a0301c20300300c059030080559401801009100138020103010160043c01a81089008103160400044189a0305c00c4c0580038040d018500e521545c07001d0049441c60402c4d04140d0f100f1101c05101606c1e03c0c8410349040e224a10174500043c0b0301a2041802c0500303c0c0c03034000020655180c00e04c05070192007151558001c95480d5549450151000c004102e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374419325 1250 374418075 374418091
    0x2130e0c04080d051e160f05010e0105100e090a110d1403070b07112808071b061106060d11180f060f040612060c1b0819020a0506010e06011403 63
    0x168170340c0c03070349212008600580e90464185108011840340c98003c1c0114100003540150b01c00100b050900b08140181540b00c8d07500413a500302410031200b5081851280140c5d00010903c80300d984540c001c80b81e8038108490014010b008110201e60203240455001c40814440c4c90715001d08000303562441c1c159009501b086404880c1c15042c400c0d0b4a401024041c45480248000c0c0203000d50034030500c9a8280842c010700308035005c484c0e004180040301040312006500608008000d40c0c52910902a045592080c1740000d1405107525440840215080c1e005600040c2103440c201625110500c0c00c0b16929004d5902045295074400890201e05a081c8030780380b000030011851230440b05010018007011036540c412480d0240910020040303040d81410142c00050025280c012910b0036034122442c541c107400410500344000b410000502e00030282e84418140c50403000002c820203030380d074607401800249a50854401405002c074003c01c0135601600524004050301448518182581c0c07060b10f00c05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374420575 1250 374419325 374419327
    0x902030a050603010b030a03050a05130f06090e010e0a0c0e0306040308040c0b070525051c0312020f070f0201141201140d1703090114011d06030102130e0c04080d05 72
    0x100100c151149603407112050380203005071002640084c0c0c441c5841d52009041c81f001165a205003881241504c601c8440020f400803895103420707040128041c00c0c40b5480c00a101c07500c001c1000309502e00001c0c101c07108401158010f4607001402409001c00e0020001084031209001c110340d80c2c1042014000c60282e100e1030005d06042c103107184201c9081c0c220308175461003005100c0008030002506aa4400509240300700c61f05003840100d0b481c2c0305940b003540c0c0108181511080d8000345644a15030a1003038960080b1010380c411900300303a002d41c52059916417005c0c4078000100d940e1681c50550184140b41040056100402208203500701001d0100f801140078018010314800f5480902c400da42254102d600d20751542d608480030308003480080b0078000102c007040105101b5040b8140c11000c03403501401c55078403803001038030042a0610b9003031114901c2002c203d1504042c400c8a200840f0000c00c3d4031803a00700031207113156a90160103848500c2c4c013044006001c46041c461082031008035a286 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374421825 1250 374420575 374420581
    0x70b19140403210212070807060b060c0304080606010813111518040f14012106020d0b19080601120212010203010609080d031a09180d09090c030513030302030c040906090203 76
    0x21095140401e42c1c3c3c40155803100200c08108490756042e04c511940c441d1455136500a54944000580103c85403a504010045000c44017410048040c0c4142c2c0c0d02403048450b640d0b00c07000110b4400c2d1055400b26007504d4421340c80d4010842c2812550b6540801600c0781c0c4460002c1c99201119a02100d12051840034204001c0340c503150034010b001404881c0c0030705200407420740c003562200d03500610403040043c1d480329101d03c150740400160411990000380841d00c0b1078803450040e0180003c40d01044c072441c410a20103418074105891f04007655a04401465070f41c1c00c0c5074030b83c2c0000350501400d9030b001c0c0e0021401c0040340c600f40020750181180d0f982c1c0c0440300c2d1030007500a00c1d00044403002003d142c00c020b4008904158142038140f0040d040700e61203101e848580c14903070f003c0d0801200a0351402001c04a030580c6030001c0320241201c2c10803c08000c0c090501208904407001941d00b91003200e40010841d010910940145030004c0809a005150642c1d80c0e0322801143c2140e031003d4451a004410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374423075 1250 374421825 374421863
    0x90a030c0801060608012301020f010c020a02040b012d02010b0a03060b09220209040f050f06040b06030109032316050601031e0822090603030e040e070b19140403 71
    0xd03c000a1016081c00c1c1c07469414000a0900914800c62032078007618001c242e04200ea00c20860103009101004c020414000805030003903d40b5108030099018608041607444207501c588281c501140800304960031403420075100e0482c240030007006204564803095006030070794aa00c05030b4001d5118000004038481e1910504c000c0b19001040d40e00301c0c080c0c04100d08110b0550700300d41c56096a040b00c20b841640c2d56460071400304041c2c4100079000f48903020360b02001c02c1000545c070380968010fa4080b581e07075984004041c242e500d001c134018000388461584260f02c0584980e00f0200f50300f20502d050400c00c04008102c4400310740401038801c0e5028600420520401e011102c40d01d514450780300e14000304a8507444c100d440340050158445623501903180c003a820b004041c5000d414240c0d81445000c2c0c3c0c900b001050841c01210083c85249002c25600c601c400011740032048850140380203003401030841c9842d0010315003d500078244034464030584001d0002e03c0050020310300c2031000c0c0034002c07500c650f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374424325 1250 374423075 374423081
    0xe030d18080d1d06040f180e0102090f040902060904140f01080102040b03070e12010e07090b0d0c0510031e020c01150501081506090604030f051c09060c0503090a030c0801 75
    0x400070700d10307070020400c006102e544075502c400003201c1d102d040c260600142000c20072910982c0e0010b11080604007000c9801d18041c0c00da8444110310344002d02031880040e01d40f500300d21581601c940d0081181c2d40e1241a410035030010014280001c24240c1071a02d840003003402e49410051400742c0407007900811403081c038182030483c00f400c1c000001310300b82820107494040d240700150180040c0010182d0460481d0356800700c6c40c0000300400001d21420004101042da18855401440c44a60800c4030381d46da83c2c180101c1c800140740d0021918400c0714070300018030003610608688001055210001000c020640704548460700307c01800059071013454503011400c4807440d0789000766180c0081c00410590307070b0103000306070001c4000d888909040ca070140010345500c60310841980201000c180081070040e81c611042505000b1000c0c0c40b4140d0924050603c00c1e6070460410340170864034101401440d03c601600c114150ac075404980c42c1000320b038001007050607142d0048414800c0c1382c2007841007202c280 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374425575 1250 374424325 374424329
    0x7050d06050907450c020c01020c04180210120c020a0c060c120503090703061505010306150503010e04141e010c0f140a03020702091911040503100c0e030d18 69
    0x4040c400203000d14800d884d200001000d02074810030700c107440a04214000c40320541403c4d1801c000700700c91290309402944610f01c50034858058010032081c0340039400c1c035005110805d070410040b4a5544101e43c00c00022a60382603c250821081400c038428139a5148201300b03003026203800406209800b8a0150f101003919042401000300c56024000081c02d12914207002c0141424038a03201e685035003000d407600241d980080c1003513081102c5110f47c00100d0801d202504c00a0b6420304c82035803100c5c0c1040b070350b084421161000510403c010412407464044030307078005200c2c0510903400980ca400c0d507403078580404080e040c40c00780c540c404541c0c0c52092091001c140c441e402c1155101400c0d4601425107803000c0c1a4910507600082c120954921a904880200f030f03000301203201d00d041004403803a84c5a03061001c2c0c41b1301803929080c5544c0f00645000d8804503130008008028403004c109004c00900180a120028810303400c6000c80176660034407880d8441e45140c1d035210440609413501071140400360b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374426825 1250 374425575 374425589
    0xb0105010311090103110c03040f080f16090504060f0219020c0a051c02030a08032701060b181f020f01051803090603150904030c020907181707050d06050907 69
    0x7412440c0228040700c01e82d100c1c3d10003403e00060780098266450080d01c50103000481d103000004020170108207201010040c0c444810450b000191002e00c417a07580c031400c4000c1c06007134050000401c0000300342c1d0803c0d58058491100401c0b92241850248103030b0b0401500b505c0394100c002c01d4503600950400c816202c8500803a1102507540c50400452807100c941c000f2b2607003881c000301c00c1c00c1c00e64408010f0b903005603a001d00b00310755070310345101102c040020301c0f800800c1854244c0040030110700d05024280558844003010f6207014445404802d084d44c46182860704140814900001100a1409525021380c550003400c0701c82729580b643d90031948010030803054409550145100300e600013003503e07400c08050350701542da070300d41c81d85440080d40c03820025540f109a0707204100070981d02c240c4509210f842a112003c4070b46901d003040d151406040441080844108020041031054180c409194800310013a60701450b00c1d000820b210000c104015140c007600c6d0030a0040b22141004048014410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374428075 1250 374426825 374426831
    0x330f030a0f0b1f0509060a0e12150c03060f040504050601360e0f010e1006060305070c020f0d021917030f120402150a0f02010506060906070605040515130b01050103 72
    0xb58005207207070803012a42803c0d0003c03015055003c0d4022000c0341d40c0500300602254440419032802001882000304203400744820f08821484000e0020780300700c403000780300003e2129648076850b01380f1942004040590000440258440079266441054000c50054019000d150304052469040e010000b00700054010380d000c222606400c0001d5140440d181404003040c2d02e00320b000301600e00409800704119552815100e8404c024001038941c0321744a80c10001d00406c1d80d00c10b0250100d4404035900b00200c0c544024070001840d080c1903035111690000d10100d82c090b5684c001c1441d110306604880100442554280415081410240031400000009601d008211404c80500e07004a48c9102100514503000c10115070b516a0b003c00b090300501c0b4060b0711006078034801000e220b07202c40450b0155107000701040060900c90201e4403140e0f80030f44020310780056999014024600200181c640b4098118142c0c565a0202ca09a001c4c14000c81d807040200080d04140d0612801039024030b040c189 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374429325 1250 374428075 374428091
    0x1e0209161416061503150c030513030f120e120301030c050f0d060b1f080a050109050114011809050403170f0f0112030c02061b07080705330f030a0f 65
    0x40c9840000c140c1c00d40c0070102103062001301c00e083e42c089600d504000d0010101030758410700e00403207605c021340fa40c4103a502880562207829071060703904015503010b070009512125242d181400380c0308250040d20f60b804001104062041c0850030403001080e40c0f070f5002c10020040061002e60161500905001c03078100301402c405400152400705807141c001c0800d80c407081900201c0c0e50706220540d052054010041d1441d00440000702031200c1219104a018640f0002242c80c003582c0c4502e0b410790303654456000510214000660321784a1004100c240700322010710100d103144031405443d010710b1080d02e500d07410741b6070703600c8100c007a1100401300b4480480544c10004120b102008041c112090b510181c0380581460800300e408101481d0080e40019000a0440055030904032005038401c1c00710030317155015121280503844410a119555000601e160b0508401c0005080d80100c50210400c514406c103030380d444080d082d045915810000c090100803c082440e1a000d480300764400f40d031041250075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374430575 1250 374429325 374429347
    0xf03030124020304030b0708010314060c030c3415020a0903030507320f0a02030c090711160603050f070903110a03150c020c09040b01031e02091614 65
    0x2046003407640810800242003495424002c0c0700701c902458105440822a140000002d404014284022200001d1541c01020a4840404c20324094080b0008041c55604e034030802030820f400040340ca40200f848120747c0419500701401031008070082000203070071407025060007184144014012a10035004002c2e8541182d030042d001001d0301c0e4503042c65512401142001820042c038200701d003455003c00910854503904803140601002a0b45088916004900c20460b44505600300e0094050340402d000840ca8a07100012980c801700701e1030038010058407684828542a031000901c07130109682d590510000d6454000c2c694888041c009030f0719030381015103004040c401a0f100c0a0103842d01603181c081c86542c0c002c0c10b08021034001140d803440c2400c540492000b400810700090152086802150660a05c0500144540d0f085128400076a1841d15800e1100c80303070b840c04d01c10283e13580c10302c040141d45072050640942000900d54020b41d001c000007401c1c1070604548480c01620501c1006040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374431825 1250 374430575 374430599
    0x6090601030c0b03070c05030c071404060303140708190527061603110703050106150e130902030a0210031a1203180d050d020d03060b040e01091a0a060c050f030301 72
    0x450040f0101907036680c420200b01c80d40e050800700280b07180000036181403401c000285070001c0d903040d200040112041c0c2420442201d1442c4001008520114407001004000701d000c0c0903954000d0f141c107441c000b088540403803001e0f00c1c55101c1000c600701007000350b030301042c9103506024100c1802c0c105030380c010345100103000d5000d00040c21007080ca00003070000426103e14142e1806603294811660340d15103d1600e180030f8000d82c00340d00120800240001004c0b031040b006014039240103069807200002001e1040c0185c025410103907014403500651100585038104171015210590b500040d602004100d00101c01146d202c1d568843c048856401c5400c03035011048404260704505403041c46600c44001c80c5040038403d502910602401c0c0c0160115500410801c00d05422a42c0070805645c40c1c251001c02c2c1d00650044299001e21400103018020855100701e6020040d200d001c00f82e078020000040d45140c03e0340141c00028001d5280c40c003005401c00494550a8130440518210340c14900e8502036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374433075 1250 374431825 374431829
    0x50124060e04020a09050f010908011814070608041b0b040f08010506030c031c1110051e090d0305040201052b060b030906060f011e02011509090201080610031d060906090601030c 78
    0x1c00c0042160118988e80203914403401484048004c2c000b20f10400a10042802070744000d540d28822942c0102c90850b001c070751a400d442c07050b156510301e61100d0321250b04105449a0b5805e41104400380410700300360b054003401c02085102503401e0342508040c1d15509692026204034060307400314449401b140d40114007107958400c10720000c0b9402204c041d00b1580114040300e640c01900030392641c003098103415000350b446070240d1540141d00000b401b0803140a460118dd16207980e0700540740200029100790031140c1c10900514141d4100f0228100f000c016400c1c028900c66600d00d140c07000207804d45580102c100030b041c0700310481d0443c900004c0e41d03030301ca000040105214401041020015038007a882c001444002d0801500c1d500c094244007034000d04600c080c0211382816030000142880160085642a61303040c1d40d10704c016210202070006c091148140301041c9a100c40c01b0151702c4946200320345801010500510141c1440160142001d4000c0c150a1245c0c001d6001480450034800074042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374434325 1250 374433075 374433079
    0x5040c0c0f0b1e041104060519060f050408030a0309151e05070921030201110306100305102d05010c0c030311030d0609050912130b07050124060e04020a0905 69
    0x1c42583c0704a01e61410300c83c0b00481106a4849005101c00d1100040e900c03212024142c0c3c040101d01d40392401c0120350304002c4101083c51907031407001d01c81107100305002c0f5070601190600074107081e180e0400d94207540061243d44000ba989880040500c46840a41c1c00b0540e161030041200509840b01410300e800603840c03000c10580c1312130108410070b01c640c59440080840c3c40040441d006c101900d0b10302210b10803800d400540c2403070381c410703455544002160b001320001400c0d4018484400f0081d000741800812000844c800c001d0001a0040d070881c01480710042180d0b0809040d00b01d48850990382c0d10798004904000c50a0070000000701070401c5402174030707054105085114907071014a0714520444110400d400e040101c009040342c080d41115000328809802d54500352004401d4415501410048260f00ca001e003130f0410181d4042e0004000c82401400007154510350300241c214507c4410381001040b9540301c508101142e88030001c203000b00800c9800f907151030380402d0014000001401040c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374435575 1250 374434325 374434343
    0x90109090e0c0607020f040518060109060509130204110409060f0905040503040b180d0c0501120e030a0e01020a0209041109070e010c03030f0905070905010602100204050d0314071b05040c0c0f 84
    0x1425903a81b42d80c1c03203031078580060052250340703446008a4500194954a24200c3c4140c1001081e1044175010781c81c10350b1b001420480241d0783d036401c5035440c80c083c0710060b83c00c140d48100040c500d039800c01c01000540704001003c500e0604d0410b0f40405400694031aa118620700000d01000903004070032942142e0b02d41c55a40d44038105010001c0d02084c1c02c0380001e80c80f0120303103e03280c1000b02ea404c1c10021034100b41c80784c0c803440340d6003090300b02517400900600c0c0d215041000094019809135551505d6a401071040790101c101e07903800302c0c4040c0c505503800d48044143c13004181280c5401440c0540c0180d07180340060128900c50006044c0f210a40e00040500d0b407034100f00041603249500c080901504001142c640340c0e1350350f0880340144005e014183c0140980c602c9800c13404e0a41c0211401c0390406444449140c1d42614102c600010069291030b66201c01c0085d43c1c00305040003c4011920340040d41402240c2c5014204011541c40d80d06440c140101c0080c4440401c02c000d0031010050740281e122 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374436825 1250 374435575 374435587
    0xe04060b030105310b01030e0109030903140309150705060702120d0209150a031505060c0307140f061006021005070f140409021305040f1b030b010203040504060803090109090e0c06 79
    0x810551800341c05545080190601807407000d00b6500588140f2000387c9040286801c0a40c00e5401d0343c2d6030343c030040d0110315411401c20008003020900d840c007021000c180c90800c0c0580e00080e002585401c4000c0c0044004200d480a0040901965800400b03500003402242161790120307525001c2d508400001079408a282412500d88000822503c515500e200b903a03040e0501025009042d0a00d010540240c1c1200104042c2040001c0716000c00c2c400d8019420807000e41e40d02d00081c000c0440e94589c600550040d5a0454010040035000b2855442404112810440000e18003030500f407a405544d030500051000340303a00700001c48221038062500b03843c5e101c004000110a0300c40e641c840c201d07a620018002041c1120002c00d0b0080e548112070501503040301028002c00d0b9402481e845030303014071441c01403155030301a0b0711102420344180107aa0410f50390341c00160455075645c1c0805515080014076520660340200d190004d081c20400800203030042e10b0026544d00000800b041c002d100000f10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374438075 1250 374436825 374436859
    0xe0c04062402010b10030207050706050f0d11070804080703030e0f090106031a060d150b090108060603100f1824052205161707080408071e080a0e04060b030105 70
    0x4000091300001c0e041302c0310031080c0040240254490401aa4075005804020448034811000c8a80104051103564103056410581c00010f050340e41c0b028940c1b20007042a0000540c90301c0184c402490481c001d00030f4186036081c054285004130340c05500c50038001416200c80e964109121341594410301c4c00142c1c00c00c03034800c2c0340d80c58412064160b921040c04145800241c0c2241c015482514850000c04000c0e40e40709032901442c002c80c0000b50101d440b40e8002807550403c0005160300c103c070442d90403c842e41d11142c0f08041c105940041034515103096060007445564011040030b003182c0681c0d0407030301050744aa034013912150702800c0d109440d55481c1c0950000c241c025446c1040c50720b4002c00c80c1d820107006020484102e0240940411190f40300d5002e020300d0108100d100709a940c035107101030358995455010715480360800701c0b030505a100b00384506c0c444031004000302c64401c0081c030703954650005001d4810058105402d1003131b41002801c1c40000c2c1c03203070283c2c2d04560342613980075645024410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374439325 1250 374438075 374438081
    0xd03060b07171204050c03070e0123030a14150c0c060f0c131e0e010b041e150e19051309030504080f0303040210030507020d0e0102031c0e0c0406240201 67
    0x140e045000d07003d0780c10b020602001142c1c1041d098012022100c040c1e0b07840e01e4074142590244078540d10705c09580c2100c0707501d01f084078081d1545100241542c00282c01d03540c40403110a03071603408400703c1d440b04040c2001118010900341e00b081d02c0e0301c010360800c2c02c550f42c03540d0307522030041c028040e0f09111000b041d00034401d102030341c1c2800714540c92280201e84038111815900f800d1500928580074684000818403400c103a258160b60f822103031035140c80c3c204030442e42040841210a803031401c50385000120034150f42c100580034010380d59191515405c0d0130821640f500000406000ba2a4440d81040183c1c8d641c000d04c1016a030000001c100c0ca0010309003034469018035070020905000f40d0781c5080c103a180110040d44a50300c02c13a01d0041048210008500700e401c2202c0c090056403124403801c25044c0203844a141c500c0c01403040b172b8035080082804c0e208035040119010301c3d00340c80d040c011000e20418480310500080a5804001d0315151401150703006485070707000c0c9489440c04a0742c0e030500340300390 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374440575 1250 374439325 374439337
    0x1b050a05310609050f010b0306011b0507050607081c020a020a030c020f040c110f031e0d06170307050106080a0506040311010e0604111354050d03060b0717 68
    0x744041022036a900501e03800341100f20341082e00c500c2c0500000c64090701c0135040d6801054103a583e00c0c0c0c80c0f88158003140c0c0b80700c08110156040e11841100140d030359151401084500e216091160b140c516032128100c0084c104800811880c0c0184195420245c1c002508410700f85c2600e0400d01c002c81c3c6001040140d201d0b00361140d000741c03c002600b64042d420081500c04000e2140031691801d1044003040c0e1a40180c09070402110f105070100300000c040701b80980520b0300341d1000003528945c0c81d20808902007114940104540000c9111401d01c5002e01c039020003010f4001c0603020784417054be113460701d400300140001c00b40200d1411030540e9040951000e001e41c2003142c222550790500f8200f650060381500a010701c6407160b180701d8580d1035014064003512218403c501605404c07601d0228907801078203828401a40c2a91184000c01407203541c5c4081007454991400410845a04001c1d051050510701a010b16042607c100040301ca0720044610068208800100480b195100e842040c4611 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374441825 1250 374440575 374440669
    0xe01030603060e06190e060109090317040327080607081b07032c030718090203060f0108011b020a02130e0a0311010c030e1b0109050307031b050a05 65
    0x3c0010b00303080303000008480f801101c0303a0f5070403050040420000c900391034070301c9103c40f6150054801002021580c0e00040d152a101c0e0415219001c07a500b2807098220081b02c00343d0005410030012042c01ca08100c0e1840c0a080320501c401d101410310845640e02e40015084104214065000030030220951380480c0100c0c0c140015940c0e50420742c00c000349030000c00126010121103c000070f80c840a46165102010381d0054040c001242c6445104071080309008141d100c0561200740240c01a9802d024042c8940d4170000c0d1441954100300d207283c215004640320304800401082031400a81d0005081c1003020f50491b40100d00c4a10556000c028001c00d994603203591107880059810540c02c08501d14212403002d000b0000001040000c034182c0c0c200b203a01c20000d03084407800114551445400d41000c9406040c04142c0980c1e58010078504441540305075101c010f8880749414680740702c2c0d1408002c090031640c00d0555800c25000a510010101c488072006806801c2540032a03900c4401418030000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374443075 1250 374441825 374441831
    0x714190c080601050f130b01030f0204180e0d0219210201020d0b010e060702061e0a021f0c0e190b0a090612200d0609090602040302040b0d030f0e0103060306 69
    0x1031428004058580c0a0111280250800421a41841031710168158001000d80c4a29014820b01383d004100700c0d001c41d410543c07224141c0f041d0b868103000a01c020406100b0344010000f0021141c011100711242426090f00040480e0324aa030740000d90b00d1282080705a01c1c0c0c1900001e140000802d4031100d101800240110100034801c0c0e0103502801d440030520600788040c0703900400441321014038401480d80320905210300300c050304144001c4c09281e000c94200d005001c01c0318090020075084a002e650040c1e02800d00041040118200b100603880c42e02024025a18942c20203000d00981d0016140110402c0f150020030500d00c40c1e840d0020204014200d81d6000781980c01004440305004410116004065100b000f00c9148505050b8250100510307140c0242e0341e122032066800129506422078683d00c3c0404c0b0801c581c0300b01d03140c072403149000581c0d86281d4410310003034651400381580b00300c0c032040300e440c04640c00101d008400d001a1511000ca2008400142c004010941000d09941c0ca = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374444325 1250 374443075 374443123
    0x3060509270f06070c021906020607051e12070908010b06030c07030c140f07080f1b0102030c06010b07110315060108270f070803270a0e0f060a09110714 67
    0x10304205d164000500959100164012104001156040510450005900c294009440716100740040c000c42805c400f106148109000c0508150b500a500c265440409807010f200c0000c1c3c111982c1c1e0000e1021000a05c454034406001400701d0000400516803210300080c0242010700c104500d500a541c00001c00d240e9541e903403030865480186280c0601329200b084004103103000006070b417504042181000b00b203074820340c0324001303101030703281380950705500c070501814030688070602c8040e0191196801d5240c032050310303040100c0403050003044036000350802c00113064041c1c038103044c181d8031010a00700901d554459403c90344c40c105118486042c3c483c80f81c0850000140045040c11000f0a00d10464001c0384c1c9440000ba12485911011b2000202d201108070b128010802101c60561000709190321036665141c02c000b03507001c116540384034032920301d080012a2405800360707070151071401410000110800390761220340c4100d8a003d1300c001680c8428401200003005200508603400ca90040117071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374445575 1250 374444325 374444327
    0x30a0b130807060f050f060a050f12012018090c16050712030206090114010509011a0d0501080d1103090112020d091b090b0306040222060305160603060509270f0607 72
    0x3c2020707200540c010f900318007c01d0300d80c40c10821036001c0e90001800c03520640703028006c000c020707919401006469529032070200f1000011080900300a54880a10f9940301e04500000047c09461703400148200500310034854044008010381c1c0401011109a810303064003030504910b0848141e11100320720304500045400c0503408503000e40504103d000370310001c402205141c2601c0300034001d803034001c0c2603140104102e08602c245050784440d00500d0030303c0d04a1020541080e500709800c800020ba2080e00320400c0554844010a02c01c010000607509209894000910301c03408a80c03010b4a140e000300d88480b2807070069004854466000900c1c11030700c14100b08a44500c0424811086040e02c4c03c02d0808643c180421782c01e01c02e50340108022402e8181540c52684162404032030001c150ba920404800500c082001d102450f0070b400b030f580291441c04500809440340c0d0b81040d4024020007081c01a20540007540b00700c3c000e0601400350700d2030f0840284502d00900420011050300c54642401442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374446825 1250 374445575 374445581
    0x9050706030c11070b0304080706230f07031401051203041d0117190201080a180b100506041d2215060b0703270302030102031005040b030a0b130807060f 67
    0x107002d50361200c40045000640c080d454078018414007544150810016002030405002004490310900300050302a03040ca400020020802f481c0c1621b250b0150305102c0d000002d004021341c426400d02d010b100805030740010120204061103424002d050320350403d80314240500c1600d0180510555140c8410080b10b0032940da80303020f106041c81140144451000540c0104405e0050b032850803c203034545240d940119503030b80000f41490400c42d900d407204180070340e8042208005501404000c11a800c2c401c1c4044551205540150311400c1c0402c010230450380d50020001003889403011103505130303841c02c1c142c2c1603191130811f010300006848041d01d01000301c603000b00c1200428a2030200481c5498800224030380c4240100940400c1403101e540241c4084c0d41c00c080103001f10002c80a40759603995001c20b003640c1043d99480c40031568100c041c8054101846155881c090840043c040c90b40c1d0750b141d0b85200200a40005510780100d02c0303200501c0102402c54581c3e9500c05010420140c00404000003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374448075 1250 374446825 374446841
    0x50f012c0f06270f0301020a0c0203160807170309030a0510111c0c020c030d0206090d0203030f010b0a050720101e120b04180c062f010905070603 64
    0x4507101d4249001014242034042e10b460846845528040c03409031240300c070741c0409290300345074041e030741d091805019102030002c3c1c00398600b9030701d46040310766141c4105803c0460b4040b80c5014004002d204101401b00040d5a00c11600503c2c0c5140040c40030345a010300b58440d84c0e01c07087c3c043c0b0a0060000030440c001030005c4c0e502141140401074840035004400b9144103681c0c0100c06110f0a13640b21103900c98a0b40700300072542c05030040300e1442e400080428201100b00000c400540c000750100000030806011044c00b001a52020710310354078040964007611901809900701d00351003c03415041083c060421190042d410003180e500c0304c1d070301d04181d820020742003003114060b0a0708010404424015107840d4944e0310505000e4800600c0c2640844110510803841c0d0842500d500340b244154595100380700c44004418241d210460700c900300500140075951140d410400e08680031000b8418004000300001400795441e0501c003007030030300039024005000d0040e000e4041c0c2ca00014429030154002c0d40c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374449325 1250 374448075 374448079
    0x51e04080a020f010524122401170a08070309081905011407020714040617031218060103020d0f050607030b01030606050f041418010801050105150310050f012c 70
    0x520200c10f0942e9098407426111101c8500c4510340004c00344144046440082001130502c40e00740c90045d060915158401c80050050400400c40781d51510fa0010b801740504800e01c0c0582c81424011045035580e0080d25000d018000003151500404d80b003007040da0014089041110f140200c15200208000c407000c10484040d0f28040302e03848038201c000c81441c460b91450300504150341c507050305119150344042e0000d80c0203030344100c0403c050011000d10800c0140c004000c544031405581c1c403000540c00500411010f0980f00c4998142071400652281901c2c0d060f10b0810091400e8038143e030380c9440c20070004003e030080c201017260866259020018030f40090f44d0900403541d9070042650389200341d25191201c004100801d00c103104c3c49020042c0c03402c201030700a01da14000341c019400039010a030008480d503516200100603031300d421441c0301e8040c0418000fa500d1400c040c0301c001c05c52040c0e84203950045060400004117070f8014501806075440d498650440d090ba161664a40c501910a81c28 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374450575 1250 374449325 374449333
    0xc070b0307122930010603030f1b0206070807060504110a0b0c0a080307020307020a0806011505040b0a0e0f060711030607090605030a0b0604090e031e030601050a03051e04080a02 78
    0x31461450f1146070001c0300070b040208a00310b80e5901e00740030400311a444159141e400b144d00d500320010403c01c2d51403102041e0800000c03040d04501d00204900300501c44d00003007000030301c982d014040c0220f008004181d03046410999401151074111101c4c01103440c00f416080c40c01e003c11007032140c000007401c0d000b64101c4500707080d681c03900d8500400340075103c040102a48040c0036880003903601d2000b0340d0032a020340101c90804d9a690b0000e00d8500c116003141e68160841c900400400c0c881c414400401081410400d0401d1b0501521040c20f01481031120100302c0030200000040d15003500103080b50001034202c0381d84a00c1c5090003520300d00340c0019540244180b000207101903125080c01d0040c1c0d0881d984041c51034440003940c002401c45542c0c1154004420040041c0ac0c042a1082a001c0d0b40207074003854407844404480c0400924400c00c0c0c1d40c01c1e071310420401120360303403100844007401080c1c100020039031240ba14000411052070021095010b0383c10512007032100c220007502c0042900d500721 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374451825 1250 374450575 374450591
    0xc02090109201801051b06010b0c010b0105071127090a201c1103010c030606020c030703020a091e060308040302030f07030308040f02031f051503010603050d050c070b030712 76
    0x2542e82c2d01c90b819580d00f006000801ea0702682d03114a0061440c2c882034480700700840c4503000c0c10b40c1400380c20381c4017144000001070803191591013030142e0100f4800908043d400d001954642c4061190404c203a91b20945c040016003031401002840c04661001d0407400307410b18038203511385682c1c1d4102142d0079102000a03007041445201c1c5807094520a48010345200480c0368440395404200c2840c03417040342c0c070748450021a102900e00340f042c0046040640c1d40443c11a02d4544081d0400c18101401e0f400703604222018009030301c4d02a8142d040791b0442c000000c4201c0d0303000c0380f2148171882d1214103505504050340007081c000500c1c0a0811740740200d0998808044009a03556101c146110080101c0c042900050200d240c183ca01c200190001c0c0039180907010342d0300d03400c1c0c09070b021801403040b035a43c03170f01400300c24a00f40d04501703103030b890660017001401d003192280b0b650341d0190f44054042020028482000c50b10901540703008101c1050920385070700f00985d01811010101740c001c44e02c20701e81800c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374453075 1250 374451825 374451881
    0x403030e07091a1c050105160e030604031706010203090a080309150c0a03031e0f050414031c050919030507020f0607020f01030e010e0706050706050705090a0909030c02090109 77
    0x41d00704080040c42000383d005030a4084c0800141c64850800100c001c0700c44590100e0402e028051040c411160912107441702440003030301003165500028020707030000040100083d000018042e60032a507490032203031651080c1c0101d1440c410f01c1e800b66000315400c0c200084580b0300002518031200212140c204070780e41c9040040d03103801503205910307203a4005990034000c00e0107544142c1d05090712902c0c41c080c240441640d80c1c10b80e540080300303031800759441e410401030103010400c5440c403035401e101652804007554241180d05000c03105111791180da40380802c2c903400081121054075507624550040030407003410094050303080500160702508642c180040b040c501801260f111a90050041c054030132007400440040c00c56681c500220340d61401d07903420054042100e04001d0103a5652140e90301c00d00d04e050010707180c0103420703a03003030190900c0b030640c007652240b88010640e0001c2c080001c0807402d50804840d4503e0301d06002e50030105840020403a4480e0741c00000388610817035a414105190350351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374454325 1250 374453075 374453081
    0x130e06150f0a26060403050a1d0405040b0f0603030c0c010e120a03020303090607030603201207140418020d080703020123010620030a1b05190201020f0c010203090918060403030e0709 80
    0x5d801030000b6802c0069194040c0512292402c62044d00303180f00d00407000c0c030007040c00c840081d5415501b640b2030300d00300030340482020f03105640008250065070804140e2010250386281c0500b81905002c10300001041c0c1c0c0c0c4580c1c0000001d200150704545e40c12000b824080c0d12079100381c4180c0d0240c01103000081e0024024014401140da0201c00030410640460b00b9040900681115551102c140040050883c0c030400544001e840c203150780034110059007080004440e081000910400709900700381001d607039a0341c021958a9041043d40c3d598544034a01240107013140284e2143d50316444d40211100c0f0966110310303041ea080350701d4031291071548103248100f451841610b0a582e85c410000507840c548140702c2c08a140800e9508040980190340d1290304142c58000043d105803040d00c009010b5690402c0b82881903a40c0c4409061030204140000b0340728800c03151500d00800356a00800d40c00224850611613403408030341500e80c54103003498003d003e4170b224403440096100300000801c12415500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374455575 1250 374454325 374454331
    0x1602090726070e030a030f02010606030908030a090f0c031a0916060e03120403060c080c0c0c0f06070f030903020a1a0301051003061a09130e06150f0a2606 68
    0x71031803a03001c1c80c100740065041d03001081c210802050080c444401d4a0811000c213000b03200c0c0d00c6030800704002c0d8031b00070308455466100c08105402c000740e40d40440c000030100da4015101c80008646130f50581048003064031803240040c41b074400180c0c00010b100741c0440003111150b08140f550a0f540b94540f1181e60744102c1000e03039501ca002a0380402c03145010300b901515100c00502590034481c2c0c100b00500e42c2d034005900940d0b6194030303400e03048020340d8403c1c026541304190000032410300d134031035914130744d1036a071444154040c007115200054513513260005c1e0350f180d42c0e04c0f00549001082c94540104009411310049019001c00da402040300e6950201601282866484c00c030300f1030b8070b03040c200804e55111101607020b042d540d480100c3c44502c0d00c0200141880c050b04461340c0d400038407091101003103284180020380e52406000906108022404e0b07500462100e2b12030f840001100b0000303409ca0510f1803000e51104a491001614100c80d10401c241003030341c20344d01201054007001d0203841d54401c0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374456825 1250 374455575 374455607
    0x3051506010806090f060109080d05030a0f020c1203100e280606020a0305030429042f010309050c03100c0207051e0108071101050406020c1015090b0303070816020907 73
    0x100002030141c417a40d44226512a9052507c1c0030040c0d601c4c10f4550500064a0403040045d50000810101000600440060b064800c4045161409052420391110703010707070307080c1041c640000c049804030110b45210b2000d42844100c1c41c4460400303414041214011010300c45a80814640c1551542c034280300d150111080c507006814104001d540c00c5509034402001191040014442c0040c2020512036075030316940e031841049082e05050401002c078140074481c400040507205c0480b00200780380d445a40180c032007800d001c11092114904182405c000201543d018883d51800180700e104a0304800034504090b02a6044e0759215000e0001c041e40807442c90329170050118401e0300c00d52241110742d50000c80c61400100d121610070a450035100c041d64242c413465008103000001100c01e10866500c0b184900302080007100300c1d01e900f00031000610460300030545e0703848000803e843c1401105c01f440d41c080010b0b9a10161115030895024401e401603020703800c810f0004602034001c0039446038034201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374458075 1250 374456825 374456839
    0x3060301140c1e0d0501081f020403080405131b030609110705210c070803072901090c05070c120c0e1302090a0603020d05060108100b0114030a060e0103051506010806 73
    0x2d540c82000d250380c40840102a945404c00803045440880d10926010300003000c05440f041c00c0240c004207007040a0001030030b816104000810002c1c5482041718119038065565404006288600d007006116109503403c058a4800c9000304c03142d41507002505903400d0312000c015032003564281c0303209030240388401407899208018007003401800c503096035105d40520b140c0360b190103109250b0038203000103980110401e070f001084190810034240001d45051480783d070116501c11141e41421010307035041c1b0807036140c1951040501c00151146040b2600b007500b100302c14182c266100701d400c2428840070030541c0d039041032080c0450b0202e90101034900400c1016840c0c0107024464080085810006d09109501956090000016290b40b0721a8903600d0080c0c1c080e100075850a40b019007440111070980da81e480c906201e40d8000e80e00000301800c1d0f011990704460f201e90754641d03080014040764104581402524000204016000910f000d6248011503002030f59150040151041e0105603002948021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374459325 1250 374458075 374458087
    0x12020f0708030406060503070b070312050624040f0f03020f0102010c17060310050f0601090806160305150607051b03060f04061a060a0507020a050d08190903021503060301140c 77
    0x100d600003440d0401d008402c0010046c4d0744400083c50b0552a510102c50194045010024160032409800c0418680c0303a0070320491a00b6400502014154940b40400391140782040441603420700c161f502901c1d243d858110120384440c00c01014a14a2204078807030b03078980501c0c55003540b0601541290105c251503007031014611110141080000400350382e0140304400948111340828003c0074002c52340c032561000315040c01000101f240346a5000000c032603100342c0a001040141c800001c40d0f101540c80d0000d001d480d500c03518003683d100402607a51240c1c0204a42c03091050204170782e24171249104002c110301c014030081c55101d0000711000102c1500324800100032501c0e03500300c034214510030314000c43d4140c9003000003062a0403140d88500021400701e10340086003800c5c1c00b448003500c811280c01101c0c400a55481181d44690008200628005490000400e00400f4400c0146500600c202004800f411354100c85410403a400c40c8250308103070101c1d41e031600c50482c540c004c0e9803068036245007032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 374460431 1106 374459325 374459333
    0x90b0a06030206180a0f03052a0303040501050a030e010c11010e060402031c0c0804080d031802030703020f0f090901060e060114030621010504050d12020f07 69
    0x3480c0c000e0500150b038428007680c180d032080e501810f551140040100c0c0303241019600c410b0084600039804800c00401180b001c43e10310440000128402c0164080c1c840514040660768058100300310a20040d445000200501140c40c00c1c0400c3c81d0142c1c80280e403c55a5842c0400000b68848411840c1e2620038001c80f0003094004004124038200740e00003d07201e5508400440d455051860543d0186016030984c030701840e08102c40d01d07180d0799079001e00d0b41c48402e10130b10303500001c0c6090507440d05034081000c500165a000380c020405103086078207000c95240078020b44d65114013601968175039030f0b9403603d0440c40b4085800020600903d06619a40100d2025040314180401800c80f007030902201c1c81a41d5002504480c00c1c0900d500b0044802c4a03d071840d00b4807015542040208010301c4400601c510b6161240ea880c020001e04a422442c102c5c007034030520810084040150101103 = true := by decide +kernel

theorem cover : BRFrame.Cov 374280575 374460431 := by
  have h0 := BRFrame.cov_init 374280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 374280575 ≤ n) (h2 : n < 374460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
