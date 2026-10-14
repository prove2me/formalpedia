-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0945
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:20:02.222936+00:00
-- url     : https://prove2.me/submissions/d3b7d863-3261-49d5-a056-f23f2342ff01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169784172 ≤ n < 169964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169785422 1250 169784172 169784189
    0x50d0908010e0307030203160f08030106120f05010612150801050c04080d0e181503060709060216120803180709020d050c1207120e010501122604060f0c080a09 70
    0x9400d940b440b400100711119160981d0142d81045001c100102000300407a0064a10503e55031040d8041035402c4004c60080c42140c981c1e030f2082080030b1a2000b542c142550190f2510f28140041011035048180c2e100d07900e8540d81c0001c0c0c1c401c411150401e43c0602034009021541c40c04042100c409520720013003041e20950030032608054400780c0c04032015440c03240641d810800d005401d0356014440b032402900f260503a0041d12182c0700590110389446800c482c580002415604204a02d43c2c05010b04030301910000481606241480424140c02900c110024080100000021222604070b04e43c0182584041d0980e142d09a41c0d00303100c0c0194001e181c000400d5880c00c00454841d0804004680d070101410005112035541c0c2d40c4207903801d02c240d820441c003440d01e900d441940d01c813007031180c0360103461105005000d050045c1096144103940000080064900c40c558148407500340007503400b1100d180c07038220302c0c04082c404101d992001c000c000514080b40420940c40054000400409662440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169786672 1250 169785422 169785431
    0xd0b062707170c1602010905040903080a05010b0403080909040f0209040305281d1507050a0b01090b0d1b0b0301080d08070212220b0a080910090c050d020d050d090801 73
    0x742c0008007110300990b100e508803201040080c00400d010340c000d1138918014184948019a2940480c065440300c10040b00003980036010410b0061a51007039901400d00c090741e2030704113425990303202c02c80e06c94032100500c5840640000340030440c803542c01216069000c0c00300310160400340303130162403a0454020421030b03894a02500102000400d400d2001e101a90b035006111622440ca03003031000c0c140c0403101d4000b24501c600b05100042b0038004d003070b000c2c4038400078612116541844449801d040e0040c9074078604294145003195581c40d80b220400b07800c140401c12545008404200300346180c0d000c910440d40200000070381c0200440d60305840d0450b07032a184410798661a0132a00d410850031744407581d4030305001c0124140c0356800317070044900e117080d903502c80c15842e040d0216507900302c1c42c41480021103130070401411190500140c40450002c1009000b0706080399142c04211030740d8000e042c0105800741c2c0b08000d42d541c2c1c4910f521701c1904641a680c00414844004040004501410310300b9801c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169787922 1250 169786672 169786697
    0x3120a0801120804051215100302040609140c0c0307170406030b0102060603071503060302031b01020d031a010503090327030c010908120a02031b0303040b13020d0b062707 75
    0x4070b0341095001d98400070b0180360904010030802c1341c4400d40b030584641d100e10604a6070000c0d49850142c099104009003070b110034503603c1000300380c4140342c001059035401c0903281000c16a59045a9400000354108543c64148400c0c03034a01d0b600445d880900340300051030b000980c9035600e4000300199030b00e59030184002c42502c001640e66290690b00180c050744030403020003403000743c0c80d1020034038041e601d0089030556981e00003c0c940f640c400f03000b40d02d040c00350b040c9104540e01040701050391460f5040501c03070300144081d01641c0c01c440e403409605010000000500502003070086070400c17010380c0c079240340412980040d2a00040c00d5800b1a00a2061980301e090030742c0522551012074000c08000c0140c026242a2070403160080c2200b0000e500c410300658601c245134050f04258a04480700450301c9160504001103c050050a40208000041880c0c0c025842d200752160010360440c0d5469443d0700c84d4004201d4900b21000c407074800548200c0f01c200001d01700c210482c000c17961a5562a040101c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169789172 1250 169787922 169787939
    0x3040f170c0a060b0102210a23040302100909020d0e0105090307020a050d0c0e1f09060b03070c150606080415021617040306050a05180c011d03010b03120a0801 70
    0x4100001899a102000da0760016040350804c0e68060018410b545a40c01d51a0240b656088003000419520001042010981303500510741d01606144803403040c028840d05407010410722a600002e8011203804058180c81c03401281c088004000c15401155030707400740840e0800034030102c4607090255090001150708400000196010b040d0001c0540ca541440c143c10842c082588032000c0744c80e070024107000074922820000103485070340028018250a403a8030445951226103400407800d813450140280301551001c010350fa4050642d0030264140b00d1035041c826084140b028090b20b400d403c2c410080b52160b0f00689a0f03000d248950840c11484007581d0b1841d06034003500710f5924a1002031040040480c0b03803a004c01e13042c003012030116407802c0c0d142c1d00c500f0180d90040b1180751510341c590050180d409400d13483d011b03c10044101522881d4501d50008150f0b512038050500900c07403220041600e950203600030040e01c0d0f0028200d0310846003107185507080b50000304058002c0f0b442940001900d08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169790422 1250 169789172 169789177
    0x2210a03060f090903171e04050a020d081308030301061403072d020114011505030c0c070e0612010e0346080a0207020f041e090b2d01150507060203040f17 68
    0x107047e00c0d03411030721201d80302014404210040040d2044d220380403071400541c80f02c041034000140904040c0e0b0762080c0c1c09011702c000c2c00903036010540c00d030f0040004020480e840482850034031513241b030041d174a85920b24119142a005100401c44140000300ca482c08198001c01d0702c1d1003945a0024407248000d074040091a450920507000040084042103460500ca0030040d81e02c40c0a802640d41486110344101e4545201c1c1d41080c5030140c894810320020f85440f1079460304a502c0480240451002942516240d004040c4551424590385850841c20400c211030540014100c024a07900031036843d034030000b01d015036800b0001149410000c00c007500c1c0303039000f10fa40054000e02a038103010320715401d000040c00301e185144807c81012282c2c00300000d15000d4144080d019201d01520381c02c0031018030355022000341540c4a40009040e5803154404143c0080341103034843c48c0140103a460301c1c00c003030341d140c0309864000345642d100104000802421262948949024501410302055451001ca0302031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169791672 1250 169790422 169790431
    0x70c2f010809121614030304061802030d0f050f0d0501050a0602151f0321080601020723030114070306030c05060702030c04050c0412060509010c02210a03060f09090317 74
    0x3604841020005900040c004000d00c1844840c0024a141551075845c04d964080c0882189030300008207010512903070303015141c04401c01090410308000c0c17950020380e50340c6480001c4403d105120208a07200ca005100355001560a007800b550f560300600c194100900c02401010b101e2804910041240d030b10000703001c0c64080060102d02519200c0380e8001038500c5090340b428a00d968881000b00005180810110900410140a060195040f4406050501e00a0006046620840d070421510b40480461803604627691803018911000c0400303e40500010302055100d4040c3c80144205154941c4c0800e080300e000c0c0d00081082c985600412846101d081806541070b403000808203002d160039482141c02040d1001024074084d590742d43c0080d03480c800341081e610b995030740e41007064880702070003107441303500c0d591014041c280400c8680c400010074403011609800c0e400716158100a020340c0c4004068030b41101c45010040d074640d039035409014034007400c4000481c001074603880305001c032407000d014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169792922 1250 169791672 169791691
    0x15020304060327050a02040501091e11070203010912020706021204180f0f0b0109120b0c030a060f12030f020c091911070804030219030503070b070c2f0108 68
    0x100340c9041c00403400340c54800c0c10403011014003091148240d00954065003124804ca02404109415004010407100d050b171102035002d04003000040b01d00c0d210f004e190440251008001002003100710500258041c504000703405610b006045001d12060720184416100750360300312246076844d10401c81c2c85404285020805200500061080076151114174600001c034260000e8500c141000400a49010640400d122a074940e086146941d200c0e007420301900c110f04130345081c6412686d03001c840314401002c810400308040086440301a954210304024245a41c9198030303131303440d07904803840ea0ba8912001c4000c521508007100100e0f001180007143c902004004402c9a610110814003036400d44e1032481c0b9580e51000383d640d90a009902402c0410300492582d91940d041d0300c1806030900000300d14203204c40340003200300005140001100c0c1265842684481692286007041d40c024000c0c4030018040004124001e07000590070307181d034440c02080004440800c10400040d0784803041628402039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169794172 1250 169792922 169792927
    0x3051e03090111190602030a0b01110c040b0d06020307020d0e03010b150d2301090c0206040c0909020604090f05150103091a0408090603040305040806060402041214010f0903080f01150203 82
    0x55560155101e806203c20758403d0718168070030b1119000b100b02c081001110481c1d80031082c0314080290388101d422450007030818045502a5189440e610302c480035a0a04c07490302c0c0d000d6440941c8401c5a07610400d54026819912402c12244c042d44643d170710146500000c540c4d52072641513250500131508200c0740038200c1000100e03800342c0d071082c6522910500c80f20585030140111081c030208540b0103d1074080c01041003a50428050b4425604810700300d8045501040c1440049511011010216210307848001a186200c1c17010500758000d5501200d240c0d4a00710310414441c441da00100d11400b00341880f5100d0340b00d80e400540031512445800b60024a015140312840c001810026811078064152107007041801400541194402c6504800040c00410200481c000412140d03800039021181982040c2c200829803190814116010b4220703c90408038a80482d000e43c486107014481c0340040c003006d64541005010604182d407840c3e44844400300010b00c2078000c0c201c090320030314254051407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169795422 1250 169794172 169794187
    0x706120506040209061605280b0105030706050d180c06051c050717180111070c080105130219091508060f0601020d050a020c0a0e010905060d05030a231303051e03 71
    0x80c0b4408841111f003407182c00b90305071000c80030f8000c4400403901543d200601c81705a28003140b2a01d8103074000c0703010b98003500092040a810009549880008035800500d00305d0200714412882d5811001a1002908000c0801d196922030004c01d160482200f40c52031640d0f900383d128003100d030103c5004000400c42003011520b408001d0203160807094640c0c408595410340301282d0300b100d11009140150b03140020300f040801071001075060042260f14000c0105140410b607460320a135040b00003d22808100b01c00c2e015001d0301e244480c0c003420020348100280101d000c121804900c0c0c60040c03911038829000003c1d04080441c040c1c0d0b1003402c040c0e01914a03c2c5c2e01241c02d03a000d82090714440158000c000c680181ca132564480c0c100200304c0c1019803485545040c0c1d0400441c0d002401300740c0107030600d400f10b00200340000100c558501b03052411080c40002c0c000e50740060000b40c001110301840010710000c00c0104801190203481c05101981e10b0300d8441d0988810094103800303450b060381c0003441400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169796672 1250 169795422 169795447
    0x7020c0a05060904110c0c0310060501080f060102101409011107020a090b150304111c02010f230d0c0206060328060b090a0501231f030905070612050604020906 70
    0x7403c01d048040c0c0049103901000e00803203410307006100d50311260791082611003a00e01d403c004900c0d5290011032300300030407414040000c1c503ca074010302c41c000300d14103500402d000381d100300b051070302c3d41c542c040b000c11034040f04441640000d442551080511b40c2082007940c280200b4400f154801a802008030800034031303100d8044040c0856180d5145d000400e9111940a0860100198415842028400c0030031000301d040002e0b401200c4043e4140449000c04140140d802c5245401c02c2d801505003440000c000300d031780e00c0c076018402c2c03d0040e401001081d140502445600030300300e42e520b541c00b511010340c1c03200c003850741e00c002c0008104012a80f003440b10266402d026151503186000e008081000c0c1215800700344c075074106440700100c0c0c0d565031004004c1c2c2c2c074a003800109084885403d00c814032403003800141d480d503c01c582801d0028950314050b60300034080d034400c240042d402010744502503661640901484000101c10350403a0500001075543d20b001e100b1111081c1000301011f00b4403ca05072174 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169797922 1250 169796672 169796677
    0x105040c110a1b0906060e09040c0510020c0901140a03030302070602070605010303080f0f1e090705030f03030103050c060f0d02090f0a093207081003060c050a020607020c0a0506 78
    0x80c405000c107078162003a040d03009101c03000a40c3d010340307807250310b20360500d10b4a401414581d008000c203a18107502400701d980e001401d8240f03c6c00844a05800e500c603410445451401588100e500c91503182403140119004114050429402ca403062141e0b0f0b40d84100c4038000e0210040c455004999010520000703000713078080c01c0c80ca40607540060a00c0c2c11540c80808650302a081940400d526004020300140700c0c0021540c80fa09030080843c4604081241d01e880203003041d41c2d1542c000d0347d2000521038403420801d2030000c0030001d04403959103028240c5076480364000e010603a030a00448484010b00c0c1081c0c0112041c60725104610b510380350101104200940041c0d203401d500546c5825000e18607643c1d43ca140b00900b407880c4000406002d5100a00c044454032109441c04030b48200141d0751085503103450540c003961a04000c0c01c141e403000313158000b054040e08020009441e1500c201d103178551100281800200540032100651241c54003a0b035109034900302d00b90300158404060055091003000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169799172 1250 169797922 169797941
    0x3100903140f0f0f04082415030f0307060b1c0201140a030f05010f170109021e0303071a01060e03060f0403030b010302070203031902070e0108030a0f2c010806040c0206010504 77
    0x4080381009100d0f0f605440992050907007601000020900340a5480309001e896461500003007050326001a03a1224a61100006c0c000503070382c110311500159586003840f04000419403002030b6a074400709807422000034000c210070f86004030804800418425420044441215016111544a0320b042e242801c00f562011680408140d15000e4454078a040c0d030180398040c001103a06c140b40740c0d06081e19200409a408402c240d141c0c10010114050380b90118488004200300000c00094401c840c0428503520a0703002c0100f402c4000c600e00660a031844035924140d8110b9030764021a42e03950070805d0340d00d410544405000c02c16140224000a0003580b24100b01c070418100542442181e800090450b042140300740b07440e01040e118a070403580d050001c807025090390865049254103005003150b903409000b007004240030100c040906024003943e00d00300040300c0c803142c482812442101070420724030514031007404100108081003051400b4020590303424001d90050039603a1910f003c00002c2d00c0d042c0d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169800422 1250 169799172 169799197
    0x1f0b07110d0c0b070c2103270b0a02010603121d010c0b070c06110703030e0c01180e040827130b0d031d06070b090705030106030c03020607140106140310090314 70
    0x9070000d000d05540302c01b0300100b6401003180c000c03081107007805400c18008209a0343c011441e2000c000c80c0051003d4400b040d280e5899565031502040ea02c00d81c01010715400c058007500d0480c94101c0159404070b600d042418042e4140c540c0d10321039000640c2e80400d62000240028104800680781c103219000318020580214400301700e40c091048030400c4c90348000c0058002031f80b20340b450f80324a0000c011007089114286802d210703c041c0b20220b0301a440007070203084a010b1800d000f02e000e010b510b0003a51101c105130508040c20455510340010b06200c50700300350340980b00d100c03203a201b1182c1a100300301924401501c080300c0c83c4d000e0b650807600d00100c42020b556840c11280c01800c151600f0000d003504620a610078005402e00343c0440f0314003009079011324845e80c1071100a10008007a400d109085940c10b40340b0341d0320750a19160603200e03132040382d0645265603c0c150b00050b0212103000310040340c810030380544011140d0480401c00752a42010040c3c0460340d000180c11070a1070b040b006080640044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169801672 1250 169800422 169800443
    0x7060207050a02060a030b0918060112060f0f0c030f0c200f031614030304120509030c0d12030b090c03060d140d03050f0705120f1f0b07110d0c0b07 65
    0x60340041c2c0706810002e030090001e47c2d20b070b01d6090b450514003501c5030400d1143e2401d503d5840540c203140d541708414050b1500108a00d202d04007000441c1c0c005020060013041c0620114401c4171140000744069585070000906020030b4200f0581c107882203648036155591000c5c21356042000301803202c004042c1070340140c03150b00f1400d458407a080c0050180300b1a0132414445c181180c1c189101000003200102da102d030020010b01001641c100070340141010241032080d1070b100c2090000341072a0300c40f10343c180c001010b00d8402c000c00003140e00100b01015607440800c41d001030b80c014084080c500702c8402c80d0032901000401c460f40303415102001114410381e031013580c40090b044540e08000c1042100004617407030b20180000101d20f02800c6070b01100d5442c12074184407074108481804d00015015140c481c9020001c81c03000d82481c46034550019a18698506e90303035440581400f580d11020068442d04800f805020b502c0c1340a090b03443c881c4d900b0030820040282000c0203612250b20022084030040460b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169802922 1250 169801672 169801693
    0xa11011101110304050111280314130b10030f060509070b07060c08060f01020c0f030708010e1006060e0303181c03030b010806060c120c121902010f110706020705 71
    0x24021000110403a01e00c10b0380f68100703894020f00356500c5031005c124042c0b0610022945080034080e46440c0400786081d1502c0c081c101c0b400f6401000465042c5080f071003a00200541c03105850003c0120760b100d4280c0c0c00c12595800300e1009207130014000100b9915003030030902d02248540e008641c03c003596509882506596215040c0f082e400700c18101e031425100c80c81c108071030303800c04089603000c8019a0103050352910040001d4071031414000551041d00005240c1031651410003101c1c000e022500002c0103201c441d81040c65442c03070503040c1100b8070381c100b000200d80c5610603c0440c3d020701d0080c008500300a0800b1007909009940c100250b00600100c00040a002a081078403445c10701940340021400640d0000500c45400207159a0046604000c001441000000c42502d2520b80d208180c0d200c1c10b04040e024205030b810b0200c04280c11010031141d44140851510300c40304161768008110b49554820400c0603103404c0104400b42c04814010000072403d190003c15000d44603409842a41c4075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169804172 1250 169802922 169802957
    0x181a0a03050f06090c060904090f17070c050a05061209010915050103031b150216050312062701060804060b040e03030105011b0807141c050706050a05090a1101 70
    0x18940e00c1596154000741214464640c20720030755800c500018007404c0c0e900c140e07801080f01c9102d5822136600669540341040103111102c0018040c65501120f4022600120000407401d0f4011800c01d4920354041c640015080c035004002c88120340380984100e0070040e6108a000344410000c101d84965500c070007826001802c0c0038040d24840c2b000c0f000c0003c0d02e5055040c001c21030055a0100206007510304e1921022031088404000117180b82032002d41d41c0c0307101081c110b40e410b010980c014040d100c081502e038809142100164031520b420b444806a210b82c4140e0003d60050700032441080c86110300050004e64410392410358094041c99011505513110004107084420b29001c0c1d4190303800200c010b001d01d40c1d1005134401c000d451540d081c0c1050401e078035050400e00c42d800c801002c150000a11004100041c0040090961b98245c0030b901072496031805496984981c40071921a480d20000407a240e110348607236406940c800008080c5407100d41d6440c42e80c02c18904a090510031100504c200307048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169805422 1250 169804172 169804189
    0x3071203120b0f01090b0307020307021804031106070c02150f07032109110405060a0e010e01150503010303020a0b0a020c030c03043b060a170a02011107181a 69
    0x18869030700e40807121407a88000007124000742c1c007544100c0c1c15010030281a0b0340300000ca81a44d01c91010207680b9207034654283d2031881901c60003900001002c0110313134040221003486214502a45420f5507440c603049490392900f030300312120808200580d50620143c20105100398840014080092406600c02a50b900724ac009034411400900e0501c861400210300448ac095581c00b05802488105850f07510800801d5510300250300459a03140020b890b032751009019001400c9078003042d4042c0d6103d010030b11000200340903503199800344107002d9031418402c1d41280e04803900740c1c0c06024a0005035072240701000001c2c101c1c0b031402e6028855034003070960900060003520f1080c002180c0d20380c0b070104000b0080020f040042408208054110626481c2c0072400c0100803600c00d046c0c0342c5546107800141100d103a908100c4118288800c06042c1800019201100c107000341c0b0381e1102d5401100b07032035a40f40d8140c0030b00c4240104001c0d4034120f80e20305400c400d40e0240c11241c2002002d1120000c6000c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169806672 1250 169805422 169805459
    0x1012060e0c0105030106050711130903050304050c0109030b0609040f020603131103030301140108040c0315140622020c0a0501050903070b010837051f060b0301080c0607020307 77
    0x140c0da00e030511049128104030408441e00203083c09420341d071501c030010f0503501038a0406410103e6030b00542499030b8550740040c417603112100303040000451310704008159030011901211248181c1407200700c2d96024080020449901660081407562194140400d0103030150080380c040c0041103043d401680c1d481d000d5440b80b0201c17a001d542c0c0740300302e08200028140c0310b034030746001e0303081040140200500d00e011008240c000b0309107007a01d6140d516002d0f000d411380b541b0203052000c100900d0111010141c000b412400071400071070f17480ea16404100600e02c03003d14007500d00e041382080c007080b0484544d00900b0007224103000b078800001d015200d03c1e0966100720b4032208150400109041008004030259014202001c0140240c19040c003c045603003c0172122003008240307020355214110084105001100c1e40902a542c1200d502440141d00d004501038803420b540c10800c000c07a1031080541035a048906040040c8100d0250400b4048a680b0012060340c160040850203d401010840c030281d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169807922 1250 169806672 169806683
    0xc05100905030a03180c1719201c0314090901030602030402030105130b01051507050d090f090c1b08120c090306060d0302060412020106180e060f060114031012 70
    0x64440448004040303c5c0600c1c0305d8504402c422243c6404222035140b02d406440004c14540800b0101c6440703546007110b121a040c50048109401100f0044502540e0b40d80c405641d4298104140f0b10341048000015140d11a20f241c01600001000c280705a0400c401a8030340c44041d4540300450b0003103140510246c10503140d1940010a020460909100301e070b600500d52149070000c0c084e80e541b2110b9041062007a913100303000361140707541d850f190102158049039011040310503a245244000e01401c1c4140305032190000c0b0540c000590318668000c090b07003121107658150090303144415103c81454408000c0c0d46140c011701940ca40d01005002c161700651081c805075840344070100400d440c0400040c1045e0044500f01c00c40e80009400261064005900480780340319129020340c124010540790740aa00361110792040703d40321030305a030300c410402c0d8a15015039404e0780c0c85040a0f044140c0c203031000ca0008045a2150400da4030080107590000c641d5408190390715074812049102412099003640d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169809172 1250 169807922 169807927
    0xa030c05070909020a06030b0102150702010b010806030616080a0207020303040f0f29180a1502070902040602070b070809032a0a050f042706060602100603080a0c0510090503 76
    0x40c44000c002a400410089805000c0703110154046082401c0a101e41400c0c55254460003501d07038001d02000d60925104021051103141100c0000c0c00707090684d15a9000c90149408900c1c0c41c10081641880303a00c4c00b0742d4582140060b010101d070f250f41c004141034010381d8240070640041e0780c00c0c8010300040091102203120301d0f0405454070114542a400310084200c0010300380e285001f11140c840400406e54905500c1e40c5180b07203500041618006003582c440328000010070f03800c400d040b101a94000e10380c2255485510b544030841244030346d0041c0f0000d40e01c42c4804010402191004041e494440ca128500388580306021914020500c100c00b40c000c0540350b00105a031241d23511700110500c04807241504240790a010500d01402c403507240d40529103601d419030461040c04011009241031045000103d41c0742d0510900510700d60240750018040d0101108900b0014040e180541e5000703101c0b145407100c1c207003090300c1c1c010040804446078010450000700f180d0840c40ba00310300c14028000f03540d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169810422 1250 169809172 169809197
    0x14040b0d05010f08030703020627070303030e010c02061b03040201091d0105012d050c1501030f03020705030604030519030e01230603010903080a020f0c0d030606020706090506030f15030a03 83
    0x8004499801100b07032981706211100209600045098000207078082d0000210803403946c500714050984412500c0d807040003800010107078554070030844020b100000304500300d40340c034080380c480e001513a40d40390030304148881e10f0100028800541c1c1007481410706001c0035503a03018542401481049028000380f03208010421560440171614ad0045e4440d03c21500703085000c0004d800d0040a60010104400421400c047c10410444203c50100c0c41c07072401c0d03807503a40749003c0405481d603410460060103a5400000d0a04000940314090396264072110304058a651880e001c2c8014007142004150f100e03181d409000c20284640e4411030340240c201c080c4c54001e04514820b03401d01420480c02685400e0244010035404000b45030082800300016940b81c150240f4583c09004000070000117024100f94100e02c3e6405520030b10469103c0e4096070160b603510042a90303503040c4c40c402c0030381103c8200006003045030503004090b031080c028401e84074811440030100340307804141c98044000c294204081e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169811672 1250 169810422 169810439
    0x9020a050904151a030703050601050f040510060809030d06081c1b021e091e100b0901110114090a0b10080c010f030209130b0913110114040b0d0501 65
    0x4001509060350301000034146551400d245010340c03c2154100e99030742150f202031010030001098814001400c0301c180c0f03a1242049074a551080c8a1248204144244a14281400e0003024816030b01c001c94042d02c14507100302035800000007003101c1c0090004100c0c0303080400203480b8000141003010003c102c0c005100d000519502003080041c0b09105110720140c0c04208032105000c1011b505559800c5080c8101e01942444800907100641c0b046100040202032000303d00480703903084000c10807000a031250b07031044e000c140c0d0b14041e400c24001c00300308449a65008a10f500d000c2107a0100014100d844c10014140c0c03803000350b5480015811080060040c004403100700740d084460ba610041103a8540340708156140d044100c0c07181072262115a20054a02950650300d1004020302070808554805616000600810007024450191840170030804100a2210b054603648480d10358401100c0800640d1024180c040c1000b040e50200008a15400075402030400407602c00c0000c6025414072034034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169812922 1250 169811672 169811689
    0x10090801060902120618061903050f0a1a0c0405090619080f011508070e040302030c0601090f0f05070c06020f070503070b0f07081009111902160b120103021c02030703060902 76
    0x80307100e12a66001c9840050103500e0b03951f0424001c580fa000c1c0c0b0b540c150a41c00c610300043d8401b402c0c074040c0b00c034080350010002c607040c81c04512442c00c203c0101008200c2010039103060380c1e80300b2a601c062100744041c0c108012040e0f08800e00030180c001c20346100703410204101c0399810603445600f1554145800401c00d00440050340341003951110250f052500d15036036108507100300300d190250380020030280340c0280101c85a500c88203040d200b1030368480c101030000e00700400300d44010900d80030401990b00034a00c2414000e0a40e1360350400c01a00c0c82e2903502c043d402c0301c1300c0190380041c100403030030009200b0401040354030300c00c1240050754078022120031050b0f40300610301e905102400701004541d00c1240095400e460a002000408124901005845002e00108540c409040e0810a2040c94000441282d1445100c9003c0a680d40782c4401c40e049000d8826000d040e80030030b00c018801072030700d486004805441e450804860300110b40010b45403210715401901c1c1c0c0c1d9030b200008001e41c10403c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169814172 1250 169812922 169812931
    0x219030518010e1e1314060d0c120b0601080705030f06011227020405010b07031707090b040e0a0c090510030203091203160e010f0804030309050f012301050a080c1009080106090212 79
    0x2c0c00c001e0303c541800c206d0112000140400c1c0b142e0081c00c1d4507010002d858940d0006000b50301c00a030881005450203016084091742c001c3e02060080e00080c030010b22407411a0305c100741c0324101c6041520361800640313041070500e003640405074482d0a00b2200800d8140141706000b09014056852582401800129807040e0007071415030604001c290041790700030568910041580e805066666030f0400300302c030481d00c240c0011005880009001030303044c4901c00d0039030259082c44e60802003410703880da00740c402d25107a205054100c0c8280340324007180c0b03000380c1c0590361108100701507840d400c05c0407a02e151587d2040b83d0f00702c06c0060b000e0281c50044c0e072010501010410a00303201d401284294400307051202c1c010070003010180c43d080c88604120301800110b0700d40208034004d100a048026003069000c43c0c0e00301d10a040c000441c00003842d464150380c41c070122401c6201800388400c50806001408076a2900c0405000c0b80100018484800b40310305402810b085900584880340c0d03980f081d192100162 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169815422 1250 169814172 169814209
    0x40914040209010605030a2d0e0601060813031b0302030c0d0201020a05041211090a0204050414130b1308040303020601060e06091008070309050307120219030518010e1e 74
    0x10000141c03100c02c21141940e50900341151266154003401000e06480c0c0e40d400c101007095a03204690404180402c5219482e52406100c05c51480304010f40e154001d228180004030030b5030101daa407031082e0035245031380340c000d04d081c400c16034510042c8907500c020180100e00685c4009400c681109062048007504986403000358948203d1010080042c007450140d0025070605074590010014a0001ca00008201030b00d8008149000c00d1880e00030f4110784140ca0065041c80d840c011041642c3e200345104004170401c620500c3e006807070326900c500c030040903c81084ca4054041020542c520040c2c80118400e6004150300c1d03040140042c00c0b0001610f405025510600c200b03400d50307891181d64880000b15250184240c1e82c0d12400310081e00030204060458000014548240300f4030341c03003e03400008a5000c0701c041003800b622800329200403c43c054006142803040c41e110341c0c030401c0d001c049102c051504060820001002865420803041d8060180c096440144440e05100d42410200505823 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169816672 1250 169815422 169815461
    0x606040e090321190b01030b2707020a05031207090509090a03090f0b0d0506040f0603110f030c06072901140f031207030e1f05030f2d091c0201020409 66
    0x942480d113402c0d40c0045118500d450f541001050303440ba501c2651405030082490491082d0038190041200e02003102281c541d041c07000040b40c1034000074904000d40e601c0030044d407a11900c120369140901015000700b0401c0501c0c02c00043c103540f0010344901450104014180803c0c0c603241c007400300c00c00c0791f0113180700c264550810804412800250f4000c450704020204040d03a41200041c014895401404840303031034028040280700d850701046da881d4030240c40100c1441c102d0010165030b20b017215003c81d4440c004220920002c1c8a0074450b05804020030145a90300ca107845d03807101c20b09004d030081c2c54500034400c00d080c030900d800760b0041800d1009038041d00c0012150801c1101520a03840083e051106100c04180c140d00e81c3c0c00100e01c003005801050724003c0011078028520382c02a43d0340340000c190303100880c80b00a0322018090500440d012180740300c1700c1d9507022040302100245030441601480407402110810300000d2000b60340142e0005a0315030500b000d82c4100c51108811a2005458 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169817922 1250 169816672 169816681
    0x90b040603123b040c031b110601090212010312030b0618030d08040203070620030f030f0a0203192403030207081e0c061b07080601060306080102070203060f0606040e090321 76
    0x120f12030a68003880c280c0e404540070b201400140c02400792282403071060901000110141c03a2301220018000340c00c01e05461450b681c1700320506c107a00500f042c412071041c02000410006080003640c0b1140c815030704003c07681c005443c00040107504501100b010115140d4104080d9141c103110b0300100c24440e0410881c607091a4001c29176981c0300c0d008807414814041c0e400c2003404840a0052010408501103075651404030040c0020341d001980c41050001002003c50303100d4140380240c034410003c840e600b14903810000010809040304105855294180e032580e20805113402406074007541c041c2d0024500140781401c1d451a04400c480051006902c03c50905c1040e44042040480540d00321381e810740754100e070564031030043d0006884014500c106200051074600100b03100d8100d40f8181c604102d07083c0d56990b001c0c240e01c03854000a5054014400181c0341d4654155141c0d00041d010b40907a080a1b20f0b2000b10308088000c1d628512076500100d90400d00d0300315098401034003072075021704c203255042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169819172 1250 169817922 169818017
    0xd0f080a1e0807120b0301180609050715020c090c0f030a050405101119090b0a0801063005041e0b0f13030801030b0603011103070e030d03060f090b04060312 69
    0x44c401c1c1d40c000154940c0c10600050f0b600350170100f01d00784501c6440099580518104004010702041154280102c94000584600c1c81030b0750a042e030510380241019502c0360041003580d41c4010704c5054160410701c05403041031041c0002c0d40c8182400c410020342c1d0b0805060280c40d007440d1140400c4401e0410b00d030450a42040c0042e074034500da00010401100003a0f00b010f46a00550f508580c0b4031010214019032650b074041841d6040700d0107902c0d19900c0c0b003141d481b1001c140b010803c000c4000301c4400a40700c510501640a00d0340640a42281d401d070f403860203410911110640c0054030042d131594140a481c4440503052508144402c0c610024000d81d640d004c2d003005414030011b003403a9100d50000c0c2480d1400c0d04010080d41070764002c5642c0345400400601401c201c050315074024403550035908270940c041d1141e20165840104820a164a8500c4260240c0469440d043d04651034110000018401030b00c0e407a00b0501948034608807222501d2441d00041810380d0480700b414184102c03818010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 169820422 1250 169819172 169819187
    0x7020f0328060605041803030c08010506030103030513090f150e011401120209101e0201140a18050703050a0b09010b13020705011d06060307081b0d0f080a1e0807 71
    0x1551001c91205901141403200090000e64000744c2c01038180050104901400352401c2e1a044c4070752010081d200c801801104e0300c40090080907000b03d010401403001ca4010b4025024401002d4a00c8030030940303902080c01a07070061094421915150010318003d20f0b0506201d801412411a801080358901601d1400424404c0d06450500c03d05991040d5451803071f4049541c1214082c10030b120f00503010030014030702c441000c070300456070708007042c00450b40d032041c021108440304c0800d00f06980d480710342c0d002c0c001345585880041120f842c0610100020020b0000c04021400381d005080c2d20302c01800c105c0c0207080d00902c0d410150745400014102c0c0d595210000300b0a0fa082c100042c3c86506510b070a6004100d005a1044044817098918600103000581c084c0702d000141e050f01c03e1603541d05141a0f45484c0119400701da0641e0041da040f19040040190a131180100a180301106851700d4080c250f40c00041e0344000226150000300b0281c1a040c03c00409441500e040900c5103851007009020341c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 169821672 1250 169820422 169820473
    0x60114061c020906040902040e0708010e130210050d05040c0923010603050c0706050406061e050d0f031404090b01030b090402030307230d05090a0801060815070201020409050c07020f03 81
    0x8582c00b02e40c2420316164141a45c01924004c00300319138075034441e90340150908040700e10304009a02d50001003050141f83ca1818010301c510b1288a2a122299081011000026a85404000080c070110710b03614286e0141900640c090501d80a070700741004611000c0d0390046483c10040303054011030f4a030407a401031480f0304450203454005603585400400c10194482c00d0b04c0600364904104c280814400640d0007001116040502d540200c40039100100b2280c42c1481030039444000b1640780381c081040780303000403001c80c0300c1c0c50300000b02c14860182d4142d517002600070030301c86590b8409102165815110300e541030901100d1140d401c1c0b4155001035aa0f02c41c0b414010144c988000010b4000011562070f08003010902007034544000101030014402d41040034120311850240d00c0000e107500c018400c42d0705a900b03d002502c9001e00d0741c0c20358042e6000140a40c42107650030400041c811540f0710415001e103c00c1c81c081585c50350a40100301100f42040901c0e407007900f01503000101c8000c0e810340f504a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 169822922 1250 169821672 169821727
    0x50102030a090e0604061a030907060816110312040f12020303040b071211040605070303060f030c03032a08030108101a0d1a0c0c150105010507020111160806011406 72
    0xf2580c41001050103068590f11040c2e030002c45403042141048482d010314411603001040351031041c2d1f10201151101c00a0715017088240510030b1480b403080c820768100d4000c140e01800c0360301d011160000d540d081c0004503002d884c403100619081d000c00442968404861100784003c504500301503c1d049503000c00946208244030818545800018182c0c20281c0045201d9956503107c40e51403038060300c1d60744030180840010307141408c0805c10b8403101c00d020707007500e402c103c8012040d41540d5042c1e40d40300c1080e10103c0d56040c001102c1c41940ca031400301c544201d21500d40781d500c0b94502500a440c1c051803680104441e400c041d000c2c43d42030b0721910041030303107141113810310b19200160800030701c601704950100f151035071444100405c1c1c0d0644001007101481406c11620004c81103904400301c888213000c0e0f00d0000700f08201640c0903622602241940301c000209139480321300c04180c1c25000586a40c403044481d005000100508611014400f400c401c0c2503810f185000a1500d0300c030321504417420381051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 169824172 1250 169822922 169822949
    0x402090a0e090313080d09051e1221070f1712040602040501030e030901081914010e04030e120309150c06090604031b0b01090203070203040e10030506150904062a110106050102030a09 80
    0x51111121100b4003140406008150794130b4081651a4598044450803084000d644174903420107410bd0303089070740b032540210310310b050900c05545924400c00c0006100886400030302c071a00103085019100d5014034070034000141ea85207032600140660344041e031240c1050b0818042c1d81c0300b59801c4000c80c0d0b80000d5000d29551100780005048004210200c4001d80d000300700000403640b90b1a001c070f01c178000c5010751036103500e00c1d1100c001c0105003101807028041d203400074040708442c1d00740440428a4106101149400c04229244413450001c044503003504651004042c0414150000f031a45d6041c682e0740486c07500206030b0b49404104620610400ba900d13580040001c0c0014070a00994001d0603c00040c46618140128561034007021800b017520f0b00e02856000c5020300e28030b512001c40c00b12024000c40b54030b90300d40d10340d1030050545d01c442840301070806482c0c0442025074180b02940c12020780300c0b448610b00b0a4401401c40340c25411090566004000c0c44600710303003200e201c1d01260780c8100c405a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 169825422 1250 169824172 169824199
    0x406080a030c080d09030809070b130e060109030609060504020108011e03080706060527070503102601020307030609060e04080306060d06050a030f060b010e010e0402090a0e090313080d0905 83
    0x2040fa22078503110b0701c0719900d44892101007581c03206007103000b00308086c1141c24090301d07400522454070481040c00728800d1091810843c1020000d0780da517102d401410010440f13030307a84e1584019a02d2192044071000c3e03460041008540c0c00c150305a0140c403542c244004082d00d803090440e0100424080900041408607400c0204071540d000f90001d0f00c03000d420304210070000700304014003090a1050680700e620b00e800280c4102d108505807441404003d980203429071800c018840b9900c545d2070303585247d0407403000c0d012401c3d40900055000303604136640001d00c94a0960307600210703100364100001c080107020030701002c03c09150035242c00c0302045440795600d0000d00090f0700200416442a0b80041125800000b484003111400b9040d5000c0ca10520031400800c004480700800c0340600c601040e20004201ca8a04186e07014014001d0b0140851a80907182ea07000e85110b20112051840c650000910184820103110250024856000100304100600b10090000607084c09114003071116592610f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 169826672 1250 169825422 169825433
    0x30b010f180302031b030f010b090103150219091403030304080403020609190b071103150a0e21040f0f030804090506040f09030c06060503030403030512060f100801060e0406080a030c 80
    0x794000c5a00030f00700d070203420a4051802c54002c0d840390142c8680510704074980d80b14018001d10840140c001c0007109660b09580d14024548071807002010829400d100310017420a82062402a14603191554019035207040207000d882d4504640d0b090107600309006020002d01d2800941c2c040d07943c100ea100e500c4111602c041021102110340f6000d0001060000007400a82100106200760140350140310100c3c4000915a50740c03844801220408900000280da4069540c0040f042c40c2060007640c4003220015181c008030005030310781115520000074100566420502090020040b82541084003403540e105c400040c0541c4c420b15031165107501c00141d041e907440c1e0210b20b00d410219420042c00c80309080040c011101403034100d030418034005000c151441c002040e00c084a42c1f5645461800d07500c038140e80e0090201802184d04a02b90f9000a2407545d40d40c0b8000c0c4150b80640d444140e0313580340c50801081c03450400c40c258042c528000040c89081004120740d05100e406041c015408101413506 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 169827922 1250 169826672 169826717
    0xd0309050609120909060d020a03150f0c020d11010f0c020c0909060c0a030e120d020913060b0a110f2e0911010309032304030201020625080c0f0417010507030b010f 72
    0x2754480c5162001104021240c8030050482e81d4940041120004c205000c000702d800304401301026a12402021a4044c8a542d02d100e81e0110328001080d500016880701d4150381d004103190300960041070340b90543e401c007581c00307d40c07000d65000281860709240c81002844c0c815544020200350b117544c00c010460504000c1003c80c0024860403a5a60324142c40c0e0348002d401c801c5100b44662020241c0381030450060148100b42c50110010340c0c900401400c0c152481d4090031120740300da0003140c020100104007030152007070845d44041c090041c1d88502d68042135003149035030080101c510303000b4031001164a40c03010b0361240c0c0c028200022009082c1c2000d5a036001c00360516031411460700c06250044e02d415010b003040728800e800322292034407440c400c1c880410111084d40d890101c6072503200d1505100e0004160051202d92500780f602800c58070071401c0340e1054000e40c8ad50729507107980e44410002407080c1342c1d00c00c20f00c1c9000c221304d00c1c015000800303109140e035101007040300c10222504040a503130034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 169829172 1250 169827922 169827949
    0x8040f03020a0c0b0304051509061305120307030b10140d0c030f060807081b090c09060f0706020702090105180718050a080105070f081302060307110d030905060912090906 75
    0x403104996a451360340149a60040360308a030705015081621900002c0e454449001c1c540090103800a550b440400c84484410341e001503034648660208038405013005401503000365120368010075001e00b80028801624485c81c3d00f201007141d03960403501c1d04c050380d43c2503038052040c00c00c1c0460340300c04150044018200f4640000312007460003e0000c3d1406000583e4011110039174207807206119400d13450441020400e00d41c84d004013101000034036074002c444c01000d0380c1c0c000810160600e1a0100f401c0c0d040e0700205d0040381c00036400104901585020311040e0b0040208a0b5032407998101c220750b41c90184c50143c002c9081c8001a06d0201d1030340c4012101c00040e0030081c0c414809290350b40401c6010341420f4410300089a240c0c003060780d16511400c280c80c072404c10030085101c0502540d0a200d100e5000030308800400c40a1003071241030b1700c0103111024900050355400315680d16107041030303424088094840d00c0c0c1a07128032202140c03800c416041d541c120b001151042403903a01d15003c40e4a030b100c0510b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 169830422 1250 169829172 169829183
    0x60b0a03020306090d08010602151b160b06031b01050d0905010605060703080a0c0c1e02010504091103150603060a0e0402030a0f081e070b040b0a200c010b040203010608040f03020a 79
    0x41044000100010034541704d16159850821590f6034050507a120f80c001010740184140e86400164000403008040c10001c5034522110702d401e1401000488500c03101c00b080b00d00e401c403207041c400b00703240400c14201c40d8180a945104042e15410011b817040c4108501199040d49507403089042c04000c1d40300c038005240280180f940d3300f500e80f8009104040c1202c642c80d10380c1c07501d13400100d1140b007940c0c41050164050418550000181da40c4145141551012810400100404112650b480c01a07505080501e22216103034200a03034401c910f1401d41841a008090034010000d05a43c1c0c00100421210304503448000e6032503500119007048040003000e00010a01d206443c1007107130440c0145013500d03030101a01100104503001703030a18800c030500640030071020008100403030350041100350400d101038070000c1d440861840640d4100d00c0c2d909520f0181c1d00100301c0c111408002c0c0a03190802104450031890366041c68009842c44401030800f034030a00c490490701003050b00802a500b401500301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 169831672 1250 169830422 169830433
    0x2030c070303060f0803030c0304110d031e020a080405120703120804050706021c030b0126010603180839011a0102010c12050c07080c0c010e030303090a060b0a030203 73
    0x4004008592108100301d000034906800015010700340803100054603183e10103985107450784e103a16a0f00d40c101034415500745008000140c6540e440002e001c00b041d20030741b01c1401000a0b442030114111030760500c83c055400c0842c100c000201d24a01311000d6400482d04130351241c4003200046d00d40025074100405c0d034141c0c0c01003414040d401080d0203100364898000c03070314034a0303c0e0941240c40d0114168140a80400394002401c0103010f5000411409018903191250a41c21010941c0035402c14904007008860080140950b0394036010b0302405008840c1440702294160340c90316810300c2500e600c091860004002c0b5141101e20720358a0074501d120f030007921003444020810358002c3c841041101c16030040b0340c407680724650040c024400b0791907207501c8000303207814a1003000000c0d2a00400108000f0801c00110000824110150540312241c1005180204e01100054100007500e0034003440b9900620070040000d41c00070300140325a902c0000454a421780c0c601250a0300c4540d00020b505010743c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 169832922 1250 169831672 169831681
    0x20102090307030602090a05032a010c02031903030f090203070306150e01091b030b0f012a03050306091e1f030606140306060402030610050304140706021006060e0d021309060203 78
    0x45170043c2251040403518210300c03d603544205640d81c03900311101074070302503a401c1c02007400c80100402e484c2a04181802003080010760300003030421004400542044074517850390300c245940f51140010f50480000204010507840d00080c0c0c7e204d8241c40014070040e10f0b104481c82c901e00c5c001502001303158005841c1c001e035846880c43c0001e003540f1011600404101403400506a12a00503100701d00006000030109500320001152118140d100e0300d010b59980300c044c4146a48107491401c1e80300c0c013a540300382e00ca05002d402c01c2650300d40608030b41303241042600c25401e00c0c0d24401029402c0601d41441c10400c1560001d0610a4443d9074809450720703240c2040060034451460042c5a03c0301f04800760b42140d80e0343e10401c4100d00056800540101c501280950094000c000843d00b01c0d014040341240782951101c001e2405100e0f4025500582200780349404145241c002c00d8054403141c00c0040b05000e0307140104001d8000307210301910842012a0104035203140740c0c4240c100f03a8000c0001d560320301e00b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 169834172 1250 169832922 169832933
    0x606091503110a0b0f031509092b02070b1308031b010b09150607050f0a1103150415020d0b040507030b01090f030f0f031b0515090606011e02010209030703 68
    0x10324881034540c84080040d400082c6400c840420079184000d65650034900035508184a5420041031249031030a078100145003075503030003115440707003011100a14140c0005044d1040d14210107480300104a00304605044090f0003213070003021358826461081e00d5640891400c2c100c40c5603684018954000000d01070744504900c01c5584010b21058000d1100300d810f8802e014056000700c0c3c61030241904120b60000702e141040041c02c1a41c0113908031400c041e04400244d080c0003041600b21003d541840c08800d4505041c003144039000307651264543c9500d42070711041310300346005c441140241d600081d0b211502e0300d01d42c0019690000504104242e2404410140c0104011010140401d406000003c1d0952103055040243c0b580900c0c122100c00c2140c1d00c80e844003030115001ca050015400414a42c040c42c080f0490340715003d0340082005c400b40f000c0d01800d10348098064031854001204000716a6040702c0400e5600004900c0061003010304d1104900a004001f201c903030500030444d001080c0007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 169835422 1250 169834172 169834211
    0x201020307110a12050a140408010b030606030a0308040f0807080a0207050a0801090314030a0908070803010911030601020a1203020c0f01060302040e010605030601030f060609020a020a1406090304030f060609 91
    0x8440da120001c07148022880c490f61880c00d80d00003400001142003280520344100c0142c0781c071800e10309080d075900344400651049038125411042403a0754804101c1c0c4540340030000ca0f60403002c03d40140100041c41c0e100100b00c01da0060020708548081155582001480422100b03c1034000d2100b03604c45e408124000c0d1207280920030103104401010002c242208184228070b0b4869150f202e1124440c90351400401c29040100f041e0021951410100c01158003c401011128400c0010568960503c041074003114241035140001ea44140100559030340c00103a131040c0300c0d42111400d80a0081410700310080e114902c0c802a05004a000e07800d03110005401071000d807403003103805000700050101061708a80c84d03841601c0d03060303011000410106054078907110300280502c0c4042060ba446080060036a4890b40c0707190700507409070345144144000d840d0301078000081800a0007240c00d09449a560740e0040d4040580a2400c2c40081010410340f81d0051000700588000dd2046500d015030386034406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 169836672 1250 169835422 169835431
    0x105040308010f050d03030b0303070203031201090c0c120503040f020406152606060f070b04110f0a08100b03031215180f1501170c130f1401050a0c0b010602010203 72
    0x80d0181d00114540c0ca10088080039260042c00b86600c0d4922500d00f100a000110302072505030001700042400f5880034002803800c03403103a072841d0850354540345100c0111100200040700700980010210b0020380320880d52a8074503014608540c494a0350705200506400c2c40348000d6020345820f200044426085d0360715803035205079849241c0c4060344003240088105a0b030494074090890100007801c02d1070540043c1201990f1a5a110b0500129603a201e50b010000e84040e078800e955000c0800a034a00100d04900f6034074241c68807083e031803400b81380a56030b81504600c1d480c0c49845644140c0951010426296448503140d24800a42041d0344105040d4480c1c0c0c18880c002c9000501110030442000801402f51240c0c0400e09031580e5082c01c0007100c180300030725507410010100800b8080d03a039030650040c018455500303126a140c1c80100c04030b40c0c1c1591640100291001800204103540c140402e020001ca002e0821907a21305980300d0443d10000002c50040612481c0c2001180080c0d0560186106 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 169837922 1250 169836672 169836677
    0x703060c0e090f1009020c060402101202070b150d0506040624170c06120408070c03080a030605010201230c0714070306020a080f04151a030a0302030d0b270402010c120201050403 78
    0x2450300c0d4030011007a8400c41f40103003803e034049000706006050884101099540030302d408a00c01c0c41c404c03505005c0e0380c0a58801d44000c1c004500b4041d0400c00c018101c110b4500c1207902c82c4148009a49268403407000400140c08141d0700c480c40511607161010113009003950030650516141c032401c26225030f42000307696401d41c1c4200c03d000070745801c0040495121410000303074804d113965035039a00c541941c04484d040741c00400c002e800000084240c400303020328049540340890340c541400b00080c2100c04010f0701c0341c000c1425000c0100141c3c2d07080c0046030045100c030180f959800fa2807e001c0340b001c1011241c42c142d032062010000c14031010f82d0151a401e1000c2d070361018142c40c2d40140c0064054140d030040c00c07424030b0401104180c2d10645c4501c080c0f40c0038600e000c50750807c00703001038203001c030806043c0c01581000400d00a45c2c0214817440c0c0c604070040780c490b0154680d00c0100b80d44980ca05c09403480030400300c0041815a8051090a40301a070300c111200a803c0c0c0085000307010f48000d480803000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 169839172 1250 169837922 169837951
    0x11030405010b0a08030d05090109060c02060912030106090e15060304080304150204031113090519050f030a02120c030d1e0e06090303061011030403060504150c020703060c0e090f 78
    0x70b05242032075250048500e0700e0000c40c1086013031a8004010080a002c031480c035035171120f18900003400f0307000784040c1008a801806407480c2c20b124641c10103070403a91020348070b6403c1005010194000e154401a560200c0424001c3d0756152005d036100c8d0081e00300a40d2001001c401c1200704031624000b98421742c4100c40c9904000700b03500d449006d0303001e5408020210011204400400c1c14503d80c00c50b00640700100220b0141601e445082c01c02c034441004c00c4146012405100501c0410480704131400903030300c025172820008440003526a0101c8101d206c1510000500c644c0e0600100701380da0150380014030420a00301015084d403c1d407120001850409030504a042810718030100d11184685c4640d0040c61440d540c0000700f180641c0f4852003601403203100b410b5410700b00c10070005040950300c504030000300d42c142130a10703000001000c1c00c5076905504141036840126400701e119411a40c1c01440400c02a01e0420140c4801582c450b02c00e4100c18a1002c0041000c00480420302904442c1d10400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 169840422 1250 169839172 169839191
    0xf070602150703180210020105071418010509061b07050f0102030723150a020a020114010b07030c08120a0f050a0212010308032203050405100e311103040501 69
    0x7615107010608007061402a800000c080c0c9000340c100169410f40e407400e010301030b01194001411040d00c0c0c00600010303075445040216640e0421410000a10640621030402a004d4840c40c4020500e021032810401c000c40d0351f01c01c0d40c852030256140810600741500e052180043d09640d40d06407803140a20409407401001c285500100880c4d420b10340124021030340800e01c09407400c403403d280008443d50f208080c4482c0e0951002f80d291401021101d40250355406124002402d60b40341d810f0000710070422800411040c091101100c00e074550504020a024482e4207107030945000d1000511814002e04ec10040190240da0004009a000741d00400c13054840380580303012801807001514010201200520100c0c04010280d0392165080c6150800d91904000c200e80c0004d5001c011000718001040902c0b044c170382a0140b644c892150725042e00702080c40b0300041e00c501e80e0700602c0340010602c1d0b541e4040202c51030a032080c00c0c0324070b40703001e010700c440c600c0b05000c059204907010307a8507529018014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 169841672 1250 169840422 169840427
    0x1515060304030824030d05042c04060f090b04080913050105031011090d1a0108010b0904080903070f1206050112030207030201050319050c0a11010903050a0f020c03030c0f0706 77
    0x480c001e940540d105103540d681d0b00a420714403041481102c00d008540c84111610340c0d42009502c908029030b40c0d5803a00c9905e0003194001c0899000c103c00941c00095250840e003590016a080d0322541040c00480c01075104071440008101c2000003400d0001001c007004188182d0100600c0086000d039003154038000140a03d1003114001c0c090f842d4980c0219960341000950341d00403055841d1617003440791418050b040000c01180366200100c17288a0b21410b400c021480e03012000b030041944800074002d00030103000040e0249001400217101020100c3c514a617a1030030002e40c4060070201449194060700c402c0c80400c8160b42400c00c848250601f0004154800c2030700020205540c950000d01c90306041d0340c01580c99800081040c2c4140c02607800340740306c0b0300d1036004441c0a6000440f20035a40e000e41c0900410000d40c0d8842940203a042c05280700000340d0040480d003040d859440c040b04038195004089043c6000d92269503418030002c80c6902402601081103000540001c0c00c9540203035031503005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 169842922 1250 169841672 169841677
    0x60306010608060f04020c2b030902030706030203090f0a11031e060117150a0f0507020c011e09091406030d0f02070603020a0e100f03200d090204020705151506 70
    0x500000540d40800714203c0d0400c03814155410760003d02c050b080a0b440000c251610843d658013071412418442c07040e40300008000381d411074204a00c3c3c01d1100012640200c0e40c0c5400c948150340030076500000140c0642806e000b01c01002c038040c0d003a03c0c203075030860800100b00e2035240c00341b9100f4011180300c69249491400e001901300e217441c002d800c0e5686030283c1f00b00035402c0900304038018002c00b5801e803401c841c20f21520b13108000440000601c91021004001201c900030032600035503100070b814040c80d0f070304010001003a422a40c0304007203581002600b2210600380d980b01400f4503050a1814042044083c103007407250b40c003601210b03998024040100e90050b100001c000141e0800101441264882e40080844000505001104229960205041c90110351240000075a030300902c034003140d0705001300e40c90103e04190034216a81c00187c04000d078851200340c91501d554860f501404c6454540580381c4407034029041e00c079070f0400c964032050300d80e40c02c0710b844160101c0310000341d0035450884c00307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 169844172 1250 169842922 169842929
    0x12060f050a02070f02060901030b0324070f020a02041a04020d021e0a08180c060f1315020709090f0c030507060e0102060f01030201230f0c0c041b050a0912060c0806030601 75
    0x100b1401d084c41c41d409110032a840344400904064030380864500eaa201088030b15480c85103c0c1c840c00400d800341400072843e8101078031890030060380c5108410b000d40c1c001041400c26404840c0060300c0015858207001d202241d00f10290000d00105c1c04c0080d100b00780d400b90200034038505e014024100e8500130441548510b4401e4000b203205180411110034070091070102c0c00503031004883c1c001090100065054024074480321180c0d000151410a0306c06551031100106141003020bc00240c1c1600040e444403102d000e5000c050740d550b14003d0510080440154100d41c00100c41481c05449082c0141c49840724018507000c1203981069900c5544005080e91096040c44618100307642194011206ea5100c40c48180008012002003811042c401004040031410941e8003a5164a40d144035801c02580d084114410b500d09080c102d05030806103403020348a541807a040e591000d8242080d40c01c0e2420f50407414854050458410810a1990015600301c040303445900c0241c0d940c10402d0fa84240901 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 169845422 1250 169844172 169844183
    0x50405040f02042115052e050307090e0c04020c074202030d14010603060503060412030203060607050a0c18180b0c0f0705010506010905031618020412060f050a0207 72
    0x1540840000c0803400040d5070240300344a105c00620001101c003058079800d95004100e030f4204000e0b01003a140010520f4400056113072a50a03861070440002d403942e0b05c520039060b149445000c0700d070f0301400921070842481c0008008544542403421116611642070007500c1d02c90304017103038690321b805044020000621100780594980760f03450035415000b45440442c0c6040d440700344108154414980140740400080035002c510540c5414001015181154440f0740660003074000c0c4404500700c0740000d1050086403c0c0560f0f03d40700e500c085189803007030ba4405044c50107000c0c0c0d40010400040c6e0010300b1a03d2201c482e02c4841d4070800140111090311710391050b080780a5001030300003801c24452170b9000f41580d021a01b004241041c131145c42d80481402c803039a9640e60104026580c000c181d4070040c000980c003e0094484440c004140749150340981c0d510300c0c50900144100110f150120b90140207000052181d1058501d070110207131031071820300c2000508000000301031800600c00d5034003a46c0c110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 169846672 1250 169845422 169845449
    0x150b0d08042607060e01090902070b040506130308060d140706020609070f0b09010c050304170303090114090303041103071a1c02090d08030a02070b2401030606140a030f0c050405040f0204 82
    0x44c800703403184000340e050385c1d052040280c400100a070142c8081c02e444d17030046103900228901071800d1414030800400180155200e04d5101e00480d40c000011070740407000f654903425000d0304d410702251254036140204c80501c240580410f2480e030124202c0d00070f0004508444e006525100c0003a0444000c3c058450118002d0120b1040c0b90312880000000c140517074280d038545030300c1d00b0b907140f14400711022807441c2c2c0c1c0c000803d200d09400e0074804c0c13400004400c1d45400300c9040965580c0e8030703484007030b20240000e4030040d4110080e60b4203000000c000c1c14a2090520001008119015140c005003800c4d4440c0f10f240144c4c030210030031070007180d40c0c041e00200b441170075101c41da4450302c0d150000f030400c240155007403180301d001603030310034405028000713980740c101c0c811a00b10301740700b1865102e006280c109400e00c40c0800c080740d0099843c0e0010042d150800d034403121180811030090061a01d0345101906003500c0e6021603801400400c16960207840500105e0450900003007a0310880c411203205c030551 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 169847922 1250 169846672 169846679
    0x50a05101815060f0611100603080912100f0b041a0102060c160c030c1a04120f0201020a0c0906060e0114030604090203070909050102041706040c03150b0d08042607 72
    0xc0c00720b0400c0100300c01d000016240d8490100a4103141c0e2500000041070394207428840b030b0032081100d10801590013070240403142c11a0f4a180307850117460f01007801034140e0010105100400d0200c91356030000c4000801c8490020150403001d0a4000121030285140043d100142e2008c04020b007081c0c403060f00200040e8451411941440d0322250380b10f018000140ca0000c001075010050b6802503001d141e540842d030b13041507144007040c500e24406011560741000100a0444912241c0c11443e421140300e020b04801800103030b09000d4010300c01480c0502603100410710010300d5011500303441603070b955800002c0b40b200c015610070a0f05603095210410620000f180c901e090341021040c144090180c1da69655511041e00686003a0001101c1d12794020500f4841100c20400101c1d41e0b110f01d10081c010790506440d1100c94a21a000145c9000b50306403c2e1101c41d0302d19000070341d818401030122500380e0140e083c154119001401802462140ca50024000b030b801483d05501008505010f0b1640302d18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 169849172 1250 169847922 169847933
    0x20702150a180e01030501050105100f0f200a0308090309010801050409080702030d11010507090311010c02042306040c0512011401031d010903030609021603050309030c060103050a051018 82
    0x407010040070040b0618031031000407002c0101c100104501488022594110310f00b55003034401c160003042c00381030001c02c00e0035038943c0950242002c0406041011505400700b4017103861602d101c04c49a0007130024003880c0f00440c400035406414900039a01d0441984440641544130300c103601000d4005504180180480c3c13605900041000b132040c424503103040303000c0d80132a00380303082c88240130041001000100d81c07040342801210391201807480c00d05010340c00e5a50306c540d080005d4401c681000b004003d650119201c560001204001d0540c04040c082c1245110642d0260101d070241d0003181061410b05040740241f040c2c410380f194408640311207a0800350544449030710400303080c0c10075444400a580c0c90801a2140c4054410f0400115000d8200d01b8058155011584000c010b43d104005041d400a21882107804483d85440c2c030903035a481d08003286145010f10244651117015080c0004200500091614030b07091250060320440919204a60102e803510707641d4411021140250000049 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 169850422 1250 169849172 169849177
    0x303260606040b0f071202030a08010f05090c03070c05010e010207030207090605031513020910031a0106080105010513090203070504061206030201020309092214101e0207080c010507050d0c0302070215 88
    0x242d00b100d182016400c6d2501114030b003e040d061b8000d03800c0000c1c01445c55500905403405041c0003041d20400310300d48008a948103d0040810041c81c10100100782c0351403140d440765003a190040000d212041c0000f144034002e500450302200540b0800b10001000300040c012003048510050141c2040841c01021541044005004005038405038044100607a1044a51402022091048420b550844c038040e9044441c0c0700c2d01e8203c0410b44401004966402030304c0a05444086c0b8180b80c581c81428130006400d107060b0040b4010500120070041100ea00a020703008540c0641da0344a0141c4021000c031301210018040a13006800070440940ca0b81004500e094100581340d1005212901c00261303100c00704c8078400112040e002c503070040c03112503c082141c4807102200503800c00003c6007000c0c48208680120002e110026008203060301400317085401c0c0e4440b82800300080c0711a240901e40100154050b00f1419800d510306880c0e20204c501c030307100382c801c002d50240c45a0a04040e0488483c990b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 169851672 1250 169850422 169850437
    0x30d0902030a0b040506040c090509210705061603150803040902090a1706011707050d12051b070f0b160f050f070909020f0306040c03080a050904060303260606040b 72
    0x51140c4000300000884a0039a54401d90245025155505246c50310666511140c0c2c803418181c0c0c10082448006800800c54335078a02c154040455400740541d551a41da020f020b9000c2c103d401020f0420031080c0c4902090000d00c14145d074208114203014107407a4040009020f08403642e44103100c24098920703d0742c014081410003c18070725065a50700451500c10708010388200c26600318000401c08109000003070300c0c219801202810704142080f010409100042001422009400c003260252038001e10441c0c00303428207048010400784440785081e80e80d034140d20610150000d0080b002a4850003501990008111109541132030022a2260418481410400c0d9624004d40f0b081081ca0384040206400031314440c000864240504d0040240100113500054000c0e0040340800000580c0c8084500a40c4da002501035244c80c20b50004880074040d032204203420034513146000c028150048200041c414010503071030620f4003c16090902c254040d80c005070081e009210a004c9002c04102800f02c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 169852922 1250 169851672 169851679
    0x219051509030f270d080904320c0c0d0207030b010b030106050a030e010b04050112020406053f1f050901110a0e180c09210604030c06150303021617030d0902 69
    0x30f44d4503d80011440070b0041400c540708130000404458608050041d03240c0719040004508096400820109103026142c0c0003515011484000604917030514041da01443c41c4034003114802208084080d603140360502082d40c2000704d40c00001408070980040701e0681c1c07a90b036202818203907006410340242c1107841c55582c00d9501e889940c80700303469510906008251405410b1000203490052104540013608603d001d1101d424009104035001c0b014100c01491284079040d40c1d00c1da00801c2000d00c0b0141400c001036008072083c110418405100241401d05e19484c00c10160b2283c00740c4034200c8181c584240000d00d400d1064445150103003c00c0700d80205c2c00b031302ca02480c41e1501d5501c0700d071500407504031130b030f02a0100c2d100405090004a04100c40d040b0345441c5891100b9180b00c50f40c1d508002e01c01005c0205a1100304100001c541144401e0003803600c4941e0196203e242c069180d00601d1403000341503d50f95400106000d2348843d005c0141d40c4100a140b900c103900d01a03102038500d544080e80c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 169854172 1250 169852922 169852987
    0x50a0b040f02031501150e0303030708130803040303090b060d03090303120207210905030609030d0f0f1406030105060d151a1e031011190219051509030f 67
    0x2580f02400184c0021002c4031814034a90304204da13005641040030492010402011100030407a100002103942005450401462a40c1c0d0028200419000300700001d0400c070012080c4000c040c0c241c3c0050084074400c16040b00070303130788003030500c90301c0d0b42086009000a0314805040011034006d807201042400d000f80c000d4a481781e10740340d251848140d681302400704105c402c02c80800b25480f4054138082c000c21030240c8154107209030300b40d640303004210400104a42c1e40c9801d24807840d031a0300c8922140c04c50300003402542407003150392007128821100c190007942000c0000e0001d29100003402081d40d0b0000215188070307404104100240894410389404094290442000b40e40daa40b6030039604c69403c000201940480c01410b0901884002c1200c3c554107200c002940710041c0c070151034011040c91040d00104101c0c4030102c1c600146010840600789603505101c040c000d0120700c403001c00340701d0103243e031454480e0b15080d5035070f10500e9440400114140101c0d4120445103002c000d010311515000403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 169855422 1250 169854172 169854203
    0x305010e0c0a08090309030f0f06060a0b1c02070b090a060501090b0d06090c0e0f010303120c140c011103070c020a080616110a0b070309050609010c091a130b04031707050a0b04 77
    0x901e020317023980719000da591000003c0040b0000411910741c1c458803c3c3c5103101224941007501c11580100d07442d00c00b56460744003c00e036021985505580700726801803007440250414408550701d940c5c01d01c0c001d841c220700302400460500f80c4c50080c14000c4c1c0c00034200481e0006151680002000382c010101d0352400f14400020b8005c03020b0440c14001e601c4410750140c154950320b4050134600381002254070035418052503407840c541200b00d15841d036003a0039650343d82c1c40380c0d00e441300d00500820805c0d1071103002c0441441000759203d8161444107200b900c06003070341915042441d0b954441125140d0030040e88410803100d45210300303e445104d5101c4012241c2001d40740c0e5540001e020b040310042c0000e0364903c5200d0500904200d91500000340d40700820880c0341240005280711910b000712000075034002c0c1e0110620344820102d880d00d412011626012640320801c2c1001c076030281c401918080404607855a50a180c1000c6400140c2d010000303101c0d010709503480c415102c000074800e8401d01c20115411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 169856672 1250 169855422 169855429
    0xf0c060b040504120f0e0f060307180803031807030b06120a0c060507020108070314060405071b0c0302010e061c090c150309050607020304030203070330030c0305010e0c0a08090309 79
    0x19401a407113500001d41c2021401c00040500150804420400000b252081044c0c1c9420700307007400c2d0791420760325256a540c4411080d80e1440c40110f05040445031000e00003950503001c0040c5004045481907903007505510300e44d281d5148228000503160081d8034001c03910b240b85c083c1038407000e80c0791701054a6122045403206483c5040e00c0e4002d2011074030008641c011580d1006405500018604042142007134541c1e1030b0711340c02001081c1178007503682c0303002240542340100b000c086014001c4242c400720308000d1800c068442400d1108a0204004400f0030329503150000035102090304454403020800300040c5d003a806440b10a40c280c0e194507a60300003088641a03c02d80e060000380a450200d021141c034940141307050001403001e01190010301c42400103030b802040000c00c694100600c1c4030480d00c88040075040001c68000c0c02102c2c01a201008802901078001e240502400d40f020411603980700b0940000703120403500c50149000c1000f00c0c41610b070080c034025420240c08403c4a051810701d2010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 169857922 1250 169856672 169856681
    0x60b39010b150a020303041103071e0e160507060f0f0908030f0c0901270b120f15060406030509100f0204050f040c02030403020114121509160f0c060b04 67
    0x11440180d45070982004141845100e0300b010082c501c00840ca051034502e0000c0d00c03400b000d84001c11070740e004803003684590b90802c0340c10081c00340202400c0c40103000c3c0e1011000761615205160168035603c00140b0892070400280b03154028580303c240ca00104e036694140180a2141c02c21510b40d5510304d0203001c030020348584c2d00541d00c0340c420300742d580c104809a9040908000d140442507041082400070b1a60303c034003035550342c3c43c0301e03c010161607200981200614407690466200d10901242d040c13078491047c64072130b020700440c40c0c002c3e85e103468044840c1e50780341c1550309640c4c1015041104100d03580c82a070001d68480400001e03155a161038000d020180d41030140203000c01d41c0c01140034051440e0245030141441720440e010040340410b094040e4480c00342c2d10010703041c0410420300309000400f180860714240c2045030145414940501300b005040c03100140a0b00070b58000c0c001808110020400c641c0208036074480121003d11240110344040e103100d0210785064481c00c1502160301c4178081c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 169859172 1250 169857922 169858027
    0x30c0312020a06050c0d0f0603080901120b090a090b0f0c0a2d0306080d05031b03070207030602070c0e060f0a26150405010b0603130204110c0f060910060b 68
    0x111307940c1c0ea81b1040404026184107034103400901d454207030100000303191842101d110366000c1c21306100c008540c40c2d0f411700802c9034240854200c4070090030000702440d0369205d002c4042c40f44158011a40310307103480344c00c0350030212111042054104008901d242c0a19481d40c3c500c8901c1c0d00c0041d0600284449416900040911a001c00c2c3c66a2051002075000c8c0702d1107844c0307455071600c22700314905003d0004811604d45c14012400c41c000000c105564801c0c4000d6018641100055640301050b140500c01203040f48034200644254401043d0b80d0700e07002c50345000c4004000c00c40064542003038440ea12a442e485202a0100325600c0140d40c0810306001042d042d5000f03c2c4400b5061a150800d5400c1d1072542d68140e1040d0b0b006c00810034aa2040214501d815806640024100a5001d89881d05214100720400301c0d1080504c1c45030b0b260400a5076070b00c21085881aa49070f401614041c06c00d640050040c910703400014880080000e40141e0045a41c10402c0030000b00d0340f4a000344403607000031640 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 169860422 1250 169859172 169859191
    0xf050708010f02120c0726070507050603040201050702040c110f070f060201020c0706031a090c07030f020105060d060902030c04020c0607030c0203120a1503050f030418020301030c0312020a0605 85
    0x90800c40c80e003080c802c0d0070034080c1d00d08040d440c085a09800c0d25070004001d20391012100041400b0043c802141c0f0b80c0061011440c1d0b080340403102c0340240042540011804070342c01d2180050100b19030500d00252806180d060715400d0070a080381c0d0070440500169800c400804c0030818045484102c10016084004c21000180800e5424100800344084460f0050340035603004001c0318484510006031b203411030320f8030318000809050480c01440035480d4002266808145c0000740050880c0f2680105180340c4261590b0700e035910701113016800d035030040300c0440d0b0111914072003034082141c54120f44241e034401410784801c622040001070407030b0090100b41c509680301400300311460760144680600500b41e40000d50900101c5056400707003040c01030020f006079440b10b10301c401501c000b0309400080c560200c1600d152224607240250350360414413560900c0070b094402c6481c0f4049901c01c8a06070ba81020038001281c0c11500d91040201c41d05049a0451284030007200100307080e032240307902903041d13a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 169861672 1250 169860422 169860433
    0xf0501021911010506281e050f041e0e030705010c0c02120601030b0103060e0c1005220b0901051c090c051305070806040b041508062a031f030f05 64
    0x401c0c002e082e94010002d1050980c541400d00c040c0780d036800b1014000805402c540700140b000c81c02d00052251095018191014038501080c81c1e0200301d14003c1c00f42c0f01c00340c91030442546c0c00001c00c015075080c0302d40151024203203010250203500d00e80080c2d030380b01c0b1003c0c120b0f842e03d40c1503075400d400c41c4e5918a00d100001d1141003d41c045250900310b035101c0b00c0d05070f0000c2407a5411600c1d4400d80400c180310062041c2c2d510080300707841e0b24080c8011300382c0030802044080511040b2001800c0b40e400300e0341c001c0c00c1000450b881e1061403e907a0140b81030720405003a82c2e003486200001034890382e02003445000c0c44980405070100300e8800b4042c0075000d1344944600346030386150909002d000910740c07440075080e0307042c00d003000006a400340030a41e015408950104030440d04c04045001401c02201c942414100303860003090b544c400190a502803290b510307540b188120130100704464410030101d14202c40a0810100b95807142003145003da01071151660030030f0759034070366444001710034210b000ca0301d54114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 169862922 1250 169861672 169861717
    0x2040b13141002061302040b0d0605040b06040207110915090a061409160e1c050f060601020307051015050901060309061104050307120c1e0f050a0e01050402070f050102 74
    0x80110301031840380a40b4182c082d00c41c0058081c0d111080140040003514821003003805554883e04124880403020340321802d400138604000d806000100c2d8150707800d401510119003913007410301c02c80d00c865401c80d000516030326000701041060803000d41800c0d070b10b1304c0403100c401d8555912010700d0b002e08160600081e4507407070b1883e0710380300c0a111030765188180291000c10407403800800d50380081802e14500842d201c094900010610400d02c014040c413402101c1101c0304011000400380d030b1403c41d80040322019a2400c004903628412031000510503000105040d00e0079080d500070381d200328880b031952000c035921207001c221266003d030302200010340c4070050740e07041c082c49101c4d00c0c40d042c80b14101d05242c03a083c6400709640f1403a903c501520524070401040500c10000150700c080c003241c0311040140131205c4940b28201050380914002d41c140024006018035000c80d040c400c50710403d0341d11500e0ba02c1c02003040001d400c110029180001c0340c07210040024800e01c02040304103252260344100100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 169864172 1250 169862922 169862939
    0x1203070b1506030411120d05090a0b03040827030d03140a09050601050d03050702040f0c110a051207060e061006030608070509060d030903060e061e0609071202040b13 73
    0x80a81180448141c031504010103440d180c0440398042d80081001440354550310109a00d1980788004c2c0641e40294a0350b82000740d1b00c0300c014a90020100c0d030000e50107403118074903072136131000340c1b0000c10b41038040100400150109008465001864401c1c1301c0520403103000c24100380392411180000781e50340510100c0028000070079500003038850b004014801282d980e5076681c1106000b2544144004254402014400e0f0304a85100740e01800c1805880210a24200905070015608010400c01850001510700c00280a60303100c0d003000c000d00301e80550040302c00c01c1d03500c412001d0790000d0703c900d0703904007406081080074010049003070320003c03182c64100010219a1107410000407608954810843e81c1d842000094004a045811f038800b042940f074245e40050b1141d0004060a040001c0103c0840020841c540b04104e025150002100d11481a50803110111031080e40590720102142c0319507c0303130f240c4001d118400480103240540340d140c1382640d504030302c1c00c170102070300c414006011014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 169865422 1250 169864172 169864193
    0x6020303060d0b18162d0b160602040b03040b13031b0305041203080604050604060605030402100e0d0302060103111008040308041502121b0403020303040b090d200307050a14060c030405120307 84
    0x46c036400841600080016524410f090f51240c4050a00d010900a01e1004440e040c0f2010540c003920455031156101000350040e0800c88041e00d2081d2040002071030f507001d05004018003035059443c0c00c070026200c68200b980303440c0c4140a0b0200042400041030b05059034034840308541c000e4031480c4d110b1070603004202c142c8034020b10389405141081001c201003504203040d03d80250781103411071842c0701000c80c00c8a0243c01c0803041c60388201c103c05180c3c241500865071074140d0b4040c40c0240640c0d5010310501c503801c2c50004406000030241c0b40000d0103e0b209080710354000340b01e00304101300d2000740d200040581e0808a085d000b20181c40040c0841035102d060050031441708401a42d050500c5c540020761a80601c0c40303039034240080010781e046d03299030b2144c0300b00c511a40910317944043d01c0344040503c1c1c80c1c01318100080c0a4400c030322000c94585000320400c01200c450810880d491340711501400315540000700300e4213440c44148000310b001d55030110404c0002c01c46000075616802d00d820061a00e9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 169866672 1250 169865422 169865459
    0xa0c0501140d0209030c040c11060a060509012705100602071e060804061506030204032a060e040914061e070804030507050f010c051306020303060d0b1816 68
    0x800e4401c0c03044980328061090b5498085210b20060310750300850042801d280748240e105070701070710307040000d1b11140d04850b540c10354a40348802c4548640e16801040101d1f1210300031280d00c03114010040200368620004180e5050f04002104840c07080d40300d404003954002d9468000c01003800b80180011039040010304010710415540b42444441140c2c54000904d00d07003e2001004450800a000d100164005503019405114a01b2a0075550540107000350414082110360b62440c56088850807624504004400c1c0820402618246801e60075a0030719428058942c005450341e580d0404240940000c1030300d00d1540c0302602080c500321500240803a002d0040c510403e040c0c406101903264014030940c0c1c890740c14180346903142183c0c10010301d8045100c0c2803009030760074510040d4050307900c0b102400c00d0010305c1d240340d145551100400d0340c90340811500607400a560441c0c00740407039114001640c001143c06241c241118415a5860500c50022666044008841c0082022405038103c003c41e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 169867922 1250 169866672 169866677
    0x603091f0b1c1e050708060108070905010603140609060d050f0303010618060c030807090806070c06060f030b040b0c0702090c0723030d1505040c02070e0c2b02040509090a0c0501 78
    0x210340740c5980c0c4000f07900c03400b800340030300740c002c6100107042003000c00c0000d0261103210112480381d13945a10070b6545000038021070f500c5900b0031b0300000c0c1c030328064000c01030f40000d02111041d00d90380d40003d20101c080010b08130350b030045542031350390080b035028046041c1031001800951380e6581013070000740074481e025008100ca520105405c1009075401040718105036890328103040141c640b02d20886222417240c1000c8450700668003481003154004040c211180c1c800c000030b00c00d0300e40d903d0104008040a10000d084140c1c0c0d840000c0005250188255000304c2288a8074240110381c0c000c2030440d002103134040501800040d0301c9060003030340d64608015480040700400c003461a299043c2e241c0c0138000300030703240300c1d01c030002d043c070907207100c0030316000307440c019000300b000c1c0c10982d00003075641c0740920580b48566588008100301d91040c104680103c80e2018404a440d8120655052800e41503460440242e609000214403503440c1c0c00e10500845950004003860b41090401300c1049100f9840f2038103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 169869172 1250 169867922 169867969
    0x6020405190b040b030405100204090c0207050a080c27090303190207021008070c120c03110d0c080a05040509010909140c01020d030b030118080c06090106050f0603091f0b 75
    0x7050740340400b103c0998034109841c40e201d03180da1908916204d000340c0301c0c0c1c07042400401d0119032401703154003c1505441c1030703080340c00b030302da4490501c140c01156002d0100b15801c0514000103904100d0345444035070f685400c80c070440d440701400804199806542c1c0484e2900000107002440070400751040d4000b010350421031800c442680040c028000c280140e000f4024540e0000d4980d600403400b14230740503001484030480c9102100002c01d420141a000c0300485d200d1280c81180150029070b8940032030b0300d500c4a40c141d400540380c01300b40b900581601c07400c00038108008030742900c8041a41d4020204c0d03000201d20301a191500900ea00700d803180981341c2d81c0c0240e820741016070340040c031010f49210905000944120100c0400e014101a5118201c0e01d14030050a10401484c00c0050079201070180c1560a83c1d00c560320141c3c244c91007803140540c41104580e00881d246070540085400400202c00c40b02e645181340c50019604802e01c100c4040d55588a403646100d06043d03a9042462009480866 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 169870422 1250 169869172 169869179
    0x130602151006020d030b12061603110304230a05100219031a1201180b0f10030b0402060d1415010224040b04050a0212070503010b0f0306070f02010b0d0602040519 71
    0x2940c9911300c0758802e0826072501074400c41030b103400c503040035003040303d07001d48180f4942240b500c201c1904000d009000249045407460b10241c481040d01c0c010356101c880c05480240f00c800701040c0104801d07803051140104024500020340030000c904080180038005a203078a83e00c5007003000150358101c1001070600b00f9800381244450041848201a02181c070004003100e4010361b21300426962101c820b078140c0e0706044009000340038056a200e004210850300f00c0c4d690344842003a4130f150303074400100b049011340007140040c6000c0300030b8140182c0c06007001500355010400c0113400b03113054031151542d0040b03950700401568140040e81c0720a0003c810704089800070b500d494a5020000d00c0544207040d003102203410020184890004030740c0003403034098410f507800b01d00ca03202c2d0701b5849114803a40c6001d00d204483d01b001ca181c07149002d0010007418140d55540000e407a28821800600c00719503035680440c07540d5680c00300d4507141c180612001601d642c00d14060261903100a400f1241140c030035041003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 169871672 1250 169870422 169870427
    0x140a0902070b16020f0708070509090c130c052104060501090501140f1201050f10060f0e0904030c0210170108030301080a1e0204050f2401020309040c0203130602151006 74
    0x100c0c1c02640f002c00202498084100c01c0b41010209038090f0401d00407008005107078280020000c055880417034038002107440c2ea8400307170b0361291100840e41e007050302c038401810920040e600c1a2281d2500b400d01d203180401e01440c6002845035010f1900014410701c0500c01886007610902c0d0240800d002d04001c59410005904282c2c088050914482c0580c4040100140c4a01d072820b92045140700c000c1c40030b410491039100e4915000c4401214100c80700c42d0000d10284030340c42030300c61400d03103840b4003502010788024002012002403003035052140d400386080c0184c83ea40c04100d1030010540e902261100803002c00300b8944810380c848030940d0300920061003184c0c0c002c0f4008030300b103900502e03514000c482c0c0445810a00104140a54031526101c1049054501d03920000e1050050007000c1c00091018010b1040c2000b4414425005a00074848649142019030100c3c4075040e9900403641014812844e00071400c03031135001500160400b6195011075100000920340045252415545442c01e00e46e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 169872922 1250 169871672 169871693
    0x1e06030c090c070213020d020304030215070905042c0c030d0915081f0b070c050409200a08010e0a0c050105071203021803010912081305060402040207020316140a090207 74
    0x41c03510b10b600c000f5511045680321105c07810440d5031080213548880d80c080d0403030020341048509402600801c05486504810001d1151080d402d0351907584039281804240300060105000d6015400c03480c90700b81c0c0000c40da82078079a0340140716500900d0070400050600d401c2214840a18051203611001841446581201814030510030702d8658000d40d5060300c2820607c00115a0180c8504401000b1031401c0c0302100030710384140641d11044111f9030310400c0c00200c84079400083e01e814907a601e1400516000d40c4100c0c0e610748010455149541c89440c0c1d182180d481d1810610140e00c0504414200140200500000d003801d0a03c5c0741410f905c2c2e1140070348400c400e207030722080507070000340c107248005140031000b40e0940280003080001100c0c43c107641d04942d04050030b400300700442c0000301c603c8040c042c1d4201c95640300e009000561900c0c0d09104c06504020b800700da0500500358111100505580c0020091540001e0502c0c280395840c20703c0030f02d0105820035001e241c01041a1404540031340c12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 169874172 1250 169872922 169872931
    0xc0d0905030304060e04020a0516030905041a0f0f130f0209040c030b0619090b04060f02010f0506030a0b060402071b18050f04110a030210030204050f030d020a0f1103061e06030c09 79
    0x1401f40c1c1e9289189021030702441400c2d041c80e5030303e15407540741e01816030220500003981c8054134208081c1400903107a91814444001095000003000048940c504007411060034090b80a400801c482c60f1000c2c1075400d4440c00d07841c0147c440e81c0802c41d0035552030035000d02d482016003400c0412801024101083c414031840c0400d09440384a142d0ba00c0c070591241c800780c001060150450383d140c40c0c594000400b110500c004c820015824103001e00c0c0c0c03c80722445214041c0b4002001400c4181c1540d0f910307040181c008018650081c2d0a00260b408a028048a03400201250f4403008042e42859000c844003092243c00031041442c0030300700020705c4041c4007950b402c00d8010400c0243c41c1c800c507000030100c04881c2c1000790003104981c07241e1304158150300500f081d224101ca92514a440100505035180600c01c44000168010400c04000c11341c2c08036420b445501038020703100c40e0750641c000300f4039010b030940783e241040c9000c02c0300c03090b413402e24044a60080001c5001d07000030001c607070000781007820161 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 169875422 1250 169874172 169874179
    0xb03060c0c12030f04051006180e011104120b010f031709060d0c03060819171b0106062105040c060503090c0315041103240606070203030c0d0905030304060e 69
    0x3031400380c880d400c2040c41c0c41e210b03005050565034648180074840030741090703030300721030a00c02e21040e5020001c01c0d020303610a03039100e421a001e96a01c0f00004c030002c0d000d0450080900d56035030400c0314600c2c2450b0b0082020f051100200c07102c2e02e00d10b00d00b40c11041016032003e207105c4101c3d1001d2000a042250380c107944900715008980b500e070703500000b50380c621030348491070003040c80c0204004109815400400842d02c06605076903c180c4451070030701c240603662074006c02031400c21122000501c10034000d030054030151994017a094070508405400c5400c15001140420b00c03202005070b0f103d0449480244140d242102404030342065610342d00034211901500c1c0c1408008800101008800c1000e50380c0500300408507000d026109603600c03c0c280054a05490450b140c46003003641d424005800c1801c2c08038494441d031450b80c0706400020300c490103041554092420071000015940400c082c1941d0840400945040c0018a901504042c82036101c0c0b030294200b840100443c1d5040492022031282c01e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 169876672 1250 169875422 169875427
    0xa1407030e030a06050105030d0203070f12030605060417060a02040b2b061409090a032a020a06050a0e1f05030a1104060908010b0d0c060f020a0b090c01120b03060c 72
    0x14501a10040a070002454062285040710020302900380c020038101c402c00d40c04c1d20003c0040c01c00490300c034855403001810022000780040300065081c0d1441c10f00e03c5043c6000a98551641d000844035801076014034007522105840b10301c001c03000c0c408182c0100e61000d046103854503042014600f170041d00d02c0c42240710000c0d038846500c503403030349401240c40f908050104190b54032141c4110071284002d4a850085805000156200310005026000640c240c0c4665815100d140c2c60003c848035030341c0317092204541c00c4004600580b60501d20b80c01904203500c40a48030110258020102c603046040a4407444c00103850000c01080451038a81407007051520603500e5507200980d4001c0d080764000d0414180c030000f070004025a0086004041c0c03200c001c000e20884e20010104224080b5403040a0900386844030308000c01801540e60260313040060059408042d02c0751140074104004841d0440c0303c1c0c21000b6021461360f484074001e20801c00c3c048082180b0004200404d03a90000181030342a1003400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 169877922 1250 169876672 169876687
    0xc021b040f060801110a030612031e030e1203041e170a020c0d050102040501080109052710050f0919051c020304080a0501090c0b1e130f030f03080c0a14 67
    0xe50300100c000d8100f26009011a002c952500784043d407080c2c0c541000030345001c0012030b444100e01d625204480d09076850000c0d0300048458206009020355040c014942d4600c9032121810090104c804005103400d003064aa182504014030f00b5040040740c4000c4c02089081c000000b50341c8107210742044d0811100c59150014a4020386c0f8000901403419440b05540056004000701500100290780c1c0a0361001800c1e42da4051000079201c0560300182e2141c0e01e42c0054900107082402c621078142c0034811540c95041482e40281101c5041d90320440030302c504420408601c00130000540390f802d204013001e48100882d01c0701743c0c907000041040e803207a113405a94070b1103ca1003041540c1c0a85030703070700070b0318030008003442d1150080042c07400440e0040b0010300d00140c9107088205580c106e1440211090021485122020269201281c06810403106810104003540300c1802039025500c1060040d140b0b40c1d440c180605501d0740203050b0414240c04001040d0070541c82754201c0459049142110f0300c5001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 169879172 1250 169877922 169877951
    0xd03051008060109020d1404080d050a02041809112d18070801050f0d0201020a0312020f0a09050f0402070507060f09030b0a021e0906040605030603070b04060c05010c021b04 76
    0x140d0312007501440b8600010505484d281c0c02441101b000c0303102004444000304010500400403500505038070018051415018601d07001340b507100260803030052a25840d03000b40543d0100e10304c5441002591190058208020003030700c68055101111426216949500130440705068400f8120143c16949c00310f807010740f00d4600b002d84480300c0f000460102d01c1c00d040300a040e4a000d10490707100380c210050302c080c10b00f01110f201d00c0c01134060340541456159a1426614283c2c02c030680403110344e08009a90346800d2142c05404105010760300c1c8070800d0303d45003c11040101008485105034410000000000c1001508000311741c0c507070a201100000d00c0c40305035407048180d4006000c14070b0950400449003665402003421507418012480444005015420240110384070581c04c01000c000501505000d003004c0c60340040020100c80b41e0640300d904011030768005a2002010401d501582d20030008280039244d20040c03513100502030303c04201409582002c101c940c2d00d005a42e200030300d648021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 169880422 1250 169879172 169879201
    0x106090f050f210307050d0e01080f090a051c030f022a0a050105040303241404020913020d02042607060309050a0c1512051003020103020a1b0c180e0d0305 68
    0x65105104030300a0a0307094500b43c5981c0204400c807114054003003412501f90141d90751000210341039448400f142d40740b220b107039a19030000c0d055180a01c0340540480020301c0c03c025000d08d0000507041a0003910311042c003d0240d5040c80041940540140102c04020016a185000d1142c02c1c0e2410781303210301e0005c01d00b8280450b1002c054915405e007410071040c10340680200d05003c200c000c90301e1101e40319018001c00b0500c0c41c0520b50007124851005c18241ca4a40c001d461009401440d8416038007580d00e07410101d81c0011045000b041c1c01060070030a8041800362401841448041e01304070700005480140c45241a001d4182859078800c10601800020400c0d107012a603c2110398540a40b0342ea5030030044251140002c000401d004110405500300307005642c002c0881e4a491500141154010360107500f003082d40c18100202d02d1120f219100358207510f05a4907000782224070366581409500841a9881c0700740c0c0603000d04000c11054841800181c0045a1503c2d1900040a031150b80d000d14208 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 169881672 1250 169880422 169880449
    0x3022203081923090109120c03020910050d12020f0307051c050405100806090a090b130512030c0703140304020d0609050c0a0602100b0312160c0510030b0103050106090f050f 76
    0x250780042c054201c40340034800130007201c0001d8a0740c108940d0340c2d018500d200c580d480c2c7c00030080d8065503020801820003054150304011100400140a6200c6020585004007140265030460864100c85441a0180300540100199001440c03a04070740da180c41c0d80e160086001c0d10b288030380c1c20070810222440b400c145d60144c0802000c5444070311b0318103402000540d050360340900c5441c8110100e00c8030001c600c5612012688504c40140b00d58814100300717a0101a03240c00c3d10580600503201c0038401000008500c1400080200d0351900c0c26424000c2c00329008841c0409001d108000b8040075944e8240b031030000e00d9011f100410a005107140960070b12800000060708200aa240803030500c3e008289980490320822080044100719810181e403800350654410170400108140340a1407900b1400c8071b021401a604082c180d40d940000c01d5004045500c4180026994000c3d00382e250b901d03000d1240101824501400f8640c100403404104464601c1418800c01e0311144001c99030b162583c090761803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 169882922 1250 169881672 169881707
    0x9071d150306040c09080c060708090a0e01170a080906030a09080313142d0313030c080607020c0102030307030b010c0501060308040f090204060203030a022107030222030819 76
    0x50a50080c0341840940098910620950030030410280fa10b11841910b07003100d0080005040158030681400055070240c8800d4941000030003c0390f619445541080c5c008100203400e40700710f58542403c25180d01584110202e0940119a1010100700c859040da4440c00080703d240d55207481d80c40d400301c002c20b000080100040c1001c81004514600c01c0407940020f40210709c0c580152440304403c0313480b00b514211000e400260070b1905a0b0301c03c580c41090050076400e100f01d034509001c4140c2a000524a6402190078402e8408148600b0009100840d004001400200524500c8200207500c90000034824410180d540f64052120b81c410540e030440150400000c0051544904000f881603001d8091085a82d490303d42c001500c103954800c54080b00d00e158003442c00d45d01e40544110181d07201700f80c7c0c0c1505030010003c1e071803a1004100e50034040caa01e91401669008071082c81c1c19410b201029001110030150070800100342d88000b110055401119401c0c13460042903820f881ca40d60003042d0050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 169884172 1250 169882922 169882939
    0xb011e031a0103090f06051e0903090f090f1902040b0c01061a03070c060b04090503160201030501090b01090302090703060b030907030203010524120f0d0504030209130209071d 77
    0x51601075100c01200066121060500072070380006605440310220010896141d40f1100f174013184a90740003d40207145041d249049000c0e402d0010010035042d903000810b40c100155600c10f80c03400c20702c0d1041a0740c0c15070740c4010528000d030030703d00c5594005150300014401440302c3d1204003400d50446028160701200c50752603640850b4094024402405960402d10b2040b0003503440d0507080050701c2c0700d24075583d40d0941924042d44c0e00e1001d00a0005100e8205448000e417000186062000e41514060014405e00c2442d060000400b5540182e01c90201d4a180c03140c0d00700a40d900040500940b40c043e1070180007a2124001203008110344c3d4402c241001d804004c0c040484808654201124001c5009001a85482c0503950840c00800060b550039008081100d1881c1014407445102465150a40780ac0e44208441581000c43d10000b003800100001818421071404003601500002e01c0403c10103a41c00a9000c40c004031406060401440a000c024100451025500050926019084d140c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 169885422 1250 169884172 169884227
    0x3040305060618100b09031203040803070e0a0612050c07060e070612020909010501030c030b090112050715020c0d060e12031e04020604060f0c0204021912090809040b01 74
    0x161600020703205184030740343c010001c04018001080d0743c1d00410042522210341468400b440d034555001d10149034043c010b2204e00c2c1c04180c1c41c20081d61099000e8880079030703289406200140b1214144520b9482140ba00400b440300c3c070b5208900d4881d10b0740d20003000406c2e0b02d40004000c824056040d00404107400e21450100000b000309030350701100c2e040d40781d40c01c1000703203001400164010b400d151070b0414402070040010b980300703401c040c0610078941000101c0900c85800704180321b009030401849146403003e1103041007020417103400184481d060707041113801003c03c02512840441c0f030f803e2007010340d40105d5050025961142400e400c05000712203918500814250b01908102d81c04612110016038200c1c2c0090031006840c4641e034020089454181800c1080c0d03000740d429051007080007074501e660360050b226071004003031032001c032504889100100c49006205841075445401000c0c1030114100c0000e90310429603d01010448012035003d644400486500704090318a00318841c84143c0c82 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 169886672 1250 169885422 169885433
    0xc020d0803090a05100623011206090c1107122409030f170402010e0909070f080109060c02150103060f090b040f03081602070b0903010204122001090305060609090c03030403 76
    0x2483d15a115100b030f44d000b201e044080504458803031007466241000d4202103040121002110b4248050504003803100c2840410303407070f084800c00c2c1c1100d031802c0e903101e000341a491740240c4121004005c0c940104007580c200203082c0d542104020000784030340600b84248848003c042d04240001415840401600038076040041910b50801412804920800e8401a04640d1505050711075070301070f1a40394800301c0aa06001003000c006100c40d0070341c0101784020414802c9070103490000c0c4424000400c9140b0785040c0f007001c49031003143c801c09649c007030080c00c0c5400d00c07070a040a04482d00040005440703807480c003610001e4401100020811000c1c2c030104030811907415031100046000f5960750205070383d0a03882031022070b1100900c0015a005060810001c1090401006103290240016050940e5995003e51002c0c114008680e400001146501902c05100321144418400d1811843c0a869600c2d200e4442d8809040103020f00241d80024000b03400c20403101008070000350441e03544a90382c0c1000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 169887922 1250 169886672 169886683
    0x4141017090312010e0702030a080c0903010e0c0901060e0a06030b03030f0a1e02030901050706051005090f07080f04020d030c02031203010b0d06091a090417040b0421120c020d080309 80
    0x40c03c0503688000010554020b2840f40f213118a40d160000d6140c0b4415a0080e03480000003048254501410481400d6035102801071700c0004485000400f420b401e40d40400c441610160005c2c41000344a082c090700703650325070b9140412241035040002e251034840d4046030442c416a4094001042c0014071004d001e507202031040d110107a10703265440f44d041c004100300d80f284a2a51043e001400c1801290301140c6c107548855000200c04994480070f65954020411248080300d0000019452004114119811111456204240701088100c52402d0b82c00110708141da4074014041088030480242152070070490394010f050415006500c960317440038204500e43c004941d5003044e90601c00c0001e1014058040c100500c0d030f200480c00d080d980380c18140031711504000c2c8241c403a03413203031010040541110307030060010b4071100c0c012594503030800f0003403019141a01491001109065030f0480483d6a10120180f1401640741c40280c146950000a4070303010080380107080c1800010500c010311000003030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 169889172 1250 169887922 169887937
    0x102040b071b030503031f03020306040501020c070f030b0115030e0609011b020a0b0105040504020105041502030409110a0801151101021b07050109030b0f0606073203041410170903 79
    0x501100c8a0b0340d42440d40c1150002d00c030052896105201143c40d1008622500e0300031030362400910352081c0d481c0c00080c6400c5007a2000e0720740743d50020b0b83e0400c504040c420354001e003101c01c5607016402e00c2c59a4400200c42d052081301c08803040c050031201c059101c2e40041c401c000300e220440720141400c1c40d1203402814002c215002c0c03070310b09816400322a4000306846a102c0c1e0032000820240c1c0c607200a11000d800c00030022030401601b00408903141c1c51f0a0100d0040c940035500450300c45041460220480b2082519114540800d22004a03a240e0004040d410340e900350798952458542c0250130340720001d80d2444c00f55154008502c6051300c1c40c0c0010929802c448171400c45000d00c0d0b076100103654201243c04087e0a41864100144042d0716558034039030081c0740940000c1c44c1043e00e072a0840079909024010041ca90000c0c0c0d0200410b10300042e032044c4103060000303549820701d841341d40d08090300c4582b5064000e04400c2c3c03d406003d4026409201002007030891951a440d001d42d60580702c0d0700c07045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 169890422 1250 169889172 169889183
    0x30e1804150c020705090a0f140403110111040509041b080d030203151c0b10050d1202060c09010905010c0c030c08100c020316060506130c02010e0c0415030f0c080102040b07 76
    0x1407041e91183c40042c0c15002c6607800b42030f901003610340c04000c80141100c00552564540c5a032222a0803500c0d204105100714000c3c0c0d0390300000c40c402c1d5000e6095030b20003031001501550900007440707190b607500308140c2c000b5400080b00f002107060100c0c0717800950b00b40c2c1c8400042e02131001c03a1080c558142e0021482000419480f00c03040f03851108001900041045690302c4c00420010100040d00d000310254012100d980000d101c03075914400215524144d4100719070f030282c40c0c0c144c1c0001c1901080169080861060414200220440020f040c0582c920805040148200d142070901850a00c070201a40d01320301c54000320f544070b0023800d40c0c7c0c1c100c142015601500d0282d010303404610210030b4440710102046203641e03c00e1240c6541001d4040a0115a440000340c070b00d03606031040c0392242c2803000b03101c5c0c0c0010520304401c0d1400e1742800c0a82190134022030520f8880080341401103c0081520340c091100014002107007419210b0501a81180103d03620010340450000c21240c0641301152044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 169891672 1250 169890422 169890431
    0x2060c0a03030506040c0f11010e0304180e0619090606050d29041a0903310e192c0a230c090603010209030303010b0702090105120307030e180415 64
    0x41c080c007084841c1a140100000c2d82c4100350300c7d5444c0f240101032800c44410001043c02c83c103600c110781c1182d0190384001e001c1c1802c0182c2250f90706460090290440c0b14801900e014a0284903000c0e40403100000709500030f83c0d41180b44108030140c0d2207140a4500039180b4841c41b20f0500d0000d00c0181c1521031011a0848018803e0030b02e01d04036183d52189a10500c04050308040425204072070702c1c0a440c060160000307110040380f10320b054014004c41b02425441c05010141c00180149101c4540c00c98036003074407141c08120418801c3d1382030780e0394a803100000049aa400804512a05020303000c45031083c20a0306907007922090004120710a01e000f42401d80003011488402c4074803143d004c948034400e42101040300300034988411500da2000c0041e0000d441d1119650000342541c0c400d810441040700041240000c0d401d09210b403a024040980d8224202c061610303e41d070f9203000b008002420420a41c0c501007254071600d0784c10300d0b103c841907a074403694145850140c0e05440d00ca1401070b40207241 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 169892922 1250 169891672 169891681
    0xb0c07080703080d020703090506120f070c170d11040b04050405010b121614070605090105070201020a120504031808010509120a0f1803050d020604110604060e010503060a0302060c0a030305 83
    0xc5169412280d024030f01a150450451400c000313900310550907824422075890004251303c90200034411103940b8004031071680f81000c0e006111800c0039010004101601760b20000085005c10404c508405500c5905d4540301900300740c00c054050b04070001c1950070003081c000380b06100302c0080d1055030403c46090104c2e80c0c0b146121605030181c820b1400f041d03406000820503240450b881250808000d1510440d400f088007070741c600300da0004c58112801c550320820081c80300c00a100fa10b4014040c1d200039403074488001c000418075000c080c0c11071040343c1d1b0b40020070101405010a10f80390590310204c422180da55503000c500901045074581d405004d0354a111070395001c0982180c420310300c42d458100e100c000c940021601d038440c803500000c04a412120110104000300100c0741003900c071398020304480c903241c9050f0b0b07080800101024058081404117200007604002001d41a65007840c00302c0e207a44c0c0c4c210000b00c86242c2c640c40a504400005040c4207100e902280450110b0f022752018405502e9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 169894172 1250 169892922 169892939
    0x1e0501020c1513050306091b09060a030b0a0b1806010810050a060302090d06090c0302010908010c020c090601050d06150e030303090a0f05101a0901170a0303020a1103040b0c07 77
    0x641460059024036142030300403010a0304009000c070100032108050b00f594569001ca882c20300e094840440f00da100c4081c0580d80504c0c40c02c1c80340e80e501d081d10302000900b480300100c0c0f9800e196001c0201010b4000002802c900020380c4181d06038800201329524000300040304100d001002d40e44140003610740c2c0f000031031200309140c0c4241281c1d0050b1201103e2460117108030029000344003d01d078011b100079a010046640d07400b03030005850003541d209403403914510002d000c003c110750110101e6418061110240e0f900460844000c403000e4400c80c095a84c1c00e00121810311820740c40280d06446d00f000131030145600036815014402c02d840304078046461400f00359485c00115101d103407540c0444c2c1800d00007212150407030f03e1641300381c08450344d80c11590310a82c240c5194031451035084203150f410420794074001007254010141080d000c98101c03080c040c41364403a81c0c200c1002c0c0c141a0001108101c0910070401d22980d801d020342540d407216114883c10009a1007000b96104907c11101d0114403440d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 169895422 1250 169894172 169894183
    0x40312030209031213030f0501050f0912090d0201210608060106020c060d0c0507020d050307110a080c01080603160b0403050d090f030605150916030c03050702030a0809010608071e050102 82
    0xc0b00203001304188070300a041c1002c15403100317540c1c202c440b644e050000002101c2c42c4002540c00e10a2002043c94501383c0080d11501000a00c00100ca602003a405400507213201d0403a01d070450142c0b000500340d0f54034001a0340302c0034404034181d800045810b80034a6a40260301034820f48081d90140c1d12966a2083e00b00e86d2105800c0880d40d00550030401c030102680507620140341107000b03007016414645a80c0010360596448042964290000075290b010000031703a1060410b038100316041600b09007410580d070756441106015906008400022848550341003140350381700250300041c9240251100104c840c96040351000f1107040c4241d1030740b0900302e0b004407604015101c195054640a17480c0da21000040c02000d0600490501000c2c07a078031050300c0c0d010340d075440362400350701d07255044c0744130140101141c4001c0000c4003058600414801d00f00d6002c4100e42c400281c51402814076190209034034010252a405403c1510806500013547c1c1940040f075510054000359420480d542d620040e6102c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 169896672 1250 169895422 169895437
    0x904110a051203090307060e010512060a090c0807080109051603020c1005011403060c190c03050d230f070e19090504210203130504110c1605130b06090d1a0106050403120302 76
    0x180b2b043c0310002c2c000e0000b02d4602ea0103000100540c801d50b981e840b801040f101c2600e0000001a211000c01507525040b06400b801003413004000c00c0545044040400048200c3d400441010b130001408110b1102c10804041880741548003041036580d03440c3d0309072610683d190043c0c024002d078030003d00c10140e000b0a80d0050341000441c6c2100e80c2e4004802c580b0448041811418444280003480c03109030b461140c1c0240c03d8224035944455a1804c80745198590020700468040c0800c50812030070960010407540004015200b03003c90700c20f20a010615904c144d0482007280c0e140038108020b014105080841d4020014660b030b201e4212284101e840340703c0c14000e043c40c828401c1e410052800c0a6219609800c03901c100c1c2d50403c1d001c004620b0030240b4070303209260340b484c680301c041c8007030710f0004150108500043d4007044203000c0c101c040707811800303003d0041d07118000d42104d05042c059188103441828441e4030012500390307103468000e4110f0300030b4041501d01e00100c0501c00b140b0b50113442280c184 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 169897922 1250 169896672 169896677
    0x221410021204050103090f0f0c0504052d071b05070905160804170c0313080106080d09120503070c060f1205040302190302030d0c0309061404020904110a051203090307060e01 76
    0x2d0609140040d4090a0b44010445460056090000204000c10341000761700380f240b07104081c91440c1000700010b4510203031001d450780c403902e40e0f540d065010103c0b106e5214071070008151540e98802c8000d940c1c4078228850b0059282000f002d404c00c00002290f00010744441003001c0107181c0f640020780c03082600610444000c5807860780410080380300440100440384000d004186003900d520700075800c5410803400386042110b107400c10b011490003030081c40043e0041c6c1c80103003140104860000c144032440d124655003c0d203100d442c00d003403102c180100c88515070015000e0b0640b66440750000c4c0210111200300c3c00082a2000c1c04000180030300032280525056802440d412410401c282d09904c4415012029880108485204000c0f28082c07038200c1c0c002a14000cc2d10707c10f6090000540e41c0d006500495250540100001aaa150008d5811942001080c030701c3da000d141c00701d07a002130b00da0000d59100300300c104004403070712000000f005142c4d016000d948400ba82c3e0101900c14054070a0054003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 169899172 1250 169897922 169897927
    0x18010f060302070f020402120601170910020c071205061b1e0a0905030607090e0c03072010090f060b0d0506060d03031401081e030306010c082214100212 67
    0x5152190700a803c480d4042c81c3c3d0212410059800a000c13a07000c01800341c150000c150401c80c07e507800900404107102060300440322403904170340064942d50a007005840865011611241d141c82c00c001e060701411945841105401075400e2050b61007000301e03190500d00003031420b05141041070300c003903e64141140300707900803030046407580101c103030409449d8070200074401c5400191030b982001030b1070185070613842e100c80d55400c0a82508869000034000303500207500300300740186079a102d412042c2e5844580700254240301c0b42e41c3c045091407040080080c40034100440c0e42c05000c04002d014040910a010402281e0324510900000111894028000380c020b5000140c1908004240380701c020320a00e00001c020650440100f6005c000f1f801403081c60b48801801c440540c90028020b0503110600c0045055250000000703103c91f03002203000f4001440420400e030b03981a43c448107440d82d040940c11010745030b12008559500d601d4083c40922910401d001034100380d001141124203018400382c2c00d407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169900422 1250 169899172 169899179
    0x120c0d05090f040f020903010c0e0a0b0313060e0607110d1202090312040801050907060c08090607080408010207050c010f0f05040e07020c060307030b010e120a0b0a11071118010f 78
    0x903019040524499041003407400c040381d15a8031441945290803d98100586131440380083c94211459092000103004e01e00c0401d020a42c1e84861150880d04080007465a96992804888001d042d0081c0108100e0400b1441000b01201094051040e5825a2503076084d84030b00c0341079560380900d0491200443e40782500c1034480c0070544c00030706001070701404442100d09034801d40601c40c0d20980c08620305940d2042400030080c0c2c1803150100601944c6446145802d168684d8240c80c800c05e0540340c881c04002900078200300c2014160740040c40940c00071500d030007503410038586581800c0c208500058850685a081c03601582103501006e074070381e551908050030081116140000a003845040d403195400010041d90340c0e40c0103501c94580b9560210307089205c14000b41c050b0304040d81ca28440c248800242c400764000217818400a90003240b12255502c80e29950b800a1681d01401201c030a0006034110030300a50403403100328100140e9a43c0140100001c0c1440790311801c1c014068480300506081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169901672 1250 169900422 169900427
    0x210a0f0806060412050a170f030c07050a12050a02070602010204080c0f03010e0105040311010605100813030e03070627030804030206071106040e19051012140607030e120c0d 76
    0x340d071061014000307914094491002c0041070130148400c940c1940050003d10401416a900100c500426403038182420100483c0d18241c1c04002c1c40011b0440b008141030050000401c81948065000001c4820a02c030340c000051440d88201001c80161180950000c1c06a10500c01ca408071901c2c000500b520015800800052285e9040d9441e495074032603c03407114240c028880c003400f130f51186d2208014015801441401e44e030165000c02e2085080c2c1d800030030040e800c0312407681d00000c2a00d03096500002464203441940c40daa0300a5014840c511020503010b42045800c1442001d0f10f8610780d851928500300c0d124a01140001880c0c9041440708100504003075020704a02d61081300060740e40800d00012034460b8201d80d12250881c103041c024002c01000c15640020b074040c0a00f014440361030401001c0703860400d54811350748883c0310003c50a0601c4a200000b050220280082ea80d080c109400c0060241c03200760b5640f5018041e440c8414801507071041100d284210701c0c4003074824015a403005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169902922 1250 169901672 169901687
    0x70c031409040f0203070804030207060c03140d0f1d010e06010b07020111030f0309010c080604090f121110050f01050d030906200f061f270905060405210a0f 69
    0x740c540242c0c5868901c101064580043d5104560790b6840d10502c0c902030800910305640b0f179000b035061142401d2814040390f44512038031110002c105903181c2c0c2d040c20a251500504201e243e120425144c91106961041c41800c050f2610304680000d000302c080340d00400d510b9020a2054100c6154200081c0c2e00550080e01f5140007000d486003640d040c420510301d16012a07000702e4980b08503955528200889580182c0300d00d41018054600300808809070340c650700c40140e414001b41000301c1c14584a00840e00c201c04441e85103621340181d503824203003100c2e81c2d409444241c54003421090800000b14032400c3c03c4c0170201c642601980c4840e03215152080a503129110a6501d9110a405002070f08503010200b156607161080d03800100101d141c00e01040c060010344400048041020400800c000d80190f1380000c0c03000b0414118951100c4101c400e00300510f1048070041041c050f410402044c0100425003041641c100220000ca0600c80000b200d0070303121b10580800443c450800003005144039610 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169904172 1250 169902922 169902937
    0x50f01021507020c030d1407020d1e0b090d0c030f1b1712090d020307020112020d051f0509070504171e0706140906030105132304020108070c0314 64
    0x1941c81ca11a004601400c4410444403040541d1086404401c682800c004503440c0412900d4a04a081c0c00089620511b10680d80d0280c880e841c4804048107001000030f05c1017000d28412071b55a1141c9003803804610428088444a2190084e528480c040b00d005105c01095036a0560700d1101c0010515010340300c00806100b0b1062180035003c41d90006040ea0002440403419001c119440d484404510546039400034405015a00070300d1a41155a40000a40b114168242480d072403801d03078819444000d00441c80910318850030039080c440300c0b02c0b0803801c90a0804013039a212a03901e44800501080c1e80d000d491030000600c1c00c010400280316050480000300ea50142990949000f0018600488003500c9941d207840d0002201046003903001901d008601007101d100381c2c14620305400140a6000c1481101d00034420449600300c1104c072503000c150801040e185e800208400c2060382200f02800b00e80803408156842c001c10030141c01410190f4800d0390607903c50014082c000018502a00500c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169905422 1250 169904172 169904177
    0x30304031401060302060a0e0f0f0310020c0c0901030609021f080c03040212060403030e011d1b0a090207080d0501050105070b0127020403060b150a120c0c060e060a0f0213050f01 78
    0x100c0100044e1ba4040c020000003c0f1617584510f100d0501c002c02441000b14040c9a2054400c1030200f86542c801083c0c840c0300803206040141c035039042d1080c0f00e080c01d00e03031441140d00c1178a010004c4208206c0c2da00c2845078900036165081110b0310713070051108542001d0851030101d0b6000c0001031090024a000390f81c014409401f8141d0040032040f0300d8541b84081c5e90480100ba06e80d009080120000d1048503015130720144003000300150f0040c40c03074590348a007500800136903241006840e0383d00c50404490003480c001b101103546080b00e080540d4160000151040128200b000009480d0300c518290350381d864004034103544503403030101030b4000c00c513007980d88196130101400400100d0f1414405040250b0203210702007103520f0703544200031440c4040c1d1582030800c1001d10031500c4090744a042e1105d001b03c8408002442401800c00755807445a01c0c01c0101010300f80241c181c2030050214086014040c4c110b414010440c0300040e9600741d008059403440c5900c1804010480e5107818004088000b1060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169906672 1250 169905422 169905431
    0x70e04110d05011811040c0c1506030f0501060303030f020304050c0108041707050a1a0c03070e01050706020c030904152d0512330103110102071509090e0c030304031401 74
    0x70b81d521400d5803420300498100d4a4000c22580501c40c0403a41005010012030b07080080101058001d02140f0400602800c8202e0008070021b91602552040d0081d40e00100030110200329803500902902076400114002400d00380f0b620752520943c000c0c3c81c015a4001c5c050038072008d0017001100c032190020025507401071345021072140841c50600a2a100b400780010f007804079014242114140c3c0300d00c8807641b20032046000c000c50b584013035066a802c42018a8181140c8402d100102c800e0700820724082c00140c80010b400307116000c0000146603038102a607082c40021006d40380207101d0503541c4151004840d1403000f110004540e001c2c44100c0403220111051940e4586c0c021406181c0b13611114045031303214400b00c2c003d02d51014008540070384202218001c2c0c03d0f483d841140e1405040c0300040011207031060040540e0300a00c414005440a4070811100ca8005007000f450058540701c0c094040346481e01180c414070000c00d007800300d8038025006501e03041c13440e07440020501d49500340c07812555a9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169907922 1250 169906672 169906699
    0x10e1201060f09020c0609030f04260105070e01020c090408032e03120909060f03120219061d0f070b0f071b0f05090708070e06091818070e0411 63
    0x510b03410740003901c81004010f88078a0003450303079071403e90f001d00010802d41c000e00120000007650f004070303003d54000c0c0700c2000d40080312034007030069002141340c0e080055082c4400c02400580c40f0403201a00d050903400c40d52642101c105120380c00a0031788001c2c000c80010130004a030740c50008444007000019241c0303d04223003500d050380146203107203400480b00c08032207101c0080408e40c0451010302800190741c04000c0f40c1d00c1d0000303607443c20034140b000600ba0606507082585043c0244002d015409601145581c0303482e00c0c1ca842c0000308044014002d0002205454018030600002c400603412101c0340108091410f0880c851021b411440c00f8110a980c00c20001e00010b025080304038104090003a442809820144400918242074001d24051150314041100d1181c0c040e00a640180040c18015001c01c495008280b00d441801881c80d000010309911030f0045800b00e8003a44540e004403401c0c83d003800c1ca0803100d9100d0b0f030386100717043e00314100038003041c00b050741981401001c20700240b0301c1e441c0488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169909172 1250 169907922 169907939
    0x10e030705190305120c0706031509150501090902090a030f14071806050d05030304170405060f0301031401053c0a0207020411041503090203010f050412020c0f010e120106 75
    0x940708040300d070b910000000308104041006851055031544002e5030901002034102e41d642d01043c0f20f61810551540080300c50030002803294806005010b0080c0100c01c0041d461202d01030003441203a0002c0d0740c0d0400054030013458426103a03402d600412450300c591641c1c84c3d204000141c000b058030303180306001c01030325881c0d010413a180041200c1110340c8000d4541c0c3d9040b41c22960a584646c4c000e55103844400001500481100c4d0300c40d520030300d009080501c4000060050007503406c11038101030b000401003541c0f00c0f004040c604036440b07248001000501714510b1400e840d002e5800e0400c45029440700c901c4800802c4280f0040d08041c40c0400c0c0d680d0083d0034070714441c0c3c003d4400d24000c5178001065401c4d030030640a0495115120441c20340307080e1400b5040e40c1c52001d02d100750020140e6409500c81195820340102c15030b807001450074000c505007403c141072480782c2d0700300038805403040e030028901c0e0b0301f0442054004080140c6840d1800740042050002e208500c0701c00c0d6565544e0fa00003c6054003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169910422 1250 169909172 169909189
    0x131407020d08100b0a080907050301020a050c0606060f1c0e010204090603021305010807060513030206120106090e010303020c06030c21070f0306081207030c060c2109020f010e030705 80
    0x900c0d030003801003450040e0040c000d1000505404020016040103001d0703144048100d400f1000c0e03501d080c950556407820307024101070464001d5a41540009040000c0961203006072244417600e02c1a5036084e00c49200300040c511502c5080c1d114840c00b400065804070140104850740e040e020800324110243c04c9070503089900c203410213504566120030500c15030a0010a81c0580f44080c503003003003d9410304410b43e9581c440d52040740200203000582e540c50028183d0128000d540c054038032511400e540c0d800c06042c000c240907890010395100c1c1e00103000303c11540360904994054018150103040c0e0030a00c01154001095403040841c00c2000c611000c015440381c0a49905010075255103080c9104024404401d488041081504050301809100e1010620201c0343d8080c170b142a03565025494151a22000080c014055a141c0b0a50042894200300b0000c400e1901020300640c400040003a8401c48024100c060340082134113000b0100c550180d03036400d021480007070446070b1031a40c0e200029841d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169911672 1250 169910422 169910431
    0x1203030b130519050a02031522020f03161b020108070c05150103030e010201140606090d230c10020607080619030317010e0f0408070804090222050402181314 69
    0xc1c2580081c0011603c0600ca01034002d21303c4001580f81d401d1000101c915441480580d5110785501c5800c8080340300a411076110ba169405815074568000e10340d8803081c3d40003141e007409201000c0307909000e03040c0301d00c10fa822200c44203020144d0860954004440c1c40707030014140b0003800412091000440e804000c00b107210b8090342e400840701e6045240081610f104d511006040da070602c14000780c1030109201003076000b0f10580d91540c54800032400521917044003c409002040501202d00f0510809580c8903880700007401250f0000583c10188104140607041d1603005030001c0000c108050710412119030440c0d4001c2c0701e030740d4810305c0c0360a001514030340e03900c110040f4811481007110f03010386602c00d07401003801c048030840c185015041c40d102c09200034401040040000744003001c000131201614050040d001045440d80f07144103e0201c1c50420f4250584444504032001a540c5402c1c022103600c0c5101c0c550035503122a81600384042041512607a140036070301e45e0307c4c240911010114641c440d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169912922 1250 169911672 169911691
    0x121202040803030403021218040f141e010803130905070309020306070917030306030304031e0b010e0403390c0302130516080103030c11030c1011070503071203030b1305 74
    0x228113040c60701900c0d00c09a88000c0c80c2a405c148825030610a0000b80d03030000281c00d44001c10003194200c20500106814900c100f60145d85d901030203039007181d000d00c11700000380b0f8096040d40d60347c07100c40d200d95a000b00a00050301509200084c00060640d030401038004c9450b040c0418013281c00e5000a040c10700807901c282c000703501e00e1410000e10280107885031540c0e004001075403460a140005c6910381c852404064a20200114031030b0304120401200070019410100705861075031507800340c40415000380d8045d40020a65800091842d0322100c520f4294001c291840d0300c8403425200e12440e0b44194007096555400002d00000940c5400b0500d480d40d02001d00002070a1402070018603490024554010403c403401c030041c00000d07003201d9034a21441d00300f804104614070743c1001900d462040f4401582220404894210054002030400da44d01c404ca01981c054649480c149651071155115800c0304c03a0f8401d403d000440c1c020307401310790008005003100706108000781c401c0064403000e41e1101c42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169914172 1250 169912922 169912927
    0x307030e0f10151d0c0a09030605040c150e01020d210f020c070e0c030406020904110a0c060608010b0a150908030a020309101d0415210c060908030403121202040803 72
    0x41d0f500c2c0601c0c1c807501030440b26040d118209441040003026500080c406410040300007031054400d405034604130002e5a06c4007040c040e0303150516114950100c1c0780304088241c0d00c1c95118100040c054a010ac00880741a8000d140e00405500d040b50200071019401700c44004942c020031801c61030b4000e111408200500260396278003400685494085541d00042201c03c2d140d0a0001160355081241d80280d080400035880700d9801c00010014091300b1000c0b4410100042c0109085402c10400940036004d010104045c42d41c1e9840242660b0030701e18100e034000c4641070f0a00140c4090f80c00c0408954843c03412a512540380e000342172840c0c1c02034040c00023680c030100350400d5914080b1900c240b40340c40d502e40110744008030020308060036981c1110341d2281c0d45840215131070141100c106001403070310503000d4960b0000d10020001c0301e40107460541d0032000a010100340382d40241d030014100d070300c0030b401189403a01e15100c1c2c04070811842c081c1000c10120701c0075800c142d081741c00900f01424008000d9603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169915422 1250 169914172 169914191
    0x303110c06100806040b07030207170309010902090907050a030303020f0921010f14040f0f170c010e0a03020c1e06120f07020a0510020915040306050720030307030e0f10 74
    0x80d0a1200390f4480c00055200c0c3c07003004006180c0030036207601704c80103080c050303220206440c1100440020b80c1d810040c21030007208020303003040150001a03460703000b40c680100315120b44e8004c0744c5440c020302034030744c01815804042000901c240d0090059880c502c1d186410b002c81c0074005541c44000580108130011000180c18604000303104490180780c881004100d07140c4070b0803517085040310050000c0e2120724141846001d102e00a2000b40650354480101c0f0030751151690300305055009210840da2941c0780c0304000000080008950071308640640041881a403280b0802400189502c03d00024615038550300140d6124400035000004401c441c800051601003a82c2c0400800200048110341c04410701d180400e030007203200c080080e1820809642c0302c5a80d008941d9a0109400340700c00d507840000c000090000e1030b8419030080449980e622024038982e202b5000c080c401c9280000b440d0401c202080c0c4043c000c3e408801d46403000c40075924513202c40340900d0b0070118403100b44080151140f5046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169916672 1250 169915422 169915441
    0x60203010510050a1e05190503100602060907030b0606040b07060902132c010212040807020f010822030c020306090601030b010617180307120f17090c0108040303110c06 74
    0x2500107a01840c080e42003000d41c0800078040c108014100704114070145c2141a018410000c480d1550304c24007503801e0303403c51240d009040350700483c7c202d00c12050400c2e0104031309101284850203819018000d040762313421521821040170000d80708a03070016003008009046c0040201402c05140282c0c00010911520300500c81214440c40d042c01400e45400481400440d40480c0191040d42c61483d0050000401038214024482e02484510181d4450b08100c06c01c4410001444038a2090f110401040400f0b00151002201a9900701c2440003c884220000007101016904c2500034584a0b661104607004039080801c02d0f1004e40311508580010f01c140300c00740021500603d01791505688000a03001ca840d85204090003200400005820600c1d41082c100140e030001e40d04000b110903907856641019162819a6042c007021031504900c00580c0c0020703496103071103a5402c0c00903101c066070300001159a010b004004609150356421079645040001e0050071140301c400000b8050307400d02d402d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169917922 1250 169916672 169916689
    0x60607140106032006160c05040e06040213060501081305030f04031505010b0906121302060c0d080114150a171807120203072303060f0718150f090902070602030105 72
    0x5103180107054001318800380c41e00780894000649064281205405070700c0d00c0c07401d40d0f010b6808958094206040c441c880800816214041e0b44200ca00c04540d58503d4001020347d50719104d0180404d1521000030f0140038411708c0c01600c10310400a59160240c84041a01c0a4100d0b810541350380101070265110314201e80b146030301414005ea102828040700b1750006039148241d40f204400480b821011070103000e002600110002d500500d030503103072140c00906c15511500399010800082c8840000264009130150840d031117840079200c000d0014a01c580481c141c0e014451707600c02c0202a150515040819a5240740102e0031800c8031158410000011464280b040e0042019620380c00041c90040c0d40c00a098001c45060103079064000c91298800314554928940e19601400b074001000300d809295010584030311440d850310140c01c1107050f405545402c5500805400a101c0c5c560b4171007141c0203540d03070715001401c0c2ca020f4a00b142c80340c01550981c2c026000460b402e07500400103100600d0305962 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169919172 1250 169917922 169917953
    0xf030a0207021228050102040e0705070c0f03022409040501030303060602070506031005330301050405091f110904090b041e08030403050306060d05090706020706090b030f06060714010603 82
    0x20060300300f40d54107004031082010f0801e00013070a02c120540400c0800e4055178000d055031071083c02140b800c114098a02d51002c40115282c02da00140030800400f442000015030b81c02508400503800004c035280c903540e85410b855910100c09200d0b203900350365903002d510301961090382c0c00320700340d4a0414040d2511060b0b03007140788509018001c020800040a12000c1240c000b22050704261114052841503550700c3c0d880e400c00506188213640445018100450407036800b600c0400442c0d45d007502e80c580b5040100000c00315000301d00d070030242c141d110b60410343d60000c48032030480c0340511020000e0b0498030145022a0307849860070401081c072054032400300141c40d900002004038501695589000e100050004084c4000031000c54101e48400d0142ca0840881c4a010419400c5c10009199100104d1007003000511a03c040410400d00c9000c2150454061102c1641580c07a00d007031090040400501040d00641c060001e403000c22040c01c41148046810000001c42c5410350920501060700c042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169920422 1250 169919172 169919209
    0x70906030f0c1b02061303060504021507080d0b040e100914010b1f03020d0e0105100504020f07030305060d020312040f06030c0801260f0c011b03021507050f030a020702 74
    0x29100c120760060394480c400b00f1038005840b241d0303d0620001d081405000100040429034000110070061103a002072301990003129401c1480c90940000c01540c86840301c0100800c070140420070242c161900504564000140080361a04450518500d000c082c141150790082d2541c4480d0301b4800c80c0e0440c2c1a503082030800900c1500303802c002050741c05044201c80304800d080b118a50201c02d20a6043c0d40b055411840140110480c14882c0c0d4007a02c0300366112180b0081c1c00e200080da0385440d01c200e800b942104441e030707400c202950300c0070780c000c1900400e000c0d0070080021141d0016581070040d4003000403245007058496081501c0034840d440d09070809030078149481112540280c2014816044420392452166899021134441e400810f034039402045610890001810101c800b04410b0668402aa9480d13110f580c503003c00280b45182040103409600441c8010401030412004d40d030384030102d814003601e41030354599180351b141e000303c0e6110703e80b640c0410134108502d41b038440702001442c03e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169921672 1250 169920422 169920431
    0x5060d020a1d10050d020c03070309140301050f0105041104050301110c060709050901090209041808030901240e090a08070302061012050c04021308010f150b0f0901030513020405070906030f 83
    0x5004201d651241d5078100e014044082204120400e068040b1381100603600f003589d40f214280d107001303400103846024850b001a10441e109038141014441c1601c584514804212181d107007406000c010f2588801405504400f044046001d803002d002e0126084010b03407040d0303610241c820b10a81000d4000d02502c04002003003c04001e40d6841550382810f55041d10401a614036406c00002c00a10841d0201e00d01c0c00411100701c0140300f2080080c52042c22180002c0c00b240103140c030726400c44070010480384501d10f00c842e0140000707101400700c0c0d988045003400311044804952a1445250403201c801c030f005074040c0c401c20503d5100e40b160000100218088500010116542c10b5125800291002d004503400b00c0c6c8034079042405003503040100752400c001c0013a1102003001e0130240c142041a040020019440000c2d0b046030030040742c1b000103201a00c1400d01210318011800f9000142500c108e0907002c0704c2040240ea40e510400d80500000e4640004172071500002030103032240300305258921841d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169922922 1250 169921672 169921727
    0x9080414210c010e18070c120212040308030a02211e060d0204200a030b0f1507030c0804031a151f080603030c0f071701051b1305060d020a 61
    0x40700481c12400b404c15408081001d40401c100301321444404220aa003c42403000e003503000041510341a01941e800c0840d101d0304070050f0b07035031907003482c203008844000c02081001c074061070065604091940009460074140340c440d000d01c6200d0307800c081d5041d00700a0502c08440400f03940300d510b040403011461b090345005030007d003c2e03203d203c0020340103c2d00c0b01e80010020700b413400c43d049008031281c05d0035262000904000c00a08100104900030704140f40199041c2c40c100302c401a00028201400303251201c00e81d41100c1c3e031031499200703c0321400c05010210000b02619010003245c03040c840c40740342c10300c0c20f951002c000e0149040b940c1d0041c1082c000c400c0c05000d0003403048426020701e00340004151680004a4a148100c0d140083c4034002c2c00c44400301c142c404240081110f000428822948c0394100c90f0f1400c80c2d006540c0224442c0c01c0c4084c140d444403c09014054244a50171600403090351440802c0065001505004542c1c0d40014006140c40c2c1000442d0506000b410080328460324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169924172 1250 169922922 169922989
    0x4060210060b1c0605090c0c24071409040f0b010e090903180d080c012013090c0c0506070806011205010b12040c030507140907020c03120a020109080414 67
    0x4050002000702c00d002512400c20603d500400020107000d0070301c0c411840c2088204c5410740050101d020030340038004800c01c42c00d46100c007241211030308412618481c3c88001096551030700b0410800d00d40001440300340540d684600c901c10b40d4401103d400318032650389100040c02d41c0f8880803a20701c1801c3d02c00505c00516000820ba411a1000b128225a4456542c00040c002d10003070100034240394001401d000004010341186d502c0c03020b01a014410280010b5140b01c841c02880050407200c010807074200052105a00803d080e42a1410034520540c11900e03403e0510404490650109a9086c1030004c1035074000381103070b55030320488010070482d41010b5140c210340c4039020000100c105040082014007290003420401564440d040317900450f030b2441c04283d1041001d403020b10034401c0d0030002c0c4d00c40703001107000c0c50b41d80c80050281c5490740c0301d800c42e1039240e002a03c0080442d0f44c1c60b000300d030014684000600c042d286040110070218030110800c40440c020000078481c0c0710b042e4009111828 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169925422 1250 169924172 169924177
    0xb0609070905060906070212031207110a0b180d0809100c08010909170703020f0616200106092408010c0507030804020d06020d091506050a03080d020d020301030804060210060b 77
    0xb0b004481482d40c0300c001c080000c15034000c01202a5200ca690914403c031200300000409041d040d02c0042101c681e6103000903140740b41c281e054240141c1064198400003103070038180e903600056080c0d021920b076082604c00c502e052021102140800c07014001c2c45001c0704100081c031b00c8241c8041081c040c1c0210b1540c0148070711f9043c842c0c900040d80320382c04141000b10042c0341c910074024445080362500c0076810003e640780c2c01015a1001340c01500c020900c0d0805105030701003005003603240d1058075005e4000f5009000004900c000e841d560725603003c5440e001d0750084000f4142c00f1040c40c003050b0494074580c4c02800f030540c0402801d0f89801314400f1015084002d0700c07061034140c240181113540d103002281090ba14128020720180c4005040e0007504269030040c440c940c0a0451041c09803204881d6108807400c5010343c55012910007010070000395004010554203000f644d0150500e401d07207403400180c0c0c00030307002107034000004501808595070402414241c02121503040c0809440d240c1c40b0070052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169926672 1250 169925422 169925429
    0x70309140f1f0603050d09031e0210080601020c031c0e0603041a04030908070902070605130203100e0c191d010e160c0f03270b12091c0c0b06090709 65
    0x1200042d02110014086910090041d5084001c0e1050350f40e125800800030006030004949240702010f07010600094042000350b0b2a6001d011013041d400b401d1010380740d0b048010843e0707046104024025189840a10030027502140403950045420504034000d04400c81e4a020f141c002c90b0140304000110703051410640c046d5569100758280f580b254242164584456041a83c2c640f06030980003800c50116401001c0f010300030041000243c403000110f252000a101010f940340e40000403000d000001d51f031162078404501011541040851800310b00109240092200c40c0c519000c3d04208814805450754600d0309182c40450066042100845142c00054400b10b1000300221104010500030702d61204c0d12900074800c0040d8083e40d20300240340c0b80021420203e10354030384030031880d40c10074202c1c0003060b15036a140141c08d0918480c100d090303030440201204143d02c110135849640302009403001c581e8075865916011018224100801c03402da0190806028552075020481d48643c05108103054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169927922 1250 169926672 169926703
    0x209010e090f010311180405030318010209101209061107050d0c03210e01050907090b01021917130e070e12030703080408090312040906060207030f080306010203070b070309140f 78
    0x38585c02004511541500000c082070031140f5000c1c801400000005188140c1001340403407021040758010600307070300406180c140c004030360511103003091b4010710b03c48440c0202e400b0005084155502ca40f403e0700c03020b40380901c4041e000611542440000e12940010341c40e142000d08450001e950003c0c4000b0b10448604802d4402c64200d425282541e000480301d4036480c4004c0c42141040c90013961038514510542d503c452916044181550000c203200c1e620480f280380d00d0300410895107881e00007440c1041105d00ca10010800c8a0001900301d501c00d01420035083d04200520b000d940c0500034150a80d1024800d0f0701d901c60030a0444000000c0b55183c40e1b151400000945942c54403461600031500c030b95502d07014607007005410030701d200081d008a82d0429814003109a0f907903021391302e401c811f00019080362a214000c20108032070308001e5400c803e0600c1180d2400217152500e0140c800103a4a00f00044d448207540340030702c440d05003d88807041e0a06c015000398410320301066551248a8485400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169929172 1250 169927922 169927943
    0x50705060408070f0605013c0b090a0308030403080103060f110403080a032009180603060105060a0e03030708030906070801060f0c060e07081606020a03021209031608010209010e090f0103 82
    0xc114020b413003d000305500060610585d40c5922421040c803100b524090500c44400c44058100c4401001041c0c00041030128040800c4c2031500000103a4000303082e2a13004000d000b00007000441c03041c001c600c124069034500e00725506610704942991440c50502410f14180684102c0c00500310303003140c04480d4400c211907911084400142c016003440d04c900b1080c0300c10380d200105031000d00001010075010841d4408403003802c004410b4112401a144150554400390040c0302c1820a01c00604a0f6544c505182c446052000006403455010710f03000c450600000c410301c800c080081241c0c036084500d40c03c03d4840f0f58103011006064095090032032041003020501c00040c091203030f05c030054041c404015500000e4640100c19580d44150b403010014a81e10b00700081d00501c081440510250305030301801001059002d0780d181c1f50803a807a801e038140201c2172207090314200003913000001c08180e800541c40f08107027030000d000000c1c440300060145200800304409188178800c2141541d601044030706 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169930422 1250 169929172 169929187
    0x70b090418060b011107080604030c02030f161401050304050c010e0402040302210f12040e1b0319060b090a0e131202280f1401020910120c050705060408 67
    0x401800ca4800000c000c1d08442030004244403031500041c8500c4400c0e2900f82c0059404010595076942521030030409401180c040f82c0081d00c2041019001030004040300c08540b030500c02d01c0e007088084030a800030035580b107000300501011060a4010f629003400d0107802e41c41c0c0ba846a64490100c00340d841d0412064644000c03c60340e407641079070b002d5500a001c0081c1c000004200d0800c1c070100544820b40b0b4030a50041c0c1248490000328007200700b07410904030b810710340383c1607039900c1101b00581115a507d41071820a007001d0000ca0203103229411030700e05032021000c0c0c60403d0b012603110f50000c00c62038804200701515501c49401e031504540b100c802d11001550741800780d685404a607100240700c000c1074088401c12942c0020b1058402c1c41c120040050407802640090224a0842c0001c11202e0049a64400300b5402d00603404045035400000d403030441c02c00002200c0c10f401410110100e4584609501c007003800340b0036240203400c2403c1040c40c01c00700b83c4030346d0341c0c03880002c000514007100080c111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169931672 1250 169930422 169930429
    0x5031512030708070b010f050102100b1804050a0614100612020c071e0608150402070218010b040e010e011a0a050403020a0b030403020c15180d0b0717090102070203070b09 75
    0x44038511149003902c0d180c2841d031034005403a600213101034403210b02d46000030421203c0c5100c0c0344112007058000f0301d0010b0500c000d1602801756940001e9200ca50b02d02d10500c004d903501c100300d1207648030348041e001c484110715042c011501911300c002c0e0414035220411003587c43e811540410748489052a5503050303110ba860201034401d2201d4003c46002d4018001381e201d81d8180044180451040d02c481078a898a000f21500601111079826490101d00440707000c2c107241d401030a003140003912010b11290114158501c002d420380c42124030007400076080101620201a05015081c400040240c0c0e5140805041c3c0755074068107030303000c0c000001568004441c02a0115801182d002e80507191842d610481d01e1001e40007164150054050074540440b9827174840b59800c0c2c0c000f15200e6541c1407045209a000e0741902034032074107402c40d101040720004949603075102132260502d581d40f251464100810740e1036545024081c408107071300600c9450300680d000f19401054610f00d4881603240c6d007080001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169932922 1250 169931672 169931689
    0xf20130308130612020a0f030207021305090c010e0103142e08011b02150a0c0c140610320f1002010e210906030405010b0604090608060115050315 64
    0x1405807100048150700700740800111011245151120f0540e402001030380000d911640c0307078100010f6410b5122000d002d001ba03000c0c010003400030340341c503001d105000c1d001e800301e8401b9603900045500201e41002d0030769111680e880f0801e400c0c0303014805c0000c0a18031906002001c0d101c003040c1402d40d51013240200003010000b004003c0205a03184982e643c2246a000780400c4c114510803c16002800e40c10900000d0902c4e00c07030007a81074114440d0f8505480c0401000382c00701c120204003110181402158075501c101094034100c40241c119030514a05242020420b40d010f00344900751402c03d407049500080203945e60303500e80d80440c0701c008040000a40203003081481a940000300072034200c14958154040f040a1040d1000c84e00400801006880e1800d6001d690201001c03040244072410708164005e10b42040c4590000309032450444001000364000d500000b00c00b039035a100c10809080100402070042c800c2c0c0d040301c06015000c0500038242c1c400207000c10312086510145181c140c071120b09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169934172 1250 169932922 169932929
    0x31602010e030a03090f060518120f01020a05191103221212030506090610110109240612020f040506030c030708030d060510081308070c060302030103060f2013 70
    0x10f0380d1200c851860302800c261210300401800b60034581001c940f0302d005908541e40c0280e0201c8004410b8041c2c1c1c10040c0b00585e44144003024014460085803402c0c00340090404608203031249515500c4072012411f05408024050b4200031407403d540303a10040c08412a08008a02c03040e10940f0180483d40040c038807410341c06040e441840020751410300504da00740d0644402d940d035007032065448400802000410666003141d100d501c80007115121030084025008111629001082000e01501c50440304005c82c0340703050880107030714801b0403003a600d44180c101818900c00d0000a0ad0102c1e00800d09010010f05001d00455441c030100704a95003c0040f20020f0600030200d41e036864503028100d443c0c1d00700c01c0318080352a06101011501e85054616401218202e40d200c43c4a50361709040e60f4052094003500340d400860810004002c038000101e6030014000540b005692945186030207002c45000c00820f13400c161800f810303001a4a2910110b050903103100b100562182880724900280488561 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169935422 1250 169934172 169934179
    0x903060106031407020109030503010b1308030f190810050f0d12050c010b0909030d02030c070807050c150309120903030f120402090f010609150306030b0f012303031602010e 76
    0x2000011440d41c150040c050444080081c44015210520181c0c2a02d444920082c040742080c0010711001882601170300c90b0716401001180d0090740d0700661405c551100b1103141c1d401030300160b400190b024010100520304818600048a85040c0e40c41201141d0f00c0d000301c910075100d4181c010b010759692003200500741d40124209001c0315404c10003034246da110017190405035080403103110a51409000c44c42c881c110800245107811f8942d030070040258801400c9085242c421b00a41d008500040c02401e074032441075004082d0080e03980308001740c001015808000c04203080081103a03080340070526420f10020450001e0700e490741c102c0000c0c158001c1403907100000c1c80c00314040c00c220701290a4540245d000303036500b28140e00d5028007040d462409000c0e240100e034500c4801c12080200d40c094403071400d000e2900107806503c0740e8540704880003c0e0384815211400e807005100000b6035001c100d80042c0c00030700c0300d520300240d03401003901ca001b40301090015441c04c030003150559000700002942d809004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169936672 1250 169935422 169935433
    0x311031005090105100c1b030c1d0f04050c0d05100905100e0c18060f0405070f2a17070c08070303020d020109020904080c0a08040f1d0f0712020903 65
    0x18040e081054a0351260324400c0030340e84000102801d001c00c102d01141035543d100001240141c58020b4989140304080034044480403000001c1030018106c0c03c041e0400b00ca48650104040c89407071a18200500481c031601901001d1000003035000400329850304042e620004082c41c18241141400d0f002c0301d00d00304150520b480c030b004101c4003007101a000030f0001c02c10000001440f4450f50348403002c0c042150440c041c00304110b104507444072280d90004000f803010705207100d0301002c2426a44107841d5107012441411a80c4019a005200140c4200b40700011200e82e12082c9240c01d009036281c10040d0554a0b02c08410450100203007c403040d05400140c4150f50765902d0f40c509a803000d440c4001d4005024035683d503180940b040c0500c856094000f420b21001340c4803a21502c505074400b0740c0d610107a2207948580b40c00105c0c01c0c80540020004801c0c0420550302d0138400440c1d00c0c0922100300300c035056030b40c100304090b0841500d860b00142c480c030f0501e42c41126903c03034100034401c1c4600e00f540752186 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169937922 1250 169936672 169936681
    0xd02040e0c15070c14010c0f05010f0207060902010e01140a050903070305010914070f0803311e06050c0607030903020a06020f070309090203070c060c0e0901030507050118060801060e01031103 84
    0x14000f800324900c6010a00c0312195244012901403071302c003104500040d0540f5190300800c0d21840c54811041c001c000020310040b001e48140102c0e44280b030700302c400d90f45500400d0f0556070090481b2260010a080c695600407001d00d44070b1091040d02c0c6c805061220210b40c4844645040160f1009503034032000030001d10100307040c8032048110009401c01e0b54440c2c1040450702c03403101c004000807242e1400045080000c2a100c1c09107180100c5c6c0d0019200c15801e0007c0d12856140200000400b0f0582d900e1004c10b80c40c100c0315038542c60310380007981030020400207016501c600003032541c0d0140c43c901d0b00040c0312080b85001ca04003900d106006e800c250010503943c007032044880c002c041c1e1a1007500d0302042581e9811400c01a8002211030318046142d9030030440108030503820440d81903096142c03589900c03510b8070010f00059002e0700b0907640d560100c43d0602080d600030914030000b41d07040106824061901c07400500241c41405003404102001407004142c4e4000d4001084129070f11050540321700e407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169939172 1250 169937922 169937959
    0x30304080d0b010c0503090103051e0a0501060f0e030303221401020307080106090b121801060905010512030415210e0f100506060a0e0f040e03180a050d02040e0c 71
    0x84140204140d14290b402c00320781d0b00800940d03148aa200c005103060014600046d8014a00100200c0360ba114820b03a0b031550481c1e102e1210f1040582e01d00010743d42d4100400101080083c280c1041800946881c00702e0f0b0b0341d800010b49a100f00881120842c3c075440b40d08004048040800050295141084058074944103401a40c800e480030790314411240c1e0795107400c592114041c07182c9201c40c1403c01140b2124a00102000d0740a10140060342010700764014a50071102c9960211000307079500c000600042c60300028081404403500300860409040101d640d075017410b400c181720240400204440b03a03282c0c2c0703242d5000c0c4241c402c1000b04010500b03843c0e07081c2c1b20300c84014600c0442c02281e0301c81030140390f1481641c0c0110b44c060140c90402c0104101070780d1102c0d0800005a00020008005805590780d0140c0c124111340030002e15280c1d074440c001110401c030780d0702c3c40c1761241c0d094040600003a241c1c41303180e6100f00d8045130085070045802c00101d0410070a452007582000e03a02000080d9a00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169940422 1250 169939172 169939177
    0x60616140d0c020d061a1302090f0a03080a1b0515180619020a09180b0111030901020d1202070b160207091506030b062101050f0103090f140f03030408 66
    0x41211060307805a40821900300c41041c076844000350310a54003501030b00403400983c01600050700c80407005540c02000000a4058082c0002050880c3d070001f13030503546801d00404440078400c0c01d07511100700504680c6c800070326015a000c3e013010030092000a03040d040746408040c07a000e03000000c1c0e03803e0902d146100f002c5913074100d405218002288807148185240000c00b10f100c2c05a0380d904e5041503206600038006540802514000c102000390007185400c845242410b40d28125000010200e09600014000c0c2d20b110000485c1da82050050840701c0c0d03000700790100103120500d0284010540c15842600a009500000c1c000307500100c1008001c1c0340ca08515400ea00b0130741c00f281e41e525030790a40d48003661021800d4414404007404100f103058081d0700b081140c2a001040d40b820024030b07a07107225801080d10000c410501120f8010886810300706043c01d80000c00303203807e211a03080c80c1c640f82c61f0b03202a05002019074404ac40761580c145e2050102c0c0800745107801c1940d50380c0c00d0905200c010358 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169941672 1250 169940422 169940453
    0x70b0706091109060108010302041e050903130614040302090a060306140f060301180b090f0d030c0f08012114030703021608190f050304050604060c060507080705040b03060616 77
    0x420051a02d80b0a910304408140e210703480503580d50000b6820369003448050100443e00d041c00c84607030402030005c038540380102449003995400850712801540c0c40c0a00854459010200b80038991240da0400d490a07011078090300d4040e1101d90050b151250300e03500030489684094100c0b854011907000008807203a556000b5200207182d2096070300d440c0d04142c206c0340318003050458a03001e200c18500080d0342941142d17021040205403404a003c0c070303618a060070042d01903440040c2e56504000d0900380c05c5502510755034120324080e0010341c18012200201c203030307024007960a80d8a00b048503040040065409000c001703603606403601c550041c50302956490382e001d1004207030701000700c2c007180d140000030300003000603400c088032214003080b5100c10006203110702c4265028002044082243d40380c49009000400d410740e6000c40c1d1109900b40321044800260203802000f80d29410b1083c01c41e4014140d50641d6507100c1034564a8461000062007489000421f8006003000f020100c140014000d445204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169942922 1250 169941672 169941683
    0xc0c12030807030b060702150f0417070905040c180e03040b2107020d12062303010c020705060301090b01030b030601030309031b08030f0c01090b040c1a0301050f090405070b070609 79
    0x1c580b42d00030280c00b66680d000800382c00120511502c000f525002080e00301d000c03c0e44840c68a84918081100201d511503048061907204800060350301ca0010000c1c08010304548008105c503003070036652070a440b0607a00c1101054030f8844141e0403010082c1d4400f003100b44c90f0b42c040300d9031580e540c00080e601e0740103180380c601c1c94a100d01e00c3e0201c1d080c900d0030f014401c0703841ea4003400c51070f140c1c100180c81010000340c00480d4180c1e14040843c04150388400d41c03108000f17400302400c503500100300b01402c0d039080c07410f030b10215044044204a261174034829203041d55030f848004110090a800120000d0200c848442d9151080d6000002030541040e982c0d0192030080300c1c068174140c0c10b81e01c0c01c0e5002003248100c3c0001d5008100c05402e40303811801074200c0400c408001302d09024241c030b440d070810b0300644007640e83d400c48000c204020b15210300725980810700c4150907411503141100142d0700e0607404c1040c0e4002c4402900140c100b01c003c0c40f07214050852000519188e02c01030030041d008180300501203a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169944172 1250 169942922 169942937
    0x1602010c02070f060305100f09050a11071110030e03030c031005060708070b180a050c0f0102010c02030d111c060302040b0d150f1b020a02030c0d02031b010c0c1203 72
    0xd440d01c003284520a40d24070382d1540711000d1400d1011401002e0041c52118070201c2108081014440320481e04020485008041154104920301d101280c000700400c0c8448001001401c0c0011801211402e01820458400711181c0c645203054000e4007166016600500000007000720500400340590b0042400b40b4080c560181c0710014002d042c85071040c0030302080c100380319407000038207000d94003980811442d02002440250410032441d10060b0102101c89420654426515060240d41e100300740c4800d200a1240e0051001d0194481c459481010032480d110500c1c0301141c001c41046506403412140504128109102c4a600038150317804224869420710f0f403010b101e4940300c0315110095400107480703804281c00b03281172001095007000d0004950f41b1070120102c0070800407808545007403242c001e0518181e05104140c105910040518802c2c60b03410440005610b00188090102002140f01c4001c1030074800103a502944038080148841c0710030034040303a01c2c03d03460000031015201e6281e100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169945422 1250 169944172 169944191
    0x2015010f060f12020310030204022703070609031106120c0301180b060a0f09031203021e040e0610020f0a06020a0807020c150906070b040605010807080c0901090c050909160201 77
    0x840c07203081c035910400000c488620709078904540761300031134002d9034900c01d8080c2d1a50b40d90120b000e90700060000700920842085031020f408100c0d0600705111001c401815a1905000c0050201c02282c0000341c010402da05403030804c0e84840d8104c61140103070316826007661502c240c030020658024060306071000c44030301151280c010140600027046200034030003030400b10003c0307088503260b0b200c0034403004101810710b00101141d0014030b040c816080d00c0c0c0c4d025945402c04640183c4036002c40c20780c070903016020001000405c001c4d0321041e80020b01106c5400a021554000700d14020140b00d0710100f901403110514100021903006005001e00c0f9214103849680d8034000307070307241e1061250083c0c0110205103c11900100f000040c401800300518103401c0c15031170348818200540490b0112041541e444c014401c2e00000c10120009041d000020710f414290200820030751201882140303015504c1e0400266250301441c2940c10800c405010350000d1310308126565850300440c441c01d0059441d108c0e006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169946672 1250 169945422 169945427
    0xb090d0903050c01080915090304050307080f0c040b15030112020f0d05060403050c100f0c0305161e1b0f0c0b13290706020a020d0e102015010f06 64
    0xc022a6001009800420b010800541d58108020b000703403250701500c0018001d04818103142401070440c42c0046480710700300018540703010003c0d0841d58031544886010881440700151940c8036040554000c6800200311012130320020010250580e240008030001c035044400d4401d8182da40c0c000c840240b076000300b002c1408141d8540c260040c10301c0c0c001d40c000070b022a026500801c0301503200700403282c00b0040506010200c810210114050303540354512080d00580c103009254106c0c0008200348000741c94543d02903c042d600300048000c2181c05400040100d00a00411908410038659221811a03d02c3d14a100d000112001c580d18440c1840200d001c2c2c05a40c00e0702c4203114031607181c80d0480e00b059912424142c031244481805004080744c407180e07050034800342545c0740c0300355400368443c4480c06019040c04401c070601c0e010040d0007600c6900f1a80c540c4084841ca00c403608280c0c941040860300e40c0d070540004500c100080c4030b60f043c2138456000d91b149141c1250068505103c50941382d103001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169947922 1250 169946672 169946687
    0x31306081e130b070216030803040c0905091b040b06031906060914300703061b090504020a230d05010518011e080106090501090e0f100f1104030b090d 66
    0x71004040b00745491000014001c003100703900300c5201c0c01151701800146046008403141d030380007111a208044144003c100b803200e0507201030500f014040c0400c0c42d042100f60f41e030b62010302020840703004401c40441c1035101d41d03010080174903001e01130959900c1d1a0800b0351820140070484034000345081c2001503164481e00c03185c0103840c00701d030344146810f0b000009c100740c03010705006200b1203a41101344003140d0940e001c5901504403400b005410114030794240842144c4210000f01c011444884049d415143d000c0488426100221001a00c0d65003e20342201c070990691084404401080000c8080050740c41c041c000c514a000c80078045680c0790402c0c004854120843c240380035110900502500031991f00c1007006400036554040400d640d9011642076403840c1c0e005c3c4c03000c0c076640c40060008542501034580d00c800044000e04d070f10303003200c183d06683c0d20f04c0000e00441140e6924941040c011319801c241102d0802401c1070391500e03200c1c03c0c03441d118503080d154a1003e03c41c030b840149805001d60f03403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169949172 1250 169947922 169947931
    0x21010c030c0f08101a21090f06192c100f02040b040b1e030a020a0305060306250e040905070501030c0908070b09010c05010207050d0e0613120203031306081e 69
    0x75050a040c2c90421012180c04150703004802800d01442008190081b4040740300b465142d50142a10342d00300b01c2a141e0400c3c00103d0704060740c3d005002049130910340d0700c0820003210440079000400484a504020881000020313150806400142c0c132250502c00040d0a032031404040d400b082411a052405001c031b20031440b5546500100303200c100500a514400f82504101801184000c1080c0340e024030443d5004071030709240745501107940f1030f285038580304d031683c4003009a0040069080007191140c11448030a09500140e90000c2c1e40c0f00058410b001c1c503002c03280080c005022280390713881c00c00e4450440b4002d10f40040c0c41c044001d06814400c9003820201c400d200041d084503070501c3d00f5400e20f50710002c03400381440203080c29400043c0c424801080c0c0c580c06140941900c248100004200324281d0380007d214410500c1804011501300100004942c03140301c405102d160180b000c40e0840c013031902c1041c0540800000050a6500100000c0c4220754180000703d420b00c84030200c00c1024070507113 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169950422 1250 169949172 169949191
    0xa020a0c080906041806080c0f010e040e1c0309110d020a06050304030201150905060a0b091c1401090b09250b070303060305030f1b011a21010c030c0f08 67
    0x2030126a62900401c4040700103402d0614007a00e991100d52565411310428002c25a00e000030402c2840c180310b54090800304640a0050034007140000b001540c6060a0510656944081c600740c000b080040700d0006a062007664191400a200a002018907101c2625104945e050a41d4a8500f880c00783c081d00e54000c140351080c609100085a540d00010f00c2141559610303030743c048403000c07038210f104002c062241020920b0700d003003814820b049040c3c1e0300040462100f40611059503a610a045c40804000c6001000011150074150200b10401c08001c00c00d505c1c1401da0402e0003982901c0620400c009411610743c003118a5181d83e40d03400741f19000d9004206188144901ea40300c07402420340038082d240218000e500ca46820f415a40803c4200c107400b40b0010f10b0700f4501c00b40d10091303001256588000c00540c4880341c10048543e05069165104401110648824101d41e1764040e10a4640c10000c110b68408104080d0003000041210310110300d903404440707402842010001d1140b141c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169951672 1250 169950422 169950437
    0x50105090106050f250501201b0109021017010b16140c030706090501020d09030b0424020c1506041b030507050405040e0705120303041703100302030a05150a020a 71
    0x2101200c40c4e4000000c100e40521013004178801d96a044134000300d0310790310f00e5004000408907141c0705003102c05040b640d581d480d03202d09a441c0500c4244060310014403184249100151200701c02d240141000c90001354056525256100060f038810b8505070403041c07001d0907482c1a40c80d84030000490080340e2002081078045400a0700040350b0b00c20700743d0b199602004441055142d503000074145059a040200007482a000400840d03034108a0821000100d0030400403480c2507488000c0710381030040000d8010700324040141c0ca4612203030451040c00481c10b404540b10f0b400102c86a480f4424201441030101c0c0750f0000c14514a8a4400c03d0340300204140035682d11400c0c1d801c1036002e820000c1010742408401e000000f8151968081c1c2d600312540c4002070300300b01d41403004005031308011a040d600395034014400c100024032070412200000d410654046c0d141d40d16018400306025440d000250140071308040b002c100b1000085c90041e2007103060a10b1403e03540c1303100517800c0340143c0391a01c0010700c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169952922 1250 169951672 169951679
    0x1d090c18160c0f0323040b0d0e03130b07060f050609040f020604050307140913031d19090c020c031b0909210307020d030203061315170c030609010501050901 69
    0x302020201070142030600c800e0700c000c0c5886440e5650304429050700811140c1c0010111945600305010704a418594402e0506090468403a190702560000e64a6107640c1d80d401e04035441d0400c00c1e10004596008001240354850401024a41011404503201030504202a02c005800d01400c0d1040704003030701403003169075203441b1001d10b15412001603810140411012500e510180b11010107070008145d40d11914100320107006600c0c400a10b0182c00c0140700112b42c0019512022001d0780d80341a03001c10032690110400280101c118803420301e045103204000050000c190741240710864070580076075508010a000b4507443e4103101682100f03030b40d40002c142500b440c003d807460703421045507002c4448801c80355041c00d902001d4202950700400000c01005901035040001c00748180c0286415030860520b07a0120705994140d200510715680c1303c00f0790390001d6114404000c000d001100d01456815074443c5000e480c0c004940b417080c0a0302038280007032150101405018100e44002d071541c0f026a18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169954172 1250 169952922 169952941
    0x507020613080a2102070b06030f0a08030a0204050a030f02040b011103040b0a110114040c12051203190606080109061406040504020a05040909030f03060e0601021b01091d090c18 78
    0x70a011010910100d1080190382d40241503070101d401c1c134034000040c3c2e19056030410003501403006245601c41e40c440e000307400300c80001203041002d01d58001001c0382c407915a284a140640120303001250049080f10000041c070003c4a0b40044803402600d007000464910750044400302d141c0b40b66504294000c106c02c10595100e28003c1c16500001e103004040031030740d07911703080c03e40f40c0400003032166016500901c4103010040007100000d110010740228400c1e419a902070300c4070010700c48c0804a03140800010003205104060b81c18507072000314100846038807804042e204c81020b0181c4101c0a14008012030400303001c10b00d400780d2400c010046410b0628003400c11001e0762280085030b0070010284000a042c2043d07014104d21148281c44466000e500480010b049030800c2d4041000303240c1a4040c0080c590700840c40141c2d0355602d090000d107007001580107072428541030340f01e207440e0342d6419081c80480f90314541c464024201d070f0040d1010401c1e804204070760360b80b808242c1d046440810011444009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169955422 1250 169954172 169954177
    0x2010e01020102090618040507020328050c0d120c11060a0207020a0b1209160302010c030e030111042603040e0c2104050102180306100302060c070f0315050702061308 73
    0x210500c005440c185620002c601940c100d607030f090300d15242802040d00640f4160090a50010300c81c801035051010000b4080c01600c1074a030b00700d419400a8041805540c481c60480d0103640d01c61089400303130542c40d80c0042c810b8440c07020404c00e5518000b80e15000f14803508042c00910030b40c1c001441c0940380e400020000754003030b00e0101d901c00303c0507000190a81070400178006450611008603514075091600f00d0030101154218032003210868420300061382c01441d01001660180b8010b044001c0a83c007090050040c2c1407141c0385400d011a00140fa950070302e0710440001d00d084072a06040316030100d445e940307000d58040c100542c05003030000f83c42180c205002c0c00c2444102c0382c04000f002a001d161000485094a040e2045c0c0d4002600140d501c42c0818103607600801030f4001c1c02c00d89041c401504600884e4040203114080c00244156015006c0000d400540030500107a440f0603580c0c40d100300810140c0080c030300042d080000040c0300b5400440c0840c40740307201110340d0851070000d50781c3d03800d0b03a17 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169956672 1250 169955422 169955447
    0x1080d0c11030f0a0f06240b0304021203041509080a0b010509040c03061802040513050c0d0303090507080303042603040204110c01050a022508070b13080c1501090203090a0201 77
    0x611502a00f000c403160304001032601c0c40d004c1e40300a403082c0f4890510074150313021040784038400c45090090041c0000c590001f01c0442e102c4420a030740301c1d12a4400284860082c001240da913100206010864100d040e0722001d6000c41e6494081c4159a00c507403c90703e550315680081c0ca00709218004014030b0901403121a07000c1d00c9010300014103912507071224122a00c280d01040140e0300c03d1000021410244a19604a03c140c070b4600d03400d45c0c082c6e45507075036482d00c0c10071980a560450700d80c10415000303400c011b680783c0c2d01c01e0079a201d0944510800e562a002214155815602c480d420700c0a920f40074038100c943c4143c900083d03d90b50b00ca8080c071024059200702100c80082c10449030304404404c5c800c0c1b07802061901d0003d6510408070041071041661602039007190020310401d4000145c02c44216034400d07901c14546010b540d0b0b00700456070b000d89481e0000e4540c880006103030100003030120710b1407005003030300d07424541d0b03a40c0b40d080800c100d00040701c035840203500c200c3c00d9401540c0503500c9022070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169957922 1250 169956672 169956679
    0x61b0a06020f030601110f06150a03021e01020c0a0807030201210509070303140c15060301110a05030f07080702060402040e070803041d010b03040f0f050307080f03090601080d0c11 79
    0x8040a580c0c0d00c10480c0d2119404420707088010090051940c2d21410f0030f000c0040100080c442606409405901c6030320144c00800c40c1031302010240d80030303201d01c0c40da4801960000d210203034500c40d03500c0114106c0c1070144001c1c018004c0000c00d40240c07030310302c50140c15103100e000180f503d24115401503c201c099001c142692051001c58200c0e00c21660164a1150101401904100345545406040c43c00c440017205c06142003840032140c1d0103000144911110601c40c1c58003083e840700c0002c01d00500184c00182404000001d1007407116800c02c0095018030142d44840245543c0c1d89011954a502a5010401178016a0100d00036140581103450400304a0041e200804e640706034051956215a1103508a04a601031901c0000b041d0f1a40e42c0c01403050f0030f0501d20f145002d945510412440c140700a048194002101090040410640d0007803940310341d6040e03444803000389030085508122014045440b82100210706910301041d441d01e09002500c80074050480782e03592030440c4c00519a066003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169959172 1250 169957922 169957933
    0xe190504051f0902030705010302030118050c0f0c0a030e0a0b07030e011707020c0301050121030f03090b2e0501020c060d0b0913050d0e011b02010219060617060402061b 74
    0x3118101e03000b100e0700103660060001044240c5105144c03c21041d0381c0240c2c189441800100991401d286440303072072900c507643c0059036a642c40c516031500c0c00354000080041d9008511484041400200c1c00d40316406502d941135103136440300c2007141c402c0c803a02408203000000e01c95907000078007413010300140710030506110480711a2441d0b4512501000c41c4c0c5400160322200c60b005c3c40c0c0c1400c1c0f044034050110a5011240c050500d410b01030000410070009041040e0307400840d80451017603102c80d40c040d910000420050422800100ba40c460010310046002da00e110345121400c07950b0000030880e107040e000390142c00d040c00c00300704071504402d17041c481040d01c60f04205090341e50711501d070344104100300d403610542c06541042d52074403184454000c11b00a8140d803c150981e00000d03820072000c102200c0041205152004070300704003010f21a24031101000902d00f007045203680010056910404a100d401d41c4004000b0b45d560348161006900941e0422000740c4403202e600400842c940130208944 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169960422 1250 169959172 169959193
    0x62410080a0b030d030f0c020f060f07020a080c010b0114120105150c07090903030606021f0c0e0402070f111c020d0507031b03020108010b040e2a0a0302130e19050405 73
    0xd040004c039038407000010b070352580e408032241818411091400c801d840240301803400b0010080c1c0d00e00b03004d0031454030b1002d0540001c030418802c01c40c0c1c401281d8041c130020b40707904220700810702030010034900c2d03404140031655801100c00140c0a8850241043e41c0d10b5803241d182006014100380610000100550b042080603482d072001c001020040414030710002d0316020300e0800030100c07125500505e003150400d03802a40c8400080312651f1901c08001c400151007011504191f0720031035507800040d0011300106500c1c040c400d002c4003000702e060107402c03411150445d6004110349201200b403100b8404019055000c05030800e030700c1805200380f00781c04841d0030544a40302d040c002c0d142900344c0344021b403070500240115648101400d0040103c80c60300c9003014181401f900032140010441c404103039242103039616101005a142d00860410301c1e940b55145d0460f007004029610288004120b02d08403c0c001408841d004101032043c54001e460f806111441903904000d041c0252090310f0502c01d007451034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169961672 1250 169960422 169960429
    0xc060609190c020a06050a0204030b04060e030d06030f0201080c030106050706090203030702030a0c08120a080c0d0b2706030c030d081e10080c0306041203090201021e062410080a0b 79
    0xc140102c0150000d003181c00c160b20f07069050f580024400c2c40054014003040000403050b03521940c02c25445a40403038902d9108090b14618050009070320049170500c0d01c000b0500c2801860310700e40b107000f80d075410390903550110307404041e200038803484001400c03c00130440414031640c03081401c00d00c000c042d685400c042c0c5d00040d02d48142810242d0f03a14034901000c100510080080e40c8544240e220914105079860202034160880240400d001d2030000850441942640c1c1c0949610b074401002e2021180207031100340300407001528041660400c00d40492018a00040d04401600e002001010403080011b070807142090007034850300900407131050600c2d01c00d00000030300f0702c01c0411040c807481d414540f020f01e614016030009480d02941055046c080401c1c0203a01d442030101c4e02d400d000c51604490310040f494840c610f040d04038101c500c03050310003110b070000c958139001d01d035821100d49198100080380c4138500103450929034404d40f1015600e42c400d0140c0442075025207840d400150002c10070021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169962922 1250 169961672 169961681
    0x8120a06060216030f03080c1c0203100807030b070f11010509030d0f0c1e140d0504060b0111100c031e05010618050f041a060a03061a0c06060919 64
    0x10a04100d454a034140005070341040000090f80040300e42d40111441c40e1148416609020b002401304568000003e503c500544211200e0155403551141c0a4104401440081d001550590100c2c00d8411000482c030400259140030b403508040446c80d079890f00c0d0303401da0b18101900880c0051011085c801c401161003803050b240300e20a0341c0061a0342d918010918003c030307032155400d000e54515200402043e25400203000c030314503502155800c240340e8030241c04d440e5689046006c0302000c0002962030050b0103c6d410480c0114440c002c04c3c1b04207040c1c20015211111600005100b5511039030021181840507007240c1600c101c54240040c080001c13056a0580e00c048010308022640c070307100100004d40d8001480d08180d200942c0380c41c0001d08100000e480c08440410b01440355868502c0c03035001150080551041381402818560344428129000c1c2c0a01020712502404100c21300107520513003407110444402e4819a005402190798a108000c84514003601c01c03000140242030b400ea030380ea1144078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169964028 1106 169962922 169962931
    0x60b0f03190615050c01051006081603060b030403050a0f110a0f081201030c08190305030105120f0115091104030b07201209010f02010504020f010c0812 67
    0x8510241a0a80040003e10042c0c2c0000000580110040c28507030403010090102d036032860045c020403091442807030003044041e80000d55801c04405200d190174180d08000414588a000804060f0812102107000c40c3e4000b50141c1d8445d00700c03200c140103180ac0c0ca0580130071203141c40690307111280c102004208d07100c48800034041112072000e4810540c19181912002c0d80d4038100a0b0141c8602d2003441d20320b0068161100e0710004901d2f0000f1460303055103943c0c2c616441e141c28070640c04d10500341004c09000e04070806000c00405e0143d005010600f640d410f02c90380c20f00e00720f101112840e1f0b40213240c031501003008100082210316056030007a0700341010302001040610481c403921040c2000c1103240211800c0c02030036100c041c050501c02e03c081e0b848651000c0320102c142d003211010b0782e01035440600e00d034505182c4e40c860035654101e03c3c41402e0309400c0407101e00c000124900141c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 169784172 169964028 := by
  have h0 := BRFrame.cov_init 169784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169784172 ≤ n) (h2 : n < 169964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
