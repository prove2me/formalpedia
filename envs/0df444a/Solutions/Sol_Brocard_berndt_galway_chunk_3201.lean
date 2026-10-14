-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:51.201571+00:00
-- url     : https://prove2.me/submissions/407a635f-a6a9-4faa-ab74-5938a0347986

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575539568 ≤ n < 575719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575540818 1250 575539568 575539609
    0x26060912070c1502030a080606090a14010903081902010e0a050d080403090803031006080109020703021b0f060d0207060b0f032d010e0609011803020601090b0411030901050906090c 79
    0x100c0003004860b420702009441688400d418260078031038003d5480e00074a0000000408150100300c441c202174088800010010340a020181c1c2803100ca640c10808c9840c13954100f1034043c0b00003020880c420007500094882d856290109514140300a00b0f4030082001e840083c0c101d000340c0c0000920004003000c0e46100350504a03100d1f0b0b12030500360b030000b41d030b070b03004542501002040007807140700007040c2400d41d0090344030303240c080c0d032108121422030242e0000140568442e25080c1012070a10703004c0320300300c80700030b000d148806980c201240603a000301c2d41b040c02c176903000300e03205007000014010680f2035002980c801c0524540304000075600c03441007a20340b0500348044043d0448c250101d2900c094440d40c907000344020350200c0910380c0d075018101d800200a502e0b2400307401c035801c4094a1402003503050b81c01411f80d6402d00c0d200a0042c5041e407030207680503956849101603850b4250141d4401e500c00303000000c1c0741c80c10000302030030301a004022034210f4112409180150b59118022411070515040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575542068 1250 575540818 575540827
    0x1207140c0a2111060f130618091104090c0c060c051303020108041a01061d03030a02151003050a0b010315060501050d0b0307031e1205250f0b0126060912 67
    0x200f140100c020341202680054000038401c0340c640e180d034003c00f950341d00d035150074149550301c030b000f19149440c0c21750808800e05003003010090b2180d00e4002c40040f125042c0002c1c5015694241d42c0d085031150344201d00455880c0f000324007804103a00c580d40f90215907043c42d904d00300804a041e200d4a0b9a800000d061040c3c080c003040601035410f00039426401440c450100a50711404d000d451f0456201034004014031001105185090100950b18000d026070010705011107010445030f803400005001e514a40d1040000001149040000d000340c6030140241d9001c40d41542000d640c2e00280a03541e041b406c2c28200104900d907484002c55100b200d0021340059402c02c0b038000241044050740c8050b1048071880b5240c0790718585110501c140710b02c01c00c0300c1c03c3c800317084000c2511640070340300b40700780d08220001d01c00d010107902c00c000c080c0b0f45100da44440c0100d94150740300f070030004080e040138020700148181d401e9640443c0c5190811020034800030611854000307074450342c5070b55031801cad4480c2650224 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575543318 1250 575542068 575542073
    0x403120c1b1407090213052701030804090c170403080a02090306010801230702150421031a0d11060922050403170702060f07021207140c0a21 62
    0x781c0c0d1024045908080801c000901c0c01c0581c0d800038040658000390090b08000201d846180c07084034584154a11902c020f585010100701c201070825040006400130703140722001a0850070006806148135800c00d5450b113043c21258401c80c0c000104010501c444a071070300c41000380c1d1890450348a0744c145422007840d0b84601405010f401003a4406e90544a000008560414107400418400080000c80c054030b503032801c007141048109948200140c0c2041e142c0312030740c0700140320745c0c7d074418000d58040c060310a0700c59400c11180068094030f00040d541e4601070910704008450800503500071a0041810295500ca120b85000f140a00317511074400081c0200b02901e421051051900c4104e0072203102c0824899104041e0004860071000510268805030a008000140d140160107650050500e5a02e940942e02e080d0350150a80c4103620640f24890248504c11005265082c81558421060000c2c2c4908524281c00301440030710550071030f01c00788804281c8241c07100340241102c480401070349150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575544568 1250 575543318 575543327
    0x12050a0b13021c02041a07110a0602160807061b151404060b150f21070c0b0c09060306060a0e04020d2705030d0221130b0702060403120c 60
    0x1440c5990809030340481c1c88041d02450740a01034032140954980211009840d543c02288164090214060440300101c160303d00100d000e0b0071514403d034100000c0950301d07000103044032510303404180103a00031001408e0a00c5054940401441c04e04001d00b05033b070a0000c040c04e510702c01d03142503008450049001050107144403407040c0c0650f03142802c01c0481050b01d0440a100340843d02540d8440c1081d07010b40c0b41e405c2c2000051aa890b0307801005043c1100c2c11807510b400d5005801420300c000741d04050f0340740d034000110254040d14980d11760703840020962400040d4114010242c00c0101420311150701e4580301c0404a95102c0d01c110b410302d03510444014180d80061003140415002031000c6441c03000f0b01c00c10f50004030a4401100740c0b9171000c250800a01010040c040c0041c0301750001d00c02000c2c2c0c02e240d0740241c44000c50001e402d0100305070380070100e050208100e80c8a0040060003a050060120340071200790081c0c910b1020b00058030b0551406044040300810050701070b03540c4d521034070165124 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575545818 1250 575544568 575544581
    0x1201080d0c05100b0f040501030b07020f0a0c090207110429120c090702030c0706021e01020313080904200306040c1e081009180516030b0f07020304030210020304080606090712050a 79
    0x14007c02c03007540c42c0d040516850700101c402801510400010703c01e040c80004404104591100400342c810b800d1042280103074203d40400c46801c84406d0345c00340640d42e2409141c2d10220036595140001d1044280e0300741c590000d40c11140170388480c1443c4031980c28046030000228509442682c440c0e1a0104201d1840c841d0400303c41a82c014544041003250303001c42c84402c980d084041c00c44d07400300c402151310308078401995506ea03c42c40800000001401c01c1c0050001003000030700005044007004415500100c01c18010b201c415000820401d25250a104e00322211a0324504543c4503000d4800001242c00316800190a1040140c00034820a06c124a000c015111244c02440206d00010020909003c405400c07a440d000300200c04d0101692a40d5080c200c0e034000070080380c3c0d81c840c0340c007031104130002615480c1103000400020025848100300c1c040200381c1603008540d82e03440d24118ae400d04a021b01224455841d400174400616400720328006d003070302c40e0903000900d5180c0071820b4006100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575547068 1250 575545818 575545849
    0x4080f0c03032401051c090302030f0706140c090d080d02190216060206090a0609080f030f010e0a0b01080a150f060507050c041112070e061201080d0c05100b 69
    0x2005166684040f410b880104402c81d200c0005521100546517070280040e02401784018129004400220342c100e026114020b0041e0b900d0030044110314100e682c4140d009403a02e54403801d43c000f012100c841801d910155006074141406414400a1a0600c5041028104010201d005007500c50140d045840e83b08546003486019011098065280c00d1081c3d42040c01c0d07000f0100c001807041c0040b0302c551148001c10090b140c04081030b40d4100050045000c00d4501042c280808001c16a05c90001e50080c241711078007206640c0341980c4a00905d500070b00b101e400034100011034900c2e981103120150007002c209404182e5181c140700800c00100b55038061040404405000036409030000c00070304030280207400740c8509042c1c0605200580d8081540681485000c00400042c0c1d141c1d01d801c25000808c510b450b070042d00b42c510000b06a1381104418061800d80c01d401000800e00411801d0700051103403c118185044070f03224283c0341c0300c41c8407030480d600b0344542c0132041650b6603c051500105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575548318 1250 575547068 575547073
    0x31101050703141f05060c1006140307080111070305030a090b041113090812071107030827010e04020d06030501140603060609251b0f121704080f0c 65
    0x1e44a04000d0150008601d070501c44076042000c104007180030030302c1c2c1d000c0140400e4202d400a00d0a1300b40090ba80c000383c03101d401d41c041d401e82003032401601c0c05620020b2070301c01003c10806c0301d40800c0500300100d0341e0081103941e1411201da50441b01d41c6091f03d01c0150181040c94480e07480a196101500492500505144440b4200710030400c11028400e40442c043c0d810f812545103046c2d41c00300300c6051680140c800c1c4801c1c0070040e40319904601d8245c0c451290720746016540f480c62843c510b02a40c541040340c6024000c524031020785200b46d600c05982648240e1940d4501300600080e110101110460b80541d4002030030103111107440e04200015648100200200d07005519a0421814192001c0740300340280e43c049080c600d000f900c0c96020f2818504d0314600109018560904984540c00c114180201130844500b0141103400c51603845008400080706a802440c1824001030300c1000e00701407255505604c11400034110360036500c035030310180072962404005101407490241001800151 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575549568 1250 575548318 575548321
    0x120f021b0601060315030c0b0708090a0f05011202040b0901030f0e0a03050415030c0215040c031e03030b030105090a11060441010e01210213050120150403110105 71
    0x201030000342903040300e00c07a64081028042c0301c1c100000c61402c0e48005407807510764082c00c3c06090700b01401000e682e07100d4603116140052400100310842d1042c2d015400a21300654100100e50300042c0c5541c1e03010286070308508d01414010704460307a010b141c14403810159134188001d407120241d440102030015440c00c55072640341a250003800d99005000b000b00080002c8440c001960181c0071b00720b48451142c010b0020f260386041505038505001b00300703503411240a040040450141151040030328100791400711030481c0e40c20b010381556004031407940a03a241404000d4500d10210b4030041c129480302c0c00c00703540c284040024840707006a41058809030505041410381d50208040c0141003008080003440c401180000c003d2180d1005482501140340c542001d40701c0c1d803080e00e413007001013000c5080b81c412100301e20001e8200d801040d00c082c0304828a810610556070800c001c84011030071404009010051000c8082d140c807080100141402c140001003010103008101112309814008020800f5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575550818 1250 575549568 575549617
    0x30c060609061706010501080105010c0809090c03180606130c020102040b0a020a020a0e0c0f0a0c15020c0c0603010f031101091203020a022d060322140606060a120f02 73
    0x1800c2902c1150152403c41e00209403c15012422074120b0708161603070030280c1c0c40c200056540b100d0400007222100d004211b03c141c9070fa6a424010301588403404441d032a4681403104a0003030004850556041e400704080190a41d18010f8600b07400b41a1300c004290a8840a8143d002e405030303401c24400124040392500010380e00180341c0c43e245008807101390311555291240c554808065918840d00c203001c00481d2584ca482c1c00c020503202180b0318120f26400340644030055a2540a0182c140c51500002d00b02d01000341080361040440c001c5410500c1c5514012007440d011a042c40001c10100220b148140140e015821200c001c128000c13807555241c1e00d510f4025188c01d088a0708038402c110060f80d483c0c010702e07488840d44030040040c80100307003582c1c08420411107030802031054141002458003403a13081184541508460300c24400c2030300103000c503c03109051010082c28240505d809104c40d50781c0641c8070107043c400745160700000407103c080e450350340d01a20a0201099401c00c680400420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575552068 1250 575550818 575550821
    0x604020927041a0f0c07080d1a0301050c2502030a05070b04150509100c0c0f08030c0607050307080115090902070b06031c0f0513030210050a020d0c02100804030c060609 74
    0x208034403524140540b02410503e4064540c82526006040c040d21400038041c8075015000701074690003142214146100d030508070080d85c441c0290701c8941d01c0c07550380968650030240038681e000803c0308a407034149854a100400f42d0180c40b113000f01d1382404250100e0564070280400c884040d00305095499154698150340300a52091188807070840d950002107000500c1b4000342c400d0211300610745640300e040c641d403c03608000340c01130a90b00321089180005162120034104402003da01014544851503e8902410164010f001900b40001003040007041940440e02506480050203030390300e10386041c0740c210380104060300a0701180c2c1c8002010010700c8040c2c1c0003148540390440c101d0703203e1200084200c14030900c2d1000c1e10085182600556070747c03401800909070203a01c008480007a2590307070300000c608840c00e1050001256002509042c0d1a906020490002c2d5203070402c2130b42401d0560200300300c0744010341044100034016000c5010181310710507041015401540604c07810340c48020650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575553318 1250 575552068 575552071
    0xe1513061a210c0108130204022a0f1b011e02030705030304030c06152301110d050406120e1b030a210e09010803030a09020a091e061205060604020927 66
    0x10894407503001614100e41c82405d40310310a50f42e40d440c141035040c050342440b021790070035040d01503890a8510ba10030717803c49120b03c80000040c818010082c842901c007801c1e0921410314428007403d14080311007031050f6041200fa800040b0312142c045905581c04c4412400c0d0302070800c000303069000020510082c59488201c21607410f00440080084500e8074080d000c1c541101d1042074240165104030981008641019245028041c148020300341342d02e0002606050143c05458085440840e0500a050740304a0030714141600352800c11040d500031036036907074031041100304030401c1505d426003094686092081e581e0b2a580a06a45003042c20f6100303500348441600c4840e0001180d42d8141030f01e503e01114000c1c100c517072501c051451600d03455000703806000540c1d010b980151042e0350001381c91a1078415001c8150b1649188403504941e80140300580300030307078040c1c0300c0f501c18041c90301d010580105a10380c001004840050359000302a0118102000406200e101c14080c5e124005e03680b11031f8058903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575554568 1250 575553318 575553379
    0xf0c0f0d08040c06050306090601030c030608030412060e070b0906092701031202150f10030803040b010503060112020315100b04080c09070207061e051c0e1513061a 72
    0x180c01c4603031660b2017180c04c1d00084907410790000f0a030020440c0d43d40a03510007225980c492501255075034541d050986950310a40c04120304029800074507050205901c5007400f110034100240003411310381103c90220340146c105042c0704020004140c42640c1e50201c0004200c0b0b0941ea110754640340d21610b041c1c0201003407005030381e007145131003d07a400103201103020b01b44142407005252481e16030301d95100d000c0e8001880e2505040c0c4210011000c604c041000d14410340c410102c50b4215810082410300f402410703403101464031101e018003401650049461003420181c8001c014070341e5680020884035004540c4142c070381501c00900410750810103d00e00700c01e210b056034442040e4071200740072070b610480c03841200001484844100014088034442581c0f01a90385040c0303040c4510002c82e4a0207000f141d400b0148140c3d05e03103c5907219001400b4000c5c02c00c03d0b0b0201d000c611b10303000c0c490240b0710b83e40440c0104151740c2d58090b0b12000300002800d40c20400040c2403810f0304001140325460140007503091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575555818 1250 575554568 575554583
    0x206190b09070e0306010618170102041e14010e13050601020109020406090b0325050607032c100c03080c0d09060e0c0909010e03070b060117040302070f0902040b0f0c0f0d0804 77
    0x41000c234001d10503a9a0b08c4243c0c0c2011260703034a0440225250380d821480d026855408103c00a0300d441d12902e0603107031000c20f02036608014600184020040c46039200c0b0342c14010200580011583c070780720b808494441c080c0c8049555a21180102c3c014803009100035405440d00d180400c0d01101a0700840e035281c2c00307508449000d01030440b80401d9100084c0000398484000809100e50f0810300054000c441c441d04101105502001c41090351010544e80076044000142c0a03800c60302c0c12101100d0074440d2030601840b192850b88000b00614402003000685201c0041c00103d40070780c6500101446270400010401e01c07502c20941070322110a1618184075821880210f00caa1006200b040509062103009514140f00c540d600c0c0c0078a180142114140724020404020380e00b0b800300b91900c128820741c045e000c01070421440459003805508208420f0381b051000344003a540060403180c0c901c0650b082252250000d0b62050320b0310950842540180c018802100311203604807501900851140f0f10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575557068 1250 575555818 575555821
    0x3091f0507032a260c0a090603020313120e130509010e2b030209031b010305090c09010e0408040f1e0e130f0203100c1d100206190b09070e0306 63
    0x140c0440340080f943c510031800e0030b2a103804078018090905980444070100050740500e04103000846800c9900300b001d000c002074049801540f2017030404c06030060703080c11411400c0c40c1d1048004041e03d11001081d80507401c144030313110b500840b425440040000e00000c060b408809030f040c06010300341da03462079940c01d20041d40b40c0460041102a00d19640303d8a01c0a03988800610070001501c268507801415401c1082313500c2030b1401d01c0a0a8098030105079070107030b1689500010300b1140c0003010104c40d40c01c2480703014107075075a078807400781140c091240b0010940c8a074100056584140c1c7d010700c45042c5403010016049006241d5085007210492140220541e01c1000c003800003400c545154040000086c0e0500154001c0c811100a6001400b2519032040402c181e030120703609202e042011800084909440c40c0b51a201c0c0082400203648a000121540d00043d6507804050710b410b92555810070610740e1400745503c403024008005180203c076081000d0082d100740da80b03c8900340280503110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575558318 1250 575557068 575557091
    0x41113050a030b0a0c0e0a080c090f09121e0301030b15010305190e07050405070c061a0102030a0809030c0a0b01080f06011505090111011104051305061503091f050703 73
    0x641c1100e400c005441001d039214242c00f0000c14020300720105001c10a0b08070403203611f50348000b1003d019031900408000e00868100f2003100d5000b403c0c0c1c03444104400810020100c08609000044540c045041d1240025550007010710401c1e50604003450000c0000418028204e4140e80510000400b094030b42038610011010381c0c00c1112504241c480d1400781003069940f40d440014120840410343d25040d8541000a0035100280c40d07200014070003a00440500001c0d1243c0030103030004004601030203403034cc00003030740341e01803810101e081c00054000105190002c0c41150480150003041e648088150300d04a1000d042c00e016501045c0301c0d41804146010300080c02e82d05950b90000e41e0382c00303d03840c2e900c103c0e11540508880ca040001812007064070207003d01a00502c184400c01da26120360030300d0240720b524900400241681d40c1420b003444901d0300d0320003400d0307441840000301903580d540d192a513074500300810f6011040d580107200d00c034441140c04d074019400380b51103640600c01e661048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575559568 1250 575558318 575558329
    0xe0c0304150b0109120206070f0308070e0103060f031b030602030103050a0317060a0506030c0c0102040b1908150114190f1b020f061b101b09030b0a1a04111305 70
    0x1403003150104d10000028008810041c00f44100d480c0300618642c074103412550b99031003564509100300e012178482014480300c80d4021002162113242880c08008803480c00d0302e1a148051980300c050580445a102d500754a46e243d60f614001c3d50b080207080d9070b2942d60349007455440603200020347c002501300b8421000d01640c07110345d45c0200c4005005d0007006040038200140b552001e08804e43e901020001802200800e0002e00028400012010749421a114110398582075410000041001c0302041003400c80829000086120302840c1680c5594101c080d000094451404803940c4c00418100030080d041d403262200c9103909450713030380c911510500310305500c0100341c0c0c5800961040150007100680c5c11715102910110100000004080481c03c0c1c200342400941c0d07415908481c0c441c05145051881c6030103142c0070f03c41902d45407503050b107152111100c0240c040d284c0000385440d01c2c228241d051524076460f40540000740101b1078075045007418115540042030201d02c2449140d800100382c5001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575560818 1250 575559568 575559581
    0x6030506090a0c0e10020c1828110d0b040e30090d0309080f15070c1a0a020c120a080705070c030c0e040b1605160c0e0c030415 56
    0x1800c1081c854071280318110251060034003000411583c003190119a9440d0b5031800b2603410a0340150201c0003080085c0f04000c2e032171074003005100c035640090005180d00041c040300c01c0c0561030304200c3e000c0055030f9541c018203003280d503000100c80081b801d083c030f21a50360b01400b5240703400c8800300041e480d1543d1b00c80d200c0a945c0d0348049044c440299054001c2c00c0c408941c40b030131802150b050329020041c400910b10700d0700560151300080e1040428010b14400b00301d800c1450010000901100d075100c04418148100289600e00300f15034202080100610818030f51f980341941840780b802e43c68008482c200a400c0520f04540601c40d0110710140169800201e800404c0d483c1e60349071040d69001d400344c2e480e038002c0c40100c40c00348040c440080880c444034240b502826250f00403044030b080a08258440d80c0010b08603400400309243c0c124010b41d0080100c40c41500c00d08080c40c02d540b003a0a000c610151154070012808070403c003000010907861000318840c80c81565981100d403a02e034420300480d0b62 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575562068 1250 575560818 575560831
    0xb010f02030316050409060f150306030c05060a030e062509080303040206090d0c0b0a09060e030d0336030f02030f0913110a0e1e06180301091b060207060305 69
    0x80001c100400c0c403c808900d40400103003080c61034030ba966490002152203503031001006c0741d41c0704410b03c0000024401903031104010b1400340252401c540703d01d1f540c84020b2283c540704140008207034600390b01a403c0740030b00f4058202034950a02d40800740340490b401c021000d800c5801c28140590f480f6000d06991801e591030640294110303511035080c0030940c2d03c0741e40803591100d90240c3d442c0000da0507000390300c06024095041512501d02000240075085030340c0081c801c0c0b100c500003c08043e1000200190848810f29003c01c0120301c0c2100340451509403107004100c6040190103208940d00d120308a88002d109941d02e02003081141c0c0103d03141d020b11035031200000c004221a05680c6040e204e034031840f05000d000060201d0201c0c04008255200f281100040350344202c40903c00e180c00058a05c0c11480d001d01805101c9450001800500c55103119082e414a039002e0f80750310751030960040c1c00082c1d1003a407000b095245480f115010046d40d01c10107006216405c00818154805d001d01c034040d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575563318 1250 575562068 575562073
    0x30d030c05030c1303120f140f07200d0309050a060302190e04020d060914010f12030c051203010308030f060406031208070201200d0e010504020906011803060c0f02010b010f02 77
    0xc0b07403030802c0101d55102c0c04140b015500c02c8400171001c03a031843c02110410981c1d8031440c00e01d0250000c00303000900f041640c9140301d442884121610b030032200840c1c0425605c541784000034480d518403000a845800c0340c0d01d401c1014118514101074110f0380032002e03a00308540055240c2d9880d00210280e1050080139112401040c0404446034000e109685a0481c0203001604100300180c91004032080ea034480c142460721000148401010103002038054441e074295031008a00302083d445211a0029004007040544951001401402d028414131803141010050b074a5a5a0801040641064030060500150180800d440340317094031524048a501060760000030306444010341d00c2c070030000c2030b4500355500d40c0100907201d20110b03001c00945000b814115101c0c80b0010700178003120b200114a1205a03d800c080c08050782e100e01401d944074000f4a001d0f007d80900a08540c3c184500d540020f00160502c40000c200d64ac000d281d01c03180300040e600802c541031030040115504a801000315001d41c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575564568 1250 575563318 575563321
    0x9241401151202190507030e0a06091211060d141302090c0703020312100f050306190902150f0415050a08180a0c090225080d02090f040f0b030d030c0503 67
    0x82c000c40c510b002d0903008450042c03c0514842c032002440148030b046600107000040c181042503040307081103801e07107c141c400c19580d604085001c2d00034000781c0905405807091100110400c404500d08000d00b000180c0030300e4641d21031003010000761003c001520426607420000440040f01c2c40c029080e5950014102d140c3c1d40c80301c01c8041c20700d43c0042000e9046000c104042000901130300c0031035000300300e20540d0b40d4030b1030714004d9191460300e0543c1141c1e1003604014180302d00d03904182c40c9134589806076140000d40701540e00c00180c203070362400546205a81f0208501c901508820050701c102d0700d8000d040c44031f003c40b07000c0c112041c0c0b180b407000c00003040134440450612086c0901301000544003034215007019485448690000259500c81c1000d650001000c0d207100c0909000c0c4841c0001442c4407010020f141c2e951903000b406580c540c108002c6d808664003d10782d4030140ba01000c4407004e04108074132082c8080d03080203460200d1407203000c0c0c41a44007500b0340034401e10411428040d142e440c503040d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575565818 1250 575564568 575564609
    0xf0311041b0212030a09062a1701210203060a0626030d1d12070c0806160827010f2901030b03030d06080f0c03010b010e1309241401 58
    0x1600058030005405e80c1c0e407407400c07000031107501c00e22841d142507455480c3e5080c0c244803840c10000d00318690b8420404805100104180e10f60440790541e4110107005040ba405c6135100c201c0d000812030080e6251290230148540030049070701000694403040900d43c1003070390220080846d440d012192030316942c01080b01c2c00800d981c0d94807540c404558080c0e004620340002100b80e151040d8107038840c496190004400c1c08214032040350400030220800609258580108008420903640005005000c400c0001800b2060055582522607541071884140803654544e800d00070411901000d1625141c440f500e40301d4104d00070000e510341220315a4004001c480c0340114054803402c0403080d0075100501454584545038002c40000e005c05030010262a1420510310340f41108001250380a80d14046841001f43d0740300800002818050f9070089a020034280c000c030040c054444081c10300c0b0301042840510303c443d441c407030084070f00302d000a0000071060b0040d2040f01400b84204190500d02c80388401c603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575567068 1250 575565818 575565853
    0x703020705070f1d0105030703030c030f02030903120d0c03050402062d0712080c04030203070303082d012919020a08040603050103020901062c0a0f0311041b02 70
    0x892142058641043e50b41010000c9104250001030f030614161200307110000b20b283c00030740140022002080000e01d903841c09440190018406001c0080700703e8000c0030b40d80200212140b000d000390803541c0b80c40ea980103080790340d000303185085403c0b400c2040d1812450722074060b4070700aa070000c203942e03d0165035003038611550b070141282410411a202d5402084038414004e03002c154021484149190703102c1074010703d80c03400204030f260080014001840562400a030f10380c107a80c0d050401021948401001d4800c0c1d005400348011000d0800c1e01000c4000c0c00c82040e1f5040f52030080e40c4c114151814007414400d103105012110249800348018071408101c8071580d9401000390040c1c0f47d000d040d944404081c0d82c0590003c0340401d440b04010011400c08800700e9004120b0391820002690341c02041c540e40d0318440c1440001c1040030580101c0329a10400e850b00145040901003600660ba443e05110b150034410419102e5407600c5e94007000029240034a507103040c142d0303000c1d10110000101000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575568318 1250 575567068 575567077
    0x106030b100e0d1a01030209060d120f03060b0304050a0507080f101a1309050d050c10050622060e0a0603051c05041203030e0d0905010e0d0602120f0118020301050603070302 76
    0x30750010720f140c203080101d04c8400a803011145503a04a8042d50304500501200f0203000d01800d020355101000d07140030440461802000248a03d00100051304003001100900f46035000300d10600d40c000184402c1040016515941034030600980390703040e036205640364403004451803280d5250071001410f044d400080c2c0c401e130200d28940d05c007601200003c0f1702013100307040086410b84920340e0301c0d1101302c20312a080022040c041104e15025181010580c41c003030301d901e0102d811303124158131000829016561282d40d00d00c4040b652145188000c01403207404043c1410b84900407140e4041400304401004030b00079142940d401200800d005110301c0000e181111120001404105003444041007a04c11803081c403c405003c4e07030b0003040e10710b441d42800e410050a040034405100c003000c0e0420199030498242d82c804001200d0544540000b030030514080d205100581c184101c2c03800401c8000b016842400b8142d40300c6100d82c04100c45000151402ca07c020f0003441d921490500000d00814840d400a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575569568 1250 575568318 575568347
    0x312090703060606081e06030304090f0e0d02030409050f0621010b03030a03020901030e0d08010e1005031005040510141b120405060103030915050d0b1c111810150504031703040b0106030b10 83
    0x9140200e601c500c0d0a003b8200b032a02d0068000080801450259028103a00901c401090501604152000403a1a03000c07111007007a41c920011040340c0780b08294461741c2c80e41400380c01c0c0c81d56070542400c010001e6025800b424040307481d11080004900000558140002d484c0d1100d001e20f03424401c2c0342c48103c5000301740200c80540c1650115403600c09005480b819002c0d103101081e2402d03b403030003500741121300d13189241c0d0305c0c40d120090f83c2d04035204141c1034001c0d49158581d81070b940120130a0110748148040c5a0b88003a2400500c001c01c1310014466040b00e010b40c0e03c014411b6240e880c0a40401d80d0285890300203041404095000d07800c0d98400a05000001d00da10318040c034021038800748140c00b01e8103581c6071540b0403000030380b410f00c43c00d4a01103440c0e61080210500d0700040c1143d08020794050203205041050b950007143e0f005004032005150803d4910326800c01101004070f069208071001c41d07090301690000500d5a000c0e000c0c0503035420740103060160103041c50804441544004404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575570818 1250 575569568 575569571
    0x19091d060609043216121203050901090f0b06030c0603090c0910030b09070501020c030c0303031906030c080106181a010f0201021b07140a080312090703060606081e06030304090f 78
    0x101c62012030498507415982d5022000c1c25281801082c51360084000340d10031b001e180156840000003440108156803550a5820002400d031280c50003e0b005007000000100052010b40c401c0342800512418140310324400c9044401d5450460f0034408180800c0d06c1140310360784031070303601105071400041f9154440340d11910081c84540d0b80c2c45803204d1150990b4907644942201d24140943c0d64140111040090250010840b00031004003003982c3e071100800c00c2c4500c07650380540c141440d4460700654001c64205182c03414850710f401130f55001301a14420100c00c41030100a00081d1600e030301980e0075189004a030310040c0410040150b4a0500c48925041195420001101e440c440c007104074806061840c01042c41c203081c04411150407008464162183c21580d9003001030315400030464804c0080d00207948199101c564655150101300c1d04010941410800049001c60340141603601c108600c0402d20341544042403603c41c4c24809035003903a00b54204201c207100c4a000e41c2c01c040c0c042c0801640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575572068 1250 575570818 575570873
    0x60d0b060d0219020c1210110702030a030f020601061701060305090c1306060905061e0c07030b160e040c080106030c0509040c080f0c09060a0e19091d06060904 70
    0x11181c00300e82c0102c2e9964011040d24001c07803203032135041011880a0000303458400d268582010056500d4210510004003640c617102d00540c201441001d80d10295070103421202085410701d8054803171106158901c00510401000092003031050300d2071600105d00b4000c519459082c500b0840282c08014000d01a074440d0b40c640e1141922580c640540d19030791900c0c000707400d071b0600300028500101a031015100b140103101c42104008580c1d100c0d4100c005d44d480403651000e42508070340c01c2a10940c00601603500900401a4416420440e06c4412402d42d4824440f02c640d0310401088841e10010400050030980050000078080d502c088221052400c0403420300140700700282c1a606401c1d940c10025112005100e1000600e0030b485070003403121885d403030405203001d003ca8090300602421000700700d89501800b545840e00100d4a00c5d0a01d01c071081c1105c283c0f82c0000c00d0141c8100403884c1c0074000f501c1050038505401007180c501840340103180060545132a12803449403090708628036442c0e214000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575573318 1250 575572068 575572087
    0x1b01050403030c111306080c060909151503040c0906061106040201050a0903080f0901020c0a06170709080d0914030a05061b21070e0a0308030a11040b0d02040e0a0b060d0b06 76
    0x40c1d403a45400039000307001c03c000781000310490403d08c800d503000340210b0044c0902001580c5e2040c02560145000701c98a00003041c04000803009000e00e46054480b11000050106000a0441d44030030b503002d040d4180a8603941d040200d03201c199100c00b06005402c0040414015131280c1300801c40c07003261b0f20344030503210f0326900d44000711b5002c1030300c0341c00611000910351040c3d6018400038440440444068012a10b4040302411400e80c0c0e00c00580c601039000e0000348250300500f119406003401c1400c50b0090604440c01610302c40c641e009000b4001c00d5011043c20500d80001c0300540241e000019268544440c1c1007496805019650320a001209200008540441421240003210004a520035504004002821181103016154001c003680070042c070104400700c0c102c941000c0d8050300080e580004669900d55406903400c0142c01800000309041102c1c9960050025600c41070b0140105840303986810084500079810301c0d4101c107081c003c1182290182d400450060340c0940390a20b4004c01e903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575574568 1250 575573318 575573329
    0xc03121819020406050d020a060e0d200102070e011508040510020a021f061a03061311070203060a0e07170307060603060609180209062b050106081b01050403030c11 72
    0x100320300c030510107461100c42949024002c43c2d0041400307aa030342d0100c40003500030514001031401268103104c041d40c8886280d40740c001c47c1c803400340d070002d003201900c50020440240c82c5080c0c96809005108894000c50185440e50000303040750311860241c0c40c0300d01203000544040c0d4000b0000d917001d01808651842100190008007805001e43e4013800d003101480402c5100c070241c0c41540c401c020324080051200042c40c80007100380280c2d21000507101d95880000460480e032403640a15072a080c0400c41c400c1c01f240f4000740950902c21803d4a403542c1c0d442441a0450340c04850304c0440b035005490400c0040b29040c5040440d803080010703030b49002c20380d07110031080e81d01c15801160002e50f6147d0410002c0101e1241c0b00c003001200e9040c80d00c00016070000b90101c84060010707449560305c1c80080d034205030038580c07600000701d0040300303000b009003d42032180c000c011500c1000e40034001c80c108294840315480a0010780c01050f11120704240c1940c408695500600c0403c86a401c1c4138118140c2580d1750 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575575818 1250 575574568 575574583
    0x7200106030c15050c072105150a0f0b031504020a1d0406180209181005090a0203070602060c0a1d0d060c02010606030b0a181116060b01050c031218 65
    0x42c200038805074074000c907122100c00300c15190340800c002030102208400000c0b40000440c2c4500300e040d4444101c45030300704410a90000e00501d5031059014490746680030102140c42910035000070001c082d408900b4000b0340300f0000c0d459131715802500c18000c0d20070303d08500c683c11500260042c14850f8480c501001c610f00f21150381108940c2c4001044100300103401a035030b80c030488024401290315907502096541502a080c000d85180000700304a00d041e08020545a00c820180309101074100441380750740314041c03418164001c0c010541e010071440d000040543c021141d1200c40c4d80740c100707403500458981d0350001c91114140544070f074081540e0780300106078081502501000401100d04100070f070844100358009070915082000d00c00c01560740d0341c503200461780001e408481c40500c420700e00c80288070310900c00d01040720109465002051000841c15450b00c0351800300309042c6028015691401200318500480e401002410b88840103a8040d80c3c0000c84203074170081c0c0d00054024141003410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575577068 1250 575575818 575575823
    0x10020a0b2404111806250611090108040609051c080f01090c090501050706060308070f050d05090d0807020d02030708031305040501050307231804060c030507080720010603 75
    0x111080c0d2440741c1000c14003503000c00321010801c4088408181d0303014080c1501e1a0549a400305000c645600c0760012902d00800703640105140740c0c0454120390000c51284030035030310149020715060640806108070341c0052016120500d00c1c0e40c3d00e17507401002c0c0454001c2180c240c0112401070715885002810b080c0c050415031208401c030720744090328811000050f1300a145450070210211202a0042c00f4082070f61400c0ca0010f03540e001c1d44c10300303c0c040d011a902c001c010807400117002c402d01447e440030b40d0b138503031040c000c0d030781001c00e90b907001c6030386024000c0720b50351251001182a00041040c0006c040561029119910b001a0350700041c2c1440800c8e800042c4607000000c00d880b004036140400c10280504079801c20241d41010040f0741d440d0b2040c010340001d04041022000840203201c020583ca1000510603e11002c0e180380c000140c21040d82c04580d01410151610f00060080c06074030f208243e207581c3c0240f99070310124101c8075007030610a203210020101708002081a001c0c000c0801850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575578318 1250 575577068 575577091
    0x603250801030b0702210d1413230601060503090f0a051006081b0103020a020313151205041a060a080118030f050a0c320105010501021006050f10020a0b 67
    0x61442c18030b050f8015000703014000715080b807030b11004030441d40c00352140500c06a41225031a02d8a0601140042099000290180340f100b000c10000100e05070542d804107100b9800070384180103c0c002c0c00b143e0440070402c1200c0790004030041c4036080c8180051030f8400f100e98222000105210304147c1270400818042e5040d400c18003228543c0041409031100800b40da20040070000f45201820f441a0a0560361604264001031000306852082060746c0300095941e48145240760b0f10b085603448040c41450810118074014441c14000d182c0b48035481c812904401801800360002d02280320442b80101400c2e0b002508000109068000348105003805c2440c2c2c215104500c81424040c0409580c6502c840401100b00042105c2643c401141c007502a848482d03807200e13400381e4003040c807948012605904140c05140d2110061041508150f048680a0b000d9903d500068128042135540e0b5001d96900030740d2440322904e41e070030300c4071007194080d4451041d01c2541e10b107941c1d009000f41043c0d41000c180e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575579568 1250 575578318 575578321
    0xf03271208010b1213140f0d26041b08070618141e0a03080706091403040b0a08040215131a0901200705090709141c0206032508 56
    0x2a80007010310340034060201c80c80d1300b01000641030f145003141c02005c07061581c0300391101d0010040001014a8040749020540388400e60003d0901d6481c40303c128900e00041002805c207020800034a02d101d0a20074444c40740c40303a1354a0303845245a800c286da040c240c0803140188001344c2c500c8144214406061141c0d41d0714120648040349201d0403005810007002c02e0500682c01c007455842c4004500c0c0b92141c50480c480c0402d2260000ea203a40c0300798400340c5034040c000b07200002c02138998408600c940c40362102a1544100d56070203580c0340902e00840c402410108108440b960180c0f2285038041c0c40104032003950000100c2c1c0c4c0c449500254804150a0514071051240c1c064008d0700880c0d8501d0550740340d04000b04030700001c1c81d034640301c1709070702282043c00c0281c44200403e0020102400c0041d0000c0740501b0710800081801b007540c0300b4140301c01c1102c00c0c03229241c5443d90070128201c0140c174041c40011496000c0260661010b05108660410000d002010103007524103900c81043c40c0c1c642d001c60307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575580818 1250 575579568 575579603
    0x5010c05070902030112060b0a0f0513110a1e0801181a030d030b09010e040308010902030402011e0e120304030b010b0c1f0f0b040504020a0306180602161b03030f0327 73
    0x2d2303c0c3c070410054811030480c03009000c014016032251040724411980c0d6010034403020680c000030300c0c01404005a1110009281d110390360807860704924642c1c0241c0055040000500841e48180e0a0003450480a40b01418a4480740c20750082451284400d0402140c0c1201d200080c0c85d205a980d1070102181c0c0312000001c40f46890ba0f44240100003001d401d0001d0310b80350b40c0081158405025071041d2541c040702040940e4411101d51345421f1980307948602110980d00041c202c1045086298811450744180741000d840200c19181140d42c001a11007142e401d100d80d4041540024501918900c103081a0140d100c2060201a01050303840074001081515800d4107029280c82e114010301039400e0406201c01a01c4002594003240d4001000061420244030007059903c0c500c44003510070740c00480c030340c0348041e01003a41c204050b124100c50b81d29542c02c2e80ca50f240d95100ca10026003c529440d854004407402a04446403500c24140c24241c1640c120410740c2000094980c20303200c4007410240ca000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575582068 1250 575580818 575580821
    0xa0e100501030c080c07020d0c030503031305060601050c03070b0603011b0c120509130f0b15121605041401050d090311250915030b0c0324090105010c0507090203011206 74
    0x1882c10fa640f91010440c070380300103810f1880c455a840203000300c0200500f0818031142e00b024202a41d03001e000d0701d5480c00c0104141ca81c51051a40c1a11940102c402107541580540d00f1101103001e004040c605007140d64840204d401030007820f2541654031190318044192a40c840c0074008441e5440350542c021140c00c0c142c280043e250030340307401d02200b0020035130a652400e0041e500c2d400c1c0d40d000800d025485415600242880c1016150840134403d180304045000390f01a00d00b040302d0740c00010107691420101e100030405c10003c407001c80c0003040140507440454617401904041818140e2502600421110440300001c9080c0c0001c2c03110310300204003034414000c01013190300040b00c0484100c181043c1c000d188016205180c0e00341d070348007942060074030508003102c015600613a040d02c0340d14007101c14408951040310390b01d03041c04210349652b829113840034241c10326507000750000c182c5a0905005569020b80c0d18000d459502c1607400c0000d15100500085010340144408005602401d00c1c0410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575583318 1250 575582068 575582081
    0x130609080a02150105060f0c070e0108031c060e0613061a12070c0312180c06080709060518010c1a09010b0f0303070b06010c0228180c08040605060a0e10050103 70
    0x1008500b010f001002299500d4042c0c61660f000c42145641e9880f81424036890859607501031071148031420000a46040040003500807507013414560000c540b540100f02084962502410380c0e1420b000002c141a4148000001c4e20410510304c00a0301a0700c54a0241010340301c0b8480b0314103981d00090961070540d0107400c858001c41daa0400c40301c1c3c054156805082c81669900c001c45596840c81c00404092a80d00300c4103c2d16001010403800585412004144503402c07500d90000c1944040d000414a200f5001c465000e08144070381c81d08c0c04c414200449114525900c140c850001c50440038810a00451240f4045c0454500010b86200f807a0b081c031104012034400d2502c0780e042480510301042e600c0095070341c0103409181c0301c804040c09200190408483d24602003040780c40d1035100050b4010f076a0b541d001e9505001112100d42c002076981c4055489100441000030302903070228002031402d0b040250408002040d00c80c4040d12000494640c003411a808041c10102e80010010340d6054030612 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575584568 1250 575583318 575583343
    0x10090b0a0f0b09040212012c01050c160303020a05070642031202160305030c10020a0c030f051c02040e0f100e060301140108160503010c0e0603130609080a02 69
    0x1404101c0e1540b000660880e402000a0f0081a03481a00c41c2640001e520250215140062004503140c05d81e0089124200e40311000b012986803001189442003410b0603144800c40f83c56080e42c1141d1a03035002c40c040d401901d0307058103000040c825240080e20038007503541d181138003c00240b156250115441420f1403110310100b210203003411013641c01c4c81600c8006c800d5075004503c2c140000a0404c1c12842c1c81c2c0c204a150748075003030300c5078080b041041c0800281400901d840c2220980c0c004201450124464a18075001190302d034910200000d004541911241c1d00c0750400e1400e04103c0140c643c9008600032080328400e41c0080e09100c1410201c0071241c00c03d5080308a03c51a1030242c994120140b801d0040032508140040040d00d160b42c25000250300000b900c40c47e80d115691443c1c01030391002c4402c0302c04010003004402041900b41403250407201c40300c99803058185181d2809106841d0302c00303049035200c00f100f01c070810003090081c00b804401d144138003a0307541e039040d00800c001e05003030148642 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575585818 1250 575584568 575584571
    0xc04060c332007080c0307021c030e01021f0c0306080304090e01110f162126070e0105070201020c030f0303040c09050402090a0e0102070609030e18010e1810090b0a0f 73
    0x2d0000e6811541500c3c80154050480c40d521006003c038545103015088000303500c0030201822038180b424940a0001c0305100c0e440f00e1054040c85001a80c8400d2034060025481000e80800300766050030b03800c00181e0400b24103000942c652288041d50440d80280c10828455480300c1040da4030b944248110781c0755901d0418181c0c200190741980040d1b912075080c40c0200c80c4801e5807404140078401d0030351101030303812204d043c0c000b10441d103014085444580703100700040700004040200350b6504c090a8400c4401e651249000c10704d02c0011f40d46900903030360a9045106055404a880c2c80030030001186d022201c005540741e141034589604018001d4018081d9281003105000046e21100740381034100702c08400125107000c80c1e44881c0d0081c000c002001d000d003800c10554205140c0c01c4155810701300e2040e6000c01481814014590280c8020b202e4009102d4031080019900048000c10859840c0d40030292200744107400452000d4404081007aa03400c060002444116036040c07013484c080d040f81290 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575587068 1250 575585818 575585861
    0x10e0d21210506130203040c030c090e07092013090b1005070201030203070e060d1a030c0a120201050712120c030e03070b06060904020a03050a0c080c04060c33 70
    0x41c5051101d80600c8105a190701c41010a8455903002c85000b0860320161045440c0e140900780301d101c002c118841526043d008840102d1040b006014100c04990007100403e00c96180c02c01c1e010040401000190100c0740a03101d08610300081c00081c070701d2150004023625540e090001da80102c40704a01060301c140c10300d174014048250060251381c1343c65024200103841e80e903800c0c403c0d60300800081305241e2000d0005030801d000c1b101c0b50320101072010030315059041d03042004c2c20b01d6507510300b03042d600c1d600000040003003001891403002d50048606c1803401c4e608044407070752001d48200d2540d140d540400c0b03c4620401c600a2244182050320320b00e440d090048201c40f8100580f0b9102e54031025200d40301c03510000d2071544442040b03c8581d080038204543e6040680740042c001c003000e03980c41d10198240710000395400d01c1a500240581484000c5600e0070f2325104064440c083c0720102221500c150007406510f401181c100200e02e03580fa1002054143e14002000d4121101e205065045910000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575588318 1250 575587068 575587097
    0xc0303070b01030b190c120506040b030a0807060b1903050606010203070b070302090d05060705040f0909240605030a11090a0e0c010309080409240911090906010e0d21 73
    0x80c1d00781c11070340c0000c4c0b91850b540350341c000411286185072620054506201520428580c4054500310340c00000104000540b81d0008010540d220701000c43c2d8154440c40050011801e503a0040c0803040c403501001506406440220b0403213080f80e201182c1d00d1147c040e00704180001031101c2513100a0074800345180028998400d0701c3c24201815800406030b02203100c04450322401803140c01581c0242c21509140380c100720041140d405402054180f0009400002e03881c0c03504d0240340328660748100300021000081320b181030403803083c84040c940c0c44c0d101c05c000111307a1024800550024050506d116400750b2400072b2002c0d0260142c48510000d261200c0e040b16010041040380903901700b440d02107016103480c240180280a01d800c941142c03850b0074214015004140444508005103101440d8400c0d0781c0c5804400301c070a4840062200001006000902e107400512607a1104050504103e42d1a41c417000c0340310310b83c02000403148031180c11030922002c0c000301039007503401c00d0904c0c2c91140182d168 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575589568 1250 575588318 575588333
    0xb090609030a110c120106060f0513060302070c030c06030603031e09050112060308191821151410080d090905090102092d06161b05031b030c030307 65
    0xc540b0103040000c00240040b0490043c0851413020000400c407120301180c4e482624024001c5200700e0000c580b290300c48000460242d010780389000c0703c10380710045640c0303031020507000381d40320359400c454000c802c1030040000f03114640303044091f1540c1d030344c0003035680d04510380640b05107841000d549191000c05009070041c1d50001e024001d4400a103071100d0300000300001d100c0503004030b0300020311410000c00c0503420350b003c8001d074014503411541d8415501c80110611010400140124002400c100d4403107a540d1b1403440f00500040e02c43c8a101d50040700c2c1884001c211406142c8203003070182108184000c0504040080003d8500c04016010700d401c1c0f810b000d00550b10b00c0c4207105c4015104c0c030003e60051001c3d4150303600c60a0150101504082c1200081880d04099808c1c1d1202c14600c0000d2a260038544103658092030fa4180d500d031100c1d056101d00107906000303050995185081d0001103120f403410311601c121003248180d50039039001d0001c1011b013040805203000380682d005200c8680440d800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575590818 1250 575589568 575589577
    0x1401060905100c03030f0204080a1104060803030a0203040c031e11271503070b030906012102061c021314040c0806191505070b090c0a14010203040e0f01030b09060903 73
    0x40d403c24003185540751038142c2c041d25440310049981e505c0400c00150a00380411002140c601c11007645040642a5041008540c950701840c0f440e81e00501c002102445950700071500203015408140d041740d41d90f903036512906401d912043d003004e103940e00c0c201045121002c0d51240403048455501d400a01401804003aa031302c43d051500c0381840c00400c90140507034085013141c2101500345c0e1881515080311100c00d40c42503038050040e101e01e03000001c0d0401c080014102c105560034110001980700e03001c00c04180c21001c00365546c40c100a420740d958110500c024011600300304a09002d10b86030142d4804081c0c44081814003550820401c0c07211550700c8802582c0c012400c80f6030041d4951081d0810005246940183c01c007036003103541140300a90440003038010103209815120305a92035207441c2e0f4580e54281c9001d5003040c078444d030038042d1400c0510382c0d0114280601c100c0b070501e5501e0b000d2100400f400d6030b00359551490381d4014414862070f030038076580c080940d4000300100e043c4505400d035a84907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575592068 1250 575590818 575590849
    0x5090613090e0a0321020d09050109050d020109030206010b0703180801060504140405060a1104091113080f060106050307050c0703080a0207080a0f02090601030b280f03080403140f0304091401060905 87
    0x1d4084450400d1180b1b90503120040d00c11a0700300130350b90b003a1524034000c1c12400d0041c0c0e81031094805c03440d1071600c140140104150300d9400750425901c4c0040007138090700610001c4061000304607102d01e03807040f5905550010302c4400300100c0d03043c1c40d203418071040343d200d110350900c14124641088003140001562030b800280400b000103000c001d0350144950743c01a9007101e10490300701114250841002805441c64801c20740a0074002c590380d0070115a82d0034034020b1a407040c0c00c04001000094080c1000d90750242040c20030718030301640628032504120090300110386401021a4180300d2a50403c209005042010000d14040c5800c0d00c84a000c124000b1000313101343d0100000a015034403d411001464030302070b0810030701112105042240c0031a1007810301c500b4502030300001e16189010301820450350800480d03454141151500500c00748038040b070043d5841116034454040e002003008000800302800d00080e82c07a02d664a1541c1440103a100100308620004188100d03680c80402251020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575593318 1250 575592068 575592107
    0x70308150d0222060b04140f0102070504090f0b0106171303030612150b0306060d11030c0307060809010b01051306031505040617071e0e040305090613090e0a03 70
    0x140300400181c0c54518011000b50031002c44070458140c107040c00240700900c82444000d0084175118071a200141c040c500c200d101051200714825094180501c8000c650070061060f0382c0b1698564001c10140c810001e0111111407031490108103121510000c24090705007032400303511024900d01d00207161315008e403c1c4c0c00c1d82c100b00000401054000d46c0400c2c020300070014580726000080c2081c01c60100311400c00442c0a0402040c4416480d0115000f4820074005150040c00300050310351000020103071003c99010301c94040c80c034040303a0741001514010000790344da030401460300380c0505082d54010100070741030040502542e03800c9005400000c3c262042c910f0000b03100000708100c092a00d070540d00154110746006001302d074130614904a00d1041800c08101c0314110764a074500640a07125a803503000710b8107041d10500494220403007480c1c0260080c0f03851410b0000c19800945c0d142d010a0035000c2e080c04a02080040003481d00652004049400191205d0459518094403160348a0076030500b54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575594568 1250 575593318 575593351
    0x6060c1502030708010b0c25050301150e010b1308070b0309150403080a050c0d0e340512070e0f04120806010f121104092018150702042f070308 63
    0x1078804000583c001000c8c0800d0000c500b00304034400d081c4107424001c1c1800395083c2118100c1c040c0c0842c1203502102c1c04908441c2c240ea29201c244082a040604d070070350200c10200001418001c2048100c0107000b041000554034202440d90910f05000e00c0c1299445603a894204008170360420402903100c0708150b00490a83da8041e0b01d224240708110300040018686100034203103c2000880c02406c0c1400303a84581036400e00c0805412000c0003108504c112001d0b12000d0003641403000e0040d00c0000d006040b00c0c6030a840e4281c0d83e0070340d82c0455003001e04507841420041404001d0545012046007400d2855150410710002081c804a03014504140214103243c0207058040c0d902c4850000c020110f407544468684c0e000c9405006c801d4002100706007122101d846070801c40049444682c0c00a00d0076105200160603c0ba05a4000d5401c9030425002e100d0500541c5441c0180309420001100c511b03040200a601d00d215448030180c081c1c484082800300100081d080101603801602c0740300b0b0070000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575595818 1250 575594568 575594587
    0x80105030f19061b0c0507080102120402060a0509060f0d0c03090809040b0a0f09020309010e0127050c0603040f020a0b0c03310f150c02060301050d06090606060c1502030708010b 78
    0x34141e10030124070031820b00714250305105e5100c0b05041180344507500b034030b40040d55018032500380d014070030b03541c260b4150880100d401490070000030004550f150415604201d001d0700025596007002c0c94130001282c0000720449003d0b4648180068078400c0d0a00304030392030312074580c0c040c0d500640c038405005660f1a020300e051030b591000e52400800340042032480ea55203810304070002e9041070b1694cc011b0760030518580c80048040c021008400f0020407188010720340e200c4074501e41115484142c0c0c0d41d0141d1b03c1101c4054444c480154422806016005114441481172140080044c4d0003020860030034400c40340307607080102c200d9004100e0050441c000700760714540580d038100425070303241d08070107062000269420002d840004442143e0045030104550705070135180c1c03803040e035002903000b03500b0401845146403a414224185010302400110428143d13038003401c960142d000744000ca980c1005e803000700a1008120481210410020341c21801c103044041c021003418015121401d0002c01d141c0c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575597068 1250 575595818 575595821
    0x3070507020a050603090a0b0f060130230601080c0306131e201603050c0f0a060b03300903100204030303200a09060e0f0a03080a080105030f1906 64
    0x140ca8014040340d17403410041c0f50300d136580c5400b040807298101c3e00b4002600320415465414800c0006844101d00011080d40d95a00060b80051445c03490a00c1501d011286c1e003544611102d800d04c49651113108a8400d460641c800d1000303004071b040210403010010329840300c005807a041030701550101028501e280e9a0805040c801000308101d02c005030002c2c00948090b0440000c2d0b02031041c060301c5455900d40b45424912505128129050300c1107000c0c0c000a1040c0024102d5000c80d0341599819107000d41e040c0d04103103201d001a03641030f40302c980451003858180180c1c480c2003410680c10400c03030b28100b02c6090110903846020b50070600484c0c82c41e180c0c2c6003440840003818049408558582e00c078034019000b40941c0001414104149082d560001601421580e022007152035000f0101d203402d200301c1c2c0d04c0d1160000785420074808101c240c50b9071200c603003441c05184100015516111290001050760310141d02442c80f07680305400100c0115000b15105000080d9030001151a4425050140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575598318 1250 575597068 575597089
    0x6050a03090218010e060a060f0f0c0213060e0c04120206030a0b0a030b0f060105270f0d03020c0f0316121a010321050301051008061302030c03070e0103110307050702 73
    0x2500b082403c450024400080340e01039050303441d0a14852000d80366142403060708480e900407440030800a4140e942003e018080f0201407114610380300c2550121030303010552506000135a02c0d00240c450109001c41c000356014580c2c88030402c01e0b020f00f070910b09143d0340900340d076004d0042d01807540000442c01004098014804d40d55006c0c1c011400b81c1e607a45888a080ea408854072826081241e0200d0085d6116904070361880307445400e00d8000b00c000ca001d10781043c0041400701d45c0030f03010702c051110a07215150702d40700250181d0090301107880752200303001c503120f046c4403124481d81007004189000e4060a4200c1e090302c503020641c6044001074034041d54000224080f081d48076484070000410041d540c3d4200d0b51000200071101741e5007000d6a000d58003070000b80600d681c4441503400380081ca52040030309940c8501d0041058202c1c0c0622007000c82280c2c42030300c10b0150141c0010810011a0300000c200c01480020320701000540801c8c031084205000140118042100000b85142590b8070b95a00b075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575599568 1250 575598318 575598323
    0x80a0b060a03150b03090d0807021f0b0103090611070303051321030605030115060215100b180a03110102060c0301080c01032309160b0909040803070203040305070b0306090a0e0706050a0309 83
    0x203699034100000b04d10f59076061f0010180005000000086100740b0105804401028011106c520310302041e0051020300180c0003441d0415590b489c00d10049211170050507014207800036001d6480701c0c0303414003c095071030050910045130500d41c24140018880c44d100001c0303694050920310703d0902240c1c101c002d05203c3d072000341d144d130a12074000e02d9580340c0c008401c201e8480f80c084840503844070040701480c40040302c000d4141010b0b140100b00c0c41080178020b1101070298041292540603080006003684501d400907210703a405040c219080d96010000c0c01d41050310b40da41141035601d0b000d40c00d5524100036003480e04164881101c51910b2584408107404250040000d52180c070700711507880d030354884806195900c1d0700d4480e400114260103c0c121030004001421503e5a070b80c840d2900101c41e84090803800441c402000700201184003405041c0c05401440a0241e1700d040c0705040040310007010300300d8400c1c186004083c1c001d2403000150341d021a03882c0e003800da48400700c0040a038000e040c5003102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575600818 1250 575599568 575599589
    0x6040c0903080f0301230a052808060106090509040b0a110403020301020703080a0b060408031602061905040801380619030e0d0f050d09020f0619080a0b060a0315 71
    0x180415001e1140295041e02d0007000b140100701400b900d07900c191b8614485007a008108210180900e00b40040b00e60307814410021503491241c4040025000203e47c2da21501d8560403500c0180015a0711061500040004442c1d003e581d040944820003140f0000d041c012043d550740c2e05251048100e42e00703407001150014000c41d1500a5404d018150413011529015000d14110002510745402402d99041d00c15400c02141000105009510340304a0200c003030341d1010045c00a03c0700034420b02002403c24985540f9261652720780544142980c0c8180b40341440c500c503100341d026010040000c00e0510600c10354100c0e50100b41840070a910b481160700340c451082049040894403030705a005416078070030710703821229030034140c1104031640d8110003182c1c00001c00420022031000810b4021144041c001481010b18201f2200041ca06502144505c080e01e29a80280010306801030100c550240e18020140900781094001848900c6011004024165140c0706180d070803003041d0980000c2c0a03d20325 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575602068 1250 575600818 575600827
    0x10f061a132c0105091308031b07050a1b12060b0d06020c0c0102060c281209030c0b060d11100e0d050715030219360812040b0306040c090308 62
    0x104005040c2054000b03031070942d030100008050803c001280e209201e80402420f440010350348191035075001400c205082c0106120707040c00b0440c83c4004052146c0300b14010a0000b9040c41c25002c1058080060f452072480801c04002101243d14040c109075072140c1f00042903202c5000244800380300d11009400c0307038400b292225803032a0000ea00c1041d1a801d8007210095502c0719807022aa204420f800c1c01044600e0b02c60b0010b6050b41065200080214100040c40981c07045030002140c280600550001d120303864540c080c0080458425001102502c61a0143c3d0007611451031140c1c09000a6004a03078000301c8110182c030401903024907280003807909503040f148cc108150f540d507650203034070500300140099900c164000c0c800c80c2c500c02403071105801c001d07840c1002550701c002003585029503100043e03441103c0400d070b00080200a1100c204000c0028145180c0521f4070010a04140074281e08200501c0700c60554815242c3c004412200450808400b1000f2075620103141d1005286100200703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575603318 1250 575602068 575602109
    0xa030e150411010e030c0607060e1f1508030703020a0b1f1d0c120103031b1b06030b030304060e040908070f0f020112060e06090a061503060305010f061a13 68
    0x8404001d0b040c1c0076070f61a010413404104060700c4140e94804250711003001c1000b071000500342c0e00700754015a569012b640c520000743c80e1182032218180350b031495056507009250f841c80b8140c01c4050242000d00b004600b041c01c3e540d4041d58481e2010300140c504030150b000203001000c4211150602c0301c03250084200203644103440b07240741c501d10342404060074000303000540716519101560422564520440010303440d60704d00b40e42d04101e13051000510500380c1c0902d804200095500c090031460005807981c005d00e010740041c2160091424544a0b400c2000104011548100054114401203500090701461407620440c82e1240c12001000d40c480a5203800034030989044402c0654002e03203992804d80120340b600030898180b800790700400b035440804245603090020300c0319440000c0c0c400014899441c1e16404000141902c42c090000e61280c070103000700802806a0005030140d0070b070900502e0309010410003500c0900b5144000a6400701e44040451490f2283c90001c00c80010b1810a100c0c051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575604568 1250 575603318 575603333
    0xf15060a02031e1c020f09090f0f06060a090b090d05120a0806030105270106051e0111190f0c1a280f030209031f060f0602010903050a030e1504 63
    0x1a1980e2900c120f0120b0441e07031020300001c55165015903036003031283d0f40025500340c0003500414101842407600340050740c3c0549480d0070781c40c0540311040540c46245440580000c1c0d600d0010840740c0142d200307000001041c2e41101c030040581c1d1009100e20703155100a0040b410070110001d02600621a0000c001d03032403142c15000f42841e410300e0b87c03124590f80e180d405160a031103041d14131110300120084501e80202d4101e201d502d91000c00c02c0003061640d91800040c03104890782e81b85078107040300155505410340e005034225104005080c040e25a4121511b000d140703107100c0c5030700a4005a103000c222002c02130105407810240503140b00003641c0800031007906407141c0180072134451702d90f5440303000300c0c0048002c2d00c0082c040515031b440ac5c4544004000c110007035084170a28030b405100b8940101400c4030354032a03051108094140c000740a03444c206c201001050a588103200f564034100802000c668010b044502001d65403c0200780ca040300750700345207400052130140d01c000356400b09010822241 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575605818 1250 575604568 575604577
    0x723070b061e0f150d050f010501020c03010504020d0b09120c01091e02090105040b04060b03010b03070f0f080412120f32060f0d0b040c0306150305060f15060a0203 72
    0x150380c080104280c1c04401080154690021603002500401c0d4141a1401c1c40c0c00c500074844013154a820a01a081450706541080c0c4158a003562078400600007540c1c1046a40003c0c50110003e103c3e5060035004115402000040603040982c40000203200c11420482450341d01d42c0320b00015580c548401b2810700905405004403280291544a0001d05c4004e1080304c485640090450419134600010440240403400c080e50300103458600c0003441c24041c80155000380358040181d0368900d010000180340341800541c0e60103010f0090300c903140059009034440d612035801190911400078450742647c1040301000b0030a825030820700d11020400c2c1e02c0d0000c4200f000c1d4912010001804007291a0441101d65101000c8401e4000081c3c01c600c1c003600c2d0201000409080c42c0c4030002c2903201c074405100111420b58552503401d03001c104104003442004c1401000030b8964403060300356a030b6503899100c042c04a03a0041e8a12000c03a018400c0b01c1288025241e008003c50795658144001035101d400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575607068 1250 575605818 575605831
    0x103061a270601050c0c0d1119090b030a050703060915050c0d050f010602330103030521010b030406020a140a0306060e09070507080309070f032003010c02060723070b 73
    0x81e030808a0b009501032425250200d42680281051441c1c02c824481c91022012003540e031400001d02908503a03c501401d26150340641e88a41d02041c180340008013602c44880c2824003d51000b1502800f00700003042000c04e603988130704040380c0550207040042034500c0e502d40c001030041c80e00082c009040c80c0d010042c000300d21100d4007400309a9420310440000c081c00d21440b40035130400c41145404c110000c189040010801ca03503040c401d444440d5011402000360000c90100320000703074010754225940a0a40c0c04180390300c004041c0c1d81801c602034001c0c08082d000500c45034011801c1c0b0481c138010108400c80c4403030810215150011200f0003400f03840716118140c041801405090b105081944001384149040d881d01032074010965212422030b440103280007075a01031110003091803500102010002c5000e0b003502d0b0080c0c00407032980104c107614001000e00c41e078940006501016000314580e039021261782807442c4031802c000c0c0c0030200e80f60900c0b01480c401e240090048104500000c1580c002d25 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575608318 1250 575607068 575607139
    0x21801020f06090d180806070e150307050912030d0e030a030b01030b150714070b120a15090507050d050f070320040b0d0603051b15040b030103061a 65
    0xc80c4403815207400003600d0005158004844140030139004900002144000410050103c0c5e5120702e094202401522800001040c500c60700c00281f404a21402c81813210014491842c02c0000014040c1c4c0300341c0d41018001d4014030181900c0b4881401515584000f00c081404007820507141562030350b01c641c1551020030303d8806280348a5229200e0510100d00103048165049100b8000405640003007034126850051b1440e480c084240900c07c0030010143c0c0c2e1843e686411415412002106004211821062901d400b00d403001400104200071581003000010321611001001c80c0c0611500000081850610040c894401125980244a01142e40e000c201c418454440788520452500c0d001207140014401030200d02002e000416042549403400500b6544d20303a505130034019000142201000ca8480110b40c0e81095280900055a049595440d050030f00695118500040c00042d20055035800f4040d080c400303052b4040c060100c010000b00081d00e41141c0e420300c1f100100ca1113692003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575609568 1250 575608318 575608333
    0x3150513061e08030702040b0a15020607141812070b13052103030c090d020d08120f3108130f060c030503150d020433050d0f031202180102 61
    0x10b001c05880641910a80d6018515180b030315020000941503031040154481e035896800155105840300e070320207101c010b4000d01454982007802800000111091913103940c01044180d5088440c1140860020000c55480d09281c148480781845c011498010140c00d205c0065001111050345c840d80085400480ea48443c213515190240d41400d9150302d540c3c0c16900a0000c00c442d130002001400c4c20b4030300503010038000c5c03910707070000303107036041d5007403090320000c6000403500004204a00c2c0e09038400300c4449070542c02d0030700d5400f280c074980e200d03a141c0d090299000740e00d0b146070001c0c020b4905020b070003000c00c64603581c1d5550583c6215113071b44550b200390303c421200003440034002d40407846c030307a40c264403140e042d0b41d922050180c6030180000440e601c00c0c0002003450042c0d6692154480c00080342c007030b50300f02c10002c41c1011862141e64a0b00640104d08030340802140d911940c42c80083c030f0307009041c2d21881416241c250707403052044c20308403030450001c21120410034980c290203000010990032950356 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575610818 1250 575609568 575609609
    0x1021213150f020c07050a3c03351914030a0e0d020105040c0b0304060b120123040b0a0b0102100606020a0b0c1204020616050a050705090f10060315051306 68
    0x4106840b58280d40d041140007059500d107038182040c58a004032290074080c4d0000d01d084540c000150704202c80b1480d82c0a0741a04c2a02c00c0321103240d82b805182d400304811490b00394443c0b100e000b0311201604500c680c3c045d8030000d41c80b888070101e807445002201500c9060a14040c0c0c048d0924415650181c80341c400200c410510500400d401241c0041100424a003000ba4181683d07000410035111a621070890b044251280c2030701e001403091900001801c0120380164201c003441d81312500003000121404d00c404108000d407002c8d0059104007001402e00018001070703041c00b4285903218201d81c505000083d1b10317030300424402031680c030075002c000e41591000038103e220700642203036140e8050450000703401400c10400801e403509282c400f24010158a90b6482e24013100940e0481d002c3e0040d802c01c004c54204001c00d0360b0840c1001220103c03510786509074410710740035403151504143e11031001814600d000418a006440042c101444010110351014050481c0d072140f028000d002c4014440c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575612068 1250 575610818 575610829
    0x301150b0d02071410060512150604050a18030809060c03070e0f0102100e0c040c050a05031609050907050c0609030f04090902060c0a0b011701021213150f020c0705 72
    0x3a165581005424859060a1500250043c1c0c8049652000041c1c9005203464100545982400d5024022031107908113024009070840501e000c05155001000504110307040d1650036034496815540024651303104038201d0301400300000910000c0d000d012403501030640c0101003d01c00c0a10401300d905903143c040300d13068644006c680303e00018401c00112445482c080c12002e801d00014412104084030b071686d80000c695003240c502410307030300411810882c1d0405008421461a05081043c20a200c02074080c089200061602ca20000410264102580113018000c0580380142c000c120a02d0441c074042c0c441d0303001040d40305552003460001a0717007000000842d0b60310402c10302800c1c2080e14200441c40601401c03070040340d00030024006a030320307520100001500309015880889980d450312034108400c40d41810700c403806900401045601088526400c0d41010340380302405240d00c03182c00e1040c4400c1c040d0183e9121035080000d6401e00308019000340c0041c0021200b5504441e940700100306 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575613318 1250 575612068 575612111
    0x60a0f0806090c070221010608010c02010e070e1914040b040b280b24220f12020d0606062102180d02010c0602040306050f160228020a03110301 63
    0x490103041000f03c04c00509107113a41648411030b07054206011281c0703c11403420340e202c1380c001c4a4907a640d5803030400305590901500600a01f4000134242c0c1504040488001510003171a064071400c000345840140185a800805003000c6c00e000c0514034142450300440300b400c00c0e07030b0560344001017502050782d0380c10f22040c40a41510003101818146000244038000c0d090f05020503a01c610b030b0340384c10300088d0b040040a4031070005070021155a1241c00d0004d0341d0080c03400c200c8050741644882c0501caa410558040e80c107850b0344006000040c5801c2c800035103103504404004001608001e00012a41e400c0031103080c1405010031405041380c00c403c0048120b0160094030075480f4031450300d0a00500300307640400700150040c5400010b0070301c5e50711800244da005038411241c1d10343d1502044110105075940c1038020703030b01050700503180000c884000e580f600c454080f5004d140d000000c4410b1b0080d580c016415859000d00000716460b560704050a040b60b880710324074003950821000d2400c0c0c0b6407181011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575614568 1250 575613318 575613331
    0x60d050c0d11090d031b020603041208010b16060b0a032f030a0302060a0b030312040309062003070b06010513180b01050a020d080c1b06040201030e0c060406080c09060a0f080609 78
    0x1c2ca40c01e04c954074110382d0704100030001c0c8000e10320080d024003d80c486c00011441b540c011a10410510900b08009149200503800302503055024030185c5d44503c1c00704401d00031a81c000b400400c001c0350705000104c60350405e510007041c014148075007001c01640940c0100609001c0d00d1000c0d4021403401c00d158039550b0a4000400503008800000d20802d1103503c000d0030741d8406400c4a05200d440c0300e143d461840c040c0da00b540481c1c40240d0030450650302103404141001d001c0200310000711454040d640d41c0c000e2000051091408400003801a482642910303032040801d111520580d80d81d0070454036025410f8140c1d01d402e81081c4000049500500448044580c03d40c0107012100d1026411244c05501520240d840c0700204915964020200b400803807040524001d07120303a0402e480054100d4440404412aa400150b40710042c1e40c0c0d41c509940840d03900f81042500c035a5000daa0b094a8070075408070340d1b030040c07000c40c2407085103901066641e25044192a50300180d21100304228201c00106c503071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575615818 1250 575614568 575614579
    0x1020f0118081602030a0302060901110906030a183507020a260d08070e09070f1805130c14030402130f2c01060608010e0601030902060d050c0d1109 65
    0x40c00014462600510007a040f40054008801e0544d0010f0308140c900c1400780c0059200704207010b1014428410604d01d424048407943c94240c8030b002050711030000403c2d070607416544140d01d2900000c0301c0307020b0081650048408000e000e140c140709800041c407007070302c0c4015858041441e2070013101100b00d03960301d500180358600c03d07440e022002c0300030198428980c112507144d1000f40c00000d01001001c00c22071682c0c03103014681c984507000828102c4181c0115118480010a00206940018250028001920742490f01117183c1600c0d008600c4a41c0c050b80d0040320148000311101072a6000e4001e50400c0c3d594a421440003002c100c980e80816107010f9884080502200103056007a40300003a680104d10012691500700d04150220807441110011003807920060380c0800c03203007031180350003904013410810703410750504075481500b10000300228181a80c1c0c403c15002d43d5a200c00707441c610796036404103000d54030300f52044904981101203a0550642030909000100380502d06840e9401c8001c0c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575617068 1250 575615818 575615861
    0x170309060d05040c0b0c28030c0204050603031201080304050f1012150306020d0b030f0102211b0a05040f090902030a0f080c010612020a0e0702061f0e0702010b01020f01 74
    0x40c00300400010f04100c42146005000160121250b4041c040c004001b201400302801c2c407501c400741146142503480018203883c2120000250403005078a901901500d0004d250380d9541d020030f01c0d501c42e081d0300f603052401c000000502c4001c000014400d40c1da042c2d4a042250222109000e0b10000c442c225001203848000d0901824102e03a0101c21a1000318140d410361079030701d0326024220791014a1002000e5210052403281d81010401d84a10030b007544021807a01d0080d04035405610203545002440b215140c011661440219110700c807114291501190303145405034001d01154054494902a070312603650025000b0410701c164403072150068040e05c3d1217689a510641e5010745040b044454150501c0b5000f032800003482444098490348140d040d404260340100003c0c0e0390203a2005501e40003407420040c40c903a001c501d2513003007a01d0030640381065400506022500c8000c0d00215000d060010800103132590541000000318000c0c0c00f41c4034040c41d0002c400742a9000c00541c0380a442c010203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575618318 1250 575617068 575617087
    0x50312030411011e050309070e01050d0204091104050702070e0108011b08090106030b071d03010504080a0f050c01091a09062404020c0d0804050601080a0b0c0306030a14060117030906 80
    0x1599902c1c580c00c14500f00c0c0041c0b0305040307800703041d0f0f0700c624019000070804410800103090400c882c2c070103400007044c514099032420f03000501c14441100020b0207541c4400c034031802c002a103180b040000f80c2c010818041d51070310001c002e42e01c030000e11441c240d0741e40940000420b000306214542807424012070100c001c4c0850b003c240d034a82400751500105643c2e500000000c0780e81d40b00314501600d1140d4840350070401281181e5411000c0d000b03024030913450101444006581c600440348114201c1c01e0104111809d0b48041d2128000c024409030355500340960041003022065001c0300070071041c000802c0c1610741445542c3d031070030304a400352804030f1100b01d00100310010b000380c0191407000074400741c035024451714000e050007916505080400c03110f0051004203c030a106840c0500000c400904401d100342e00c40400050000e4000003601c00c00001140c0640c4007130040580280c0c200d001401c03840d0746c8495156591800344a4071841c03841408820710b601300048210740071514014501401c110044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575619568 1250 575618318 575618333
    0x21f0804020906010e1201020a090b090307140a080d020a02040f02030f0c0f0c0f1e0307030203040603091e030f08070c020f040f1d0c01140a200f1905070503120304 72
    0x50f240505200140151100f5030b900c9044003241c507a241e04c00980c03507a128102c0940050840e40000d0400d00f014403800700141c41c00a2444111a411a0100001410341e00410156862600441c070580900f08400342e80741c1d0002412800700c4d100b5903040141300b029042d80000c07400196020a0720000c01004942c0f60440840a44410b00061151500d0607506030385003072410303800e001100d0264126410004101d40e0071000c10201e440604061842e00324641d0300203459120701d004034014155904918070520801954040c00e0100c28280c0761052241410007400c019400c0c40d0030000100064000340c1003a06c00c20300540c2440c2d0241086842039080c204000151118005c60000c240e502c150100b106442182e0421a800504000d0806a024000018a50484c8080b8160591001c00201d4640d40d8024035003888900e4241c118110007017800065030034144119810803080c4200915601c841c9040380455140d2481081161113056541c0c0501d9200c400b0300840204400b0280001808695030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575620818 1250 575619568 575619571
    0xc190806010327050708010c050409110409020706020d06090e12031f0e04060c1404030f0c0306051504050618190e060a05091b030309010c08090a080a021f08040209 72
    0x1418041110b80b2015640d292a0303580f48001d07084000300c0710061013400001d01c5444040c101c090000d20000d102c1039800390042c4103030310840319920303905d2081d052441c03012400da8018055216082d55120b00d1828141c01035003245502180031840e221303002503100440d11480303050203034100103800b229102d04076800498000402240d6513403240d40d103035011309a10f081800b02500b800d0309040310a08107811305c1c408a9103901d400d4014401c40301440000180004c055078103c4e40d004515025082151510851014542d84020840740c18501840100610385407801c0c8170050030345040041ea07a482003001083d00311000c0800035200c001e00454110020791090082c0e11040e0500400c0344100404180d1030494112400d40c0c44c281e4941c10b108402c0001d01120318402c403d1495504c055201000181c0c5910580155a05000b1180346280801000710161080c100d40100480e0103d0341e83d102e07454581d48550b41c00c0703125051209098142c984c0440300301c440356440b030341c0c0c4088903915542480700342c400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575622068 1250 575620818 575620831
    0x181d070e06061305120120120f070c1a09010b03010b0604060e030a14100b01170109050901062c070203070f0206092b0c1a0f0d180303020a080c1908 65
    0x50f00400800d1944900901c0c040d900c0c4581c2c0006108003850f0840303440301c940600d030341031001d2003044100d4403103503080003068010a05462a05241d10780010a403822264148010688004108800e038445c0500c1d003154030400200c4020700101d40e180041500300c810010724654441c3d02844184403c43c030880b010340800c0ea018080360545015616071301850b80104414102c03c1d4001c2030b12110f8109540a000c541981c20708044c10380691924400164400501403c04040d07600c0000442031202500f00304010618040d07030030308400300402c00840d041c1c4811422080f5074a80c4021070001840082120306c010303000000c001e07044460742d08011340b0390b004051156000c003689541d00c40740b281c0c0d110021140e43e00c0c402d81400c40210b9103400e05600031240d103c0d49940070307862946800c10b07104c6001c41d01844003504046540e03600c0840458018540720518241a503241c43c450010550140d00034540e84003140c95041c2150b88200d181c198030700c501080b0030040b0100000085600b8080e0103405d80094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575623318 1250 575622068 575622097
    0xc080c030711151005040504030c0b04020a1e1508010b16050a060c050702120d05070609140d09060e0409150c140f09090603031602011404181d070e0606 67
    0x400042d038146800440304045418518420a20040301207042100b00146020f1704e0601c02d92400f43c5001d40381300d22025000d03140e00d4900f00002c0456031034109030405010a00c013a46181101d50034213860300010350150245495001c8500481e0380e000b421114129800c115026161000c4104080701c10300a0290840c1c0611800000340e00003081030040701e0580e882503942c076442c1d1803680100040b00600c84c1c590340603500100450340310640e000b01181c4150f070b004034000c145e94145250108a1610391a0f40c0d00d114000d4041862845600642100480d90590b90b8490800703050b004000807100008002001a0f0303000903512441003036a04031100034121410070741d072070044101c104101e0b0f42c40308044d0006100000ba00021500e0024441e82d0011803d4008504050b00030298580460f001c1c10060b040c0315003481d85414501607201101c019000d02d40c0e013602d604001404080c06402d00c8000050342441c00c9000308403040c2e000034400103e0f46840c0320104d040e08c4540c01d202440e13120503680c5c0c1005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575624568 1250 575623318 575623337
    0xd020a03020d0503210a1b0210020c03071208090709060e0a0c12060305280c03170408010f062102090406020f040f030b0601032307080c16140d030c080c0307 69
    0x3050201c1c043d030000070806a0704001c1c54110900b078111807d0000392000b00e8148112901e08035030000f85044032005075a40180e0310f40c0700002844ca1401428002080034032107006c0c0316032003944800c105000d1849201100c0d180e545401103107060f140a809444040c0381040300048100c45244c01600b82c40855040042d002030102d1181d070143d0b03005400a84103607000e071420b5072000c0c116090042c4101142d601781c441480340d66a44601e1500107201c06403035140c06003e0200008010307000c076030082176000000c1004d41c2c090040b01004d0140c0d4800c40c03103c107041207414036105410b200d14200140d4014600354040c0e65550b141002034110258104444200348030105201c050300c41e010f00918011100c2074010f10701a4001000d41380d1828145030900700107190b07459500524207516030050118140341c0d901d60340c3d0300201d442a0250101c0caa00038100d030580801401720303450242c850602c4071400c0d00e6541540d66019016220b90349040000108490005020300f40103c000c1c581102c168500100700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575625818 1250 575624568 575624587
    0x71d061215090a060503070312090506040905010905100b03131e0c170c0310180609060b0f0415090905070b070b070801051903060b01111204090b0d020a03020d0503 72
    0x9480c1100c1c1080e4036403822560070300510b402c054095010700b40c1c0c03100b07010240c01e15000c13948990091000a00180988000b5500e0702d004420340c1c000750001904140c0c0380e96aa504110141c0300a11440003818600030205400340520001c20040ea0f02403c030301455500c03410048024000300f4402070303a0b0441d410011444981203043c040341068040c02d0526034003800e202085080c000749030b08081040d4040283c1c91126203000c618140000714a0b1000039074802d140b130042c440003840000003031030146807180300030800185501c05c506050041e111102c043c44810284400c40b118150200c91404103001e0802002000f904090a0036204006851505a4510500403a900240b50844809010004102c503540d07000f02a940100341c201d807091049115034902d0f040b2181c082c0000f905290716181005c806900440344421100c8a40046800e40b094081180410740c00c140104c404c00744c10241003140600c0c01a5421145980042ca051720700791640d030070051911501403040715103002c1881952070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575627068 1250 575625818 575625847
    0xc0b03280c020c0a0620010e0303072109020a090b060708031e0c04050a03120c050a0b07030b0901050604050409170d05061807080c2d0405011106071d06 67
    0x400803000c80340454861031059000e400c00f40d840040303c1c0688034243d0108201035204000c840051071b800207072007941030050162405090f820208420610002040c00b24417648400c0c400d00c00804610b20101341075001400d5003c0e15081e59000e540000d20880a0000002951141c0075076040104041e1600c0c149599024554004584801a18201d5809400142645800b0075801030034a4251450303e0b0401d400901c11101a01020388510403074a000c50010340a240001c6910341c10030119440300e90740789803480d46074000300e8071000001c2c10100b0864080c2482840603043e2680144942d0409007030809010082c908020143c030080044002a03580c0c04500e00140390780480081e0114141c5045d00a2100c02030380445020303c441132103001c000086600241c21a0411015614103540303040c0015100d02d03405032408043d00540380d560070340d11004110070040c0202c81080c0c03034001c0041c000700c0c64a502d6400403111440480c01c165180c5c06022040300011001a000400b010704001402c410000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575628318 1250 575627068 575627131
    0xa1a1207030b0c03040b070504060516170304050604030212070f080a0203091e2418060417160902040e041b0909140c0604080c0d05100c020307030905030a0c0b03 71
    0x1c900303d40001071000380080060350551208050801c1d62805181540c014440d20426503119911070700440c3c0e0004108581d81c410070840c0c54045165124200f5080c51f0391550415038044016100d40911400f9900b01d0005440303420741c000030004042e20460301e628031282c0c0f05ca80c0501c1180010009441c107565071158503221409051a9800201590b8003403040152904114000c0340301041244860030307d8203412642c24a03c6803900e44050f010700030200742c8500031500700c01651580b855060102036000142c40c0e001514590401c6440d0b903542c9855404c8dc4124021510340c0c180050008004c55204006144c0c0182c0115400a58580e00c0408900719803e0001c00c03500c20702d0f4640b804070048800c02030304c0307641001110703124603040c070f400c0050380d440325403600003402516500c060205110050005000035030350742100740300c000341c090760080d141c0e803003940d048010882400011925080000e04e002030264081d04a0201d1418a1114281500b00030881c2540148949211540303552010b9100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575629568 1250 575628318 575628331
    0x200a090b03120d0615020a14030301180c02070302030111121501021e0f03130311090c0d18020306040f260306090604090512040527041205070f12080a1a1207030b 71
    0x40c029888180307002250309018820002d0700f503002b40014000b214041d500301c0d0480c0310417800000d200030620f0f4264103000d07155201039410751814044040e00e140071001814410369501e4200182d9503580c8151603120401c07a51a40103a00102c00710640440002e0021000d03e008003c507014401c070008400d00d141d00044602c0d00ca02030080302082000280e035082c8041c02d1007191040d849182070720311912140074994155100c140c0b200900d080340501040071032903582c0c024041c0d030071903d442d00b4440c01140044008840c0200703440407403104060401018901d488076290000d143d03450351010031100880107800700354819980c0400c0320004008000c140c13140307070801e0490380d1510728000400c500b4503003950011072000d100b40e04130782050b20b080030030380c1d401035000302c9140c0c0b440310408049480d03001e990070051400d8103081c14502070061803c82d0001482c107075941c905050f541ea045400c00c1c3c40f584c041d6170f02d0010801c82e0000c83e030f00d808202280d1105021003150300301c81ea26110038088100a031642c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575630818 1250 575629568 575629573
    0x90f0c0f06120c0f0f05070c091413050703061d15060306010b070203030313230f24040b07031e0e0c0103021201030b13200a090b03120d061502 63
    0x108511a044040200b1040c1d24103410000302107406400381050304d03004004010000c07000c44c40c06106016000759101c03690010b09244140303840c0c159040042540b000c5010301400c0c0b03040000e0082c040e0090040a050f44580942041c610303583d581300240030340d8403840c1410200b0341c249425003101085108001d0403003130f0400c80c1c90704281007458100786041e0000c8114240030045680503031400070032030b900705212905020030a807090401020814400c403000c1c0152030902084065144c0000c3d50581100310f0005440d5240c1e940c0c40300c0001842d401c0d00500100b54441d0005001c910081c00d402c0d4800191309021944c9840201640f800c1c03009010b0751350100d681c8003802081190104000c04100341d00b0300741180307064240030120300903c505110052120b03690300000b4544400090188100603442084102e0080e200c418081000c842c074440d45025000c08140010455141c1c000e444041034041d001d0403070814000c49a40c116440098018452602c0d07840c000340d0038101d548005a11420f9030702 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575632068 1250 575630818 575630849
    0x1902071a0403020d0e10141c06030b01060f08040c0e0a0b120d080907031113020d050c041e030b010611071505030f09031312210302090f061c090f0c 65
    0x501030900c11740410300501441e010b00041804580000143e555420141000d50310744c00040400c809803017505000c0c032a590305089000081002c42202103043e14065103c00e1010045104100d401b03040446015201c00310401c01001310f10012103015400070103400010800f2001640440d40001c0000f035101c0c00c0303a000340b42103070700030303a0011110b600712803034501501c60740c1d282d030710f451440e007401905c05840390454001c4100035000503030403140e0031039521400f80024544580401e5007174101d485800300ca20140c403155140c0c040a00e25400a603035200c00c024980c0d0f42000c80480c0d00340982d0b5248a55445501d1005c1004010000d0307071003881c1626920159039242c20f01074000e21040c0940103002c264000d2054601070203030901c0c17140c240d81104d0100030b60f20f401030400421280403101034000700d00e0500d00741100c0580c990014000341100703840545c1450040024002584110050079500c0510b031281112021296082074201074041d03000c005c0d8250b03d54481e807210040340da1182c031801c1520720 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575633318 1250 575632068 575632093
    0x703180803180307211e0905010905060933030406050402101119150203070210060503030f04053d0f091202100201060b04030602090a0b031902071a040302 68
    0x5903180e856064030080c60400c0104c0c0e80703050010503980010040005c0400000300d40700d1060305804989804140820440010048050300100150040d10b000546035400421641000c50481c1c8030703034070b0207400c002c803040500607580000b1501c003806a8028442d212000e178030362032140c082d6000710701900d0001040d0909104000e80380700480410f2080c018074108100081074040382d02c042e115004810803403042d0762403615211204c60000050001c901c04024031603496070020f01298142a119000c1142c0c0d42c841c0300301581c902880d10906102103080000380000e042c94603851601c11615071030340003c1e020501d00410f040310f4030100a294202d2800e00d003c42d2a0340052b4005c8608201c2c20000750690411824180000441a000c1d0094100482da50a614806d40c8a9001018001c01c0c1d00d854075220f103480b0001c2c3d07110f140c07006e1069030f00300404110003002e841100d00803611049034554803c0c084518501039001a0401c1c1c9011101560034010004030b9400244600c0c406c1e80641610b01518 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575634568 1250 575633318 575633341
    0xf0e10030605100305062416050c0909070b0a0e1504081b09060d0b10171015150c03140a050c0d0804050c01121b0f080702030c0c090703180803 63
    0x100602404c041c2848140a200d13280c40c42c0300320b109078000c03940b065040710084042c000c61091800f812100c1c0c42443d0039a00b4041c01041c20803d0f144101c0360311410340c844079481c80c3d80f503038140191407461400304909520940212415400740034090025086803c00311480d440c036803c558810750050b0400e54800d00c003100307220190414408110340380d4041e4100f0502089120030700c6c400003480e9090000101d0108281402007100510141140c188078040034240c4a40b102440302c00e003805507007480071504484a4a40940040e2800c1000d140c0c0960500c560841d9001019031060b000d0041800c00b01003002c42e80c4004062201c6079843c0c81d5640c2440d009050702c0d103102c29004104000802c82480300103074000c40e1110a07010b09280040c1d140d64042140d90041c6406000c0005090903a880944482d411180442d00c1600c5600e0360b128603501c20000b039032284a05108214a03030031503050100c65140829001d904071940d40f41c0014072610002404620460441c8103a42002c0003000700151403000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575635818 1250 575634568 575634589
    0xa1401020f0d020601030803060402120106030c0314060306070507020105070c0f15020c031b03150f100f030f170d090302011e1505060705010e030a050d060608070f0f0e10030605 78
    0x309001071800b951450002521090180001401003c000021030103982d51601500c2040e00500d031301c6a41960354000160091600f4100302d80428285405803042c00d401c42d110360310580c0003070302801c1265540030003100d80398130540c01241030290030b202000100705a04c2491014110007982039804904000c03081a2407260181e80070119449070084082c2c0d42c9010510044000806800802c80c94034140000c1c10522003a08241c012454a01002100c1080c40300c91070050308011041c048190b16001500e80c10900707808080d0105000d600364031b0001c0d40a800c00d9424012150071142082e40d0388410743d080d15100c1d8415070050791158500501c001d054061681198001c0c5030421420740d81d400e0611407002148640c40c824200480c82d1824000290801110802c181080c0c0b43d8840e8840340107000e41d00000d00080000346001030100d1081c2c052400d40303014074240e44074090304002c504411140502000603000c10041c040a030070280e925a03038030600e1201c0041d1404a2400e0400080c060203420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575637068 1250 575635818 575635843
    0x1110032c0c060c0c040c110109030801031a0105030712080d060308030a050c2a0a0204090812060103020414060a0c1b140418030c03020a0f06051e2203020c0a140102 72
    0x708000081440f0001d41d802200e0019100420841c0040900f40c2d405141d54079aa4019400c200c45d080c2010381c0440343c11306032881401030080c0d41907150344031502c0e8002406016019400507005103e240c400c85081d110680c4a04401858891901440c5040d1100c60707204641540f40403040c0003518186020351644401ca40c0240390030f10200c028010001a2060882030b2140841c0744000c040713a4081c40340c2c1400a0300540306028240d100d2801030b206501202382d500108007840c01160f80d6604c80d0007210221020000c6a22036400170804110280d4030610f100000e0041e00d101010011340340c01040d10480c1d542200d421040c6107088110510904100303c1c0a104900e0080102600d400c0c0c013400c06c0001e501458904842211071034160b14110441402400d1420f0100c014420042c85410152190740d416008003a404405010848688425909494690030688154a4806c0c411030b245e4070391030003481243c20300303e40180071880c040038541116000704030801620700c055804009845100d10b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575638318 1250 575637068 575637079
    0x30f0105090d18030c08071508040321090609140f010e030f0f0c070902130e27030405130f1b02030f0a0c050d110106121110032c0c 58
    0x640351609035166555030801d0002e003c0d80304041c102c1d00e40314200c0300024540c0500c4040415840d4503069a50388814843c07440b02c030441c991240040c0313128001e21402991301d13440748040020703101403000c10000a0b400340c0c00c0d1559152140760108e202400360740d000d039024001181d40b03400030620315428603d81c0000d5040c680e040041d00140844008102c0720107482c01030b100307901c0b808003840030589449040c3d41a44184682c20000c100d0341600e900400319034401e041c031038640e69918074586460643c110346404403200819075425500c0b2480040c0740d6103035682400e03207241c162141c0c00070b0400d801204181011990790f01002c0d00f1440e070752003200c8840c035285420445200195074029560300c1a10608100c0d07200c0070514403a09802641201c0100d035005050351008180c0c180b0040c0f650381c1d402403c10f0150300740400014011318400b002030032039811600b000b80e940342c0d070b40c24045408d0700c2000010806507102c1109006480c10f91f80ca584001c48140100b03100340c906141c0d18501411140b100d031041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575639568 1250 575638318 575638321
    0xe0a0b100f0e040f02060909041b1403030d27060b030d02060609070302090a050a1508072f030d05041b06021f09020315010f0501090f0e010e0a09150902030f0105 71
    0x90b40340c003084680c0680e103d1001c815400180c408516140545001260803074008018002000010b0194283d03600c0c4003116050300325500c141820b02408040c01a41e01130708100010307403690b181a0070100d07500b000003154121045012001420300b125200041d9141c590760003540850745024400a48007642c03910040406003050000240d28074005055a4245680081c0328a915156003031120001c00000f42813410f9507a40d40e504142114115071101d00140c1464000f03070885028040c08088040c0028901c40d02c0b803140500f154964040c40b6442c6c103148000e22621072036120f54003e42d442144141c0c0400100c01102c2c001c0080300c0300030b4004500b07540000d07008180310610b0403101e905008204c4d00200c1c0d07280490000c00c0c10032401400405190001030f0020031041141c1104004031117003a6a81021144d540d400d10708030709158011200300c8540719004103c16081055416000101c800000990180590310120803101920905100b00d803111000c0007503107418018003000440759002031190707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 575640818 1250 575639568 575639579
    0x210022a0102100933020a0c0506060109140d031b0309150201050601080a1109040516020c030a0f0809030709060e010e0606091f03020d14180f07050d0201030e0a0b100f 74
    0xc070070b60303e071052204048841d01e82402d44441d0b0384a18003c9910104640d2141d00840040401c141c2304001d031418840c0402180442d441400604105c0744040705402e042c00410b401c01c20f11490303c00096040100c007030f1f2240252513403005d110181034420385601d441b4514192600007075100c684643d000790b91420003005101c0e604413500d190301202084000580c621045642c141d14020181c00b00d42042c0b4203c20803810780002501c1c1512080c207a0201c0310071200c040308044d6500d1205030028011202d07440c91304002844071003c0d100c400802025100401e031140f20b5901220107980c03118a006104000400a4442019400b900420217039400c510b00b86450010400078a1a1819a560310700d140d0300c003c004038882d5060f035060309440602844250382100d88040500b40955a840360824074596255502c1c400085008030310708408050a0003a24000400864500c1070100740d0600d40c81e800c002c030100340c09203c8a50103611540e10300100f4144020700c0000040140c114942c1c83c0b1829009011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 575642068 1250 575640818 575640833
    0xf140c0903070f0e060103020703030906020706060906090606050f0c0c27100605180f131407030b01020a1101021c03020a020610060203070204020d020412050a05150f040210022a01021009 82
    0x178080f80c00c4c00d02503aa8203c1d031808074001c1c014210040c161a00c0891548100003d54010604440030b00c40b003800300d40e440b281c40c10101e400900c1018003061042041c0c4540084c808090707d919800e40d020b5550911020b000710b01d41d2000c842e80101c45200403801c14601c4111540c2c0a074004d5010750a40d00d41900f40389000d02688144604135500c8007881c01c10708035607621101021981e0f6406068542100005440000a442a508040e8049200d000081d05c0b0a2203449114a8050140c0c014040c0318403944515401e40b8614103550304500882c1402400c0c08418881c50b94100c607560780040c0d582846041c001e04000d00030f41106908086c00c2000c02100b5800800d4410f600d40403200142d461500303141c0c0f0320082c89968440081c045a40760040c041c4078000c02d201e04013600410550b801402000341d40b80401c0021a07100840ba480b023400300e000341c105280395110a016030300403250340500281280c00c4d10891000703111040300c40d44002c8402564140031803600c00220140c203000e924044d0355444c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 575643318 1250 575642068 575642071
    0x10e0a0503011e0c1706130621020103051311220908120601080106050a0e0f0a0f0303090b0c0a060507110106140a050102061506130e010b0304031709100f140c0903070f0e 75
    0xe20450b01e07080f1100d807e0351076511400040001811401248030f0140120310b96280401090b4042840d01e00042c0b43e22404280c40c04040fa4007001d0160744e807910030100807440603800360b44a10440304444111603400385124150f04180101c514946607036010f400d0007071401c0700916860420216400400446400006031807149a9a040c8800d40041c00404280301080c0f011001c0c0e4072001541000844c0040c0c43c3e410400e681c02541c540380c8050b240c040b4691117118507a0700c1c05403035119a0405000c603415511031900007401c0d1808a07030840103003030741c942500c24680004000b2090990412810702e4000050801828280080c0100340341c12079148071202d202008590040100003801180d001100c61081d000e410007070b0001d202035848101e501c4a640044071b0880100e18100201c3c80519104640503205030f000e00020a075010f00c00710120050844122040c914a0f281c03800c031180d0000c1030703a0a520441a9891326500c81d96030004051411809900242641e03040e003105000d403100354034260f0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 575644568 1250 575643318 575643331
    0x30305340803070201231626060103060e180105060d210c02180106020705040b03060712020f040305060f0f07081315020c0313060503090705010e0a0503011e0c17 71
    0x9a103954402c0f0041c1d0140a20f0b02d16840b0b24000e00c089802c0ba50510310707446002e010418504d04801c0700803002921410f803440700e0486a94001c1040b40d03041510b01c3c4049a00140601d40070502c0da80e00c483d1422000c10a031042c402c60240350301040040c46003407140d554400001c4400071081c0217641c5421400384c02c45289003c000c40d0b0750990300700060292689003001c65000e8026072001504c8525400f214000b0f00401c0d006001d013403000512403806000c0c002c000742c0300074050940b5454003031095500c0a4800c80300001e1940034050100d4206503440540700860160f40980642c0c500101038100d09440149010b010030b04007014000c4459100101a6000e01e250424085019141c20103418444921131080c0c4010b000092020340b480b00840a045a0b03005000902000354a6040680381c50008a42d04600c940c8280c0082100790320490080020702c00c0079004038071050320350000c6403d40f41e091910f80e861400600d1300c0c3c0480c1c6114400c045c0258514074141040c000860840002000041c080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 575645818 1250 575644568 575644583
    0x2030307091a090616060e06040305220f06020d170f040b0403021f1a030601081902130c08190b01050307030518161d010b030109090807080403030534 66
    0x1036542500082c0441e8450400246115101d4039040c140c155501400e03142241c0d80b908003c40311005203800030742c4500940d41901c855007841503e603c0c8020b1003840c83d03042c2112001c40c841c00143c01400d141c480c00640140da0141080c0c00c016500030308400d0b01c01d1250008411035200304100884045507a0760020391140e0290030030340301c03410101c1c13070021140740324560b01c2010768001d00c59080c154401c5202058031200c2e1003010420300c041544a0000b48185c400c2c0e0b42114100c4806c0c50300016100004510040103250b03014900c0720207104681c0e1208005010602441c1440340300f0314520400c12041024001c140315821245000903c1800080e102005164a640c0425016030401c08202000844501250305020303107060f2202ea40e07040e0f8407031805900100003506c090100d121010034143ca00070100c00e40355910b000070100003000780880544007203e0500c210030004950f81c5c000c20082d800ba85e030b82601c44220f110948000c804003a04040c51b90b1807210b64100c2c0c0c1100400c0998050b411456 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 575647068 1250 575645818 575645849
    0xa030b1f03111c080c011406030a03080f19020c0c24090409021f030b0f100212070c030c0905010f0b0705150402060f1b07090c0c0f050102040e070c030e010203030709 73
    0x100e9910681594500070104100405d400c1101c041c1503005071640e2000100070a1940c44680500d502e40d0048080030300000c0901000034020140100d210b50080d0310078000040c15941400a1003c07604400d20302e40c1d058000c2e89412500d4a8441e4001c50b038002091801001c2103080800040350b845140c000d03d0040b0707180e004490079903070340396a50700403821807480132103c0c1070f116400100202400d0030124421043c0004e2814a410b00c505000d400d10000c1d0002d14250700c184000d09100d03040800e08440b105440325002c40011100d03207407a03000b413803145c4000c9129418030400d02c150f250319411200d08100140a401c01240d000100586c001180300c040200030b407694004200030b841003148801d112513000a41e181d9035000c540c01881840001303401c2e80c100c039449420400503603190a0708180040c0d0381068a5000c2402d4202a190a40c0320b10700042c6440d076030750741c1e2603703042044803814041510001c0303036420315400c107c030160080001d00c05180b0b50320b041701000d0302010340e500039001001b0b104d12 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 575648318 1250 575647068 575647099
    0x20a020102091810150e180f010b040b0703030513060e060f13030e2101050112170304080304021c050d0818010c0503010b1e030408190903050c09060d020a030b1f0311 73
    0x850400303420f1405003003240c00034607848140441c0402503400c8007512841c4800042d01400250948083da02a45450b518042341c643b0101d000e044003900c0c45510882c3e440c100030000380984514051309980a014160b5031600003400e500402004010800301604484d81c5800254808040c410191084448403084a4140c070030103050402c808a140140d80b8280022900300b40c4541c0005c40d503845440d468401102c180414152404146e5000300042c030144041801483c02d198901c00401c041c0d400041c4451994031060722701515400b4078400b1607110014488500b031030070384241c80c1c100724400a10a8805410000b00305210521554041d60b001240c0d40c0750010181600780c50141c1100c0110ba00c904050034020007581c40a01c482010030040c07081c6190351400b0364074000480780c220011b440303000441c074288004a040180100d601901d21452440140d46d084903c10186026610072030462510204032900150711460b0b010a180d840001000010703d18140f08414030f0090b10142b0080c031109 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 575649568 1250 575648318 575648327
    0x70504060f120f0f180209270319032f0c0304170c10090e041b0314060702010b04110f0c031b0f160b0711030709020a02010209181015 59
    0xb103072080e074281103500141c1a42500441c8000d81100d0b402c0000031400008003d00b00300000d40250099050000100c04180c2140c100c0000003d40024010480d0516400c03800c5600804910008060360b0140c4546d40d80c0c0b5114542804034000306124140c5607a580c2c078180c1807039005000041c1480050b441425041c140305072070003040070740d84d07241c003940ca07805e20140c43d45540310010707001e035410407500240a4841c100140859005d14518a00c54071a42c9030709020008825a69210301c43c900000000140080504000301c0f43c0d0f00c02a1516040c100320007800d450650700d46d28410b60030201c1000282c0d40d0181143d10120115109a81c1d520340c400e1294258002e40701c0221001c00031300b00e10030704c0030008a41e0056107024101662160fa0140320309000319180e0380500001104148030080014031240721503080d02000a0844000603070b42d50500099034081d00071000140d4003c2414039081c00e0640d60b4508010050819058605d4443c07203c840303841d510b11403040080d12000382c0d4994039025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 575650818 1250 575649568 575649587
    0x804031101090846020f090103032102191706030c0307091d0d05071203020f0a03020c0c090a02070501050a0e03031909080a030c111c050c010204051806030706020303070504060f 78
    0x440818800f80884c0030b001c0c801e40b00385005901400c00b204a1540e0f61810039080c90503285e1585074a440001e03c4c109880d04048040c12161459900b000090040c2580c01020413800f00182da503404a0f40c1c0744040361a0070800500194080d900c024400c840c295008680e44041c1e071f001444c00031703a020240092010903219040d040318070b80548c03001081495880b1004141041c017590342e400252100600480407403048a00d071554620007800002c411600c20b400a040c20b29100f01260040402d503000100030410542d5009203641d40000c25004000c0c1c203000d859844110407804218806520b00c00544922000309034003c011044000c10400f40c48d0f075400403409940000245482c0d00d02d100000d001824100d103044085841c010b8038030181c010009840d1044188025580004e01d1441070030754240d00705c007800205a5400380300119003900c0b901c0c0c2040c000d4042038060310803820010309250415130250028000c54008000f002141e64001c021502110802d00d010045200c4151302120541d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 575652068 1250 575650818 575650903
    0xf110409110d0e01021b0a0f02060904020d050a0501090c1418130c21090c1e080307050a0201030e12042102090403231e03070504030f08040311010908 66
    0x3c0d180c056002d50a0550182c20b692040c0c1303191b098140041001c659590400d100010695038a00340c415005041c400c000d40030b0958040c00c0581000c410349882410344070219244843c941c0c0e50001080010b4003801028091004c0c1e0400140e1702c40c0b10030080c1d400348501c42c804402f81d904d1140152403611060310362605050201c10803c0b902c0380907140100019110403200860981c00104a503101c0d00611801c4072655024010280152034280d0720100d680c43c010a07600c9240d40d80b440002c001100b840104071040c80381000e0407031b50b000c5100240440b440032055001540c081803014401d0b03142d0034201c40a90b005588401c2c0442454810301101c030740c1c4130900941081150050204064000039059500e0100742c8014000701a0360202e01200e00600c001c0c0b108203507aa074500c21100c501c400041d03420901c41d1810700c0c0341c503440391036451504101f60700484000100140070018090a803030b4244421a00b460820f945916040c0c071181e1755660f00360003403211741201c10340d643c0002210400079500d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 575653318 1250 575652068 575652071
    0x1d01050f030f1305033c16060605120f07060e09040809040915090c091e240b041703160b060d1b08012703080903090604030b06040f110409110d 63
    0x194071400c6e0510312070b150b10744098094060035002c0359255140102d0103410840f82c1030600f0048116405540600a403100752586503071120041030b2a100c00d0107000d10b250901e4014541807008441c028903102030355001ca410441900d1400045964124503a600280c20015131611400c0c03000004004203801640241506100314040014018035040304151a00400c8007030341c040c0e030b1150150151003144265840d00c0795a242551200422035003c40326001c8821002c0780700e900c80c0614030320340e0061900001082c440125081008082118081d070b40014100b02440c1080c060614903010900702c004010315070b904c2500007880175200c4059801005400c142d150390601412064024141c0c00d40c0214560b650801b482e203100daa01e440d542c044c082c1000200c0030110b424589040390b46040c0504480e020340001c100d0075202c2d0ba254005000958050250071100c5d08164041004032660105175031141ca042c13200d105085440301054a0440e940ca89000c9040c041d0303000d046000b8401da44a0700d0103103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 575654568 1250 575653318 575653327
    0x10e0f0c0d02180f0904031209050109020909061f050d0303110d0f0c0f020118060e120a020d08063001090c0f03022e0e010c05030a1d01050f030f130503 67
    0x200407010040f00810703c1660924100480308090020904080320082c1c049000c2c40c1b900c8982c080f565000040550184000003034018142e40044d1912009540815455020b1030034402c059907003002603601241d40341e004007501440c060102c1c1c08180f5000001e030505659101ca410920f00c080100d40300d9101ba0482000820131401e4250000d00c15046040d0000b14140f100c0001030380144640040e00c01c0140c0404000c44460b035038034020b800c00040100c1103000c1d001070984040c01001c043d2100248540142030781311611000208100401442c59100d99094a2800305081070040c41500ca081d5003200b481d04501c160743d026014010724180141002540800010f2303011440d50600107a030700c00c443d07a070798030040c8140c00e07040303c01006504220040c070301c1c04084806000c0d0400068928060502c0d80041c046500c400c2c0c155004414981c010134115504a1018102c000c160703100c540c82428810b0030003d0300e10064689000082200c42003820010110705250340501c0c0d07030440c2540c03003400c80703644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 575655818 1250 575654568 575654587
    0x1104170a0501050714030a150305070f180911010f020712080d06050103060303090b07021306030506090d1b2004050c18100c0204020d09020604060203091503010e0f0c0d02 75
    0x94041249040e40d680d46000d001c2402c2c1c0c1d200d201c4403005c4504418060f400d58032010300e04001082040e502c200c501c401440e0010000b0420301690008008004000e02140c7c40c05106900009500c99004080752a000900e40020100b594022030300e00203107050030f00e4240d0a8010707407070320fa01600140700080401c400001044034460042001c03601c00d4009020aa60b110019020342d006800000e000c5003c0303000034401004554081c002c0e150005003445080f442c0300c185001111801e40041d14640c2140c002c00c49007550412070710849221914011820003081d042443c8110391810000b0b0610018040b121003402c005280078010520052081088d802c00da035070b001103588060459600e240b40f1001c508440d03d0b1174409030248500544850701d4800703043d800c10001398440382c0008112541e07420040056181c04002c0c002800142e001542e0316148042002001084242d17020010300c41000184907814200b03c2c0c0c50740009061445800c591249122a030103030041d150001c11452010642484 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 575657068 1250 575655818 575655823
    0x60b060c0c01020c0f0a03020108040c050405070323060105090d02031c02060403020f150a050603030c01111819030b130614010510081e0c040807080606150406090603110417 76
    0x7008242c08442004900005104640159507100d95010403010303010800365008800165200384035150700070030142c85400080451300240c407800c2c002950f86105c50316826030310995244d40c0d000210700030741d0f81c540f600000b42903114601c1118003801c240521102151000c001d418003080946150800b980f2010400943c2c0e42012030302940144036070a44115410004200b80c458280c00140d0089641e44509421014000c050001501448100100c4220740b000388211030082a0081c2d919980f0b200e0715810fa09002c2148000750301c64100c240f24911000340d020815412294013505e10200350f0f480c9003904101c102d0a28002c1c3c07905062024508644101500c4141a240102c406013500c00700010102c54060080302e204c0c01c0c001c158901c00d04003000075a00f10741e1010b0040b46041c42e0581f40d503030300342c1415036662060706507074001414482e0a140c03038801035840700e21503040c01e410309107000b800400c40002485030030185036807664000086050340c0121005000d04201400d5a00c0384004003070b9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 575658318 1250 575657068 575657083
    0x60b04090f06050604032f090907090c09120f060605060408070603180816050304090c020f0705030111071203020f1209010c0305090c1306080601120507050105040e01060309060b060c 80
    0x70546800c40100351442c140c0181c4003500d412100100301800300181040d0083d2003128a440d490034480381c209280d80d42c40c0c515074803c0c901140501590381c0b07043c60800a80d0320130200304c0c6c00e0004603101030000d9403e1000300250035802c82c0b22034035981c8590600500900c0113800c0b440d008200000c01250945000522030100e50140e9001c01c41d141440c40103c185070740304880100544402c200a140706a40740b408024141d0242051b00d107001d5540c0711000031074500d540040c0158102c1c4052080445c0b09005250040034180c0080c000325045074000451072080c0c0b01c0081030010115220030031540701c0d90544070b01d030040c1d5403810b907503001d802542d0503c80c000f2030301c2c0c0e43e083d030803c0199224980701e802550700809040000b8800c86c58482c0820120982d054030052045907a50b000103089481040414022306c41e290320040685c00c9820103504100a50f00400c0c10300608200810450402e0580a0b04540584c5400506140701d8034240c0050b28440144031350124002c1941000c0f11404540503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 575659568 1250 575658318 575658341
    0xc2b0302030a1103040311121f0b0a0b04030b011802071a04122c2b1b080d0c080702040501090b1207230d06050108030703140313080d060b0409 63
    0x5443d04140031959540b48114000100314480c1c3e809203905501380b44921802c0c4d005c11006460405c8107142c080302c1401660b400c4540410b45030802400e1601b08a203880015041d1255190700d07280c1540ca13864040c25040c0700e0418003244050b40f1a141500c2941515500c581c0f020000940c0d10161031068030010302543e0036624604040442014240680b5404500030b848078407901c02e42104106e0054001028040650088420140c4076560340c01184006d403c18240c00c1c0d1400d07140b09509060304030010881e201c40040d100344100740000d941c0024418407080d071034034102017800f5413442c214405024901d030080d04241440001303d1038070890b0f00b0904001e10155046110304040003485035541085110b1200c035860395941c4000f060491034030203109544c1c05400100c088c8900d94a100496809a10011f25600701040560416501007604007031400340d03400c05819401c1904c0902801e034507400004045200c001511002000c480c1c01440041800804250320345940d03001c03c1c0c1c040e00c0d1807441e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 575660818 1250 575659568 575659577
    0x60d05060901060f0e0712110f03041505011203020303040609140a0b090c010f14030408040e100806131a0414070b0304020a0e070527040618050105120c2b0302030a 72
    0xc54482e80210300d10f4414503060340ca141000d491031610500a000351880123214840070800741401440e4040118080c51044604c8019016007900132000ca42040e00000403440d01c403a00440400c0d400815282c0007500504000351203412031900203d81c840310640c204d0f00d405140c82001c280000c4156151143c001181601c2882200c0d50045030321040d64404040450031440c030961480c01c49101540d4014400c0701d01d07500c2c058603038204894019048880b5612080d0a00e414004035005008031a0022902e80e03041d0910300c1a565030140c4a6120040f440202c0007500008003404200308155a00c03410060990310b03c251940343d040110350040387e05038001c07240b00c100081c94610454130f0911030700081d510b00b8240303840030318011034241203039450380c0500ca0424142e02440e901c0340f203840f00403c03031455440700c80184640e1100075104140e01252260b048900d10000400e00428481d4005104130340b548258003c1d00c00f181c1800381d810b80f04c203803030781d03402c0241030200341d0004000c100c448034070b458 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 575662068 1250 575660818 575660849
    0x60201060b0f091f03050a1407120b0a1e150c080f07031202220b1815130e0f060307080705040b120613260403060f02160b1503030309030909060d0506090106 69
    0x123401041a003914210000395080d04074a0040e944c41e0b200541502009010307900700c0c0e503112400a4401e1031500d040c0000c003003c400c1003100c1c08501580006119050400680071070103a01d5207001400b410901c00000000060250b080512a4015191f0001559400c40d01c42c8405040392444d0b0a805856031200140d0b5440400d00503c810300340c03007000c1200f0076071401c140121000d00401000140200c003074030100340300c02c16201c03502ea407016000e45400d0401c03544901e0006084804104080d007482d0080c0c0000206000c800742c0424100c064a80c26103001c80d4811001020410310a07416096207124003c142c1480818000400000303843da01611599144400309141401ca5604c0c000482c07403144410001000000c002d43c004540400c0c00c103030700505040782043d01003e0540b10300d40488484040c0c00402c1f100f04442810038080200980065080d0310703100e45000d80c2da01c1802c2030315104042000020b805940c0d1071981a004035844002e8030200d00b4190800743c06024135005560000d01e02c9030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 575663318 1250 575662068 575662091
    0xd0f05060621100b030a051f0b06070c1413060f0312050c070311041e0b0307090b03030720100302030a0b2b0305090303130906060201060b0f091f03050a 67
    0x11581c01c0e0307842010014094855901d9040c10044c04401070080d010f0140903c040e000c00c0040c441850222000030788000b60220b40d440940443d05040313505032091405020328000b04e5401c540341015180104a14488110706074001080022a000020f00700307400c3c00404290400c50041860440f40300b120300d00700541c0c103143d05546900450600700401c1d1700c41c610810121351850300c0b4201c1000d0141c0b001401110030401c1403110300c111300c2c038005151b44510585030300e800d08102c110001d050310501006038480310400283c40b403154075006401002039140360b45a40c00c8540c402c580904006180c0c203050600108060044c1d04201c807101c0182d8036041510009040214a61100c84201c21b14000440e054020000892810500503000c0160502c48140c0c1c68a0400041011082e0381060681c0d852401e010340d03068a804e0780040c0110390402d40108601103203c4184c1e440003000c00c082d5600c0e50041d42c0800c11072400900040f4014483d01d1602d05825090b80c0002d019a0810006228080000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 575664568 1250 575663318 575663359
    0x11030703180e04050604080a1806030e0d0504080d030207020a0815011a07080706180501050112060609020405060a0c0303110d050103140f0c0d060b030d030e0715140304020d0f050606 80
    0x45401419031742000d00014001908400140402c1b04c3d03a041c40e101c0403104034118040c442003500400d01107580c0f1880c06e560a1010400d41a8908580c07420034a01420810030310b403589e03c2c0380c4440c8203040d004151101190388510111000d4510301040f00c2c506040c0300c003551a00e17031081c031510801c0800e00107980700030050712003141e48507031700000c0c1c0c140340c2040e0307a1751030700109401440002004400030180000480070f009490007440380d14202c1c0e401c0ca900e410300304100c1d40c250b40300c1d41b84c1c82d02c1040108580d49038003050f110790030004c0c02d210314884540d040603405081c056582c0d031600000082c65842070502503016034140ca010740648150b944000e80510382d20b000d45c502d800c0c0a03a101001e413101902e4103190040c0d45501c42c03140455880804400300346490204240c100c0400e84849007003007482404c0080c3c000400d8036140d24600303561042c502405806405004410f82400000001c0c1503458216104103002d40c0507540281c00090b6090403a01c078101035694520901d24081800d0101141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 575665818 1250 575664568 575664571
    0x510050a02150a1b0519091421010c120b030d021e03090a180e0d0c0201050307030b030318150f0f070c03120302030f06120a060c11030703180e 63
    0x190010141160071082142c44a00d0080054884944400c0b6081d221800356040d03420700f481075100c068481d03004500c0d6119040c200b14144080001404081100c200c240005103c050405d6420180106010004036030b10144001410030943c02e0040000070150301c003010b0500c5540602e000c03c089599102090b444091030036041c1d00680c0444919481682000d46411580b415031007201d1420701c141011552006569102082c184855401304100100340c0c050700c00700c061924040c0003082c0580102410b01c0c8a11b4030042d04111000c800141c605002c2d90240360440d40003004c594503000c0d00e01d207003c1c050704e94000940c0284803202d8606400d1801e0003d907804602c1c251211070800f0b80140411640380c20001c1c00741c440b0f800c03045001000ca200000e05601070800f5a0340541d0b60b1034a0300300760b0300c13036600035207072034018012071500c044201c2000c0303108054164005000300300c01e1103010007210310000440d0481010b0200040c2d071002c2603004200303000d2540580401070b40303c9644140300e440e207940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 575667068 1250 575665818 575665837
    0x506040b1909050301111c060e0705131a0c010c0e010207170a0f0b011a04122303030112150509030415020304090501180f0504030e3007051005 63
    0x24014052800319440d00601d1801031460b180340516680d000080c01d543c0150601160b02d0800100701c80452000007da09200c0844d80090010070314040400c140d00c98001d0030329040003408a88039440e064801c80e140c3c01001601002035072881116041d40ca00e51103000e410625628203200c0e540240e002c0c007480000004c058020b448080e180071042c0e04105400c2c400074259004005144d400035a16400d011100ca004d988036003041c3d070618549000c400c02c9407001410f901c40c180300c100080854002d8041007581c1c05214070f01d496544060100340701030390411240c00b0b40000301c00428000c3e1003182c0f081e499409254045419080a51410b0840300c00351030006840d00100300030711498520861014003d80e25104491800b030760340c040d41d13044400a030421050907203850f1608800d2403142c05400003821040e801040507040580d009090b40906c0748000c1c2c002e03130030003000340c0043d00c00c3e00e8151400854800442c803403050040c441912000f440c0601c61080342d5000c40301c00554401e1065451448 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 575668318 1250 575667068 575667089
    0x607110601050d020301091a06010f031b0309080712030b03010b180c071403160605010902090d110103020904050a02040e09030c07090209211b0f150a030b03150907050604 75
    0x2402c003000d1003904a89008281c2c0c041d900d4113101400903001c0d940c13254403850110407001c00d03030409800061084101002940815062654080b107414041400801c4140e550400103800b0070b80780b400c00424054008040c00072511400703031000254058104d01c0045ca81240200300c0000742c0700400001c54100e451880c101074400000a04040c0c00354014090700307004034a0007010010000c050303445c0d81d20a40811a2203a5001007450800c0180d01509014004031003066060505940108180112040c80a48944680c03504504540d0003030b4115004080c010b403050250b440c200300d400b000395001c4c1c4204e10803818000300140c2d040e040402601c1c8903a207200b000e8803096160a040c07401030b40240780d15680c410071900801a0385643c0245400303030b03848200041d007440c1d40c491880c46004030182000b98090200b844001005a80f111809030015010385d00c0e664495115071030450040ca8802140d60705803080c0ca01484c1d0015140070607170301c1220301c042140c0300507884400b130094170b028a01c02d01c8103e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 575669568 1250 575668318 575668321
    0xf0e03040b090a26010c0f050910030f060605071415040809010e09040f0c06111513082205010e1c032705040b03010c050f1e040902030906071106 64
    0x201e004900400315a072004058025040e03c801d00411181d46002d01e0b12001c00105102031640b00c001e0151038810842414009000000c010000e01148501008503218500d20002076884c6c038000d9000d5800c001400108121154840034007420303582c0302000680e042080394022902c0c0082c00034080b00c003040ca41d800a50a0303142c4d9039595040e9082220101c1c1403203000240301c0c13055102d0048251040b030042c64560400f5407941012072504015402031010002d1881411800260020340d06429114203200c1c0c14440e0780301a003e203100150894010009000001c00000c001c511403524180e0210070342c81600d800d40e61b100107440d2080030800d0642c02c140210302c041c030a203040074a910140307800707810302100401d4005c45402e41a080300d0f5034101100600341007444281824400c00b5004d020641c000c01c070304520b005c07001d0100e00400340440d14154000440401a0050f02d0b180c0d442c42c5001c1d01d4003034503a40c07102001c00194004a803000580c2c030443c400a03201c207220384c42600b0300d403030034401a2459 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 575670818 1250 575669568 575669579
    0xc0f01020a02150f0f0a030509010501050604180b060d020a17010f0302040507020307020916030e0c030604080f0d0204060201061404090b3d05010906080c04060f0309021009090f0e0304 81
    0x2080c0000608103c3c8050070b10201882c5600d260040644110001e091940c2c0d00c20b00601030700b210700241036a00305070315290040c02241c441d04100c4042ea034090101180b107941400300c001c01341540f91101e503001940465100c402e10b200da0054406440591503540b800c0f011044c5c50103210f8000d1040410b01c8424980030805410315920041e0400e00343e1042d00e2400300960082030b40c400b02074a10f6222601c54514030004d0980c940b040c400d100b1000000703050f5205840c00041d0b41c8030700250020b418403a000640c000b00c50b540e00704407802048071200c255241c1d50384e0b920181c02040755105001e1451049030071000c462400d84103e404503a4014400080e40c0c4416040081e90303007515000d0100e06c900f00c1510702c001c1c0d01030098850070380d103004080e00c80141040d00042c1181426404030003803081c2002800074450040080e2400d8420f80e28020b115001c200318118054885900040c5d080340b8030754080600b40b64030410300703816034008400c01d00034081c0101401040301c0d000080440c0d290400c2c8410b012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 575672068 1250 575670818 575670829
    0x904140402120d0c0609110613080105010b0703020307061d0604050706030501120210120b1c02041125050a0212150601050a0909181e03030506010c17090109080d0c03020c0f01020a02 80
    0x2c1b020300559294100040e880c01082c019440800710b04118a01c16808001c0c480342402442d02400001c880c050030301c44590303000381d0b80340641400100400e894510180c050241c603c001d4401e04000404c80f401410329080c03c40d00c540e20360280030300090030007001040d02e0a444055840d996800b400f05000e240c043d06040703803c8105031a080041c00c0d21a04030808640d078120640b2030810740709030405600300092041108a490303849505010032070620600c81e646180c2c0c13461504041440b00900c41d00345551401e9801c2800100c0001d500465191a8900c0e603100040d2503002110184c01c1c440098403820010354071800313029040c0c00002c0e43d015003480100307a1504214517910f51030105141d03204540d6100760080240700c00312115811401020f10134541e00d4020280c002400b800e242162140b50b13220f00340347d81024005c84010041c00181074581c0d902c0360403844002c0160f01c0680322501c000c82d00050003a20800015401886226100010b40c40c00d5441703a480320805030001c20311804a80e00303000c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 575673318 1250 575672068 575672081
    0x8070903062013090516050f0a03020d0914010c02210c0705060a0f171027050702070501090504060e280627200f0904140402120d0c06 59
    0x151103140d84207482e4840c1101014003918090800c442a40c81e00b081080303070445500070701004c1142010f4141c072a002d0741006c12a04000c4068880301d0f95005e0010040e0301911802100c42041032030b00040b04284150070381c0030040d0050b0700d0001d100b185200d031822a5034a554200b041400c040d49940c0310303840d8106000601c1d800900ca01598180c607501c0c0c0019400b500b280c847c510200790894000c100260380100b0581e008021102a481141409030101406071000d001754200150820b4503003004211034a000058050010024803180c900003200a499210521070f15010490110307020805141c81c4c0121001d99403509800d451543d1a07583c3c10301e00400c04a10706158480c2d1025041c01c0305e0700c502650018040810750610f105484503856034010400140d000040f0b464209408403000041c4a039009404401c4801521805002c0c030b107000c184906640d041e0722924188417510003002154110744510300803200c4c65854800e0010b696102c46002504a000820300348140c3c0c00075040d42e0150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 575674568 1250 575673318 575673341
    0xc010806010e0303160c06090f0e0703022205040b0303160f020d120e09070c1e02011e030e0c01080f01031401020f0a02011505010201020a020c0f0612010e0906070807090306 76
    0xd14140900b0790200e401e41c0c0c880740416414010042c031503401d004440018000600341440c1c60100249010043c00842a5034090304032038450306004607802c14031079015500180180072400e12415241d1010310012165440b030300340540c1c01c145402611b850301209492150080a08104100380c099442c1201e82101c10002c0340d0040700d132001600803c03002d00c4c0d940b00e0140c0c191603046402500f8404c03c0180c100040c00318040004e039038900800100207000c0649100821100b04240071407600c010380d285640041d82c100b00c18660740b419102d40354103030440000d038031040080c2c800c00e0f001c041c01142e41503011503680201d151000300420001d80100c460f000d464210070001800d10078041c42d50080c1e1b501c07c85032400182c1d1030340c1030014920f508424181c0108424002103103000034110000e515440c41c3c1385030502c100c07600c4841c401c2d07945844007200c0391200311070440103840d80c44400d5826988019a0018540d2084600080905018041441c0101056103841c40305614556407080900b01c0e00100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 575675818 1250 575674568 575674577
    0x12110322061d030703110c011202130810020a091707060c0f08030a06060f090806010b090315130b0901020307050409090203030c0a050c270a09020307030c0902040302040c0507050c01080601 83
    0x15403015a502004098054000310040c40e91039404d802c0c020700707564074419850746980100d8410b40d1750384e03080703900d65800c54200100542c48600c0607540c0c40810240350721982c3c440c010764180340d44042c001e0b401080c6074045900d030140119220303524403d0107a800300c100512b5600060060003103500901c0c000007840e10440101145035004d40e64031405800503154640d03803945903141400a40c0d0044221280180310f40343c00e250b11850050300d1a5545418801e05003007071030004a0504548040c00241074442c6000b0004285080000180d0000403c0301800d40d5108901804503e8409040c001c03640100f410341e45460a150400483d40b0080c8803598081340d241c4000c110300c12122109002400901d405040989808140301060114000303000b0708010703201807080c00031962404400d040e50f410043e21400040e82d0b405600c0480c6c684003c9c1d80003d004d00d1080000040c07101c04d80d800030030640e4800d94007400043c0020000f1b071018002c00400601a8024060500c03440d44142582070b03120605141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 575677068 1250 575675818 575675831
    0x10e0f07031721071119021c0f050f012315011205070807021903020a110d050f0c0a05040911090622050a06080a080f0a0e0a061211032206 61
    0xc5400f030b502d00d901450200c2c0305441e81003000d810782011012400c015143c0107807006100c18115050740c4c0d0003581c0007e01c1100a09441c10030a003004444156840e0b2081404288130002c0c28003d542ea840c00b44100310300d41c01e0450380b104034041c4580f82c944507416500c000c6040e40b0780c2c00c410403130401450400340c104210340d1400031000300a40140c80c0142c0c80d50715840e0b9541003600c0008c2c14514503000404111030701248410000390f00027030700b420050f0407070400e194008600340007030455002c151015040b40300390889001041030208040d50303a101e08413140b140b280c0d560700901095807102d083c0504420320000c005002414608829030780032200801030700900300100c105108826260801c10111030b940d10420440074050312030007014050840c020103503c070444e51128401d00c81c0c034484420b070b81d80105951845030f0098201e54101500188001306082d01c401005004040c3c0030601c551712400d2078120070610881404036402111a80144840d60b42c3d1540260048021540100c606555030038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 575678318 1250 575677068 575677087
    0xa210e0a030f03030b0913031d030312090d1706040b030c06160201090f030c03020d0f050a0f02030d0801140121060f0513060602100b030c090901020408010e0f070317 73
    0x10540005503126640703200300410b0906000701296000a4103a009045403014008510780c80c0440c505c030710340c0c50310b003035048500840701b41c0d94080e918990f07a541610010440c0f48042107496580e5100d4550310301110b401c0706015000700c40713041d00d445500459825400c04a20b8604142d005140c10440c0941229420b648000108510303a02200e1018100c910451140c0c0856a01240c000b0050044051003010302d802d58864082080161000900c24012440100200500c18078030700040d41d0081c00b0b880b225405810900b00400220408038841d008211001220030301a2950505845407050310303641051070341005449106003041d20040c803071803c2c044a50782200da4060032014140340b40400d0841860f11003849083d01d40003040f42141c5007895020300c42301e0f90000d03210b00e9154078a600401c0200101c0003090400b40c050b008075400c00340c0c1004010000c1c005400402c2210000300003000100d42c500074054a9400c03100f000134090300312320010400310740d040b400280c254091442085c0340c000380380f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 575679568 1250 575678318 575678329
    0x809030a0b0a110403021503061315060305070527010203120109020c010b0a030f03140708160b100305250807061d100507120203250210020a210e 64
    0x400301118180844400c0202d2804a40160000d11050081d0503092904540c0024000c2d840060b81036076000340480040c6041d1b5850741202c0f4800b40400c01002810f90640d500d08403025540180030100c2e04200200d0819807150045405119407204004c0c0401c1030040461102010541308604500c000d100861016011a24090080c0441d02c00160307513001001c911403c1d21041c80105204440004042000c030b4051042401160392514000d0810780d00b030703007108486000c2d483c40508810320216003020700da003c080c02c405006010300111485641d451000c01a00c0d60b540c0002440743d08070307240b000d1307940c4003284401c000b41e64121301d41780c5090b88902d0340901d05030441d4042d4001904500c1c0c4201600d8081c05c543c400600c060394002c2c00e04590003c05000352040310030081c0107640500070880010b2003441034030340580e6100b008a010b4144c508103500c14185020041c7e2142c0c05c8003d14995142c00012105400da52100010158006520040b20b600000c8845c0900b4003000240b00c55642e41c56 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 575680818 1250 575679568 575679583
    0xf0f03060601230d0e16030302030a0503070302040b0f093307050109021005030109050c0a0f1d040c111b010f270e15100509042004090501052812080903 67
    0xf0015003217032030025007441c0c010028071b00e50070b43c40c0411007400400da001c000c60741d2107000760030070b01e90b26190990700314000d2165074004110340c0800f05400049440c5c0000801e0490f0007241d5140c0705134202c0d0800200a240020703042409105101c80f56086030b020406040d455000b10000039450301c0b96000f1600b130130804410040010310000050080103000e02c1259000340c40503540c1070905910100203400c0e52908102801880a80e505c00b1100e4900300c1e01c0d01c140004090001e220004034045c003e011644004044030840c011588000c5034202c6540401030391441c165950900c603000c2d0401a00c040c41c0c0d0300401142e040c101c1c069940c6c0c408507291802d0041c0080f5000038082e18194003035103100b1070616000c5120320300070500600b40c554000b040d550b40d00021980003078048000801c03000c1c1a0310a2202d410881d01c049400100c0c404564001c0e812142c2c16208882d645c81c900c403900e40c281056001010b144030724290180304000300840300d10f802e10303c90711005140102c0e110019191841c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 575682068 1250 575680818 575680837
    0x140405090106021c02011803050f0d060f0819052e02040303021e0a030e01110f010f0903110d0512060f0303071b0b0705060c03250e0f0f0306060123 65
    0x64035051381003610318100b080c0f841841d072000300600c66803003c9443c0c001d04e100f24050100900032600c8014144100c0880f9500a1031250410400d0b0383c44d00344039800001c900c00c6421900510081d00b030244100140c10021a03400700c00b91486460b514030aa4100d00070b20071401201e65070505405100d0f0951004201842c069001081420350a03d161104601c4130803844d500ca03080304080100003070300052003c0b2101c00900304103204c502c0074041145044440b00c0c00203800c0d030901001400030304840d8001ca200038080c0c1d031284101120a54025039a240600d00040050130412040e00003849a00c52039402000040001c520310342d51400007459030704020f130705540c140c2c000b103400100b0240da4040c0f6001089681c1640c0e061668640380c1c00c3e1243d50040180c01090070000c0064901c54070360810130300c2d920003030a40d80305000c82c4400080c1010303c0074a0940c00340d0755000e0518042d01c0c00b9190030f100c222005006010710781e100801100c5500132010b40c0d85560280d07040805c07021000c2c030081c0c50241c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 575683318 1250 575682068 575682073
    0x8071431091104020903060a0504110406060509150f03040f080904091b0504200706060e0907061803081c14161403090606091015090602161514040509010602 69
    0x7080e9041060700c030410311264910961040180c0c0c05241c030b0200e1a03d0f8042c0300e140c0009070994540c200b6601c04c03034004517a2075105e450480d0200d041c1e908080508804e500544040351104496290354016100d880c201c41e41101040c40010000395609040200300c42c070503100541803100020210b4107441c2c001d0402c8941080b1001c5000e0f00000c00c6400c0c1c0002e0508650520020001c0001c0705400d8500719402403405000141036414019603070071110080c035405900c02c54074a002550680c48400602070500007581000b4804854400b031035058060307a4100d090989042c0281710300c3c1c0b4003008602d80c1c1502d80e5441c0c1d501d2441808880c1c182d2841a0503a9641c407041003a48a40180241ba6400301114203510034401d00460f024005861a44404e081e40d0110240e25401c0802840c60713030583c080510070100070400d4140d00d034040446000c44240c1d03000c41c0c442101d9500b00c1e1040100c51700404022012007400c070718907103220721803103801c0e40b20307850009280c1611080840c80c0384909800100241e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 575684568 1250 575683318 575683331
    0x209072304080f0705090a020904060f0305010b10090e01181803090512010917031902070501060302040506060702011e090f080f0613210e040f050402030708071431 72
    0xb0b02c41440103008107000c0402420383c0d141408000781d40b10402401d45401940e000c079112081c1c1d282d56200b1405092b404d00c0030100b035a92480c000d4003801c030304502d082c000d01645000c1c40307009005034030b100d056032801a00d400f0141c1c00c0803084131f54420400c1e15209040c1c1c40c2ca40401c0c3d0b500440407944174183c069528640014142000d000c012000e560f071311601a850010742e100410030004032030108218240401d541c1e52106061540f540e00001c04034402244005200010403805511000483c0d2090301c09100594840040055500440e24064085050034407141500020040d031000500c845050110f00907484440c509a040e9198000061f15402126144041182045420380c048821403c11046620943d5a2030560700081d0b601126120200500a00383c0d0060384201130142e005007080040d0300c08456807101600c1c00351405d0740280a100d9020800240c0442c4000540302215056480c0c0410740c41072042240915a043c2c0c0b4281010410000c0c3d0003504244060451a085010691 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 575685818 1250 575684568 575684579
    0xc0f13032001022808090307030503031e010603020f0912010e1f1a01091a0d05040803250c030e03030702060c062509050103050621010e1014040209072304 68
    0x10b220040d80c04001c010304c44184010b48a0101072007000f690fa228141d1911000124040b1740b901d04550401040b0b0300000c000c04c641040030490410b03503080302c983c085c0350383c1c4d0740c07000160128401c007100450b00394070401c400d103c030f4100811100405861000001030103a000d441c8a4109506001c0007282215000c0300c1410b0301820703000f01092a04102d15500300340100100207000c8800c903100d03507200303200700750032040c4006401000d40c1c45070b9444001c02e01c042d04d028074102409902c02c46080e0b64600807032821040703100400c200c4d1034901115440310601c11000b51025900c941c40450140c2d4103210412100c0700507283d640180c1301090210740248143e0410465100142604041c00d450300e2001c0d022080440b544004038404485082c240046c41d501c0304e20109e000801d0f01c8031035444c039100079451816690015440419103903801000d032204212980f0000301541c041c1c510514407490318001080c054544040116001519801c0c42e40510642641c02e1150000085080310382c0745011504104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 575687068 1250 575685818 575685823
    0x130c1809020f0406050a05130e030708041805070e13290907111b0f0307030506010501090902031302120307051009120305090718140a0506010e090c0f1303200102 71
    0x40e1001c01c40b03080c0049805c0c0004117130003c2c620302c203462081d09a200040440c0c1265800707070404030811001c0c0c0e55245445c0c20408a154458450820b584410003140c00100c1003522a0a000c0d00d2650f0302c59a000d801d89042154a01c01c0040c0d51700003907550b5010b010405c11400503d0641886900100814100d203820485103040052018052043c40f0410300e00c002d80c04161030000010b51b403050043c0c0304005000c1035030300c007416881d150075118442d0003009124000413400e041b15404d98136051400d45404105040e0700003920324400111226000c040185406464480004054011242841c9141c1c50b15031609080c07080786901269114881d40a00040150880c08a035040c203060100782041810349a4820442c1314218000020045c652100c0140750003050344c42c4d030035038007004180c245034003618020402a02c013140841d0305503826268608006404904c102a407100c0d2a0901720410f910080d81c1d485030661a02c4201520340110000d00000c950010018840c013103445841d00f000000391 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 575688318 1250 575687068 575687089
    0x31104090506040c08010806040b070c230111130b0c0c090c03041112061b0d020a051c0b060f0d09080f09330702060c0141130c180902 59
    0x44c05c011000e8010f020802000501d1030f00544d00c0118480141e5600204039401d0b850301000500c4211a8441da0850070540c1944001e0101200e0082001440324940741d02d0900c60035405050740d4a100c501009801c0405e005003401002000548140035071140000e00040f4044814000b941008800c0c00f0600014141d0003800e000e0580c2d100400e00c0c0031008850351410001c1c4079200c0208181c07440b010b660f01240580303800644007407007551111030341740c0c0c007401e03d804c40d0020070007060a40850154503c40c0b40140b4000e5100138041342e02e00001c000341c98403aa4000b40030803004039181c820070781c00288000300800460303031010b00e0b445e15040b480c410803c54030f142498020350800400445011085001038100e80c200710844601d585042900c041820b50203103810f07405d019440c00f00c0104640e9034800c00c4240b58050600c10f024440c442c0c2c80050008448242d103805a0405000000c0c80005d00100c03000750980a10300c0d6200c1c50f41d03035444544150f42002100101d05446110b040210b0615040c01c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 575689568 1250 575688318 575688341
    0x10801020403080f0c0f030a020a030e1f050c010b030d0906021e0712020114180102070f0609060804061b02010209040b06040e04030c02060d09081c0b0d060c03110409050604 76
    0x3540780600e55203c2004074011180079500c8010005100c02c2c145c40c003001a015038410700400c4d0382d1110440e2030081e44642104406801181c1d180320440c0561412150102c0d1a108541d0310307000380c00146d142112540c00095010325599a1503540000d075039001c02c00b800da10039940e5580d480003810610004d06084521000c050845824140d0303849400001c03034483d0603030300148150258086a8001240c000b080c42d1440c540b4000c0003d0707a07440b000600804010305040070380865042a0f40c41404403140501751280d000050302916061042900ca005150342160250300042240c0b0001c5402400480c220030101003d42e500194040642c2014060048150300032a03449083c94904081900703032403c0204018104001d20780381c10b045540d41c00503518100c440c038a00300f00600070303890102e020b03074131085c50080070b05101041d40d03a610341180940410540e01402910114882e56030740d8010f411034048580605898810310041d40100380050001000d0315440440d06091a1040c07204a85030f14048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 575690818 1250 575689568 575689571
    0x1e010b130905160e040902040504140d0c03020c040515030d1d0111030f0307140403030e030610031208100b0d1b0f0503040312061502060a0b0102160e09071a04030b010801 75
    0xb000110070801440710059121820700764400004d44e000036004001e5040000d60161500c4148002d00c003540c10a40d1800036903508803882a11010300544050a00070300050041e484031080a001d410305401c015044228002c1c0d6040c5201e645001034141161380303091074000340c1103413100e602c1445641e00c01b628940080c04c10540f181c4d0542a041d4903880790041500626400101140403a403007404c140d101c071043d80080703d490f01d0300c81c60000c1110300c42842981c03088c45007030081110100603441078021264043c550094103000341a00340c46401000f8000c000390040440300203507084090000b0b160645441c0000100621280035492000c03081c20300c4d407420486444072018680c0c0d009000c503034005c0d4050400349a81302c2400c0305940601038a8102d19240150903007240b45981d000108940106240c10342440000440c0004a85d60800d000036207205018005c402c004a030700504900760001e0000c815125040d4071019000070003c51449450a82140010104144981c0440e400d000d010b21400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 575692068 1250 575690818 575690821
    0x708040203012703320301030501060b120402010c151b0206130305040e15040f0203010e09210a05120c04080d11100f0b03010606030e071a070b1e010b130905 69
    0x70040c26803c4103500101401009040c0906000b01480104002600c0080014400f40508140b0201b50170a10040705c081d828503c01040281c07099090b203107c4405841c0e44030603a561a001160200c10001003030b07401319172816081180aa650041d003c1600c0110241040c41c0c40390480286014801840400da00700b415a4260000380d0040c1210704440c1000b1002c0015101d03000306864140d1040c09040c1e02515018000920f100c40b5000b40d4100c0c0c031010030348013031a0b440603101c503220800c0a41104121700c50505a5440145160140109204074906103080c488a05103c01c0d000f071040e40c460f400002c0c0400c08001e0701d8000c20103030f10802803924011408101d10a03501d075481241074070034089141c584030005d0030003000394416065413030010000d020031543c80b94094010306401c1132041860240d50070200d0364182d8504513920100e580c220043c50401c42c1d0b20b40080d54100a084078420310240008040c40d05010005540a08404a0141c0d550050100343d110000140d600c9090890b08000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 575693318 1250 575692068 575692121
    0x90d061b0e030a2310090b0a1d07030209180109060603140d090b280f030606030b030304140312030705120709030f020409050f010204030309080c06120a2003070804020301 75
    0x1012181e415007914207101c0c4a0002c261541c03d203040043c140005d503151040c000c09101c01c02c48202d008510f241c10820418032000d07440003040d2030750718806141d94400802003005041013101d05500c46219050907000784101244282503581c10001507522540351501801807000b0600e011082d0700b0081d00804811030303c0007010380411030302d2162120020b8042224100313504c9540b0000090010511304843c4075a00034009080744032540708800000740340006c04201c00d80203110748001004001d00642c1000d00d8200c19103e000c002074181034040c01480124001208201c0c0554080c00050722101e840c3c40d1490980c0c00b40b500020011010040909000c2000c1550805c0610b40e15030150b5000c0352980103401c02c285843c4000c1c010005039032000400000341a0700624041c00e8400c01420365481725180c0c4200001c41c02070100241c6580c420742c004c980b1590f0117501010201a403000040e18119000c00740d0061608111640c0d07020511407010007003103290078444c400311070100c0d40707422004a0095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 575694568 1250 575693318 575693333
    0x6060309020d170904020d150801060602031204051905030304060e0703020d121e02070602011406060307050711040908031909031e181d070503040807030302090d061b0e030a 76
    0x140c0007074252029812100380f40c1412408a03a42d994014006664407084042c3c0130b8010404a0808030040840d5000071403403c4042c040e000480384c07950b00842c02c10a005595035400c0780f011f00300302d80600c00d000d000c02801c0d076641c02c025002800b45000d16142e1a2071700b0a04240c44128586030840d0300500000d00069a580480ba202c468005a03031303069040303031580c040d240180c00780500030440c0307010540c9403c01540083c0080c242c405540c02404442c0343d54400409000342600c40035400f400074000100340c80e10602c0a030a007140142c070040010190100414102d0702030060a40d428134000082101080c03001100754111070030004104003007425034038010489c0988008210081a0748001840c800f4807071040f00c041704000c00c0f04c0a01171a40c80f1100e0103201c20030001101c0320550400003c203410b02440c2501e109903088800d25140c6002541c049009501200c4603030380c0030380c0522540021408510034850010a865a40d1444103480c00014040500c010011b0b4800d5101040c52000134418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 575695818 1250 575694568 575694589
    0x1150909020714060907080c0d020f091b04060509100206070818161203030e07082104090e0d030b03010204030818040908180a0e1311030f0f030c010606030902 70
    0x1821401601e800003454840000300d03699800403811300c2808184440300b40040b0f07607001104e0500048820b001104028000f0007008a00080c2d400148048100001d0822032415540003000241d924114010041d80a0710b541054002c80b0008201145200190034112980d4020007420b0000301014581280c00901a0100170500301c421b500c828030110101004000c40c0b1340740c904205000d10840e40740c1d40155142800202c0680001b0706103460314003c1e07400412150103480d40c8c80003030841d41d818514800301c0c0002e4139003c003100326810040045c141c1c0d160300c106002d822000002c0d001009038070030010281c3e01c016104900c00d07441004204005000c1000712518048401608901c0d9183c1c0c00c00034000302540e900141503850001180c0c405010b00340e82d9a4082c000845034851041e4464511a00e000c44c110b601d00503440d04851401301180302d03190108881d06001b812109001c44811149081c008480315400103a8004250000594800e000303400261100f40b40421104a083c1c00082c0784094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 575697068 1250 575695818 575695829
    0x105090f061e040204080102071a24010e121011040f0501030e0f0105040f1205030105012c0a0815010504020a0c020112060504061401030c0c0c14030c03010608010b09011509 76
    0x4410540d2a03078441e0ba90038050452000520031521503503500c01d800d0107540562000c4540e520945032032042c42c41084e1955019424030044c03020211b8407040300300e80c007409103440c090502680e04070a0509a440701a032041d210b500da03000d4400103000d4040682035035600401c0050a100c140400e100354034054030303400111a02440c010880b80300e4403540c50300302112024440768550805040200344240d040101d41041e00c607138031050244840341030441e8140803c1c098240001c603064104140c40c040f07900380c1c03010340004d495089a5032031400d001030020341e801d82c8846160b4011094443e2043c0c4007044103801084c06860951a0480c014001007441071b01d88002410703c4031101d05485060f5056220102401000e841000155110440c1d02c000e0b038060140d1751300090800b100c43c40b21521500308016042c2e44000f0300c515480c1003500420400360740310041034262140c5020300c0d000707a600340280d400a290b000000211100e414003803007003048050304080e41981d2003040d8409956400b078110012200e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 575698318 1250 575697068 575697079
    0x4140306010e06060a0908070e011d040b0105040b040e060f1008070302030a12170c090405070302120c030a0e15011a072a1221031811010302090901030f0b0105090f06 73
    0x41a803a802d43e806caa194000c2113413441074210118a03002945030540c180d0b401d80580008102402c05000c070385900440d001007640015000420450a040c1c110311000d0400901c003083c541507040c0741601c0e0541c2250a40c548501d003a00344040316541c4030054001d0325440d0060f204550031078011070f5860360301c00c4005008001c8144180b034014071412081101800d04641c40300c850502c100c0241080c0c114404503489249084007041c10700d40281308803034101d10b42142d0700d04a60b440300c413134076102c0d00010300d40420a03440d006e003941a06000d0060030349940b68200728406070f5041c0f0120500400014480d00c035043e9007002202c011902c6010916126014014006c1c111220941340307801ca400d1f69480314403008000344882003040a290f440b442c400c003403000740380003044800b607045040ea03e4102031280001c042c10007440c00305070042c85c680703070540041c100945400300490119018a40990050342c04c1c10240f4224000c10040f10003890060008850540e110304041c044242c12070350240c1114400c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 575699568 1250 575698318 575698327
    0x90a030e060a09120c0509070807020a140f1f050c09090f09210706140106120b0604051903050c0904020a0905040f0c0f1403030c030702090a0e0a0804140306010e0606 73
    0xd84900d8499002e0100c82d81134082c049490b141c8031042591500406101c1e254403000140268850007106101c2e003c2640100000c01560316800207540204412046030b0007030b1140d010468104005800949111094008006040340c0d445011100068440007100707600f0802c3c00455078440000070f030400c011031601003e5490351040c1c54908181e0000f4100d200d403095400d40000d107071100140946900801c81400081e07218140001030103424018580440e05001c0140c241e903160707a0020b180c900c009000070303241603114000a004a5041c00714007000d00c1000005000b0003500380700b60014a482a81d4900c0d29003059400680c2030328a60049030030496440000800f840f50300903a0801c207903001080c10082c1c50300c41c000d6040380001e50140312001c0c82000b08081700ca040004c1191500603425000e542400b0050782005518a000360124007041e0705c40b404542010303424804000e80718407400fa0f5590340c502d4088550310303c680741d91055102c0d4000c80010001840c048003903e40c004003c45005030354 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 575700818 1250 575699568 575699587
    0xc070602102c2404021e010f0f0302040f15021002040609030b09010b12011505030307020904060e03040b180109050f030a06020306010c0b091513120c0201050405030a0308040b090a030e06 82
    0x2021030303000c409201c402c0000002c150810a84003100c0c044c138020385101c1c0210807801c009880c1840c080303505500040c0881c02c01e001c510b00c20032200d0070071241498054a803668806035180d81d603545170410811440e80100380704441e60100842100c81103850070640c00c0c0741c68240c000e0a00c1016110103040000c041000522180013035100d2244000001c1c1403402003d010482da500070000c0305408404404a4074000c50181340001c10b6801c0140e004081d0381d40c90f51103960385005018201d050140e544000d01c4045050398003007028180c650a01c80411800c00c0e4070b20001010004158411b43c000c44003001300c81419100072481000041e000325001d07a80e5140c180048540602083c0040c0100440c4800c0c401c0c41f00780415012180c1300201c1c810441a102c8800c550074948a601c03004000e20b051807a0342804c41d0042206c40001801410110b05195840010904094001d48102d0005401c64100070401c2204c04c02c041c1c00000100041c2a00c039141da40c040c0400c2d45100d0310910607032003c1102480e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 575702068 1250 575700818 575700823
    0x307110f2d060a1a12030702121c0c0605070c031d0102031b011401060807020d0f120e0c010f020309010203160206090604080a11030d0906051e0c070602102c 69
    0x70030409504071070355450480e1090b0020240003081c10710070420b041303108240f8a8801145074585070008059490301d2103503030800203140e0080c08000c034035000d07140140b1710b4032841260003410703a5074645910310304003006c0c80c1100444030003d141105100d11781c81c000010a50240301c44039010800458007540606400040c1d20b9401924407007040d10ba40d503100b0440080d0103401582a1050340c070200042a41c80340302c16100710104136881740059001d14002a055442007042080304903942c05d200b030b041000400d00006440c01d0900907055640440c040307aa165031320441c11b000984507880590b0070604c1c0140001d4591180f102c44200b4024080340d05803d6540b44c0040752500c1308014100d035030f40c95840146039140c0d58003070000d90704500c64134a82441c0d41004100c2c0d060015450303483c170b00c079181071601c10780d100e800001c089050f5503a96a5848c860780c0085000302402444040104690703441c042c0000d142003900001c0340701e00c90030314070241403030b400032800164481c2454032034180f1061003480c05403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 575703318 1250 575702068 575702143
    0x305120702010f1a150403020f09072f1b130f1d062409010b1c0c1107060203040f050409082b0f1e240b0307110f 50
    0xd507000d1134903032004450071105842c9220980140c400900c1c0d164400c20a600398003803440060b40064010210141c5440d01441d401e80c03050071400e01c00400c1051008103594140b141010680b101408483e20b0038842e002c01030703e07400c60b61441c06030280300c03840030205120722400654160460348548081c1d61580d581d400601c0c03405040240701103811a5401526501d050903100c080c4582102041500c00c842c050b8204291040080d1080c2ea8992a00b900d09180f91f01000030b040000420300c0104e000c01309030b40980099901c241c1e6806603508000301d05e081c2800c0030341c3e202d501554000c12042007212182c8126a0840b181107030b0010b00c5078032508048019202d00c105003c0d01d01100030301c5c7c0210316810710308414002d01e0924100036882407202e512007111001d40901f112489025808840c0300429000350b10000c440c480480600c84082c40b070304505040c41e800202d441e00020040081c2c60307a024051100161030039000f0a01010340c00030301c64a5000d01c0c2068094260b00b1062440c240b0398142006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 575704568 1250 575703318 575703341
    0x50415050a180b1501080405190f080d0b01091d06040c09031704060306060c051515060c030d0f0506100c0303060e01060f030c0509030706120e0d2109030512070201 72
    0x85188078020310340f41103da1402c45640c00510700782d5030302e040a5440754035444d10860b444802000045007400d00d00e106071103090f104580d030b490b4403d40d00c0b000880d054007800c402c03664003070081078140300c041c000740c10016950852214a0032a8143c1e015544036244850303044070040d01c00003000c0451100499950f41c4a4101912100c3c0100b060380d41492401700070411945075540801099488a4086560032200b10300039140d030380180800d1121110030380c84150400c4261001044400c18100410281e4012224450b015000411041e42d40d0600d800f6000c24002241001c100f6403909800113040d06200060810800ca004d039000c80c1010300980c4460040c012682805806696503080100141e034a2040070000a040c003400e2000c2c280110305581da0000002d002e0f2083e1030501004071500365800c08005100c0703413031f07429540c0c4205090080000008596a0708144a020840c20116a80018840c2d109041ca498100b9002c20392140c155290800c2c4002103107415241c03110308901400085801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 575705818 1250 575704568 575704601
    0x405090705030f0105060a0f0806030a0501150e1005030a12030e010504110f01140a050708190201051b0708040e04021f02030306030d0e090a1521060b04050415050a 72
    0x2031110850300709019520800d544800d010250380c8480a0000700d004402c0e881c4042050040403030b0b8400d00444880d41d0200c3c000d811209c401c002c94980307030300b914140c5031152a40600c182c002d0020703594141c0e1169100781d140d0300e00c0d0720561404000c603030303140c40409001c1e1541401c085141d00f11842500482d0303070814401d0090000c2d0130907007803120b0700640800f00d03070b0b228407a01e00c4405030a50084500040526400032010305151000000399070076840310400f2203011f40b0811205003410100d10290707000300025070000640385081e60b00c60301f2414504030b000740c0301d0700140142800600d80344100c405660310b21040c00441d03200da1000c24040340020007107000d407581880407807404903400409507200d500114200c459543c1400e0050341d110341a501c860303400c2030f103010000345810020382040810004c00d00c0500401507441303a804109814040041000384d4031700e103483c0f051081d00d014100d80c1c40320440e4200001d041c40e941e505032082c0710760101c4200d107031035400051030b00801d9130041e1700da18280c605 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 575707068 1250 575705818 575705821
    0x3010b100c0507030c08010c080105040507081b070219080c030313291b0c06120112050a140d170112060923030706060e0f0c0304111005122d0606040509 67
    0x2040d0740a80348004c0d00030005080c0e827000040354905402124014000e030f480d1069103448990808145444569002c3c1c0f0080c8208040001a1200d141c1c154103480c642e0003a07180c103400d00045e40d0802100303400d1244079a009014451140c00c183d02170804640c00c1000090004103075a00e2502400a00e00303400d1002030000c501c1190034012118800703c040d40c07800c26110201a104100b01550090b150384460710103018005001713400044100d500ea5500500440701030403501c2c1d59500380c0e10340900001501f130300020942d551607500400e551070710050966001400350304101c0c9503106403449110181c000d94840b10100280a100800310303403107514100038040b010450640380f81d07803940b0004003150100c0c03420b180022003050309000303035010b022185c4402d42c0b5503c3e001c42440c40c940020700140c603111302c40d40c4001080e66078903000d02c0c01c0c0301c0b00c1d403190381e201c10441c0c4070528070034001040300d0310500c01c00144a80c11180c030050407140140d50842c1181035100c1c540841c01d64019904429000700ba03840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 575708318 1250 575707068 575707079
    0xa03060e01020c070e092e051e0a060303141b0f030a1b32011b030524190504050408030103150e0c0607030309050718060503010b100c0507030c 63
    0x4000b4403c84000ca002c0f5090141d07a0210659105400c0b121503046412103003408016004661841880b041d0b51811380040c1380d0100014022103106032100740700c0d2401e402082080302040102a5405810705204004541c60358502601502010340a08007500001583d99401004603046d500292248801c9a045940c1c500318550343c2c1d806181c40c4008207550038412880c45060100c0e242149901c20845201402c41e112821024042c80046140c25104240d11140c104002d100e403190010240c13410740d4154080b290301804460300038180711148280480d0085c0b1410001210002808055500c0d400c00c2842c800b103481004020b070400c03a070040c02e02c410700080c8014940036505032401802e010844510140d0700c0c60481e0f9100404111035000314000030300e07a28042d0003620406029050214031040726544280c01c21015802200c0c4c0701124ad4402842c17064680f0800001e400c06400810280e04180e001400071000565400208076090760540f08202007400040029030784018420019501c1e40e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 575709568 1250 575708318 575708321
    0x80c0105010f09020a0e2106040b0624070201050f1207080a0e0c0306070e0301021201080703210f0e18040605091c0503010e0702011416030510210303060b0a080f0603120d0b0a03060e01 81
    0x182e80bc241b048120000724860b00b2411082c007090190108101c0786800c4542c0d005540e0b640000d41d60718000801444800c8244803403403007882c420b00c080d503254000d034503181400e40c007142e154010b015403903409024104065100000d103560480c0003814003e094481401c000790180c45104401088665000d0001481180020303004054a11070712015049c141e8000140403058004152400014030b29001b00c0402ca008080700001843c0107000c01603a010340c9424141070250a40e002c0703800903518410004039540501c81d6a188004410300018403144d141c10003082400b040c0245d070740012042001c500354038002d501c02051080c4250f03080304107140c191600507044201d403440b0790109041200040c5002a401c09038016503240000b861380d088401c440c41c1c1c5110301801800c0703003031655595021908400c0000600504505569005101c0c9042507910020b1940682400e010754000c0d480c0311280001142904c038441000d078000100c0e0100e050000c0c61040c140c0d8800380c1001c4c5051101202141e06 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 575710818 1250 575709568 575709571
    0x1020903030a17011a040605030c070c061206171e030705010606080109051f1203140d0f230f0403021c0504091407050d02090301020403080c0105010f09020a0e2106040b 74
    0x19200c21030302503aa00d000c03425640c1d21814038003070f03113213006c10040c06001d00403009107800c00b80c003500d25410082c1b02d603110140c00000740c0007040400d0000e414619044030902940d009004036030782e05521014401c1080b40e850b01e18009400980c0c80440040d400e601040066409440d0004000e200396a520b0b400605a10000e004410309a420180042c441012151036441c40d0180c040601c030309186002e600c60307002d0441c503070110f04012400c201406c07908240400391030a11044000080c070600710080c02c074100c51105070f031103408503444850340102806100c0e00581c4072200e4000c0c800d00d40c0d5286000c0b03040a50602100340291410003081e2803440e445006082901c1c40c5103010000c80c0e1142205010383c2404031012000514100543c10310f002c040d40251100580240c0094201134503036442081d943c06c440305840d2203a6462004000f01d090b00113040b80144038100c01189428210140206100320341c03041d142c0211200c004080280844400c108103070300c0102c0035102036040c649048804001c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 575712068 1250 575710818 575710847
    0x13090501050703021c2715060b0c0106080c0303090d080f0a0806010e1806041e051504200906090604080319140f18030a021c0203010510051804020301020903030a 71
    0xc444030030100f404921801901d0450403d0446d071646c0d030f0010082880c0c81c4003104030340c0d00607250a109802103290081c0700141c0207487c120750300c1e40000d150150850340154416a070031707800180b0380c000645010048903001f080642e01d480404074a1b081c0b40410f0312500d1030104c80c8580000d0b407020b005030300954503809600245d03115032f2010641800c00c221640c1050781201c80394280703030124815103443d80c08503040700c4202c0c0d200c030390782c100d0031441008841c1c08507a005d40c04180f50f1000292882d282c0b02c3c020b050210400610404800c3e80c410103001d006005040307005a000045601259603440c05440040c8920400c172681d960030304280c505032906c20a0350a02090040500103080314141c81680c0c00e80c2c016a547c0c40c20008a22200f844c0f072800030f201c0030307054041c25140101684903003854002c81640151010350380a0144141030071518001c0610382c00040c180000d010f507541300c400001403041d12601d2003c05480b54000280203101d50200749905220024080c070700142c000d46071800074103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 575713318 1250 575712068 575712097
    0x90a2901030f020a080a0b012616021207030507020301061214010c1d0f040608030c0706020601050d020d03110111160606050603041119050315011e050f1309050105070302 75
    0x503082d0400e800d9000b2a01020701040581c00002e20242e82c030750042c03462890502d40040d61001c000641403040c10500300f01028900400f0030042c1d040c100701100003c100302440280306000c12004040f10b280a19000101002000100b0b0700655600350071840142a201c00034114041c06480c1c030444450f001c0c2001c0c91070303500f42043c0760500b40c0608610076803020540d0309502e5081e040d4081008500c0708280c221f900c2a600e100200d0308601c10805070a5000080005004c02410039402a10f07080050703100c5c0e44207410041d901d90058a4007584000748960501341000500607829609015000004401c1004c13003000c10f02d001a102080440a00d4900a0804208c401d4548041c4080c80c80102d5000d0700d1924814001034035400d01c5d1503081c41d40c3c49242d07d08601c040e180c1000a0a040c0800701c194a01018580184901401c074044004076480c0b0360f0515021030b2410b804105900000d42d0300e90312407031300c0001c1c055010059030095900954004000c01803490034820240094014101400003403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 575714568 1250 575713318 575713331
    0x32001110c0604180f050112030801140a15021905011b05030c07020d02060c060a05150906010c0303050601200d3b0f090708042f090a290103 62
    0xc010810041400d406000e080c41c0a0800715142da02041e181d44000c4900d80d500442c1480c0183d40c4200341c0031b00101ca8655235150740f00c0c14010700b0100c068026600040f0b4080c7d17599010760340c10701428115644108c000b01c00c403074044016810204040086031500140000a0080100640c0f15101c0007000c04c0018007021f107080f1080360b90340012601052401000c000070009498141c502c1552548001e12091621450b4090f05003003540c160365280c081600c56041c080c03103001064500c1c035111010785020030030b45880000240403500345200541456940e00c00700704564443e070603014501d030b1011a004405441b400c103166490265907000e00008680d410f4a1441e400e04c902e441420304440d00d204c00020034041100507038080044a002e900880070034240041d9103881e02d050744180029201c81c8401c0c503103810440300e030309410300c45120b07000b00c022828030401002e01d546460b03204c010784808810785c0d5030720340742c2c8010280b030b00101c010503e651101c002c500c00d90310b4411543c070798207a9041c0700a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 575715818 1250 575714568 575714597
    0x509090f01080f0f300412020a06110606040c0908030412060e0303060a0e09150906040b0601020c10030e19081b0c09010302190e01060522030c030b10032001 69
    0x196a02d08803810350b6a0013400c0070060b01c2d0160305d0220781c41d0115050030300c200c4460031038080c055070043e4411854220003505680c01c0d46410481d2000410a41c02d1220301c00603805001a244c8500801c1e6510646d80c0b0761034140320b503107c0c400720009000b200303040ba582c80b81c840341d00720036000e100b65048500320308101c0903442c50b110100503a03000386006030080402c142089031417624064000d00c09402480b464070700e136000c151a207074428080c600c001c0251034103082c1402c1c02944084018041810340d07000030301312901c81d00c589000d240e424296140014113121601003450070205595000341a062903a0841d4043c00044801840301001800b1101c1a0344901000940c45512240381c0d241d00041e001c2c01000582031148105000b030403000c66001c21203403210f9200003000800e0304094000342e00070400c6050203100304400c540003a2503c0c2103030030151035507880e18680c0c4100d00000b00801a0240410300700400e2040745405194401c01083d1030000342c0ca0030030b200b18108d40d19103000078248040c4020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 575717068 1250 575715818 575715823
    0x200604260d200328170114040b0a1e0e07080c04090f0207060c050a02100b030c04020c0a0c030b1501031b20062a0a09060f0509090f01080f 61
    0x100350006071241042000d07044020310b49401c0007141c908403800104401e000c505909010001c2c00d040700200303250034501d1034030020840c440407094550103211402c0140003803400741c00d03001c0041c901214040750580b41c00012540c006c4040d0300009008282c4d01d00030301d40d000500c503580c090718528000784000e541c5483c82220404030990302c1c0b2884c1181004140440c594580020304040b829481c050302d441410380d20b040840340101e80b03036000a103000c243c040e001e51b810310156030f80100d521800d0015182e814000380d20b4a0440c030342d0070300c03590380040c280c1c5a0420602c198202c00c3c0d0083d40c03010b000b907640d050501ca0302504840c40c6403a04045001010298080d00c2001c0b406403101401007244200e03680b050351850503601c0c00288041d03900880800b808000c20925200f05151b180c041908640c620040b0049070300794a28141c046401d21190f9a0b440c1d1040098080f1200b031314141d100080014015116071285042081c2c20041c071800704401e0002d402841c80c12140c10038100c0c4c402024290900e0f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 575718318 1250 575717068 575717083
    0x628180b01141617031906080111181513240807030b0604050a0f050f0102030a0219240518010b0d0803060310060e07030e070501090320060426 63
    0x1450128203102e403608514825010220952240d002501481c03e00440004217800c100c400c884054100240002900402d02910b4010000078000b400400c000110400c15405907151102003101031030f1100d0351680d102e402441502c1080c0700400e50715442c4034030280c590300c1d25001c0c0000d00c10f2100705c0c04c1c020580600510703044121070758503110b0a1b00c900030100c0c081c1c81141d0b40360390310450a10001c509176841425520040110403403d80b015454101405140000c4241d0241550414031103000d540b50040b80305001d21400180c00003d410042c03402064034465901401c0c0c80d840300000c40c409203103943c4d2020f030041d141c8803402d8036a6008141c0e02402da426a4404540010140b1074400010314414060341d0480801829104103142508002d81256055030000d0750041c8120b040c02160350b0584030b50303181084c0542c0038012050500001802540c507034403004024540d410503101e00c81c1e0700911000108003000741400c0e0380d190380d086001c0280c3c03541103132b07180140045009200c2c0d02c0000600359 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575719424 1106 575718318 575718347
    0x403121101020f0d0509060f04081308101e110f1b0109050105040213020a0e010c050a0218072a080304050a061803030f050f0628180b01 60
    0x20800c1d1240902031800170b81144048c0311103150030030619540b29800c906069030740c1e2044a0a5203024042c0c0c2d000f40b4031350060008540301d070030a680203003042182c0c0703c408a00c040d1004c2d40ca04101e0b0100140b0b42c4000d2810480e403496401724001500c41d02800810a200058200d185a829130b06842c0080310301e80d55803403c02c0f007107261011702c0f105108060f9400718100100b00401078501c0780c540d001981400118000001040070401c2000107081c2c0c09031001d0018030002c2d041e0021040d041c2c4940c1c0201c2d9095800c814000c18010380c5400c40c5440c0a0700400c242100d0319442035980c0041e000352070500071206a07102244143c050920011015000800140a2800d008040380c81070070028041900b0710050000c2511034007000c07a000402115044600c0840140175100d20300d2500320144051003414000400022412401846e80380c00342040c4020600c00b00111481c00161204 = true := by decide +kernel

theorem cover : BRFrame.Cov 575539568 575719424 := by
  have h0 := BRFrame.cov_init 575539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575539568 ≤ n) (h2 : n < 575719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
