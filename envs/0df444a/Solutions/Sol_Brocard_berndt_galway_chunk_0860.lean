-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0860
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:13:24.696846+00:00
-- url     : https://prove2.me/submissions/0f279dce-8378-425d-9144-65a828324044

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 154496402 ≤ n < 154676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 154497652 1250 154496402 154496411
    0x302070803190b0d0b06120319031d060405030406051606060b18010e100807050c07060905090606090a05040b0d05060408030405070b0703020a0611040b160201021213090b0111030a0201 81
    0x1400070a8411030203c580c0441e013050210a280e0f40303001c00070200408151040c14040549110618184100d070340c5001003042481b800b10300030601034010030201090303c4d10b004011600c100040400a0101d000d90b4000008508042c61301030f0454240e4803c0c480306545040f00c680542c006551401030001402000d40c00a44507083c0c1c01591803480b131703014001d42c10010000343c0000f0a807285104002d03000c10f503151002c0c03540c0d52880c4c00c2d200703440707103800144062198200009506520020030707820b4034400c0790304803116100d44080004074040d50115a61000201d401044585882ea02403000c1c0d080103011103103a0b40440d1200360611008890559154030000200401c01000b8480c040280c041404030b2400c015440e01d00950394000c64400510555807a40d08043c0640c4074001d54008120507802d00e46c1e9544503582401e181024504128050320031403e03d80b4403040c2410a40d2000d0002c820405031251804034a50040c100d80d0460506000f01c039003094003507102c140000e0984070055000030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 154498902 1250 154497652 154497691
    0x20f0301050a06031b0506030a02030604020918101d0628090203041b0e0a05060a0f15030f0b06120c07020d0503180411030a05040317280e0a030c030302070803 70
    0x1149100c1603100f964045c10340700300340318568031352080d2a0014500c0c0300c01602c3c0d0303036603a01040080c440c2042441d401408540c0344100b01e81e24480240c450505d440b0464441a6210702010960301c0ca030708440e0000c40307884000380c26820011006000384100d102500107c25522003454201904d5400440310182c0000c10441480890001802c0190700c80016030840c900d0b00380780c03809184010f4800070010341c850010070285c0c2c1c0c400103880007a10500006621199552407441000458540f1010100c0d0412800c0400000540310704003440e0400307402940351441413802e0310401c4100600c1c00e00b07402010b0142d0703030141e10340c0340c8500c0e0804e1081d0010b50b0740301142101e032200ca01280c00a117100d01c1c10902000e00e0042c01e1803ea83e0440d03031080c4049401c0e201e0b450b054800070108880340c00741d100084200801581001619110802e81c0305035641c098802c0c84c40c1c03c0c242c5800c42c5000d8444c3d0b104001450000b4400d80294620034007900d00181005442d5030384684540c010387d514140c00c158801b480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 154500152 1250 154498902 154498913
    0x2071e05150304110d050c040c0512100f05040c030e100608190f0609140604060c110303010f0303231821070501030506060f0d0e070f03030813020f0301050a0603 71
    0x304801d40304020003801c518107982d50801c1c0da40892081030040d052146900108001041200e10810004005200409039628001e0441e0810980310901038204e40100700c1c0306205408070820f48298100700c0c058a0309003418007019000003042801051380d20b40203100b0101e4248648551001401d00100f203180c40c11a81d80c1c90441c0c500300700e013407061030080350000140d65008907480c7c0f107030303c5035012440301c0c00d41c2031540000d85a07603238403002070150300c080108200302e5602c21020b001c16500c600c0088201a107825079640000d01030702c1160012000c003400824003540c0800440c50100d0045c003501030302511041c0c07054116655007044100c1954400b005468486000d020b4a03440310202c0010b02d440f0900c0b07951b500c0329840f03542d040c19075030804980c180c2ca42c0c804940201e070400354600d0341d500c0c061000c030000301503840307400740d50b07014110300410140501c0310400200c9801d070381e400b06a52940c582c1450700c0408821704a0b40004500d000310110780f42800780a00c61100c0d1800012407030302d9410300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 154501402 1250 154500152 154500169
    0x14091c020a06090b01240f1404080d0804060f0e15060418030921020f01030515120f0606220b030a020a08010b03010c050c070e06040b060f03070e01090f06050a02071e05 74
    0x4c48030001a4990f0441203130344411811f0303202041345030400c51040c420901191510030f58100702c8545c007400d0030484015420081c045c0c002c6d417090100300000026001458111001242040001d8100c40c0d00b184040321040c0c511500000300410008a5200300d090b0018100b6440c20100c0c04202005010454204011408900d14200c031003110164100d0ba400a103411000309280c50505640d80040f07407841b410380c55505140d0320094800422071010748000c5540f03507003846203641c1e2485000c00007444d40c00c02d80c14010a10702d0b10406045907140c000b01ea207000c1e05000910540501c02d001e120f8000d071743c0c1e1844400c02040c0d40000022195983c2090509462081c0044428032004104403040c607000020f443c81180e262060004a6481c1c4200190140881200540d404200070802c1c4100340c42e00c0d802540542d03505d498116502491a0065840e00f00700c4c401d4102210985d5070401c00c0358003d10041c2140b0403188196002151180700c10150910803400e01c00d890044030b8014052070030420207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 154502652 1250 154501402 154501439
    0x7140307210308010501170c03090c0a0b250f021302070f1a1308030115030b060a0203090a09110d0f09020307030606060e040e0601060c030c050d020309010314091c020a06090b01 78
    0x7803180c030461801501400047c40900030250b00f0380e000000030040203051103407013000301c03008141085099903082041d40c1c68009020040013a0000317079440440c2141088003c00c0f2540c4901c0c074201c0002107408126004a105410100f0150208007646c0015420040381c48040c0c4152200c1f0070891070607007070320000e00e0002e01c082d01c1c0030340c204c845101044010007030741e04440c1200003440030b491010760200c010b0041030f00c0d1640c00c060301007100400704d9008005003100d10801c3d55141c00055440d02690300342c50305030441c0c520b8190108400501d048217500140c60504503540040350706e4805074003003890044254825110180c0d42e40041c000d03664000600300d0341c000125010300c2000c030340d022507545681061080300144680605110101401444041f0030250820165030102c4540c000107512507010068044c0043e140240310003c3e40c0c0e180c13101601032544900100381d9107102c2e4010002d54262480300310154032480301c0c14400074a450152035601840ba120300880c551400f5031543e012003180e80c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 154503902 1250 154502652 154502657
    0x903080a0c0807140915190e27040f02121006090212062407060203060f0409050d0c03120906021e04360f02071407060207140307210308010501 63
    0xd2010050f0700242490a026501140d107a882e1030b240d00041580801c0101194404804104e800c203040124020804444062300c1c0e240014814504100340407800d4010340c050100c03031480c0541c500b50701540860b8824400c60b81a01e140d2059000695040b259602a01e51948040070300c1c5241d810301c0c02010001c03c0640e0040d400c0c0703403848414200300c0800a1010f0300070360310000c10300d40307081c0001d5210360014200c045080c0e9600c56030a00310b01951040340c015000d01c00c841c4c3c1098060410b48107415907240c00101514041c0381d420000c0b204210000c4050781006069445a030b4079001c144107110180b8411100107a03510b0b6400c10f0524491903204e948807003508180000c0140281d0324a0000050320310003a42060b0360f00340d491040c01d503494846492011461b10721040c030700194940c018051075019440c6049207500d21130b101c1c2d5580d035060050000503008200f04024100d644040e040036000c0040642d14001c6d11a040c0340314401c1c03000d000a01001c81e1440d64018141c00c0207545005d03110a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 154505152 1250 154503902 154503917
    0x9060c0a05010f02031e0c121303080603070302060403030e01110d020a06270b0a0f1a0111062e080f070f09050c030f04060e06090d020706080f0402041508010903080a0c 74
    0x581d05d6615214030000b46d0820040d400d000540c4000c640003111303c0751905c0b480880c0103007006540c0d00404103511fa4110302003000c2101003003c514002503074004490b4018951481c0c281141d8040f6100010503540d00e044c0072401d03c0380c0d035a03044140020b920003d15036000307016a00381d5041000550300143d400c1160901000c4410480400b0b211000954503001480110380d61500304524000340b112103400001e061505d012608003030344664841b07180c0c0300240d850a00c01c40b0000d41160f1140010744880499102c83d854503034048251780c0c442909648600088440d80365101c0002d42049002d03c4e4008640e0003500b004d1040d03c0b8241080e00180c48040800c00180c0341800a0105912000e44038010150038440000c040101542241c119040c22a09640541c1404601590348815080001026004083c00450302d18413a031101c0e485141d2450903a02640c49030b4080c0402011a82d40c001103c500c0d00e0700100d5032042c03d003e280400c80c401d40c0c90b61218036051203044121040c0b483e0400410100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 154506402 1250 154505152 154505161
    0x303272409100614010503060d0606090204060801080c18090c03031305100c050307080304290108121809130507060c0309060e1305061c030503060f0405040503040b0a020309060c0a05010f0203 84
    0xd810745000200080c06d003e0b660780c60300c8000a01180ba0240024122400c000e0041402c1107a900a00200c0301e503619000c0d40340c0d89a12880d074441d1600000c0c81c0e000f480509a1031115540c003440240c0203001030013603a190b019480e01003130440e801444c0038002901e00003000c0085040540c0700c03242040780741c0f801e01c1036540b0558a8a80300d114444010301644400f00c00b29091204030b041c1d001c2a01c0342e040203100450500d441188040c20240300f043c1140c0102c6200311210001c00302254070b0710540c82287c4040d030f6451360400c02080800f8100780c80200003002c0003000620308020200180455840c4e20310810103502d801002c12149411038001c00000b00c52014550315280c02c0180489250000441c0356602c9001003204c5070103c0208840c80e03600d1109520500d0b030888025801130f0400d42c1c1d141103a518400501054580030780f4000c10302d03801007208001004084018010484081c07040da4a490b41090001d0459046920f801e0071913001028100b04202c000d206e04401c0048803002582145003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 154507652 1250 154506402 154506419
    0x8090607032406030509100608210c0105070206090c100e10030f11040303110a0206030105120a020301061401030e011a010c020f040c1e0203032724091006 68
    0x50310010905840b01c114001c003098140d000c4081e44040102c00d40010b6480c0d4008000c0c00b03040d1055803103030241c0104035007203d0290003240150780003000205181c048010f80610205018101541640c00522030540154000e026450080050364000d002e24108020000d0401030009241807082e96801c946241854100c070921248050032211820b9150407a1400e901403c8200d801144c20f40c60a03d8820491030042c0c050010b50303000b5602d00c4041e0481c3c0e020b2035954816407001941c401410300040100380741400402003481c802070196150b40c0600d0780842c7c00d50301c803030300300000c0484084101800355a0503c41d1181d0404454001d004142c1e0103e180e0b0201070b03011072003c0c10040508094415510f9241d255014418068030410800198510044c28901001d64100c043c41040281e44050380c80041174900942407440c0c1080e00701c6104450000c03c030001e0100c281030b0b000310192442c01d041400c20211282c114100d111020b80b030960501803c003c848408142e5661800380280710400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 154508902 1250 154507652 154507663
    0x3081e271008073504050304080d090e0c070c0b030112120e01140a020a05030c0a0515150103090c1706070e010c0b0a0f020408070b0408060106080106080f07050405030a0309030c05010809 82
    0x14001011050f141c40c40014040544d4901105103000c600141031000b001000001403045034203103012b41e4403034924904103c030f00f4201886440b02e60351008000c40e804040447c01000e4517071150540180c1d0300e5981c01c0310240c0b134200f40c7c002c40381c51b61031802e0002070004110820b096101c05d03150006401d641c010010300044100c180303600c0b40960101d040a100c07802004030b00c030015002002c0343d0303c0f8220401c0c0955202c8400c4c00c11512805805440d56440301c10084c07250064410200b030281c07482120004500130000d20b00c2c191491801000c0020f40001104042d852481515000d4807452800e5600a0f2100701c904110300d040041510008002c00c1761031514030340098005030b000c0340c0031190031000c901a000e40c1e000240c450241c81400140720796020000c008862501c01501c070a6a81d820301512199000d11516020403c40c1e40014154044a440d41e82d01c540b440c24020708003031b105c8001c6071074402c5403902207004c980f411100380240710250300380c2801848246030185591610000c4603171640b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 154510152 1250 154508902 154508927
    0xd0b211c0e030a240905070f15080f0703150e0f010e150d210206040b01090c08070e040603060515031c0e0111010e0a081c0603081e27100807 62
    0x480ca1040012890040c0c01c58482160944c80e2050050a50307a040c00c9071584070703d20034a44100c6401c3c6000402c15200c1103143c0d1107200e00d03124900345503203440302c0c0f00341c160000784030a003019600d0f907240016090320340d5242d0241c0a480800ca03035603d403142c1d2402c80201c041e0042c0c02031041d1141000381401e6600916450f80c070301600c2640c4510403600d02680190312402951642c02130458598402c00d500003205407007140a0b542a0702e0990303a03881000112464002000c0c0025003000014141e00d004882000c0303140c1000d0300010728580d0341d4070790000700e5200355035402c099140c0c1d071000b00d4246003c2080e205014111940100041da0408026001580310800507040c044d50a0741c1c0c10ba4520294000240440036000760b810004480c030b0680003d5100c0e044d00f802c0a025809a01c00c48144e07481b40401350380d400040d007481c0501c0c0032943da14081145180725104031082264220402211020740800f0484030740309181040c084081215107400d0340c407860104080c0104200b096580141054080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 154511402 1250 154510152 154510163
    0x804050607082d041e0510020a02100302030f0103030804030513090b0406170307020d0221032503080a050a0e0a2003030a05160201050702040c0e0f150d0b211c0e030a 73
    0x11082d4002050440051940c0034681c005221f003202481c0c55004204121502d01c00c50300000408458142603049010a41d401b032850354040005100090040601d1f0390003c2c040c4c00c040d82070502014101007001881d4100071141c580302d000c03000440c1000c0c011500a801912904072038002d8024159559005480c000380c03081710074090000654a40310b0540f40002501522503032819560200701e540c80c0d0116202818410317424180025031150701c80840c100d640e06a583d41c9050314ad08000034007402c0c0203004071107540d070f40c2c0e001c520700c9420030800d045000d84110250201741d06400100302e0700f05a03c51040e40241c1041061400c1b0720ba001d003c40f040300c000245034140120060004944c5400f401c2c40c002d4006140c0304403810700d541c10000c130001502d4226040d10028002006000c2d503c44c000c00944000901442a41c00802441d0448295450041d010310b40b0038181d070381402e01a125900d44440942c02030000c000d145c6021403020180780304e1a040c02c804c00403240e03000c2031b6650b000300306c080c15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 154512652 1250 154511402 154511429
    0xc080705040617070e060705010204140604050f040f2c12030603060c0c032104021203250f230601090605010f0e0307050603100f0e090a030c0804050607082d04 70
    0x30f6000781d52021800c10090301b680e490340300070b280c028001c1d40a0300400c02ca80d50020510112031603c01e081b43c5c00d030340e03001e00003030206082041400058a8003890b040c6506485a05101000326403444840780381c9152801c404c01c1c4c0d0b12841d40a418007014403280f41c40300000300100034207900c2c0000d01d681c00600001c0d103299070f00200075055013580104400100386640043c0c2221807240c41c080c0c018001ca008960040a003040c26560503681d10400c40303281206034041d5032000c0b000e900b42c01e1444e80a40074210103203c3c5090380d07072a20201c08400500080d0004d140c0700200702c1001c00c120045c050103a44a0070842d03241001c001801d007030300700031411040000c1d00c2c2300003549480c1404024010038018120315268104104041d4054806004100c003402802c0d0300000c1c824000b000f200d00540c0d8220151082c40001d840c1114040306095003524030100c100400941511140024850107018912060b103c03d010349018507804c01940850400e0b100600034010a101100c0403a01140d00e054500c1c82c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 154513902 1250 154512652 154512661
    0x1104030b06061305010c08071502190e0f2e0503040309080106031a0c0d05040804150309080915041203020106090b0f010906050a020c040207060f0c050408060f07120f0c080705040617 80
    0x141f81c1d01c10140014a1801c2d0540c15801645d16500904803030503900c05201c400316001d04080316401024110103500c401c201c101c105250401c1000070b03041c071039001ca00b441034904083c2d41200b1103841c0c001202c0007490000412041c9588601e2002c00360508000910039503280d6219294507084200900c920841c881e404a00303440c0d00301003110002200c2c51f109000c00d1400d0308000b01150042d22461003600c040b000e1203500c0c24400e04c03a10803555445000107090104100521040621580c0c108a00b40010803001c41c1145c003854074424403074402c1e40041055030501e0240401d80d8002a4200d0040804050740c152a82e0409070303003004ea855174549140c4075000b80d8001c03031070582504c410503046840080d0f004244400f80d0070100001781c401606000e52042000201e601d449588900c034256040180440d2070003040d8403004c0e03005411071a08488031203854110008450b90b4541d83ea0043d07075601420507460750040180f5600001c036040c03842c10140781000190103c2c602c1e01402d940d0407000400039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 154515152 1250 154513902 154513913
    0x303140403050a1b0b04230d080304150f0b0f0907213606050601090f09020304050c100f1b050307031205100605160212011104030b06061305010c 64
    0x140d00071030b0481c04a61050311107041c080b400c82e0800d40a484079070a010b0740400ca200c030036002c44007141c40c02a00007e142e240d0881c0980702001d40c208441d80300c400c0381c10207404a4004d9014600643c0240c440c1440001f4680ca003000b00d44c16180c0d0300d440e05081001c0c0401982d248406c00e1850042030310480c4050b41ca0701c4080f505041c10094007111b40300b0b8041c07201000700d402c0d8044d0401c8825030201e10030000703884841300000442d81001d40c5242d000384000000050144e008a80c0041043c182034004580b284640f00e00f0955503004884031582c04410803060040821000715100c0f41a04c40100c44134030080c00811340081c0c40b2003202445148401c0065980603e8010840241c1150650391941d0007850000e00c174003448011030440c6803c00000c1000285004803176822600340742c0713450785849030080c00421000344035101030340d02058414500d4030740c0100b1b00601001c41c010b060003954690951420080a01b800307014a80100c400f8407000f03c02242201d60b038400d6170741c2420a01414000e900e1b08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 154516402 1250 154515152 154515157
    0x302060d0f050a02071a010317070602040f12050d08040b060616021203120c1603030c0201020c010f050105010f030504081b0319030c09170709150e0408030604050619030314 76
    0xc40c01c451400b010032445403e0703503025001340d6114154000e16050240341c105025082800041c0988135000509000d90040303a0042144500c00d900140c101587c1c2c0100000350b008940c0212041c51002002ca81040804e22600e008900d15040002143c141030b26440f125000c01080a4010900010001d03c1d82c1d4542d140740740410781c0208100d5203003455420b280e440e50412902c85440c0000310000c215001918806d440c0c009200d03850a0a1070309a0f40c40071006010203109100c1555800c00041810a4088c043d20312000c0c0101400314003549400001880000004400e90405142c9014000080d41203030495044441c0d0010b40c98400c00028942820b61040000743c0741c400050b0101d40d4802505a0058a02080d0030744413070305255070700d0000441c045038400b1191100d410441c0107004500b1198880031b895001d000403103000e5910b65000d5000c0c0c82d42900d0603256184040708009403450725011f95980140e054a000502d290300e81c19031070752a030060000409201c1c42000a10400003403805 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 154517652 1250 154516402 154516421
    0x201020c0102160203010605150904092a030516080a0807051207050a0c090c0c061e060303021507090308120a15030f06110307140f04080105191a09010302060d 70
    0x3196144103940e00f6a9400300c149004038001d50810800103041d240c07001c00c0b0b241c3d941c0000704032460b046c514800c010050030400d030704880c44101c5003c20484645100368406c50006181c5d8400760490035418007d1814001c28403c914001810301c09200107100400c000040950005e0282d442d051075103082c6007000120640350303501c54804242c80090180000f81d4954117409402c10f4100e10351210491f000b601c40c80d41400c00030500060350b00001074400da0004202038140e1007500b84100c600d18200782a90f001e540103800582c001c0c3c40324246083c000701d009400100d1030030803c2d08c2510715645c013203940c0611a10166004541000598114002c2d008000d1280041117220041904c83c07820309080d425245058442f82d18060356420031500d0070301141e00440d0551100500805201c07400c0b4407650065000e91400c40c414480010074000034040d01c0d000c0c0d8160121000302c1c1c0b454405800031a42c0c40440070314a8a080d041c4260251102c0e07440506482e01603440e25a00e600740c2044c0400f420403e034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 154518902 1250 154517652 154517677
    0x30405030a030b0103090c170106031502070c05031606050c1906060e073b090403090e09060c16210e01030b0609030c1215070203070606081912020102 66
    0x4110422201100401e045440c0e9101007049401e450011002c0300c0c01c10100414001c54088140241c1c1c9208207003000300d1030304c030001142ca55229034400c00648100d000328102150042a40000c011582280c1d8010b80825002056200c895075411840f100e007a108010500c0000101d0030944c040511030340c5428010102c1c0010210340c01d16207040204a80d10400b032034454504049180c1c02d01ca010084403003000310b40d0054100341940a0410619420300c880e0107100075581780c06000e600d42c1005548075501a88504c1031191600000707887e152001060f407080d0b41c02500c10840200164030030344020290703195001030384c1c3c41c2178945070304090030f03002008007200c0d07021684600207a031148015600c00020b0b6401d100444070706060080c5400303400070ba80d525812403440d030070f41810300e181009004041394086840000c0122681d0b07c5001040e00d000006800c0060b500040c80954016980140030000062114414a80d00071038100150074005000051000c01c0c00c2c1164400d4044c0c80403a030004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 154520152 1250 154518902 154518907
    0x38090a030c0602100c02060403021b0301060f150305090f07030f0807021305011802090319030c02060a020a051b0904020d0c08011113060c05120d020403060e030d06090e0d030e010e03 80
    0x2d00d40030f0b50314890601640416410800d01c001e80300d00c0840e4070b034011603041d001051264500490151300c1c1c41030030f01480c1c0540d49c0341000a01550300c055040f000342945811300038a41000000103094940040a20b0940e030700010101c0445a8001000c074201c0303422040da150360459030314007070500e031090f03640c003a41c4076038800000384d4000442e038072550480324890740c0c2076980c0f00400030260030ba002d411a91549a001101400d180480403900c4180301c038440d141503041c0e030320705600143d6580c000d05074502c0180d10800542d006c200041182185008482400880101030000080d000b601e00620003402420300103210703410010350041c008081c00001c4001d100401402189100f070360401c3c0d008070718a81788003000140450060307103051b000e82e4010020b0100e541d4554031010140e4007242c203001381e003542007000201082c2240306a900d1602e034040034641d00c50b42c40742640142c3e1003540001200320303e40940d15010000c00601007107403224508000c030300c1c8246940c4040c01040038051114071070000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 154521402 1250 154520152 154520159
    0x30909070f03060e100b1308010606051c0513020f210a02180f2d0403200d021011120403050405030d030c050703050903011b050438090a030c 62
    0x9a00701c0203500080c2e500f000015074503481074134141e00696201d045518000c4040c00020480c40086c18041100d00d0110801a903805450342110040ea108000140b804140c14500a0582912010b000e2a5100600840c1801f460780e4002ca100e40c50b0080c0704401140c844c04958580390119a03980c060711482d00b211640c0d80017441d80710160034030100e110701e04070241c007600c0ca260340340042d0152950703a6480b03080c0d64405011300841002d9000c100b4445039131108201d9040205101148118400d594800525020300c0c0100e400090140c50340810f50401e10700e440b503981d400100080080c0c242d40c0042a9250741040700c01851140c015040d107072080701e108000c00e062304080240200c2d0003c0d0112103071000c00da901241103039080522030300014404c05c0003d001c2881040502271203503000303000095200d40005401e41e1480c0380c20610001c80d4010604010030103c62120a0940c10142040103a005099015603000740b4001d9982040000c0401c103003284d171701ca5184a2015541c084030020500d41c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 154522652 1250 154521402 154521407
    0x207090e2b0e06120a0c0c0f030306060912020f0f0a0305010207050c03060708070801060e1807030b040f0e030706050903090a090209030c0a05060a0c0302010213090f0605011b060b0303090907 84
    0x164120710801140c1c100034000c525040c420100c6110b4005500402ca441e00c614150b4005094220801401c000310f0402c4100481ca20700c054114052180d1000140030341303820400703040141168440000000e11070b011501603202d44544e555152021507000c2c038151030b00400600c010121344c201500c41c1d0301c00308064007001310018660196240c100c04984840d82e8481044500c100211090b00c00074906c10300400109000310b91002d00d4100080c12181c440400c0c80c6014481134007109c40c840000e8a913000040302d400d19120720300d02c0c2d118881c018010040745481c4640d8a01c1442c100034800b99403040000c581c90800d1003074170ada9080051140301020341c0c4000d51b00c00f079040012001d12034012203d4078800c62811200c2c81c000c40e0b201914150401072251010785a2041100041e0195502000a808094403614002000e4085100700107030005148040004440541d0406410b0026500d074100284041c1201e200910b039000b40d01054039940324000c04d00394000d01081c150846d88507014807856a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 154523902 1250 154522652 154522723
    0x40305070b07031b11070e01030c0e040807020d0b061201020a0516020a030803011e080109110d060f050c280206060d03032003010e09010b060a030b0a030804030b040311030405010207090e 82
    0x91207040306d00e800d890382e030b00441080c0c081c400100010070340b49080010714417441c5010b60040c064006c0c04d08004030342c0c001c910b445051400c211803040d0200100310162400c16030810401810b0402107007481d42d9a100640540b080d54445159100c5070b43d80b03e0110740d900e03200600510707071001204e5140e59558883c081c40c4a40d100f01d211150190080200b205d040500c10017483c19003058000d04907a03080003e0200c3e183e694039042e02d80c15220b1031000c91039071540c040d5a0003104003a2541c0e941e602401d800314446005020355000c40075040b03d244022990001d102070700440c040320440d8000b00145819030040070007204201485d4002c06902d1850b000d0b0030302441c100d0f02c00c510040c2d065510b001700c4900303c80d0b07401d00d040c0d489070342448580300c4c00d07120b0781c03200c41442006070010502607102e881d00480e0b5002540112107103c05501000b0030103a100401031014947d6a00441c245401e01c030010b520369000d40240c0050b0760384e8140d85003906204020b07080103d4509100300d050001d80c4c400740790303220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 154525152 1250 154523902 154523927
    0x5060403060501150c112107170f430806151f08060604090e01060f050319060506061204060203090d14030604050a06050d050d081006120506010327030215040305070b07031b 76
    0x24001c0003d03e202043c80410b034011542000003100980c0702a01e20429500302f82d100c40c800c54000d8a079000d4045ea58032240141c050018074006008928101041c44120070380164454001c1140840300c00341c00c454000c654580700f00e02c1c03c03d0421030381c40300d0104c0c100d806a43d00a0f0301d020300b0050b28402039001035002c80144e906180b002000c1c0361700d40080c03542d165081c11001c8042d028849668010801d030394030154001c5c4008058508d0311824091100e400901030310f089d644a0303400030034002c0004007008510040c801c242440200c2400c540000c6407a404000c06482c000c503200c0c400160501c3c410f0340400c001e4807009200d84465a21802c020342d880c41240c4005000c10300246c0840c10680b014640841140c0c00741d52684600c2e5500c000150151101410b80c6060545410b44121600200d00e21404035180d244545891615207090003031030040f449003480d0343c0b68051020300020a41c40f004582d407850300610107201c01e8a0711001100240064200105018602d04507141826803000d09081c10303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 154526402 1250 154525152 154525199
    0x210020c090a05060a1a031b040f08100b030a03090e04080d140406050c03090d11210d060506030115030507092402011d0a02010c030905060403060501150c112107 71
    0x1742929100201d4014030b2212001800b131b001840010741103030105000711011031410f03110500b071aa540c44001914030b1341d5008902c01d9004040d500510211070720a012004008400a200180b102d1b00c000d030203000e50b8080c50503c80c1814001600340f0601000b101d0014481000030002090361000392812140259811100e05040034003066407850044141c9014103104c90241028100081050302c000c1c80c078210a0703185004c1c207281802801c400f040c079510910402e054459541c14911281801c881d80b9401191150206000602510f00c200900308070002c030700d0400140c1900c0b240d40c10388012903254800c000b54400900e01640c6002c9010202c00c1324403d81d002400001204a1344c00a40070010a404019900c4010490b001d0340c17040102c400000d0103818014040768440000c00d10f0f42d4865002581d1403030b194030040254644849a0140c03070346d00c2b80781481d040350b44c2e40c0e5220b910060f004d100d64030842107000b44c18502c4400492036050058144c0480308000d40d0350020000b0490b120380400c2c80d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 154527652 1250 154526402 154526419
    0x70812042109150c0503120405070b0301142704031e0e03190309080a0f021503070c1211010e060414030406050f0f07120c060f11070210020c090a0506 66
    0x2800040400158040306181c40b11040c2d90b0900740200190f041c003c880000b081030f81c4401034046081400100610300c00e00c00c9080c0341d4585400e205181c03242c65400b4a80c000820801045a03801e151218204010101c031001203088000c44003035042d01659144540601c0a88184800c141d0403c0c118030190003e280002c08080398078000752544103c01c079030759825402400d50400b01c6071000c41920240c51280c18100c083c40d40703441681d440c15940e144212401541080d03940700303600d800c0c00384011a05540d90807920318540502d000303080000c8244020010109503807003800c03060107802e41440b09020b080080000050018107079544860a4800341ca404844140300111482d021040702c0550300a6214503141c50401300d0f54010561026006001c001014042c01d00018503020420448041a5507440c882d4007440c01d0442c11114000d5250361070524045180c50360300e0300300043d00c0700c880c1c0407075001034210702d00d0400780e0500318075440d0581d0003404081000500c240b5940043c2c0152130946183d007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 154528902 1250 154527652 154527683
    0x10c0206030a0c14070c03151418010510060e12030904020a0903060b03150708062b060b090709060c0503120405030408100902130504051f0f1107030c1707081204 71
    0x100c00744501c3c140906660703417806c4c0070300c00702d000c010041c206000d07100c030009101c1c0d100e040f0484180c2c1e41941c800788009240301c85410717240805d0250580060303503524035000f00c44c50100094090750318202c4483c00394600c138455080c042d41c2030050743e02494000d03005550b1140b644200a0294200340000c50f0300c01d00d008400d0015090000300c007800102c000c0888260b0b03807680c2005440b0440001e0100c6d17400308420089074041000e00400c400c0f4179143d020504440241c3e468880300f518034003034103a1300500c0000704101a05620226803401c0360100d0404602094050601e1400c5200b140c4040c0340614030801804200131001004000b101c0c0a038081d01c286034000074001c001d43d01680f00103507101d01d9009030800c076113010390700c00fa802c80d108801301c1d40001040c40c134030584006007448141c040e65607405a0a452041d0780507031049843c10302901440d2001e155070140040c0b0202d48013034042c100d0003588000f5920400100c600395a00701103c2512075243c0c03100a40591400c072000c9544240c03203142203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 154530152 1250 154528902 154528937
    0x705010f02211902160b06010206040b1f0512160603110306130e060a06081501051008090a0804080307060b091303080c1303060515030307030e0609010c0206030a0c 72
    0x31611004540a90300790340d44540d000818400c0050002030303142854590030046107405100409540c1d0b44017140d8082c007081030074000c001100040000341950865130400000405890f003080e0700107190840c1a103503241401c1e1140300c4030626001203030401c61061540c1880d034000981c02504840013001070b441251111021015a001000030f100010418404681d4500d408161806590307000d145c0024000360100f0010f1800c1400d554281d442903444505201003030040c04001180d00c00d440400b101342d4540400305400a441142010802c9403007004501040401d01c0305c8942c00c0e800402e825165511002440c1e1a52300c90308003200e032146000846591420301070901e0381714407665048080c1d404095103003030300c0c1c1c642c008000c0d400d0502d0801c03042c0c2001c41800c0e4400040c60003542d0006062034074100140000ca4207002c0360703110303500500c41c59000a0340f0003811507c080c8166910754880b00d0140040c0c600d080b41e510002d41c010404010401202c0143c0d0004078550b4990b550300848074000e4904 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 154531402 1250 154530152 154530157
    0x18041404060615021b1203070c0e0a0e1005040c0e010902040e01060905030a0615050a090b03070803190e130603050102120a0b0a03020d080d05101503020405330c030705010f02 77
    0x106001d030b04440e80d0440c12a043e0b07030103445ca066003e400d01000ca001c1c0486e141c110340c01600100e4038000301d0582403007407503020340102da800510081c4c204030300d40321108490741d902e08421800d0215519100018100887c805040008004500d100340c05542c4400760200650490300490b02c40311161800043c5a0307210343c0310b46080ba1001f502401120409442c2c81010348a04288217450041d940c2000440c2c2e00c6808400000300201c100014898080c442050700b003001d50b500c141855030003402242804000820381c448803465905241e508480e0b01000301f02441003c0c0d580b130408a1400500205202041d001000c1029194680c0d03071903565024500c000b03d42401003180d4002640c0c401c24001420a4095401d00d00c0c090000e007401c00d001c2400c60400d560b802c50702c20420725130290040000341d01c0817000a51107222420154205810000800d101e0320441c4020031801040c2120311180024806ca81450743c0c8098103165940c20113104ca181e03581d0300801d42298158a0500d070100048203a109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 154532652 1250 154531402 154531439
    0x6010807080a090302070807060509011112040e090f0303070509040c080108070603020c010e07030503090a090b091b161101020f01050906060603041a04030f120b0102060c180414040606 81
    0x100c0180300d803602c6404400034043d01c0c0381281035105600011078401810458213000b0711036a62260790750080400010503842d44455001c055920102103000c400004401351402d0300d410800b4814542d407800e400911b0590350f030705a00c4040c04000288060598080c0051100c044107a070300340b01804140703100f00d4540d0f1091144e5070311908652014441140302c1e8000308007000b241400418440c070030881c0b01d0708020090307000311407d62000510360b050307050048100b401008001c0040001c0c44004010801c0000c0040505010b446d540300c080012101013010b0f124210100c460f03100028401d8135000d074070741c0303000340c003c0d8094417424402c0980c41005000f090b10901c60f400103400d807501d804090080a0300090030446001c0403080c0c2a4280d449080c413101c1c8514005c6c0c0c0c403000040d425a04c00b03444003001015408c10241441001503c5907000288250400a00d04056544004100c42d040329030030405045075020f030508050542c4207010401007409507004500810049507150321100d01100c0d40741 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 154533902 1250 154532652 154532657
    0xc051e03090c04020a0c020306010e0a0b030a050a0f0c0902161e020618031507030f0f0204230604120602030105090f0105180c0d0c020a11040c0c080904020c030c0a0b06010807 77
    0x100500b00381050b401510100e0071900700819841000c0d40001e0410f042604040c040d8480e4408206010505001c0c8841110041d00a040f05112548503552240c1407960080d02d0888502010010800010102d800900d41c42c1c400315252040c420b095000800b09607010341e01d00090100f030741401064007105048003a4000c0c1814038103003c00105c0090003002e4019aa85400303100e82e4401d00311f42c2184280d1182d4050383d00003545041d6103d1580844406403a4410120320501c4144400148011403505942810055071540d0070400e0000740c0c01e01ca1038110014803c42c0e00b01e070a0400ca45900035606880c0200c0e4081c0f0942e0701d081422f176416100b440b80d036500442c51220b085d111412600d00e550000401110700e4a00003030341c2c20807410f9410403c91480160f04c44214003090017410300c45460f402400f26030a01403034040c03001c000c0c211000260080c04001c00001d103540781c1e55030355046800c84900344040c0c81d2200c051190807600c88492004c107a90082c1c3c40000100258403980c100b0744554000d8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 154535152 1250 154533902 154533913
    0x40918030305090d09050906040b04090507030c080a080a031508031b060105120c060c0f01050f06030c0a0b0306010f05040f0303030c0809060609010e0604090209150a0906080309040c050d0c051e0309 87
    0x4020007e29410107013003a41c100340d0700c00200000d9100d50180c1c40c8498001d1006050702c2c1d15502e0115450043c0d580b01880315008291542c0010b183c4208039030050f0250f243c00f05240710802103590b41c01080740d010314140e02c00000e04050600c0d070450080d40d60314942e001d5130780e41d80e6a081801401030034198901c5c10354011300403040442c50300340f000c2c1c000415040c040340e1980304000c0700320742100c005461150070010300d40d0800005240401c880c43c40100280d4000c0070051500880c1e1030240005010203041c00b0b00c084514000f14410801d4800a0071040c0350034042c0fa60321b0030090020002020f031400060003d000040c82c0300400aa4035004100c040d007410300c103070320380b0865100001d00a805607500c40e40b2111007074007580e0303100768140c000c5800c1d0070380060701c001c40001c0040b42d5000d030b4010740216003018000c205041020007038582418082d100812810581c0000319007a2103040d01c5580c10b2442c00e1050310b1441e0303210026085602924ad69002941c02a405100c85400b046441542d0b940c000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 154536402 1250 154535152 154535159
    0xe07050a0b0c0a08070501091e050a031b0501020316031506050d021b0307030e0f120703020907210c020c0d02090a09021201060605090301050f0c0301061103040918030305090d09 78
    0x7003038020141c0b90742c00420740d0540030042d9101452680f1002e819207203691115200007e001c640000c1085000344544170f02104111076407101d403110138441000e000d200194003180340c02c984000b011040e1a138414000c43d42c916240760b0038a099910b40c40c1184c00039280c5421a0003215240d80e91206650451300e48a0a0844084000300607501802d9188140c02001c4100348000c00100003030701080d480307a00d91135a009000000c0c0b205094042405a01c144035640c00000d202201003109400d0b6074040c1c41100349035a801d00280c5000121961030f40c3d90824440304092101c04e1580a40441c121540c00d90b015034140800304003011a0841d0060344c0840d071034000c500e404d001640180d601ca0300c041c14420110805041560071585142e00c081d000c1703800050039001c540350078881c55501407650a1046041c0c14140b282e0500c601050041c0300500c0740c44080d6074115481042580d00811207034209100360459062840082d01c021901113010900704804100208070101318180044203a03618480c00710314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 154537652 1250 154536402 154536419
    0xf12090f090c050f04170d080622090c060f0801080102120601110c040f020d0b060703020a031209060c0f1e1b110904060e070806010b090d02010e10020d02010e07050a 73
    0x70720082c0c5409021081041c4906203c000010344010011441950100f00036a503410307040442001b0301400304140c0000700580da568886404580656000c090510181c0c060700020080140d038401900015800d83e0004c0d403141d01c040e00d202d41d4140c5659810060b40d03541c040c14243d000e14000f00580000c4000003071300c59489000c1c01d85222860f2412a61003071041c0700407030200d0700c1c41c01c03610007500d40000e40100000d5003130280038070f408c40681d0442e01d80819618029241c41c0013100090400003d540240d10300e400710b8102520bc5d40d04034004000311004010054984030081880034041141180f250a980600800d030501c1140c65480710b609009290300e0030040e009140004031003000d0300c1c0e014803101d500c41e1f801282c0700302d10034000007030310407941c1c08440d140088035485091158080030051190801d540180c5203d002c095650a9000080b8801030310702d117010804007600001111b1400d400d040c0d0015424203842c440d03400810107424141030710380d200d1809004071500800703581410003030000f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 154538902 1250 154537652 154537661
    0x706080903070b0c0301051c0506010b031f0806070e04090c0b0f041805010f05030601081f0207080a02010b0405060f06041502030f300127180f12090f09 67
    0x14020981e07103402c0050b5a118807000b0180c401c5a00100048014050b0303041030362141408000d07555240307468078110390710309075100c2c4140a8a0070007003010001c00d1015124280240c4290700403070700e43e03484603129103810b551200c0403502080022041c40300101303241000d100d68505150000c1341e5114403400d0100959160740800fa590b803080e0b008010016200d94426540ca11004071007402103225454201d400d03440700304503042548660813a00040151190005c0c002c000780100f8003810558101d0304149000074043d203034000d803411f1000a00d5018480c0e0650000880c524112010009c03621520107001e0044800720459800030340c00c1000b8401c1702d440f49604007070103481b0320440345484401c130410805604035659960307145510300d41500d00100319075102084084008549010b07989002050f907240c210f4a4810040c50382901403104000029400c085000030011000e400104810320b421a01c2d0729210030240d5018a601c5441c806451150208400703d82407003240c03810710707030502c00c03414000c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154540152 1250 154538902 154538911
    0xb070f201305040819110c032404080f0a020105070305150d0602030603012003011503051b07020a0b03010b09090c0304020d14010e060a05041103060c2704090b04051c02070608 77
    0x84c4820700c510032003440d603012405100702041d40d8041d4014180c4400b075140c00b9500155034401c0d0030452505070209041040a1030500440503c0d40c06a00c45080a80145c030520100d048800800101b2502168054019900452a9a41c100a10303a1030a0305c1c00551401403800540c05683c43c508480428119000f441e00035400400009644d000781089846244003a140804036000c0030004020101580b18003440103801800c040c001480c0c500c2d4400c01c18005a981e88410031404145e8609548501c0344070000b40c07041c180c038285d417940c6505842505400050f401441284d1410010b0811040c0c0015280600d80c042d04910340c100e80c1da0b58580c19200051001003096603502c11050024404000c0c0c41d0280c50101c40000d0340d0b05003070400f5074285042c950201d000e940030385c003408600380006086444a003c400311140c1002c14220540700d202c00c03502d4074964482d00b0410a007082c03000c81400580614480d0088600300d45007185000c20b045800101600907803c001d00811001e8080c00722036501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154541402 1250 154540152 154540163
    0x60901090308191d0f0d0503100e04060213061206091e180804180e0109030e041e090c0f0e0103080306060a05070803090601030507051519090b070f20130504 69
    0x800702d4040480c048940c1c4074038013003e512580001c16607190502c1030022501407407404c10f00d14a44000740e201140403600c911012650400d002606001c4a6815108000000e45400000640d00d82d0004d18100300c2e070042c0401945400340010f0380340410720452114150004d241c00005440040303581c000c0081e5403000030084c40c072030180c000160f494001040034100c0f1411048024a50307008603022148024003d0b8200d030315000b11b001c01704e50001410070b25288201c0703001c214140810b240c050980d00b48100a11554141200041004031144200d01514440503001400a07a161030381c1e950ba49083c8405040803030100081202402c0c000d000b000400b00500301340d4030307000340340c0c0d0341d06569841113030b4022054024800520400c00280310345001082c04480340c0400007058440184148076101a80003035255158900719041e0144040000a00f00c0c40700080d01d54140c1d0400280c140c425110403a81d0074442007255045c5500540707500b00f40c0e8001341c503110310490301d0b4484c0c600820340a0400e480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154542652 1250 154541402 154541411
    0x207060b0307080d140a0c0204151a03010503060906130305090a030f0609020a0501112d0a030216050901030f02010c030c1e02030c0609030c09071707030b0306090109030819 76
    0x3194a081220300018000c2d0b00040c9900703070280c0c60061055004100d02d06540b4400c000c912031855001701348080e110340456000035450101804081d8000b09039000f44a11034101c41501d0010100790301660483c2e10176070903a000307541d1303845e442511808100d5848a0040c01180c14401003440780029040b800d802900302002c8944903120039550510364041158180d44510a0784210709000f41c41500078242805c00300c140b05011600c50b43c5891140004141d11099040d009100ca40ca00e034851040040c100c00742d0304201e1207810300944400040b21019900204c0d0000041d4078200820014100d9030082500200000b5070f0f801161040700c050700950800401e20524000300300030310a41c510700c550402d4000e11110851041c1810001c440107158415001031040c01e000d9140030401034420103084820807142e80c0d4088081e98001400c00c00103006030f01c1541009101ea405602c50365803010220b00700c031920364481900038203960500300000c00094905012510705140c0b00300212203604240c1c001304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154543902 1250 154542652 154542671
    0x61015020f12031f05101202070204091a090706020a0b25020c12030702090c070305040b1602040e0c0a06081504020d0212070c0f0b0c0c01090c0609150e04020706 71
    0x340b0b4800811620a442d440000902910000c06203001300b0742464201682202450840007070741481e8484205810720652156455884140d5812540307031584c010010070400fa054100390710714110341c40f8800d007842400b40200e5440c610000c0e40c4011245150f005100300c040c13940c3e810304600c0c405800103a205d1004610104146415000301c2c1100455034020070505d00304004001500304404070300d50b800e81080100001584862110303582c0f001c103260070a580c0c1c441914017150f030383c85141e000050313500020564000585040b840c0c00010f600031207040c800801d40700b086949911a44002a90180d0018020003410b800385104c10b6225201ca059049048e003282c000c0f50030381c0e100c0f0342003203006a8001f505121220019940030340044a919040170a0300d11551405409425820007800350046400001c0f00540307e502210810030141009120043c040e241c4410031110500904011030803500c004120210001400342518801d0b40d035082c0d03540d50000c1480000c4d070103508240c1d80213480c1c4d800c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154545152 1250 154543902 154543933
    0xe0c04150c0f050c03010c090602030912070e0f06041b0813020406050a090912020307080f0304150207050607030c0e1003050603070504110a09120b0106050912120a03050906101502 79
    0x25207642c0240f000e00001c13000d4100705401c4402c5446030105100c071040702400030a82c00019075400410903102170181044441c1500d181400580c00007800352080410041d210585101450080c80b042d00d00f400030344584044e1075406e80203010140c0003c1c209c0d50000f6a00c140720804004494005480018021340b650040f0300c540381203400034501103461f401c00c4010008003088a01c9048960310141d4140700866680301c41038415589200d40444d00030002c1828814000d50a0030221300203581150344581500d0130507150842155000040703407800f00d002c58241d00803d60000c60007001808580d0b910440d12065000b40406090300c0d0f0540304400e80855203855500c2116000e001d118840b640b90b100d40e5400910141850f003180c3c0c01d0350f4030081000d0004034036000c0141525000d0801780d840c0c2402c000411a08189243c0b4102ca030320400049148140b0404000c210812a80c5c7e01889542e0b581c54159564030380958100410b2801401c0070001c000c01c2007403007400700b01b5030b2056801042400020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154546402 1250 154545152 154545173
    0xd111801080f061b0306061804020a090e0708010308030105040e0a02090906041e020607201003060801060f03050303010501050f07061a090603011e0213030b0a150e0c04150c 76
    0x3082a4442e4100100c610820400742c1d6000806440d400301d0206070303801e854544d01014200a008101c0851848112100d00d1000e405c04003010b00115222980c4a1000b80102c105108401030015444c4c00320305034030312aa0200b810303203403c88a940d1440e440c04d018000204005a800001d80c0116113000340166900000c1d28040d0803403a0081546080c64101072120010510380c005040714205080801078a0b9101512940764014405032980a82000c100d0003102c5d8541550b80d21101884030003004981590001040d41c401000800c049903d824048050094a01014002c0e5206000420040d031103080100300304402d041f01e071030410080313641d5401658044c00001803845190b002301d000c0c0d0b0070f11a0345c1d16400305c0114020302582c4041c00b490310001c2103403c072401009800081c440c0c03032111580018401554010844841882d00304510f000511128084801c0446680b4001441001c2d00a40a0041c26006c21061801d440e00d045200800468807241c01808203c400440200313450284 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154547652 1250 154546402 154546409
    0x1101090b010f080607020f06070f1b030c0506060303070c05060702150706020403020f0414040b07110d090e09010c050f070609080f090f01030c022d0718060f03020d111801 75
    0x102c407036040c20080e4003400c004009103000210343c054011004140000181543c101c0e002c1e0038500102c07001810111420380c140e0b240f22034400d00d081144004c040e4818404078074140100240c908544403a0100743c1ca03413080640140001198400500c050f24041000740209407004212980c0703401c4c0302250207155001380c1400d58510342c2c08035080095082868a5160300d043c210f408110340032580c040c50303c04860144c0050103504003036001417400b9000b034082c40c2c11160360008880c0d5400c00c00b10002c02a0f9400d01448000138882c0000c1903040c1e205009a0030171002c41d481d1b0604100c5d0806441000d50045001174403211303200c450000111b201c000090804da4440c0aa00e0340d580102e4040c094211410040f0b507040600e005c003c226010707400302c0e01c820018078001647c0900c2032a114400035104c200110702c4000e0248690000d000040c13003041e0400b6803480c6809001240d07a40100c1c410b071036034030310003c1d41107070001400b2030000c0e001e4984100341e104c4c02880000315112041c5402003d0318244c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154548902 1250 154547652 154547669
    0x80d06050405090f011b050f0309012025020105030f0a060b0703110c011d060d2304170315041d06040305030105040e071d040203030c1204050907031b1101090b01 71
    0x514582d0b080000b1b000f00c180090003440302103640c10314600d006246209204075065502030100110326014400c9d000b20041096140d494203a000014009400d99405032807110079803c024107007403200d121a0681c460410390161603050840c3d40c3c42d0032918004900800541e599650740d01c002c103846080b000a060050300036615203040a010500f12031819042002c140e0521103a07945903600808044040440782c0c1041c1c40d0143c0b0344405a4841c000380c1010055583c800190f8000e001c465950340c0441849035010300c0d0180084240844410351910060750001c2c10035003000c0a0301401d08180d007180c010329103030240350036400000c000c8071801e201c010358040b000180d002004001c5850303c0e0040365240c0744544046c005440c03600d00c0150140c0100c080003c81340c46244002405d56600b032090310544d141c0d900035201c007607100c41c0c5010220390160080c18403c420000c04612114460b04c0b403005486c01001034840807240340340055a0001c1500c0e040c126964030703091404002210300404074000c05280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154550152 1250 154548902 154548913
    0x1409041d0a0312051323031209030706060e0408030708040305040314060703050109060e060f0105090306010e01030b070f08040308190609020403050c0d051e03040308040605130501020c0607080d0605040509 90
    0x10070342c190569001820901c06000c010300c03030700c01003030319024020840a80b0003807411b503211000952904500a650391000c40340f200501b009074001010009142140c496481004061744030b44619000280030380700034041e00700a1000810b5103002d04402c0d9001f40c00f030304105080990300d5840a05802c0500d424003400d0b00f005d07081c0203865406009050240400d00c40a104075820b0125141c2401801801c41e8440c141071444403d459004000300c032440c02000d005d1390742941c2c6560004102201c284001ca80006101340040c0e41580f24440e0440b880300107550701c80b0984c5840d1821a403058002d007011503800b20150404448518a210355001011202c0015880d030341f5508060742404000030032640940a0304594500040e0b000c140400502082902c4498400002c41c10034074501076500000d00c404000100450700300e40280c06481d070b00c02c0c0c003444a41019105c1d001242c03503098954a0940102c004c0c03022500252400000e0072004240d40400202c1507503610018086e950301f6101304416411a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154551402 1250 154550152 154550177
    0x705071416081903050d0617030703022e051801020d0b03060108010e03160507050303030a02072003030301120812040b0711030306010f0e010e090705090a061409041d0a03 75
    0x4070a9410060501401414500001c0301441c5021401110002d04202e00043e8895000b603031039200c0c00281c00190032400828100d050036655039800040c058000d0b102d440ca0b070b078124802c0041d815001a810b228441c4820034241074080c0540400307031501c081c054001451141d040000d201401c1c00301200e0030b0101d80c8003100001d25082901c183c1100c40540d040c4990b030402540e00104969001000b03100d452049810b90500e103003032600c5c60300f025a06000c004141701904010b0f1b0080c00720705028485051201a85440d07105c20084d10340c10691705038005000400441c02c40542c1f480c2d00301d020303458951070181030300c01406071018116401c840929050052202c00c40e40070070000c0050303403144000c529504006e400a006c08507280142070400007000c1c0325074556440303040d051090505c040c001452504003140007900342c4c1c102c410075a000740a0190009200ea211b40080300800190b8070344146464610001e00c805051101e0340010441407244100c02c150a0030400005000e00a542d040c03003c1d50b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154552652 1250 154551402 154551433
    0x15210510060c020607020d020105130602010203010f0b0c0606060a0909050901270b04020607020a090e0c01020c01020a0b040b0a1e050603010c03060302091609050a0f090507020a0f080307050714 85
    0x36070400010800319804400060311010210788402d50112050042c0c22160303c0121628440c035075500301041c48a400000301c1075015005035041e42e1a61682d40b2030152500071362001e81c01803040c1c06c1801d40c8080b01290b00c0c4c1c113101006041c000586e14002d0300698a8241d0030080d035500382c1e021091a0740d41e01071103e10509290050611103440550308000d0422a1500b00182c40c3c0508064455030380010b9500466582080041c01402c48400503c04d40b0000c144654070744443c0c0340d119015008801c40c01006601c04288080c1c810f600411403a4242c54603114800c5891008003c2904260303a00765103540d003510660320045021070620b001c5130700d181c030070309141c2501e0415401c00e0505040c5202840141d581c08460b0390700c42c0100044201070b2100700e400b01e840300844c0d840207400218009000c100106a2000c070700c15902028003d2205888940041740e032004544130140411429803e6900000d408000440e0821828900181031003526280d20b8511450311150a1035a408035861401004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154553902 1250 154552652 154552681
    0x30a0903110910030303020c0102090a030302010e0628020903010e0111030414010c0c0303090c050406120c08030c0307031404030b070305090d020607051803011b0f1107050a152105 79
    0x7003510241c0b51800e01c214a02c0112000b40002000e05402056042000030254141c8903100c0004102074403456036030401900a150a000039500d41c094000001c01115058603890320f502e441103160314020b1154205a00203400240210742d25548855004906002c240100e43c07280c540b14400603544d040518001d84480840401031520b6410100c7d040d040c9608400016a41505401d001c549040c49280080719541141c1216a219143c00400310fa01c81403003080340325591090401728015a00c80340d249650f4082c2103400030b01d0b54001c0080c030700080c0c0704d0316090301c020340030400d128107254482d0355400340ea0741c0489200000070f40d500100800c08a04000018584c1ca450010f4008c03030410403030091880c8146d680d031003c0c8185250f20070500e51400d5002c0381c0c0c02803c600364010442c01840c002090103940c00c8540000030654404180d002c0000b003440c0782200c8004082c41c200384d01d489607907074000300001013100a0140c1c8001d040c0800a4607004984840a4494009190700d4105440c95400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154555152 1250 154553902 154553933
    0x2102071a0f0a0e2b0303020d150e0106140403020907051e0c010906060605090f0f060c100c020c01020601140d11060c0109020118050a0b030603070308071505010e09060f0702010e030a0903 82
    0xb06055011810304c2181c14400351410740c06140159444d4000c1e0f00c010003030702070100d0a0340382c2980d2070b030001440600b02400d18144d816941e181121204148800d20480c000c5000180d40040080e020441a50080c0b00401c2c1145460031403c26240a050b4155029002690401c03101e1351240740000030401d4a1203690040d120380d040c0207003081000780106080004c01d5100600550ba212840c0d0002c4e581c217426151071980c0ca008035000da2805640c01c001901001c03a025016103d0315912141c0d07580081100d40c1600e01031075940403029105020090515280c002c10b40d030030540941d44105a40b0345c1001880516065000401e1940c05031000410b24541c07130082d03c080420b10007050206030359140d0503a0465505040302901c035200c080000342461443c0c2e00c0180940030018451040081210800d86003280030402004160f988200c00803040b68200c601c800b01d604041c0002d01c101601c040c0454124031a4030001541e1140d007071107a8a1a4001694900465a800030410800c8010071500e40c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154556402 1250 154555152 154555189
    0x110a1d04020f0a0f090801020a020114010f1d0618070804200307030f02190e0907150c020127120c08030a02030712050d05010902072102071a0f0a0e 65
    0x500b488152000c1c0940204803d4004015012001104c4d19102d80300940280403c0f4008641d1000c1e80c040c040c0c024a800801c12044107100700c0000740d00c030315000c1805c0c215180300d070810568122245000070103040003003d4561010000321110000c500683e54240329044030b031a011a0340c182406c04084108d10210b00880c82c0311841c010070100e0b02d001c1422011a9403050350007165280300c0c03000540641c603044401b1400014008001640c070b5003100303402e0064401105940e5859295804410390461840c50301001c10392142c00007006502c40d030300d10380108941100da0310040d0a5840c0c084610362480d03124200c5089100700308014030a5100850000301f00500045103000c81d00f1001039100d004003a03025240400e0b85d20190b9060b0702901c1215000c941e1040104250b42c0c44243d610000d42046c6c5050300c110001507822146a880304081d03035580a45038004151061070143d481c0d1480102000100b105181032006101030040d440240800c0e0b402034403071915449200d03090001c2120104207142c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154557652 1250 154556402 154556407
    0x708010608090a050c0609030f19030f02060105030d0c051606050a020114090c062d070605011e0e09070302120705041113030b1522230a020706110a1d0402 68
    0x2613000124400c3d21032090760a02d440c0d10451001030b0511514400b4019180500c0204580b038000c0250010003251082e03c1d070201d1788a15007022650340e0000d010311501a44a01d41d0881400d02803014800342501c00c4040b651440901d0541c104002665885500856400b01d4ec400105070280209000007520444940302841c02c1c0131183e5481d541c008410f4011640000d007000c8903d424a1496814a8004d007088224090440c00584640c40142d00b640d10714505000404c82401c2d40b01d03c068000e800c0780805010380d08084a0310f1414002805003c40d51180c58000801038883c11950304d901003000d00a009443d00c0d000a001c1030320382074440c4a4203108104111140d5840c140160800d0340d812007070030354a69a41102d004200c40c44c0d200940e43c4481079450000410815288402580340920002d000040c1400c1801079081075000300c450050603007100050381c3d0800c607030103040418028040441c00d0000e251601c010341e40400c040f040003950320414180e000e41d0595680325a03103003d540461 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154558902 1250 154557652 154557673
    0x30915050d020d06030c15030f02041410050d1a04050606040b0a0c03030b060c0303070f02070609060c0c0b0712030c021c0f0e0909030405090105040b0a03080a090e070801060809 78
    0x2066031040344070400a060340421481180c810b0b40d4401070142d540090003054541d150a0030a0114003109080c0c40000d08092000c050480c141c02901c1c00c94580c4055082d038030700081d00300000003007803c04040401400340444002c6506600031414210940b00f0b4080160519005002c140c0d80014043e07802007100b000200305400701481211000d0740c5a02d0640c540580c80d1800300e0192400001c0356a0201000c1940038184001100541c0241500e86483c0918440031006980740c0800388101404980e40781d5040004500840242c014180704050946980c0d84039007000c6242d4010100580b003152019601015040e014403a903003004105000400e002000c80c00e8030303160011a16244020800382d0505420340d90700030b07142030030f0b4800014415151844c0c41c4101039a00d8000f442418820140d440001540703090911804022a201030400b020060030368458014551207010001708125010b080090051400c4103c140a200300d0707a10109103516000c0014402240900032034659007102000700d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154560152 1250 154558902 154558907
    0x150301030c1a070b01170118020303030a1d03181c0b041e022206060504050d080307180803090114030f010303200a05010516080907050d020625030915 66
    0x35040b00e0004440e42040c042980c101c2406025007600140306101450001c10b0800d0480c00c07800280441c40c008121080c0d076516181016600240003a405030010408104103903540d03008803d6000c03d00602e0b0400048150b211481d55100300c80b401019103a80140600c10310f056225100c000141c3d41e00304042d040c168840000004000c2d000401100c2c0700c0c149541c038483c1c564031052100707400401001740301083d020711521145a1450302a401c0d0b25200d004600390303001d1000d440660f070019203070704941000c2e603458540c544e101405030010301005900b80303444852183d07503117005004c202015588076045400090030464070005105200300b001e00410041d06131220070241100d4140c42c0900000012030f40744681802c80040200310390045412030418803070150001c1b402041241c0080c1004181c05c03e04a40f01801030300c0340e90042e080420100a5490000004044680003c00702440d0041c90030b403584020034091828000c0103a092181f6013419000b0408034000c089000786c5010a20208000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154561402 1250 154560152 154560173
    0x30506071e0e0418060b09090109030c080a02010e03281b060f020f040f05090f090714060d060e07020f030a0c080d0b030a051e2a0310050c040515030103 67
    0x100c0402014440c0301030b4656454001d40f2504a1140748850b001001d810110040d01e4000f40090080900201044407800c0510800c8101501070303541c0780b0010003e542c0d18800ba44001207000c01c66494401d07141017007906000078440013100790f08081010320741c0000c61203035079460100c690034440303100c85140d030403c13221080203400e540c0140c00243c15060b40070404024003613080780e440c49610105004c90791a802000c482c099800c100c40c0c0e02c2141c3d4070b0000d4600280022117095000750820942008400c8a000c9149a22080104043d0402c085800400110740440d4403400302c0d41c03001d40a10031a1601070118005000110014601d004c4255601030071b16501203000600c014000200145c0034403080d41b2600702940000c0030342c1c9042c070380ca050465442540c12440403940764107041c10465100001900f258603c2c1820602181d4410601c0c0a54004030301c020a07501806070320715603104800640b088500c9685113082e81519241854107000c0c4030000708000c40c100582c100014400b041e200e455 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154562652 1250 154561402 154561457
    0x3091506010e0108130c150201020c010e0604020a05270c090f01090501020d1407050106030507051e0a0302010c030c050d021f020c07051005070803040605040212010b130c020703021903050607 84
    0x502c104800b129180c41c0700c1c0054140d11204e101002007101f2945194190000c00900f01e00400034031081080005181e214042074070020351154066000f007040e03081c40240001c44e000c103641071000128815440c8551000c08031400002c810000850030f1480c500105910099142807030024003150500002035610b81c480d000e1002070004000505000410020403501110744c410001d100700c5d0b40c0ca1034041d50717500c0b40c1d0140314483c50100c800d02111214140b8141d0702e040b001806024400e2554006590f41c41d40980141c04000c8503041140c082402000030150380c80280d030081c100240f100c455a49a141c0c0005401c41c0c95004002c2c00d542c8100008800c0240c58044642d1a00c000400e070040e0b071144210070000380099408001c100900c40158071061107180213903840b610528841c2a682d00f00c8906200003030b8000e0310444200000403869001001d40c1c681801103d00c0d440d140d8000401ca0740c01e80e4042c07803080901d2241402082018404075800c024503082c0130146540c40864490410540380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154563902 1250 154562652 154562671
    0x605010b0c0c0f030705130c0807110c041112040c06030e0d02100e0a050d0203030f130f03030c03060f080307060c030c02060103030c02010306150203031605030105010903230303091506010e0108 85
    0x70f15180d107540c003880020010100203020f0300e4251030040300d140180c503c800b003d40100714407100140210340102d800003c2082142d0251050300718440400c4003c100c02e01d0141c8010300d0902220042680b0646043c1c055402142903411007441c0040040031f03034117826080045904420520300c0313616000034400501c441d04c16808280c6601c550f001c01d2400d92a00e0002e4544e200700c1610642c0b194010000318003400e020b0132598901d0b591030b00404014907410600400f051400301c07403800840c1c4641d00200080c0300c0340c5008180c071a5610390410600d20340d50030204031500001464000c20030140301c2c00034108540c3c2818080d406c80c4036006529103005220150900052034102402c680c841e5000c1c20140612000c0d501d40d00070321010003546c03500300311450001e400044041d224100d001d1400d803070488005a45404400c0c0c02c590700c844200e48016425904071005a60700075a440c0140007551045241c032004085503010050400c1030b0540c042c00490500125200803070999030b0161649038888141c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154565152 1250 154563902 154563919
    0x1b031d010213030213020717040305010c0207060f030b0f060a0f0e1203090915091608130503041203090e012c0702060105060306010e031e1011040911130e040605010b0c0c 75
    0x1070a82070007a100c2c0903002028102380d079440c41b441124030300140041d00d000d4002004035203182d9205036581c00d024001d02000c0b42907160510302451003a08001d4031060040c2c84220f00c40020404141c80d40c006104c000c01045511b070b000200280e0102c40c020400230704035551840a24154006a01d9103e540c0c0f800f401894010000740c4850141601c5620600b0085d0441c4182e00d0161160713080c005100b0006000110a030000c0b4034660003a404902c10143c10501640c54285030000b000c0d01489814403c600f48028290002414080d0f40d10381c1d8000e00c640f62450007240e103969001d003031448410003005440e6603001d040c230034003950015500e410743c0d01c161b81782507813500c9840060b03d1000c0c00c00c0341c19a0500c1091f40c2040043c081005c40d80400c9107074012202c02c0c14100f00858250303100d48888403144401408208a41380f42500124845070106000c07900d0940c1c1c001850b1142034640d006980d91228080a0204003e154030030b0f10300421524060b01d00b002d0301d5003844d588803101141140d1046c2000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154566402 1250 154565152 154565179
    0x3020108040f1e0b060102011415120f0c030c0a060e0409060e030c0a0308060303040302030c13060812040f140303070f0204020c0d02061f030305070b07031b031d0102130302 76
    0x1450380c45100b05401a40d92114604411910b00d0076044082c2c044030f024002c100400d035154014000c4048459050b040c4c1483c0c5e9480d980030400c0410440c0c151a440110707001c240700c030000148452110407a01c140602140e41c041c0051628114080c03145072702600011a0400079103078040c00710708605100312400f10300079885040100c050400340300b074800580000a58170300220340000e000b0348882d1090701c8516041e551502016104d0069100280d01504420001d10803032500c000d540600a0070344c100081e0b03036616180150300d4095642c040b13240303603940044e05002800e26107007000020100610141300d03112000700440d440c0c1c022503200510100001e810041195195010343d41d1056160085030420704a0510096491400f9078100c51040320b03500c0c15010300801c003c402000d40c3d415440342850030180e682c415911840c018a5003080559408001040724a001000903040310079aa02103074580e64401d1481d142d4000340c007070000c03980c810005583c803641980105000c0342e8048804110040c007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154567652 1250 154566402 154566413
    0x15030c030615050d0c08090307060e030c01050709080c0a0b18030c0405090c0103064b0b07020108070206060102100b01020304120b1006050c1f1401031415010b040302010804 76
    0x70250442c1920154500c0e4a074806030340140542135513581d41d402408032240282040c1c0d01c500060300c0e5181c071500200320f42c40c0401d405030020311000005c14100c030300c5e000c5001005800c450007036403400001a41b2a0080080342010421030704010320450b420807090307140800c440301c903214000c40400c070311109106003801b95600740003045d03041d403002e4070a000603d01130514944411490702d003540807a103080b00c0407034140d4001d2141507180d4000d50201c10513080303d82c950b24440741c1500c90b800c080d42612200350340a65035940e014004021081000d81c88010fa4400900842e400400707000031944030400700001a0380c00030350444c00005441c00041c540d01030a004038158440c40e002469850000c0e9254402c100d81800100d00c50902402c0c802c0406840310021070b480e1044010090991b8012080306032410310302e86c08803005020480c40003d03c1042c094420081801c01d80c403e54114482e0004900124014031245040ea8040c0b8543c105540c10702c419a0300c14029030001a04124511000404000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154568902 1250 154567652 154567661
    0x3031b020409060e0f011a01030b1c05070e0603061015020312130501061509030204050a0b09041b050103090302120d14040c060e060333061308061015030c03 69
    0x540152050180002c5401d04001400c43c104a85583e4411640c4100c070420061143c41035001d515041405d402e500700c001100034080d0000103980c003044480c508620050a00b446000c010322660141c1145841d10200c2c0369078401c020049806030b00080100b14000c48200384e00415141d00d08400060a0340b400d104900c1d60254845035a40c00083c1d509000903900145111100d41d072090000307228042d15041034200714146a0340500108a090f9400d10040c58075422090b40011a03100000b541c610f04400940d012005480a5070382e0f0419043d4802100342c03485a000c041c03e02802c090011088031f6900a646411807241c40070610700100d1f145032a50f6030740c4c01540c0d40d4644080c14480d80e0420f4101410710034603500c10200070801086100c1004e05010090340d2160400c0b0401d01a007146211030000754020380c07807601d80e0032902d104246c1c0499030740b240901800c5800d54401546141800c0301549892000307020080c8510032100d0800c05001c1d07090340700408940f00e18002c00d4442c4010310a50182 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154570152 1250 154568902 154568957
    0x509030d1202090d2d030801060c030210181104050601050f13030b07050309070801060f060302160c060504030506090604021c03090b040e040317160f3f0e03040303 72
    0x40ca2601c4c52400c0c0850004100140810001d404180c55501c1c00010080364403410001c01141181c0e0040040e42d0088900a055034004d0060b1031485c141510790400b00c3e04010300342c0071005107100c440400c0c8031022880015503002958200f003e420a0720010b091406440b40b0104809030020b1686650442139103080300a55110704010f15a08086030050f2a0b0780040b6190f03081e40c4160803001540c4201402010100c2d403421110100403814840220301942c824629440c1d0750781100c440c039000032000240700008045235510140c0759400c1d890b11505010b070107070112017aa4400300601000d0f0307640010f074840c034500030a5070950101c400d190980302c0710132991007045800c1000ca0300003004d400340d01880e846148039540307440b400580d016008540300c00545001d0b0324003005041c0503580c20f009052851008540b4282034041c00781c20362195161080c035840e82d01030707240b070207140c1c0d40948a40c0121100d00f0301c0c11031040c0012800034150766541c0c0164440941042026007865441c40010413945041c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154571402 1250 154570152 154570159
    0x1140309060f13020a0302062b020406030605030a0c05010309020a08070e07030c020105070e090912040801020c0f03040b0f0a110d020c0a15140a1b050610060509030d120209 76
    0x100d1914524041e11508200c0b448040500d0100026011490100502c4020365005103124031050558003800301c5a00000b04d088901c101c0000e519007031014901180d944280c2407032000d80e5072030928400400b0741d191580198000da100401e5040024100c03400003050710800e28002502d84200d000040c1014a2507101251702e0044160100c0d01e0615030040a100700100d41701400f0b0102c1c210360403400c98808950500006204004055951428481c0c2c0d50300908403000702d8a0451000081030b060b9031007039110602d40e85d07000803a00312102c000d2040b0044000408040d504043c80c000002d040f5204071366031801c03140700018800c22610b001381418440031414000721103410913400e00180d6911407807950244100040107001030b04405082d556281d41d0001d540d000ca1100b030140407040517402c612403010074000d00894594800810013688903070b00340224010009400d040c8a07042100c9584d400030341c2040001c228443e11624001090007c000c075915040b2414000d40130218000e0203003200480d407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154572652 1250 154571402 154571407
    0x919030b0c030106081311010e040b041812020304080703150f021b07090203190902120f100606030203040228050a090c020c040b0109050108040c0506040608150d0201090902090114 79
    0x82209100295050304c030b00f07494101194588203403884951030000c20081803800d007218107500951040c1381c14554510041c101003000015031002609603904540000e58103803041103103c00b4884040006c42d6101d41c06c0c00034500d45070514508584900340d07400040c00d001400984000c2200c03495001748039041c0a40c000310341390041030b04009040300c03250101522170310643c50003042181d81c0e8030883e03000b1140a02c10300c0000c000c000b00303103020b020035000903a8014030841541410075014080f07241d95041d8440130346454101d10180380120b455a030400010180305000700401a10780074180c583d41e030b01440350316551480c003503640a086005a000240c0142400310002200205600003a841d42c06ea03809455240e21904207000413140501030140c0000c041040400065020b160004c0d000b030302a081c06115070751100040f8140b541b00d45e1020b80041d001008201c50a5140180d80b10b0210040310f902c1081125900028600452805013412507070340081d04042582c064070b000c2600c210602c01054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154573902 1250 154572652 154572661
    0x60f080c0d052806211a040506060108072f010f0606111b090406020a050d11040501091e1a0c011d060106050309030a0818032d0a02030919030b 63
    0x16403407640f050000f9074643c6040d10070200f94206008010a80e03800408558002c0c00c101220401c0701201e85090f14004440610140d4203140716180a2296008100030b24160911800040080a0080582c4100300b40a075540300308000702c0350003504c5501144a60600d040100c0781403801403c3e00140c00010514001000603403079000a03155540203154015101141c014042c0c00720040561a000c613404803035000007800080b03550740a003041d400e032403400a04001d06001402c084400c2060107450410700442c040005680c0040c1c0d01c070140c01d0040300340f1000c04040b03155001c0345006014034151511040490ba0025548a00b5a000c0819020083c4199889a10754103400340c2e0b0040c281e1843e0090710000b050707860090701180d0054012400031840c240d211001216900c101920080c80025024001020381108001070490352a081c2c161204406c8000c1c880106d01f1a064080200050706201ca00c10b02d030b4020003582c00030f541c15214014240160b201c004400d5011b40c1005243c90310301e00601 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154575152 1250 154573902 154573921
    0xc0a0c030c060f0c1707050d0302030f0112120c050c2e051e07050c1509030d2109020a030204020a081506070f022112120a06060f080c0d05 61
    0x2001100c0c052150428001c2d00c42c102111003070640b52081d0040340308100342800182d1072000c11844041308503055400c0400315901d0760f040c40314111107500040c1d0040b080c0306d6038541c54000759004140810520000018030707a949411014a80d59007824011840c40b0f040074420b0621622081c124020b00703120071400f45840020740c1003100781e400b8107030329900c1d080d440700e43d0f0180e0119007903200480c1051400c400e0390041500d40380e01c428030440b000d0081c64440c000070386841c0400e0480c3c00c0741e0f0700500d40b680301000078945402040b201404c108001c0c3c01c1024a9a0400c50199000245081d00815800c0c2e0600215500c0e104681c0000e401500c001480e2500d181d118414038011045920108054100342d42003103014005c01d030b4058100d54040080f80010b24041c4d90740c40f5160650900340c0c8040c608081d506c1c3c200384400715000f0080400081c4455418040703441b4662114207900d08010380703410454018000d900007400d120502050b01c0105001c038100e1030a86449161007801800f4918100411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154576402 1250 154575152 154575173
    0x30f01050a0c1d060301032907050a031b081602030c062502030c030d05060d0f05100606080f01031115030a06030201080a091a0c070218070915020307020103110c0a 72
    0x20b0400052091040b0002c03503c150714600d0380010000c03c9903003180d085480d04001c0744650280004204500b11a070b02040c0585007070580309074001e481d030a490383c115410140580307c010b0013400241d0060204c00da183e87d0009500c80c0c112207400300919070030103c100c09921f10321400d204900284944401c006200b0301031401403802c8014240c1c001e10f8515011400da070b030390150919200141e002800031400c81741b031039405241e20413002050140c10042640b2100503810803501d0598850700040d82002c501001805a40300610b81460071000ca442c226452070320303919040c04000d004035001400d070038180e5185144159640310742d00c01955681014000d400c0109100d1000f2404a120140000c070300d02d22906c5044c1c4800c4d000019000940890000850f800200401a5011400c10f022a001603200c19051031121140c440c09860039090032200a407000d0311540c01410805191801c0c2000950301005071032026a0a00700402e1503c858650660b03c0e00998090700303641e00c1640300354024030a80e0040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154577652 1250 154576402 154576421
    0x304020316081903140309010f0507090303020a020f010201021c0516030207030e0f0a09091103011b090b0f07020409060515030601050a1806080115030309060c0b0403030902030f01050a 81
    0x445101805075100c8008441540c072528145420480d6410f09944501c100d05801e248680360460101c04240a2625140c000740c58007500f42c0e540d000105606c4a181c4034030740c0c00c5800d501300130281070301d5950020340e200c400800003406580140c0c01032045900035019114030007910104091841da01d00c0c2c00070010030b4122008600c0c11510089404554042c0c42113451071901590780d0901280c010042c4202480380c0740b4803540207207007008001600c051610079481018403c00ea15151009404101420f49019851007552054142080c01200e074000214070101c2d2000070880340c6962400194000d240200000a50058102010744040015550040748519550031500d81000d21210a05a03a404240502a04003000c3d91050114074503080c2c0c226209116080c0120b8a191a11411800d40e184a50029a1004541030a200701500904650064805450300000c030f1586a00c54580088020b0b0020b405e0690366505031041d500e00f0710158502050600092180f410008090340081c40140e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154578902 1250 154577652 154577659
    0x1506030f0b0f010f03022103031e0c04051f020f010908030415050c04050618030d0309050d03090302100203040f1b050f0603100918060e07150e01140d021c02030402 72
    0x60000e040b640c000c0c90070301c0c113031010026540301d120308550a200d101e8014941151600b5000c1484d14031001c8100300030342c0f003032414801d5600380c1008a80b0245402c8005000d4034425403050005000a807038526480b0f000d000607480405076800040410780c21700801280340300c403550a10348920140945ca80c0154042ca1040d006071440d5a00300309520301300d482c1030b42c0a04079650100f204005528240f0050900c0302c0000502c10140c2c012000028a010030b11141c40020a4803403900c0010b100042c40000c0700c403e12400c040c00000210381d03009455554843d80b82c0e01466021020805010141e40040b2103198840d40b07165103c0316036020340440c0760084c8079039849140018102c11035802c080c01234901643c04100c0d0340310300700e08180c607880240a00c0040580040203c07a80b41005c5245400788041c001103a00140200780d09040e039000240380c0c0f110103442804403803220901d07c3d0342d0205c0d00321150503410034100c0c0c0b50219010580068403e80c1c42d00d03400c0c0c03003061031850f09034481540214005d500c2103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154580152 1250 154578902 154578923
    0x80604031e0518040509030d021c05060105070305030a0c110f06010e07021b0906041b030e0d0302041d040804081b0315010602030706090204060506030115020f120a03091506030f 78
    0x20004984a12682e0f0a4a003821441000c41a15052513000541c02240c4c4409a82c241254000004121b030042d0003d0343c44410030540f0000d00801c180b081c5030f040002880e005d4500105a10702030420301c8060002610705507504907000721284201d502511100c044c03016142d000442a12140d50380380280a2400d59848000c0401c41036400000c3c2c0040d0b0018000b10107201d240c3c000100003902100400c6190000d0702d0b260034842c015041405840c060501361400107010030540700a900c0d00c000280c42c601403520400c0188000c8201c0b807440030324812280040000761b5103a1401c803003203004580c000d032094421300390383c0061805d085601c421410004c4d011a4505200a101ca003103408d0280f00358000f5070020003c030004194160014400c07940058804a0040e50b51070100324145c0c0242d01c0801e4416000081d001003a505005015505103200e005180980411006071100d01c94900540b00f4503580c2c030561002c000c504443c25040c3c03104003c041068550380d00b400003c48040000c1205c211256 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154581402 1250 154580152 154580207
    0xa020d090f0815060301020f0403030203030f06090c030112050a06020d1a0402040303091806050904030905120a0206041401091203180b030f130f0c140406060e0609091008060403 78
    0x40c00700c0446030400014042c480586030f0000b00d100c0040d20854040d5000c002c0d84400c03800c0700300144015446680115560715141c03801c0b0040d008040c00c558403030038004d401d02441c2c0b0890030035681512200070350311a03d41c0d000c1c5000d610301032180100138030301030010540030214042d0350700003949420154120921405000c04020403031145002c01404548508000c1c0444031100010030000581180005616030b203920028801040490302200020b00c515000c2c44182082c907441c11100c070741900208000403040c2c1c000b8200340964000c0c02558880607040030302d40c1e8840c0c01503d005140850000c2584089800c000301141c07602e00b281060481816070010b4a03c2ca1f2208480c454020b45c0d0f5030354480c0d26146402c448110b080f030130648840311103040c80d1010409031300740c450080603074107404d00303022007810280310035120b059000794103004003c0010031480d01c0d4402111074160084841e055140d0320000c04100040c0250003c680d24889c100c02c0004141e040004199141114414000301408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154582652 1250 154581402 154581419
    0x110c09010e1602160608091f050703060503010209010c080d0609020403050c0909190f1703070f02010f0c090905091608010f0f05010803090904031b030203041d06060f1804020a020d09 80
    0x8454001c82c4c480750314138800c208140c41416883d400c0303150441076480710050980a03008400b0290000e203001d42d5038a0900c500690903200705002020180e00a41c1800c0c40e05002803d0802d0540307020741020400030320080d4110b8643e004070301524800700b0840d00c1e9522401c00c80d5890b411048168000d6903a0301c04a070752090002401d6242103c048107152988aa5560f2550090814101140d03084600d8000543c1c0e0402100554032500703650b65030042c2c08280180003825100309195052005190001d00b500540d07002c0a9401510a240f0b00030803603407180074640c1d01c0c003031000c07601e10080209510080382c1103c064006140000000005102c240c641e10b041200310780e0700784240d00d02940704125410583c2401d2020581c818041d0400c0303590246489200d0340304003081003007200180c1000030700388044d48206200d41c1d8000080d4080003401d29110300811903031711910801c0016603078081403008810508500c090b0344080054420340d00c130466090040e5540c01001210008102c11a1004c2003020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154583902 1250 154582652 154582663
    0x5061902130b0703032a0806040c0f0503060307030c0e1803030c03160c14030d0e010b030601050d05030c1504060c0215060105090d0b0106020a0c090209060a110c09010e1602 76
    0x100c00d00c15001d41403400102540b035901407002107092685031107401c060007008000c028a00e4400c0c1c1440910605c021000038185030004110b00e11a07440c0500d043c81c010791105071140c3c2c217401428070320303900d4484000007450b2002c2130707000400e0048111004518141011034030b600840c0c0200b41101c10904402c035913900c030701044600da0014003040c40060754650114001801c0201d00303040c90011400d05483d10460300d050001301000c00c1d840042e0f44408a0028070440e14020f030140700800110700383d000000e480c0c4c41d042c85558850200c564641050040900c100c0f403a009006080f903150035078108190344080001c0710140d030610f15001c0b41d01c006d00c0c00443d5071941d00c402003604040c940e440100645040e00800e00c09500250581c1071000010345629446010b00015001001807800503c0c00f401c10910035000f80509900522840e0b4007626564266481b4040e039040c030295000d01184124901a940c140d2240c2c4160210000070b6440141c1d85202d0050750300f031100169981c0d00580c160b9890 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154585152 1250 154583902 154583917
    0x30c0e090c040816061704060b04060602031803070302030d0509130501080622030c020108090304030c0b0c061305070501030c11060a0b1521150603090d0e010806011e030e0a05061902 80
    0x203059100107406144001346c1c604d50041c0319010008180c26040d02040881d00179412200250b8070001e4003d5500c1c8189002881030b0300704500a2050b02d0456003c41c1c1c5036a101d501510603c0030104042203155100c4034103041c0c0c3c3c444810100702540e0344484981c0d480303109030b03151640140c241c14442c1c1e108103042090007030b2a0b0140c58000d11881d01354011244400010b000d4401e3b400240400700005101c1c200410040c65030a0303c3da07032030350b00310140303036040c1540a04101182c0c1c130150014800204085a0741c0708840007401c000034020428030056038070904400000180e030145008102580529912030380645030152224104c0c10a05003200700a0720400d80f1807510505a03088101a281110340c8242d4803a074421241c00d00300700031030041211508241d4a81100d600445941c03000d959210030111241442443d001040d0f040040c000b0b00042061117a07002c10412003101480c02600036006140d500c481602201e1540d960340c14020381f10320040d652484a500e2609028881c8031980c000e946c0360 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154586402 1250 154585152 154585157
    0x40f0b060126040305090307030302010911060a090306020c070e041b0603060602031602180426070b0a1d06090304030c05040603120c050109021507021305090c01030c0e090c04081606 80
    0x22190070790062940b0107801081202042001c01414401c0d46051010100030b501c207400201d072501051401b100d4200030a880704e801024180040c0c01e1a55100398801c00712900701d04016a80c079883c00c445800c01c20150020031458110304148000c000171691008400340c0c660440c5035000d91100f400300c0546e5403922500006a00902081030380c0080701003192402d0744018075039614200040e880103080c040c100d03820b44008141454550360008180d42c81c0d040101d105003c1c80c0b03004010f5882c0030090b1000741505610310354408052212881a400c0703aa40311001030119240d41c98006005542c96126000890311405952400551800d09009035000d81b64400f03400d01400c030038220102d4000e401401c05440564035400010701680380c0b0140c075100401c41940b03003035030380415005000340326101d040410344551414080010180340031400d103009080919000c1103080050034122800c444d09944180e00165000034456100030f458001e10480347c58400799190402140b050040c0a6024440ca001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154587652 1250 154586402 154586447
    0x206010303093602030103020102070f080709091a0c0a030e0f0a02061c0f0207120f08010902130506030a060602013e0409020d0501030203060a150e04030203070506040f0b0601 77
    0x4814000502d000b0450340442682404a0503480c2c910f081c1518400000070075400801130082d0b5a040c400800905520b00c6c18a10862030700080ca40d46185a200700b0028a0f034480c992000c010b10500c05070110b55654110303800d28102440d00b412598000c04404002c01c0c03038400051800903000c90780300c9507038040350003410300110b0716000d101c5940d005103c0b0f01c841800c050b540c00c1c03824010f480b513149640c890800041e1115030340e142134040c01c3d0b100300480701440003e044652115a200e803a003419204da47d4000f50722000811462035034802240c01c03890f0300900c04000c0081d189120f40c041e40c103c404c00da0003400300c01c1d03c2400c201d401d07583c1e00d01c488004a0f0059500100030b528150b02080c40c0031644c0a46282036a10403800c0f0898202c40100700f6031a8071100100150703d0100f10951704071a19140030440e18840c00c07014071440509204a003c0404040002010f0500038420f940602e50444142c1d4070516180c5000d440700040710000320f65407500000800c0c12035100d03110301d5034002004045407a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154588902 1250 154587652 154587659
    0xe090a08040e07020a0b010e06010210060b090111031903091b050d1412030406050403090509060f0f030c060708040905070503060112090f060204080705032401180b0d030f0807020601030309 83
    0x40c01c0303460081084040d84a500d05d2240064100c0300700e02c2c000e151254200781203040c00c0d00020b080000c1403410501d5542000014001001d00d2004c440342c02c27800342404010005d8901e0281d00b14010510483c2c0e0423407143c0d202d00c0049815821510b09a44101c4004a030b00308003d11026a175591406001d1b0001c055094030710009040748c503181400c08044007228015021600c05006036401201d007101c0741e030f4450007030001305504081018080d1008550b01211482c002c00440d401c0761501c0030807403080d42c2da0f0355140f00c80c0c1c50610a0300c0000d803000d0205a9600c1480c108190960f106218803013840789071000003045544100d050302c0c0502016950b000400d6070711142e0002910403160141d441e8000b03200c24000040c0c041c03008000501c141c40c0640289880c0070201420800305008000039111225601228007402c1000e5030306407080c00c41d880100e0301c80c52a00c0300090000c20140740e008912280203000745604000c602e0701c090002d40c5c4580d4241d4500d030701242c07554820b04c0020302040c1074110a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154590152 1250 154588902 154588919
    0x225050108040f05060403030f0c0305010b0a0f1704050a0c0b090a031217071e02030310090203190e0a0210170705090103091505070e0d08040e040227010e090a0804 72
    0x7990098015a042c140002c46511024180b1400b520224040b0f5950045460340691078040d12694503000c0c00c0c100130300e43c5041c0303622181d880783d46a4502002405659411403a006c1d1401c00c00c0e40381000c426041c0c5161a1528507039841c0f45020030b079a0045c4001001481280700000c9843d401c0001d028125003600d965a80b00c40100a824600c060040280c0b000010347c6001007524480c1c500b980d100311072600104000d44ca5410b20003050021500200304024400300b6180000e02201c2400c000140e0f00c0d915018140c010144406901d44020b0501c41e07060b5004900080103e11503000b03c0740c03c0040b400300d4001351640034800030350242580081d0006083d4074060b0000d01360700e04040c10003040c400840c1e510000100c0c07600b000c1c001244ea503482404038a035800044240130410690382d5424609850721a402c89001c0d501c1210200c0b4603280001d0115200c0303035110b001c2c2c078046100c1d031095034200d4503040460340000d00546402c04c0040000800801c00020000f9000e60442c4000b450b050409006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154591402 1250 154590152 154590167
    0x10e10080a08130503030a031e02090603130204060503030a0203040815060f22090b0a0507020609060a0c170f16050a0e040218030708030307020d050703080f0414120403020102250501 80
    0x8020840d0f001181c00115500d05000804102d1080d94001688034003445d036203150701000482028041d0700c18450205c564480c04d00301c0e03404c50703440d280f80010301c1c103d4070019000d042140c002a400d80004220100516000000b5209403500042a41d15a40c0310818502c42114100e418a9101c1168085c8405a0a21890102d420041800c2c0c01c1c031403460741c2034440181c6d652600700311920b519503410030144106520406412204520241c80b1600305413102681c3c5000140402400c180d0f2111020603960240741c80007080c84805244400900c3c141e0703556164030108517402c40d2001c480c401041e00941c410411114002001c2c1c41c3d1540400c000d805010080d04600609882080311583d41906960301704004001001da90b801560f9a11780030038000cdc20580182020320a200742405254000b98201400c0c41c1c2c408001b0241007075558942c200000100386440721008035000f410217621841d00d0b20402041035034000c3e02141c000380031003100b041064040c003e07421403d20f01040107109942c4140c65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154592652 1250 154591402 154591417
    0x303030203090709110d050606030705091e10080403030e0601080304091518020c070b0903030a0305060d060903020601080c0306010b0910051b03090a090506010c061d0601030b010e10080a08 83
    0x11030f41d07a1515840e628088803c110714280101d01d021580301c0c0c910310303c0d004695011209a420310300314241580c01a0650150311119803082c03410f1034108111080d280c14980d0340c5c403070050404044210194000c0c018040640301030700020305042d004206100002840b604840c80100114902454642d4681c0200620710000000c1ca00e20780c0c0008048035000d400c440406540140140c0d961000318043d858850941d012131520003040c021a0066907002c001d0743c40f58400380c2000708055480c00000b800100340c11400428103490441e800003451750000b441c41c1615000800c948101c0803800c101075954409115481d42007134200075011701414440300e1240900c41c5402d041d801d016040c003d00205102400d08003c20340d101045552061800101c1d8100400014400304018144200002e1201c004491f02170031403511940000c03403005040300496032020080c410b40d10790b0758580c941104405030a1140002200102c4007141c2500c05e289240b00c11284000010300c400c140c5a40c41d502c03660801d24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154593902 1250 154592652 154592671
    0x1909060e0a0e0c130e0a05010c0e010216030807060623030d111b0f030609010b01031805210405040f02070605070f021b0a0b03010605091503060f060c0a06140708130c0303030203 78
    0x5e000380d0840b0708002001e20b041c4250004500e40d48241c1c0000c05500d07050200904543c4a902105a03c2e0b101034604810b0f65005030b810360f80c6020a050038406003a00d81e104907201500c60708150f502204140307800280803000c42c00da500700d0a60301d201719400100700c85200c105421854000303590f41040f401020500e0b02c042c00c03640d015050031740040e0138150110340b4054aa5115030f45422a50f85c50300c1421414010f558a40c000b01200e038440c559540640c80d01c00b0000c4110f42c000f1400340403194140c3d0010301004105102c0c011001c60200003a410100c401c640040c00c1c6000b0031907035401440c0c6a90080810390013044c080c060220b120521070282000c0c6074102403d050042003594148c0003c501a025984070160b0383c0003c0014032140313030628800a0f020f6201401840075565a0607201070881600f10717a40c0d500e803916008030b1801d2014a41700140401e203031214128112810045c000d11501a070f031117580c00c82d618807160036108a095100209035159603103051001038025030156030000c0300708 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154595152 1250 154593902 154593911
    0x1005010b2d0c0609010525051315030905070b070503120406020f1b0d140a05070c0e0403020c090f0106050307112103180102120112021909060e0a0e0c13 67
    0x641000c90542c44062290207a4120f0303003c122011034240a065000045901d10b41c0200d44a500c06000810142003e84200400051803005008598400001400791030308402c001c0d03080345001034024440d10004441600507020700055620391441034400a0b0380050156240170480408000c0140005000310748a036800d108881202c402580a001c035064418661100031820003c10351412401e04403000402214481080c1044c400d4401d4070010403441c28000d884940382c1c9040c40301a02240c00c03503403088010b0001c002c149940000c203400340b414141c602c00225200c1502ea845101401d01421010450070404120783c9440350400c001407684d0101598092405002c7c00c4141c00c00e0003050f040d00318004000e00c03d0712420800a20b980c0a9840002c501d0030710035550900c054103051140c140c1407903030705801d541507483e004d41454418a00078074000e00c403038468186030000c0c4605d006a6201c0f07200340c0001121050b1521a04103e000c000f8014264043c0100802c990110441c0c0300102080d102d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154596402 1250 154595152 154595227
    0x490503010f0b130605032205010c09051e01030c0c150204050a0506040602070303080709081906050a0207050703080d09080c0f01061202180c0408010c0503150a0308070b220f051005010b 81
    0x603414811f80d00c128004200d920809070300030308411040c0c001d01d01c9072040f9030f244601412039a007030046000d000c2c2008aa108144041034402400000025009000411030603441c40040d9004209075070003101d00300b41c103948441c140b08090040f8014240580e0248800f800468001e0b051550310034082d18000c0099622031080f1802c100c09005110020300f02840c500e810007059004072540480c82700011810174000740c039019035840d210311003d441c400c40041c1000e401c18081d0800c0360501d8001510341ea80308042c1003090740d1203801024001165291002c041520340502c084d0b100c4140d0024244541c50314600161031050402503d40407121808102c0055074400070f0023030b1807909606494442d16841d00b041c500e80c0c2c0d211040c029901c20a11010700384000341c3c960f4141d071803854000e6016203607a62111021810070764a004104c01d52001c0303458100810580d10159071180348120203483c08813184010005c1a42e5080c06407200424041c001c0255104600300b031000688402e04030203020880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154597652 1250 154596402 154596451
    0x40e18011d0303040b0f0c0915301b030c2214040e010509030304120e0d0f12020f10020a02030405100818490503010f0b13060503 57
    0x500310364102900b0100801042c00140c0c1c6619910150b01620311100740707800c503413024061261100d014403d00c00682c410343c03070281a1095070204100b88000031083e0800804509110120007011240641d042c0001904140c6040420120046080c44681551035081200c4020380052241ea0303803018400000c01d810080c0d07503602000905958410815104104042c4070039140c130040f2000e05a81480c040c400540400021240d100e9000360701059484169501121040b000b404941e074008240040a01031115515035010302500c2610b60756200d004002060707848104100c88907030b1942042c00000c00f8001650001c02c1d0840003441a42e02d426207600020f6049c0c40c46008c0000003c1c0a9401c214a0380c43d80c012610402d000746009010041c1c0541d0305169250100f25011689181d502000fa41500761710a40c4aaa13074074a502c5c0c02e100921488010b140c0c1c2c109200d691311910003142c000a0300354000084410080780c81c00391072109402d0400640b010f80c000b404022050341c001d083d0803040314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154598902 1250 154597652 154597691
    0x11060103030e030d09050901050f0a0305010203041a070c050c0108070201090c151701030f080f090301090302010c02160e0604111b0a060b010e1c020102010209120106030215040e1801 80
    0x144a62121052481103405141c500502d401c141c00a105041750b080c42039076506180107046a8040b00d01039442c107482000308408001e10741c0028a158004001c1c4010000da05810f0180017100310144202036882c0841290042c03044580505982c011b62000c81865215081080c1c0c080a680000700e414521580d402001050b075034400070300459040c08490042d0750002d02085e2451614100e00078650441e200d03664114103901c0b004100100010309032000351114400d48248440040c020400c49a00c2c3c01c0180c00307001d0340f080300d0b001400380b6140540803080101498043c0c8003070f494500303003540d11013080c0401003040c100c102a00c80c106001d90701c031b80d03d0b40c01d000029201840020b025159894030305a01070301c00521005c1d040c4450000b44401940303078003104150180001c8809a81c401203030006034028480c0c280c80541100c10902ca408503044150400802c4074801d803612064952402c034820242c2c004c0c1d014000f021000b00c1f000c40d0f505c922400180c03a10148007400001d03804440710f006131994 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154600152 1250 154598902 154598909
    0x10e03070c08060c030708010605091c050a1703010b07020906120a05070815010e070c0f201503040f0b090c0a06031d071a1e04090204080d0314041101110601 69
    0x106041ca206010720b500c288042600000800c1d852811070030004809040d0740b030705000328820810301003101e020316511059206240c0c0e10380322040c0200c001604095032186c142c14070959424024000c03c84500a521040343e04030b480d510307021800c00b140365013008480d0b2806401990304c405040c0c80c3e8000c45005004001c00345202d80000d0801a01e013007441c509201d441d4003101d107004001d01c01005544142d42e0b4640c0e210105180c1019502c0c60761600e1000381d4098070001d40810a8601d102101c400c482c1c0c1c14440b0414120f070f07285040b401c046250b07403040c032003180c0062081030150900c000243c0e807014520741002d0741109540c03011000a0104403130408aa10060029480715002d5400c03200e507540700d131030040454000d003c40b10700300203517900d08031a141101503842c8000541000c1c0315042e0100c1c240c0503a03d01e040300d940c869540595002035003145c0905d1080740241c08003416214000e204490748116504840c0c50b0590721a1200780311100c03400045070500140c4268002e100d20140030aa019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154601402 1250 154600152 154600163
    0x7050114071d010206040f0204020d0e100b0301020c0c092d0f01170723040219020c010512040b1b0a02060114010507050714010e0d0305090f0103020f0d050405010e0307 74
    0x152600340001024600d00320b80007200ca640b010848035460764081040c07584183c01500c4e504440001d84080f800a02c500009950304500c4c0400d120805440401c500c08a0000f901d0b080c8210461002058205e00c564110354200d6030082000345100d0801c2e06c1d58660001442002516a01100510700515031588100d10b9030700150104100448001010b41409051010304040a1391882144c1c02c3c2d0f02c8915004281c4010421084030351101c81c2c100700d40001d040c02802c10340d12b4000407003010b0f060541c0300e0aa100507010344810036001d07500c00c20a8511014846100c1031b8251100d46481c5420040a072210001c20030030b03058951b041d65480d004008087e0030341e000b0f194a40c5800e245000402c144208a41005001c028070408501c0010701001a6200b1900d55600d029041005031075042040d03800d65004801100c240d01416004809805020000c0c2c41d064148040080114124851800c0d20268464244500b41000c42c85a01095102d4450400000d40008000301989940c0041c44200d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154602652 1250 154601402 154601441
    0x601022503020a141e130935040303030905150421050301151d10020a03080f0402131a0a0803040f050306070f08071e050a18140d0206070501 62
    0x450805030b002c2c40050104042d05600560b041e000900d0703000d040e900350265004010b0488169656020050000303e1041c1c5007044040e050b450a00034500c00b0010310900c10b0708c06520350300b0442c0011a402012680440072074640b40c01c5603410b90080001200680b8a071240c040c60b50826040c1440f0280264091040500d132252800030044580d400000110304206040c401006058441b26000d070002e00e6508058031090000301d8040d0b030f00102c102c0b44591010440000c0f0000c3c0c0c2d00272940314405406692811815556012450119202510002d400010403200111030400b15840714481c458031600070054001080c00280034090150499070050f00000340400c100d41055581d0001880b05401406d06071a0441d4007a05d4401d00800040501050f200000e1840303101d66992400740c200320b00301a0b800c0c003103440020302035000002da8101044400c40002c600645c6010084200e9a4002c0c000b5012464441404940441890102d0708018180511b200268080c003c60076a5060401200b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154603902 1250 154602652 154602659
    0x2030d020a0e0f100509060d0b0a0b0c0d020a030e010c1406040303060503010608061306090305040b0c07090b0d150c120f0905120c0c04091104090f0c0617060906010225 74
    0x840641c07907820b03e80c03094184c041c41c0d40001e80c0000980e00340c50b1007111041d45651514003040301603c08405803a60100e0280300104000250501a00d4000b003a1400c40c1c0d80210700030f400b6642c590001c40c01901040300414884c5443d8810b000d1140d80500c150100d104941c2c005884514112040d50101d003c82d443d4070b4103100f281424450207000f080c0d000c3c014009401c0040d1004003802e04000f0140c005512842e06109241c05101100c000380700b007800c1d503940c400002c10703c0c1d5115031841c02040e8009040000820040c03508010361112107800c9480038061510042d490310040c106c0341c801105005500304d420b441c00c00704d8420262450b0b910170001c110f414092070100d00300701c0500300500f03040c81e0034408203802e2440040c040080b031342d05490001e2018058100b0321091918044c105a00c40e050007050020009400c503181e00d850303c2009c580c0e00054440c002518070100c034031801c00301c0b03100c5200041d40a141080c0c65541081c01070055600c0025104000840e00c4d01404032134040840381d20040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154605152 1250 154603902 154603909
    0x50d0f141905160e13090209040c03020916121d19060507090b04031b051c12081608061906020d0f020d0507060b0109170a05060c09010215040302030d020a0e 69
    0x1581c455601402030001c0801040060000004206060b0041034190078a4171840c615500400b00e8a0f00103011074044e00c0d1a1401001c000002d00049005070780d1200401e4111b255800c00254814150b114150300140c5444420000e001d03a00f00c04010244802d80046075138418410050700301d44144000c0c8070248241420410307140042c4c188130410105000c00c2251100207816075040e0395100e0343c10a10041c7d000c46000c00e0004070741142d41e011003c049412400c00044540e041140e210b40a02441000d10050540380d03003408840340c0074220804178001c40b01a1045852039070000d0010071003c24400140040211000903802c404003607440384041840d416040010102084254402441026107000c1c0091460242c0d023030044c8081c0c3c9482d034203440343e801601e40c3e101820001468450049011241c00d94881e07251000b074580e4050764010070300a61103101107a40c2940180c000f0300c440129010000b4909100400541c1180400d00c000c07051818540010011f91046e907851a91905035807040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154606402 1250 154605152 154605161
    0x3090f05060906030702011104150206090705010912080c0102210c03190c020c181006090f0605160803040516050423060d02040510061b03050d0f1419 66
    0x252806910a010412103680c0c0c01c1d044451a80054941c26201c0d21041c105902500751034a0500003c0c0c0040f80220f5030280e058041c80c40c0c5a03c5d03038200c40c0c00e929252038258558125000301c038005590658140010350865403100852885256040d01c0c0c0910030b400c240c2280c004590b40307041c0302511100220300744021020540c0109821200070700c0e608010041d01c4081074211105a0005c5c1c8442030344d00401d00030311404400c2c0801800e044605c045004441406100032aa4211524484200850400c0c070038240d423010343d9080444070401d24109041515182c001303443d60b6003555400c9007500d00050303120000d94000e9110780020110700c02504081c20304240c258118500803840d0034041441d82140c1c000040c000104404200c081e40c4500010130303d480032100010703410600303100c00d22040b03104d124106003c50b0a0390b6240c820121301c0c1007002d00c140000c0d6501500083c0144944507038421503074031071800d20a640d0000a144a44082d40e01d228942c00c40d15803041e803261001f01c601c18803040c0034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154607652 1250 154606402 154606409
    0xb070b0109110a02100902010903051009060f020901051204020303041a03070206010e060d020d03020f030a0503010e0a0b0105030a0f021902030703021c02070e04020303040801061203030f06030305090402071b0b070309 95
    0x84007403c14040c803000a590300300d414000d0000580b21100b410540e40203540e150003075600107007a1100040303149926006040406c00c00c48440e441c141ca00300a07000903200b500c51540059486a01d408104002c51043c000003900c26a0305000803c800120f501c103c01c2940c0800640316201030300ca10305114081c0c00c2101c142d00202c1074a81010801c10169101a2040130070b079812101940040b1b420304007285480741c0088142884d10000030300ca100705810401840c12596204000301c4181e032001080307020341d56144c8443e800f0a005001107607000a542e080440c1c000d00c20a40142001d4416104014603800007078108003607003000400b01c050542c18815890404c4010f00c10101d002300300c15000b1b54602c1c06100701001800317100302040031507800b8000c40300104502c80017030000540b6107006058100040c038084011901d001a400f5012065014001c202c94240c0c44460030020030000f4003029502851040358809003001c04e08810f2000680741074003070b103414055642c80e403841c0c5c43c1c0649450700356003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154608902 1250 154607652 154607681
    0x80d15090c0504030809060c0f0f1e030705030f0a0c0203070906061815030902130c030c0906020106152609010501090b0406031e03020f011109010306140904110102070b070b0109 78
    0x200504c04190358504071001c0000c00e55a20f680c0d40c1d000c00c02c207424100c1055820009002c0c052071300410400c005500c0c100a030200503c01c813205501900281e49201d801030043c0207070414001e007041c0c107003a5800b41c21600d00d0780c1082c10b90800c040d400039007003941d0b03a04150850340e41c901050050540c05503104600180c0d440d00c0000700c034103100b80c005180c440d9001c04030400da1607a50b00d50454070342c40b50100c0c0d8031150401c02e0003013404900000d40a8091040e442000602520b0006411b91050240b4400c980b80071055512020401104032022810304104104104007408044041500503261a118100c110000a46541000c1d8120156040320450511480c1041d10501c0403c40c038006480300c0708104820010580500c1c50300364200410000c1900303065180003034100c024440480180900c03003090340d0801c800b40c0c45170640b110f0000341000a581108110000a0016113141c41e14400e00b0340500484100030f44da90b0503140780354000b4008075546014a801003059a245002e180580103521 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154610152 1250 154608902 154608907
    0x115081303090311060f0309010207110d0b010515121005120a030230030a0203010305010f0203040b0f04060204080d090f12080a0804110405040303050906010e0709050d080d15090c05 80
    0x140c41c0104041c1c9a0b0001800e110180e40c1c1640043d5581400c4074004814007920903200d1030901207241c000d4100e000b042d11040350981c011411450484a101881c41c6e00009100482c0d0030039003801960441c4440c0c800103040b04010700b0b2504122813000130311641c0499054004541404188584a049a004e0283d2940300000d103000183c0c021810700000c44a00400804442c140422065911a003440e4000085400030a100b6a013055400442c1601e014100a0000c000e424036080100d01c021a00030301039010010100308107108102089400500406000d4242503e885805090404001c08000403910840040225040000041d0018020f141c04080f003100c0544411180303100e550000c40030070500000090800400d600c5101d0002070103881000300386000e00c0d010b00240b03415103810b1424496640002103051040481c544101740540e1210742043c5880207006650031501411210801c041c811815840f40038854001501c2d0700d449030282d614a0040a0700444d44414014020410308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154611402 1250 154610152 154610191
    0x30306031002090d020d050a0308010b07020a0311030115120b0603010e070b0703050d02071515050a050609010c06110a080c0406050f0a03090632010e04080c070e011508 74
    0x100304030880d1210144050f80d2002a8400a8000b603180c08000f5400f8280954501c1031100001300c140c8810701c43c0e100c00030146d132580c3c0040454010610000d602000d80c1c4400d0000441c668090841c460740580049044090918000782c400c2c44c47e005084003614014034a414040c00d245030381d070040803e4000704403071501550710f42e0701c86240d03004020442c000054007104051046003140e003c9100c07090115161590f43c0f80815103405800240f1103030070304000940d00d54525290201d002c03500000c1c00780060f14a40810b00800760410108036051010b0300300e94202107103460090845c1c01031040d1009a507041c00450180103160040e1519081d941d051206221b100c1c0c00034211000b5240b072000340c0f5190441da074021000750002e031100801a030b041c5460044010032002c45103488480c0021098038000400c1300300d1821b12400d1007140c107140e9101c00401c0105801000611503003e80c1c0050711a1144c40c4c030f0b03488100031800ea00c101d8a281220a2940c851030784a2041600110402a0b00c1c0340401c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154612652 1250 154611402 154611409
    0x915031002071104050c0c0d051305010f0e150409050907091112070c060603050f07090b01030b030304050402070206070b0c21070e040c021f1409070f03141519060602030306 76
    0x100e00b80f59a004954500200301004560070a80e1540c0760030400725090001307500001440c54110010300701c0790309681e51000c146980240140f5184102030380d00c0235200c064a0042209250701d20b032851000b083c0801c00852554002d0199030b2060800c0e40091501a140c21022030440b8400c800c00e2584d10400c0c4091225262103845181d00320426191035001a0002e0400b80c6c011302d00d82c1c0c8028a03d12459141d83c00c2d0781c2c1d02261040480e40c59000800400030840015820b40b41210324403a4503420802043c066803130300d60f001c0e000ca140040d2015081c582c040c4c0c0c0300803030041d0035035200e10840400705441c4000c110050403c943c0300d01c1214000a2070410500152411103c4910707688181d45482e110610a4420031070b85c01000e02915107044081d61001c620401420703c54085207010b0700440001c1c0e00d0350b50020390300045031401041d40c2d400b20305e9910750040c0c04640c2c0c4100000c0303000e0000c8843c0b01c0d124095072180200d691980b2071410388103414200c011a003684d4401c5d41990003d2007009880d85c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154613902 1250 154612652 154612673
    0x5030705061c0506031513020f0312040e1308070c0e06030106150e0112050c040602060a051312051c1a01030c020303060f04091703191109061602091503100207 70
    0xc0d41c00c2404030f419181c5200007824414110859444903880500704646200d4812815046500a075070108082c50f0301d4041c561070702c40d450803d10b00e600c0200300400c440c04110301c01544c0801170002a24a4050a035241c81c0a03900080040d9016860400c0c10702c01940d030110070541081c0102c00030003034945803000410340c206200740403509210034004c1214007a4061841200c1020301c003003007000b86190207180c068490b002401800010310031140013030300c040c00c42d120b600e009610709032210f80130b2501540c840c072400160341d4502c420020240700391000282c019040c544615010b03580400e44003440204000b4044114000c58105820400095541d503004800c8076008041911014481c041c1c880200740508a240ca00901040e12485501c200e01d0902e0090340c040c0004034554060030b071006042106846a020300010019410042c0a4581c9000c000400b00075518200c00310406040b500010000c40742142e0285c2800c0001c0d074070400600c0c0920811240d002160402c40c2007007220341301d0000c0722 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154615152 1250 154613902 154613947
    0xc190515180a090e010e060f04170408030a02010f0c02031908090f06010b0d0606090303090521010516030606170a02160503031806100b070321060603060503070506 72
    0x420009181ca00c0032440049070345240002030600400903a071008440000c0150101245655180c06005001120042150750007058941c43c0c0c1c0c072490301c0d1500d0302400c02002c1e540d589030b554410880021140c4041c0090300b180c0c0324a800000303034640c04001035002e4a0891405100310341080003078a21203860501203460311403240c40e100f801e99980c0c0b00302901d0310040c41c0200c1e02e9846800c1c00001e00c116144018140e200c040344051003104e50b103110542d000c80540c04024041941c0d45414002d0f800d03da0064008056052004d51307200c010064842d08445043e03400d1813160514820040c603103601030040d040201a00c1c60001082a500d07000e0106c080f6025044204403500062100c5e40f4405440103004600c0d0018256507403810f1600005d282c0710b40808078100640240300c0020320895990741d800089a03483c600791490b0030010741c2d0071114480703888003034403200c00040d00c80510b40318180328117400303021141c400282c5242490101440c2002c80d41c45035115280801c21980c459803107108c0f0b008403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154616402 1250 154615152 154615189
    0x6071701060926242a03040f060605040504050a17130b210c0301030b070e090402130e0304090c08060603090c1507060f0c112803090510020c1905 64
    0x91035040500908104421644440780318442c40313402800000b007440030b4092002c80042804101c28503008a40c1280800c080c405c400c0c00520000b00410485d86071503160318400c440000d012501c03a40042c0031075805490a0351f0030f0f4041b81c0d101d02040401104005190f01a050160601451290700a0603a500d802040000040461084901408510701050103039044e52851403605d828000c100c07141e08248020340c2c118031680d0106480600502030b11184032000350584803590303207d4080c01955484051003c0f0400d80e5a68003c08400c02440680090483d200300840c0f40d504e6490000c0030320354050100c074404d00040090080110002444810300a010390758a481c1031080c00b5081104e0003008400703840c03a805d0030380340c807080c10b0903621520342e85030f00ba100c00034989907040b091035540256281c8290b038880d0389040c414402404420340002d25102e440e028041984410126510018404400016a0242c0b03200300c418a08043d1100f4542c0c22541020b58081c600400248021551162005e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154617652 1250 154616402 154616459
    0x30807032f0d11040603090210030204030c12080d0515030c030c1309170d061502030a08060f030712080c0715091503020912060103060b0a03151a03060717010609 71
    0x20b21040c2c1c0d0f000490341c1c00395054000d880e81c3d62a00054040c3c1030403081281710380000ea224041c0703240240309071019240c10091b00d001e503604260602e0480c1e0348140044d00c0180c41449042c0c0659514002c041c400c400103500005144003030024145019100d0000034840d0300b01684103c400c0d26a40c02c2c80c0c1301460a64804519a095070030b00c00c3d0b060804842c0c2816170400001c030191340c44001d4205500311400c0c0901e080c8104800a400c90702c900a1000610000b088000811002d00e400c1d580404a850b000b401d84481d240c0d2410310f100d0344056075038221030440c070210310303907402410500404009200f50603059000e4104003800801c4404240105183d240551851220142c401d60581d0800b0901520310709450300a000300e20343c0d40000348411900c0701e041040d014210300f000300300b660880350b02c0914240b0080c82c0d110028013130040708041100c0b41100e00c041010a5074200700b0300c1d0041c102900c0701501c504880c13500310315a01058000380280044402d0412001d16840210003440c01c0c450740980 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154618902 1250 154617652 154617667
    0x510050c04030f05030705121206010e060f160501150b12070c0b04030c050606011404031104020717040305060606211801020301080c031902030a2607030807032f 71
    0x300107000300d070400b9000700c20380249442001000070003819118041c0084501c1d1040e00305e41040d0303611030b028507400310760300303c0c004240c540d409a0210314161800410a0741480314610003002c20b50080d800308840750b4540f42041040c40380070720074441c00d00b214030211a000d500b800e204203820312034641c6a11344800090000303180188a0030075400b21030b900c50400b00260516041c01040085006801c5e1640d001c2d0001041c07556002e01e081c010000c044000d00c0d418a0324549401d694050070031592504180c0800a4000107039440f1100c01000b0049482691103a045041c010702c1c000c0f00a011601940781000410100c0300081e01c4944003454803d81001603650b41c0d8401241c0075200306c0f04060541c008400820341ca4004074126003a07600a030200c030703085544603c84200c0000030b0074001c4d415402981000700841c180308030300d4041d4407000c8010701c11405034403070700b1ba520380c40504290700140c03071441400b00c82640b40c054000012942c1c2d02000403200040e00007002031410824800020130b0025080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154620152 1250 154618902 154618921
    0x30507060b0618180603190c0b07120f03060308070204050a020c010e0c1002150c0c1603030504050f0d0215031305030301030f020f09070e011409040f0c03060909051005 74
    0x1070031140400341074152125a10203a02d40400c003c1c2d002c00e481840704802009003102100012071207414020001c02040a80c1c0c00e0040c0c200340c04240c16502e5400042020400c1030081c002040310300e21603401c03545e081c032111400400c3c900080d18514101400e00380d003007021a03114410b0345c8030705030100d400045580351580780800034804c3c0361900c0c1d100e500f400c00c0c0d4683c0720408101902403000030788850507000b021007000c90300c0e2101d0321000c0c0c00051561000c10500501d00001c0c220000b01101115401c0005030f41150305101160f00c103c0001c0e4000500380020b04043e03114441e40d00d0300350740e44000f0b10302907400540f4403a5a0145048103400120018480c0303035115405001c4207070002c064983c0ca58486c1007a81501d886018243e010380b4985046503494103000502a220b42815920b0201000c1c035a1700455a5101481020607409002d014050955a85c2e00c80e1140c2c001e140a4005001c095241010b800c0d192035502c0794001510303095001c0042000800d0b58410203c812900103010341c2d908020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154621402 1250 154620152 154620161
    0x912060b180a06030507080a020619091a0310061103070f150e030904110c0a060e0a0804090e010c020309180c071b0e10050a0506070303060308031f0b030601090303050706 75
    0x1c0c5250811120140848007038150700c000306480c010b80030790708002e03154905182c0d02c0100f0400290483c00070428485101c800d0702c50341089064510380b40840382d0780c50084171008111190a41d204c802c000083c131102400b8586010000c00645c00c1030101c003243c81c0c46039626070003003000140c58080400c1c81907003001100554011007d02d03108040040050710010580d072074200c0780d4014003072454030400b00200c04c800c100742c440d541d1a54008040051655076004068a01440503036807905c142162000007075201c074003403c0a03101451000425808900400d4217480c540e000a00c299007040000b036050341c5400c400c8912071140340c00b01115030385600d5840204ea1141d410058140404160015916540018604111101000417081c1e6480d44110b91080301d0300da100b00c503400441d04004118508140000d04074403030082c103000403015500d48030040664070444914012402540c925a0072112050750b605c007400005282c42c6c250f19000c0c0018202c5103140c08045c06020002c511b10041100e280c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154622652 1250 154621402 154621429
    0x10b04020c1b0303250302150c03040303140606030a0b010c020a060f080c0f0403141e0c011211030601110f030406050d181a09030918010501020105070912060b 70
    0x115581c08904034195100c1402d40e618211441e24104441d91915001007514400c50301c00344151890b4020000c1a910148a01011001d60151f1040700300d0740d00c40707018600d00c5000000b845660701c0c41d151400400700c230b08030711901100402c0309003880a01d448030016240d008108120004002c112540180c0b49410322010096122182610100e030542e03000712001c1c40c281f0b0350740b560800c94881541382907450042d115107002c449814002080480c246203c640d10842011068580414142900700c06603d42e00070455415070201c441c040255038445450b24130b00c0c000200c100b10075160800b03e00c2d80d030301c0301402080c10045500362090b10090b091086205800c81c41040329a129900c3c14041c1c9207030001c00c3e6031800304c0d1030702c0940b4444034070852103026820307030014040c20800788001c45040c10241c06410048140b1007402070155540b21000904100320304c03c00b40310032075850140024251080202031404002c5003000400074001d2400a898807168005c10206405116902090180400c0d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154623902 1250 154622652 154622659
    0x6030804120b07091215091406010611030903070e04050c0a030b190209010c0f03140d0518010c140717040e040c09020a020c010806040207020603160801141011010b 72
    0x1400240c0035140000510000c0d00c9500b40b41c00310b42d07030a10199084107003485503010b151104115a030000703a183d4032030440740070400c000081544ea1070f02c5c1e03280c106d00d403080c20080a9001c030006200751604480401c40c564120f200851034801381c080403035114a50b40c400c00c0c1c144a0310502141c1088402e03c0006540c0340040c020002e02e45e603c0c10009500350095a040d003005030400660034107500d85c0d008403001202e040e115009428503903036441101100001041e4100161464014548100c400051110004072980401d842c1010400c01000c80800220900180e00d00440c503200c00390450341d41d003100c0e120003191545813a85d0b801c1512600b0f480428801e05044002070202d50300c204c41000710700803030082840b030350480d40346c0140030202d00c5142420400740c1d002000c0100301d580f09500c4960310003800f80c0007605050803a8040b0b001e83c0c00c15078070f498817200c0e4040c404005507070203401d850050003500d1008007038605020200e02141e90845050301003092041242004400c250820000124080e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154625152 1250 154623902 154623907
    0xf040f090b041103031326030a1205060d0c03021c0203100504120305040507050d03200a20090a0509032209150b0d0e0a06020a17060117040303020a03060308 69
    0x146072100001d1011201281c3d000c0c00d010710600d00d42000010f1b0790b00351b6510503100010300d0900382080e0040c40c8642e41d43ea203841040d084418003900c20f1001d0182040c480d101c14081460096a43c0c0544500604c03031170040c1d24546611002c5500042424203c0b03406449103060101c1f1002c1d11360040f0141c4030301940510490b444001ca10210303600691044c0d0003441614058514408100e065410544e009811907204040600480c544940f443c02c4152003401c024090003945001d003002044545000c05032904281d4100c014442d8121401c0c003010000b4152540b40e208030400190341d4080500000703140e07562400055a00c1e00e007001200d500160261080c1940f25040b00c4804504d07415004551286003030100403019813441051000954140e404910b0410300b41596280080145002124080c440c010110012807010701c0144403540c000e542e0000100c942e03847d41171400314003400301410048440034001d0144140010613800c55070514000d603807100d114604a001c0c00d4150800341520000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154626402 1250 154625152 154625171
    0x160605090d0801050315150a0915080c030307080a0c0602040902180102010f02070f0b060d080307030609060f0605031305160815070201090c06050a03151701050907060e0f040f 77
    0x40c014900c0003455a600340c00340e03241c4040c0b50b10390040305510b0b0212900c40c00400c5001d402031030609034402002e4802340599944070004825103400507419281405005818028000144016032054100b90001c61074000303983d4540040f4072030054160200700c142c0c001d84040210f107404032401081601c00a5482d401040e401418040030803d49a001d9807030300f0000c41d03501c004d41c029190760035005283c40c091600c80d6200c0c2140c1c00c40c01083c05074415000c16000000074000c0010394042c90040c2da00007125418102100e08840c0c450f0840002e81800020400000f0b80c04070031258131400e1001c9100100106146c100d2405030130b1040c260f0784404400c03001c180c1600005502d605841c00d040c4160240d10385078020b03800c8404044000d040c0821381c1c1c1d002e012040c0950f00600e1940464a070000b9003d10800c0000184513094200c109800c101d1342c1c0c548086e840900407650402c900801400e04c080c0b4040015000007a41c4a000c1e02070f8510045088403680d07235501941d920f03c0d4880d4140b010f51030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154627652 1250 154626402 154626421
    0x170903030714010c0f21020c0f0106030c031208041205090310020a020c0916020706050705070f0b0a0201050a05071d150708040519030215070f02150c0c12030906160605 74
    0x500c4c0c8810000420000a40c001103218518040b0052818072010104424a003040c002a60283d80d2030340d102d11a9688480352030400f41b15080007540641800b0018038110300c5c00044001280182d0001c12030b04405010101e82060f000d244d28102605203507507034003c0d0401007800c099502d0000a1418404616074010319000716201140c01c4044035550080d6a80340c219030310140b0380c1108000141d0052400303000c1d0500410082080b94080c204031405c807507440f4220790021450740c0115a00003002301d90b00000c0d035024001e80b500440b01020a20040c41d100c44010701c0d2034402c080c4442c0342207156021880d070381c64003180c24003100040700480e46da4000c0d5050411040e4401d00ca9103003e40e41c42010056000b090040140a49a0040240d4056404e03511900b000d908404003d5500230305410207040181e030f0320310300460000600d0303030800e860740b550700029418000d0300c56055004a554003860215180d0210484e8100340b01252050386074450754500d10801f00380414005c11907803801c81070018400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154628902 1250 154627652 154627661
    0x703060812210601090f121a070c03080601030e12031b03070c02090c0903030703080907050102012a171306050a02040302061c0f09030c060b010c17090303071401 71
    0x515000441d940a045020244080d2140b510903480100c0003035841c09001040091482d00504149080f034141c54a507110030180e091264003156050319280400400c110780410f05a21240394101c135040185411007000d01000f180e208020100040c840001c2d080d60301036401007080300c0402045490380542070060f990150310689240721400e1005038a01a507811540441e44509191b680b60031064070750b0380c20311004010250480c00710040c2800b0409480d1810805040c1203806680e07088007504000d52800d040543c1c1390095030442e41012003240104000b20140c021001c004440c12011646116045480d94010811355096507519002e0150303400709100700907034903400b401c0308002c1515014a0481207109a1100940000d028400d03481d07860307000300264121030342c41507000c50031174644008001141c240440840114504424070820f002c218840c81060907000e00f892641d0202a88665201c0c00f0346a080705840200068900c90b0f64405200f62881c2a40c0845042d03c00001e480300c070390281c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154630152 1250 154628902 154628909
    0x1060f0302030f01050405150901060b0f09041506050a21150e0109050610030c091a070c0806091207140709020703030c0915050c0102071b050a0b0304111c0209070306 73
    0x24450501d00a03c003075010312401d07000c0c40e41b0000800ca090700c90700e43e07640c02000003007480d26075558948000441082000045c100b1014100699503654401810041203508160010751403007140780d0700340103072604041264000fa071141000714100c4015000e0b800001001c816100c0010709040c0d030036800c44442180d00003a1442c0741120070041ea29400060222507084403c20380c03020b40750310310084e000d0082d40b000002c0292840c04200c80ba80f25107000b0840d01290302c20880e40b00000801d4000c0c44035080208010380348800142038207042c280b5240c0d9945001200542820100054007030401005040c0395000c000c05d0419111110358030142d42e0029080f04009601180c2000900042507210301c1412040d106010b04440c0100c481354000c0b183c581007102e424455650030002c90001c41c801040140305411400e0404203003034100010320010300c01d00d41c0035847c1c04000b482800700180396030303038590381142003620168600c810003600c00150106001c8069000401c1405000000d98140c10101c282e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154631402 1250 154630152 154630159
    0x1027020f0f0304021002010c02070311031006081e160306020c15090303060406050405090d0f050f18010306060203040e061909050a090c050f131107020a12020f01080412030f020c01060f0302 83
    0x105c0f10310090a9080c1c52039452040c0040c2c00c554400d000041d203201031610002d5014040318407880140422008642454000a80e10f6004030046400d400c8507810720110020f182d405400078203e0605000c800b001e1601000b07104a0300894120500704040124144202660004400030b0900c034240c6034982e802540c1080c012401d0600c08941d50605002d0300340500c2a582c0207003508441c03404100c0d40088901c0c21801004810080d07031480c004080702802407414070f0a10301504a0051001600301c0e0b01e250300c42070035904103120400c0003d40c100c146a5201a00360740214141030501c0c00200c1120007900152242450882440200c00450740050321f1640f044d202d181c2603070340341c00810003540c203034081c40d6601007040040750082d80da15130007004100c1d0800e02c1c031600380111341e40001d419882c941c100f150401c0116542c2010f41c0340c000702d0411480c0003030802e1209400d0a03128000d890300030307401000603da20341010007440381043e030450b100161002e00802006031a507401c1b4050640c02d20060f0b20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154632652 1250 154631402 154631419
    0x36030a03031a060703020a0605040c090c12150f03080a030b0a030605090f0c0f0103020711100203180913031b0c0807050405010e100e07090f030305030f1027020f0f030402 75
    0x86007407003c111040c558240c0c00a01d4000102d50740c802c0504001001201d50745040e03203001541c0c2001c3d0045400c5190141c90b041c90b07491000c50800100d481c10070b2541340b0140446000c00c420061700070402c040e2604246071960b04e039010740040c0c000d080c1c0740400341d8200d0300d11500041402101d034800e9003d40c450030103442e091580344544990365610814035590014441d5240c0301258003a50042220314030030030b421404050030500251940ae0b0110050000d03800020705044005070880e807020007500308a40311421820007450038050b0b2010000010240500314030000d54131103002e110b000e51a98480110703005503803183c00040c1c0780c018920030b8900803030404c0004102d2504880881d0710619000070304101191800c3c040f0300300301030058110400e210f050390f8049030b40c091303444086001c0e40c000d0300d03000d590f4141030415030420800141004148040b43d0014800c845007031380006010f0182c3c04011980d40c11030440f1000920901d101205005000510344001400c8100550710a5008845018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154633902 1250 154632652 154632701
    0x60305010b10080601110a080c0a020901150203030f1e09031312020603040602070c09020309150609070c110324040303060b030906010b0a0e0306250536030a0303 71
    0x10541000c2901c1001203010a0001141e179407007440c080c94400c11440888400c001603032100300d042c0c8e000200300ca85640104004070207500702215001e00401141c00c0c03100c0d400852940094590001901d5008145071000100e041c02e4904008001c40c0380701c1c004c00303103042d00709400400e95031790002c8401d200910300144001113800b0301d1708442008a4025120741c0c5582c0c0c40f42d48890080d070240f04201c40c01109201d000c02c16444a10183d84950166002041a044501142d15044e24000c107103030b1142d040c100c10008120362013554821242c0c2d22400c6035100d110400d00103130501c0100d0041e041e28000304000c51070602800301460380030380d009031010054681c4901501400703101c125143c50040e40f01200401800358003038010a400c0b10340340303130101c0b018840c42d00090031f2000135940501c0088e80e402119600300c403240030300c0c1d107002800d00f0040e03e040000c000c01444008009034000c1d100b0744000190803000c024a0039031070289002410384000e1003c1d032030081d000f0071011450448441c80100d004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154635152 1250 154633902 154633909
    0x10302010201110c030438070606050d0305091912060203041a0403170c09130b0906041b180e09030a02120901080c03100305030d1e060608010e04080c03030109060305010b 75
    0x1320300ca0030811014518060501d0500b620f0403408000001902180450005203c980d400350003c00300710003070459a841c0359a04005003a0348072600454400d215050302a0000798000c411909042c1040e207a44100c4000303040030810b084001e50282c00040001415542080001e900443c800c2d803003421403c0d0700e0940880f80644a00c03040724000d0100d4000d1002420100c407541c00280d000001e0b600ca50f281c561444040360341f543c814001508000e0303d0341400032861810310f0300d0707a5100800390f0b0108800342046141800341040ac9424400f804403002010080480d112110b0024140e602c03170b846e40c94100f01040c07a5580e884125804014001e8070200054034490800b2a001101c05130b40360038050b00d8000118a450b8400341c04008090b00840c0008001107062001d040041c0440c1400119114a40212020500300c5480e89030034038a42401440070a403c8000320703040d40e109100007003081c0d0707840c94801040d1003000701c5030081c0e22000c0000114401c05401071800e0f01d100700020300658000c0402d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154636402 1250 154635152 154635157
    0x20c0609070501022d0712060b010e22090215121003020a0311040f090506092515020a0c082103040b0a020c010f090605010614030f040305090105120f01030201020111 73
    0x8075070050304a092040c24103d00c0640781180c840b284e088501805c20030380c042a1400f001d95220081003401e0b100b2074405d210303191162006941c4203003055040d000c281000038440b00400441c0ca020314040101c40094000c1d6544031032051a0301800c410a5502d410000110355000031103c0e400380c180500c0010812940340c00414222580a408213202e44d041d070f540c100c4220030300c5101d0b0fa040783d41c5a80c0c001e03103140540200e01d840c0707009902500a500302203060904082031003400c0307207000e0070003401d042490404614000844107041c51014400c05190000c0b8103251524001409074281e480340850246001f0680d10100e400b404120404000440403404060104880c0600800412000641903500d660001c046444110380006a0100541e902008444501006650444d0341e0401172000d9070b0010b0a160a58145e90106801e42c031341800703840700b0018020401020400003251460325640a40151885c180782c031030240c1035600d80840f4400284001744001d070700540c2080322000c1c001810108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154637652 1250 154636402 154636409
    0x90903040305030f071106070f030e04060305071505040e160207060e0105070204090302190501021306090b030123041d10020c1b0a210302150105090415090605070201020c060907 78
    0x914185134007074040480903004501d05560065981c1c541d40000d684080c000c0001c1846102ea1240801c001d0400900301d940c8141c846000d189420001e101040002a101e000c444028192020318510030500703c40b0f90080754010321000d044801481039400b000b100b80042038030b5580c02c0300c20b450795030101251104820b07486c45000c6101002105c0143c10301f40c2002c8003c40c064011101e200c80d4026030080700c2c509098013510240d60100c0c82c551f0600440410380010805880c1130030b02c0074142440c0d61a54401031140c01c01000c0050b000c000e17a004002c844080e4a100180100100c20360000d200070a129403a02d103010500a807a003240c200e00f01482650100d405c03113802040b814000b041d003107610f000801c80382d80c0c2c8505028400a070711450180d8440c070903030384060b820101d0010703840c0182c608800d000400c001c102d0f03040300520064a070041084c1d031064004c03e030401080c489507642c1d0000c004581018207407e040c4070800c01d1407501500205154008181242d0761684d8a1505a456000350b01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154638902 1250 154637652 154637663
    0x20c0718110a0815010e1023040503060106050d0b13320a020a050c0604060b030d03090b07030209010302190504140603010305190c0e07090609060534020a0308090909030403 76
    0x308036010384100c1484d07004001810810384118960000a55240620040030001303a0040001ba05441440001481761400820111709240c2440d000a44584c07050049400b007003000318000c101c40788103401c4070050950140030703800c41c06400c280c000043e10400203003c028107041c8403101000c003010300a40d02d112812070030406c581d4444040110295110204100c100324044c007901d10944014007456001310721444002445900550038182804801945001410b00d0001000041802c5844099001c4c81c14940140d85440300030059002b0301903d03a904c00d08098415084503480c0d0000024819540e03050101d449041481c802c1007501e20013400003d0070781c3c000c040e11029064080302001c0f001407040c1d003c20704441d22403400b020800003c440704400a40c090204000e01c0b500103019401a1413145403c902d81b81c0c00e84102ca50503040c007030503410001c0352030030135500a5001c01c02c91603281e98000d002a1100d42c1da8207040406402000405100741010800314406000c00412a000c03a075000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154640152 1250 154638902 154638917
    0x1a03070501050d06050616030207051002030301030314040314060702100902130b0a030f0c0617060d0f021f0305010302030d02030309060c0903030f1b060a15090f020c0718110a 77
    0x100448043e0030045806810603181c1801082d66034610703003e0410705004102c51403610300035040003403510803194040ca0284044240032980298040100e9065a805003040a8007075210b10031207034284140e80c0301410051001f050042aa040030640c14020480d580c00c884142c01c1007040355040703030708500c0003d5201c3c03036114801c1071609642d0018054204001c1c250101542e0301e0b121003090103c0ca40040700d04203040302051040e1500916000d03120355801d030680c6198904200481c61000402c0e1000d0400000c0408a0b0700f113640302d516505000302c0000300d001001b640000d018001e40401c1c00f04911074001d900784031403124800010340780714000e100c0040c82d154440700000003442e801040c41907014001000b01c201c815007504000c06104080b514040031482d0800311042c1000f6025240c07880740c0703003080030b0a490f00034081c0d0a04161010b8410004a5080003400c400c001d100d02c0001c818a801050000626140002c2c01c2c0641000d14038010f1010990f40c10308050a40b082151b1900440c524 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 154641402 1250 154640152 154640159
    0x50c0d08060406090e031c14040222020c010c0908210a02070302041404060e060402100f020c03063409060c14061815190902150c0604061a0307 63
    0xe031444940211000c0d1000624680b00c010403070565564203202a1264400a80d0b080060000c40740c5805111546804008031186130107080800318010380041c0c170403212240f010310035038642ca10814490b9611003085540d00101000ca9000e0a404ca03491408a1520800000c5078a404103201d00c03441140f40c28012071541305580d0b480c141c0c00c501888030440c030a04802000680b030b00c0c8913640351ba94480138040350303d1502d46856000e54101000360b810907040241404016119402c00101600e1503040c5204202003d5804078034107002c1c001c0250707240c400c0c1406d229560003d0745001540140d011020b001603e101c10340103a100c116a0312000000b515001c04002070b52090018600d418440c4c40d0b08134501034104d41d11403501c20251220785084140302d04802802404210461680700001c1d513928440c40c1580c480e030054000200c6204045440d188110110f40d0340034a42c410a01a0036005600d50a00d1603800d50b85101c2103504440c55440c010000c01a0364600c080095407000c000c008207085402c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 154642652 1250 154641402 154641407
    0x40201030c1103070605011701020705070501080c0d0612020f18040318030b07091404090203030f0d090503070501020a1211030a11090a060c1a04030504030f052b030507050c0d 77
    0x1050762003804000081c0055040c0400078070007451010f024501c00310f00c950400f0307804081c40200100c4000641c0c8100044800030307901055410481d4024240811160f54a2405622501c62000145002803800348081213944d0303078250b0080d00e90b000303a80310310384021000305003d4002c003910407250401c6441c1000a000078402e00200703400107000600640c030740b9a0b0340c1d28043d0b40403050b1016030207d12100c2050140340d202110403a8400c40c1110f0900021351a030300401c0d12032003084c102c90484440040c01800601d410b401c080f0710f055101003265a07510541c00e0242c005e41029450703400007040300322410310700b145602944c06a01d2a882045145843d50b9820400a01740441c80e008a1501070006510710754480480d80001c00c481e46030100c21b0062803400340380d01007a0b448101000440c440034007002c0383d40700042d101682c3d40f05103051183c0c2400d0520516001c0d05100c42c0c1e041030380b440790740d686403400c5480090b04d800f03031078809100035110701806480394001c2c0f000300c41c0c070340d03025106c3c141e0041d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 154643902 1250 154642652 154642661
    0x1021b0d03110301210b0f04051203100e040c050303070503120901060609060804050f19050105090d080718030c0b0d1406010f0c0c0807031406150102070504020d180605062704020103 80
    0x203507031200030041e5600c26038441b0450364086038004074207141c0d4003c00043c0b00d011b02001e5a012500d00b40f0ae8610b2a24041580010390907000d000d01c640d411400003410080c00d02102c001803e4001c0841c0d40300c43c40791600e10b6607940040714000848000401040091070140156400d64810b900c6080702c00e030802c1004c84a0f5070b001003044d075651043c040c0d24500344805002814140004001c0120034a01c1ca0900c0d5007901d10150001341e1603440720914003001d03540282c626401440d20724040145040d00001d040c07403400b0355080a800104028400548081028014500c4554a0303405001c0150607208000300c03410100d60300c07400b01c0c10403415410300d14031a85160518a1289040e03680254640e162245000c009410480342061641d038140400342081001382d80c4407000c800d12681c100388150000351112403610039240034039000b0804040c00c102c03d0b04148503544628003201458080c2e810400060302050351400d024100c03070b501d045150752109404411842d164030380c12600c0d0b2100d0b4011070041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 154645152 1250 154643902 154643939
    0x305180402120403030b10020f06070f090e090303060f0102030306010c0605180109111c0c0b030c0903010c020d08150108130804050306100f050604060f110c0301021b0d03110301 78
    0x107908000000d8403207694800700780114001e540001d003050112082c1724a04a203591114255846002c07601010070001542c580c3c0714a1742d00d0821a80b001800c2c05641c0394206401c0510744401420401c10b004100101442c8990800c07110b52070183d0580005a03101c0c0f00903a5210f000906007000c3c01d01040d00c5411050b00990609180c3d241d0a0000074154219800b2850440e0200c0000da2040098a0486c6581c0000c94a240c103000042020765500940b400c0c00344240c000b84400400090002d42e4032805a07501080060002d1248404081d4025201c18406003200d01186410020483d04020780d8580604420181c44e03000b9140c507601000c01540c411420107c610601c100000316843e02d0a20030103025000c9488454070744c504100000040081540000e80191300501082024035840707400304111f000d4a090403202a5a501d031440d050444114101d501580001001078661000c082e580d03080204a105542000038019421801d844a5190b850b00d049000d03c01809881400450f20561 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 154646402 1250 154645152 154645159
    0x131509020f120a02120c21010f06080606030f010204260c030109031e0201090b04260c030a030b19031502040e01090e150f070c050a06020d020405100903030518 70
    0x7201c0e00007001909251200700c00c040700f504400100720841c140061100540c400507005071140845003c082a896011000340240005540c024038079010710039405000700e82c20f0310a050007020745588859580d02d50540741d981c028840e480349005d6404040c4252020f075032000965404071501c2c106850030404505843c02d503140900c200802c2d030795a00340b10300750a00f8880e8440ca48403004100049995100d46101c0b8400c0d6414002940001416030080310341c0a6032160500c4902c4c00d054036403030024a030000305254404000034506801c8000000500348541e010703039040c0203204080d0184110005a04030000225500040500c0025601005014541660000142011740c0c0350b4260070000c800382d02000c40c541c1d541c00001d030110070500c50b00d9210b00c860004510719041c4007803060412103004204104008043c0c0c01d0300c0c10000305205c0240c00302c0c3c2000c8299140c0ca0149100c100a50180c030907144038800b4200c1e026041d60089040ea411241c264443c98101117002ea030b460207504840401513030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 154647652 1250 154646402 154646419
    0x504020f0607061b1107090b030d030915290a0f0e0403050f130314010b0a09020a02070b180f0d03080a050604110706050108011104050d02150c07030b06010813150902 73
    0x8013612110b0034548018038503903e03401c1420341d280d000d500341105508100d10036400d051031000746031000250541d03501217516001078a0300d11400d0540c001c00c041112004100d0a08082c01c600342c01c15182c1c000031008420250903040f00903003c20054552520440594000700302d41006039055108866a01500900f8440d2504820b014110710760340c4104803200a659520901303105002070040000405852a0020402c030307600070000641c110410310580300803540005010902601c00e00c5200000d0600c0c541894440c041a240110203000840180740200c42d80407884096182407001085801e07015101c03d0b58a0b00c0300344100001d4000242142d03000381d00c4e07000341c410700f00c01900180750060160000107115418000a00d09485600910042507182448148410750b108800c1c4201d0b180d046892800c0784140391801982400384041c061a94040c150000040c800851155485604240c1e01e840c1d4940d90080e041d010854204800b03081c84912140070341c04150380381d2042820a0000384a4071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 154648902 1250 154647652 154647671
    0xd0f0339290408030a0507030204230105040b07030801080d03051605090f0a080d09080f1209190e0a0e0d050301050904050703060e0f12040501050306010f121103041103010504020f060706 82
    0x45031401c2a034048404a1000003008a02c465038410150440d031940ba0542c980b41c036100c02d2102010004041d880d804110b146240c51a0303000c0d00c219402404070440882d00c2d40c20700c0c10041c118000034441c0c00e440e4010014515100f92091041c10721030042004800324120300341c5030403103054110113106604014007940250040e44e4130105030008103c0720000705840404d5450051100310298409240e0f50b00a0808040007940450500902d00c0c66034a882c2d102e520040020303900b0300f01480481c40450038400046448400e06803040d100305400401481800c038172054203550747c04600d01c5c07180002c030140010300451604c149141e0300180120201c41c100303912034441d00102c41244150700940e41c04100c0b10040b5110034488000c0e1140352240700c5d03081a242070006040b52000400303c42c100485800003900d03181c084d851030002070003201002c001054031024000300b29842541c040e52030301000301c5e0300500c03890b05001d424403a99018001c1c101c40d003000e105200594020900840e5140c0d120781d2681c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 154650152 1250 154648902 154648973
    0x1b01060506070f110d05060105011409040204081e06101511011506140f030703020a02030c0a081806130303110c04051005010f090806060f0d0f0339 65
    0x82580d180500100d500d03c009600e005018103401512480c0520040035000d000709002159150440b074080c2407090f03204000b981030500600c6901142c1d6400751001c1404034580e400011000c20441c00c10b144d06001c540028a0150f8682c0110f50040310308543e418240f0510040d1030b408991950780782484e03450400004403260035605002c40f00c02415421540c1002455031090344414010403410b108c0785016a00e91203003d20380320080a4500f807580000e03045c04140d1080007103c009001c178070300341d0310800740e1482c110450380d016400000000c0741c5801c1c0d2071150300d002d5049965012000c840351040d2840d55600362034411041468141c0e1740242000e0311a66113550048510608503820042d040604000c00505203030340b040c02d40010800990420b10600000040d41c0e42c000381e0450750342040e405544002648101925002080c01443e195800209904401e240483e00c48041d0303e1284150740c078021030300d10020403c0c0032018800c50302d40304001c60b11081c3c101e040e0418001c0005441c0c092030108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 154651402 1250 154650152 154650157
    0x3006050303030f040605060a03171e04080a05010b04110703030c270e010b030c041a16050c03010e010209130b06070c0815060d031e0c05060c07261b01060506 69
    0x6062810714003c013004100401481900e034000c804407011001181991540e0303504081c2030b00240b050444c0001c0da12040e003500040c01c0342000d181c2c02e419a81d00d8035147c0203501d580803d0422585582000f445c400140781c18000d212603441150340041c104000f1b510b048000e089007600d0141480b400081c40c0703107483c80203a10524000d000c0c0d0500701c60f241c0392803012180701c02d050f032103c54506018020302c02c801c0c0b0000e084030b01b119503010b00c0f00007800d0800d409074410300c564180400c600100081d444200310001c690720030341d00303811002000076040a900700c42c04c0c2d21a00d4501d50780155580c40316812191264003400c0034510203400d84d820080700c0e81c2c1d40c40f14000c15030030000e1315a0001c40040d1031081400c00e4954031400a403006281400941c2e40500300003d88a00340c0c541400d142614400036219214201c00150070208581490a06041c0e0700420707400300c0410350b0101211300303101c3d840242ca041c0861600c030701c0816541c40c105c3d9000b070144901400445174942552203120010715651140b02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 154652652 1250 154651402 154651411
    0xd05071403090a03110d080c0c03161a07080c0a050a02070506040305030415051e070203010f0c110c01030207082a060c030106030b0d03080a1a0a0807090c300605030303 74
    0x6155000f180d0a0240606100b0000c01e11160b005422014100d6440503560383c118402c120a1600c58806045003030460054049207680422103010040c24040304030301803044080d12050031690340d2150301085403050812100c26051038420402c082009205000801307100d0320307a10540c3c090980b00d00000b11582d0003a8429109580003190034824540c904038002c81c1c903c054202a0310f4008070b1103203800c0c1120346444c501031000000c40e075101035490a401c074020080700240200700c1340c1541c901c042e1080d01c110380c0c0c02c5101c2c42118600341d0740b54042d100f100c40050300016078a0074014800b0100b040e0309000c0b440f59484030020312220324112010003e840c003070f01c1314030180c1b41c4941c1040001022620440941480b840400000002082d001968550404607110002c01c071603580702003003c40b100c62490240e401400c00180003490b0880490354000f6030304041c1c07061102c4d00c0d1008088503c4e66a810055403c240008000b82c141d0024041000400c1940e04001c55426030751000a41180c01c2202d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 154653902 1250 154652652 154652671
    0x705031b16050f19060c1b06140618040204180f0309080c060f0306040f0e030a0c120f020d0e01020a14010203070e0405010b07020603090109020901060216050103060303050d05071403 80
    0xc01c80400405111820351420341c10001c012480e281e900b286800e0a000c0000b62003180c0e1485d00003402c17031043c0d0480344031241c0c502010044011525002000704168004d660002d150f100c0800c040b4a01134080c003110310b0300402035520765107662f000c0100400d1030b00f0480c0004552085040e001070010001052440d00130b0f01c84120842c43c242c0c1c6142010002c42c4806d102d05020414140601000000d5941000068800268503503030b01c0c8041c001031a224108808078800450034014260303009444007150352040f40c4102c0d905444c01015141103003181898800368114545c10a09548030303010400b02814148101c0304401210b0b00d50410b010408404400c4694001080111481c1c2055860302151403c2d10204641c1d89050300b045800d009481c8028419407001010030380544094000c070113200c0e002450742c02c00756902c0070007079641c07204181c00080760b20a181c00042e2170741c024814442141d40548800313141c0030386802c0310380050200401ea81d0610114603040c0040d441d40401440c0b2a00160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 154655152 1250 154653902 154653937
    0xe090a060c05031e060108180106090e0a111509060a0c061503051504030203090f010306050312040302210601092c030901090e10060309020a0e0a06050a090b03060705031b 75
    0x402c400c50260001c0328111013080304041c0040c59902654103079100d900d5501801c212081110b03241e002d0582a8010403016007091107035501d41ca030200300c0c40401c900c60f4040c180610898411f01c4a0703003100e078144403440f0310144044410350800d00300501c040c03155450031442182e120b81c0c40c0c2084401c0d80d40c0f0101c5240c0c401400303208111040019944041e01116160910b2402e507500030f50302d204881d40c0601078070030750000d000e00764069017010002d810010107407510706c0000200020036400c5840107030b2240f0080d1113642e0769203042c02c040d40b01c071030300310405481207030b080180c080080c1c80134000e1080e00c0c44a41d504403810600040308006680c165030b001e1a518942d2000051139041c0030340001c0b4402010070300b4082d00014052840048a803242800308181e2101e000041c008a01070b480449000c0707594081041c11240e40d40008181c40e001c4801c04c051581303070003003001113480c0301120740d07010740c00003006c1040d450245025541c08940c0031103520305030404002c030862a400c40c810021000d4400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 154656402 1250 154655152 154655161
    0xb2b0c030b0f0907030e030c071421030403030804030e09040302010515010306050d0b04050a080f030105010201060b04080c0d05010608030706050a050901090302070b181e01030e030a090e090a060c0503 88
    0x360080300a8008100e0314104070620b204000340040728041c00750000d255491140250400060041d241c01441c8042510945da40e00c800d006403081400600074403d03c4c1c0041d04442043c01c1c0350524490610200040d0f003054190350301500e2103400a40207030103112000c0c00352b41d02d69540d580d020b07100c0d40c8039038000309860030139102c10424114001c0c1030a040c58100203041c0304c6521030303c0c0301c5501240c120110203140c0e100c0f030409a00b440c0025101422144000403080c1d0702850a078019030403204223034000c003c229581d086843c00b60180d4012444143c1040c54451800d250501c7e10b00921402440001000b9139100c005501d1a406030700100c030259160700400401004602c209684184880004c1c80940260365000f900c90095024002c800440440c0500b00d007c4113103c40320480101808001c1c0c02580d101000300000151540b050000c0e06140106500d4400403041da0f19154030707074440107101c40c14003100004a1b20300606000d040d10400b2071202c0807480900a42c2c810305503d4407000c0d07403802d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 154657652 1250 154656402 154656407
    0x90c09140106110a06050c0c1504030e03032104060f050703060501090e0105010212030903120408040801290f2404050306090307051002090d120207090b010206040c0b2b0c 75
    0x30503403014080c00003110010307a42480104100b5000ca40c04040003502d640c5407180c000541c002e1080701c0c5001c0c41400341c822200303003030148810301550090315401c03481a0024105942c0303108440503640c20003000009184c01d40801d0450f60340080c07146e20089001c00c40c06e4000c4040361400c03100d600c0000d407910410442560020014405048005403101e5290f05000020350365000c4005400e040c2240000084c100d05018016203403601d4030b4454001242c20705080c1012190842d0103058195403904082a204459020600c4206860084003031050411f10082200c034038a00d00209800c034000075042c4c002c0f0a42108142e0215880b40c150300d49460909040c586800d84c0106032485640c405c00a01001c200c00060b85e038551000000c0269070b81e84c0c0e00004c01c40e11401d030b51004200c102024a81d090150700070480b9401e5a014004c20403186a031600120303078540342510064101907200506110306c0d880c8800030810180301880080300e0003d000351104100d0150324003a01201d94400404c000c1d2503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 154658902 1250 154657652 154657691
    0x10614040902061207090e0408120a02030403080402010e130f0504060c0903050712060b0324060307030c05120715030b09010b120a0906061701020403020f0102120a080703090c09 78
    0x4180c60810008900c0d82c0880ca99102c2d09540d4486005030b0400100514400d4007480b01912001280c1005800c091400c5206da0304041e80004000c10098000b5280c051a8402d4034812070b095a0b40502d0768480390015540c2007414498203400600c0000c1120094180f40140001e441c07032000c00103000c1c40e00f810010b046070380180a00d4100710242100700085400013a07039a0954041103070b40400c4040710701d4401c1c01028203900c00e0390140200c02481d005980408504500134800e56481152544d039441055215800e40c04003e110003007409040c0020300340f107140358001e40c0441c3c04450840e5100d001810b03401c40c580440100003525075a00780d007a801c019000f20700621001e2111800d03c4010a9850108003000308038103150756458010509000094000700c0c0209541e0100d2000407054200140c040d5105010990041e41d4824072160a544005040440e03088000740d454201100c9060480e010400170303180d1401c04d1b84ac2c1c8041004074003995a8400140000e4000051000c0742039100c44608 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 154660152 1250 154658902 154658939
    0x1140d0b030322081005090709020918040807151b03020903010f0504140f010501060903020f01030603060c050408010510050102060f04061b0801150206040203031917040602030601110102180d1109090106 89
    0x5e4104814040103010004018040c0d600340c600258507984d0034000b01c0e0a00300880c4840f955100e500c0e09210038400c3d603600038160030740110341841d40554070900c008152455410000124210140045d076a2803190380941080701c00100081412068150030078242c1d8000e841c240d8500c0c20314181f4104130402004850712081c20000244140e40c0340200c041d02d098841c1c4006402680140440380f1981e200e42c0c040b002860340b01000300050303e94020010119005800740359215840c0c2404a100442d6a850380700454605031300a080c9076803441e04d4589072000c0a031007100d0b4039448003240c41c00880d0380c2c00c0c920f03484101a9152030303c640c5001090200106404010415500042c0a20015032030110440d180300742585401c850203101807604840080840c0d400d214600000300c14482001251b400841c0236142c00da0301c0c0b41d100c40d40300c400d041c00c034070400c0c81085081d440480c40f06254100407884003480e0b4052030303410312a00c0c4040040b50340104221821003403651744401c2031040d003045a0040000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 154661402 1250 154660152 154660183
    0x30f060305060705042c070e030307050715090501021f02070203070e01030b061f14031b0408010933050705070204020c060403030e0a020120070308040806040b0601140d0b03032208 79
    0x2030342d61000001c0100c040a447d0600704414890746410765101001118400340c1e016045882842d40c44840314510084003000400288000c1800255584005803859181c0301c404410380900f030142d10480c00a501484041340c040c000e18500040c200140407220f07000314021600c1f001d1a190082c20054101c900d807200c1c5000529054900744602e902c9215841c805a96234201070b0b6a40f2505100c2010003c4459602c41c1404000b8000c20624019000f80f084d080c410303025030182c04180c00c212103c5c2c41d0343c042500c0d540581000000720700509c5411082e000742d010b05000307141c1085a00480d0903a409900e020f0300951100003440201a0316200328404880c0c140c01030160010580c1c0000c1c4a04803c00345408882580f5042c001403101c1030080100071a03021a0a543c0c55680e41c03251600c440e0105d405907581e8480b000041d0495000380810f44400d003409120a10304010b15030803a0003030241c801c241d600351205101100d05d0a1a06034143e00e1080d5961101181a282c031308428901024060348606 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 154662652 1250 154661402 154661459
    0x207030206160306260d020309030d351015050909090124061404120201030213180609061401090303080c070b0703050a2a030f06030506070504 63
    0x800d601041c5075400c601c6800070550300032403000c0101c0140c190350300080c2650259583d040c0382103c625007804034140c0b101e03040e1100c15511006c240d0322400742c81c19540e01a0025544007042500c02c8070340c91695000c01c11450f0b141c01d54082e10925801c0c075041d85c1c441001001050001320380d126001c00300241100c0b02400b24495004a0060242c05a005d1a0740605041d00201d09504800e400045c4000b0f5500a002c525100801450040407403d00c54000410415901e1241c0c4501d030004032015a00e200c00d4007142c0c8030041d4011402940f28100c06094508480e402042c000804a440c807842c035039240000c603c071800d0024400445180342d012821580320100c40302c0d81c42c1d800900c001c003200e07014145012196620103250170103114048008001c00c0300a0100840307a40c02da40054020742103030004020020140e1410f5171482101058500483d409903041d2070390714801c0c1c000340720340421030b1004107955940ba0380e0a80b51900c151130001c041031000c6000c1c0a041c03c4600d10f88100300484181a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 154663902 1250 154662652 154662667
    0x219030509040e070305060717070813020d230106050f010216091d0a060903090608040c0308030c0d0905071a0301030b070e010e0d110102240f071803030302091302 72
    0x2091407040c10450303070140e500c80038403040710710042c441d8200031a0404281d0300286083c8000911f12020b10701d404c15941c03a21008a0b00c814800c049007031103191241c4040011038029003c00c00c2d5160710300d404441090112002050044220264402600782d134000070828505040400900c0399440718054119840403070b21451490007140312208590f4820b10009a084075a40400c180000250101d4420701c0703201306410401049501240d030050013035840d0301c001904d50340d084076007641c00e03940981055000c072410b1012401080007182c200d11004000d520745001420b9a4056855002054415800440e030030805c0c404070840c809140101500121b2a643c11641c3d591003404000e49000104142c0158211150740288008906148001d108d8003109803d07250a0040780d03001c02056006004500712154240404c07000b0744414151102d14512507aa11603049500076002842081000702d040e030150078520424150b0800b85020790f0703001d030390b41f8446070a0102c0001c5460034101450310412404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 154665152 1250 154663902 154663907
    0x2190f23030a020705013c110a080a0e0a03080103050c0904030f030e03070605151018031b0b1c05060604030f020402030a110c03040504140f0402011206081606021903 73
    0x22640700000b19001a120740403030070300078010500003603245414104030051050407003401c0c200341e15513110201e042c04660070403010f9106488140f0701d501e8203518180100074a442c065203078140d101010290001e2050302d40d840301761500a49100c142c001c20820070060090040030b020242c40c181080d07588030f04504165900400d609200c1e1081c00030107660780783c0314a000b28140122544240c10410501440c20030b912420300081c141d0b040940b2030f001e1020b1241c940d900526200c04000c0301c041400301403510f5601c1d0240100020034400442d64a0040007180b07000d410b4010f45285412031400031800c0000003015022164007408062117003105100400000328401c2e00062803950649000d070301c03600e400c000b42020300701c1c580302221048004580c40b25007510010140088403400c039000e00850241c1da0f48455100380654107111984007a80005004d54011003405002002045001640300d80d1140710500303164410184040384100308808201d000d9042102101080400281580070010359034013 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 154666402 1250 154665152 154665157
    0x1050307050304051606120f05010509060609150307030207170c0d03020c03070f11011704050a0b07020f03041d0f1501030e0304030213050a061e090f02190f23 70
    0x100c08029001000504020040c8520f003601107206154400e001c0d100c0801500d480c0d160310a0441c00c910b05022480c02a02c103004032412140064188031072602c0d001d060015035840180e0603074009a46403485040848100c000354400d180c00d40c1d0040c0c4400e01440e2401c25402e452004410844040c40f100e070328a41b010035403d8001003d800e005a0318200c1100150540c00346e400e014049000351010442448008802c07450041c8090340e408030900c81c03110041001440984010b012548803079160000200a141419003112072801180d8120000c0c2d02864030795401038003d5488000e450800c20050701d2244d91041d009200b2205085540c074010403104034080168001604041d2034100007140da001c103000300c0f400303984c000e80a0b6a9050b030059504000c1d201c242c40c0c001c0c483d841c019000441d0100d04041e000c05c002491030f103110542ca44220314001e046140400d0020603400c2045c452407851b504100a028180340c1c40300c8c1206007050703201609404120b03c5007000d6043c07642d10b4a00c0c07500308104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 154667652 1250 154666402 154666411
    0x1406060d03120902120a0c0807080d020c040b0d02090a02070209070f0507060b0a091a030601050f0904030f031107030c14010b0f061606020309030301030516050f01030e0f070915080705010503 84
    0x4902c1624000100c103c800304176034416074020058020148241c291440042d600c80800f00c544069940220660303d08446444900680001065100318601900500c114000081450707456828170b40000710070460035241d02e032009a0004031b0740b00b142800091b00398441c18030f04095410908000d0003421500c90000000e104a41e03500f061040344e658038544d10080c111310070341003102e40d0051070a8082c0c501140d1540d8880d10428000203140e01c1c0100c0710520550001d000c4084a07261a0b40c265103848900018100381038480383c04000236400ba0003d4038449001c3e030743e0703102500b91034201038180300b402c040c403a4000c0c1d04228000350b2035200d0600302c1285140c107540d529a55890340c0313005622000004002002d4070b0001007804502c4400002960589008034203680f610348520302e0520500d8441d00c21190014a84002820745c4c2d80070b42d204140809000f42a20348000f101c0112500340900b90300040310599940c210301d8070291461800d00007500b080d50017020700908040001c5e00c02d0100a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 154668902 1250 154667652 154667687
    0x2040e0f090f061005030105010e130b130f03090510030b150a0509030a141213050108090a06060608073903110d05031e1317070f1406060d03 62
    0x804100d081c03404001d880c126044a60a80d115401d141d080c4102090061158611941c00c2c40000705144044012050280d402440c0780e01c183c440c01d503102404504000e10b20104241d0810010f00070541840303a11458610075503a105495040500f0804014544032001d4205460040c40e15890f0326512404a8070003000c84405455901e41030b021a858803680d00215010700610300c0c00001c0204005c1c0d8410440c02c000c0658540c0c503460300c6901520b004040d000300c4201010383c41040b4a500409401c0d80101803581680e04000481e210841038403c194020b00000381020104014030b0342c8844007084100c0003034a101d815000404110725000b491500d0025012406098070042501598500101c482c2240c10786d84d10300e0318840040c0c040c0d0401c1f036005148a030340828010040c0706180c01c892080c1500c1640f201419038603150555034079400592440a02d0b000c010140100701d00984080d0820b11400074020070340849845c19060040280c0720601030b5184c101c000b4002074106803a01800070303001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 154670152 1250 154668902 154668931
    0x901090902031506130e0903070b04032a03110106080106030305030604110c070e0402040c080f070c03021204141201050105060f0c0304031e02100e010e010302070809040c0207060306080102040e 85
    0x8205685039950f0240958081d4000803006640d0b4005540d0718103d039a034000c3c1c24002d0781c9414001d80c60f4402e0310b0008084140e541e00040020f4040c20340340d2500e4100d0020001c41065a4405290300c00b00c2c1c0300e0680104012001100c4042c0003402001c018250b82c100078820b651450f513015090b4040034000b40e00c43c5450b006160542a17441c020368000000ca00102d60750165030701b001c1112414143c0e41680584c0c180200b0182d020301414a9600078030035181c11011039524290111902030607864214210700540e084032050441e10360242010f01030803d180c1000e801610200440108480807100e056418180100403030740e02d54007601c80e6401031400c032554440c0000e60880c1982304075040180007540f98540c80c0342c010401c06d14001f14038800e807540512200360302c3d000c0e603034441c2001c1000d0000d5080b800401e4a94841d80250101030720800c80f0608000191000905490702210030f02d0050b885008204800d80d41401404000c1c07588034000c51030541042a0202010b20080c00182d601000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 154671402 1250 154670152 154670161
    0x2070e0a0b10051c0605090406090212010e0114090610060c0317010303030501030209150609061c060b09130e03070201321815090d051c050304060f02090109090203 72
    0xc982205480382070040c42142c01920030340b4050029082000c2c01000400207075040350032100745114440c16510000d0002050750780719901c030400340540030b108a07082181210007612044090107840035800503400080b4082c841c424103100e209100900611650740800244941814407542050a540e030500c1d2040b0303001c20608080c2c4481009207181c0100da10715200000a050b85030f4450381c16030f4800c84040516481d005031502c10745401c2100c55078400010043d400c80c0e0300c1c0c4032004149160b1061800e17420380d42c0046800e0201e42244d40f19404d4070f00c0000344800b907860b1801e030380506540c525400f00005c002c0c04000f95030f03900550a000b0b060106400743c892002000d81d40c070480b03000704012491164100900c1c1000e142d00b100044101060f8030f0140d01e101403812038010815425000030280c280102c9030204100408a41da05603100d0281c24031190030003000044148000074241c4410b07640307080030f00c0c3c8481110030b03040000769550b1050100c0d10301d0f40c0e809084c80e401c440c4049409a160b485 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 154672652 1250 154671402 154671421
    0xb061b0307050303071d060702030d031509090804060e18060108060406150c0c0b0f030c090d050d0c030915020c040c02010e0102040f050a05010c0f080708210a05060f0102070e 77
    0x7400c007000c1c18510001c002c200303203603501244e21011620103003402080c0d00c41403003d00805014070307140254190055045052405d1280d032109130042544805500342e0395039208a04110740032a0720540b006080010244145c81c0c002c00343c20f40c030f0369042d80d601c0c01c04030307681c5a0245040c00241c2028100b100c05400700340c1641e039641150000d0112a10701e45800004842c0103040e43322032032001c0310710300084200020681c4d0314509892800749005506851692080b4500c21140d00000c1c1d0254000852039104000c22420440d40705000217584810140900a04002d0581d40031680030000715a550401441d0387e0b5400b080c0030300440f0080e03401150403860084242e02601203031241001944c808039000401541903144003007110001da500701202500d5400450b40018a0300015250680c020700c5140000e03440740050248034086c1090a0829050001030780501d2440e0440b0940722a94000b8131141136020b104d0290401021a4044c8041d241e800020792a5000761159414a21032240021006607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 154673902 1250 154672652 154672657
    0x60b0609040f0902030705010906020705040f0908030c0a0305090a0f1b0e070c0c2108160602040e0411010905010e12160f06140c031b010f0501030c090e010b061b03 72
    0x140207006000d2051a01c824900820707a01d41c00b80e21912a040000960754062004c00c0c1c142c801541c040c240150a2030144806092000c40e043c0d10159250040e402003410100518000c10303400c041c940da0741010305002001d850000e011003450350001b007182740010310b2000001c000310b54048505c040380c007940c1000e00004126544520701c80740000c01040606076108040e030560b680305005100f8843d8031007505120744c40058003c0c51300307122900458000310784080094007040405a401d180c89841e284d17200300c240e81190340710055001c8200180003c03c10303242c01d0b0000300f030400e1038030007012031412000130009480400502d0051140d08945024410140541301c103c08010191890303140d0b455040702c503844a1481142c0c0000d914248202c00b141001c821503000e07010310320081d0b00741900003c5108c0c2d11607002900f0b2000350b5030f41c06001c02054060064500960240002c256082c1c5051a00e0055404410301e4401c180d141c0b0f0b000403c20340d140301c15a15003026040c142d4840700c0c4494038062030361 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 154675152 1250 154673902 154673917
    0x706080c090a09020306030f06060901030f05030f040b030a0605030102160206130b0c06160c08030a050c041205070305010e0703200d170d060b072a0f03140c0d0f060b06 74
    0x41c85242c0458141040d0700214014001a022a10703c591141c0300c2c03580301c55050361342c6039202a0301e1004001241c1180e02c8245028003440940785002c00d91810940c0039806588820301c00b40d800f104100100449210b00c04c02081c040e802580342a07503d0910034002080c000c80248100c82c08901842d80042c00040400030b0198040b0080c0d8522030010820355542e0112010218024501541800c26101c2d20400d0305081d0701080c4030341982c483c2040100070b0040200a107503059402c5c880080d4100c8131064a00c1c100f80110080d100c1d0504600b0510b0954030b92400e80301955002c02406c000068803082e020040c6844c100010381c040c071010000800072907200300c000d801e070000e202c1600d500b0540140200f64a42d4885000c101c010340d102c2050040e4018008050200d4400e4414041c0305074040765800010300d0000d805261140d10703007c50081c0d0380d6a0390400d540305207078480d42080c100401c004446540f04100d500850300403c1d80d540352a8024540c00082c400703521491096515202c0800ba100b41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 154676258 1106 154675152 154675159
    0x4031e08040308090117010605070606080c010207030303150e04140607170406020901180b0a020f01063f12080604052e030501050a060e0106030e0706080c09 69
    0x540c100301e4100e07040c003496201e106c1d040e580c080740b0350380a01240d844483e2580035a0605030119042034100200b0f552200c0d0706614941c3e00042e5400c12282d05260209000c0380860030b016022589038480000c09400d1000d0104004098a15540000017802200c21550b01d051048400d50003007a1101c07105240d40020038007040b4260010110058103043c0790f0740340d004c1c00203494103640007640700950080f030200b52540142c2c4e050140000032440200284203103420300740c004d0050440216403140c0e655451005132602425004040807a060140031010400701c17a007084540d41914407803000000f940c040c0000e41c589050310a05000340c010740840e0220080c2a40407115071384541528060580804100000040003400307580d00c594080c50003c13462900d0004020005c04041e0080b40900d4207250250f20f800e4000102602280c1c040d01d0b107240c1907140d41650586501c11503481030f41 = true := by decide +kernel

theorem cover : BRFrame.Cov 154496402 154676258 := by
  have h0 := BRFrame.cov_init 154496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 154496402 ≤ n) (h2 : n < 154676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
